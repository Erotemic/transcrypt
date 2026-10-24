#!/usr/bin/env python3
"""Prove what Git actually passes to a subprocess for `%f` (no Rust needed).

Exercises exact bytes for whitespace, quotes, shell meta, newline, and a
non-UTF8 Unix path, so the path-bound encryption layer isn't built atop
an incorrect or dangerous shell-quoting assumption.
"""

import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest


CAPTURE = '''import os, sys
with open(os.environ["TC_PATH_LOG"], "ab") as f:
    path = os.fsencode(sys.argv[1])
    f.write(len(path).to_bytes(4, "big") + path)
sys.stdout.buffer.write(sys.stdin.buffer.read())
'''


class GitFilterPathContract(unittest.TestCase):
    def test_git_percent_f_is_one_exact_raw_byte_argument(self):
        if os.name != "posix":
            self.skipTest("Unix raw Git path semantics")
        names = [b"with space.secret", b"apost'rophe.secret", b"semicolon;$(echo BAD).secret",
                 b"with\nnewline.secret", b"raw\xffbytes.secret"]
        with tempfile.TemporaryDirectory(prefix="tc-filter-path-") as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            (root / ".gitattributes").write_bytes(b"*.secret filter=path-capture\n")
            (root / "capture.py").write_text(CAPTURE)
            log = root / "paths.bin"
            env = os.environ.copy()
            env["TC_PATH_LOG"] = str(log)
            cmd = f"{shlex.quote(sys.executable)} {shlex.quote(str(root/'capture.py'))} %f"
            subprocess.run(["git", "config", "filter.path-capture.clean", cmd], cwd=root, check=True)
            subprocess.run(["git", "config", "filter.path-capture.required", "true"], cwd=root, check=True)
            for name in names:
                with open(os.fsencode(root) + b"/" + name, "wb") as out:
                    out.write(b"not secret to the test process\n")
                log.write_bytes(b"")
                subprocess.run([b"git", b"add", b"--", name], cwd=root, env=env,
                               check=True, capture_output=True)
                blob = log.read_bytes()
                seen = []
                while blob:
                    self.assertGreaterEqual(len(blob), 4, name)
                    size = int.from_bytes(blob[:4], "big")
                    self.assertGreaterEqual(len(blob), size + 4)
                    seen.append(blob[4:4 + size])
                    blob = blob[4 + size:]
                # Git may also re-clean earlier staged paths during add;
                # every invocation still passes precisely one raw pathname.
                self.assertIn(name, seen)

            # Git must use a root-relative pathname even when invoked from
            # inside the subdirectory. The cipher AAD must not depend on cwd.
            nested = root / "nested"
            nested.mkdir()
            (nested / "path.secret").write_bytes(b"nested plaintext")
            log.write_bytes(b"")
            subprocess.run(["git", "add", "--", "path.secret"], cwd=nested,
                           env=env, check=True, capture_output=True)
            blob = log.read_bytes()
            seen = []
            while blob:
                self.assertGreaterEqual(len(blob), 4)
                size = int.from_bytes(blob[:4], "big")
                self.assertGreaterEqual(len(blob), 4 + size)
                seen.append(blob[4:4 + size])
                blob = blob[4 + size:]
            self.assertIn(b"nested/path.secret", seen)


if __name__ == "__main__":
    unittest.main()
