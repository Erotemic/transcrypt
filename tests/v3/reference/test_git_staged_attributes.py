"""Executable Git contract for the v3 staged-filter preflight.

These tests exercise real Git precedence and exact NUL pathname transport.
They do not stand in for the Rust integration tests or formal verification.
"""
import os
import subprocess
import tempfile
import unittest
from pathlib import Path


def git(root: Path, *args: bytes, data: bytes | None = None) -> bytes:
    p = subprocess.run([b"git", *args], cwd=os.fsencode(root), input=data,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if p.returncode:
        raise AssertionError(f"git {args!r} failed: {p.stderr!r}")
    return p.stdout


def query_filter(root: Path, paths: list[bytes]) -> list[tuple[bytes, bytes, bytes]]:
    if not paths:
        return []
    raw = git(root, b"check-attr", b"--cached", b"-z", b"--stdin", b"filter",
              data=b"\0".join(paths) + b"\0")
    fields = raw.split(b"\0")
    assert fields[-1] == b"" and len(fields) == len(paths) * 3 + 1
    return [tuple(fields[i:i+3]) for i in range(0, len(fields)-1, 3)]


class GitStagedAttributeContract(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="transcrypt-v3-attr-")
        self.root = Path(self.temp.name)
        git(self.root, b"init", b"-q")
        git(self.root, b"config", b"filter.transcrypt-v3.clean", b"cat")
        git(self.root, b"config", b"filter.transcrypt-v3.smudge", b"cat")
        (self.root / ".gitattributes").write_bytes(b"*.secret filter=transcrypt-v3\n")
        (self.root / "account.secret").write_bytes(b"opaque mock bytes")
        git(self.root, b"add", b".gitattributes", b"account.secret")

    def tearDown(self):
        self.temp.cleanup()

    def test_staged_attributes_not_modified_worktree(self):
        path = b"account.secret"
        self.assertEqual(query_filter(self.root, [path]), [(path, b"filter", b"transcrypt-v3")])
        (self.root / ".gitattributes").write_bytes(b"*.secret -filter\n")
        self.assertEqual(query_filter(self.root, [path]), [(path, b"filter", b"transcrypt-v3")])

    def test_info_attributes_override_even_staged_policy(self):
        path = b"account.secret"
        (self.root / ".git/info/attributes").write_bytes(b"*.secret -filter\n")
        self.assertEqual(query_filter(self.root, [path]), [(path, b"filter", b"unset")])
        (self.root / ".git/info/attributes").write_bytes(b"*.secret filter=other\n")
        self.assertEqual(query_filter(self.root, [path]), [(path, b"filter", b"other")])

    def test_nested_staged_attributes_override(self):
        (self.root / "nested").mkdir()
        (self.root / "nested/.gitattributes").write_bytes(b"*.secret -filter\n")
        (self.root / "nested/ledger.secret").write_bytes(b"raw staged bytes")
        git(self.root, b"add", b"nested/.gitattributes", b"nested/ledger.secret")
        path = b"nested/ledger.secret"
        self.assertEqual(query_filter(self.root, [path]), [(path, b"filter", b"unset")])
        (self.root / "nested/.gitattributes").write_bytes(b"*.secret filter=transcrypt-v3\n")
        self.assertEqual(query_filter(self.root, [path]), [(path, b"filter", b"unset")])

    def test_nul_raw_path_transport(self):
        path = b"odd \\n'\\xff.secret".replace(b"\\n", b"\n").replace(b"\\xff", b"\xff")
        (self.root / os.fsdecode(path)).write_bytes(b"mock bytes")
        git(self.root, b"add", b"--", path)
        records = query_filter(self.root, [path, b"account.secret"])
        self.assertEqual(records, [(path, b"filter", b"transcrypt-v3"),
                                   (b"account.secret", b"filter", b"transcrypt-v3")])


if __name__ == "__main__":
    unittest.main()
