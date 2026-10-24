"""Tests for the trusted, deliberately narrow Rust-expression-to-SMT bridge."""

from __future__ import annotations

import ctypes.util
import itertools
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from generate_z3_model import generate_base64, generate_policy
from rust_expr import UnsupportedRust, eval_node, parse_function


ROOT = Path(__file__).resolve().parents[2]
POLICY = ROOT / "rust/crates/transcrypt-policy/src/lib.rs"
BITCORE = ROOT / "rust/crates/transcrypt-protocol/src/base64_bits.rs"


class SourceModels(unittest.TestCase):
    def test_model_contains_source_operations_not_old_pinned_copy(self):
        src = BITCORE.read_text()
        model = generate_base64(src)
        self.assertIn("shr(a, 2)", model)
        self.assertIn("band(c, constant(8, 63))", model)
        mutated = src.replace("a >> 2", "a >> 3", 1)
        self.assertIn("shr(a, 3)", generate_base64(mutated))

    def test_unsupported_rust_fails_closed(self):
        src = POLICY.read_text()
        for replacement in ("let hidden = true; authenticated", "unsafe { authenticated }",
                            "authenticated as bool", "authenticated; false"):
            mutated = src.replace("&& authenticated\n}", f"&& {replacement}\n}}", 1)
            with self.subTest(replacement=replacement):
                with self.assertRaises(UnsupportedRust):
                    generate_policy(mutated)

    def test_policy_source_matches_independent_truth_tables(self):
        src = POLICY.read_text()
        cases = (
            ("secure_stage_allowed", 6, lambda v: (v[0] or v[1]) and all(v[2:])),
            ("unlock_writes_allowed", 4, lambda v: all(v)),
            ("migration_publish_allowed", 6, lambda v: all(v)),
        )
        checked = 0
        for name, arity, independent in cases:
            f = parse_function(src, name, ("bool",) * arity, "bool")
            for values in itertools.product((False, True), repeat=arity):
                with self.subTest(function=name, inputs=values):
                    got = eval_node(f.body, dict(zip(f.args, values)), "bool")
                    self.assertEqual(got, independent(values))
                checked += 1
        self.assertEqual(checked, 144)

    def test_byte_expression_selected_inputs(self):
        src = BITCORE.read_text()
        split = parse_function(src, "split_triple", ("u8",) * 3, "[u8;4]")
        join = parse_function(src, "join_quartet", ("[u8; 4]",), "[u8;3]")
        for a, b, c in itertools.product((0, 1, 42, 127, 128, 255), repeat=3):
            env = {"a": a, "b": b, "c": c}
            sextets = [eval_node(n, env, "byte") for n in split.body]
            self.assertEqual(sextets, [a >> 2, ((a & 3) << 4) | (b >> 4),
                                       ((b & 15) << 2) | (c >> 6), c & 63])
            unpacked = [eval_node(n, {f"s[{i}]": s for i, s in enumerate(sextets)}, "byte")
                        for n in join.body]
            self.assertEqual(unpacked, [a, b, c])

    def _check_mutation_is_rejected_by_z3(self, kind: str, source: str) -> None:
        """Run the actual C proof with a temporary Rust-source mutation."""
        with tempfile.TemporaryDirectory(prefix="transcrypt-proof-mutation-") as directory:
            folder = Path(directory)
            header = folder / "rust_source_model.h"
            header.write_text(generate_base64(source) if kind == "base64" else generate_policy(source))
            driver = ROOT / "proofs/smt" / ("base64_bitvector.c" if kind == "base64" else "policy_bitvector.c")
            binary = folder / "proof"
            library = os.environ.get("LIBZ3")
            if not library:
                # On a normal CI host libz3-dev provides -lz3. Linux dev
                # containers with only a versioned lib can use LIBZ3.
                library = "-lz3"
            cmd = ["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic",
                   "-O2", "-I", str(folder), str(driver), library, "-o", str(binary)]
            subprocess.run(cmd, check=True, capture_output=True, text=True)
            result = subprocess.run([binary], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("SAT counterexample" if kind == "policy" else "SAT (counterexample)",
                          result.stderr)

    def test_policy_mutation_produces_smt_counterexample(self):
        src = POLICY.read_text().replace("&& authenticated\n}", "|| authenticated\n}", 1)
        self.assertNotEqual(src, POLICY.read_text())
        self._check_mutation_is_rejected_by_z3("policy", src)

    def test_base64_mutation_produces_smt_counterexample(self):
        src = BITCORE.read_text().replace("a >> 2", "a >> 3", 1)
        self.assertNotEqual(src, BITCORE.read_text())
        self._check_mutation_is_rejected_by_z3("base64", src)


if __name__ == "__main__":
    unittest.main()
