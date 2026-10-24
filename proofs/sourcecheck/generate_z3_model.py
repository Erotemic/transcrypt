#!/usr/bin/env python3
"""Translate a closed, checked expression subset of real Rust into Z3 C ASTs.

The generated header is temporary proof input, not a shipped artifact.
Any unsupported Rust construct aborts proof generation. The Rust compiler
and a future Aeneas translation remain outside this limited assurance claim.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from rust_expr import parse_function, to_z3_c


POLICIES = (
    ("secure_stage_allowed", ("bool",) * 6),
    ("unlock_writes_allowed", ("bool",) * 4),
    ("migration_publish_allowed", ("bool",) * 6),
)


def generate_policy(source: str) -> str:
    parts = [
        "/* Generated from the actual Rust Boolean policy expressions. */",
        "static Z3_ast aand(Z3_ast x, Z3_ast y) { Z3_ast z[2] = {x, y}; return land(2, z); }",
        "static Z3_ast oor(Z3_ast x, Z3_ast y) { Z3_ast z[2] = {x, y}; return lor(2, z); }",
    ]
    for name, types in POLICIES:
        func = parse_function(source, name, types, "bool")
        args = ", ".join(f"Z3_ast {arg}" for arg in func.args)
        expression = to_z3_c(func.body, {arg: arg for arg in func.args}, "bool")
        parts.append(f"static Z3_ast rust_{name}({args}) {{ return {expression}; }}")
    return "\n".join(parts) + "\n"


def generate_base64(source: str) -> str:
    splitter = parse_function(source, "split_triple", ("u8", "u8", "u8"), "[u8;4]")
    joiner = parse_function(source, "join_quartet", ("[u8; 4]",), "[u8;3]")
    split_expr = [to_z3_c(n, {"a": "a", "b": "b", "c": "c"}, "byte") for n in splitter.body]
    join_expr = [to_z3_c(n, {f"s[{i}]": f"q{i}" for i in range(4)}, "byte") for n in joiner.body]
    return "\n".join([
        "/* Generated from actual Rust u8 shifts/masks (all modeled at width eight). */",
        "static Z3_ast rust_split(unsigned slot, Z3_ast a, Z3_ast b, Z3_ast c) {",
        "    Z3_ast out[4] = {" + ", ".join(split_expr) + "};",
        "    if (slot >= 4) abort();",
        "    return out[slot];",
        "}",
        "static Z3_ast rust_join(unsigned slot, Z3_ast q0, Z3_ast q1, Z3_ast q2, Z3_ast q3) {",
        "    Z3_ast out[3] = {" + ", ".join(join_expr) + "};",
        "    if (slot >= 3) abort();",
        "    return out[slot];",
        "}",
        "",
    ])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", choices=["base64", "policy"], required=True)
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    raw = args.source.read_bytes()
    source = raw.decode("utf-8")
    output = generate_base64(source) if args.kind == "base64" else generate_policy(source)
    digest = hashlib.sha256(raw).hexdigest()
    args.output.write_text("/* source_sha256=" + digest + " */\n" + output)
    print(f"Source-derived {args.kind} model: {args.source} SHA-256 {digest}")


if __name__ == "__main__":
    main()
