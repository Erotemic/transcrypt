"""Closed-subset Rust expression reader for proof model generation.

This is intentionally *not* a Rust compiler. It accepts only pure functions
whose bodies are a single Boolean or u8-array expression and rejects other
Rust constructs rather than guessing their meanings. Aeneas refinement of
compiled Rust remains the stronger end-to-end target.
"""

from __future__ import annotations

import re
from dataclasses import dataclass


class UnsupportedRust(ValueError):
    """Source escapes the modeled subset (do not claim verification)."""


@dataclass(frozen=True)
class Function:
    name: str
    args: tuple[str, ...]
    body: object


_TOKEN = re.compile(r"\s*(?:([A-Za-z_][A-Za-z_0-9]*)|([0-9]+)|(&&|\|\||<<|>>|[!()&|,\[\]]))")
_BINARY_LEVELS = {"||": 1, "&&": 2, "|": 3, "&": 4, "<<": 5, ">>": 5}


def _tokens(text: str) -> list[str]:
    result = []
    offset = 0
    while offset < len(text):
        if text[offset:].isspace():
            break
        match = _TOKEN.match(text, offset)
        if match is None:
            raise UnsupportedRust(f"unrecognized expression near {text[offset:offset + 40]!r}")
        result.append(next(item for item in match.groups() if item is not None))
        offset = match.end()
    return result


class _Parser:
    def __init__(self, text: str):
        self.tokens = _tokens(text)
        self.i = 0

    def peek(self) -> str | None:
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def eat(self, want: str | None = None) -> str:
        got = self.peek()
        if got is None or (want is not None and got != want):
            raise UnsupportedRust(f"expected {want!r}, found {got!r}")
        self.i += 1
        return got

    def expr(self, min_bp: int = 0) -> object:
        first = self.eat()
        if first == "(":
            left = self.expr()
            self.eat(")")
        elif first == "!":
            left = ("not", self.expr(6))
        elif first.isdecimal():
            left = ("num", int(first))
        elif re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", first):
            if self.peek() == "[":
                self.eat("[")
                index = self.eat()
                if not index.isdecimal():
                    raise UnsupportedRust("only literal fixed-array indices are modeled")
                self.eat("]")
                left = ("index", first, int(index))
            else:
                left = ("var", first)
        else:
            raise UnsupportedRust(f"unsupported atom {first!r}")
        while self.peek() in _BINARY_LEVELS and _BINARY_LEVELS[self.peek()] >= min_bp:
            op = self.eat()
            bp = _BINARY_LEVELS[op]
            right = self.expr(bp + 1)
            left = ("bin", op, left, right)
        return left

    def body(self, array_len: int | None) -> object:
        if array_len is None:
            result = self.expr()
        else:
            self.eat("[")
            items = []
            for i in range(array_len):
                items.append(self.expr())
                if i != array_len - 1:
                    self.eat(",")
            if self.peek() == ",":
                self.eat(",")
            self.eat("]")
            result = tuple(items)
        if self.peek() is not None:
            raise UnsupportedRust(f"unexpected trailing token {self.peek()!r}")
        return result


def _signature_and_body(source: str, name: str) -> tuple[str, str, str]:
    # Anchoring to a non-comment line avoids accidentally finding mentions
    # of function names in documentation. A compiler-level extract is still
    # a separate future acceptance condition.
    matches = list(re.finditer(
        r"(?m)^\s*pub(?:\(crate\))?\s+fn\s+" + re.escape(name) + r"\s*\(",
        source,
    ))
    if len(matches) != 1:
        raise UnsupportedRust(f"expected exactly one public function {name}; found {len(matches)}")
    start = matches[0].end()
    depth = 1
    pos = start
    while depth:
        if pos >= len(source):
            raise UnsupportedRust(f"unterminated signature for {name}")
        char = source[pos]
        depth += (char == "(") - (char == ")")
        pos += 1
    params = source[start:pos - 1]
    rest = re.match(r"\s*->\s*(bool|\[u8\s*;\s*[34]\])\s*\{", source[pos:])
    if rest is None:
        raise UnsupportedRust(f"unsupported return type or body for {name}")
    ret = rest.group(1)
    start_body = pos + rest.end()
    close = source.find("}", start_body)
    if close < 0:
        raise UnsupportedRust(f"unterminated body for {name}")
    body = source[start_body:close].strip()
    # Any statements, comments, nested control flow, macros, or explicit
    # returns must be reviewed and modeled separately.
    if not body or "{" in body or "//" in body or "/*" in body or ";" in body:
        raise UnsupportedRust(f"{name} is no longer a pure single-expression function")
    return params, ret, body


def parse_function(
    source: str, name: str, expected_arg_types: tuple[str, ...],
    expected_return_type: str,
) -> Function:
    params, ret, body = _signature_and_body(source, name)
    declarations = [param.strip() for param in params.split(",") if param.strip()]
    if len(declarations) != len(expected_arg_types):
        raise UnsupportedRust(f"{name}: arity changed")
    names: list[str] = []
    for decl, expected in zip(declarations, expected_arg_types):
        match = re.fullmatch(r"([A-Za-z_][A-Za-z_0-9]*)\s*:\s*" + re.escape(expected), decl)
        if match is None:
            raise UnsupportedRust(f"{name}: unmodeled parameter {decl!r}")
        names.append(match.group(1))
    if len(set(names)) != len(names) or ret.replace(" ", "") != expected_return_type.replace(" ", ""):
        raise UnsupportedRust(f"{name}: unsupported signature")
    tree = _Parser(body).body(4 if expected_return_type == "[u8;4]" else 3 if expected_return_type == "[u8;3]" else None)
    var_types = {n: t for n, t in zip(names, expected_arg_types)}
    if isinstance(tree, tuple) and tree and isinstance(tree[0], tuple):
        for node in tree:
            _validate(node, var_types, "byte")
    else:
        _validate(tree, var_types, "bool")
    return Function(name, tuple(names), tree)


def _validate(node: object, types: dict[str, str], kind: str) -> None:
    tag = node[0]
    if tag == "var":
        if node[1] not in types or types[node[1]] != ("u8" if kind == "byte" else "bool"):
            raise UnsupportedRust(f"unmodeled variable or type {node[1]}")
    elif tag == "index":
        if kind != "byte" or node[1] not in types or types[node[1]] != "[u8; 4]" or not 0 <= node[2] <= 3:
            raise UnsupportedRust("invalid modeled fixed array index")
    elif tag == "num":
        if kind != "byte" or not 0 <= node[1] <= 255:
            raise UnsupportedRust("invalid byte literal")
    elif tag == "not":
        if kind != "bool":
            raise UnsupportedRust("invalid Boolean not")
        _validate(node[1], types, kind)
    elif tag == "bin":
        op, left, right = node[1:]
        if op not in ({"|", "&", "<<", ">>"} if kind == "byte" else {"&&", "||"}):
            raise UnsupportedRust(f"unexpected {op!r} in {kind} expression")
        _validate(left, types, kind)
        if op in {"<<", ">>"}:
            if right[0] != "num" or not 0 <= right[1] <= 7:
                raise UnsupportedRust("shift must have a literal amount in 0..7")
        else:
            _validate(right, types, kind)
    else:
        raise UnsupportedRust(f"unsupported syntax {tag!r}")


def eval_node(node: object, env: dict[str, int | bool], kind: str) -> int | bool:
    tag = node[0]
    if tag == "var":
        return env[node[1]]
    if tag == "index":
        return env[f"{node[1]}[{node[2]}]"]
    if tag == "num":
        return node[1]
    if tag == "not":
        return not eval_node(node[1], env, kind)
    if tag == "bin":
        op, lhs, rhs = node[1:]
        a = eval_node(lhs, env, kind)
        b = eval_node(rhs, env, kind)
        if op == "&&":
            return bool(a and b)
        if op == "||":
            return bool(a or b)
        if op == "&":
            return (a & b) & 255
        if op == "|":
            return (a | b) & 255
        if op == "<<":
            return (a << b) & 255
        if op == ">>":
            return a >> b
    raise UnsupportedRust(f"unexpected node {node!r}")


def to_z3_c(node: object, name_mapping: dict[str, str], kind: str) -> str:
    tag = node[0]
    if tag == "var":
        return name_mapping[node[1]]
    if tag == "index":
        return name_mapping[f"{node[1]}[{node[2]}]"]
    if tag == "num":
        return f"constant(8, {node[1]})"
    if tag == "not":
        return f"lnot({to_z3_c(node[1], name_mapping, kind)})"
    if tag == "bin":
        op, lhs, rhs = node[1:]
        left = to_z3_c(lhs, name_mapping, kind)
        if op in {"<<", ">>"}:
            return f"{('shl' if op == '<<' else 'shr')}({left}, {rhs[1]})"
        right = to_z3_c(rhs, name_mapping, kind)
        return f"{ {'&&':'aand','||':'oor','&':'band','|':'bor'}[op]}({left}, {right})"
    raise UnsupportedRust(f"cannot model {node!r}")
