#!/usr/bin/env python3
"""Differential corpus for the v3 primitives, from independent implementations.

AES-SIV comes from OpenSSL (via `cryptography`), Argon2id from the reference
C implementation (via `argon2-cffi`), SHA-256 from `hashlib`. The Rust test
`tests/v3_differential.rs` checks the production `Keyed` primitive and the
verified core against every case: byte-exact sealing and opening, and
rejection of every tampering, truncation, extension and context change.

    python3 tests/v3/reference/differential.py           # check the corpus
    python3 tests/v3/reference/differential.py --write   # regenerate it

For development/test only; the Rust product does not depend on Python.
"""
import hashlib
import random
import sys
from pathlib import Path

from argon2.low_level import Type, hash_secret_raw
from cryptography.hazmat.primitives.ciphers.aead import AESSIV

HERE = Path(__file__).resolve().parent
CONFIG_DOMAIN = b"transcrypt/v3/config"
FILE_DOMAIN = b"transcrypt/v3/file"
CONFIG_MAGIC = b"TCFG3\x00\x01"
FILE_MAGIC = b"TV3F\x00\x01"
# Block boundaries of AES (16), the CMAC padding cases, and larger bodies.
LENGTHS = [0, 1, 15, 16, 17, 31, 32, 33, 47, 48, 49, 63, 64, 65, 255, 256, 257, 1000, 4095, 4096, 4097, 16385]


def siv_cases():
    rng = random.Random(20261025)
    cases = []
    for i, length in enumerate(LENGTHS):
        key = rng.randbytes(64)
        cipher = AESSIV(key)
        salt = rng.randbytes(32)
        prefix = CONFIG_MAGIC + salt
        config = prefix + cipher.encrypt(b"", [CONFIG_DOMAIN, prefix])
        depth = rng.randrange(0, 4)
        parts = [bytes(rng.choice(b"abcxyz019_-. \t\n\xff\x80") for _ in range(rng.randrange(1, 12))) for _ in range(depth)]
        path = b"/".join(parts + [b"f%d.secret" % i])
        if b"/./" in b"/" + path or b"/../" in b"/" + path or path.startswith(b"./") or b"//" in path:
            path = b"f%d.secret" % i
        plaintext = rng.randbytes(length)
        ident = hashlib.sha256(config).digest()[:16]
        record = FILE_MAGIC + ident + cipher.encrypt(plaintext, [FILE_DOMAIN, config, path])
        # The associated data is a vector of three separate components
        # (RFC 5297 S2V), never their concatenation.
        assert cipher.encrypt(plaintext, [FILE_DOMAIN + config + path]) != record[22:]
        assert cipher.encrypt(plaintext, [FILE_DOMAIN, config + path]) != record[22:]
        assert cipher.decrypt(record[22:], [FILE_DOMAIN, config, path]) == plaintext
        cases.append((f"siv-{length}", key, config, path, plaintext, record))
    return cases


def kdf_cases():
    rng = random.Random(5297)
    cases = []
    for name, password in [("min16", b"0123456789abcdef"), ("max4096", rng.randbytes(4096)),
                           ("utf8", "pässwörd – ключ – 鍵".encode())]:
        salt = rng.randbytes(32)
        key = hash_secret_raw(password, salt, time_cost=3, memory_cost=65536, parallelism=1,
                              hash_len=64, type=Type.ID, version=19)
        cases.append((f"kdf-{name}", password, salt, key))
    return cases


def serialize():
    rows = [f"{n}\t{k.hex()}\t{c.hex()}\t{p.hex()}\t{m.hex()}\t{r.hex()}\n" for n, k, c, p, m, r in siv_cases()]
    kdf = [f"{n}\t{p.hex()}\t{s.hex()}\t{k.hex()}\n" for n, p, s, k in kdf_cases()]
    return "".join(rows), "".join(kdf)


if __name__ == "__main__":
    siv, kdf = serialize()
    if sys.argv[1:] == ["--write"]:
        (HERE / "differential.tsv").write_text(siv)
        (HERE / "kdf.tsv").write_text(kdf)
    elif (HERE / "differential.tsv").read_text() != siv or (HERE / "kdf.tsv").read_text() != kdf:
        sys.exit("differential corpus does not match the independent implementations")
    else:
        print("differential corpus matches OpenSSL AES-SIV and reference Argon2id")
