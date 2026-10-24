#!/usr/bin/env python3
"""Independent v3 byte vectors using OpenSSL-backed cryptography and argon2-cffi.

For development/test only. Neither dependency is required by the Rust product.
"""
import hashlib
from pathlib import Path
import unittest

from argon2.low_level import Type, hash_secret_raw
from cryptography.hazmat.primitives.ciphers.aead import AESSIV

HERE = Path(__file__).resolve().parent
PASSWORD = b"correct horse battery staple long secret"
SALT = bytes(range(32))
CONFIG_DOMAIN = b"transcrypt/v3/config"
FILE_DOMAIN = b"transcrypt/v3/file"
CONFIG_MAGIC = b"TCFG3\x00\x01"
FILE_MAGIC = b"TV3F\x00\x01"
SAMPLES = {
    "empty": b"",
    "short": b"Hello secure v3!\n",
    "binary": bytes([0, 255, 1, 2, 0, 128, 13, 10]),
}


def independent_cases():
    key = hash_secret_raw(
        PASSWORD, SALT, time_cost=3, memory_cost=65536, parallelism=1,
        hash_len=64, type=Type.ID, version=19,
    )
    cipher = AESSIV(key)
    prefix = CONFIG_MAGIC + SALT
    config = prefix + cipher.encrypt(b"", [CONFIG_DOMAIN, prefix])
    ident = hashlib.sha256(config).digest()[:16]
    result = []
    for name, plaintext in SAMPLES.items():
        record = FILE_MAGIC + ident + cipher.encrypt(plaintext, [FILE_DOMAIN, config])
        result.append((name, plaintext, config, record))
        assert cipher.decrypt(record[22:], [FILE_DOMAIN, config]) == plaintext
        tampered = bytearray(record)
        tampered[-1] ^= 1
        try:
            cipher.decrypt(tampered[22:], [FILE_DOMAIN, config])
        except Exception:
            pass
        else:
            raise AssertionError("modified ciphertext unexpectedly authenticated")
    return result


def serialize(cases):
    return "".join(
        f"{name}\t{plain.hex()}\t{config.hex()}\t{record.hex()}\n"
        for name, plain, config, record in cases
    )


class V3Reference(unittest.TestCase):
    def test_fixed_vectors(self):
        self.assertEqual((HERE / "vectors.tsv").read_text(), serialize(independent_cases()))

    def test_configuration_substitution_is_not_accepted(self):
        for _, _, config, record in independent_cases():
            altered = bytearray(config)
            altered[7] ^= 1
            key = hash_secret_raw(PASSWORD, SALT, time_cost=3, memory_cost=65536,
                                  parallelism=1, hash_len=64, type=Type.ID, version=19)
            with self.assertRaises(Exception):
                AESSIV(key).decrypt(record[22:], [FILE_DOMAIN, bytes(altered)])


if __name__ == "__main__":
    import sys
    if sys.argv[1:] == ["--write"]:
        (HERE / "vectors.tsv").write_text(serialize(independent_cases()))
    else:
        unittest.main()
