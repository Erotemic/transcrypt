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
    "empty": (b"archive/empty.secret", b""),
    "short": (b"reports/short.secret", b"Hello secure v3!\n"),
    "binary": (b"raw/\xff-binary.secret", bytes([0, 255, 1, 2, 0, 128, 13, 10])),
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
    for name, (path, plaintext) in SAMPLES.items():
        record = FILE_MAGIC + ident + cipher.encrypt(plaintext, [FILE_DOMAIN, config, path])
        result.append((name, path, plaintext, config, record))
        assert cipher.decrypt(record[22:], [FILE_DOMAIN, config, path]) == plaintext
        # A completely valid ciphertext becomes unauthentic in another Git path.
        try:
            cipher.decrypt(record[22:], [FILE_DOMAIN, config, path + b"-other"])
        except Exception:
            pass
        else:
            raise AssertionError("cross-path ciphertext transplantation authenticated")
        tampered = bytearray(record)
        tampered[-1] ^= 1
        try:
            cipher.decrypt(tampered[22:], [FILE_DOMAIN, config, path])
        except Exception:
            pass
        else:
            raise AssertionError("modified ciphertext unexpectedly authenticated")
    return result


def serialize(cases):
    return "".join(
        f"{name}\t{path.hex()}\t{plain.hex()}\t{config.hex()}\t{record.hex()}\n"
        for name, path, plain, config, record in cases
    )


class V3Reference(unittest.TestCase):
    def test_fixed_vectors(self):
        self.assertEqual((HERE / "vectors.tsv").read_text(), serialize(independent_cases()))

    def test_configuration_substitution_is_not_accepted(self):
        for _, path, _, config, record in independent_cases():
            altered = bytearray(config)
            altered[7] ^= 1
            key = hash_secret_raw(PASSWORD, SALT, time_cost=3, memory_cost=65536,
                                  parallelism=1, hash_len=64, type=Type.ID, version=19)
            with self.assertRaises(Exception):
                AESSIV(key).decrypt(record[22:], [FILE_DOMAIN, bytes(altered), path])

    def test_path_uniqueness_and_determinism(self):
        key = hash_secret_raw(PASSWORD, SALT, time_cost=3, memory_cost=65536,
                              parallelism=1, hash_len=64, type=Type.ID, version=19)
        cipher = AESSIV(key)
        config = independent_cases()[0][3]
        a = cipher.encrypt(b"same plaintext", [FILE_DOMAIN, config, b"a.secret"])
        b = cipher.encrypt(b"same plaintext", [FILE_DOMAIN, config, b"b.secret"])
        self.assertEqual(a, cipher.encrypt(b"same plaintext", [FILE_DOMAIN, config, b"a.secret"]))
        self.assertNotEqual(a, b)
        with self.assertRaises(Exception):
            cipher.decrypt(a, [FILE_DOMAIN, config, b"b.secret"])


if __name__ == "__main__":
    import sys
    if sys.argv[1:] == ["--write"]:
        (HERE / "vectors.tsv").write_text(serialize(independent_cases()))
    else:
        unittest.main()
