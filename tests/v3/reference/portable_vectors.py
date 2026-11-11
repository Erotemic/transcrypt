#!/usr/bin/env python3
"""Independent byte vectors for the portable v3 profiles 2 and 3.

Written from docs/verification/specs/V3-PORTABLE-PROFILES.md with Python's
hashlib (scrypt, PBKDF2-HMAC-SHA256, SHA-256) and the `cryptography`
package's RFC 5297 AESSIV. No Transcrypt code, Bash or OpenSSL CLI is used.

    python3 portable_vectors.py            # check portable-vectors.tsv
    python3 portable_vectors.py --write    # regenerate it

Development/test only (needs cryptography>=42 for empty AES-SIV plaintexts).
The Rust test `portable_profiles_match_the_independent_vectors` and the Bash
suite `tests/v3/bash/test_reference.sh` check both clients against this file.
"""
import hashlib
import sys
from pathlib import Path

from cryptography.hazmat.primitives.ciphers.aead import AESSIV

HERE = Path(__file__).resolve().parent
OUT = HERE / "portable-vectors.tsv"
PASSWORD = b"correct horse battery staple"
SALT = bytes(range(32))
CONFIG_DOMAIN = b"transcrypt/v3/config"
FILE_DOMAIN = b"transcrypt/v3/file"
CONFIG_FAMILY = b"TCFG3\x00"
FILE_MAGIC = b"TV3F\x00\x01"
KEY_CHECK_PATH = b".transcrypt/key-check"
KEY_CHECK_PLAINTEXT = b"transcrypt/v3/key-check"


def derive(profile, password, salt):
    if profile == 2:
        return hashlib.scrypt(password, salt=salt, n=32768, r=8, p=1, maxmem=67108864 + 4096, dklen=64)
    if profile == 3:
        return hashlib.pbkdf2_hmac("sha256", password, salt, 600000, dklen=64)
    raise ValueError(profile)


# (name, path, plaintext). Plaintext lengths cover S2V's padded (< 16) and
# xor-end (>= 16) branches and CMAC's block boundaries.
SAMPLES = [
    ("empty", b"demo.secret", b""),
    ("one", b"demo.secret", b"A"),
    ("fifteen", b"demo.secret", b"0123456789abcde"),
    ("sixteen", b"demo.secret", b"0123456789abcdef"),
    ("seventeen", b"demo.secret", b"0123456789abcdefg"),
    ("thirty-two", b"dir/sub/x.env", bytes(range(32))),
    ("thirty-three", b"dir/sub/x.env", bytes(range(33))),
    ("binary-nul", b"raw/blob.bin", bytes([0, 255, 0, 10, 13, 0, 128, 0, 0])),
    ("non-utf8-path", b"raw/\xff\xfe-name.secret", b"bytes under a non-UTF-8 path\n"),
    ("unicode-path", "données/clé ü.env".encode(), "unicode plaintext ✓\n".encode()),
    ("spaces-path", b"with space/a b.txt", b"x\n"),
    ("long", b"big/long.dat", bytes((i * 7 + 3) % 256 for i in range(1000))),
]


def cases():
    rows = []
    for profile in (2, 3):
        key = derive(profile, PASSWORD, SALT)
        cipher = AESSIV(key)
        prefix = CONFIG_FAMILY + bytes([profile]) + SALT
        config = prefix + cipher.encrypt(b"", [CONFIG_DOMAIN, prefix])
        assert len(config) == 55
        check = cipher.encrypt(KEY_CHECK_PLAINTEXT, [FILE_DOMAIN, config, KEY_CHECK_PATH])
        ident = hashlib.sha256(config).digest()[:16]
        for name, path, plaintext in SAMPLES:
            record = FILE_MAGIC + ident + cipher.encrypt(plaintext, [FILE_DOMAIN, config, path])
            assert cipher.decrypt(record[22:], [FILE_DOMAIN, config, path]) == plaintext
            rows.append((profile, name, PASSWORD, SALT, key, config, check, path, plaintext, record))
    return rows


def serialize(rows):
    header = ("# Independent portable-profile vectors (portable_vectors.py: hashlib scrypt/PBKDF2 + "
              "cryptography AESSIV). Columns: profile, name, password, salt, key, config, key-check, "
              "path, plaintext, record; all hex, '-' for empty.\n")
    hx = lambda b: b.hex() if b else "-"
    return header + "".join(
        "\t".join([str(p), n] + [hx(v) for v in rest]) + "\n" for p, n, *rest in rows
    )


def main():
    text = serialize(cases())
    if "--write" in sys.argv[1:]:
        OUT.write_text(text)
        print(f"wrote {OUT}")
        return 0
    if OUT.read_text() != text:
        print(f"{OUT} differs from the independent computation", file=sys.stderr)
        return 1
    print(f"{OUT.name}: {text.count(chr(10)) - 1} vectors match")
    return 0


if __name__ == "__main__":
    sys.exit(main())
