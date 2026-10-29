#!/usr/bin/env bash
# `ok` and `bad` only print (and record a failure), so `test && ok || bad`
# reports exactly one of them.
# shellcheck disable=SC2015
#
# D-01/D-02 feasibility probe: can a reviewed deterministic authenticated
# encryption scheme be built from the plain OpenSSL CLI (the only runtime
# allowed for the Bash implementation) without putting secret keys or
# passphrases into process arguments or environment variables?
#
# This script is evidence collection for the decision register
# (docs/verification/10-decisions-and-blockers.md), not a protocol
# implementation. It is safe to run anywhere: it writes to $TMPDIR only,
# uses no user credentials, and never modifies a repository.
#
# Usage: bash contrib/verification/d02-openssl-cli-probe.sh [openssl-path]
#
# Test-vector provenance (see docs/verification/reference/d01-d02-feasibility.md):
#   - RFC 7914 section 11 (PBKDF2-HMAC-SHA256) and RFC 4231 (HMAC-SHA256)
#     published vectors.
#   - Ciphertext constants marked PYCREPTO were computed independently with
#     pycryptodome 4.1.0 (Python 3) on 2026-10-24, not with OpenSSL.
#
set -u

O=${1:-openssl}
TMPDIR_LOCAL=$(mktemp -d)
trap 'rm -rf "$TMPDIR_LOCAL"' EXIT

FAIL=0
ok() { printf 'PASS %s\n' "$*"; }
bad() {
	printf 'FAIL %s\n' "$*"
	FAIL=1
}
note() { printf -- '-- %s\n' "$*"; }

hex() { od -A n -t x1 | tr -d ' \n'; }

# ---------------------------------------------------------------------------
note '0. toolchain versions'
"$O" version
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
note '1. AEAD ciphers exposed by the enc app'
cipher_list=$("$O" enc -list 2>/dev/null)
for c in -aes-256-siv -aes-128-siv -aes-256-gcm -aes-256-ccm; do
	if printf '%s\n' "$cipher_list" | grep -qx -- "$c"; then
		ok "enc exposes $c (unexpected on 3.0/3.5)"
	else
		ok "enc does not expose $c"
	fi
done
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
note '2. PBKDF2-HMAC-SHA256: openssl kdf app vs RFC 7914 (section 11)'
# RFC 7914 vector 1: P="passwd" S="salt" c=1 dkLen=64
rfc7914_v1='55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783'
kdf_rc=0
kdf1=$("$O" kdf -keylen 64 -digest SHA256 -kdfopt pass:passwd -kdfopt salt:salt -kdfopt iter:1 PBKDF2 2>/dev/null) || kdf_rc=$?
kdf1=$(printf '%s' "$kdf1" | tr -d ':' | tr 'A-F' 'a-f')
if [ "$kdf_rc" = 0 ]; then
	[ "$kdf1" = "$rfc7914_v1" ] &&
		ok "openssl kdf PBKDF2 matches RFC 7914 vector 1" ||
		bad "openssl kdf PBKDF2 mismatch (got $kdf1)"
else
	note 'openssl kdf not available on this build (OpenSSL 1.1 / LibreSSL); skipping'
fi
# RFC 7914 vector 2: P="Password" S="NaCl" c=80000 dkLen=64
rfc7914_v2='4ddcd8f60b98be21830cee5ef22701f9641a4418d04c0414aeff08876b34ab56a1d425a1225833549adb841b51c9b3176a272bdebba1d078478f62b397f33c8d'
kdf_rc=0
kdf2=$("$O" kdf -keylen 64 -digest SHA256 -kdfopt pass:Password -kdfopt salt:NaCl -kdfopt iter:80000 PBKDF2 2>/dev/null) || kdf_rc=$?
kdf2=$(printf '%s' "$kdf2" | tr -d ':' | tr 'A-F' 'a-f')
if [ "$kdf_rc" = 0 ]; then
	[ "$kdf2" = "$rfc7914_v2" ] &&
		ok "openssl kdf PBKDF2 matches RFC 7914 vector 2" ||
		bad "openssl kdf PBKDF2 mismatch (got $kdf2)"
else
	note 'openssl kdf not available on this build; skipping'
fi
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
note '3. enc -pbkdf2: passphrase from file/fd, PBKDF2 key derivation'
# Test passphrase is a fixed constant, written to a 0600 file and to a pipe.
printf '%s' 'd02-probe-passphrase-constant-2026' >"$TMPDIR_LOCAL/pw"
chmod 0600 "$TMPDIR_LOCAL/pw"
HAVE_PBKDF2=0
if "$O" enc -e -aes-256-cbc -pbkdf2 -iter 1000 -md sha256 -S 0011223344556677 -pass file:"$TMPDIR_LOCAL/pw" -in /dev/null >/dev/null 2>&1; then
	ok "enc accepts -pbkdf2 (OpenSSL 3.0+ feature)"
	HAVE_PBKDF2=1
else
	note 'enc -pbkdf2 not available on this build (OpenSSL 1.1 / LibreSSL); skipping section 3'
fi
if [ "$HAVE_PBKDF2" = 1 ] && "$O" enc -e -aes-256-cbc -pbkdf2 -iter 1000 -md sha256 -S 0011223344556677 -pass file:"$TMPDIR_LOCAL/pw" -in /dev/null 2>/dev/null | hex >"$TMPDIR_LOCAL/pbkdf2_file.hex"; then
	# (a) determinism
	"$O" enc -e -aes-256-cbc -pbkdf2 -iter 1000 -md sha256 -S 0011223344556677 -pass file:"$TMPDIR_LOCAL/pw" -in /dev/null 2>/dev/null | hex >"$TMPDIR_LOCAL/pbkdf2_again.hex"
	[ "$(cat "$TMPDIR_LOCAL/pbkdf2_file.hex")" = "$(cat "$TMPDIR_LOCAL/pbkdf2_again.hex")" ] &&
		ok "enc -pbkdf2 is deterministic" || bad "enc -pbkdf2 nondeterministic"
	# (b) file: vs fd: channel equivalence
	"$O" enc -e -aes-256-cbc -pbkdf2 -iter 1000 -md sha256 -S 0011223344556677 -pass fd:3 -in /dev/null 3<"$TMPDIR_LOCAL/pw" 2>/dev/null | hex >"$TMPDIR_LOCAL/pbkdf2_fd.hex"
	[ "$(cat "$TMPDIR_LOCAL/pbkdf2_file.hex")" = "$(cat "$TMPDIR_LOCAL/pbkdf2_fd.hex")" ] &&
		ok "enc -pbkdf2: fd: channel identical to file: channel" ||
		bad "enc -pbkdf2: fd: channel differs from file:"
	# (c) matches the independently computed ciphertext (PYCREPTO)
	#     AES-256-CBC of a zero-length input (one PKCS7 pad block);
	#     key = PBKDF2-HMAC-SHA256(pw, 0011223344556677, 1000, 32),
	#     iv  = PBKDF2-HMAC-SHA256(pw, 0011223344556677, 1000, 48)[32:48]
	#     OpenSSL 1.1 writes `Salted__` and the salt before the ciphertext
	#     even with an explicit -S (3.0 does not); compare the ciphertext.
	pycrepto_expected='f0c944791e0817f81674ed5e8868d9af'
	salted_header="$(printf 'Salted__' | hex)0011223344556677"
	pbkdf2_ciphertext=$(cat "$TMPDIR_LOCAL/pbkdf2_file.hex")
	pbkdf2_ciphertext=${pbkdf2_ciphertext#"$salted_header"}
	[ "$pbkdf2_ciphertext" = "$pycrepto_expected" ] &&
		ok "enc -pbkdf2 ciphertext matches independent (pycryptodome) computation" ||
		bad "enc -pbkdf2 ciphertext differs from independent computation"
	# (d) differs from the legacy EVP_BytesToKey-MD5 derivation
	legacy=$(
		printf '%s' 'd02-probe-passphrase-constant-2026' >"$TMPDIR_LOCAL/pw2"
		"$O" enc -e -aes-256-cbc -md MD5 -S 0011223344556677 -pass file:"$TMPDIR_LOCAL/pw2" -in /dev/null 2>/dev/null | hex
	)
	[ "$(cat "$TMPDIR_LOCAL/pbkdf2_file.hex")" != "$legacy" ] &&
		ok "enc -pbkdf2 derivation differs from legacy MD5 path" ||
		bad "enc -pbkdf2 identical to legacy MD5 derivation"
fi
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
note '4. raw-key input: enc -nosalt -md sha256 -pass file:/fd:'
# The file holds 64 hex ASCII characters; enc uses the file content verbatim
# as the passphrase of EVP_BytesToKey(SHA-256, pass, salt=NULL, iter=1).
printf '%s' '00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff' >"$TMPDIR_LOCAL/key"
chmod 0600 "$TMPDIR_LOCAL/key"
data='The quick brown fox jumps over the lazy dog'
# CTR: no padding; key = D1 = SHA256(pass); iv = D2[:16]; 16-byte BE counter
# Expected ciphertext (PYCREPTO, pycryptodome 4.1.0, 2026-10-24):
ctr_expected='28f0f2c42edd6d60ecd1699d5c4c9921f03b6ba0fcb3d0ac0780c2055f9c4c3b00ad12580d2447257a7df00f'
got_ctr=$("$O" enc -e -aes-256-ctr -nosalt -md sha256 -pass file:"$TMPDIR_LOCAL/key" <<<"$data" 2>/dev/null | hex)
[ "$got_ctr" = "$ctr_expected" ] &&
	ok "enc CTR (EVP_BytesToKey expansion) matches independent computation" ||
	bad "enc CTR differs from independent computation (got ${got_ctr:0:32}...)"
# ECB: PKCS7 padding; same key derivation
ecb_expected='c31d48ab9f17da6cfa06597fe49b2ef26d292174145176e5e6ebb0e35ee6d18c5a6b73c3526953f3d0d7cfc12cfeab3b'
got_ecb=$("$O" enc -e -aes-256-ecb -nosalt -md sha256 -pass file:"$TMPDIR_LOCAL/key" <<<"$data" 2>/dev/null | hex)
[ "$got_ecb" = "$ecb_expected" ] &&
	ok "enc ECB (EVP_BytesToKey expansion) matches independent computation" ||
	bad "enc ECB differs from independent computation (got ${got_ecb:0:32}...)"
# fd: channel equivalence for the raw-key path
got_fd=$("$O" enc -e -aes-256-ctr -nosalt -md sha256 -pass fd:3 <<<"$data" 3<"$TMPDIR_LOCAL/key" 2>/dev/null | hex)
[ "$got_ctr" = "$got_fd" ] &&
	ok "raw-key path: fd: channel identical to file: channel" ||
	bad "raw-key path: fd: channel differs from file:"
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
note '5. process inspection: secrets in child argv/environ'
# Run a short openssl invocation and sample /proc/<pid>/{cmdline,environ}
# while it is alive. Only meaningful on Linux; elsewhere it reports "n/a".
if [ "$(uname)" = 'Linux' ] && [ -d /proc ]; then
	# (a) -pass file:/fd: must NOT expose the passphrase in argv or environ.
	# 1M PBKDF2 iterations keeps the child alive long enough to sample it.
	"$O" enc -e -aes-256-cbc -pbkdf2 -iter 1000000 -md sha256 -S 0011223344556677 -pass fd:3 -in /dev/null 3<"$TMPDIR_LOCAL/pw" >/dev/null 2>&1 &
	pid=$!
	found=0
	for _ in $(seq 1 100); do
		{
			[ -r "/proc/$pid/cmdline" ] && tr '\0' ' ' <"/proc/$pid/cmdline"
			echo
			[ -r "/proc/$pid/environ" ] && tr '\0' '\n' <"/proc/$pid/environ"
		} 2>/dev/null |
			grep -qF 'd02-probe-passphrase' && found=1
		kill -0 "$pid" 2>/dev/null || break
		sleep 0.01
	done
	wait "$pid" 2>/dev/null
	[ "$found" = 0 ] &&
		ok "passphrase NOT visible in child argv/environ for -pass fd: (1M iterations)" ||
		bad "passphrase WAS visible in child argv/environ for -pass fd:"
	# (b) control: -macopt hexkey puts the key in argv (the exposure we
	# must avoid in the product path). Informational only: if the process
	# is too fast to sample, the check reports n/a rather than failing.
	"$O" dgst -sha256 -macopt hexkey:0102030405 -in /dev/null >/dev/null 2>&1 &
	pid=$!
	found=2
	for _ in $(seq 1 100); do
		if [ -r "/proc/$pid/cmdline" ]; then
			tr '\0' ' ' 2>/dev/null <"/proc/$pid/cmdline" | grep -qF 'hexkey:0102030405' && found=1
		fi
		kill -0 "$pid" 2>/dev/null || break
		sleep 0.01
	done
	wait "$pid" 2>/dev/null
	if [ "$found" = 1 ]; then
		ok "control: -macopt hexkey DOES expose key in argv (documented exposure)"
	else
		note 'control: hexkey not sampled (process too fast); n/a'
	fi
else
	note 'not Linux; /proc inspection skipped (n/a)'
fi
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
note '6. keyed MAC channels'
# HMAC-SHA256, RFC 4231 test case 2 (key="Jefe",
# data="what do ya want for nothing?")
rfc4231_t2='5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843'
printf '%s' 'what do ya want for nothing?' >"$TMPDIR_LOCAL/msg"
mac_rc=0
mac_out=$("$O" mac -macopt hexkey:4a656665 -digest SHA256 -in "$TMPDIR_LOCAL/msg" HMAC 2>/dev/null) || mac_rc=$?
mac_out=$(printf '%s' "$mac_out" | tr 'A-F' 'a-f')
if [ "$mac_rc" = 0 ]; then
	[ "$mac_out" = "$rfc4231_t2" ] &&
		ok "HMAC-SHA256 via mac app matches RFC 4231 case 2 (key in argv only)" ||
		bad "HMAC via mac app mismatch (got ${mac_out:-<empty>})"
else
	note 'mac app HMAC unavailable on this build (n/a)'
fi
# CMAC: available on some OpenSSL 3.x builds; on 3.0.13 and 3.5.9 the
# cipher fetch in the mac app fails (documented there)
cmac_rc=0
cmac_out=$("$O" mac -macopt hexkey:2b7e151628aed2a6abf7158809cf4f3c -cipher AES-256 -in /dev/null CMAC 2>/dev/null) || cmac_rc=$?
cmac_out=$(printf '%s' "$cmac_out" | tr 'A-F' 'a-f')
if [ "$cmac_rc" = 0 ]; then
	[ "$cmac_out" = 'bb1d6929e959374828118c8bee8b18f2' ] &&
		ok "CMAC via mac app matches SP 800-38B example 1" ||
		bad "CMAC via mac app mismatch (got ${cmac_out:-<empty>})"
else
	note 'CMAC via mac app unavailable/broken on this build (recorded: 3.0.13, 3.5.9)'
fi
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
note '7. kdf parameter value semantics (informational; classifies behavior)'
# Whether the kdf app treats pass/salt values as literal text or expands
# value prefixes (hex:/file:/env:). On 3.0.13 and 3.5.9 only *key-name*
# prefixes (hexpass:, hexsalt: ...) decode; value prefixes are literal.
# These checks record which regime this build is in; they never fail, so
# a future OpenSSL that adds file-based kdf secrets changes the recorded
# classification (and therefore the D-02 evidence), not the exit status.
if "$O" kdf -keylen 4 -digest SHA256 -kdfopt pass:x -kdfopt salt:x -kdfopt iter:1 PBKDF2 >/dev/null 2>&1; then
	# (a) salt:hex: vs hexsalt: — equal iff the value is hex-decoded
	shex=$("$O" kdf -keylen 4 -digest SHA256 -kdfopt pass:x -kdfopt salt:hex:0011223344556677 -kdfopt iter:1 PBKDF2 2>/dev/null | tr -d ':' | tr 'A-F' 'a-f')
	hesalt=$("$O" kdf -keylen 4 -digest SHA256 -kdfopt pass:x -kdfopt hexsalt:0011223344556677 -kdfopt iter:1 PBKDF2 2>/dev/null | tr -d ':' | tr 'A-F' 'a-f')
	if [ -n "$shex" ] && [ -n "$hesalt" ]; then
		if [ "$shex" = "$hesalt" ]; then
			note 'kdf salt: value prefix IS hex-decoded on this build'
		else
			note 'kdf salt: value prefix is LITERAL text (hexsalt: key-name prefix decodes)'
		fi
	else
		note 'kdf hexsalt: not supported on this build; classification n/a'
	fi
	# (b) pass:file: vs hexpass:<hex of the literal string> — equal iff literal
	printf '%s' 'd02-kdf-probe-text' >"$TMPDIR_LOCAL/ktxt"
	litstr="file:$TMPDIR_LOCAL/ktxt"
	lithex=$(printf '%s' "$litstr" | hex)
	if [ -n "$lithex" ]; then
		pfile=$("$O" kdf -keylen 4 -digest SHA256 -kdfopt "pass:$litstr" -kdfopt salt:x -kdfopt iter:1 PBKDF2 2>/dev/null | tr -d ':' | tr 'A-F' 'a-f')
		pexp=$("$O" kdf -keylen 4 -digest SHA256 -kdfopt "hexpass:$lithex" -kdfopt salt:x -kdfopt iter:1 PBKDF2 2>/dev/null | tr -d ':' | tr 'A-F' 'a-f')
		if [ -n "$pfile" ] && [ -n "$pexp" ]; then
			if [ "$pfile" = "$pexp" ]; then
				note 'kdf pass:file: is NOT expanded (literal string) on this build'
			else
				note 'kdf pass:file: IS file-expanded on this build (secret channel!)'
			fi
		else
			note 'kdf file/hexpass comparison n/a on this build'
		fi
	else
		note 'kdf hexpass: not supported on this build; classification n/a'
	fi
else
	note 'openssl kdf not available on this build; section 7 n/a'
fi
# ---------------------------------------------------------------------------

note 'summary'
if [ "$FAIL" = 0 ]; then
	printf 'All checks passed on this toolchain.\n'
else
	printf 'One or more checks FAILED on this toolchain.\n'
fi
exit "$FAIL"
