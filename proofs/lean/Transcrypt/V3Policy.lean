import Transcrypt.V3Policy.Constants
import Transcrypt.V3Policy.Paths
import Transcrypt.V3Policy.Authentication
import Transcrypt.V3Policy.Lifecycle
import Transcrypt.V3Policy.Git
import Transcrypt.V3Policy.Credentials

/-!
Independent specification of the v3 protocol *decisions*. This module only
gathers its parts, each importing only what it builds on:

* `Constants`: the ASCII encoding, size bounds, named bytes and lengths;
* `Paths`: canonical protected paths and their selection by Git's
  `filter` attribute;
* `Authentication`: the abstract suite, sealing, opening and the keyless
  envelope;
* `Lifecycle`: what hydrate, lock, smudge and the pre-commit repair do;
* `Git`: index and tree records, object names, snapshots, pkt-lines and
  `cat-file --batch` replies;
* `Credentials`: the agent's requests and framing, and the stored key.

Written from `docs/verification/specs/V3-AUTHENTICATED-P0.md`, not from the
Rust source. Aeneas refinement theorems in `proofs/aeneas/v3` relate the
production Rust core to these definitions.

Cryptography is abstract. `Suite` models one derived key: `siv ad pt` is the
deterministic AES-SIV output (16-byte tag then ciphertext) for the ordered
associated-data list `ad`, and `digest16` is SHA-256 truncated to 16 bytes.
The only algebraic facts assumed are functional ones that hold for every
deterministic SIV construction (length and injectivity for fixed `ad`).
Unforgeability -- that only a key holder can produce `siv ad pt` -- is the
*computational* assumption under which the theorems below have security
meaning; it is not, and cannot be, a Lean theorem here.
-/
