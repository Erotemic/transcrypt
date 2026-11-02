import Transcrypt.V3WireCodec

/-!
# Constants of the v3 specification

The ASCII encoding of names, the size bounds, and the named bytes and field
lengths of the Git and credential-agent formats.
-/

namespace Transcrypt.V3Policy

open Transcrypt.V3Wire

def ascii (s : String) : List Nat := s.toList.map Char.toNat

/-! ## Constants -/

def maxFile : Nat := 16 * 1024 * 1024
def maxPath : Nat := 4096
def maxRecord : Nat := maxFile + fileMinLen
def slash : Nat := 47
def dot : Nat := 46

/-! ASCII bytes of the Git and agent formats. They are reducible, so `decide`,
`simp` and definitional unfolding see the numbers. -/

abbrev tab : Nat := 9
abbrev lf : Nat := 10
abbrev space : Nat := 32
/-- `0` and `9`, `a` and `f`: the ends of the decimal and hexadecimal digit
    ranges; `a` is the hexadecimal digit worth `hexLetterValue`. -/
abbrev digitZero : Nat := 48
abbrev digitNine : Nat := 57
abbrev lowerA : Nat := 97
abbrev lowerF : Nat := 102
abbrev hexLetterValue : Nat := 10
/-- The radixes of decimal sizes and hexadecimal pkt-line lengths. -/
abbrev decimalRadix : Nat := 10
abbrev hexRadix : Nat := 16
/-- The credential agent's opcodes `P`, `E`, `D` and `X`. -/
abbrev opPing : Nat := 80
abbrev opEncrypt : Nat := 69
abbrev opDecrypt : Nat := 68
abbrev opStop : Nat := 88
/-- The derived key's length, and the stored key file: the config it was
    unlocked for, the key, then the key's check value (`Credentials`): the
    tag and the encryption of a `keyCheckPlaintextLen`-byte constant. -/
abbrev keyLen : Nat := 64
abbrev keyCheckPlaintextLen : Nat := 23
abbrev keyCheckLen : Nat := tagLen + keyCheckPlaintextLen
abbrev keyCheckStart : Nat := configLen + keyLen
abbrev keyFileLen : Nat := keyCheckStart + keyCheckLen
/-- Git object names: SHA-1 or SHA-256, in hexadecimal digits. -/
abbrev sha1OidLen : Nat := 40
abbrev sha256OidLen : Nat := 64
/-- The most decimal digits of a blob size Git's reply may have. -/
abbrev maxSizeDigits : Nat := 19
/-- A pkt-line header: its length in four hexadecimal digits. -/
abbrev pktHeaderLen : Nat := 4
/-- A Git file mode, such as `100644`. -/
abbrev modeLen : Nat := 6
/-- Where an index or tree record's object id starts: after the mode and a SP. -/
abbrev oidStart : Nat := modeLen + 1
/-- The bytes `SP 0 TAB` between a record's object id and its path. -/
abbrev oidEndLen : Nat := 3
/-- The bytes of an index or tree record besides its object id and path. -/
abbrev entryFixedLen : Nat := oidStart + oidEndLen
/-- A big-endian `u32` (`be32`). -/
abbrev be32Len : Nat := 4
/-- Where an agent request header's config starts: after the one-byte opcode;
    its path length follows the config. -/
abbrev frameConfigStart : Nat := 1
abbrev frameLenStart : Nat := frameConfigStart + configLen
abbrev frameHeaderLen : Nat := frameLenStart + be32Len

end Transcrypt.V3Policy
