import Transcrypt.V3Policy

/-!
Proof-engineering tactics of the refinement proofs. They belong to the
verification layer: the independent specification (`Transcrypt.*`) neither
defines nor uses them.
-/

namespace Transcrypt.V3Verification

/-- Unfold the specification's named byte values and field lengths (the
    reducible `abbrev`s of `Transcrypt.V3Wire` and `Transcrypt.V3Policy`) to
    their numbers in the goal and every hypothesis, for `omega` and
    `scalar_tac`, which treat a named constant as an unknown, and for
    matching against the production constants' numeric `X_val` facts. It
    does nothing where no such name occurs. -/
macro "unfold_v3_bytes" : tactic =>
  `(tactic| try simp only [Transcrypt.V3Wire.configMagicLen, Transcrypt.V3Wire.fileMagicLen,
    Transcrypt.V3Wire.saltLen, Transcrypt.V3Wire.tagLen, Transcrypt.V3Wire.idLen,
    Transcrypt.V3Wire.configLen, Transcrypt.V3Wire.fileHeaderLen, Transcrypt.V3Wire.fileMinLen,
    Transcrypt.V3Policy.tab, Transcrypt.V3Policy.lf,
    Transcrypt.V3Policy.space, Transcrypt.V3Policy.digitZero, Transcrypt.V3Policy.digitNine,
    Transcrypt.V3Policy.lowerA, Transcrypt.V3Policy.lowerF, Transcrypt.V3Policy.hexLetterValue,
    Transcrypt.V3Policy.decimalRadix, Transcrypt.V3Policy.hexRadix, Transcrypt.V3Policy.opPing,
    Transcrypt.V3Policy.opEncrypt, Transcrypt.V3Policy.opDecrypt, Transcrypt.V3Policy.opStop,
    Transcrypt.V3Policy.keyLen, Transcrypt.V3Policy.keyFileLen, Transcrypt.V3Policy.sha1OidLen,
    Transcrypt.V3Policy.sha256OidLen, Transcrypt.V3Policy.maxSizeDigits,
    Transcrypt.V3Policy.pktHeaderLen, Transcrypt.V3Policy.modeLen, Transcrypt.V3Policy.oidStart,
    Transcrypt.V3Policy.oidEndLen, Transcrypt.V3Policy.entryFixedLen, Transcrypt.V3Policy.be32Len,
    Transcrypt.V3Policy.frameConfigStart, Transcrypt.V3Policy.frameLenStart,
    Transcrypt.V3Policy.frameHeaderLen] at *)

end Transcrypt.V3Verification
