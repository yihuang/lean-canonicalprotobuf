/-
  Canonical Protobuf: the bijection.

  Canonical messages of a schema are the messages `m` with
  `canonMsg s m = true`.  `encode` maps them to bytes and `decode` maps bytes
  back.  We prove:

  * *soundness*: if `decode` returns `m` then `encode m` is exactly the input
    (`decode_sound`), hence `decode` is injective;
  * *completeness*: `decode (encode m) = some m` for every canonical `m`
    (`decode_encode`);
  * consequently `encode`/`decode` are mutually inverse and `encode` is
    injective — a bijection between canonical messages and the byte strings
    that the decoder accepts.
-/
import CanonicalProtobuf.Proofs

namespace CanonicalProto

/-- A message known to be canonical. -/
structure CanonicalMsg (s : Schema) where
  val : Msg
  canon : canonMsg s val = true

/-- The canonical encoder, as a function on canonical messages. -/
def encode (s : Schema) (m : CanonicalMsg s) : Bytes := encodeMsg s m.val

/-- The strict decoder. -/
def decode (s : Schema) (b : Bytes) : Option (CanonicalMsg s) :=
  match h : decodeBodyCanon s b with
  | none => none
  | some m =>
      if hc : canonMsg s m = true then some ⟨m, hc⟩ else none

/-! ### Soundness -/

/-- The decoder only ever returns messages whose re-encoding is the input. -/
theorem decode_sound {s : Schema} {b : Bytes} {m : CanonicalMsg s}
    (h : decode s b = some m) : encode s m = b := by
  unfold decode at h
  cases hd : decodeBodyCanon s b with
  | none => rw [hd] at h; simp at h
  | some m' =>
      rw [hd] at h
      try dsimp only at h
      by_cases hc : canonMsg s m' = true
      · rw [dif_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h
        exact decodeBodyCanon_sound hd
      · rw [dif_neg hc] at h; simp at h

/-- The decoder is injective on canonical byte strings. -/
theorem decode_injective {s : Schema} {b1 b2 : Bytes} {m : CanonicalMsg s}
    (h1 : decode s b1 = some m) (h2 : decode s b2 = some m) : b1 = b2 := by
  rw [← decode_sound h1, ← decode_sound h2]

/-! ### Completeness -/

/-- `decodeBodyCanon` accepts the canonical encoding of every canonical
message. -/
theorem decodeBodyCanon_encodeMsg {s : Schema} {m : Msg} (hc : canonMsg s m = true) :
    decodeBodyCanon s (encodeMsg s m) = some m := by
  unfold decodeBodyCanon
  rw [decodeBody_complete s 0 m hc (canonMsg_orderOk hc)]
  simp [hc]

/-- The decoder inverts the encoder on canonical messages. -/
theorem decode_encode {s : Schema} (m : CanonicalMsg s) :
    decode s (encode s m) = some m := by
  unfold decode encode
  rw [decodeBodyCanon_encodeMsg m.canon]
  simp [m.canon]

/-! ### The bijection -/

/-- `encode` and `decode` are mutually inverse and `encode` is injective: a
bijection between canonical messages and the byte strings accepted by the
decoder. -/
theorem bijection (s : Schema) :
    (∀ m : CanonicalMsg s, decode s (encode s m) = some m) ∧
    (∀ (b : Bytes) (m : CanonicalMsg s), decode s b = some m → encode s m = b) ∧
    (∀ (m1 m2 : CanonicalMsg s), encode s m1 = encode s m2 → m1 = m2) := by
  refine ⟨decode_encode, fun b m h => decode_sound h, ?_⟩
  intro m1 m2 heq
  have h1 := decode_encode m1
  have h2 := decode_encode m2
  rw [heq] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- Every canonical message is recovered, and every accepted byte string is the
encoding of a unique canonical message. -/
theorem decode_eq_some_iff (s : Schema) (b : Bytes) (m : CanonicalMsg s) :
    decode s b = some m ↔ encode s m = b := by
  constructor
  · exact decode_sound
  · intro h
    rw [← h]
    exact decode_encode m

end CanonicalProto
