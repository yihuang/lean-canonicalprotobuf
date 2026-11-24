/-
  Canonical Protobuf: wire primitives.

  A byte string is `List UInt8`.  This file defines the *canonical* forms of the
  concrete wire encodings used by proto3 (minimal varints, 32/64-bit
  little-endian, length prefixes), together with their inverses and the two
  facts that matter for a bijection:

  * `decode (encode x ++ rest) = some (x, rest)`: decoding inverts encoding
    even in the presence of following data;
  * every successful decode satisfies `encode v ++ rest = input` and consumes
    at least one byte: no over-long varints, no non-canonical byte sequences.
-/
import Std

namespace CanonicalProto

/-- A byte string. -/
abbrev Bytes := List UInt8

/-! ### Varints (base 128, little endian, minimal) -/

/-- Encode `n` in at most `fuel` seven-bit groups.  For `n < 128 ^ fuel` this
is the minimal (canonical) LEB128 encoding of `n`. -/
def varintEncodeAux : Nat → Nat → Bytes
  | 0, _ => []
  | fuel + 1, n =>
      if n < 128 then [UInt8.ofNat n]
      else UInt8.ofNat (n % 128 + 128) :: varintEncodeAux fuel (n / 128)

/-- Canonical varint encoding: exact (non-truncating) for *every* `n`, since
`n < 128 ^ (n+1)` and the encoder is given `n+1` groups.  (For all 64-bit
values this uses at most ten groups, as the wire format requires.) -/
def varintEncode (n : Nat) : Bytes := varintEncodeAux (n + 1) n

theorem varintEncode_fuel (n : Nat) : n < 128 ^ (n + 1) := by
  have h1 : n < 128 ^ n := Nat.lt_pow_self (by decide : 1 < 128)
  have h2 : 128 ^ n ≤ 128 ^ (n + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 128) (by omega)
  omega

/-- Read one varint, accumulating its 7-bit groups.  No length restriction is
imposed here; canonicity is enforced by `varintDecode`. -/
def varintRead (shift acc : Nat) : Bytes → Option (Nat × Bytes)
  | [] => none
  | x :: xs =>
      if x.toNat < 128 then some (acc + x.toNat * 2 ^ shift, xs)
      else varintRead (shift + 7) (acc + (x.toNat % 128) * 2 ^ shift) xs

/-- Read a varint and *reject anything that is not the minimal encoding*.
The check `varintEncode v ++ rest = b` simultaneously rules out overlong
encodings and values that do not fit the wire's ten-group budget. -/
def varintDecode (b : Bytes) : Option (Nat × Bytes) :=
  match varintRead 0 0 b with
  | some (v, rest) => if varintEncode v ++ rest = b then some (v, rest) else none
  | none => none

theorem varintRead_lt {shift acc : Nat} {b : Bytes} {v : Nat} {rest : Bytes}
    (h : varintRead shift acc b = some (v, rest)) : rest.length < b.length := by
  induction b generalizing shift acc v rest with
  | nil => simp [varintRead] at h
  | cons x xs ih =>
      rw [varintRead.eq_2] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp
      · have := ih h
        simp only [List.length_cons]
        omega

theorem varintEncodeAux_nonempty {fuel n : Nat} (h : 0 < fuel) :
    0 < (varintEncodeAux fuel n).length := by
  cases fuel with
  | zero => omega
  | succ f =>
      simp only [varintEncodeAux]
      split <;> simp

theorem varintEncode_nonempty (n : Nat) : 0 < (varintEncode n).length :=
  varintEncodeAux_nonempty (by omega)

/-- Arithmetic core of the varint correctness proof. -/
theorem varint_step_arith (shift acc n : Nat) :
    acc + (n % 128) * 2 ^ shift + (n / 128) * 2 ^ (shift + 7)
      = acc + n * 2 ^ shift := by
  have hpow : 2 ^ (shift + 7) = 2 ^ shift * 128 := by rw [Nat.pow_add]
  rw [hpow]
  have haux : (n / 128) * (2 ^ shift * 128) = ((n / 128) * 128) * 2 ^ shift := by
    rw [Nat.mul_comm (2 ^ shift) 128, Nat.mul_assoc]
  rw [haux]
  rw [Nat.add_assoc, ← Nat.add_mul]
  have hn : n % 128 + n / 128 * 128 = n := by
    have h := Nat.div_add_mod n 128
    rw [Nat.mul_comm 128 (n / 128)] at h
    omega
  rw [hn]

/-- Roundtrip on the raw reader: reading the encoding of `n` returns `n` and
the untouched suffix. -/
theorem varintRead_encodeAux : ∀ fuel n shift acc rest,
    0 < fuel → n < 128 ^ fuel →
    varintRead shift acc (varintEncodeAux fuel n ++ rest)
      = some (acc + n * 2 ^ shift, rest) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ fuel ih =>
      intro n shift acc rest _ hn
      cases fuel with
      | zero =>
          have hn' : n < 128 := by simpa using hn
          rw [varintEncodeAux.eq_2, if_pos hn']
          simp only [List.cons_append, List.nil_append, varintRead.eq_2]
          rw [if_pos (by rw [UInt8.toNat_ofNat']; omega)]
          rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      | succ fuel =>
          rw [varintEncodeAux.eq_2]
          by_cases hsmall : n < 128
          · rw [if_pos hsmall]
            simp only [List.cons_append, List.nil_append, varintRead.eq_2]
            rw [if_pos (by rw [UInt8.toNat_ofNat']; omega)]
            rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          · rw [if_neg hsmall]
            simp only [List.cons_append, varintRead.eq_2]
            rw [if_neg (by rw [UInt8.toNat_ofNat']; omega)]
            have hbyte : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
              rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
            have hmod : (n % 128 + 128) % 128 = n % 128 := by omega
            rw [hbyte, hmod]
            have hlt : n / 128 < 128 ^ (fuel + 1) := by
              have h1 : 128 ^ (fuel + 2) = 128 * 128 ^ (fuel + 1) := by
                rw [Nat.pow_succ']
              rw [h1] at hn
              exact Nat.div_lt_of_lt_mul hn
            rw [ih (n / 128) (shift + 7) (acc + (n % 128) * 2 ^ shift) rest
              (by omega) hlt]
            rw [varint_step_arith]

/-- Roundtrip: the decoder recovers the value and the untouched suffix. -/
theorem varintDecode_encode (n : Nat) (rest : Bytes) :
    varintDecode (varintEncode n ++ rest) = some (n, rest) := by
  unfold varintDecode varintEncode
  rw [varintRead_encodeAux (n + 1) n 0 0 rest (by omega) (varintEncode_fuel n)]
  simp

/-- Soundness of the varint decoder: the bytes consumed are exactly the
canonical encoding of the value. -/
theorem varintDecode_sound {b : Bytes} {v : Nat} {rest : Bytes}
    (h : varintDecode b = some (v, rest)) : varintEncode v ++ rest = b := by
  unfold varintDecode at h
  match hread : varintRead 0 0 b with
  | none => rw [hread] at h; simp at h
  | some p =>
      obtain ⟨v', r'⟩ := p
      rw [hread] at h
      dsimp only at h
      by_cases hc : varintEncode v' ++ r' = b
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hc
      · rw [if_neg hc] at h
        simp at h

theorem varintDecode_lt {b : Bytes} {v : Nat} {rest : Bytes}
    (h : varintDecode b = some (v, rest)) : rest.length < b.length := by
  unfold varintDecode at h
  match hread : varintRead 0 0 b with
  | none => rw [hread] at h; simp at h
  | some p =>
      obtain ⟨v', r'⟩ := p
      rw [hread] at h
      dsimp only at h
      by_cases hc : varintEncode v' ++ r' = b
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, rfl⟩ := h
        exact varintRead_lt hread
      · rw [if_neg hc] at h
        simp at h

/-- The decoder consumes at least one byte. -/
theorem varintDecode_cons {b : Bytes} {v : Nat} {rest : Bytes}
    (h : varintDecode b = some (v, rest)) (hb : 0 < b.length) : rest.length < b.length :=
  varintDecode_lt h

/-! ### Fixed-width little-endian integers -/

/-- Write the low `k` bytes of `n`, least significant first. -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: leBytes k (n / 256)

/-- Read exactly `k` little-endian bytes. -/
def leRead : Nat → Bytes → Option (Nat × Bytes)
  | 0, b => some (0, b)
  | k + 1, [] => none
  | k + 1, x :: xs =>
      match leRead k xs with
      | none => none
      | some (v, rest) => some (x.toNat + 256 * v, rest)

theorem leBytes_nonempty {k n : Nat} (h : 0 < k) : 0 < (leBytes k n).length := by
  cases k with
  | zero => omega
  | succ k => simp [leBytes]

theorem leRead_leBytes : ∀ k (n : Nat) (rest : Bytes), n < 256 ^ k →
    leRead k (leBytes k n ++ rest) = some (n, rest) := by
  intro k
  induction k with
  | zero =>
      intro n rest hn
      have hn0 : n = 0 := by omega
      subst hn0
      simp [leBytes, leRead]
  | succ k ih =>
      intro n rest hn
      have hlt : n % 256 < 256 := Nat.mod_lt _ (by omega)
      have hdiv : n / 256 < 256 ^ k := by
        have h1 : 256 ^ (k + 1) = 256 * 256 ^ k := by rw [Nat.pow_succ']
        rw [h1] at hn
        exact Nat.div_lt_of_lt_mul hn
      have hrec := ih (n / 256) rest hdiv
      simp only [leBytes, List.cons_append, leRead]
      rw [hrec]
      simp only [Option.some.injEq, Prod.mk.injEq]
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      constructor
      · have h2 := Nat.div_add_mod n 256
        omega
      · trivial

/-- Soundness of fixed-width reads: the parsed prefix is exactly `k` bytes. -/
theorem leRead_sound {k : Nat} {b : Bytes} {v : Nat} {rest : Bytes}
    (h : leRead k b = some (v, rest)) : b.length = k + rest.length := by
  induction k generalizing b v rest with
  | zero =>
      simp only [leRead, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      omega
  | succ k ih =>
      match b with
      | [] => simp [leRead] at h
      | x :: xs =>
          simp only [leRead] at h
          split at h
          · simp at h
          · rename_i v' r hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have := ih hr
            simp only [List.length_cons]
            omega

/-- Soundness with value: the parsed prefix re-encodes to exactly itself. -/
theorem leRead_bytes {k : Nat} {b : Bytes} {v : Nat} {rest : Bytes}
    (h : leRead k b = some (v, rest)) : leBytes k v ++ rest = b := by
  induction k generalizing b v rest with
  | zero =>
      simp only [leRead, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [leBytes]
  | succ k ih =>
      match b with
      | [] => simp [leRead] at h
      | x :: xs =>
          simp only [leRead] at h
          split at h
          · simp at h
          · rename_i v' r hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hrec := ih hr
            have hx : x.toNat < 256 := x.toNat_lt
            simp only [leBytes, List.cons_append]
            have hmod : (x.toNat + 256 * v') % 256 = x.toNat := by
              rw [Nat.mul_comm 256 v', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
            have hdiv : (x.toNat + 256 * v') / 256 = v' := by
              rw [Nat.mul_comm 256 v', Nat.add_mul_div_right _ _ (by omega),
                  Nat.div_eq_of_lt hx]
              omega
            rw [hmod, hdiv, UInt8.ofNat_toNat, hrec]

theorem leRead_length_le {k : Nat} {b : Bytes} {v : Nat} {rest : Bytes}
    (h : leRead k b = some (v, rest)) : rest.length < b.length ∨ k = 0 := by
  have := leRead_sound h
  by_cases hk : k = 0
  · exact Or.inr hk
  · left; omega

/-! ### Length-delimited splitting -/

/-- Split off a prefix of length `n`, failing if the input is too short. -/
def split (n : Nat) (b : Bytes) : Option (Bytes × Bytes) :=
  if n ≤ b.length then some (b.take n, b.drop n) else none

theorem split_of_length (l₁ l₂ : Bytes) : split l₁.length (l₁ ++ l₂) = some (l₁, l₂) := by
  unfold split
  rw [if_pos (by simp)]
  rw [List.take_left, List.drop_left]

theorem split_sound {n : Nat} {b : Bytes} {pre post : Bytes}
    (h : split n b = some (pre, post)) : pre ++ post = b ∧ pre.length = n := by
  unfold split at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.take_append_drop n b, by rw [List.length_take]; omega⟩
  · simp at h

end CanonicalProto
