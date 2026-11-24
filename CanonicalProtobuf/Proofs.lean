/-
  Canonical Protobuf: correctness.

  * soundness: every byte string accepted by the decoder re-encodes to itself;
  * completeness: every canonical message is accepted and recovered.

  Together these establish a bijection between canonical messages and
  canonical byte strings.
-/
import CanonicalProtobuf.Decode

namespace CanonicalProto

/-! ### Numeric bounds -/

theorem ok_i32_lt {st : ScalarTy} {v : Nat} (hc : st.cls = .i32)
    (h : SVal.ok st (.n v) = true) : v < 2 ^ 32 := by
  simp only [SVal.ok, hc, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem ok_i64_lt {st : ScalarTy} {v : Nat} (hc : st.cls = .i64)
    (h : SVal.ok st (.n v) = true) : v < 2 ^ 64 := by
  simp only [SVal.ok, hc, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem packedOf_nonempty {st : ScalarTy} {v : SVal} (hp : st.packable = true)
    (hv : SVal.ok st v = true) : 0 < (packedOf st v).length := by
  cases hc : st.cls with
  | varint =>
      cases v with
      | n v => simp only [packedOf, hc]; exact varintEncode_nonempty v
      | s b => simp [SVal.ok, hc] at hv
  | i32 =>
      cases v with
      | n v => simp only [packedOf, hc]; exact leBytes_nonempty (by omega)
      | s b => simp [SVal.ok, hc] at hv
  | i64 =>
      cases v with
      | n v => simp only [packedOf, hc]; exact leBytes_nonempty (by omega)
      | s b => simp [SVal.ok, hc] at hv
  | len => simp [ScalarTy.packable, hc] at hp

theorem packedOf_eq_payloadOf {st : ScalarTy} {v : SVal} (h : st.packable = true) :
    packedOf st v = payloadOf st v := by
  cases hc : st.cls with
  | varint | i32 | i64 => cases v <;> simp [packedOf, payloadOf, hc]
  | len => simp [ScalarTy.packable, hc] at h

theorem packConcat_cons (st : ScalarTy) (v : SVal) (vs : List SVal) :
    packConcat st (v :: vs) = packedOf st v ++ packConcat st vs := rfl

theorem packConcat_length_ge {st : ScalarTy} (hp : st.packable = true) {vs : List SVal}
    (hall : ∀ v ∈ vs, SVal.ok st v = true) : vs.length ≤ (packConcat st vs).length := by
  induction vs with
  | nil => simp [packConcat]
  | cons v vs ih =>
      have hv : SVal.ok st v = true := hall v (by simp)
      have hvs : ∀ w ∈ vs, SVal.ok st w = true := fun w hw => hall w (by simp [hw])
      rw [packConcat_cons, List.length_append]
      have := packedOf_nonempty hp hv
      have := ih hvs
      simp only [List.length_cons]
      omega

/-! ### Scalar payloads -/

theorem parseScalarPayload_sound {st : ScalarTy} {b : Bytes} {v : SVal} {r : Bytes}
    (h : parseScalarPayload st b = some (v, r)) : payloadOf st v ++ r = b := by
  cases hc : st.cls with
  | varint =>
      simp only [parseScalarPayload, hc] at h
      cases hvar : varintDecode b with
      | none => rw [hvar] at h; simp at h
      | some p =>
          obtain ⟨n, r'⟩ := p
          rw [hvar] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [payloadOf, hc]
          exact varintDecode_sound hvar
  | i32 =>
      simp only [parseScalarPayload, hc] at h
      cases hread : leRead 4 b with
      | none => rw [hread] at h; simp at h
      | some p =>
          obtain ⟨n, r'⟩ := p
          rw [hread] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [payloadOf, hc]
          exact leRead_bytes hread
  | i64 =>
      simp only [parseScalarPayload, hc] at h
      cases hread : leRead 8 b with
      | none => rw [hread] at h; simp at h
      | some p =>
          obtain ⟨n, r'⟩ := p
          rw [hread] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [payloadOf, hc]
          exact leRead_bytes hread
  | len =>
      simp only [parseScalarPayload, hc] at h
      cases hvar : varintDecode b with
      | none => rw [hvar] at h; simp at h
      | some p =>
          obtain ⟨n, r1⟩ := p
          rw [hvar] at h
          try dsimp only at h
          cases hsplit : split n r1 with
          | none => rw [hsplit] at h; simp at h
          | some q =>
              obtain ⟨chunk, r2⟩ := q
              rw [hsplit] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [payloadOf, hc]
              have h1 : varintEncode n ++ r1 = b := varintDecode_sound hvar
              obtain ⟨h2, h3⟩ := split_sound hsplit
              rw [List.append_assoc, h2, h3]
              exact h1

theorem parseScalarPayload_complete {st : ScalarTy} {v : SVal} (rest : Bytes)
    (hok : SVal.ok st v = true) :
    parseScalarPayload st (payloadOf st v ++ rest) = some (v, rest) := by
  cases hc : st.cls with
  | varint =>
      match v, hok with
      | .n n, hok =>
          simp only [parseScalarPayload, payloadOf, hc, varintDecode_encode]
      | .s b, hok => simp [SVal.ok, hc] at hok
  | i32 =>
      match v, hok with
      | .n n, hok =>
          have hn := ok_i32_lt hc hok
          simp only [parseScalarPayload, payloadOf, hc, leRead_leBytes 4 n rest hn]
      | .s b, hok => simp [SVal.ok, hc] at hok
  | i64 =>
      match v, hok with
      | .n n, hok =>
          have hn := ok_i64_lt hc hok
          simp only [parseScalarPayload, payloadOf, hc, leRead_leBytes 8 n rest hn]
      | .s b, hok => simp [SVal.ok, hc] at hok
  | len =>
      match v, hok with
      | .n n, hok => simp [SVal.ok, hc] at hok
      | .s b, hok =>
          simp only [parseScalarPayload, payloadOf, hc, List.append_assoc,
            varintDecode_encode, split_of_length]

/-! ### Length-delimited payloads -/

theorem parseLen_sound {b : Bytes} {chunk r : Bytes}
    (h : parseLen b = some (chunk, r)) : b = varintEncode chunk.length ++ chunk ++ r := by
  unfold parseLen at h
  cases hvar : varintDecode b with
  | none => rw [hvar] at h; simp at h
  | some p =>
      obtain ⟨n, r1⟩ := p
      rw [hvar] at h
      try dsimp only at h
      cases hsplit : split n r1 with
      | none => rw [hsplit] at h; simp at h
      | some q =>
          obtain ⟨chunk', r'⟩ := q
          rw [hsplit] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have h1 : varintEncode n ++ r1 = b := varintDecode_sound hvar
          obtain ⟨h2, h3⟩ := split_sound hsplit
          rw [List.append_assoc, h2, h3]
          exact h1.symm

theorem parseLen_complete (chunk rest : Bytes) :
    parseLen (varintEncode chunk.length ++ chunk ++ rest) = some (chunk, rest) := by
  unfold parseLen
  simp only [List.append_assoc, varintDecode_encode, split_of_length]

/-! ### Unpacking packed runs -/

/-- Soundness of a packed run: whatever is consumed re-packs to the input.
Strong induction on the length of the buffer. -/
theorem unpackAux_sound {st : ScalarTy} (hp : st.packable = true) :
    ∀ (b : Bytes) (vs : List SVal) (r : Bytes),
      unpackAux st b = some (vs, r) → b = packConcat st vs ++ r := by
  have key : ∀ (n : Nat) (b : Bytes), b.length ≤ n → ∀ (vs : List SVal) (r : Bytes),
      unpackAux st b = some (vs, r) → b = packConcat st vs ++ r := by
    intro n
    induction n with
    | zero =>
        intro b hb vs r h
        cases b with
        | nil =>
            rw [unpackAux.eq_1] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        | cons x xs => simp at hb
    | succ n ih =>
        intro b hb vs r h
        cases b with
        | nil =>
            rw [unpackAux.eq_1] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        | cons x xs =>
            rw [unpackAux.eq_2] at h
            cases hparse : parseScalarPayload st (x :: xs) with
            | none => rw [hparse] at h; simp at h
            | some p =>
                obtain ⟨sv, b'⟩ := p
                rw [hparse] at h
                try dsimp only at h
                cases hrec : unpackAux st b' with
                | none => rw [hrec] at h; simp at h
                | some q =>
                    obtain ⟨vs', r'⟩ := q
                    rw [hrec] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have h1 : payloadOf st sv ++ b' = x :: xs := parseScalarPayload_sound hparse
                    have hb' : b'.length ≤ n := by
                      have h1 := parseScalarPayload_len_lt st hparse
                      simp only [List.length_cons] at hb h1 ⊢
                      omega
                    have h2 : b' = packConcat st vs' ++ r' := ih b' hb' vs' r' hrec
                    have h3 : packedOf st sv = payloadOf st sv := packedOf_eq_payloadOf hp
                    rw [packConcat_cons, h3, ← h1, h2, List.append_assoc]
  intro b vs r h
  exact key b.length b (Nat.le_refl _) vs r h

theorem unpack_sound {st : ScalarTy} (hp : st.packable = true) {b : Bytes} {vs : List SVal}
    (h : unpack st b = some vs) : b = packConcat st vs := by
  unfold unpack at h
  cases hrec : unpackAux st b with
  | none => rw [hrec] at h; simp at h
  | some q =>
      obtain ⟨vs', r⟩ := q
      rw [hrec] at h
      try dsimp only at h
      by_cases hr : r.isEmpty
      · rw [if_pos hr] at h
        simp only [Option.some.injEq] at h
        subst h
        have hb := unpackAux_sound hp b vs' r hrec
        rw [hb]
        cases r with
        | nil => simp
        | cons y ys => simp at hr
      · rw [if_neg hr] at h; simp at h

/-- Completeness of a packed run: it consumes exactly its own packing.
Structural induction on the element list. -/
theorem unpackAux_complete {st : ScalarTy} (hp : st.packable = true) :
    ∀ (vs : List SVal),
      (∀ v ∈ vs, SVal.ok st v = true) →
      unpackAux st (packConcat st vs) = some (vs, []) := by
  intro vs
  induction vs with
  | nil => intro _; rw [packConcat, unpackAux.eq_1]
  | cons v vs ih =>
      intro hall
      have hv : SVal.ok st v = true := hall v (by simp)
      have hvs : ∀ w ∈ vs, SVal.ok st w = true := fun w hw => hall w (by simp [hw])
      have hparse := parseScalarPayload_complete (st := st) (v := v)
        (rest := packConcat st vs) hv
      have hpay : packedOf st v = payloadOf st v := packedOf_eq_payloadOf hp
      have hne : packConcat st (v :: vs) ≠ [] := by
        rw [packConcat_cons, hpay]
        intro hnil
        have hpos := packedOf_nonempty hp hv
        rw [hpay] at hpos
        have := congrArg List.length hnil
        simp only [List.length_append, List.length_nil] at this
        omega
      cases hbuf : packConcat st (v :: vs) with
      | nil => exact absurd hbuf hne
      | cons y ys =>
          have hb : y :: ys = payloadOf st v ++ packConcat st vs := by
            rw [← hbuf, packConcat_cons, hpay]
          simp only [unpackAux]
          rw [hb, hparse]
          dsimp only
          rw [ih hvs]

theorem unpack_complete {st : ScalarTy} (hp : st.packable = true) {vs : List SVal}
    (hall : ∀ v ∈ vs, SVal.ok st v = true) :
    unpack st (packConcat st vs) = some vs := by
  unfold unpack
  rw [unpackAux_complete hp vs hall]
  simp



/-! ### Payload of parsed pieces -/

/-- Key-less payload of a complete field value. -/
def fullPayload : FieldTy → Val → Bytes
  | .scalar st, .scalar sv => payloadOf st sv
  | .optional st, .scalar sv => payloadOf st sv
  | .message s, .message m =>
      varintEncode (encodeMsg s m).length ++ encodeMsg s m
  | .repeated (.scalar st), .repeated vs =>
      varintEncode (packConcat st vs).length ++ packConcat st vs
  | .repeated (.scalar st), .scalar sv => payloadOf st sv
  | .repeated (.message s), .message m =>
      varintEncode (encodeMsg s m).length ++ encodeMsg s m
  | _, _ => []

theorem parsePiece_wt {ty : FieldTy} {wt : Nat} {b : Bytes} {piece : Piece} {b2 : Bytes}
    (h : parsePiece ty wt b = some (piece, b2)) : wt = (ty.expectedWire).code := by
  unfold parsePiece at h
  by_cases hwt : wt = (ty.expectedWire).code
  · exact hwt
  · rw [if_neg hwt] at h; simp at h

theorem keyBytes_nonempty (num : Nat) (wt : WireType) : 0 < (keyBytes num wt).length := by
  unfold keyBytes; exact varintEncode_nonempty _

theorem parsePiece_full_sound {ty : FieldTy} {wt : Nat} {b : Bytes} {v : Val} {b2 : Bytes}
    (h : parsePiece ty wt b = some (.full v, b2)) :
    fullPayload ty v ++ b2 = b ∧
    ∀ (num : Nat), encodeField num ty v = keyBytes num ty.expectedWire ++ fullPayload ty v := by
  have hwt := parsePiece_wt h
  unfold parsePiece at h
  rw [if_pos hwt] at h
  try dsimp only at h
  cases ty with
  | scalar st =>
      try dsimp only at h
      cases hs : parseScalarPayload st b with
      | none => rw [hs] at h; simp at h
      | some q =>
          obtain ⟨sv, r⟩ := q
          rw [hs] at h
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq, Piece.full.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simpa [fullPayload] using parseScalarPayload_sound hs, fun num => by
            rw [encodeField.eq_1, FieldTy.expectedWire, fullPayload]⟩
  | optional st =>
      try dsimp only at h
      cases hs : parseScalarPayload st b with
      | none => rw [hs] at h; simp at h
      | some q =>
          obtain ⟨sv, r⟩ := q
          rw [hs] at h
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq, Piece.full.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨by simpa [fullPayload] using parseScalarPayload_sound hs, fun num => by
            rw [encodeField.eq_2, FieldTy.expectedWire, fullPayload]⟩
  | message s =>
      exfalso
      repeat' (split at h)
      all_goals simp_all
  | repeated t =>
      cases t with
      | scalar st =>
          dsimp only at h
          by_cases hpk : st.packable = true
          · rw [if_pos hpk] at h
            try dsimp only at h
            cases hl : parseLen b with
            | none => rw [hl] at h; simp at h
            | some q =>
                obtain ⟨chunk, r⟩ := q
                rw [hl] at h
                try dsimp only at h
                cases hu : unpack st chunk with
                | none => rw [hu] at h; simp at h
                | some vs =>
                    rw [hu] at h
                    try dsimp only at h
                    by_cases hv : vs.isEmpty = true
                    · rw [if_pos hv] at h; simp at h
                    · rw [if_neg hv] at h
                      simp only [Option.some.injEq, Prod.mk.injEq, Piece.full.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have h1 := parseLen_sound hl
                      have h2 := unpack_sound hpk hu
                      refine ⟨?_, fun num => ?_⟩
                      · rw [fullPayload, ← h2, h1]
                      · rw [encodeField.eq_4, if_pos hpk, FieldTy.expectedWire, fullPayload,
                          List.append_assoc]
          · rw [if_neg hpk] at h
            try dsimp only at h
            cases hs : parseScalarPayload st b with
            | none => rw [hs] at h; simp at h
            | some q =>
                obtain ⟨sv, r⟩ := q
                rw [hs] at h
                simp only [Option.map, Option.some.injEq, Prod.mk.injEq, Piece.full.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨by simpa [fullPayload] using parseScalarPayload_sound hs, fun num => ?_⟩
                have hne : (∀ (st' : ScalarTy) (vs : List SVal), Val.scalar sv = Val.repeated vs →
                    (FieldTy.scalar st) = FieldTy.scalar st' → False) := by
                  intro st' vs h1 h2; simp at h1
                rw [encodeField.eq_5 _ _ _ hne, FieldTy.expectedWire, fullPayload, elemPayload.eq_1]
      | message s =>
          dsimp only at h
          exfalso
          repeat' (split at h)
          all_goals simp_all
      | optional st =>
          dsimp only at h
          exfalso
          repeat' (split at h)
          all_goals simp_all
      | repeated t =>
          dsimp only at h
          exfalso
          repeat' (split at h)
          all_goals simp_all

theorem parsePiece_body_sound {ty : FieldTy} {wt : Nat} {b : Bytes} {sch : Schema}
    {chunk : Bytes} {b2 : Bytes}
    (h : parsePiece ty wt b = some (.body sch chunk, b2)) :
    b = varintEncode chunk.length ++ chunk ++ b2 ∧
    ∀ (num : Nat) (sub : Msg), encodeMsg sch sub = chunk →
      encodeField num ty (.message sub) =
        keyBytes num ty.expectedWire ++ (varintEncode chunk.length ++ chunk) := by
  have hwt := parsePiece_wt h
  unfold parsePiece at h
  rw [if_pos hwt] at h
  try dsimp only at h
  cases ty with
  | scalar st =>
      exfalso
      repeat' (split at h)
      all_goals simp_all
  | optional st =>
      exfalso
      repeat' (split at h)
      all_goals simp_all
  | message s =>
      try dsimp only at h
      cases hl : parseLen b with
      | none => rw [hl] at h; simp at h
      | some q =>
          obtain ⟨chunk', r⟩ := q
          rw [hl] at h
          simp only [Option.some.injEq, Prod.mk.injEq, Piece.body.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          refine ⟨parseLen_sound hl, fun num sub hchunk => ?_⟩
          rw [encodeField.eq_3, FieldTy.expectedWire, ← hchunk, List.append_assoc]
  | repeated t =>
      cases t with
      | scalar st =>
          dsimp only at h
          by_cases hpk : st.packable = true
          · rw [if_pos hpk] at h
            exfalso
            repeat' (split at h)
            all_goals simp_all
          · rw [if_neg hpk] at h
            exfalso
            repeat' (split at h)
            all_goals simp_all
      | message s =>
          dsimp only at h
          cases hl : parseLen b with
          | none => rw [hl] at h; simp at h
          | some q =>
              obtain ⟨chunk', r⟩ := q
              rw [hl] at h
              simp only [Option.some.injEq, Prod.mk.injEq, Piece.body.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              refine ⟨parseLen_sound hl, fun num sub hchunk => ?_⟩
              have hne : (∀ (st' : ScalarTy) (vs : List SVal), Val.message sub = Val.repeated vs →
                  (FieldTy.message s) = FieldTy.scalar st' → False) := by
                intro st' vs h1 h2; simp at h1
              rw [encodeField.eq_5 _ _ _ hne, FieldTy.expectedWire, elemPayload.eq_2, ← hchunk]
      | optional st =>
          dsimp only at h
          exfalso
          repeat' (split at h)
          all_goals simp_all
      | repeated t =>
          dsimp only at h
          exfalso
          repeat' (split at h)
          all_goals simp_all



/-! ### Facts about canonical messages -/


/-! ### Facts about canonical messages -/

theorem numsOk_cons {n : Nat} {v : Val} {rest : Msg} (h : numsOk ((n, v) :: rest) = true) :
    decide (1 ≤ n) = true ∧ numsOk rest = true := by
  simpa only [numsOk, Bool.and_eq_true] using h

theorem sortedOk_cons {s : Schema} {n : Nat} {v : Val} {n' : Nat} {v' : Val} {rest : Msg}
    (h : sortedOk s ((n, v) :: (n', v') :: rest) = true) :
    (decide (n < n') || (decide (n = n') && isMultiField s n)) = true ∧
    sortedOk s ((n', v') :: rest) = true := by
  simpa only [sortedOk, Bool.and_eq_true] using h

theorem sortedOk_one {s : Schema} {e : Nat × Val} : sortedOk s [e] = true := by
  obtain ⟨n, v⟩ := e
  simp [sortedOk]

theorem fieldsOk_cons {s : Schema} {n : Nat} {v : Val} {rest : Msg}
    (h : fieldsOk s ((n, v) :: rest) = true) :
    (∃ ty, findField s n = some ty ∧ canonField ty v = true) ∧ fieldsOk s rest = true := by
  simp only [fieldsOk, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  revert h1
  cases hf : findField s n with
  | none => intro h1; simp only [hf] at h1; simp at h1
  | some ty => intro h1; exact ⟨ty, rfl, h1⟩

theorem canonMsg_facts {s : Schema} {m : Msg} (h : canonMsg s m = true) :
    numsOk m = true ∧ sortedOk s m = true ∧ fieldsOk s m = true := by
  simp only [canonMsg, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem sortedOk_orderOk : ∀ (m : Msg) (s : Schema) (last : Nat),
    sortedOk s m = true →
    (match m with
     | [] => True
     | (n, _) :: _ => (decide (last < n) || (decide (last = n) && isMultiField s n))) →
    orderOk s last m = true := by
  intro m
  induction m with
  | nil => intro s last _ _; rfl
  | cons hd tl ih =>
      intro s last hs hlast
      obtain ⟨n, v⟩ := hd
      cases tl with
      | nil =>
          simp only [orderOk]
          simpa using hlast
      | cons hd2 tl2 =>
          obtain ⟨n', v'⟩ := hd2
          obtain ⟨hsorted, hrest⟩ := sortedOk_cons hs
          rw [orderOk]
          have hhead : (decide (last < n) || (decide (last = n) && isMultiField s n)) = true := hlast
          rw [hhead, Bool.true_and]
          have hsorted' : (decide (n < n') || (decide (n = n') && isMultiField s n')) = true := by
            rcases (by simpa [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hsorted) with h | ⟨h, hm⟩
            · simp [h]
            · subst h
              simp [hm]
          exact ih s n hrest hsorted' 

theorem canonMsg_orderOk {s : Schema} {m : Msg} (h : canonMsg s m = true) : orderOk s 0 m = true := by
  obtain ⟨hnums, hsorted, _⟩ := canonMsg_facts h
  match m with
  | [] => rfl
  | (n, v) :: rest =>
      have h1 := numsOk_cons (v := v) (rest := rest) hnums
      have hpos : (decide (0 < n) || (decide (0 = n) && isMultiField s n)) = true := by
        have h2 : 0 < n := by simp only [decide_eq_true_eq] at h1; omega
        simp [h2]
      exact sortedOk_orderOk ((n, v) :: rest) s 0 hsorted hpos

/-! ### Parse completeness -/

theorem parsePiece_complete_scalar {st : ScalarTy} {sv : SVal} (rest : Bytes)
    (hok : SVal.ok st sv = true) :
    parsePiece (FieldTy.scalar st) st.wire.code (payloadOf st sv ++ rest) =
      some (.full (.scalar sv), rest) := by
  simp only [parsePiece, FieldTy.expectedWire, if_pos rfl, ↓reduceIte, Option.map,
    parseScalarPayload_complete rest hok]

theorem parsePiece_complete_optional {st : ScalarTy} {sv : SVal} (rest : Bytes)
    (hok : SVal.ok st sv = true) :
    parsePiece (FieldTy.optional st) st.wire.code (payloadOf st sv ++ rest) =
      some (.full (.scalar sv), rest) := by
  simp only [parsePiece, FieldTy.expectedWire, if_pos rfl, ↓reduceIte, Option.map,
    parseScalarPayload_complete rest hok]

theorem parsePiece_complete_msg {s : Schema} {chunk : Bytes} (rest : Bytes) :
    parsePiece (.message s) WireType.len.code (varintEncode chunk.length ++ chunk ++ rest) =
      some (.body s chunk, rest) := by
  simp only [parsePiece, FieldTy.expectedWire, if_pos rfl, ↓reduceIte, parseLen_complete]

theorem parsePiece_complete_repMsg {s : Schema} {chunk : Bytes} (rest : Bytes) :
    parsePiece (.repeated (.message s)) WireType.len.code
      (varintEncode chunk.length ++ chunk ++ rest) = some (.body s chunk, rest) := by
  simp only [parsePiece, FieldTy.expectedWire, if_pos rfl, ↓reduceIte, parseLen_complete]

theorem parsePiece_complete_packed {st : ScalarTy} {vs : List SVal}
    (hpk : st.packable = true) (hne : vs.isEmpty = false)
    (hall : ∀ v ∈ vs, SVal.ok st v = true) (rest : Bytes) :
    parsePiece (FieldTy.repeated (FieldTy.scalar st)) WireType.len.code
      (varintEncode (packConcat st vs).length ++ packConcat st vs ++ rest) =
      some (.full (.repeated vs), rest) := by
  simp only [parsePiece, FieldTy.expectedWire, if_pos rfl, ↓reduceIte, hpk]
  rw [parseLen_complete]
  dsimp only
  rw [unpack_complete hpk hall]
  dsimp only
  rw [if_neg (by simpa using hne)]

theorem parsePiece_complete_elem {st : ScalarTy} {sv : SVal} (hpk : st.packable = false)
    (hok : SVal.ok st sv = true) (rest : Bytes) :
    parsePiece (FieldTy.repeated (FieldTy.scalar st)) WireType.len.code
      (payloadOf st sv ++ rest) = some (.full (.scalar sv), rest) := by
  have hwire : st.wire.code = WireType.len.code := by
    cases hc : st.cls <;> simp [ScalarTy.packable, hc, ScalarTy.wire] at hpk ⊢
  simp only [parsePiece, FieldTy.expectedWire, hwire, if_pos rfl, ↓reduceIte, hpk]
  simp only [Bool.false_eq_true, if_false]
  simp only [Option.map, parseScalarPayload_complete rest hok]



/-! ### Helpers for the main proofs -/

theorem encodeMsg_cons {s : Schema} {num : Nat} {v : Val} {rest : Msg} :
    encodeMsg s ((num, v) :: rest) =
      (match findField s num with
       | some ty => encodeField num ty v
       | none => []) ++ encodeMsg s rest :=
  encodeMsg.eq_2 s num v rest

theorem keyWire_eq {key : Nat} {ty : FieldTy} (h : key % 8 = (ty.expectedWire).code) :
    keyBytes (key / 8) ty.expectedWire = varintEncode key := by
  unfold keyBytes
  have h1 : key / 8 * 8 + (ty.expectedWire).code = key := by
    rw [← h]
    have := Nat.div_add_mod key 8
    omega
  rw [h1]



theorem cf_s_msg : ∀ (st : ScalarTy) (m : Msg), canonField (FieldTy.scalar st) (Val.message m) = false := by
  intros
  unfold canonField
  rfl

theorem cf_s_rep : ∀ (st : ScalarTy) (vs : List SVal), canonField (FieldTy.scalar st) (Val.repeated vs) = false := by
  intros
  unfold canonField
  rfl

theorem cf_o_msg : ∀ (st : ScalarTy) (m : Msg), canonField (FieldTy.optional st) (Val.message m) = false := by
  intros
  unfold canonField
  rfl

theorem cf_o_rep : ∀ (st : ScalarTy) (vs : List SVal), canonField (FieldTy.optional st) (Val.repeated vs) = false := by
  intros
  unfold canonField
  rfl

theorem cf_m_sc : ∀ (s : Schema) (sv : SVal), canonField (FieldTy.message s) (Val.scalar sv) = false := by
  intros
  unfold canonField
  rfl

theorem cf_m_rep : ∀ (s : Schema) (vs : List SVal), canonField (FieldTy.message s) (Val.repeated vs) = false := by
  intros
  unfold canonField
  rfl

theorem cf_rs_msg : ∀ (st : ScalarTy) (m : Msg), canonField (FieldTy.repeated (FieldTy.scalar st)) (Val.message m) = false := by
  intros
  unfold canonField canonRep
  rfl

theorem cf_rm_sc : ∀ (ms : Schema) (sv : SVal), canonField (FieldTy.repeated (FieldTy.message ms)) (Val.scalar sv) = false := by
  intros
  unfold canonField canonRep
  rfl

theorem cf_rm_rep : ∀ (ms : Schema) (vs : List SVal), canonField (FieldTy.repeated (FieldTy.message ms)) (Val.repeated vs) = false := by
  intros
  unfold canonField canonRep
  rfl

theorem encodeField_fullPayload {num : Nat} {ty : FieldTy} {v : Val}
    (hc : canonField ty v = true) :
    encodeField num ty v = keyBytes num ty.expectedWire ++ fullPayload ty v := by
  cases ty with
  | scalar st =>
      cases v with
      | scalar sv => rw [encodeField.eq_1, FieldTy.expectedWire, fullPayload]
      | message m => rw [cf_s_msg st m] at hc; exact absurd hc (by decide)
      | repeated vs => rw [cf_s_rep st vs] at hc; exact absurd hc (by decide)
  | optional st =>
      cases v with
      | scalar sv => rw [encodeField.eq_2, FieldTy.expectedWire, fullPayload]
      | message m => rw [cf_o_msg st m] at hc; exact absurd hc (by decide)
      | repeated vs => rw [cf_o_rep st vs] at hc; exact absurd hc (by decide)
  | message s =>
      cases v with
      | message m => rw [encodeField.eq_3, FieldTy.expectedWire, fullPayload, List.append_assoc]
      | scalar sv => rw [cf_m_sc s sv] at hc; exact absurd hc (by decide)
      | repeated vs => rw [cf_m_rep s vs] at hc; exact absurd hc (by decide)
  | repeated t =>
      cases t with
      | scalar st =>
          cases v with
          | repeated vs =>
              unfold canonField at hc
              unfold canonRep at hc
              simp only [Bool.and_eq_true] at hc
              obtain ⟨⟨hpk, _⟩, _⟩ := hc
              rw [encodeField.eq_4, if_pos hpk, FieldTy.expectedWire, fullPayload, List.append_assoc]
          | scalar sv =>
              have hne : (∀ (st' : ScalarTy) (vs : List SVal),
                  Val.scalar sv = Val.repeated vs → (FieldTy.scalar st) = FieldTy.scalar st' → False) := by
                intro st' vs h1 h2; simp at h1
              rw [encodeField.eq_5 _ _ _ hne, FieldTy.expectedWire, fullPayload, elemPayload.eq_1]
          | message m => rw [cf_rs_msg st m] at hc; exact absurd hc (by decide)
      | message ms =>
          cases v with
          | message m =>
              have hne : (∀ (st' : ScalarTy) (vs : List SVal),
                  Val.message m = Val.repeated vs → (FieldTy.message ms) = FieldTy.scalar st' → False) := by
                intro st' vs h1 h2; simp at h1
              rw [encodeField.eq_5 _ _ _ hne, FieldTy.expectedWire, fullPayload, elemPayload.eq_2]
          | scalar sv => rw [cf_rm_sc ms sv] at hc; exact absurd hc (by decide)
          | repeated vs => rw [cf_rm_rep ms vs] at hc; exact absurd hc (by decide)
      | optional st =>
          cases v with
          | scalar sv => unfold canonField at hc; unfold canonRep at hc; exact absurd hc (by decide)
          | message m => unfold canonField at hc; unfold canonRep at hc; exact absurd hc (by decide)
          | repeated vs => unfold canonField at hc; unfold canonRep at hc; exact absurd hc (by decide)
      | repeated t =>
          cases v with
          | scalar sv => unfold canonField at hc; unfold canonRep at hc; exact absurd hc (by decide)
          | message m => unfold canonField at hc; unfold canonRep at hc; exact absurd hc (by decide)
          | repeated vs => unfold canonField at hc; unfold canonRep at hc; exact absurd hc (by decide)

theorem assemble_msg {s : Schema} {sub : Msg} :
    assemble (.message s) sub = some (.message sub) := assemble.eq_1 sub s

theorem assemble_repMsg {s : Schema} {sub : Msg} :
    assemble (.repeated (.message s)) sub = some (.message sub) := assemble.eq_2 sub s

theorem encodeMsg_rest_le {s : Schema} {num : Nat} {v : Val} {rest : Msg} {ty : FieldTy}
    (hfind : findField s num = some ty) :
    (encodeMsg s rest).length ≤ (encodeMsg s ((num, v) :: rest)).length := by
  rw [encodeMsg_cons, hfind, List.length_append]
  omega

/-! ### Soundness -/

/-- Reassemble a pair from its first projection. -/
theorem prod_eq_of_fst {α β : Type} {p : α × β} {a : α} (h : p.1 = a) : p = (a, p.2) := by
  obtain ⟨x, y⟩ := p
  simp only at h ⊢
  rw [h]

theorem parsePiece_full_shape {ty : FieldTy} {wt : Nat} {b : Bytes} {pr : Piece × Bytes}
    {v : Val} (h : parsePiece ty wt b = some pr) (hp : pr.1 = .full v) :
    parsePiece ty wt b = some (.full v, pr.2) := by
  rw [prod_eq_of_fst hp] at h
  exact h

theorem parsePiece_body_shape {ty : FieldTy} {wt : Nat} {b : Bytes} {pr : Piece × Bytes}
    {sch : Schema} {chunk : Bytes} (h : parsePiece ty wt b = some pr)
    (hp : pr.1 = .body sch chunk) :
    parsePiece ty wt b = some (.body sch chunk, pr.2) := by
  rw [prod_eq_of_fst hp] at h
  exact h

/-- Soundness: every byte string accepted by the decoder re-encodes to itself.
Proved by strong induction on the length of the buffer, since both recursive
calls (`pr.2` and a nested message's `chunk`) are on strictly shorter buffers. -/
theorem decodeBody_sound : ∀ (s : Schema) (last : Nat) (b : Bytes) (m : Msg),
    decodeBody s last b = some m → encodeMsg s m = b := by
  have key : ∀ (n : Nat) (s : Schema) (last : Nat) (b : Bytes), b.length ≤ n →
      ∀ (m : Msg), decodeBody s last b = some m → encodeMsg s m = b := by
    intro n
    induction n with
    | zero =>
        intro s last b hb m h
        cases b with
        | nil =>
            rw [decodeBody.eq_def] at h
            simp only [Option.some.injEq] at h
            subst h
            exact encodeMsg.eq_1 s
        | cons x xs => simp at hb
    | succ n ih =>
        intro s last b hb m h
        cases b with
        | nil =>
            rw [decodeBody.eq_def] at h
            simp only [Option.some.injEq] at h
            subst h
            exact encodeMsg.eq_1 s
        | cons x xs =>
            rw [decodeBody.eq_def] at h
            try dsimp only at h
            cases hvar : varintDecode (x :: xs) with
            | none => rw [hvar] at h; simp at h
            | some p =>
                obtain ⟨key, b1⟩ := p
                rw [hvar] at h
                try dsimp only at h
                cases hfind : findField s (key / 8) with
                | none => rw [hfind] at h; simp at h
                | some ty =>
                    rw [hfind] at h
                    try dsimp only at h
                    have hvarb : varintEncode key ++ b1 = x :: xs := varintDecode_sound hvar
                    by_cases hlt : key / 8 < last
                    · rw [if_pos hlt] at h; simp at h
                    · rw [if_neg hlt] at h
                      by_cases hcnd : (decide (key / 8 = last) && !ty.isMulti) = true
                      · rw [if_pos hcnd] at h; simp at h
                      · rw [if_neg hcnd] at h
                        try dsimp only at h
                        cases hpiece : parsePiece ty (key % 8) b1 with
                        | none => rw [hpiece] at h; simp at h
                        | some pr =>
                            rw [hpiece] at h
                            try dsimp only at h
                            have hkeyb : keyBytes (key / 8) ty.expectedWire = varintEncode key :=
                              keyWire_eq (parsePiece_wt hpiece)
                            have hlen2 : pr.2.length ≤ n := by
                              have h1 : pr.2.length < b1.length := parsePiece_snd_lt hpiece
                              have h2 : b1.length < (x :: xs).length := varintDecode_lt hvar
                              simp only [List.length_cons] at hb h1 h2 ⊢
                              omega
                            cases hrec : decodeBody s (key / 8) pr.2 with
                            | none => rw [hrec] at h; simp at h
                            | some rest =>
                                rw [hrec] at h
                                try dsimp only at h
                                have hrest : encodeMsg s rest = pr.2 :=
                                  ih s (key / 8) pr.2 hlen2 rest hrec
                                split at h
                                case _ v hpc =>
                                    obtain ⟨hval, henc⟩ :=
                                      parsePiece_full_sound (parsePiece_full_shape hpiece hpc)
                                    have hm : (key / 8, v) :: rest = m := Option.some.inj h
                                    subst hm
                                    rw [encodeMsg_cons, hfind]
                                    dsimp only
                                    rw [henc (key / 8), List.append_assoc, hrest, hkeyb, hval]
                                    exact hvarb
                                case _ sch chunk hpc =>
                                    obtain ⟨hbody, henc⟩ :=
                                      parsePiece_body_sound (parsePiece_body_shape hpiece hpc)
                                    have hlen3 : chunk.length ≤ n := by
                                      have h1 : chunk.length ≤ b1.length :=
                                        parsePiece_chunk_le hpiece hpc
                                      have h2 : b1.length < (x :: xs).length := varintDecode_lt hvar
                                      simp only [List.length_cons] at hb h1 h2 ⊢
                                      omega
                                    cases hrec2 : decodeBody sch 0 chunk with
                                    | none => rw [hrec2] at h; simp at h
                                    | some sub =>
                                        rw [hrec2] at h
                                        try dsimp only at h
                                        have hchunk : encodeMsg sch sub = chunk :=
                                          ih sch 0 chunk hlen3 sub hrec2
                                        cases ha : assemble ty sub with
                                        | none => rw [ha] at h; simp at h
                                        | some v =>
                                            rw [ha] at h
                                            try dsimp only at h
                                            have hv : v = .message sub := by
                                              unfold assemble at ha
                                              cases ty with
                                              | message s => simpa using ha.symm
                                              | repeated t => cases t <;> simp_all
                                              | scalar st => simp_all
                                              | optional st => simp_all
                                            have hm : (key / 8, v) :: rest = m := Option.some.inj h
                                            subst hm
                                            subst hv
                                            rw [encodeMsg_cons, hfind]
                                            dsimp only
                                            rw [henc (key / 8) sub hchunk, List.append_assoc, hrest, hkeyb,
                                              ← hbody]
                                            exact hvarb
  intro s last b m h
  exact key b.length s last b (Nat.le_refl _) m h

theorem encodeField_nonempty {num : Nat} {ty : FieldTy} {v : Val}
    (hc : canonField ty v = true) : 0 < (encodeField num ty v).length := by
  rw [encodeField_fullPayload hc]
  have := keyBytes_nonempty num ty.expectedWire
  simp only [List.length_append]
  omega

theorem encodeMsg_ne_nil {s : Schema} {m : Msg} (hm : m ≠ []) (hc : canonMsg s m = true) :
    encodeMsg s m ≠ [] := by
  match m with
  | [] => exact absurd rfl hm
  | (n, v) :: rest =>
      obtain ⟨_, _, hf⟩ := canonMsg_facts hc
      obtain ⟨⟨ty, hfind, hcv⟩, _⟩ := fieldsOk_cons hf
      rw [encodeMsg_cons, hfind]
      intro hnil
      have hlen := congrArg List.length hnil
      simp only [List.length_append, List.length_nil] at hlen
      have := encodeField_nonempty (num := n) hcv
      omega

theorem keyBits (num : Nat) (wt : WireType) :
    (num * 8 + wt.code) / 8 = num ∧ (num * 8 + wt.code) % 8 = wt.code ∧ wt.code < 8 := by
  cases wt <;> simp [WireType.code] <;> omega

theorem sortedOk_tail {s : Schema} {n : Nat} {v : Val} {rest : Msg}
    (h : sortedOk s ((n, v) :: rest) = true) : sortedOk s rest = true := by
  cases rest with
  | nil => simp [sortedOk]
  | cons hd tl =>
      obtain ⟨hd', tl'⟩ := hd
      exact (sortedOk_cons h).2

theorem canonMsg_tail {s : Schema} {n : Nat} {v : Val} {rest : Msg}
    (h : canonMsg s ((n, v) :: rest) = true) : canonMsg s rest = true := by
  obtain ⟨hnums, hsorted, hfields⟩ := canonMsg_facts h
  obtain ⟨_, hfields'⟩ := fieldsOk_cons hfields
  have hnums' := (numsOk_cons (v := v) (rest := rest) hnums).2
  have hsorted' := sortedOk_tail hsorted
  simp only [canonMsg, Bool.and_eq_true]
  exact ⟨⟨hnums', hsorted'⟩, hfields'⟩

/-! ### Completeness of `parsePiece` -/

theorem orderOk_cons {s : Schema} {last n : Nat} {v : Val} {rest : Msg}
    (h : orderOk s last ((n, v) :: rest) = true) :
    (decide (last < n) || (decide (last = n) && isMultiField s n)) = true ∧
    orderOk s n rest = true := by
  simpa only [orderOk, Bool.and_eq_true] using h

theorem parsePiece_complete {ty : FieldTy} {v : Val} (hc : canonField ty v = true)
    (rest : Bytes) :
    ∃ piece, parsePiece ty ty.expectedWire.code (fullPayload ty v ++ rest) = some (piece, rest) ∧
      (∀ v', piece = .full v' → v' = v) ∧
      (∀ (sch : Schema) (chunk : Bytes), piece = .body sch chunk →
        ∃ sub, v = .message sub ∧ chunk = encodeMsg sch sub ∧ canonMsg sch sub = true) := by
  cases ty with
  | scalar st =>
      cases v with
      | scalar sv =>
          have hok : sv.ok st = true := by
            unfold canonField at hc
            simp only [Bool.and_eq_true] at hc
            exact hc.1
          refine ⟨.full (.scalar sv), ?_, ?_, ?_⟩
          · rw [fullPayload]; exact parsePiece_complete_scalar rest hok
          · intro v' hv; cases hv; rfl
          · intro sch chunk hpiece; cases hpiece
      | _ => unfold canonField at hc; exact absurd hc (by decide)
  | optional st =>
      cases v with
      | scalar sv =>
          refine ⟨.full (.scalar sv), ?_, ?_, ?_⟩
          · rw [fullPayload]; exact parsePiece_complete_optional rest (by unfold canonField at hc; exact hc)
          · intro v' hv; cases hv; rfl
          · intro sch chunk hpiece; cases hpiece
      | _ => unfold canonField at hc; exact absurd hc (by decide)
  | message s =>
      cases v with
      | message m =>
          refine ⟨.body s (encodeMsg s m), ?_, ?_, ?_⟩
          · rw [fullPayload]; exact parsePiece_complete_msg rest
          · intro v' hv; cases hv
          · intro sch' chunk hpiece
            simp only [Piece.body.injEq] at hpiece
            obtain ⟨rfl, rfl⟩ := hpiece
            refine ⟨m, rfl, rfl, ?_⟩
            unfold canonField at hc
            exact hc
      | _ => unfold canonField at hc; exact absurd hc (by decide)
  | repeated t =>
      cases t with
      | scalar st =>
          cases v with
          | repeated vs =>
              unfold canonField canonRep at hc
              simp only [Bool.and_eq_true] at hc
              obtain ⟨⟨hpk, hne⟩, hall⟩ := hc
              have hne' : vs.isEmpty = false := by simpa using hne
              refine ⟨.full (.repeated vs), ?_, ?_, ?_⟩
              · rw [fullPayload]
                exact parsePiece_complete_packed hpk hne' (fun w hw => List.all_eq_true.mp hall w hw) rest
              · intro v' hv; cases hv; rfl
              · intro sch chunk hpiece; cases hpiece
          | scalar sv =>
              unfold canonField canonRep at hc
              simp only [Bool.and_eq_true, Bool.not_eq_true] at hc
              obtain ⟨hpk, hok⟩ := hc
              have hpk' : st.packable = false := by simpa using hpk
              refine ⟨.full (.scalar sv), ?_, ?_, ?_⟩
              · rw [fullPayload]; exact parsePiece_complete_elem hpk' hok rest
              · intro v' hv; cases hv; rfl
              · intro sch chunk hpiece; cases hpiece
          | message m => unfold canonField canonRep at hc; exact absurd hc (by decide)
      | message ms =>
          cases v with
          | message m =>
              refine ⟨.body ms (encodeMsg ms m), ?_, ?_, ?_⟩
              · rw [fullPayload]; exact parsePiece_complete_repMsg rest
              · intro v' hv; cases hv
              · intro sch' chunk hpiece
                simp only [Piece.body.injEq] at hpiece
                obtain ⟨rfl, rfl⟩ := hpiece
                refine ⟨m, rfl, rfl, ?_⟩
                unfold canonField canonRep at hc
                exact hc
          | _ => unfold canonField canonRep at hc; exact absurd hc (by decide)
      | optional st => unfold canonField canonRep at hc; exact absurd hc (by decide)
      | repeated tt => unfold canonField canonRep at hc; exact absurd hc (by decide)

/-- Generic unfolding of the decoder at a canonical field key: the key varint is
split into its first byte and the rest, so that the decoder's equation lemma
(which needs a syntactic cons) applies, and the `findField`/`parsePiece` results
are taken as hypotheses so that each field-type branch of completeness can apply
this lemma directly.  This is the technical crux that lets completeness evaluate
`decodeBody` on `encodeMsg`. -/
theorem decodeBody_key (s : Schema) (last : Nat) (key : Nat) (ty : FieldTy)
    (pr : Piece × Bytes) (k1 : UInt8) (ks rest : Bytes)
    (hk : varintEncode key = k1 :: ks)
    (hfind : findField s (key / 8) = some ty)
    (hlt : ¬ key / 8 < last)
    (hcnd : ¬ (decide (key / 8 = last) && !ty.isMulti) = true)
    (hpiece : parsePiece ty (key % 8) rest = some pr) :
    decodeBody s last (k1 :: (ks ++ rest)) =
      (match decodeBody s (key / 8) pr.2 with
       | none => none
       | some rest' =>
         match pr.1 with
         | .full v => some ((key / 8, v) :: rest')
         | .body sch chunk =>
           match decodeBody sch 0 chunk with
           | none => none
           | some sub =>
             match assemble ty sub with
             | none => none
             | some v => some ((key / 8, v) :: rest')) := by
  obtain ⟨p, r⟩ := pr
  rw [decodeBody.eq_def]
  dsimp only
  have hdec : varintDecode (k1 :: (ks ++ rest)) = some (key, rest) := by
    rw [← List.cons_append, ← hk]
    exact varintDecode_encode key rest
  rw [hdec]
  try dsimp only
  rw [hfind]
  try dsimp only
  rw [if_neg hlt]
  try dsimp only
  rw [if_neg hcnd]
  try dsimp only
  rw [hpiece]
  try dsimp only
  cases p <;> rfl

/-! ### Completeness of the decoder -/

/-- Completeness: every canonical message is accepted and recovered.  Strong
induction on the length of the encoding; the recursive calls are on the shorter
encodings of the tail and of a nested message. -/
theorem decodeBody_complete :
    ∀ (s : Schema) (last : Nat) (m : Msg),
      canonMsg s m = true →
      orderOk s last m = true →
      decodeBody s last (encodeMsg s m) = some m := by
  have key : ∀ (n : Nat) (s : Schema) (last : Nat) (m : Msg),
      (encodeMsg s m).length ≤ n →
      canonMsg s m = true →
      orderOk s last m = true →
      decodeBody s last (encodeMsg s m) = some m := by
    intro n
    induction n with
    | zero =>
        intro s last m hlen hc ho
        match m with
        | [] => rw [encodeMsg.eq_1, decodeBody.eq_1]
        | (n, v) :: rest =>
            have hne := encodeMsg_ne_nil (s := s) (m := (n, v) :: rest) (by simp) hc
            have h0 : (encodeMsg s ((n, v) :: rest)).length = 0 := by omega
            rw [List.eq_nil_of_length_eq_zero h0] at hne
            exact absurd rfl hne
    | succ f ih =>
        intro s last m hlen hc ho
        match m with
        | [] => rw [encodeMsg.eq_1, decodeBody.eq_1]
        | (n, v) :: rest =>
            obtain ⟨hnums, hsorted, hfields⟩ := canonMsg_facts hc
            have h1n : (decide (1 ≤ n)) = true := (numsOk_cons (v := v) (rest := rest) hnums).1
            obtain ⟨⟨ty, hfind, hcv⟩, _⟩ := fieldsOk_cons hfields
            have hc_rest : canonMsg s rest = true := canonMsg_tail hc
            obtain ⟨hgn, ho_rest⟩ := orderOk_cons ho
            have hlt : ¬ n < last := by
              rcases (by simpa [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hgn) with h | ⟨h, _⟩ <;> omega
            have hcnd : ¬ ((decide (n = last) && !ty.isMulti) = true) := by
              intro hcon
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcon
              obtain ⟨heq, hnot⟩ := hcon
              rcases (by simpa [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hgn) with h | ⟨_, hmul⟩
              · omega
              · rw [isMultiField, hfind] at hmul
                simp [hmul] at hnot
            have hlen_rest : (encodeMsg s rest).length ≤ f := by
              rw [encodeMsg_cons, hfind] at hlen
              dsimp only at hlen
              rw [encodeField_fullPayload hcv, List.append_assoc] at hlen
              simp only [List.length_append] at hlen
              have hk := keyBytes_nonempty n ty.expectedWire
              omega
            have hrec : decodeBody s n (encodeMsg s rest) = some rest := ih s n rest hlen_rest hc_rest ho_rest
            obtain ⟨hk8, hkm, hkc⟩ := keyBits n ty.expectedWire
            obtain ⟨k1, ks, hk⟩ : ∃ k1 ks, varintEncode (n * 8 + ty.expectedWire.code) = k1 :: ks := by
              match h : varintEncode (n * 8 + ty.expectedWire.code) with
              | [] => exact absurd h (by
                  have := varintEncode_nonempty (n * 8 + ty.expectedWire.code)
                  intro hh; rw [hh] at this; simp at this)
              | k1 :: ks => exact ⟨k1, ks, rfl⟩
            rw [show encodeMsg s ((n, v) :: rest)
                  = k1 :: (ks ++ (fullPayload ty v ++ encodeMsg s rest)) from by
                rw [encodeMsg_cons, hfind]; dsimp only
                rw [encodeField_fullPayload hcv, List.append_assoc]
                simp only [keyBytes]
                rw [hk]; rfl]
            have hfind' : findField s ((n * 8 + ty.expectedWire.code) / 8) = some ty := by
              rw [hk8]; exact hfind
            have hlt' : ¬ (n * 8 + ty.expectedWire.code) / 8 < last := by
              rw [hk8]; exact hlt
            have hcnd' : ¬ (decide ((n * 8 + ty.expectedWire.code) / 8 = last)
                && !ty.isMulti) = true := by
              rw [hk8]; exact hcnd
            cases ty with
            | scalar st =>
                cases v with
                | scalar sv =>
                    have hok : SVal.ok st sv = true := by
                      unfold canonField at hcv
                      simp only [Bool.and_eq_true] at hcv
                      exact hcv.1
                    have hpiece : parsePiece (FieldTy.scalar st)
                        ((n * 8 + (FieldTy.scalar st).expectedWire.code) % 8)
                        (fullPayload (.scalar st) (.scalar sv) ++ encodeMsg s rest)
                        = some (Piece.full (Val.scalar sv), encodeMsg s rest) := by
                      rw [fullPayload, hkm]
                      exact parsePiece_complete_scalar (encodeMsg s rest) hok
                    rw [decodeBody_key s last (n * 8 + (FieldTy.scalar st).expectedWire.code) (.scalar st)
                      (Piece.full (Val.scalar sv), encodeMsg s rest) k1 ks _ hk hfind' hlt' hcnd' hpiece]
                    rw [hk8, hrec]
                | message m => unfold canonField at hcv; exact absurd hcv (by decide)
                | repeated vs => unfold canonField at hcv; exact absurd hcv (by decide)
            | optional st =>
                cases v with
                | scalar sv =>
                    have hok : SVal.ok st sv = true := by
                      unfold canonField at hcv
                      exact hcv
                    have hpiece : parsePiece (FieldTy.optional st)
                        ((n * 8 + (FieldTy.optional st).expectedWire.code) % 8)
                        (fullPayload (.optional st) (.scalar sv) ++ encodeMsg s rest)
                        = some (Piece.full (Val.scalar sv), encodeMsg s rest) := by
                      rw [fullPayload, hkm]
                      exact parsePiece_complete_optional (encodeMsg s rest) hok
                    rw [decodeBody_key s last (n * 8 + (FieldTy.optional st).expectedWire.code) (.optional st)
                      (Piece.full (Val.scalar sv), encodeMsg s rest) k1 ks _ hk hfind' hlt' hcnd' hpiece]
                    rw [hk8, hrec]
                | message m => unfold canonField at hcv; exact absurd hcv (by decide)
                | repeated vs => unfold canonField at hcv; exact absurd hcv (by decide)
            | message ms =>
                cases v with
                | message m =>
                    have hcanon : canonMsg ms m = true := by
                      unfold canonField at hcv
                      exact hcv
                    have hlen_sub : (encodeMsg ms m).length ≤ f := by
                      simp only [encodeMsg_cons, hfind, encodeField_fullPayload hcv, fullPayload,
                        List.length_append] at hlen
                      have h1 := keyBytes_nonempty n WireType.len
                      have h2 := varintEncode_nonempty (encodeMsg ms m).length
                      omega
                    have hord : orderOk ms 0 m = true := canonMsg_orderOk hcanon
                    have hrecb : decodeBody ms 0 (encodeMsg ms m) = some m :=
                      ih ms 0 m hlen_sub hcanon hord
                    have hpiece : parsePiece (FieldTy.message ms)
                        ((n * 8 + (FieldTy.message ms).expectedWire.code) % 8)
                        (fullPayload (.message ms) (.message m) ++ encodeMsg s rest)
                        = some (Piece.body ms (encodeMsg ms m), encodeMsg s rest) := by
                      rw [fullPayload, hkm]
                      exact parsePiece_complete_msg (encodeMsg s rest)
                    rw [decodeBody_key s last (n * 8 + (FieldTy.message ms).expectedWire.code) (.message ms)
                      (Piece.body ms (encodeMsg ms m), encodeMsg s rest) k1 ks _ hk hfind' hlt' hcnd' hpiece]
                    rw [hk8, hrec]
                    simp only [hrecb, assemble]
                | scalar sv => unfold canonField at hcv; exact absurd hcv (by decide)
                | repeated vs => unfold canonField at hcv; exact absurd hcv (by decide)
            | repeated t =>
                cases t with
                | scalar st =>
                    cases v with
                    | repeated vs =>
                        unfold canonField canonRep at hcv
                        simp only [Bool.and_eq_true] at hcv
                        obtain ⟨⟨hpk, hne⟩, hall⟩ := hcv
                        have hne' : vs.isEmpty = false := by simpa using hne
                        have hall' : ∀ w ∈ vs, SVal.ok st w = true := fun w hw => List.all_eq_true.mp hall w hw
                        have hpiece : parsePiece (FieldTy.repeated (FieldTy.scalar st))
                            ((n * 8 + (FieldTy.repeated (FieldTy.scalar st)).expectedWire.code) % 8)
                            (fullPayload (.repeated (.scalar st)) (.repeated vs) ++ encodeMsg s rest)
                            = some (Piece.full (Val.repeated vs), encodeMsg s rest) := by
                          rw [fullPayload, hkm]
                          exact parsePiece_complete_packed hpk hne' hall' (encodeMsg s rest)
                        rw [decodeBody_key s last (n * 8 + (FieldTy.repeated (FieldTy.scalar st)).expectedWire.code)
                          (FieldTy.repeated (FieldTy.scalar st))
                          (Piece.full (Val.repeated vs), encodeMsg s rest)
                          k1 ks _ hk hfind' hlt' hcnd' hpiece]
                        rw [hk8, hrec]
                    | scalar sv =>
                        unfold canonField canonRep at hcv
                        simp only [Bool.and_eq_true] at hcv
                        obtain ⟨hpk, hok⟩ := hcv
                        have hpk' : st.packable = false := by simpa using hpk
                        have hpiece : parsePiece (FieldTy.repeated (FieldTy.scalar st))
                            ((n * 8 + (FieldTy.repeated (FieldTy.scalar st)).expectedWire.code) % 8)
                            (fullPayload (.repeated (.scalar st)) (.scalar sv) ++ encodeMsg s rest)
                            = some (Piece.full (Val.scalar sv), encodeMsg s rest) := by
                          rw [fullPayload, hkm]
                          exact parsePiece_complete_elem hpk' hok (encodeMsg s rest)
                        rw [decodeBody_key s last (n * 8 + (FieldTy.repeated (FieldTy.scalar st)).expectedWire.code)
                          (FieldTy.repeated (FieldTy.scalar st))
                          (Piece.full (Val.scalar sv), encodeMsg s rest)
                          k1 ks _ hk hfind' hlt' hcnd' hpiece]
                        rw [hk8, hrec]
                    | message m => unfold canonField canonRep at hcv; exact absurd hcv (by decide)
                | message ms =>
                    cases v with
                    | message m =>
                        have hlen_sub : (encodeMsg ms m).length ≤ f := by
                          simp only [encodeMsg_cons, hfind, encodeField_fullPayload hcv, fullPayload,
                            List.length_append] at hlen
                          have h1 := keyBytes_nonempty n WireType.len
                          have h2 := varintEncode_nonempty (encodeMsg ms m).length
                          omega
                        have hcanon : canonMsg ms m = true := by
                          unfold canonField canonRep at hcv
                          exact hcv
                        have hord : orderOk ms 0 m = true := canonMsg_orderOk hcanon
                        have hrecb : decodeBody ms 0 (encodeMsg ms m) = some m :=
                          ih ms 0 m hlen_sub hcanon hord
                        have hpiece : parsePiece (FieldTy.repeated (FieldTy.message ms))
                            ((n * 8 + (FieldTy.repeated (FieldTy.message ms)).expectedWire.code) % 8)
                            (fullPayload (.repeated (.message ms)) (.message m) ++ encodeMsg s rest)
                            = some (Piece.body ms (encodeMsg ms m), encodeMsg s rest) := by
                          rw [fullPayload, hkm]
                          exact parsePiece_complete_repMsg (encodeMsg s rest)
                        rw [decodeBody_key s last (n * 8 + (FieldTy.repeated (FieldTy.message ms)).expectedWire.code)
                          (.repeated (.message ms)) (Piece.body ms (encodeMsg ms m), encodeMsg s rest)
                          k1 ks _ hk hfind' hlt' hcnd' hpiece]
                        rw [hk8, hrec]
                        simp only [hrecb, assemble]
                    | scalar sv => unfold canonField canonRep at hcv; exact absurd hcv (by decide)
                    | repeated vs => unfold canonField canonRep at hcv; exact absurd hcv (by decide)
                | optional st => unfold canonField canonRep at hcv; exact absurd hcv (by decide)
                | repeated tt => unfold canonField canonRep at hcv; exact absurd hcv (by decide)
  intro s last m hc ho
  exact key (encodeMsg s m).length s last m (Nat.le_refl _) hc ho

/-! ### Top-level decoder lemmas -/

theorem decodeBodyCanon_sound {s : Schema} {b : Bytes} {m : Msg}
    (h : decodeBodyCanon s b = some m) : encodeMsg s m = b := by
  unfold decodeBodyCanon at h
  cases hd : decodeBody s 0 b with
  | none => rw [hd] at h; simp at h
  | some m' =>
      rw [hd] at h
      try dsimp only at h
      by_cases hc : canonMsg s m' = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h
        exact decodeBody_sound s 0 b m' hd
      · rw [if_neg hc] at h; simp at h

end CanonicalProto

