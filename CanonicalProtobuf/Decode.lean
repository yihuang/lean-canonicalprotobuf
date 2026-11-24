/-
  Canonical Protobuf: the strict decoder.

  The decoder recurses on a *suffix* of its input rather than on a subterm, so
  termination is proved by well-founded recursion on the length of the byte
  string: every step consumes at least one byte (`varintDecode_lt`, `leRead`,
  `split`), hence both the remaining buffer and a nested message's chunk are
  strictly shorter than the buffer being parsed.  No fuel argument is needed.
-/
import CanonicalProtobuf.Encode

namespace CanonicalProto

/-- The result of parsing one field payload. -/
inductive Piece where
  | full (v : Val)
  | body (s : Schema) (chunk : Bytes)

/-- Parse one scalar payload according to the wire class of `st`. -/
def parseScalarPayload (st : ScalarTy) (b : Bytes) : Option (SVal × Bytes) :=
  match st.cls with
  | .varint =>
      match varintDecode b with
      | some (v, r) => some (.n v, r)
      | none => none
  | .i32 =>
      match leRead 4 b with
      | some (v, r) => some (.n v, r)
      | none => none
  | .i64 =>
      match leRead 8 b with
      | some (v, r) => some (.n v, r)
      | none => none
  | .len =>
      match varintDecode b with
      | none => none
      | some (n, r) =>
          match split n r with
          | none => none
          | some (chunk, r') => some (.s chunk, r')

/-- A scalar payload consumes at least one byte. -/
theorem parseScalarPayload_len_lt (st : ScalarTy) {b : Bytes} {v : SVal} {r : Bytes}
    (h : parseScalarPayload st b = some (v, r)) : r.length < b.length := by
  cases hcls : st.cls
  · cases hb : varintDecode b with
    | none => simp [parseScalarPayload, hcls, hb] at h
    | some p =>
        obtain ⟨v', r'⟩ := p
        simp only [parseScalarPayload, hcls, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact varintDecode_lt hb
  · cases hb : leRead 4 b with
    | none => simp [parseScalarPayload, hcls, hb] at h
    | some p =>
        obtain ⟨v', r'⟩ := p
        simp only [parseScalarPayload, hcls, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have := leRead_length_le hb
        omega
  · cases hb : leRead 8 b with
    | none => simp [parseScalarPayload, hcls, hb] at h
    | some p =>
        obtain ⟨v', r'⟩ := p
        simp only [parseScalarPayload, hcls, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have := leRead_length_le hb
        omega
  · cases hb : varintDecode b with
    | none => simp [parseScalarPayload, hcls, hb] at h
    | some p =>
        obtain ⟨n, r0⟩ := p
        cases hs : split n r0 with
        | none => simp [parseScalarPayload, hcls, hb, hs] at h
        | some q =>
            obtain ⟨chunk, r'⟩ := q
            simp only [parseScalarPayload, hcls, hb, hs, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            obtain ⟨happend, _⟩ := split_sound hs
            have hle : r'.length ≤ r0.length := by rw [← happend]; simp
            have h1 : r0.length < b.length := varintDecode_lt hb
            omega

set_option linter.unusedVariables false in
/-- Read a packed run, stopping at the end of the buffer or at the first
payload that does not parse.  The match on `parseScalarPayload` is named because
`decreasing_by` needs its equation. -/
def unpackAux (st : ScalarTy) : Bytes → Option (List SVal × Bytes)
  | [] => some ([], [])
  | x :: xs =>
      match hparse : parseScalarPayload st (x :: xs) with
      | none => none
      | some (v, rest) =>
          match unpackAux st rest with
          | none => none
          | some (vs, r) => some (v :: vs, r)
termination_by b => b.length
decreasing_by
  have := parseScalarPayload_len_lt st hparse
  simp only [List.length_cons] at *
  omega

/-- Read a packed run, requiring it to consume the whole buffer. -/
def unpack (st : ScalarTy) (b : Bytes) : Option (List SVal) :=
  match unpackAux st b with
  | none => none
  | some (vs, r) => if r.isEmpty then some vs else none

/-- Parse a length-delimited payload (varint length, then that many bytes). -/
def parseLen (b : Bytes) : Option (Bytes × Bytes) :=
  match varintDecode b with
  | none => none
  | some (n, r) =>
      match split n r with
      | none => none
      | some (chunk, r') => some (chunk, r')

/-- The parsed chunk is a prefix of the buffer and the rest is strictly shorter. -/
theorem parseLen_len {b : Bytes} {chunk r : Bytes}
    (h : parseLen b = some (chunk, r)) : chunk.length ≤ b.length ∧ r.length < b.length := by
  cases hb : varintDecode b with
  | none => simp [parseLen, hb] at h
  | some p =>
      obtain ⟨n, r0⟩ := p
      cases hs : split n r0 with
      | none => simp [parseLen, hb, hs] at h
      | some q =>
          obtain ⟨c, r'⟩ := q
          simp only [parseLen, hb, hs, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨happend, _⟩ := split_sound hs
          have hle : c.length ≤ r0.length := by rw [← happend]; simp
          have hle2 : r'.length ≤ r0.length := by rw [← happend]; simp
          have h1 : r0.length < b.length := varintDecode_lt hb
          exact ⟨by omega, by omega⟩

/-- Parse the payload of a field of type `ty`, requiring wire type `wt`. -/
def parsePiece (ty : FieldTy) (wt : Nat) (b : Bytes) : Option (Piece × Bytes) :=
  if wt = (ty.expectedWire).code then
    match ty with
    | .scalar st => (parseScalarPayload st b).map (fun (v, r) => (.full (.scalar v), r))
    | .optional st => (parseScalarPayload st b).map (fun (v, r) => (.full (.scalar v), r))
    | .message s =>
        match parseLen b with
        | some (chunk, r') => some (.body s chunk, r')
        | none => none
    | .repeated t =>
        match t with
        | .scalar st =>
            if st.packable then
              match parseLen b with
              | none => none
              | some (chunk, r') =>
                  match unpack st chunk with
                  | none => none
                  | some vs =>
                      if vs.isEmpty then none else some (.full (.repeated vs), r')
            else (parseScalarPayload st b).map (fun (v, r) => (.full (.scalar v), r))
        | .message s =>
            match parseLen b with
            | some (chunk, r') => some (.body s chunk, r')
            | none => none
        | _ => none
  else none

theorem map_inv {α β : Type} {f : α → β} {o : Option α} {y : β}
    (h : Option.map f o = some y) : ∃ x, o = some x ∧ f x = y := by
  cases o with
  | none => simp [Option.map] at h
  | some x => exact ⟨x, rfl, by simpa [Option.map] using h⟩

theorem map_len_lt {st : ScalarTy} {b : Bytes} {p : Piece} {r : Bytes}
    (h : Option.map (fun x : SVal × Bytes => (Piece.full (Val.scalar x.1), x.2))
            (parseScalarPayload st b) = some (p, r)) : r.length < b.length := by
  obtain ⟨⟨v, r0⟩, hq, hpe⟩ := map_inv h
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨_, rfl⟩ := hpe
  exact parseScalarPayload_len_lt st hq

/-- A parsed payload leaves a strictly shorter buffer behind. -/
theorem parsePiece_len_lt {ty : FieldTy} {wt : Nat} {b : Bytes} {p : Piece} {r : Bytes}
    (h : parsePiece ty wt b = some (p, r)) : r.length < b.length := by
  cases ty with
  | scalar st =>
      simp only [parsePiece] at h
      split at h
      · exact map_len_lt h
      · simp at h
  | optional st =>
      simp only [parsePiece] at h
      split at h
      · exact map_len_lt h
      · simp at h
  | message s =>
      simp only [parsePiece] at h
      split at h
      · cases hq : parseLen b with
        | none => simp [hq] at h
        | some q =>
            obtain ⟨chunk, r0⟩ := q
            simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨_, rfl⟩, rfl⟩ := h
            exact (parseLen_len hq).2
      · simp at h
  | repeated t =>
      cases t with
      | scalar st =>
          simp only [parsePiece] at h
          split at h
          · by_cases hp : st.packable
            · simp only [if_pos hp] at h
              cases hq : parseLen b with
              | none => simp [hq] at h
              | some q =>
                  obtain ⟨chunk, r0⟩ := q
                  cases hu : unpack st chunk with
                  | none => simp [hq, hu] at h
                  | some vs =>
                      cases hvi : vs.isEmpty with
                      | true => simp [hq, hu, hvi] at h
                      | false =>
                          simp only [hq, hu, hvi] at h
                          obtain ⟨_, rfl⟩ := h
                          exact (parseLen_len hq).2
            · simp only [if_neg hp] at h
              exact map_len_lt h
          · simp at h
      | message s =>
          simp only [parsePiece] at h
          split at h
          · cases hq : parseLen b with
            | none => simp [hq] at h
            | some q =>
                obtain ⟨chunk, r0⟩ := q
                simp only [hq, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨⟨_, rfl⟩, rfl⟩ := h
                exact (parseLen_len hq).2
          · simp at h
      | _ => simp [parsePiece] at h

/-- The chunk of a `.body` piece is a prefix of the buffer. -/
theorem parsePiece_body_len {ty : FieldTy} {wt : Nat} {b : Bytes} {sch : Schema}
    {chunk r : Bytes} (h : parsePiece ty wt b = some (.body sch chunk, r)) :
    chunk.length ≤ b.length := by
  cases ty with
  | message s =>
      simp only [parsePiece] at h
      split at h
      · cases hq : parseLen b with
        | none => simp [hq] at h
        | some q =>
            obtain ⟨c, r0⟩ := q
            simp only [hq, Option.some.injEq, Prod.mk.injEq, Piece.body.injEq] at h
            obtain ⟨⟨-, hcc⟩, -⟩ := h
            have hlt := (parseLen_len hq).1
            rw [hcc] at hlt
            exact hlt
      · simp at h
  | repeated t =>
      cases t with
      | message s =>
          simp only [parsePiece] at h
          split at h
          · cases hq : parseLen b with
            | none => simp [hq] at h
            | some q =>
                obtain ⟨c, r0⟩ := q
                simp only [hq, Option.some.injEq, Prod.mk.injEq, Piece.body.injEq] at h
                obtain ⟨⟨-, hcc⟩, -⟩ := h
                have hlt := (parseLen_len hq).1
                rw [hcc] at hlt
                exact hlt
          · simp at h
      | scalar st =>
          simp only [parsePiece] at h
          split at h
          · by_cases hp : st.packable
            · simp only [if_pos hp] at h
              cases hq : parseLen b with
              | none => simp [hq] at h
              | some q =>
                  obtain ⟨c, r0⟩ := q
                  cases hu : unpack st c with
                  | none => simp [hq, hu] at h
                  | some vs =>
                      by_cases hvi : vs.isEmpty
                      · simp [hq, hu, hvi] at h
                      · simp only [hq, hu, hvi] at h
                        simp at h
            · simp only [if_neg hp] at h
              obtain ⟨⟨v, r0⟩, _, hpe⟩ := map_inv h
              simp only [Prod.mk.injEq] at hpe
              simp at hpe
          · simp at h
      | _ => simp [parsePiece] at h
  | scalar _ => simp [parsePiece] at h
  | optional _ => simp [parsePiece] at h

/-- The leftover of a parsed payload is strictly shorter.  Stated for the
result pair, which is the form termination and the soundness induction use. -/
theorem parsePiece_snd_lt {ty : FieldTy} {wt : Nat} {b : Bytes} {pr : Piece × Bytes}
    (h : parsePiece ty wt b = some pr) : pr.2.length < b.length := by
  obtain ⟨p, r⟩ := pr
  exact parsePiece_len_lt h

/-- A nested message's chunk is a prefix of the buffer.  Stated for the result
pair, given the equation identifying the piece. -/
theorem parsePiece_chunk_le {ty : FieldTy} {wt : Nat} {b : Bytes} {pr : Piece × Bytes}
    (h : parsePiece ty wt b = some pr) {sch : Schema} {chunk : Bytes}
    (hp : pr.1 = .body sch chunk) : chunk.length ≤ b.length := by
  obtain ⟨p, r⟩ := pr
  change p = .body sch chunk at hp
  rw [hp] at h
  exact parsePiece_body_len h

/-- Interpret a parsed length-delimited body as a field value. -/
def assemble : FieldTy → Msg → Option Val
  | .message _, sub => some (.message sub)
  | .repeated (.message _), sub => some (.message sub)
  | _, _ => none

set_option linter.unusedVariables false in
/-- Decode a complete message body.  The matches are named because
`decreasing_by` needs their equations; they are not used in the body. -/
def decodeBody (s : Schema) (last : Nat) : Bytes → Option Msg
  | [] => some []
  | x :: xs =>
      match hvar : varintDecode (x :: xs) with
      | none => none
      | some (key, b1) =>
          match hfind : findField s (key / 8) with
          | none => none
          | some ty =>
              if key / 8 < last then none
              else if (decide (key / 8 = last) && !ty.isMulti) = true then none
              else
                match hpiece : parsePiece ty (key % 8) b1 with
                | none => none
                | some pr =>
                    (match decodeBody s (key / 8) pr.2 with
                     | none => none
                     | some rest =>
                         match hpc : pr.1 with
                         | .full v => some ((key / 8, v) :: rest)
                         | .body sch chunk =>
                             match decodeBody sch 0 chunk with
                             | none => none
                             | some sub =>
                                 match assemble ty sub with
                                 | none => none
                                 | some v => some ((key / 8, v) :: rest))
termination_by b => b.length
decreasing_by
  all_goals
    have hb1 : b1.length < (x :: xs).length := varintDecode_lt hvar
    first
    | (have hp := parsePiece_snd_lt hpiece; omega)
    | (have hp := parsePiece_chunk_le hpiece hpc; omega)

/-- Strict decoding: parse, then reject non-canonical values. -/
def decodeBodyCanon (s : Schema) (b : Bytes) : Option Msg :=
  match decodeBody s 0 b with
  | none => none
  | some m => if canonMsg s m then some m else none

end CanonicalProto
