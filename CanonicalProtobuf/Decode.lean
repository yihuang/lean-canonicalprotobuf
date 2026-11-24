/-
  Canonical Protobuf: the strict decoder.
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

/-- Read a packed run, bounded by `fuel` elements. -/
def unpackAux (st : ScalarTy) : Nat → Bytes → Option (List SVal × Bytes)
  | 0, b => some ([], b)
  | fuel + 1, [] => some ([], [])
  | fuel + 1, x :: xs =>
      match parseScalarPayload st (x :: xs) with
      | none => none
      | some (v, rest) =>
          match unpackAux st fuel rest with
          | none => none
          | some (vs, r) => some (v :: vs, r)

/-- Read a packed run, requiring it to consume the whole buffer. -/
def unpack (st : ScalarTy) (b : Bytes) : Option (List SVal) :=
  match unpackAux st b.length b with
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

/-- Interpret a parsed length-delimited body as a field value. -/
def assemble : FieldTy → Msg → Option Val
  | .message _, sub => some (.message sub)
  | .repeated (.message _), sub => some (.message sub)
  | _, _ => none

/-- Decode a complete message body.  `fuel` bounds the nesting depth. -/
def decodeBody : Nat → Schema → Nat → Bytes → Option Msg
  | 0, _, _, _ => none
  | fuel + 1, s, last, b =>
      match b with
      | [] => some []
      | _ =>
          match varintDecode b with
          | none => none
          | some (key, b1) =>
              let num := key / 8
              let wt := key % 8
              match findField s num with
              | none => none
              | some ty =>
                  if num < last then none
                  else if (decide (num = last) && !ty.isMulti) = true then none
                  else
                    match parsePiece ty wt b1 with
                    | none => none
                    | some (piece, b2) =>
                        (match decodeBody fuel s num b2 with
                         | none => none
                         | some rest =>
                             match piece with
                             | .full v => some ((num, v) :: rest)
                             | .body sch chunk =>
                                 match decodeBody fuel sch 0 chunk with
                                 | none => none
                                 | some sub =>
                                     match assemble ty sub with
                                     | none => none
                                     | some v => some ((num, v) :: rest))

/-- Strict decoding: parse, then reject non-canonical values. -/
def decodeBodyCanon (s : Schema) (b : Bytes) : Option Msg :=
  match decodeBody (b.length + 1) s 0 b with
  | none => none
  | some m => if canonMsg s m then some m else none

end CanonicalProto
