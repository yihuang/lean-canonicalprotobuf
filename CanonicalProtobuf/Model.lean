/-
  Canonical Protobuf: the data model.

  ## Design

  A protobuf *schema* is a list of numbered fields.  A field type is a scalar,
  a nested message, a repeated field whose element type is a scalar or a
  message, or an explicitly-present (`optional`) scalar.

  The value of a message is a list of `(fieldNumber, value)` entries.  Repeated
  fields are represented by *one entry per element*: a run of adjacent entries
  that all carry the same field number.  This makes the canonical byte layout
  literally a flattening of the value:

  * every canonical message has non-decreasing field numbers,
  * two adjacent entries may share a number only for a repeated field (and
    then the elements are, by canonicity, all encoded the same way),
  * plain scalars are never encoded when they hold their default value,
  * `optional` scalars are encoded whenever present, even if zero,
  * packable repeated scalars are encoded as one *packed* length-delimited run,
  * repeated strings, bytes and messages use one length-delimited occurrence
    per element,
  * nested messages are canonical recursively,
  * strings must be valid UTF-8,
  * numeric values must lie in the canonical range of their declared type.

  Maps are deliberately excluded (as in the reference CER specification),
  because their canonical form needs a total order on keys; see README.md.

  Floating point is represented by its raw bit pattern (`fixed32`/`fixed64`):
  proto3's "deterministic" serialisation does not canonicalise `NaN` payloads
  or `-0.0`, so preserving the bits is the only choice that keeps a genuine
  bijection.  `float`/`double` fields are therefore `fixed32`/`fixed64`.
-/
import CanonicalProtobuf.Wire

namespace CanonicalProto

/-! ### Wire and scalar types -/

inductive WireType where
  | varint
  | i64
  | len
  | i32
deriving Repr, DecidableEq

def WireType.code : WireType → Nat
  | .varint => 0
  | .i64 => 1
  | .len => 2
  | .i32 => 5

inductive ScalarTy where
  | int32 | int64 | uint32 | uint64 | sint32 | sint64
  | fixed32 | fixed64 | sfixed32 | sfixed64
  | bool | enum | string | bytes
deriving Repr, DecidableEq

inductive SClass where
  | varint | i32 | i64 | len
deriving Repr, DecidableEq

def ScalarTy.cls : ScalarTy → SClass
  | .int32 | .int64 | .uint32 | .uint64 | .sint32 | .sint64 | .bool | .enum => .varint
  | .fixed32 | .sfixed32 => .i32
  | .fixed64 | .sfixed64 => .i64
  | .string | .bytes => .len

def ScalarTy.wire (st : ScalarTy) : WireType :=
  match st.cls with
  | .varint => .varint
  | .i32 => .i32
  | .i64 => .i64
  | .len => .len

/-- Packable scalars: everything except `string` and `bytes`. -/
def ScalarTy.packable (st : ScalarTy) : Bool :=
  match st.cls with
  | .varint | .i32 | .i64 => true
  | .len => false

/-- The canonical value range of a scalar type.  Signed 32-bit types are
sign-extended to 64 bits on the wire, `sint*` types hold zigzag values. -/
def ScalarTy.inRange (st : ScalarTy) (n : Nat) : Bool :=
  match st with
  | .int32 | .enum =>
      decide (n < 2 ^ 31) || (decide (2 ^ 64 - 2 ^ 31 ≤ n) && decide (n < 2 ^ 64))
  | .uint32 | .sint32 | .fixed32 | .sfixed32 => decide (n < 2 ^ 32)
  | .uint64 | .int64 | .sint64 | .fixed64 | .sfixed64 => decide (n < 2 ^ 64)
  | .bool => decide (n = 0) || decide (n = 1)
  | .string | .bytes => true

/-! ### UTF-8 validation

Strings are stored as their UTF-8 bytes; canonicity demands a well-formed
UTF-8 sequence (rejecting overlong forms and surrogates).  Only the decidable
predicate matters for the bijection. -/

def byteIn (lo hi : Nat) (x : UInt8) : Bool :=
  decide (lo ≤ x.toNat) && decide (x.toNat ≤ hi)

def utf8Valid : Bytes → Bool
  | [] => true
  | x :: xs =>
      let c := x.toNat
      if c < 0x80 then utf8Valid xs
      else if c < 0xC2 then false
      else if c < 0xE0 then
        match xs with
        | y :: ys => byteIn 0x80 0xBF y && utf8Valid ys
        | [] => false
      else if c < 0xF0 then
        match xs with
        | y :: z :: zs =>
            (if c = 0xE0 then byteIn 0xA0 0xBF y
             else if c = 0xED then byteIn 0x80 0x9F y
             else byteIn 0x80 0xBF y) &&
            byteIn 0x80 0xBF z && utf8Valid zs
        | _ => false
      else if c < 0xF5 then
        match xs with
        | y :: z :: w :: ws =>
            (if c = 0xF0 then byteIn 0x90 0xBF y
             else if c = 0xF4 then byteIn 0x80 0x8F y
             else byteIn 0x80 0xBF y) &&
            byteIn 0x80 0xBF z && byteIn 0x80 0xBF w && utf8Valid ws
        | _ => false
      else false
termination_by b => b.length

/-! ### Values and schemas -/

/-- Wire-level scalar value: a 64-bit pattern or an opaque byte sequence. -/
inductive SVal where
  | n (v : Nat)
  | s (v : Bytes)
deriving Repr, DecidableEq

/-- A protobuf value: a scalar, a nested message, or a packed run of scalars
(the value of a repeated numeric field). -/
inductive Val where
  | scalar (v : SVal)
  | message (m : List (Nat × Val))
  | repeated (vs : List SVal)
deriving Repr

abbrev Msg := List (Nat × Val)

/-- A field type.  A nested message type carries its own schema. -/
inductive FieldTy where
  | scalar (st : ScalarTy)
  | message (s : List (Nat × FieldTy))
  | repeated (t : FieldTy)
  | optional (st : ScalarTy)
deriving Repr

abbrev Schema := List (Nat × FieldTy)

/-- Field lookup by number (first match; well-formed schemas are duplicate-free). -/
def findField (s : Schema) (num : Nat) : Option FieldTy :=
  match s.find? (fun p => p.1 == num) with
  | some p => some p.2
  | none => none

/-- The wire type a field's payload uses. -/
def FieldTy.expectedWire : FieldTy → WireType
  | .scalar st => st.wire
  | .optional st => st.wire
  | .message _ => .len
  | .repeated _ => .len

/-- Repeated fields whose elements use one occurrence each (strings, bytes,
messages) occupy several adjacent entries with the same field number.
Packed repeated fields have a single entry and are therefore not `isMulti`. -/
def FieldTy.isMulti : FieldTy → Bool
  | .repeated t =>
      match t with
      | .scalar st => !st.packable
      | _ => true
  | _ => false

/-- Element types allowed in a repeated field. -/
def FieldTy.repOk : FieldTy → Bool
  | .scalar _ => true
  | .message _ => true
  | _ => false

/-! ### Well-formedness -/

mutual
/-- Field numbers are positive, below `2^29`, strictly increasing, and every
field type is itself well formed. -/
def Schema.wf : Schema → Bool
  | [] => true
  | (num, ty) :: rest =>
      decide (1 ≤ num) && decide (num < 2 ^ 29) &&
      rest.all (fun p => decide (num < p.1)) && FieldTy.wf ty && Schema.wf rest
def FieldTy.wf : FieldTy → Bool
  | .scalar _ => true
  | .optional _ => true
  | .message s => Schema.wf s
  | .repeated t => FieldTy.wf t && t.repOk
end

mutual
/-- Structural equality on values (hand-written because the types are nested). -/
def valBeq : Val → Val → Bool
  | .scalar a, .scalar b => a == b
  | .message a, .message b => msgBeq a b
  | .repeated a, .repeated b =>
      a.length == b.length && (a.zip b).all (fun p => p.1 == p.2)
  | _, _ => false
def msgBeq : Msg → Msg → Bool
  | [], [] => true
  | (n1, v1) :: r1, (n2, v2) :: r2 => n1 == n2 && valBeq v1 v2 && msgBeq r1 r2
  | _, _ => false
end

instance : BEq Val := ⟨valBeq⟩
instance : BEq Msg := ⟨msgBeq⟩

/-- `isMulti` of the field with the given number (false if unknown). -/
def isMultiField (s : Schema) (num : Nat) : Bool :=
  match findField s num with
  | some ty => ty.isMulti
  | none => false

/-! ### Canonicality -/

def SVal.ok (st : ScalarTy) : SVal → Bool
  | .n v =>
      (match st.cls with
       | .varint => true
       | .i32 => decide (v < 2 ^ 32)
       | .i64 => decide (v < 2 ^ 64)
       | .len => false) && st.inRange v
  | .s b =>
      (match st.cls with
       | .len => true
       | _ => false) &&
      (match st with
       | .string => utf8Valid b
       | _ => true)

def SVal.isDefault : SVal → Bool
  | .n v => v == 0
  | .s b => b.isEmpty

mutual
/-- All field numbers are positive. -/
def numsOk : Msg → Bool
  | [] => true
  | (n, _) :: rest => decide (1 ≤ n) && numsOk rest
/-- Field numbers are non-decreasing; equal neighbours only for multi-occurrence
(repeated) fields. -/
def sortedOk (s : Schema) : Msg → Bool
  | [] => true
  | [_] => true
  | (n, _) :: rest@(_ :: _) =>
      (match rest with
       | (n', _) :: _ => decide (n < n') || (decide (n = n') && isMultiField s n)
       | [] => true) &&
      sortedOk s rest
/-- Every field is known to the schema and its value is canonical. -/
def fieldsOk (s : Schema) : Msg → Bool
  | [] => true
  | (n, v) :: rest =>
      (match findField s n with
       | some ty => canonField ty v
       | none => false) &&
      fieldsOk s rest
/-- Canonical value for a single field occurrence. -/
def canonField : FieldTy → Val → Bool
  | .scalar st, .scalar sv => sv.ok st && !sv.isDefault
  | .optional st, .scalar sv => sv.ok st
  | .message s, .message m => canonMsg s m
  | .repeated t, v => canonRep t v
  | _, _ => false
/-- Canonical value of a repeated field: a nonempty packed run for packable
numeric scalars, one element otherwise. -/
def canonRep : FieldTy → Val → Bool
  | .scalar st, .repeated vs => st.packable && !vs.isEmpty && vs.all (fun sv => sv.ok st)
  | .scalar st, .scalar sv => !st.packable && sv.ok st
  | .message s, .message m => canonMsg s m
  | _, _ => false
/-- A canonical message. -/
def canonMsg (s : Schema) : Msg → Bool
  | m => numsOk m && sortedOk s m && fieldsOk s m
end

/-- Ordering invariant used by the decoder: each entry's field number is
strictly greater than `last`, or equal to it when the field is a repeated
(multi-occurrence) field. -/
def orderOk (s : Schema) (last : Nat) : Msg → Bool
  | [] => true
  | (num, _) :: rest =>
      (decide (last < num) || (decide (last = num) && isMultiField s num)) &&
      orderOk s num rest

end CanonicalProto
