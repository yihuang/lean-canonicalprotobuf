/-
  Canonical Protobuf: the canonical encoder.
-/
import CanonicalProtobuf.Model

namespace CanonicalProto

/-- The field key: `(number << 3) | wireType`. -/
def keyBytes (num : Nat) (wt : WireType) : Bytes :=
  varintEncode (num * 8 + wt.code)

/-- Payload of a scalar, including the length prefix for string/bytes. -/
def payloadOf (st : ScalarTy) (v : SVal) : Bytes :=
  match st.cls, v with
  | .varint, .n n => varintEncode n
  | .i32, .n n => leBytes 4 n
  | .i64, .n n => leBytes 8 n
  | .len, .s b => varintEncode b.length ++ b
  | _, _ => []

/-- Payload of one element inside a packed run (no length prefix). -/
def packedOf (st : ScalarTy) (v : SVal) : Bytes :=
  match st.cls, v with
  | .varint, .n n => varintEncode n
  | .i32, .n n => leBytes 4 n
  | .i64, .n n => leBytes 8 n
  | _, _ => []

/-- Concatenated payloads of a packed run. -/
def packConcat (st : ScalarTy) : List SVal → Bytes
  | [] => []
  | v :: vs => packedOf st v ++ packConcat st vs

mutual
/-- Encode a canonical message against its schema. -/
def encodeMsg (s : Schema) : Msg → Bytes
  | [] => []
  | (num, v) :: rest =>
      (match findField s num with
       | some ty => encodeField num ty v
       | none => []) ++ encodeMsg s rest
/-- Encode one field occurrence. -/
def encodeField (num : Nat) : (ty : FieldTy) → Val → Bytes
  | .scalar st, .scalar sv => keyBytes num st.wire ++ payloadOf st sv
  | .optional st, .scalar sv => keyBytes num st.wire ++ payloadOf st sv
  | .message s, .message m =>
      keyBytes num .len ++ varintEncode (encodeMsg s m).length ++ encodeMsg s m
  | .repeated (.scalar st), .repeated vs =>
      if st.packable then
        keyBytes num .len ++ varintEncode (packConcat st vs).length ++ packConcat st vs
      else []
  | .repeated t, v => keyBytes num .len ++ elemPayload t v
  | _, _ => []
/-- Length-delimited payload of one repeated element (one occurrence each). -/
def elemPayload : (t : FieldTy) → Val → Bytes
  | .scalar st, .scalar sv => payloadOf st sv
  | .message s, .message m =>
      varintEncode (encodeMsg s m).length ++ encodeMsg s m
  | _, _ => []
end

end CanonicalProto
