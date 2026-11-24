/-
  Canonical Protobuf: executable examples.

  Each `#eval check` is evaluated by the compiler during `lake build`; a failing
  check aborts the build, so building the project doubles as a test suite for
  the encoder, the strict decoder and the canonicity predicate.
-/
import CanonicalProtobuf.Proofs

namespace CanonicalProto

/- Build-time assertion: throws (failing the build) when `b` is false. -/
def check (name : String) (b : Bool) : IO Unit :=
  if b then IO.println s!"ok: {name}"
  else throw (IO.userError s!"FAILED: {name}")

def bytes (xs : List Nat) : Bytes := xs.map (fun n => UInt8.ofNat n)

/- Round-trip check: decoding the canonical encoding recovers the value. -/
def roundtrip (s : Schema) (m : Msg) : Bool :=
  match decodeBodyCanon s (encodeMsg s m) with
  | some m' => msgBeq m m'
  | none => false

/- Strictness check: the decoder rejects `b` outright. -/
def rejected (s : Schema) (b : Bytes) : Bool := (decodeBodyCanon s b).isNone

/-! ### A schema and an example message

```proto
message Friend { string name = 1; int32 id = 2; }
message Person {
  string          name   = 1;
  int32           id     = 2;
  repeated uint32 scores = 3;   // packed
  string          email  = 4;
  Friend          friend = 5;
  repeated string tags   = 6;   // one occurrence per element
}
```
-/

def friendSchema : Schema := [(1, .scalar .string), (2, .scalar .int32)]

def personSchema : Schema :=
  [(1, .scalar .string), (2, .scalar .int32), (3, .repeated (.scalar .uint32)),
   (4, .scalar .string), (5, .message friendSchema), (6, .repeated (.scalar .string))]

def al : Bytes := bytes [0x41, 0x6C]      -- "Al"
def xs : Bytes := bytes [0x78]            -- "x"
def ys : Bytes := bytes [0x79]            -- "y"

def person1 : Msg :=
  [(1, .scalar (.s al)), (2, .scalar (.n 42)), (3, .repeated [.n 1, .n 300]),
   (6, .scalar (.s xs)), (6, .scalar (.s ys))]

def person1Bytes : Bytes := bytes [0x0a, 0x02, 0x41, 0x6c, 0x10, 0x2a,
  0x1a, 0x03, 0x01, 0xac, 0x02, 0x32, 0x01, 0x78, 0x32, 0x01, 0x79]

#eval check "person encodes to the expected bytes"
  (encodeMsg personSchema person1 == person1Bytes)
#eval check "person is canonical" (canonMsg personSchema person1)
#eval check "person round-trips" (roundtrip personSchema person1)

/-! ### Nested messages -/

def nested : Msg := [(5, .message [(1, .scalar (.s al))])]
#eval check "nested message round-trips" (roundtrip personSchema nested)
#eval check "empty nested message round-trips"
  (roundtrip personSchema [(5, .message [])])

/-! ### Defaults and explicit presence -/

def optInt32 : Schema := [(1, .optional .int32)]
#eval check "default scalar is not canonical"
  (!(canonMsg personSchema [(2, .scalar (.n 0))]))
#eval check "optional zero encodes its presence"
  (encodeMsg optInt32 [(1, .scalar (.n 0))] == bytes [0x08, 0x00])
#eval check "optional zero is canonical" (canonMsg optInt32 [(1, .scalar (.n 0))])

/-! ### Strict rejection

Over-long varint, wrong field order, unknown field, unpacked run, truncated
payload, and a nested message with a default scalar written out. -/

#eval check "over-long varint is rejected"
  (rejected personSchema (bytes [0x10, 0x80, 0x00]))
#eval check "wrong field order is rejected"
  (rejected personSchema (bytes [0x10, 0x01, 0x08, 0x41]))
#eval check "unknown field is rejected"
  (rejected personSchema (bytes [0x78, 0x01]))
#eval check "unpacked run is rejected"
  (rejected personSchema (bytes [0x18, 0x01]))
#eval check "truncated payload is rejected"
  (rejected personSchema (bytes [0x0a, 0x02, 0x41]))
#eval check "non-canonical nested message is rejected"
  (rejected friendSchema (bytes [0x0a, 0x01, 0x41, 0x10, 0x00]))

/-! ### Integer encodings -/

def minInt32 : Msg := [(1, .scalar (.n (2 ^ 64 - 1)))]   -- -2147483648, sign-extended
def minInt32Bytes : Bytes := bytes [0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0x01]

#eval check "min int32 is a ten-byte sign-extended varint"
  (encodeMsg [(1, .scalar .int32)] minInt32 == minInt32Bytes)
#eval check "min int32 round-trips" (roundtrip [(1, .scalar .int32)] minInt32)

#eval check "sint32 zigzags -1 to 1"
  (encodeMsg [(1, .scalar .sint32)] [(1, .scalar (.n 1))] == bytes [0x08, 0x01])
#eval check "sint32 zigzags -150 to 300"
  (encodeMsg [(1, .scalar .sint32)] [(1, .scalar (.n 300))] == bytes [0x08, 0xac, 0x02])

#eval check "fixed32 is little-endian"
  (encodeMsg [(1, .scalar .fixed32)] [(1, .scalar (.n 0x01020304))]
    == bytes [0x0d, 0x04, 0x03, 0x02, 0x01])

/-! ### Range and UTF-8 checks -/

#eval check "bool 1 is canonical" (canonMsg [(1, .scalar .bool)] [(1, .scalar (.n 1))])
#eval check "bool 2 is not canonical"
  (!(canonMsg [(1, .scalar .bool)] [(1, .scalar (.n 2))]))

def bigUint32 : Msg := [(1, .scalar (.n (2 ^ 32)))]
#eval check "uint32 above 2^32 is not canonical"
  (!(canonMsg [(1, .scalar .uint32)] bigUint32))
#eval check "uint32 above 2^32 is rejected on the wire"
  (rejected [(1, .scalar .uint32)] (bytes [0x08, 0x80, 0x80, 0x80, 0x80, 0x10]))

#eval check "invalid UTF-8 is not canonical"
  (!(canonMsg [(1, .scalar .string)] [(1, .scalar (.s (bytes [0xff])))]))
#eval check "valid UTF-8 is canonical"
  (canonMsg [(1, .scalar .string)] [(1, .scalar (.s al))])

/-! ### Repeated fields -/

def tagSchema : Schema := [(1, .repeated (.scalar .string))]
#eval check "empty repeated element is accepted"
  ((decodeBodyCanon tagSchema (bytes [0x0a, 0x00])).isSome)
#eval check "repeated string is canonical"
  (canonMsg tagSchema [(1, .scalar (.s al))])

end CanonicalProto
