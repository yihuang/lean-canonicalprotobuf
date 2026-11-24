/-
  Canonical Protobuf: executable examples.

  `#guard` checks are evaluated by the compiler at build time.
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

/-! ```proto
message Friend { string name = 1; int32 id = 2; }
message Person {
  string          name   = 1;
  int32           id     = 2;
  repeated uint32 scores = 3;   // packed
  string          email  = 4;
  Friend          friend = 5;
  repeated string tags   = 6;   // one occurrence per element
}
``` -/
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

#eval check "example" (encodeMsg personSchema person1 == person1Bytes)
#eval check "example" (canonMsg personSchema person1 == true)
#eval check "example" (roundtrip personSchema person1)

/- Nested messages, including an empty one, round-trip. -/
def nested : Msg := [(5, .message [(1, .scalar (.s al))])]
#eval check "example" (roundtrip personSchema nested)
#eval check "example" (roundtrip personSchema [(5, .message [])])

/- Default scalars are not canonical ... -/
#eval check "example" (canonMsg personSchema [(2, .scalar (.n 0))] == false)
/- ... while explicit `optional` presence is. -/
#eval check "example" (encodeMsg [(1, .optional .int32)] [(1, .scalar (.n 0))] == bytes [0x08, 0x00])
#eval check "example" (canonMsg [(1, .optional .int32)] [(1, .scalar (.n 0))] == true)

/- Strict rejection: over-long varint, wrong order, unknown field, unpacked run,
truncated payload. -/
#eval check "example" ((decodeBodyCanon personSchema (bytes [0x10, 0x80, 0x00])).isNone)
#eval check "example" ((decodeBodyCanon personSchema (bytes [0x10, 0x01, 0x08, 0x41])).isNone)
#eval check "example" ((decodeBodyCanon personSchema (bytes [0x78, 0x01])).isNone)
#eval check "example" ((decodeBodyCanon personSchema (bytes [0x18, 0x01])).isNone)
#eval check "example" ((decodeBodyCanon personSchema (bytes [0x0a, 0x02, 0x41])).isNone)

/- A non-canonical nested message is rejected (default scalar written out). -/
#eval check "example" ((decodeBodyCanon friendSchema (bytes [0x0a, 0x01, 0x41, 0x10, 0x00])).isNone)

/- Negative int32: ten-byte sign-extended varint. -/
def minInt32 : Bytes := bytes [0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01]
#eval check "example" (encodeMsg [(1, .scalar .int32)] [(1, .scalar (.n (2 ^ 64 - 1)))] == minInt32)
#eval check "example" (roundtrip [(1, .scalar .int32)] [(1, .scalar (.n (2 ^ 64 - 1)))])

/- `sint32` zigzag: 1 denotes -1; 300 denotes 150. -/
#eval check "example" (encodeMsg [(1, .scalar .sint32)] [(1, .scalar (.n 1))] == bytes [0x08, 0x01])
#eval check "example" (encodeMsg [(1, .scalar .sint32)] [(1, .scalar (.n 300))] == bytes [0x08, 0xac, 0x02])

/- `fixed32` is little-endian. -/
#eval check "example" (encodeMsg [(1, .scalar .fixed32)] [(1, .scalar (.n 0x01020304))] == bytes [0x0d, 0x04, 0x03, 0x02, 0x01])

/- `bool` is canonical only for 0 and 1. -/
#eval check "example" (canonMsg [(1, .scalar .bool)] [(1, .scalar (.n 1))] == true)
#eval check "example" (canonMsg [(1, .scalar .bool)] [(1, .scalar (.n 2))] == false)

/- Values outside the declared range are rejected. -/
#eval check "example" (canonMsg [(1, .scalar .uint32)] [(1, .scalar (.n (2 ^ 32)))] == false)
#eval check "example" ((decodeBodyCanon [(1, .scalar .uint32)] (bytes [0x08, 0x80, 0x80, 0x80, 0x80, 0x10])).isNone)

/- Strings must be valid UTF-8. -/
#eval check "example" (canonMsg [(1, .scalar .string)] [(1, .scalar (.s (bytes [0xff])))] == false)
#eval check "example" (canonMsg [(1, .scalar .string)] [(1, .scalar (.s al))] == true)

/- Repeated strings are one occurrence each; empty runs are not canonical. -/
#eval check "example" ((decodeBodyCanon [(1, .repeated (.scalar .string))] (bytes [0x0a, 0x00])).isSome)
#eval check "example" (canonMsg [(1, .repeated (.scalar .string))] [(1, .scalar (.s al))] == true)

end CanonicalProto
