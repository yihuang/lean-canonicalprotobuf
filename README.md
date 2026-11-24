# Canonical Protobuf in Lean 4

A **canonical** subset of Protocol Buffers 3 — one value, one byte string — with an
executable encoder, a decoder that accepts *only* canonical bytes, and a
machine-checked proof that the two are mutually inverse.

```lean
theorem bijection (s : Schema) :
    (∀ m : CanonicalMsg s, decode s (encode s m) = some m) ∧          -- round trip
    (∀ (b : Bytes) (m : CanonicalMsg s), decode s b = some m → encode s m = b) ∧
    (∀ m₁ m₂ : CanonicalMsg s, encode s m₁ = encode s m₂ → m₁ = m₂)   -- injective
```

Status: **every theorem is proved, no `sorry`**, no dependencies beyond Lean core
(≈2.2k lines). The only axioms are `propext`, `Quot.sound` and `Classical.choice`.

```
CanonicalProtobuf/
  Wire.lean       minimal varints, little-endian fixed integers, length prefixes
  Model.lean      schemas, values, the canonicity predicate `canonMsg`
  Encode.lean     the canonical encoder
  Decode.lean     the strict decoder
  Proofs.lean     payload lemmas; decoder soundness and completeness
  Bijection.lean  `encode`/`decode` on canonical messages; the bijection
  Examples.lean   27 build-time checks (round trips and rejections)
```

## Why canonical, not merely deterministic

Proto3 has a "deterministic" serialisation mode, but it is not *canonical*: map
ordering is left to the implementation, `NaN` payloads and `-0.0` survive, and
unknown fields are preserved, so two conforming encoders can produce different
bytes for the same value. That is fine for caching heuristics and fatal for
anything that hashes, signs, or content-addresses wire bytes.

The fix used here is to carve out a subset of the format where the encoding is a
genuine bijection, and to make the decoder *reject* everything outside it —
over-long varints, unpacked repeated runs, unknown fields, wrong field order,
duplicate singular fields, non-minimal nesting. "Deterministic" then becomes a
theorem rather than a promise, and a canonicalisation function is unnecessary:
invalid inputs have no canonical form at all.

The design was derived from first principles;
[regen-network/canonical-proto3] (the "CER" rules) was used as a sanity check.

[regen-network/canonical-proto3]: https://github.com/regen-network/canonical-proto3

## Quick start

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned by
`lean-toolchain`.

```sh
lake build     # compiles the proofs and runs the build-time checks
```

```lean
import CanonicalProtobuf

open CanonicalProto

/-- `message User { string name = 1; int32 id = 2; repeated uint32 scores = 3; }` -/
def userSchema : Schema :=
  [(1, .scalar .string), (2, .scalar .int32), (3, .repeated (.scalar .uint32))]

def alice : Msg :=
  [(1, .scalar (.s (bytes [0x61, 0x6C]))),  -- name = "al"
   (2, .scalar (.n 7)),                     -- id = 7
   (3, .repeated [.n 1, .n 300])]           -- scores = [1, 300]

#eval encodeMsg userSchema alice                                -- [10, 2, 97, 108, 16, 7, 26, 3, 1, 172, 2]
#eval canonMsg userSchema alice                                 -- true
#eval (decode userSchema (encodeMsg userSchema alice)).isSome    -- true
#eval (decode userSchema (bytes [0x10, 0x80, 0x00])).isNone      -- true: over-long varint
```

(`bytes : List Nat → Bytes` is a convenience from `Examples.lean`; `Bytes` is
`List UInt8`.)

## The verified interface

The codec is presented in layers, so that the proofs can talk about the codec
and the API about canonical messages:

| layer | type | role |
|---|---|---|
| `encodeMsg s : Msg → Bytes` | total | encodes any message; only correct on canonical ones |
| `decodeBody : Schema → Nat → Bytes → Option Msg` | strict | core decoder, well-founded recursion on the buffer length |
| `decodeBodyCanon : Schema → Bytes → Option Msg` | strict | `decodeBody s 0 b`, then `canonMsg` re-validation |
| `encode` / `decode` | `CanonicalMsg s ↔ Bytes` | the verified API |

`CanonicalMsg s` is the subtype `{m // canonMsg s m = true}`, so a non-canonical
value cannot even be passed to `encode`; `decode` returns `Option (CanonicalMsg s)`
and is therefore total with no separate validity check at the call site.

For any canonical message:

```lean
example (m : CanonicalMsg userSchema) : decode userSchema (encode userSchema m) = some m :=
  decode_encode m

example (b : Bytes) (m : CanonicalMsg userSchema) :
    (decode userSchema b = some m) ↔ (encode userSchema m = b) :=
  decode_eq_some_iff userSchema b m
```

The second is the sharp form of "strict": the decoder's accepted set is *exactly*
the image of the encoder, and each accepted byte string has a unique preimage.

## Canonical form

A schema is a list of numbered fields; a field type is `scalar st`,
`message schema`, `repeated t` or `optional st`. A message is a list of
`(fieldNumber, value)` entries; a repeated field is written as adjacent entries
sharing its number, and a packed run as one `.repeated` entry.

| rule | enforced by |
|---|---|
| field numbers strictly increasing (equal only for repeated fields) | `sortedOk` |
| no default-valued plain scalars (`0`, `false`, `""`, empty bytes, enum 0) | `canonField` |
| `optional` scalars always encoded, defaults included | `canonField` |
| packable repeated scalars: exactly one packed run, never empty | `canonRep` |
| repeated strings/bytes/messages: one length-delimited occurrence per element | `canonRep`, `FieldTy.isMulti` |
| nested messages canonical recursively; every field number known | `fieldsOk` |
| `bool` ∈ {0, 1}; integers in their declared range | `SVal.ok`, `inRange` |
| `int32`/`enum` sign-extended to 64 bits on the wire; `sint*` zigzag | `inRange`, `Encode` |
| strings valid UTF-8 (no overlong forms, no surrogates) | `utf8Valid` |
| minimal varints; exactly 4/8 bytes for `fixed32`/`fixed64` | `Wire.lean` |
| over-long varints, unpacked runs, unknown fields, wrong order, duplicates, trailing bytes rejected | `decodeBody` |

## Scope

This is a codec model, not a protobuf compiler: schemas are Lean values, and
there is no `.proto` parser, no code generation, and no JSON/text format.

Deliberately out of scope:

* **Maps** — a canonical map needs a total order on keys, and that ordering
  interacts with default omission in ways worth their own proof. (The reference
  CER spec excludes them too.)
* **`oneof` and groups** — not modelled.
* **`float`/`double`** — represented by their IEEE-754 bit patterns, spelled
  `fixed32`/`fixed64`. Deterministic proto3 does not canonicalise `NaN` payloads
  or `-0.0`, so preserving bits is the only choice that keeps a bijection.
* **Unknown-field preservation, extensions, wire compatibility** — with ordinary
  protobuf data this decoder will often reject rather than decode; that is the
  point, not a defect.

`encodeMsg` is total and returns `[]` on malformed input; well-definedness is a
hypothesis (`canonMsg`), not a check inside the encoder.

## What is proved

**Wire level** (`Wire.lean`) — `varintDecode_encode` (decode inverts the minimal
encoding, for every `n`), `varintDecode_sound` (successful decode implies the
input *is* the minimal encoding), `leRead_leBytes`/`leRead_bytes` (fixed-width
round trips), `split_sound`/`split_of_length` (length prefixes).

**Payloads** (`Proofs.lean`) — `parseScalarPayload_sound`/`_complete`,
`parseLen_sound`/`_complete`, `unpack_sound`/`unpack_complete`: the scalar,
length-delimited and packed-run codecs are inverse on canonical payloads.
`parsePiece_full_sound` and `parsePiece_complete` lift this to whole fields and
carry the matching encoder equation.

**Decoder** (`Proofs.lean`, `Bijection.lean`)

| theorem | statement |
|---|---|
| `decodeBody_sound` | accepted bytes re-encode to themselves |
| `decodeBody_complete` | every canonical encoding is accepted and recovered (given `orderOk`) |
| `decodeBodyCanon_encodeMsg` | the strict top-level decoder inverts `encodeMsg` |
| `decode_injective` | at most one message decodes from any byte string |
| `decode_eq_some_iff` | accepted set = image of `encode`, preimage unique |

## Design notes

**Canonicity is a predicate, not a normalisation function.**
`canonMsg s : Msg → Bool` characterises legal values, and the theorems are stated
at `{m // canonMsg s m}`. Since sortedness and default-omission are hypotheses,
the encoder never sorts or repairs anything, and the round-trip proof is a
structural induction rather than an argument about a sorting algorithm. The price
is that the encoder is only *correct* on canonical inputs — which is exactly what
the subtype enforces.

**Repeated fields are one entry per element.** For packable scalars a repeated
field is a single packed entry; for strings, bytes and messages it is a run of
adjacent entries with the same field number. The decoder therefore never *merges*
occurrences: it conses each parsed element and requires that non-increasing field
numbers occur only on repeated fields. An earlier design merged during parsing,
which complicated both the decoder and its proof considerably.

**Termination is well-founded recursion on the buffer length.** `decodeBody`
recurses on a *suffix* of its input rather than on a subterm, so no structural
decrease is available — but no fuel argument is needed either: every parse step
consumes at least one byte (`varintDecode_lt`, `leRead`, `split`), so both the
remaining buffer and a nested message's chunk are strictly shorter than the
buffer being parsed. Both `decodeBody` and `unpackAux` are therefore declared
`termination_by b.length`, and `decreasing_by` discharges the two obligations
from the "returns a suffix" lemmas `parsePiece_snd_lt` and `parsePiece_chunk_le`;
`utf8Valid` already used the same device. An earlier version threaded an explicit
`Nat` fuel instead, which made every completeness statement carry a
`(encodeMsg s m).length ≤ fuel` hypothesis for no mathematical gain.

**The one real proof obstacle** is an elaborator problem, not a mathematical one.
`decodeBody` matches on the byte list, so its equation lemma only fires when the
buffer is *syntactically* a cons. Completeness must evaluate it at
`encodeMsg s m`, which is an **append** built by a `brecOn` recursion — and the
key prefix `varintEncode key` is not syntactically a cons either, so `rw`/`simp`
refuse to reduce the `match`.

The fix is one generic unfolding lemma,

```lean
theorem decodeBody_key (s last key ty pr k1 ks rest)
    (hk : varintEncode key = k1 :: ks) (hfind : findField s (key / 8) = some ty)
    (hpiece : parsePiece ty (key % 8) rest = some pr) ... :
    decodeBody s last (k1 :: (ks ++ rest)) = ...decoder step...
```

after which completeness is routine: destruct `varintEncode key` into `k1 :: ks`
(`varintEncode_nonempty` eliminates the empty case), reassociate the append into
cons form, apply `decodeBody_key` with the `findField` and `parsePiece` equations
that the branch already knows, and discharge one goal per field type with
`parsePiece_complete` plus the induction hypothesis.

## Tests

`Examples.lean` runs 27 checks at compile time; a failing check fails the build:

```
ok: person encodes to the expected bytes
ok: person round-trips
ok: default scalar is not canonical
ok: optional zero encodes its presence
ok: over-long varint is rejected
ok: wrong field order is rejected
ok: non-canonical nested message is rejected
ok: min int32 is a ten-byte sign-extended varint
ok: sint32 zigzags -150 to 300
ok: fixed32 is little-endian
ok: invalid UTF-8 is not canonical
...
```

They cover round trips (including empty nested messages), default omission versus
explicit `optional` presence, sign-extended `int32`, zigzag `sint32`,
little-endian `fixed32`, `bool` range checks, UTF-8 validation, out-of-range
integers, and rejection of over-long varints, unknown fields, wrong field order,
unpacked runs, truncated payloads and non-canonical nesting.
