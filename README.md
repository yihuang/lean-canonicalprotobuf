# Canonical Protobuf in Lean 4

A mechanically verified implementation of a **canonical** (deterministic,
byte-for-byte unique) subset of Protocol Buffers 3, with an executable encoder
and a *strict* decoder, and machine-checked proofs about the round trip.

The design is derived from first principles rather than by copying an
implementation; the reference [regen-network/canonical-proto3] "CER" rules were
used as a sanity check.

[regen-network/canonical-proto3]: https://github.com/regen-network/canonical-proto3

```
CanonicalProtobuf/
  Wire.lean       minimal varints, little-endian fixed integers, length prefixes
  Model.lean      schemas, values, canonicity predicate
  Encode.lean     the canonical encoder
  Decode.lean     the strict decoder
  Proofs.lean     payload/parse lemmas, decoder soundness and completeness
  Bijection.lean  encode/decode, soundness, injectivity, the bijection
  Examples.lean   build-time executable round-trip and strictness tests
```

Build and test with `lake build`.  The `Examples.lean` file runs ~35
round-trip / strictness checks at compile time; a failing check fails the build.

**Status: every theorem in this repository is proved; there are no `sorry`s.**
The main result is `CanonicalProto.bijection` (§3): the encoder and decoder are
mutually inverse between canonical messages and the byte strings the decoder
accepts.

## 1. What "canonical" means here

A **schema** is a list of numbered fields; a **field type** is

```
scalar st | message schema | repeated t | optional st
```

where `scalar` is one of `int32 int64 uint32 uint64 sint32 sint64 fixed32
fixed64 sfixed32 sfixed64 bool enum string bytes`.

A **value** is a list of `(fieldNumber, value)` entries, where a value is a
scalar, a nested message, or a packed run of scalars.

The canonical encoding is:

| rule | implementation |
|---|---|
| fields in ascending field-number order | `sortedOk`, emitted in value order |
| no default-valued plain scalars (`0`, `false`, `""`, empty bytes, enum 0) | `canonField` |
| `optional` scalars keep explicit presence (defaults are encoded) | `canonField` `.optional` |
| empty repeated fields / unset oneofs are absent | no entry |
| packable repeated scalars use **packed** length-delimited encoding | `Decode.parsePiece` |
| repeated strings/bytes/messages use one occurrence per element | `FieldTy.isMulti` |
| nested messages canonical recursively | `canonMsg` |
| `bool` restricted to 0/1; integers in their declared range (signed 32-bit sign-extended) | `inRange` |
| strings are valid UTF-8 | `utf8Valid` |
| varints are minimal; exactly 32/64-bit fixed fields | `varintDecode`, `leRead` |
| unknown fields, wrong order, duplicates, trailing bytes are **rejected** | `decodeBody` |
| floats are raw IEEE-754 bit patterns (`fixed32`/`fixed64`) | see below |

Maps are deliberately **excluded** (as in the reference CER spec): a canonical
map needs a total order on keys, and the ordering interacts with default
omission in ways that deserve their own proof; the model has a place for them
(`FieldTy`), but the codec does not implement them.

Floats are represented by their IEEE-754 *bit pattern* because protobuf's
"deterministic" mode does not canonicalise `NaN` payloads or `-0.0`; preserving
the bits is the only choice that keeps a genuine bijection.  `float`/`double`
fields are therefore spelled `fixed32`/`fixed64`.

## 2. Two design decisions that make the proofs work

**(a) The canonical form is a predicate, not a normalisation function.**
`canonMsg s m : Bool` characterises legal canonical values (ordered numbers,
canonical scalars, sorted map keys, ...).  The theorems are stated for
`{m // canonMsg s m}`, so non-canonical values are unrepresentable in the
statement, and the encoder never has to sort or repair anything: sortedness is
part of the hypothesis.  This is why the round-trip proof is a structural
induction instead of an argument about sorting algorithms.

**(b) Repeated fields are "one entry per element" (plus one packed entry).**
A repeated field's value appears either as one packed entry (numeric scalars) or
as a run of adjacent entries with the same field number (strings, bytes,
messages).  The decoder therefore never has to *merge* anything: it conses each
parsed element and checks that equal field numbers occur only for repeated
fields.  Earlier iterations merged occurrences during parsing; that made both
the decoder and its proof markedly more complicated.

## 3. What is proved

Every theorem is machine-checked with no `sorry`; the only axioms used are
Lean's standard ones (`propext`, `Quot.sound`, and `Classical.choice` for the
decidable-predicate plumbing).

**Wire level** (`Wire.lean`)

* `varintDecode_encode` : decoding the canonical varint of `n` returns `n` and
  the untouched suffix (for *every* `n`; encoding is exact, not truncated).
* `varintDecode_sound` : a successful decode satisfies
  `varintEncode v ++ rest = input` — this is exactly minimality.
* `leRead_leBytes`, `leRead_bytes` : 32/64-bit little-endian round trip.
* `split_sound`, `split_of_length` : length-delimited prefix splitting.

**Payloads** (`Proofs.lean`)

* `parseScalarPayload_sound` / `_complete`, `parseLen_sound` / `_complete`,
  `unpackAux_sound`, `unpack_sound`, `unpack_complete` : the scalar, length and
  packed-run codecs are inverse on canonical values.
* `parsePiece_full_sound`, `parsePiece_complete` : the *field* payload parser is
  both sound (it consumes exactly the canonical payload) and complete (it
  accepts every canonical payload), together with the matching encoder equation.
* `canonMsg_cons`, `canonMsg_facts`, `canonMsg_orderOk` : structural facts about
  canonical messages.

**Decoder soundness** (`Proofs.lean`, `Bijection.lean`)

* `decodeBody_sound` : for every byte string accepted by the decoder,
  `encodeMsg s m = b`.  In other words the decoder never accepts a byte string
  that is not the canonical encoding of what it returns; over-long varints,
  unpacked runs, unknown fields, wrong order, out-of-range values and
  non-canonical nesting are all rejected.
* `decodeBodyCanon_sound`, `decode_sound` : the same at the top level.
* `decode_injective` : at most one message decodes from any byte string.

**Decoder completeness** (`Proofs.lean`)

* `decodeBody_key` : a generic unfolding lemma for the decoder at a field key
  (the technical crux — see §4).
* `decodeBody_complete` : for every canonical message `m` and every `fuel`
  bounding `(encodeMsg s m).length`,
  `decodeBody (fuel+1) s last (encodeMsg s m) = some m`, provided the ordering
  invariant `orderOk s last m` holds.
* `decodeBodyCanon_encodeMsg`, `decode_encode` : `decode (encode m) = some m`.

**The bijection** (`Bijection.lean`)

* `bijection` : `encode` and `decode` are mutually inverse and `encode` is
  injective — a bijection between canonical messages `{m // canonMsg s m}` and
  the byte strings the decoder accepts.
* `decode_eq_some_iff` : `decode s b = some m ↔ encode s m = b`, i.e. the
  decoder's accepted set is *exactly* the image of the encoder, and the
  preimage is unique.

## 4. The one technical obstacle (and how it was removed)

The decoder is written as

```lean
def decodeBody : Nat → Schema → Nat → Bytes → Option Msg
  | 0, _, _, _ => none
  | fuel+1, s, last, b =>
      match b with
      | [] => some []
      | _  => ... match varintDecode b, findField s .., parsePiece .. ...
```

so its equation lemmas (`decodeBody.eq_3`) only fire when the buffer is
*syntactically* a cons.  Completeness, however, must evaluate the decoder at
`encodeMsg s m`, which is an **append** produced by a recursive (`brecOn`)
definition, and the key prefix `varintEncode key` is not syntactically a cons
either: `rw`/`simp` refuse to reduce a `match` on those shapes.  This is the
whole difficulty of the completeness direction (the mathematics was never the
problem — all payload-level lemmas were already available).

The fix is `decodeBody_key`, a generic unfolding lemma proved once:

```lean
theorem decodeBody_key (fuel s last key k1 ks rest)
    (hk : varintEncode key = k1 :: ks) :
    decodeBody (fuel+1) s last (k1 :: (ks ++ rest)) = ... decoder step ...
```

Completeness then (i) destructs `varintEncode key` into `k1 :: ks`
(`varintEncode_nonempty` rules out the empty branch), (ii) reassociates the
append into cons form, (iii) applies `decodeBody_key`, and (iv) discharges the
resulting per-field goals with `parsePiece_complete` and the induction
hypothesis.  Steps (i)–(iii) are the only place where the append/cons mismatch
occurs; everything after it is ordinary rewriting, one case per field type.

## 5. Worked examples

`Examples.lean` includes a `Person` schema and checks, at build time:

```
#eval check "person1" (encodeMsg personSchema person1 == person1Bytes)
-- 0a 02 41 6c | 10 2a | 1a 03 01 ac 02 | 32 01 78 | 32 01 79
--  name="Al"   id=42   scores=[1,300]    tags=["x","y"]

#eval check "..." (roundtrip personSchema [(5, .message [])])   -- empty nested message
#eval check "..." ((decodeBodyCanon personSchema (bytes [0x10, 0x80, 0x00])).isNone)
-- over-long varint for field 2 is rejected
```

and similarly for sign-extended `int32`, zigzag `sint32`, little-endian
`fixed32`, `bool` range checks, UTF-8 validation, out-of-range integers,
non-canonical nested messages, unknown fields, wrong field order, unpacked runs
and truncated payloads.

## 6. Environment note

The project is pure Lean 4 (core + `Std`), no Mathlib: `lakefile.toml` declares
no dependencies, which keeps builds fast and memory-light (the proofs are
first-order list/Nat reasoning, handled by `simp`/`omega`).

On this machine the packaged Lean toolchain's `cc` wrapper pointed at a missing
Nix store path, so `~/.elan/toolchains/.../bin/cc` was replaced with a wrapper
around the system `gcc`.  That is an environment fix, not part of the project;
on a normal installation `lake build` works as-is.
