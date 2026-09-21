# Proof-oriented fork: plan

Fork of `gakonst/evm-bend`. Upstream is a **conformance** artifact: 5,741 lines
of Bend under `full/` that pass 15,918 pinned Amsterdam state fixtures on both
backends. It is not a **verification** artifact -- it carries 15 laws, all
against the 93-line `core.bend` Shanghai toy, and **zero laws under `full/`**.

This fork's goal is to make `full/` proof-friendly without changing what it
computes, so that a contract author can hand us bytecode plus a `LAWS.bend` and
get back a machine-checked statement of exactly which properties hold.

## Target artifact

```
contracts/mytoken/
  bytecode.json      runtime bytecode + storage layout
  LAWS.bend          the properties claimed (human-written, never AI-edited)
  PROOF.bend         the proofs (AI-written)
```

`bend PROOF.bend` is the gate. It already fails loudly on any open or false law,
and prints "All terms check." only when every claim holds. That gate *is* the
"which proofs have been made" report -- the harness is not the hard part.

## Ground truth established so far

Measured on stock Bend 2.0.25, no Rust/Bun/evm2 needed for the proof layer.
Spikes in `../evm-bend-spikes/`.

Works today:

- `full/*.bend` has zero `@unsafe` and zero foreign code. Pure and law-eligible.
  Only `full/main.bend`'s IO driver (4 defs) is impure.
- Whole interpreter type-checks in 4.3s; `bend PROOF.bend` in 180ms.
- Laws over concrete bytecode discharge by `{==}` through the real Amsterdam
  interpreter (PUSH1 42; PUSH1 1; ADD leaves 43, 1.76s). Negative control fails.
- Universally quantified laws work when values are symbolic but stack depth and
  control flow are concrete (POP, SWAP1-involutive, DUP1-POP; 1.59s).
- Proof cost is flat in program length to ~1k opcodes (10/40/100/200 opcodes all
  ~1.6s; 1,000 opcodes 2.95s). Time is type-checking the import graph, not
  normalizing the program.

Upstream's `toolchain-layout.patch` (255-argument workaround against a copied
2.0.5 compiler) appears obsolete: 2.0.25 changelog #944 upstreamed wide-record
boxing, and `full/main.bend` checks on the stock toolchain.

## Blockers

### B1 -- Symbolic stack depth is impossible  [DONE]

`full/opcodes.dispatch` guards underflow numerically:

    enough(Nat.is_ge(List.length(&2,W.Word,M.Frame.stack(f)), required(op)), ...)

`List.length` forces the whole spine. Given a stack `x <> rest` with `rest`
symbolic it never reduces, the guard sticks, and every law over an open stack
dies in normalization. `core.bend`'s toy laws only work because that
interpreter matches the stack structurally.

RESOLVED. `H.has` and `H.capacity` in `full/opcode-common.bend` replace both
numeric guards; `full/guard-laws.bend` proves the replacement correct; and
`full/stack-laws.bend` carries the first six laws ever stated against `full/`
-- POP, ADD, SWAP1 and an underflow fault, over an open stack tail and with
symbolic gas. All 88 local Bend tests are byte-identical to the upstream
baseline.

The structural predicate:

    def has(n: Nat, xs: +List<W.Word>) -> Bool:
      match n:
        case 0n: True{}
        case 1n+p:
          match xs:
            case Nil{}: False{}
            case Con{h,t}: has(p,t)

`has(2n, x <> y <> rest)` reduces to `True{}` without touching `rest`.

Semantics must be preserved by proof, not assumption. Obligation:

    law has_is_length: for n, for xs. has(n,xs) == Nat.is_ge(List.length(xs),n)

The 1024-capacity guard (`length + growth <= 1024`) genuinely depends on the
whole stack and cannot be made fully structural. Two mitigations: short-circuit
to `True{}` when `growth` is `0n` (sound -- pushing nothing cannot overflow),
and for `growth >= 1` let laws take the bound as a hypothesis, the way
`stack-proof.bend` already threads `evidence`.

### B2 -- Storage is unreachable

SSTORE laws fail two ways: at gas 5,000 normalization sticks on an unreduced
`world.lookup(Account.storage(world.find(...)))`; at gas >= 15,000 the checker
blows its JS stack. Gas magnitude alone is not the cause -- the stack laws check
fine at 200,000 gas. It is the state-gas/reservoir path plus the
association-list world.

Fix, in two parts:
- Give `world.find`/`world.lookup` reduction lemmas, or replace the association
  list with a structure that reduces on symbolic keys.
- Get unary `Nat` gas out of the state path for proofs. Standard move: a
  gas-erased `step` variant plus a theorem that it agrees with the real `step`
  whenever gas suffices. Avoids rewriting gas accounting.

This is the blocker that matters. Nearly every contract property worth stating
is about storage.

### B3 -- Arithmetic laws are unanchored

`word-spec.bend` carries two word types: `L.Word` (8 x U32 limbs, what runs) and
`Word256` (`Word(256n)` bitvector, what is provable), with `of_limbs` between
them. The refinement

    of_limbs(L.add(x,y)) == add(of_limbs x, of_limbs y)

is explicitly OUTSTANDING upstream, with a 5-lemma plan in a comment. Until it
closes, a law about ADD's result is only as strong as `L.add`, which is tied to
nothing. `word-proof.low_add` proves the low 32 bits only.

Lemmas 1 and 4 of that plan ("generalized bitvector adc returning result and
final carry", "final carry equals the overflow comparison") are the same
carry-generalized induction over `Word.adc` used in `../u256/m3_sub_add.bend`.

### B4 -- Program size ceiling

4,000 opcodes overflows the checker's machine stack; 1,000 is fine at 2.95s.
Adequate for single straight-line function paths, not for whole transactions or
loop-heavy code. Not on the critical path; revisit if B1-B3 close.

### B5 -- No conformance safety net locally

The 15,918-fixture suite needs Rust, Bun and a pinned `evm2-reference`
checkout. Until that is standing, any change to `full/` is unverified against
upstream's own gate. Every interpreter change in this fork must therefore come
with a Bend-level equivalence law proving old and new agree, and B5 must close
before anything is proposed upstream.

## Order of work

1. ~~**B1** -- structural underflow guard + `has_is_length` equivalence law.~~
   **Done.**
2. **B5** -- stand up the conformance suite so B2's larger surgery is checkable.
3. **B2a** -- world lookup reduction lemmas.
4. **B2b** -- gas-erased `step` and its agreement theorem.
5. **B3** -- limb refinement, upstreamable as a standalone PR against
   `word-spec.bend`.
6. First real contract spec end to end; then B4 if the ceiling binds.

## Non-goals

Performance. Native compilation. Blockchain/transaction-format conformance
(upstream's own unfinished work). Replacing the differential test suite -- it
stays as the safety net for every change made here.
