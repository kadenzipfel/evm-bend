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

### B2 -- Symbolic storage values  [BLOCKED: needs a gas-path redesign]

The original reading -- "storage is unreachable" -- was wrong, and
`full/storage-laws.bend` now carries the counterexamples:

- `sstore_zero_over_zero` -- SSTORE through the full Machine interpreter.
- `sstore_writes_value` -- SSTORE at **200,000 execution gas**, zero to
  nonzero, spending the full 97,920 of Amsterdam state gas out of the
  reservoir. Large unary gas is not by itself a barrier.
- `tstore_symbolic` -- TSTORE lands **any** word in transient slot 0,
  universally quantified over the value.

What actually blocks is narrow. `state-ops.state_if` and `state-ops.refund`
branch on `W.is_zero(value)` and `W.eq(current,value)`. For a symbolic word
those predicates never reduce, so the match stays stuck, so the checker
normalizes *every* branch -- including `G.spend_state(e, U32.to_nat(97920))`
and `G.refill(e, U32.to_nat(97920))` -- and the composed unary arithmetic
overflows the JavaScript call stack.

Isolated by four probes: concrete value at 30k gas passes; concrete value at
200k gas passes; symbolic value at 30k gas overflows; symbolic value through
TSTORE (which has no value-dependent branch) passes.

The hoist proposed here was tried and **does not work**. Three refactors were
implemented and reverted: sharing the five slot predicates as `+` bindings
(plain CSE -- the checker substitutes rather than sharing), taking the
post-store world from `paid` instead of `funded`, and collapsing the first
`commit` into a helper to drop a nested stuck match. Each still overflows. Full
bisection evidence is in the comment block at the end of
`full/storage-laws.bend`.

What the bisection shows: a stuck predicate is survivable when it only reaches
fields the goal never reads -- with only `refund` left stuck the law passes,
because the checker is lazy there. It is fatal when it reaches the GAS path.
`cost` holds `choose(Bool.and(untouched, Bool.not(same)), 10000, 0n)`; a stuck
`same` makes the cost stuck, hence `Checked.charge` stuck, hence `G.failed`
stuck, hence every `commit` on the way out a stuck match. The checker pushes
each continuation into every branch and the term grows multiplicatively past
the JavaScript stack.

So the fix must keep stuck predicates out of the gas decision, which means
reshaping how `store_paid` charges. That is a redesign of gas-critical code,
not a hoist, and it should not land without the 15,918-fixture gate. Worth
raising upstream before building it.

`world.find` is already structural and needs no lemmas.

Bend has no computed match (`match f(x)` is unsupported), so the case split
must go through a helper def that takes the Bool plus its evidence. That idiom
is already used throughout `opcodes.bend`.

### B3 -- Arithmetic laws are unanchored  [CLOSED]

`word-spec.bend` carries two word types: `L.Word` (8 x U32 limbs, what runs) and
`Word256` (`Word(256n)` bitvector, what is provable), with `of_limbs` between
them. The refinement

    of_limbs(L.add(x,y)) == add(of_limbs x, of_limbs y)

is explicitly OUTSTANDING upstream, with a 5-lemma plan in a comment. Until it
closes, a law about ADD's result is only as strong as `L.add`, which is tied to
nothing. `word-proof.low_add` proves the low 32 bits only.

`word-refine.bend` now carries 10 proved laws covering four of the five steps,
all generic in the word width:

- **Lemma 1** -- `adc_out`, the final carry of `Word.adc`, with `carry_bit`
  proved to agree with the second component of `Bool.full_add`.
- **Lemma 2** -- `concat_adc`: adding two concatenated bitvectors is the low add
  followed by the high add started from the low add's carry out. This is the
  lemma that turns one 256-bit add into eight 32-bit adds.
- **Lemma 3** -- `adc_is_add_carry`: a carry-in is a second addition. Routed
  through `adc_zero_right`, `adc_carry_is_inc` and `add_one_is_inc`.
- **Lemma 4a** -- `adc_out_is_cmp`: the carry out IS the unsigned overflow
  comparison. Generalising over the carry-in is what makes it true -- without a
  carry-in the wrapped sum is strictly below x on overflow, with one it is at
  most x. The per-bit step (`fin_shift`) is proved over a quantified `Cmp`, then
  instantiated at the tail's comparison, which sidesteps Bend's lack of a
  computed match.

- **Lemma 4b** -- `adc_out_split`, carry composition: a two-step addition cannot
  overflow twice. A direct induction fails because the second carry chain runs
  over the bits of `add(x,y)`, not over x and y. Carrying both chains at once,
  indexed by the three joint carry states reachable (`a = b or g`, never both),
  makes it go through. Stated at width `1n+n`: at width zero it is false, since
  a 0-bit `add(x,y)` cannot represent the carry the increment would produce.

**The bridge to the running code is also proved.** `carry_is_adc_out` shows
`evmword.carry` -- the two `U32.is_lt` tests the interpreter actually runs -- IS
the bitvector carry out. `limb_sum_is_adc` shows a limb's value is the 32-bit
adc. Both need a case split on the carry bit, since `evmword.bit` is a stuck
match on a symbolic Bool and blocks `U32.add` from unfolding.

**The theorem is proved.** `of_limbs_add_word` in `word-refine.bend`:

    for x,y: L.Word.  of_limbs(L.add(x,y)) == add(of_limbs x, of_limbs y)

35 laws, 1,209 lines, checking in 650ms. The assembly went through
`add_splits_into_limbs` (eight `concat_adc` instantiations down `of_limbs`'
nesting, 256 = 32+224 ... 32 = 32+0), `carry_chain0..6` (evmword's c0..c6 chain
is the `adc_out` chain) and `limb_val0..7` (each limb's value is the 32-bit
adc). The eighth carry is discarded for free: the last level's high half is
`Word.adc(0n, WNil, WNil, ...)`, which is `WNil`. That is what makes the
arithmetic modular.

A negative control -- replacing the conclusion with `of_limbs(x)` -- is
rejected, so the proof is not vacuous. `word-spec.bend`'s OUTSTANDING comment
has been replaced with a pointer to the proof.

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
2. ~~**B5** -- stand up the conformance suite.~~ **Fast net done**: 624/624
   differential on both backends, precompiles, frame invariants and contract
   fixtures all green with B1 applied. See `LOCAL-SETUP.md`. The 15,918-fixture
   state gate needs a 2.57 GB corpus and hours; still open, required before
   anything goes upstream.
3. **B2** -- blocked pending a gas-path redesign; needs the state gate and
   probably an upstream conversation. Deprioritized below B3.
4. ~~**B2b** -- gas-erased `step`.~~ **Not needed.** Unary gas at 200,000
   normalizes fine; the overflow came from stuck branches, not gas size.
5. ~~**B3** -- limb refinement.~~ **Done.** `word-refine.bend`, 35 laws.
   Upstreamable as a standalone PR: additive, touches no interpreter code,
   closes a gap the author flagged himself in a code comment.
6. First real contract spec end to end; then B4 if the ceiling binds.

## Non-goals

Performance. Native compilation. Blockchain/transaction-format conformance
(upstream's own unfinished work). Replacing the differential test suite -- it
stays as the safety net for every change made here.
