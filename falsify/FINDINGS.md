# Phase 0: is a bounded exhaustive falsifier fast enough on evm-bend?

Bend 2.0.25 (`~/.bend`), macOS arm64. Contract is `falsify/contracts/ERC20.sol`
compiled with solc 0.8.4 `--optimize` (1,046 bytes runtime). One "call" is a
complete legacy transaction: `Tx.prepare` -> pure `VM.step` fuel loop ->
`Tx.finish`, from a freshly built world each time.

## Verdict

**Proceed.** The pure transaction path works and a real ERC20 `transfer` costs
**48 ms on the JS backend**. That is inside the plan's 10-100 ms band, so depth 3
is the working ceiling and Phase 5 (dedup/parallelism) is mandatory rather than
optional. The native number is the one that matters and is still outstanding
(see Blockers).

## The pure path works

`full/transaction.bend` `prepare`/`finish` are pure, so the whole transaction
runs without `Runtime.loop` and without the precompile host. Confirmed against
the real 1,046-byte ERC20 runtime:

| call | result | gas used |
|---|---|---|
| `totalSupply()` | success, returns 1,000,000 | 17,359 |
| `balanceOf(alice)` | success, returns 1,000,000 | 17,782 |
| `approve(bob,5)` | success, returns `true` | 125,890 |
| `transfer(bob,7)` | success, returns `true` | 138,490 |

After `transfer(bob,7)`, bob's mapping slot reads exactly 7. Storage,
`keccak256`-derived mapping slots, ABI dispatch, the Amsterdam state-gas
reservoir and settlement all work through this entry point.

## Measurements (JS backend, `bun`)

`bench(N)` runs N transfers of distinct amounts (1..N) and sums the resulting
balances, so nothing can be shared away. The accumulator came back as exactly
`N(N+1)/2` every time, which is the proof that all N really executed.

| N | wall | accumulator |
|---|---|---|
| 1 | 0.36s | 1 |
| 10 | 0.62s | 55 |
| 40 | 1.76s | 820 |
| 100 | 4.94s | 5,050 |

Marginal cost N=10 -> N=100: 4.32s / 90 calls = **48 ms/call**.
Marginal cost N=40 -> N=100: 3.18s / 60 calls = 53 ms/call. Linear, no blowup.

At 48 ms, a depth-3 search over 2 senders x 8 variants (16^3 = 4,096 sequences,
~12k calls) is **~10 minutes single-core**. Tolerable, and the reason Phase 5
is not optional. The repo's own `benchmark-results.json` shows native ~10x
faster than JS end-to-end, which would put native near 5 ms/call and the same
search near 1 minute -- an extrapolation, not a measurement.

## Blockers

**1. Native compilation hits `an arity over 255`.**
`bend falsify/spike.bend -o spike` fails on the stock 2.0.25 toolchain after
23s. Type checking the same file is fine; this is native value layout only.

This **corrects `evm-bend-spikes/README.md`**, which called upstream's
`toolchain-layout.patch` "obsolete" on the evidence that `full/main.bend`
type-checks on stock 2.0.25. Type checking was never the thing the patch was
for. Native builds still need the project-local toolchain (`bend-local.sh`,
Bend 2.0.5 + the value-layout workaround), which is what `evm.py --build` uses.

**2. Mutual recursion is still rejected, as `u256/FINDINGS.md` recorded.**
The natural `drive`/`spin` step-until-finished pair is illegal. The working
shape is a single self-recursive def that takes the termination test as a
parameter, because a `match` cannot scrutinize a computed value:

```
def drive(fuel: Nat, done: Bool, m: M.Machine) -> M.Machine:
  match fuel:
    case 0n: m
    case 1n+f:
      match done:
        case True{}: m
        case False{}:
          +next = VM.step(m)
          drive(f, VM.finished(next), next)
```

**3. `Word` limb order is little-endian; the field name `a` is the LEAST
significant limb.** `W.from_u32(2)` reduces to `W{2,0,0,0,0,0,0,0}`, and
`full/test_keccak.py` builds its limbs from byte offset 28 downwards. Any
generator emitting `W.W{...}` literals must follow that or every address,
storage key and balance silently lands wrong.

**4. Affine friction, as expected.** `case 1n+p:` then using `p` twice is
rejected; rebind `+q = p` first. List literals passed to a `+`-binding need an
explicit annotation (`{[...] : +List<M.Slot>}`).

## Note for Phase 3

The one real bug in this spike was a hand-converted ABI selector: `0xa9059cbb`
written as `[169,5,156,203]` instead of `[169,5,156,187]` (`0xbb` is 187, not
203). It presented as an empty-data revert with most of the gas unspent -- i.e.
indistinguishable at a glance from a legitimate `require` failure, and it would
have silently made a whole enumeration vacuous. `manifest.py` must compute
selectors and calldata programmatically, and every fixture needs a smoke call
asserting a non-vacuous result before any search runs. This is exactly the
R5 "silent vacuity" risk from the plan, hit on day one.
