# Laws about storage, against the real Amsterdam interpreter at the Machine
# level (VM.step, so SLOAD/SSTORE/TSTORE route through state-ops.bend).
#
# These correct an earlier reading that storage was categorically unreachable.
# It is not. Writes are provable, including at realistic gas and including the
# Amsterdam state-gas reservoir transition. What is NOT provable today is an
# SSTORE whose *value* is symbolic -- see the note at the bottom.

import Base
import ./vm.bend as VM
import ./model.bend as M
import ./world.bend as World
import ../evmword.bend as W

def run_m(n: Nat, m: M.Machine) -> M.Machine:
  match n:
    case 0n: m
    case 1n+p: run_m(p, VM.step(m))

def slot0(m: M.Machine) -> W.Word:
  match m:
    case M.Machine{e, parents}:
      World.lookup(M.Account.storage(World.account(M.Engine.world(e), W.zero())), W.zero())

def tslot0(m: M.Machine) -> W.Word:
  match m:
    case M.Machine{e, parents}:
      World.lookup(M.Account.transient(World.account(M.Engine.world(e), W.zero())), W.zero())

def start(code: +List<U32>, gas: Nat, res: Nat) -> M.Machine:
  VM.initial(M.initial_frame(code, gas, Nil{}, W.zero(), W.zero(), W.zero()),
    M.empty_world(), M.default_context(), res)

def start_stack(stack: +List<W.Word>, code: +List<U32>, gas: Nat, res: Nat) -> M.Machine:
  VM.initial(
    M.Frame.set_stack(M.initial_frame(code, gas, Nil{}, W.zero(), W.zero(), W.zero()), stack),
    M.empty_world(), M.default_context(), res)

# PUSH1 0; PUSH1 0; SSTORE -- no state transition, so no reservoir traffic.
law sstore_zero_over_zero:
  {slot0(run_m(3n, start([96,0,96,0,85], U32.to_nat(30000), 0n))) == W.zero() : W.Word}
def sstore_zero_over_zero():
  {==}

# PUSH1 42; PUSH1 0; SSTORE -- zero to nonzero, so state_if spends 97,920
# state gas out of the reservoir. Provable, and at 200,000 execution gas: a
# large unary Nat is not by itself a barrier.
law sstore_writes_value:
  {slot0(run_m(3n, start([96,42,96,0,85], U32.to_nat(200000), U32.to_nat(200000))))
    == W.from_u32(42) : W.Word}
def sstore_writes_value():
  {==}

# TSTORE lands ANY word in transient slot 0. Fully universally quantified over
# the value, through the whole Machine interpreter. TSTORE charges a flat 100
# and touches neither the reservoir nor the refund counter, so nothing in its
# path branches on the value.
law tstore_symbolic:
  for x: W.Word
  {tslot0(run_m(2n, start_stack(x <> Nil{}, [96,0,93], U32.to_nat(30000), 0n))) == x : W.Word}
def tstore_symbolic(x):
  {==}

# NOT PROVABLE TODAY -- the blocker, with the refactor that does NOT fix it, so
# nobody re-runs this experiment:
#
#   law sstore_symbolic:
#     for x: W.Word
#     {slot0(run_m(2n, start_stack(x <> Nil{}, [96,0,85], ...))) == x : W.Word}
#
# overflows the checker's stack. Established by bisection on `store_paid`,
# calling `state-ops.store` directly so the VM loop is not involved:
#
#   concrete value                             passes, 0.54s
#   symbolic value                             overflows
#   symbolic, all three value-dependent terms
#     (cost / state_change / refund) stubbed   passes, 0.26s
#   symbolic, only `refund` left stuck         PASSES
#   symbolic, only `cost` left stuck           overflows
#   symbolic, only `state_change` left stuck   overflows
#   symbolic, any single term stubbed          overflows
#
# So it is not storage, not gas magnitude (a concrete write proves out at
# 200,000 gas and a 97,920 reservoir spend), not the world (`world.find` is
# structural and reduces), and not the reservoir size (0 / 97,920 / 200,000 all
# behave alike). The checker is lazy about fields the goal never reads, which is
# why a stuck `refund` -- it only feeds the world's refund counter -- is
# survivable on its own.
#
# What kills it is a stuck term reaching the GAS path. `cost` contains
# `choose(Bool.and(untouched, Bool.not(same)), 10000, 0n)`; with `same` stuck the
# cost is stuck, so `Checked.charge` is stuck, so `G.failed` is stuck, so every
# `commit` on the way out is a stuck match. The checker then pushes each
# continuation into every branch, and with several independent stuck predicates
# nested through `charge`, `state_if`, `refund_if` and two `commit`s the term
# grows multiplicatively past the JavaScript stack.
#
# TRIED AND REJECTED (all reverted; none moved the needle):
#   1. Hoisting the five slot predicates into shared `+` bindings -- plain CSE,
#      `W.eq(current,value)` was being recomputed three times. Still overflows:
#      the checker substitutes rather than sharing.
#   2. Taking the post-store world from `paid` rather than `funded`, so the
#      storage read does not pass through the state-gas engine. Still overflows.
#   3. Collapsing the first `commit` into a `store_commit` helper to remove one
#      nested stuck match. Still overflows.
#
# The real fix has to keep stuck predicates out of the gas decision, which means
# reshaping how `store_paid` charges -- a redesign of gas-critical code, not a
# hoist. It should not land without the 15,918-fixture state gate running, and
# is probably worth raising upstream first.
