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

# NOT PROVABLE TODAY -- the precise blocker, recorded so it is not re-diagnosed:
#
#   law sstore_symbolic:
#     for x: W.Word
#     {slot0(run_m(2n, start_stack(x <> Nil{}, [96,0,85], ...))) == x : W.Word}
#
# overflows the checker's stack. The cause is NOT gas magnitude (the law above
# checks at 200,000) and NOT storage itself (TSTORE checks symbolically). It is
# that `state-ops.state_if` and `state-ops.refund` branch on `W.is_zero(value)`
# and `W.eq(current,value)`. For a symbolic word those never reduce, the match
# stays stuck, and the checker then normalizes every branch -- including
# `G.spend_state(e, U32.to_nat(97920))` and `G.refill(e, U32.to_nat(97920))` --
# whose composed unary arithmetic blows the JavaScript call stack.
#
# Fix direction: hoist those predicates into parameters, the way `opcodes.enough`
# and `opcodes.room` already take their decision as a Bool. A law can then supply
# the case split instead of the interpreter forcing it. That is a local refactor
# of state-ops.bend, comparable in size to the guard change in B1.
