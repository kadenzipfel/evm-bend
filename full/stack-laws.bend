# Laws over an OPEN stack, against the real Amsterdam opcode interpreter.
#
# None of these were statable before the structural guards in
# ./opcode-common.bend: the old numeric `List.length` guards never reduced on a
# stack with a variable tail, so normalization stuck before reaching the
# opcode. Upstream's equivalents in ../LAWS.bend hold only for the 93-line
# `core.bend` toy.
#
# Every opcode here is zero-growth, so ./guard-laws.bend's
# `capacity_zero_under_bound` carries the capacity side.

import Base
import ./opcodes.bend as O
import ./model.bend as M
import ../evmword.bend as W

def frame(code: +List<U32>, stack: +List<W.Word>, gas: Nat) -> M.Frame:
  M.Frame.set_stack(
    M.initial_frame(code, gas, Nil{}, W.zero(), W.zero(), W.zero()), stack)

def after(code: +List<U32>, stack: +List<W.Word>, gas: Nat) -> M.Frame:
  O.step(frame(code, stack, gas), M.default_context())

# POP removes exactly the top word, whatever it is and whatever is under it.
law pop_drops_top:
  for x: W.Word
  for +rest: +List<W.Word>
  {M.Frame.stack(after([80], x <> rest, U32.to_nat(1000))) == rest
    : +List<W.Word>}
def pop_drops_top(x, rest):
  {==}

# POP charges exactly two gas.
law pop_costs_two:
  for x: W.Word
  for +rest: +List<W.Word>
  for remaining: Nat
  {M.Frame.gas(after([80], x <> rest, 2n+remaining)) == remaining : Nat}
def pop_costs_two(x, rest, remaining):
  {==}

# ADD replaces the top two words with their modular sum and leaves the rest
# alone. This says nothing about W.add's own arithmetic -- see
# ../word-spec.bend for that open obligation.
law add_replaces_top_two:
  for a: W.Word
  for b: W.Word
  for +rest: +List<W.Word>
  {M.Frame.stack(after([1], a <> b <> rest, U32.to_nat(1000)))
    == W.add(a, b) <> rest : +List<W.Word>}
def add_replaces_top_two(a, b, rest):
  {==}

# SWAP1 is its own inverse, for any two words over any tail.
law swap1_involutive:
  for x: W.Word
  for y: W.Word
  for +rest: +List<W.Word>
  {M.Frame.stack(O.step(after([144,144], x <> y <> rest, U32.to_nat(1000)),
     M.default_context())) == x <> y <> rest : +List<W.Word>}
def swap1_involutive(x, y, rest):
  {==}

# An underflowing ADD faults instead of reading past the bottom of the stack.
law add_underflow_faults:
  for x: W.Word
  {M.Frame.action(after([1], x <> Nil{}, U32.to_nat(1000))) == M.Fault{2}
    : M.Action}
def add_underflow_faults(x):
  {==}
