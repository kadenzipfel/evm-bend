# Justification for the structural stack guards in ./opcode-common.bend.
#
# `dispatch` used to decide stack underflow with
#   Nat.is_ge(List.length(stack), required(op))
# and capacity with
#   Nat.is_le(Nat.add(List.length(stack), growth(op)), 1024n).
# Both force the whole stack spine, so neither reduces when the stack has an
# open tail, and every law quantified over a stack died in normalization.
#
# `H.has` and `H.capacity` replace them. This file discharges the obligation
# that the replacements compute the same thing.

import Base
import ../evmword.bend as W
import ./opcode-common.bend as H

law nat_ge_zero:
  for n: Nat
  {Nat.is_ge(n, 0n) == True{} : Bool}
def nat_ge_zero(n):
  match n:
    case 0n: {==}
    case 1n+p: {==}

law nat_add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}
def nat_add_zero(n):
  match n:
    case 0n: {==}
    case 1n+p:
      %nat_add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# The underflow guard is replaced exactly: no side condition, every n, every
# stack.
law has_is_length:
  for n: Nat
  for +xs: +List<W.Word>
  {H.has(n, xs) == Nat.is_ge(List.length(&2, W.Word, xs), n) : Bool}
def has_is_length(n, xs):
  match n:
    case 0n:
      Equal.sym(Bool, Nat.is_ge(List.length(&2, W.Word, xs), 0n), True{},
        nat_ge_zero(List.length(&2, W.Word, xs)))
    case 1n+p:
      match xs:
        case Nil{}: {==}
        case Con{h,+t}: has_is_length(p, t)

# The capacity guard is replaced exactly wherever the opcode grows the stack.
law capacity_growing:
  for p: Nat
  for +xs: +List<W.Word>
  {H.capacity(1n+p, xs)
    == Nat.is_le(Nat.add(List.length(&2, W.Word, xs), 1n+p), 1024n) : Bool}
def capacity_growing(p, xs):
  {==}

# For a zero-growth opcode the replacement answers True{} without measuring the
# stack. That agrees with the old guard exactly when the stack already respects
# the 1024 bound, which is the hypothesis below.
#
# RESIDUAL OBLIGATION: that the bound is an invariant of the interpreter --
# every reachable frame satisfies it -- is NOT proved here. `initial_frame`
# starts empty and every push path passes through this guard, so it should be
# inductive. Until it is proved, a zero-growth opcode is the one place where
# this fork's interpreter may differ from upstream's, and only on states
# upstream's own guard would have rejected as overflowed.
law capacity_zero_under_bound:
  for +xs: +List<W.Word>
  for bound: {Nat.is_le(List.length(&2, W.Word, xs), 1024n) == True{} : Bool}
  {H.capacity(0n, xs)
    == Nat.is_le(Nat.add(List.length(&2, W.Word, xs), 0n), 1024n) : Bool}
def capacity_zero_under_bound(xs, bound):
  %Equal.sym(Nat, Nat.add(List.length(&2, W.Word, xs), 0n), List.length(&2, W.Word, xs),
     nat_add_zero(List.length(&2, W.Word, xs)))
    : {True{} == Nat.is_le(_, 1024n) : Bool}
  Equal.sym(Bool, Nat.is_le(List.length(&2, W.Word, xs), 1024n), True{}, bound)
