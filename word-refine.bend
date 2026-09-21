# Limb refinement, step 1 and 2 of the plan recorded at the end of
# ./word-spec.bend: the carry-out of a bitvector adc, and the concatenation
# split that turns one 256-bit add into eight 32-bit adds with a threaded carry.

import Base
import ./word-spec.bend as Spec

# --- Lemma 1: the carry out of a full adder, as a Bool ---------------------
# Base's Bool.full_add returns (sum, carry) as a pair. Projecting the second
# component inside an induction would need a mutually recursive helper, which
# user files cannot express (a def may not forward-reference). So the carry is
# defined directly and proved to agree with Bool.full_add.

def carry_bit(a: Bool, b: Bool, c: Bool) -> Bool:
  match a b c:
    case False{} False{} False{}: False{}
    case False{} False{} True{}: False{}
    case False{} True{} False{}: False{}
    case False{} True{} True{}: True{}
    case True{} False{} False{}: False{}
    case True{} False{} True{}: True{}
    case True{} True{} False{}: True{}
    case True{} True{} True{}: True{}

def snd(p: Bool & Bool) -> Bool:
  (x, y) = p
  y

law carry_bit_is_full_add:
  for a: Bool
  for b: Bool
  for c: Bool
  {snd(Bool.full_add(a, b, c)) == carry_bit(a, b, c) : Bool}
def carry_bit_is_full_add(a, b, c):
  match a b c:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: {==}
    case True{} False{} True{}: {==}
    case True{} True{} False{}: {==}
    case True{} True{} True{}: {==}

# The final carry of Word.adc, mirroring its recursion exactly.
def adc_out(n: Nat, a: Word(n), b: Word(n), f: Bool, c: Bool) -> Bool:
  match n:
    case 0n: c
    case 1n+p:
      match a b f:
        case WCon{ab, at} WCon{bb, bt} False{}:
          adc_out(p, at, bt, False{}, carry_bit(ab, bb, c))
        case WCon{ab, at} WCon{bb, bt} True{}:
          adc_out(p, at, bt, True{}, carry_bit(ab, Bool.not(bb), c))

# --- Lemma 2: the concatenation split --------------------------------------
# Adding two concatenated bitvectors is the low add, then the high add started
# from the low add's carry out. This is what turns one 256-bit add into eight
# 32-bit adds with a threaded carry; instantiating it seven times is step 5.

law concat_adc:
  for n: Nat
  for -m: Nat
  for +lo1: Word(n)
  for +lo2: Word(n)
  for +hi1: Word(m)
  for +hi2: Word(m)
  for c: Bool
  {Word.adc(Nat.add(n,m), Spec.concat(n,m,lo1,hi1), Spec.concat(n,m,lo2,hi2), False{}, c)
    == Spec.concat(n, m, Word.adc(n,lo1,lo2,False{},c),
         Word.adc(m,hi1,hi2,False{},adc_out(n,lo1,lo2,False{},c)))
    : Word(Nat.add(n,m))}

def concat_adc(n, m, lo1, lo2, hi1, hi2, c):
  match n:
    case 0n:
      match lo1 lo2:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match lo1 lo2 c:
        case WCon{False{},+t1} WCon{False{},+t2} False{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{False{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, False{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},False{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},False{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,False{}))
        case WCon{False{},+t1} WCon{False{},+t2} True{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{True{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, False{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},False{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},False{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,False{}))
        case WCon{False{},+t1} WCon{True{},+t2} False{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{True{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, False{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},False{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},False{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,False{}))
        case WCon{False{},+t1} WCon{True{},+t2} True{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{False{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, True{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},True{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},True{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,True{}))
        case WCon{True{},+t1} WCon{False{},+t2} False{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{True{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, False{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},False{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},False{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,False{}))
        case WCon{True{},+t1} WCon{False{},+t2} True{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{False{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, True{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},True{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},True{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,True{}))
        case WCon{True{},+t1} WCon{True{},+t2} False{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{False{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, True{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},True{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},True{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,True{}))
        case WCon{True{},+t1} WCon{True{},+t2} True{}:
          Equal.cong(Word(Nat.add(p,m)), Word(1n+Nat.add(p,m)), w => WCon{True{},w},
            Word.adc(Nat.add(p,m), Spec.concat(p,m,t1,hi1), Spec.concat(p,m,t2,hi2), False{}, True{}),
            Spec.concat(p,m,Word.adc(p,t1,t2,False{},True{}),Word.adc(m,hi1,hi2,False{},adc_out(p,t1,t2,False{},True{}))),
            concat_adc(p,m,t1,t2,hi1,hi2,True{}))

# --- Lemma 3: a carry-in is one increment ----------------------------------
# Step 3 of the plan needs `adc(x,y,cin)` to equal `add(add(x,y),cin)`. Since
# adding a word that is zero except in bit 0 is exactly an increment, that
# splits into: adding zero is the identity, and a carry-in is one increment.

law adc_zero_right:
  for n: Nat
  for u: Word(n)
  {Word.adc(n, u, Word.zero(n), False{}, False{}) == u : Word(n)}
def adc_zero_right(n, u):
  match n:
    case 0n:
      match u:
        case WNil{}: {==}
    case 1n+p:
      match u:
        case WCon{False{},t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{},w},
            Word.adc(p,t,Word.zero(p),False{},False{}), t, adc_zero_right(p,t))
        case WCon{True{},t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{},w},
            Word.adc(p,t,Word.zero(p),False{},False{}), t, adc_zero_right(p,t))

# A carry into the bottom bit is exactly one increment of the carry-free sum.
law adc_carry_is_inc:
  for n: Nat
  for +x: Word(n)
  for +y: Word(n)
  {Word.adc(n,x,y,False{},True{}) == Word.inc(n, Word.adc(n,x,y,False{},False{}))
    : Word(n)}
def adc_carry_is_inc(n, x, y):
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match x y:
        # 0+0+1 = 1 with no carry; inc of a zero bottom bit just sets it.
        case WCon{False{},xt} WCon{False{},yt}: {==}
        # 1+1+1 = 1 carrying; inc of a zero bottom bit just sets it.
        case WCon{True{},xt} WCon{True{},yt}: {==}
        # the two mixed cases push the increment into the tail
        case WCon{False{},+xt} WCon{True{},+yt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{},w},
            Word.adc(p,xt,yt,False{},True{}), Word.inc(p,Word.adc(p,xt,yt,False{},False{})),
            adc_carry_is_inc(p,xt,yt))
        case WCon{True{},+xt} WCon{False{},+yt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{},w},
            Word.adc(p,xt,yt,False{},True{}), Word.inc(p,Word.adc(p,xt,yt,False{},False{})),
            adc_carry_is_inc(p,xt,yt))

# The word that is `c` in bit 0 and zero above it.
def carry_word(n: Nat, c: Bool) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p: WCon{c, Word.zero(p)}

law carry_word_false:
  for n: Nat
  {carry_word(n, False{}) == Word.zero(n) : Word(n)}
def carry_word_false(n):
  match n:
    case 0n: {==}
    case 1n+p: {==}

law add_one_is_inc:
  for +n: Nat
  for +u: Word(n)
  {Word.add(n, u, carry_word(n, True{})) == Word.inc(n, u) : Word(n)}
def add_one_is_inc(n, u):
  match n:
    case 0n:
      match u:
        case WNil{}: {==}
    case 1n+p:
      match u:
        case WCon{False{},t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{},w},
            Word.adc(p,t,Word.zero(p),False{},False{}), t, adc_zero_right(p,t))
        case WCon{True{},+t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{},w},
            Word.adc(p,t,Word.zero(p),False{},True{}), Word.inc(p,t),
            Equal.trans(Word(p),
              Word.adc(p,t,Word.zero(p),False{},True{}),
              Word.inc(p,Word.adc(p,t,Word.zero(p),False{},False{})),
              Word.inc(p,t),
              adc_carry_is_inc(p,t,Word.zero(p)),
              Equal.cong(Word(p), Word(p), w => Word.inc(p,w),
                Word.adc(p,t,Word.zero(p),False{},False{}), t, adc_zero_right(p,t))))

# Step 3 of the plan, in bitvector form: a carry-in is a second addition.
law adc_is_add_carry:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for c: Bool
  {Word.adc(n,x,y,False{},c) == Word.add(n, Word.add(n,x,y), carry_word(n,c)) : Word(n)}
def adc_is_add_carry(n, x, y, c):
  match c:
    case False{}:
      Equal.sym(Word(n),
        Word.add(n, Word.add(n,x,y), carry_word(n,False{})),
        Word.add(n,x,y),
        Equal.trans(Word(n),
          Word.add(n, Word.add(n,x,y), carry_word(n,False{})),
          Word.add(n, Word.add(n,x,y), Word.zero(n)),
          Word.add(n,x,y),
          Equal.cong(Word(n), Word(n), w => Word.add(n, Word.add(n,x,y), w),
            carry_word(n,False{}), Word.zero(n), carry_word_false(n)),
          adc_zero_right(n, Word.add(n,x,y))))
    case True{}:
      Equal.trans(Word(n),
        Word.adc(n,x,y,False{},True{}),
        Word.inc(n, Word.add(n,x,y)),
        Word.add(n, Word.add(n,x,y), carry_word(n,True{})),
        adc_carry_is_inc(n,x,y),
        Equal.sym(Word(n),
          Word.add(n, Word.add(n,x,y), carry_word(n,True{})),
          Word.inc(n, Word.add(n,x,y)),
          add_one_is_inc(n, Word.add(n,x,y))))

# --- Lemma 4: the carry out is an unsigned overflow comparison --------------
# `evmword.carry` decides the limb carry with two U32.is_lt tests. Tying that to
# `adc_out` needs the carry out expressed as a comparison. The clean statement
# generalises over the carry in: without one the wrapped sum is strictly below
# x on overflow, with one it is at most x.

def sum_bit(a: Bool, b: Bool, c: Bool) -> Bool:
  match a b c:
    case False{} False{} False{}: False{}
    case False{} False{} True{}: True{}
    case False{} True{} False{}: True{}
    case False{} True{} True{}: False{}
    case True{} False{} False{}: True{}
    case True{} False{} True{}: False{}
    case True{} True{} False{}: False{}
    case True{} True{} True{}: True{}

def lt_or_eq(c: Bool, k: Cmp) -> Bool:
  match c:
    case False{}: Cmp.is_lt(k)
    case True{}: Cmp.is_le(k)

# The per-bit step, over an arbitrary tail comparison. K is a quantified
# variable here, not a computed term, so it can be matched directly -- Bend has
# no computed match. The main induction instantiates this at the tail's cmp.
law fin_shift:
  for xb: Bool
  for yb: Bool
  for c: Bool
  for K: Cmp
  {lt_or_eq(carry_bit(xb,yb,c), K)
    == lt_or_eq(c, Word.cmp.fin(sum_bit(xb,yb,c), xb, K)) : Bool}
def fin_shift(xb, yb, c, K):
  match xb yb c K:
        case False{} False{} False{} LT{}: {==}
        case False{} False{} False{} EQ{}: {==}
        case False{} False{} False{} GT{}: {==}
        case False{} False{} True{} LT{}: {==}
        case False{} False{} True{} EQ{}: {==}
        case False{} False{} True{} GT{}: {==}
        case False{} True{} False{} LT{}: {==}
        case False{} True{} False{} EQ{}: {==}
        case False{} True{} False{} GT{}: {==}
        case False{} True{} True{} LT{}: {==}
        case False{} True{} True{} EQ{}: {==}
        case False{} True{} True{} GT{}: {==}
        case True{} False{} False{} LT{}: {==}
        case True{} False{} False{} EQ{}: {==}
        case True{} False{} False{} GT{}: {==}
        case True{} False{} True{} LT{}: {==}
        case True{} False{} True{} EQ{}: {==}
        case True{} False{} True{} GT{}: {==}
        case True{} True{} False{} LT{}: {==}
        case True{} True{} False{} EQ{}: {==}
        case True{} True{} False{} GT{}: {==}
        case True{} True{} True{} LT{}: {==}
        case True{} True{} True{} EQ{}: {==}
        case True{} True{} True{} GT{}: {==}

law adc_out_is_cmp:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for c: Bool
  {adc_out(n,x,y,False{},c)
    == lt_or_eq(c, Word.cmp(n, Word.adc(n,x,y,False{},c), x)) : Bool}
def adc_out_is_cmp(n, x, y, c):
  match n:
    case 0n:
      match x y c:
        case WNil{} WNil{} False{}: {==}
        case WNil{} WNil{} True{}: {==}
    case 1n+p:
      match x y c:
        case WCon{False{},+xt} WCon{False{},+yt} False{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},False{}),
            lt_or_eq(False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)),
            lt_or_eq(False{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt))),
            adc_out_is_cmp(p,xt,yt,False{}),
            fin_shift(False{}, False{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)))
        case WCon{False{},+xt} WCon{False{},+yt} True{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},False{}),
            lt_or_eq(False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)),
            lt_or_eq(True{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt))),
            adc_out_is_cmp(p,xt,yt,False{}),
            fin_shift(False{}, False{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)))
        case WCon{False{},+xt} WCon{True{},+yt} False{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},False{}),
            lt_or_eq(False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)),
            lt_or_eq(False{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt))),
            adc_out_is_cmp(p,xt,yt,False{}),
            fin_shift(False{}, True{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)))
        case WCon{False{},+xt} WCon{True{},+yt} True{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},True{}),
            lt_or_eq(True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)),
            lt_or_eq(True{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt))),
            adc_out_is_cmp(p,xt,yt,True{}),
            fin_shift(False{}, True{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)))
        case WCon{True{},+xt} WCon{False{},+yt} False{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},False{}),
            lt_or_eq(False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)),
            lt_or_eq(False{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt))),
            adc_out_is_cmp(p,xt,yt,False{}),
            fin_shift(True{}, False{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},False{}), xt)))
        case WCon{True{},+xt} WCon{False{},+yt} True{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},True{}),
            lt_or_eq(True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)),
            lt_or_eq(True{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt))),
            adc_out_is_cmp(p,xt,yt,True{}),
            fin_shift(True{}, False{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)))
        case WCon{True{},+xt} WCon{True{},+yt} False{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},True{}),
            lt_or_eq(True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)),
            lt_or_eq(False{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt))),
            adc_out_is_cmp(p,xt,yt,True{}),
            fin_shift(True{}, True{}, False{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)))
        case WCon{True{},+xt} WCon{True{},+yt} True{}:
          Equal.trans(Bool,
            adc_out(p,xt,yt,False{},True{}),
            lt_or_eq(True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)),
            lt_or_eq(True{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt))),
            adc_out_is_cmp(p,xt,yt,True{}),
            fin_shift(True{}, True{}, True{}, Word.cmp(p, Word.adc(p,xt,yt,False{},True{}), xt)))

# Adding zero never carries. Needed by the carry-composition step below.
law adc_out_zero_right:
  for n: Nat
  for u: Word(n)
  {adc_out(n, u, Word.zero(n), False{}, False{}) == False{} : Bool}
def adc_out_zero_right(n, u):
  match n:
    case 0n:
      match u:
        case WNil{}: {==}
    case 1n+p:
      match u:
        case WCon{False{},t}: adc_out_zero_right(p,t)
        case WCon{True{},t}: adc_out_zero_right(p,t)

# --- REMAINING (lemma 4b and step 5) ---------------------------------------
#
# `evmword.carry` decides a limb carry as
#   or(is_lt(add(x,y), x), is_lt(add(add(x,y),cin), add(x,y)))
# so tying it to adc_out needs carry composition:
#
#   law adc_out_split:
#     for n, x, y, c
#     {adc_out(n,x,y,False{},c)
#       == Bool.or(adc_out(n,x,y,False{},False{}),
#                  adc_out(n, Word.add(n,x,y), carry_word(n,c), False{}, False{}))
#       : Bool}
#
# True because a two-step addition cannot overflow twice. The `c = False{}`
# half follows from adc_out_zero_right above plus `Bool.or(b, False{}) == b`.
# The `c = True{}` half is the open work: a direct induction does not go
# through, because the second adc_out's carry chain runs over the bits of
# `add(n,x,y)` rather than over x and y, so the induction hypothesis is about
# the wrong word. It needs a generalisation that carries both chains at once.
#
# With adc_out_split in hand the rest is bookkeeping:
#   - bridge U32 to Word(32n): U32.add(a,b) is U32{Word.add(32n,·,·)} by
#     definition, and L.bit(c) is the U32 whose word is carry_word(32n,c), so
#     adc_is_add_carry and adc_out_split specialise to L.carry directly;
#   - instantiate concat_adc seven times over of_limbs' nesting and discard the
#     256th carry, which is step 5 and is mechanical.
