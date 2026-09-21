# Limb refinement, step 1 and 2 of the plan recorded at the end of
# ./word-spec.bend: the carry-out of a bitvector adc, and the concatenation
# split that turns one 256-bit add into eight 32-bit adds with a threaded carry.

import Base
import ./word-spec.bend as Spec
import ./evmword.bend as L

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

# --- Lemma 4b: carry composition -------------------------------------------
# A two-step addition cannot overflow twice:
#   carry(x+y+c) == carry(x+y) OR carry((x+y)+c)
# which is exactly the shape evmword.carry decides with its two U32.is_lt tests.
#
# A direct induction fails: the second carry chain runs over the bits of
# add(x,y), not over x and y. The fix is to carry BOTH chains at once, indexed
# by the only three carry states reachable together -- the invariant being
# a = b or g, and never both b and g.

type CarryPair is Data:
  Neither{}
  Base{}
  Bump{}

def pa(p: CarryPair) -> Bool:
  match p:
    case Neither{}: False{}
    case Base{}: True{}
    case Bump{}: True{}

def pb(p: CarryPair) -> Bool:
  match p:
    case Neither{}: False{}
    case Base{}: True{}
    case Bump{}: False{}

def pg(p: CarryPair) -> Bool:
  match p:
    case Neither{}: False{}
    case Base{}: False{}
    case Bump{}: True{}

# How the joint carry state advances over one bit. Bump can fall back to
# Neither or promote to Base; the invariant is preserved throughout.
def pstep(p: CarryPair, x0: Bool, y0: Bool) -> CarryPair:
  match p x0 y0:
    case Neither{} False{} False{}: Neither{}
    case Neither{} False{} True{}: Neither{}
    case Neither{} True{} False{}: Neither{}
    case Neither{} True{} True{}: Base{}
    case Base{} False{} False{}: Neither{}
    case Base{} False{} True{}: Base{}
    case Base{} True{} False{}: Base{}
    case Base{} True{} True{}: Base{}
    case Bump{} False{} False{}: Neither{}
    case Bump{} False{} True{}: Bump{}
    case Bump{} True{} False{}: Bump{}
    case Bump{} True{} True{}: Base{}

law adc_out_split_go:
  for +q: Nat
  for +x: Word(q)
  for +y: Word(q)
  for p: CarryPair
  {adc_out(q,x,y,False{},pa(p))
    == Bool.or(adc_out(q,x,y,False{},pb(p)),
               adc_out(q, Word.adc(q,x,y,False{},pb(p)), Word.zero(q), False{}, pg(p)))
    : Bool}
def adc_out_split_go(q, x, y, p):
  match q:
    case 0n:
      match x y p:
        case WNil{} WNil{} Neither{}: {==}
        case WNil{} WNil{} Base{}: {==}
        case WNil{} WNil{} Bump{}: {==}
    case 1n+q2:
      match x y p:
        case WCon{False{},+xt} WCon{False{},+yt} Neither{}:
          adc_out_split_go(q2, xt, yt, Neither{})
        case WCon{False{},+xt} WCon{True{},+yt} Neither{}:
          adc_out_split_go(q2, xt, yt, Neither{})
        case WCon{True{},+xt} WCon{False{},+yt} Neither{}:
          adc_out_split_go(q2, xt, yt, Neither{})
        case WCon{True{},+xt} WCon{True{},+yt} Neither{}:
          adc_out_split_go(q2, xt, yt, Base{})
        case WCon{False{},+xt} WCon{False{},+yt} Base{}:
          adc_out_split_go(q2, xt, yt, Neither{})
        case WCon{False{},+xt} WCon{True{},+yt} Base{}:
          adc_out_split_go(q2, xt, yt, Base{})
        case WCon{True{},+xt} WCon{False{},+yt} Base{}:
          adc_out_split_go(q2, xt, yt, Base{})
        case WCon{True{},+xt} WCon{True{},+yt} Base{}:
          adc_out_split_go(q2, xt, yt, Base{})
        case WCon{False{},+xt} WCon{False{},+yt} Bump{}:
          adc_out_split_go(q2, xt, yt, Neither{})
        case WCon{False{},+xt} WCon{True{},+yt} Bump{}:
          adc_out_split_go(q2, xt, yt, Bump{})
        case WCon{True{},+xt} WCon{False{},+yt} Bump{}:
          adc_out_split_go(q2, xt, yt, Bump{})
        case WCon{True{},+xt} WCon{True{},+yt} Bump{}:
          adc_out_split_go(q2, xt, yt, Base{})

# At a nonzero width, "increment by c" can be written either as a carry-in over
# a zero word or as adding the word that is c in bit 0. Both put AND(s0,c) into
# the tail's carry, so they agree.
law zero_vs_carry_word:
  for +n: Nat
  for +s: Word(1n+n)
  for c: Bool
  {adc_out(1n+n, s, Word.zero(1n+n), False{}, c)
    == adc_out(1n+n, s, carry_word(1n+n,c), False{}, False{}) : Bool}
def zero_vs_carry_word(n, s, c):
  match s:
    case WCon{s0, st}:
      match s0 c:
        case False{} False{}: {==}
        case False{} True{}: {==}
        case True{} False{}: {==}
        case True{} True{}: {==}

# Lemma 4b. Stated at width 1n+n: at width zero it is false, since a 0-bit
# add(x,y) cannot represent the carry the increment would have produced.
law adc_out_split:
  for +n: Nat
  for +x: Word(1n+n)
  for +y: Word(1n+n)
  for c: Bool
  {adc_out(1n+n,x,y,False{},c)
    == Bool.or(adc_out(1n+n,x,y,False{},False{}),
               adc_out(1n+n, Word.add(1n+n,x,y), carry_word(1n+n,c), False{}, False{}))
    : Bool}
def adc_out_split(n, x, y, c):
  match c:
    case False{}:
      Equal.trans(Bool,
        adc_out(1n+n,x,y,False{},False{}),
        Bool.or(adc_out(1n+n,x,y,False{},False{}),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), Word.zero(1n+n), False{}, False{})),
        Bool.or(adc_out(1n+n,x,y,False{},False{}),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), carry_word(1n+n,False{}), False{}, False{})),
        adc_out_split_go(1n+n, x, y, Neither{}),
        Equal.cong(Bool, Bool,
          w => Bool.or(adc_out(1n+n,x,y,False{},False{}), w),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), Word.zero(1n+n), False{}, False{}),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), carry_word(1n+n,False{}), False{}, False{}),
          zero_vs_carry_word(n, Word.adc(1n+n,x,y,False{},False{}), False{})))
    case True{}:
      Equal.trans(Bool,
        adc_out(1n+n,x,y,False{},True{}),
        Bool.or(adc_out(1n+n,x,y,False{},False{}),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), Word.zero(1n+n), False{}, True{})),
        Bool.or(adc_out(1n+n,x,y,False{},False{}),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), carry_word(1n+n,True{}), False{}, False{})),
        adc_out_split_go(1n+n, x, y, Bump{}),
        Equal.cong(Bool, Bool,
          w => Bool.or(adc_out(1n+n,x,y,False{},False{}), w),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), Word.zero(1n+n), False{}, True{}),
          adc_out(1n+n, Word.adc(1n+n,x,y,False{},False{}), carry_word(1n+n,True{}), False{}, False{}),
          zero_vs_carry_word(n, Word.adc(1n+n,x,y,False{},False{}), True{})))

# --- The bridge: evmword.carry IS the bitvector carry out -------------------
# L.carry decides a limb carry with two U32.is_lt tests. Lemma 4a turns each
# test into an adc_out, and lemma 4b joins them. U32.add is U32{Word.add(32n,·,·)}
# and U32.cmp is Word.cmp(32n,·,·) by definition, so the two sides meet.

law carry_is_adc_out:
  for +xa: Word(32n)
  for +ya: Word(32n)
  for c: Bool
  {L.carry(U32{xa}, U32{ya}, L.bit(c))
    == L.bit(adc_out(32n, xa, ya, False{}, c)) : U32}
def carry_is_adc_out(xa, ya, c):
  match c:
    case False{}:
      Equal.cong(Bool, U32, w => L.bit(w),
        Bool.or(Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
                Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
                                        Word.add(32n,xa,ya)))),
        adc_out(32n, xa, ya, False{}, False{}),
        Equal.trans(Bool,
          Bool.or(Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
                  Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
                                          Word.add(32n,xa,ya)))),
          Bool.or(adc_out(32n,xa,ya,False{},False{}),
                  Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
                                          Word.add(32n,xa,ya)))),
          adc_out(32n, xa, ya, False{}, False{}),
          Equal.cong(Bool, Bool,
            w => Bool.or(w, Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
                                                    Word.add(32n,xa,ya)))),
            Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
            adc_out(32n,xa,ya,False{},False{}),
            Equal.sym(Bool, adc_out(32n,xa,ya,False{},False{}),
              Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
              adc_out_is_cmp(32n, xa, ya, False{}))),
          Equal.trans(Bool,
            Bool.or(adc_out(32n,xa,ya,False{},False{}),
                    Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
                                            Word.add(32n,xa,ya)))),
            Bool.or(adc_out(32n,xa,ya,False{},False{}),
                    adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,False{}), False{}, False{})),
            adc_out(32n, xa, ya, False{}, False{}),
            Equal.cong(Bool, Bool,
              w => Bool.or(adc_out(32n,xa,ya,False{},False{}), w),
              Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
                                      Word.add(32n,xa,ya))),
              adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,False{}), False{}, False{}),
              Equal.sym(Bool,
                adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,False{}), False{}, False{}),
                Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
                                        Word.add(32n,xa,ya))),
                adc_out_is_cmp(32n, Word.add(32n,xa,ya), carry_word(32n,False{}), False{}))),
            Equal.sym(Bool,
              adc_out(32n, xa, ya, False{}, False{}),
              Bool.or(adc_out(32n,xa,ya,False{},False{}),
                      adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,False{}), False{}, False{})),
              adc_out_split(31n, xa, ya, False{})))))
    case True{}:
      Equal.cong(Bool, U32, w => L.bit(w),
        Bool.or(Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
                Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
                                        Word.add(32n,xa,ya)))),
        adc_out(32n, xa, ya, False{}, True{}),
        Equal.trans(Bool,
          Bool.or(Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
                  Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
                                          Word.add(32n,xa,ya)))),
          Bool.or(adc_out(32n,xa,ya,False{},False{}),
                  Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
                                          Word.add(32n,xa,ya)))),
          adc_out(32n, xa, ya, False{}, True{}),
          Equal.cong(Bool, Bool,
            w => Bool.or(w, Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
                                                    Word.add(32n,xa,ya)))),
            Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
            adc_out(32n,xa,ya,False{},False{}),
            Equal.sym(Bool, adc_out(32n,xa,ya,False{},False{}),
              Cmp.is_lt(Word.cmp(32n, Word.add(32n,xa,ya), xa)),
              adc_out_is_cmp(32n, xa, ya, False{}))),
          Equal.trans(Bool,
            Bool.or(adc_out(32n,xa,ya,False{},False{}),
                    Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
                                            Word.add(32n,xa,ya)))),
            Bool.or(adc_out(32n,xa,ya,False{},False{}),
                    adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,True{}), False{}, False{})),
            adc_out(32n, xa, ya, False{}, True{}),
            Equal.cong(Bool, Bool,
              w => Bool.or(adc_out(32n,xa,ya,False{},False{}), w),
              Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
                                      Word.add(32n,xa,ya))),
              adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,True{}), False{}, False{}),
              Equal.sym(Bool,
                adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,True{}), False{}, False{}),
                Cmp.is_lt(Word.cmp(32n, Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
                                        Word.add(32n,xa,ya))),
                adc_out_is_cmp(32n, Word.add(32n,xa,ya), carry_word(32n,True{}), False{}))),
            Equal.sym(Bool,
              adc_out(32n, xa, ya, False{}, True{}),
              Bool.or(adc_out(32n,xa,ya,False{},False{}),
                      adc_out(32n, Word.add(32n,xa,ya), carry_word(32n,True{}), False{}, False{})),
              adc_out_split(31n, xa, ya, True{})))))

# The other half of the bridge: a limb's sum. evmword.add computes each limb as
# U32.add(U32.add(a,i), carry), which is the 32-bit adc with that carry in.
law limb_sum_is_adc:
  for +xa: Word(32n)
  for +ya: Word(32n)
  for c: Bool
  {U32.add(U32.add(U32{xa}, U32{ya}), L.bit(c))
    == U32{Word.adc(32n, xa, ya, False{}, c)} : U32}
def limb_sum_is_adc(xa, ya, c):
  match c:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w},
        Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
        Word.adc(32n, xa, ya, False{}, False{}),
        Equal.sym(Word(32n),
          Word.adc(32n, xa, ya, False{}, False{}),
          Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,False{})),
          adc_is_add_carry(32n, xa, ya, False{})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w},
        Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
        Word.adc(32n, xa, ya, False{}, True{}),
        Equal.sym(Word(32n),
          Word.adc(32n, xa, ya, False{}, True{}),
          Word.add(32n, Word.add(32n,xa,ya), carry_word(32n,True{})),
          adc_is_add_carry(32n, xa, ya, True{})))

# --- Step 5 feasibility ----------------------------------------------------
# The split lemma instantiated at the first limb boundary. The 256-bit terms do
# not strain the checker (90ms), so the remaining seven instantiations are
# mechanical rather than blocked.
law concat_adc_32_224:
  for +lo1: Word(32n)
  for +lo2: Word(32n)
  for +hi1: Word(224n)
  for +hi2: Word(224n)
  {Word.adc(256n, Spec.concat(32n,224n,lo1,hi1), Spec.concat(32n,224n,lo2,hi2), False{}, False{})
    == Spec.concat(32n, 224n, Word.adc(32n,lo1,lo2,False{},False{}),
         Word.adc(224n,hi1,hi2,False{},adc_out(32n,lo1,lo2,False{},False{})))
    : Word(256n)}
def concat_adc_32_224(lo1, lo2, hi1, hi2):
  concat_adc(32n, 224n, lo1, lo2, hi1, hi2, False{})

# --- What is left ----------------------------------------------------------
# The theorem itself:
#   for x,y: L.Word.  of_limbs(L.add(x,y)) == Spec.add(of_limbs x, of_limbs y)
#
# Everything it rests on is proved above. What remains is assembly:
#   - seven more instantiations of concat_adc down of_limbs' nesting
#     (32/224, 32/192, ... 32/0), threading adc_out as each carry;
#   - matching L.add's explicit c0..c6 chain to that threaded carry using
#     carry_is_adc_out, and each limb's value using limb_sum_is_adc;
#   - limb 0 is `U32.add(a,i)` with no carry argument, so it needs
#     `U32.add(u, 0) == u` rather than limb_sum_is_adc;
#   - discarding the eighth carry, which is what makes the arithmetic modular.

# --- Step 5a: one 256-bit add is eight 32-bit adds --------------------------
# concat_adc instantiated down of_limbs' nesting: 256 = 32+224, 224 = 32+192,
# ... 32 = 32+0. The eighth carry is discarded for free -- the last level's high
# half is Word.adc(0n, WNil, WNil, ...), which is WNil. That is what makes the
# arithmetic modular.

law add_splits_into_limbs:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +x5: Word(32n)
  for +x6: Word(32n)
  for +x7: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  for +y5: Word(32n)
  for +y6: Word(32n)
  for +y7: Word(32n)
  {Word.add(256n,Spec.concat(32n,224n,x0,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))))),Spec.concat(32n,224n,y0,Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))))))) == Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))))))) : Word(256n)}
def add_splits_into_limbs(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7):
Equal.trans(Word(256n),
  Word.adc(256n,Spec.concat(32n,224n,x0,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))))),Spec.concat(32n,224n,y0,Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))))))),False{},False{}),
  Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Word.adc(224n,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))))),Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))))),False{},adc_out(32n,x0,y0,False{},False{}))),
  Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))))))),
  concat_adc(32n,224n,x0,y0,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))))),Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))))),False{}),
  Equal.cong(Word(224n), Word(256n), w => Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),w),
    Word.adc(224n,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))))),Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))))),False{},adc_out(32n,x0,y0,False{},False{})),
    Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))),
    Equal.trans(Word(224n),
  Word.adc(224n,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))))),Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))))),False{},adc_out(32n,x0,y0,False{},False{})),
  Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Word.adc(192n,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))),Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))))),False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),
  Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))),
  concat_adc(32n,192n,x1,y1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))),Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))))),adc_out(32n,x0,y0,False{},False{})),
  Equal.cong(Word(192n), Word(224n), w => Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),w),
    Word.adc(192n,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))),Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))))),False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),
    Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))))),
    Equal.trans(Word(192n),
  Word.adc(192n,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))),Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))))),False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),
  Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Word.adc(160n,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))),Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))),False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),
  Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))))),
  concat_adc(32n,160n,x2,y2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))),Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))),adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),
  Equal.cong(Word(160n), Word(192n), w => Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),w),
    Word.adc(160n,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))),Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))),False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),
    Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))),
    Equal.trans(Word(160n),
  Word.adc(160n,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))))),Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))),False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),
  Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Word.adc(128n,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))),Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))),False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),
  Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))),
  concat_adc(32n,128n,x3,y3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))),Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))),adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),
  Equal.cong(Word(128n), Word(160n), w => Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),w),
    Word.adc(128n,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))),Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))),False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),
    Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))),
    Equal.trans(Word(128n),
  Word.adc(128n,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))),Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})))),False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),
  Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Word.adc(96n,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))),Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))),False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),
  Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))),
  concat_adc(32n,96n,x4,y4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))),Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))),adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),
  Equal.cong(Word(96n), Word(128n), w => Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),w),
    Word.adc(96n,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))),Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))),False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),
    Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))),
    Equal.trans(Word(96n),
  Word.adc(96n,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{}))),Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))),False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),
  Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Word.adc(64n,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})),Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})),False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),
  Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))),
  concat_adc(32n,64n,x5,y5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})),Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})),adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),
  Equal.cong(Word(64n), Word(96n), w => Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),w),
    Word.adc(64n,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})),Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})),False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),
    Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})),
    Equal.trans(Word(64n),
  Word.adc(64n,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})),Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{})),False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),
  Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Word.adc(32n,Spec.concat(32n,0n,x7,WNil{}),Spec.concat(32n,0n,y7,WNil{}),False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))),
  Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})),
  concat_adc(32n,32n,x6,y6,Spec.concat(32n,0n,x7,WNil{}),Spec.concat(32n,0n,y7,WNil{}),adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),
  Equal.cong(Word(32n), Word(64n), w => Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),w),
    Word.adc(32n,Spec.concat(32n,0n,x7,WNil{}),Spec.concat(32n,0n,y7,WNil{}),False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),
    Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}),
    concat_adc(32n,0n,x7,y7,WNil{},WNil{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))))))))))))))))

# --- Step 5b: evmword's carry chain is the adc_out chain -------------------

law carry_chain0:
  for +x0: Word(32n)
  for +y0: Word(32n)
  {L.carry(U32{x0},U32{y0},0) == L.bit(adc_out(32n,x0,y0,False{},False{})) : U32}
def carry_chain0(x0, y0):
  carry_is_adc_out(x0, y0, False{})

law carry_chain1:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  {L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)) == L.bit(adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))) : U32}
def carry_chain1(x0, x1, y0, y1):
  Equal.trans(U32,
    L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)),
    L.carry(U32{x1},U32{y1},L.bit(adc_out(32n,x0,y0,False{},False{}))),
    L.bit(adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),
    Equal.cong(U32, U32, u => L.carry(U32{x1},U32{y1},u),
      L.carry(U32{x0},U32{y0},0), L.bit(adc_out(32n,x0,y0,False{},False{})), carry_chain0(x0, y0)),
    carry_is_adc_out(x1, y1, adc_out(32n,x0,y0,False{},False{})))

law carry_chain2:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  {L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))) == L.bit(adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))) : U32}
def carry_chain2(x0, x1, x2, y0, y1, y2):
  Equal.trans(U32,
    L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),
    L.carry(U32{x2},U32{y2},L.bit(adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),
    L.bit(adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),
    Equal.cong(U32, U32, u => L.carry(U32{x2},U32{y2},u),
      L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)), L.bit(adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))), carry_chain1(x0, x1, y0, y1)),
    carry_is_adc_out(x2, y2, adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))

law carry_chain3:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  {L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))) == L.bit(adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))) : U32}
def carry_chain3(x0, x1, x2, x3, y0, y1, y2, y3):
  Equal.trans(U32,
    L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),
    L.carry(U32{x3},U32{y3},L.bit(adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),
    L.bit(adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),
    Equal.cong(U32, U32, u => L.carry(U32{x3},U32{y3},u),
      L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))), L.bit(adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))), carry_chain2(x0, x1, x2, y0, y1, y2)),
    carry_is_adc_out(x3, y3, adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))

law carry_chain4:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  {L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))) == L.bit(adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))) : U32}
def carry_chain4(x0, x1, x2, x3, x4, y0, y1, y2, y3, y4):
  Equal.trans(U32,
    L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),
    L.carry(U32{x4},U32{y4},L.bit(adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),
    L.bit(adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),
    Equal.cong(U32, U32, u => L.carry(U32{x4},U32{y4},u),
      L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))), L.bit(adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))), carry_chain3(x0, x1, x2, x3, y0, y1, y2, y3)),
    carry_is_adc_out(x4, y4, adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))

law carry_chain5:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +x5: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  for +y5: Word(32n)
  {L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))) == L.bit(adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))) : U32}
def carry_chain5(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5):
  Equal.trans(U32,
    L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),
    L.carry(U32{x5},U32{y5},L.bit(adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),
    L.bit(adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),
    Equal.cong(U32, U32, u => L.carry(U32{x5},U32{y5},u),
      L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))), L.bit(adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))), carry_chain4(x0, x1, x2, x3, x4, y0, y1, y2, y3, y4)),
    carry_is_adc_out(x5, y5, adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))

law carry_chain6:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +x5: Word(32n)
  for +x6: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  for +y5: Word(32n)
  for +y6: Word(32n)
  {L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))) == L.bit(adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))) : U32}
def carry_chain6(x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6):
  Equal.trans(U32,
    L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),
    L.carry(U32{x6},U32{y6},L.bit(adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),
    L.bit(adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),
    Equal.cong(U32, U32, u => L.carry(U32{x6},U32{y6},u),
      L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))), L.bit(adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))), carry_chain5(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5)),
    carry_is_adc_out(x6, y6, adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))

# --- Step 5b: each limb's value is the 32-bit adc --------------------------

law limb_val0:
  for +x0: Word(32n)
  for +y0: Word(32n)
  {U32.add(U32{x0},U32{y0}) == U32{Word.adc(32n,x0,y0,False{},False{})} : U32}
def limb_val0(x0, y0):
  {==}

law limb_val1:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  {U32.add(U32.add(U32{x1},U32{y1}),L.carry(U32{x0},U32{y0},0)) == U32{Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))} : U32}
def limb_val1(x0, x1, y0, y1):
  Equal.trans(U32,
    U32.add(U32.add(U32{x1},U32{y1}),L.carry(U32{x0},U32{y0},0)),
    U32.add(U32.add(U32{x1},U32{y1}),L.bit(adc_out(32n,x0,y0,False{},False{}))),
    U32{Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))},
    Equal.cong(U32, U32, u => U32.add(U32.add(U32{x1},U32{y1}),u),
      L.carry(U32{x0},U32{y0},0), L.bit(adc_out(32n,x0,y0,False{},False{})), carry_chain0(x0, y0)),
    limb_sum_is_adc(x1, y1, adc_out(32n,x0,y0,False{},False{})))

law limb_val2:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  {U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))) == U32{Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))} : U32}
def limb_val2(x0, x1, x2, y0, y1, y2):
  Equal.trans(U32,
    U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),
    U32.add(U32.add(U32{x2},U32{y2}),L.bit(adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),
    U32{Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))},
    Equal.cong(U32, U32, u => U32.add(U32.add(U32{x2},U32{y2}),u),
      L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)), L.bit(adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))), carry_chain1(x0, x1, y0, y1)),
    limb_sum_is_adc(x2, y2, adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))

law limb_val3:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  {U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))) == U32{Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))} : U32}
def limb_val3(x0, x1, x2, x3, y0, y1, y2, y3):
  Equal.trans(U32,
    U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),
    U32.add(U32.add(U32{x3},U32{y3}),L.bit(adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),
    U32{Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))},
    Equal.cong(U32, U32, u => U32.add(U32.add(U32{x3},U32{y3}),u),
      L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))), L.bit(adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))), carry_chain2(x0, x1, x2, y0, y1, y2)),
    limb_sum_is_adc(x3, y3, adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))

law limb_val4:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  {U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))) == U32{Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))} : U32}
def limb_val4(x0, x1, x2, x3, x4, y0, y1, y2, y3, y4):
  Equal.trans(U32,
    U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),
    U32.add(U32.add(U32{x4},U32{y4}),L.bit(adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),
    U32{Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))},
    Equal.cong(U32, U32, u => U32.add(U32.add(U32{x4},U32{y4}),u),
      L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))), L.bit(adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))), carry_chain3(x0, x1, x2, x3, y0, y1, y2, y3)),
    limb_sum_is_adc(x4, y4, adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))

law limb_val5:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +x5: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  for +y5: Word(32n)
  {U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))) == U32{Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))} : U32}
def limb_val5(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5):
  Equal.trans(U32,
    U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),
    U32.add(U32.add(U32{x5},U32{y5}),L.bit(adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),
    U32{Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))},
    Equal.cong(U32, U32, u => U32.add(U32.add(U32{x5},U32{y5}),u),
      L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))), L.bit(adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))), carry_chain4(x0, x1, x2, x3, x4, y0, y1, y2, y3, y4)),
    limb_sum_is_adc(x5, y5, adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))

law limb_val6:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +x5: Word(32n)
  for +x6: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  for +y5: Word(32n)
  for +y6: Word(32n)
  {U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))) == U32{Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))} : U32}
def limb_val6(x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6):
  Equal.trans(U32,
    U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),
    U32.add(U32.add(U32{x6},U32{y6}),L.bit(adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),
    U32{Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))},
    Equal.cong(U32, U32, u => U32.add(U32.add(U32{x6},U32{y6}),u),
      L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))), L.bit(adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))), carry_chain5(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5)),
    limb_sum_is_adc(x6, y6, adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))

law limb_val7:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +x5: Word(32n)
  for +x6: Word(32n)
  for +x7: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  for +y5: Word(32n)
  for +y6: Word(32n)
  for +y7: Word(32n)
  {U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))) == U32{Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))} : U32}
def limb_val7(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7):
  Equal.trans(U32,
    U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),
    U32.add(U32.add(U32{x7},U32{y7}),L.bit(adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))),
    U32{Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))},
    Equal.cong(U32, U32, u => U32.add(U32.add(U32{x7},U32{y7}),u),
      L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))), L.bit(adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))), carry_chain6(x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6)),
    limb_sum_is_adc(x7, y7, adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))))

# --- THE THEOREM ------------------------------------------------------------
# The limb representation refines the bitvector spec for addition: mapping the
# eight-U32 word into a 256-bit bitvector commutes with adding. This is the
# claim word-spec.bend records as OUTSTANDING.

law of_limbs_add:
  for +x0: Word(32n)
  for +x1: Word(32n)
  for +x2: Word(32n)
  for +x3: Word(32n)
  for +x4: Word(32n)
  for +x5: Word(32n)
  for +x6: Word(32n)
  for +x7: Word(32n)
  for +y0: Word(32n)
  for +y1: Word(32n)
  for +y2: Word(32n)
  for +y3: Word(32n)
  for +y4: Word(32n)
  for +y5: Word(32n)
  for +y6: Word(32n)
  for +y7: Word(32n)
  {Spec.of_limbs(L.add(L.W{U32{x0},U32{x1},U32{x2},U32{x3},U32{x4},U32{x5},U32{x6},U32{x7}}, L.W{U32{y0},U32{y1},U32{y2},U32{y3},U32{y4},U32{y5},U32{y6},U32{y7}}))
    == Spec.add(Spec.of_limbs(L.W{U32{x0},U32{x1},U32{x2},U32{x3},U32{x4},U32{x5},U32{x6},U32{x7}}), Spec.of_limbs(L.W{U32{y0},U32{y1},U32{y2},U32{y3},U32{y4},U32{y5},U32{y6},U32{y7}})) : Spec.Word256}
def of_limbs_add(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7):
  Equal.trans(Spec.Word256,
    Spec.of_limbs(L.add(L.W{U32{x0},U32{x1},U32{x2},U32{x3},U32{x4},U32{x5},U32{x6},U32{x7}}, L.W{U32{y0},U32{y1},U32{y2},U32{y3},U32{y4},U32{y5},U32{y6},U32{y7}})),
    Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
    Spec.add(Spec.of_limbs(L.W{U32{x0},U32{x1},U32{x2},U32{x3},U32{x4},U32{x5},U32{x6},U32{x7}}), Spec.of_limbs(L.W{U32{y0},U32{y1},U32{y2},U32{y3},U32{y4},U32{y5},U32{y6},U32{y7}})),
    Equal.trans(Spec.Word256,
  Spec.Bits{Spec.prepend(224n,U32.add(U32{x0},U32{y0}),Spec.prepend(192n,U32.add(U32.add(U32{x1},U32{y1}),L.carry(U32{x0},U32{y0},0)),Spec.prepend(160n,U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.prepend(192n,U32.add(U32.add(U32{x1},U32{y1}),L.carry(U32{x0},U32{y0},0)),Spec.prepend(160n,U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.prepend(224n,u,Spec.prepend(192n,U32.add(U32.add(U32{x1},U32{y1}),L.carry(U32{x0},U32{y0},0)),Spec.prepend(160n,U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  U32.add(U32{x0},U32{y0}), U32{Word.adc(32n,x0,y0,False{},False{})}, limb_val0(x0, y0)),
  Equal.trans(Spec.Word256,
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.prepend(192n,U32.add(U32.add(U32{x1},U32{y1}),L.carry(U32{x0},U32{y0},0)),Spec.prepend(160n,U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.prepend(160n,U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.prepend(192n,u,Spec.prepend(160n,U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  U32.add(U32.add(U32{x1},U32{y1}),L.carry(U32{x0},U32{y0},0)), U32{Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))}, limb_val1(x0, x1, y0, y1)),
  Equal.trans(Spec.Word256,
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.prepend(160n,U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.prepend(160n,u,Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  U32.add(U32.add(U32{x2},U32{y2}),L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))), U32{Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))}, limb_val2(x0, x1, x2, y0, y1, y2)),
  Equal.trans(Spec.Word256,
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.prepend(128n,U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.prepend(128n,u,Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  U32.add(U32.add(U32{x3},U32{y3}),L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))), U32{Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))}, limb_val3(x0, x1, x2, x3, y0, y1, y2, y3)),
  Equal.trans(Spec.Word256,
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.prepend(96n,U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.prepend(96n,u,Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  U32.add(U32.add(U32{x4},U32{y4}),L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))), U32{Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))}, limb_val4(x0, x1, x2, x3, x4, y0, y1, y2, y3, y4)),
  Equal.trans(Spec.Word256,
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.prepend(64n,U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.prepend(64n,u,Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  U32.add(U32.add(U32{x5},U32{y5}),L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))), U32{Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))}, limb_val5(x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5)),
  Equal.trans(Spec.Word256,
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.prepend(32n,U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{}))))))))},
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.prepend(32n,u,Spec.prepend(0n,U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))),WNil{}))))))))},
  U32.add(U32.add(U32{x6},U32{y6}),L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0))))))), U32{Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))}, limb_val6(x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6)),
  Equal.cong(U32, Spec.Word256, u => Spec.Bits{Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.prepend(0n,u,WNil{}))))))))},
  U32.add(U32.add(U32{x7},U32{y7}),L.carry(U32{x6},U32{y6},L.carry(U32{x5},U32{y5},L.carry(U32{x4},U32{y4},L.carry(U32{x3},U32{y3},L.carry(U32{x2},U32{y2},L.carry(U32{x1},U32{y1},L.carry(U32{x0},U32{y0},0)))))))), U32{Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))))}, limb_val7(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7))))))))),
    Equal.cong(Word(256n), Spec.Word256, w => Spec.Bits{w},
  Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))))))),
  Word.add(256n,Spec.concat(32n,224n,x0,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))))),Spec.concat(32n,224n,y0,Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))))))),
  Equal.sym(Word(256n), Word.add(256n,Spec.concat(32n,224n,x0,Spec.concat(32n,192n,x1,Spec.concat(32n,160n,x2,Spec.concat(32n,128n,x3,Spec.concat(32n,96n,x4,Spec.concat(32n,64n,x5,Spec.concat(32n,32n,x6,Spec.concat(32n,0n,x7,WNil{})))))))),Spec.concat(32n,224n,y0,Spec.concat(32n,192n,y1,Spec.concat(32n,160n,y2,Spec.concat(32n,128n,y3,Spec.concat(32n,96n,y4,Spec.concat(32n,64n,y5,Spec.concat(32n,32n,y6,Spec.concat(32n,0n,y7,WNil{}))))))))), Spec.concat(32n,224n,Word.adc(32n,x0,y0,False{},False{}),Spec.concat(32n,192n,Word.adc(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})),Spec.concat(32n,160n,Word.adc(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))),Spec.concat(32n,128n,Word.adc(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))),Spec.concat(32n,96n,Word.adc(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))),Spec.concat(32n,64n,Word.adc(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))),Spec.concat(32n,32n,Word.adc(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{}))))))),Spec.concat(32n,0n,Word.adc(32n,x7,y7,False{},adc_out(32n,x6,y6,False{},adc_out(32n,x5,y5,False{},adc_out(32n,x4,y4,False{},adc_out(32n,x3,y3,False{},adc_out(32n,x2,y2,False{},adc_out(32n,x1,y1,False{},adc_out(32n,x0,y0,False{},False{})))))))),WNil{})))))))),
    add_splits_into_limbs(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7))))

# The same claim over arbitrary limbs, and then over arbitrary limb words --
# the form word-spec.bend states as outstanding. Split in two because a match
# may not scrutinise a field bound by an enclosing match.
law of_limbs_add_limbs:
  for +a0: U32
  for +a1: U32
  for +a2: U32
  for +a3: U32
  for +a4: U32
  for +a5: U32
  for +a6: U32
  for +a7: U32
  for +b0: U32
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +b4: U32
  for +b5: U32
  for +b6: U32
  for +b7: U32
  {Spec.of_limbs(L.add(L.W{a0,a1,a2,a3,a4,a5,a6,a7}, L.W{b0,b1,b2,b3,b4,b5,b6,b7}))
    == Spec.add(Spec.of_limbs(L.W{a0,a1,a2,a3,a4,a5,a6,a7}), Spec.of_limbs(L.W{b0,b1,b2,b3,b4,b5,b6,b7})) : Spec.Word256}
def of_limbs_add_limbs(a0,a1,a2,a3,a4,a5,a6,a7,b0,b1,b2,b3,b4,b5,b6,b7):
  match a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:
    case U32{x0} U32{x1} U32{x2} U32{x3} U32{x4} U32{x5} U32{x6} U32{x7}
             U32{y0} U32{y1} U32{y2} U32{y3} U32{y4} U32{y5} U32{y6} U32{y7}:
      of_limbs_add(x0,x1,x2,x3,x4,x5,x6,x7,y0,y1,y2,y3,y4,y5,y6,y7)

law of_limbs_add_word:
  for +x: L.Word
  for +y: L.Word
  {Spec.of_limbs(L.add(x,y)) == Spec.add(Spec.of_limbs(x), Spec.of_limbs(y))
    : Spec.Word256}
def of_limbs_add_word(x, y):
  match x y:
    case L.W{a0,a1,a2,a3,a4,a5,a6,a7} L.W{b0,b1,b2,b3,b4,b5,b6,b7}:
      of_limbs_add_limbs(a0,a1,a2,a3,a4,a5,a6,a7,b0,b1,b2,b3,b4,b5,b6,b7)
