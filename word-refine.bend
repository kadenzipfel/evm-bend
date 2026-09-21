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
