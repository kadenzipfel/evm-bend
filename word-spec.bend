import Base
import ./evmword.bend as L

# Independent fixed-width bitvector specification. Bit zero is stored first.
type Word256 is Data:
  Bits{value: Word(256n)}

def zero() -> Word256:
  Bits{Word.zero(256n)}

def add(x: Word256, y: Word256) -> Word256:
  match x y:
    case Bits{a} Bits{b}:
      Bits{Word.add(256n, a, b)}

law add_comm:
  for x: Word256
  for y: Word256
  {add(x, y) == add(y, x) : Word256}
def add_comm(x, y):
  match x y:
    case Bits{a} Bits{b}:
      Equal.cong(Word(256n), Word256, w => Bits{w}, Word.add(256n, a, b), Word.add(256n, b, a), Word.add_comm(256n, a, b))

# Concatenate low bits followed by high bits without using machine arithmetic.
def concat(n: Nat, -m: Nat, lo: Word(n), hi: Word(m)) -> Word(Nat.add(n, m)):
  match n:
    case 0n:
      hi
    case 1n+p:
      match lo:
        case WCon{bit, tail}:
          WCon{bit, concat(p, m, tail, hi)}

def prepend(-n: Nat, lo: U32, hi: Word(n)) -> Word(Nat.add(32n, n)):
  match lo:
    case U32{bits}:
      concat(32n, n, bits, hi)

# Explicit representation map for the future full refinement theorem.
def of_limbs(w: L.Word) -> Word256:
  match w:
    case L.W{a, b, c, d, e, f, g, h}:
      Bits{prepend(224n, a, prepend(192n, b, prepend(160n, c, prepend(128n, d, prepend(96n, e, prepend(64n, f, prepend(32n, g, prepend(0n, h, WNil{}))))))))}

law zero_representation:
  {of_limbs(L.zero()) == zero() : Word256}
def zero_representation():
  {==}

# CLOSED. The refinement theorem
#   for x,y: L.Word, of_limbs(L.add(x,y)) == add(of_limbs(x),of_limbs(y))
# is proved in ./word-refine.bend as `of_limbs_add_word`, generically in the
# word width where the lemmas allow it. The five bridge lemmas this comment
# used to list are `adc_out` + `carry_bit_is_full_add` (1), `concat_adc` (2),
# `adc_is_add_carry` (3), `adc_out_is_cmp` (4a) and `adc_out_split` (4b), with
# `carry_is_adc_out` and `limb_sum_is_adc` tying them to L.carry and L.add, and
# `add_splits_into_limbs` doing the seven instantiations of (5).
#
# add_comm below still proves only this reference's commutativity. With the
# refinement in hand it now transfers to L.add.
