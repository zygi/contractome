import AssertCmd

namespace ByteArray

-- deriving instance BEq for ByteArray
instance : BEq ByteArray := ⟨ fun a b => BEq.beq a.data b.data ⟩
deriving instance Repr for ByteArray

structure Iterator where
  s : ByteArray
  i : Nat
deriving Inhabited, Repr, BEq
  -- deriving DecidableEq

def mkIterator (s : ByteArray) : Iterator :=
  ⟨s, 0⟩

namespace Iterator
def toByteArray : Iterator → ByteArray
  | ⟨s, _⟩ => s

def remainingBytes : Iterator → Nat
  | ⟨s, i⟩ => s.size - i

def pos : Iterator → Nat
  | ⟨s, i⟩ => i

def curr : Iterator → UInt8
  | ⟨s, i⟩ => ByteArray.get! s i

def currn (it: Iterator) (n : Nat) : ByteArray :=   
  match it with
  | ⟨s, i⟩ => s.copySlice i empty 0 n


-- def hasCurr : Iterator → Bool
--   | ⟨s, i⟩ => i < s.size-1

-- def hasCurrN : Iterator → Nat → Bool
--   | ⟨s, i⟩, n => i+n < s.size

def hasCurr : Iterator → Bool
  | ⟨s, i⟩ => i < s.size

def hasCurrN : Iterator → Nat → Bool
  | ⟨s, i⟩, n => i+n-1 < s.size

namespace Test
  private def inp : Iterator := ⟨ ByteArray.mk #[0, 1, 2] , 1⟩
  #assert inp.hasCurr == true
  #assert (inp.hasCurrN 2) == true
  #assert (inp.hasCurrN 3) == false
  #assert (inp.currn 2) == (ByteArray.mk #[1, 2])
end Test

def hasPrev : Iterator → Bool
  | ⟨s, i⟩ => i > 0

def next (it : Iterator) : Iterator := match it with
  | ⟨s, i⟩ => ⟨s, i+1⟩

def prev (it : Iterator) : Iterator := match it with
  | ⟨s, i⟩ => ⟨s, i-1⟩


-- def setCurr : Iterator → Char → Iterator
--   | ⟨s, i⟩, c => ⟨s.set i c, i⟩

def toEnd : Iterator → Iterator
  | ⟨s, _⟩ => ⟨s, s.size⟩

-- def extract : Iterator → Iterator → ByteArray
--   | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
--     if s₁ ≠ s₂ || b > e then ""
--     else s₁.extract b e


def remainingToByteArray : Iterator → ByteArray
  | ⟨s, i⟩ => s.extract i (i+s.size)

def nextn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => nextn it.next i

def prevn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => prevn it.prev i
  
end Iterator

end ByteArray