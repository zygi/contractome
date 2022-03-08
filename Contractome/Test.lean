import Lean.Meta

import Contractome.Utils.PersistentArray
import Contractome.Utils.RBMap2
import Contractome.Utils
import Std.Data.RBMap
-- import Std.Data.PersistentArray

open MStd
open Lean

deriving instance Repr for PersistentArrayNode
deriving instance Repr for PersistentArray

def pa : PersistentArray Nat := PersistentArray.empty

#eval [1, 2]

syntax "p[" sepBy(term, ", ") "]" : term

macro_rules
  | `(p[ $elems,* ]) => do
    let rec expandPArrLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandPArrLit i false result
      | i+1, false => expandPArrLit i true  (← ``(PersistentArray.push $result $(elems.elemsAndSeps[i])))
    -- if elems.elemsAndSeps.size < 64 then
    expandPArrLit elems.elemsAndSeps.size false (← ``(PersistentArray.empty))
    -- else
      -- `(%[ $elems,* | List.nil ])

-- macro_rules
--   | `(p[ $elems,* ]) => `(List.toPersistentArray (α:=UInt8) [ $elems,* ])

-- #eval (#[1]).get! 0

set_option maxRecDepth 1000
#redComp p[5, 2]

structure FakeArray (α : Type) where
  data : Std.RBMap Nat α Ord.compare := Std.mkRBMap Nat α Ord.compare
  size : Nat := 0

namespace FakeArray
variable {α : Type}
def empty : FakeArray α := {}
def get? (a : FakeArray α) (i : Nat) : Option α := a.data.find? i
def set! (a : FakeArray α) (i : Nat) (v: α) : FakeArray α :=
  if i >= a.size then a else {a with data := a.data.insert i v}

def push (a : FakeArray α) (v: α) : FakeArray α := {
  data := (a.data.insert a.size v)
  size := a.size + 1
}
end FakeArray

syntax "f[" sepBy(term, ", ") "]" : term

macro_rules
  | `(f[ $elems,* ]) => do
    let rec expandPArrLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandPArrLit i false result
      | i+1, false => expandPArrLit i true  (← ``(FakeArray.push $result $(elems.elemsAndSeps[i])))
    -- if elems.elemsAndSeps.size < 64 then
    expandPArrLit elems.elemsAndSeps.size false (← ``(FakeArray.empty))

-- #reduce f[1, 2, 3, 4, 5, 6, 7, 8, 9]

#eval (pa.push w5).get! 0


-- #reduce pa.tail.set! 0 0
-- #eval (pa.set 0 5)
