import Contractome.Interfaces
import Contractome.UInt256
import Contractome.Utils.RBMap2
import Std.Data.Stack

import Contractome.Instances.Element
import Contractome.Instances.SByteArray

open EVM  
open MStd (RBMap mkRBMap)

instance : Zero UInt256 := ⟨ 0 ⟩
instance : One UInt256 := ⟨ 1 ⟩

instance : Zero (RBMap α β τ) := {
  zero := RBMap.empty
}
instance : EVMMapBasic UInt256 Tw (RBMap UInt256 Tw Ord.compare) where
  empty := mkRBMap _ _ _
  get? m addr := m.find? addr
  set m addr val := m.insert addr val

instance [Zero Tw] : EVMMapDefault UInt256 Tw (RBMap UInt256 Tw Ord.compare) where
  empty := mkRBMap _ _ _
  get? m addr := m.find? addr
  set m addr val := m.insert addr val
  get m addr := m.findD addr 0
  
instance : EVMMap UInt256 UInt8 (RBMap UInt256 UInt8 Ord.compare) where
  get32 m addr : UInt256 := Id.run do
    let mut b := ByteArray.empty
    b := b.push $ (m.find? (addr+0)).getD 0
    b := b.push $ (m.find? (addr+1)).getD 0
    b := b.push $ (m.find? (addr+2)).getD 0
    b := b.push $ (m.find? (addr+3)).getD 0
    b := b.push $ (m.find? (addr+4)).getD 0
    b := b.push $ (m.find? (addr+5)).getD 0
    b := b.push $ (m.find? (addr+6)).getD 0
    b := b.push $ (m.find? (addr+7)).getD 0
    b := b.push $ (m.find? (addr+8)).getD 0
    b := b.push $ (m.find? (addr+9)).getD 0
    b := b.push $ (m.find? (addr+10)).getD 0
    b := b.push $ (m.find? (addr+11)).getD 0
    b := b.push $ (m.find? (addr+12)).getD 0
    b := b.push $ (m.find? (addr+13)).getD 0
    b := b.push $ (m.find? (addr+14)).getD 0
    b := b.push $ (m.find? (addr+15)).getD 0
    b := b.push $ (m.find? (addr+16)).getD 0
    b := b.push $ (m.find? (addr+17)).getD 0
    b := b.push $ (m.find? (addr+18)).getD 0
    b := b.push $ (m.find? (addr+19)).getD 0
    b := b.push $ (m.find? (addr+20)).getD 0
    b := b.push $ (m.find? (addr+21)).getD 0
    b := b.push $ (m.find? (addr+22)).getD 0
    b := b.push $ (m.find? (addr+23)).getD 0
    b := b.push $ (m.find? (addr+24)).getD 0
    b := b.push $ (m.find? (addr+25)).getD 0
    b := b.push $ (m.find? (addr+26)).getD 0
    b := b.push $ (m.find? (addr+27)).getD 0
    b := b.push $ (m.find? (addr+28)).getD 0
    b := b.push $ (m.find? (addr+29)).getD 0
    b := b.push $ (m.find? (addr+30)).getD 0
    b := b.push $ (m.find? (addr+31)).getD 0
    UInt256.ofBytes! b
  
  set32 origM addr n := Id.run do
    let mut m := origM
    m := m.insert (addr+0) $ UInt256.toUInt8 $ Element.byte n 0
    m := m.insert (addr+1) $ UInt256.toUInt8 $ Element.byte n 1
    m := m.insert (addr+2) $ UInt256.toUInt8 $ Element.byte n 2
    m := m.insert (addr+3) $ UInt256.toUInt8 $ Element.byte n 3
    m := m.insert (addr+4) $ UInt256.toUInt8 $ Element.byte n 4
    m := m.insert (addr+5) $ UInt256.toUInt8 $ Element.byte n 5
    m := m.insert (addr+6) $ UInt256.toUInt8 $ Element.byte n 6
    m := m.insert (addr+7) $ UInt256.toUInt8 $ Element.byte n 7
    m := m.insert (addr+8) $ UInt256.toUInt8 $ Element.byte n 8
    m := m.insert (addr+9) $ UInt256.toUInt8 $ Element.byte n 9
    m := m.insert (addr+10) $ UInt256.toUInt8 $ Element.byte n 10
    m := m.insert (addr+11) $ UInt256.toUInt8 $ Element.byte n 11
    m := m.insert (addr+12) $ UInt256.toUInt8 $ Element.byte n 12
    m := m.insert (addr+13) $ UInt256.toUInt8 $ Element.byte n 13
    m := m.insert (addr+14) $ UInt256.toUInt8 $ Element.byte n 14
    m := m.insert (addr+15) $ UInt256.toUInt8 $ Element.byte n 15
    m := m.insert (addr+16) $ UInt256.toUInt8 $ Element.byte n 16
    m := m.insert (addr+17) $ UInt256.toUInt8 $ Element.byte n 17
    m := m.insert (addr+18) $ UInt256.toUInt8 $ Element.byte n 18
    m := m.insert (addr+19) $ UInt256.toUInt8 $ Element.byte n 19
    m := m.insert (addr+20) $ UInt256.toUInt8 $ Element.byte n 20
    m := m.insert (addr+21) $ UInt256.toUInt8 $ Element.byte n 21
    m := m.insert (addr+22) $ UInt256.toUInt8 $ Element.byte n 22
    m := m.insert (addr+23) $ UInt256.toUInt8 $ Element.byte n 23
    m := m.insert (addr+24) $ UInt256.toUInt8 $ Element.byte n 24
    m := m.insert (addr+25) $ UInt256.toUInt8 $ Element.byte n 25
    m := m.insert (addr+26) $ UInt256.toUInt8 $ Element.byte n 26
    m := m.insert (addr+27) $ UInt256.toUInt8 $ Element.byte n 27
    m := m.insert (addr+28) $ UInt256.toUInt8 $ Element.byte n 28
    m := m.insert (addr+29) $ UInt256.toUInt8 $ Element.byte n 29
    m := m.insert (addr+30) $ UInt256.toUInt8 $ Element.byte n 30
    m := m.insert (addr+31) $ UInt256.toUInt8 $ Element.byte n 31
    m

  -- TODO not implemented
  maxKey m := 0

  empty_get a := by rfl
  set_get a b c := sorry
  set_diff_get a b c d e:= sorry

instance [SByteArray UInt256 UInt8 ByteArray ByteArray.Iterator]:
  EVMMapSeq UInt256 UInt8 (RBMap UInt256 UInt8 Ord.compare) (BA := ByteArray) (BAI := ByteArray.Iterator) where
  getRange m start length := Id.run do
    let mut r := ByteArray.empty
    let nl := length.toNat
    for (i:Nat) in [0:nl] do
      r := r.push $ (m.find? (start + UInt256.ofNat i)).getD 0
    r

  setRange origM start length content := Id.run do
    let mut m := origM
    let nl := length.toNat
    for (i:Nat) in [0:nl] do
      m := m.insert (start + UInt256.ofNat i) $ content.get! i
    m

instance [SByteArray UInt256 UInt8 (List UInt8) (List UInt8)]:
  EVMMapSeq UInt256 UInt8 (RBMap UInt256 UInt8 Ord.compare) (BA := (List UInt8)) (BAI := (List UInt8)) where
  getRange m start length := Id.run do
    let mut r := List.nil
    let nl := length.toNat
    for (i:Nat) in [0:nl] do
      r := List.cons ((m.find? (start + UInt256.ofNat i)).getD 0) r
    r.reverse

  setRange origM start length content := Id.run do
    let mut m := origM
    let nl := length.toNat
    for (i:Nat) in [0:nl] do
      m := m.insert (start + UInt256.ofNat i) $ content.get! i
    m

deriving instance Repr for Std.Stack
deriving instance BEq for Std.Stack
instance [Inhabited T] : EVMStack T (Std.Stack T) where
  empty := {}
  pop? a := match a.peek? with
  | Option.none => Option.none
  | Option.some s => (s, a.pop)
  peekn? a i := if a.vals.size <= i then Option.none else a.vals.get? (a.vals.size - 1 - i)
  setn? a i v := if a.vals.size <= i then Option.none else Option.some ⟨ a.vals.set ⟨ a.vals.size - 1 - i, sorry ⟩ v ⟩ 
  -- peekn? a i := a.vals.get? (a.vals.size - 1 - i)
  push a v := a.push v
  size a := a.vals.size
  push_pop := sorry

namespace Test
  def x := Std.Stack.mk #[3, 2, 1, 0]
  #assert (EVMStack.peekn? (K:=Nat) x 0) == Option.some 0
  #assert (EVMStack.peekn? (K:=Nat) x 3) == Option.some 3
  #assert (EVMStack.peekn? (K:=Nat) x 4) == Option.none
  #assert (EVMStack.setn? (K:=Nat) x 0 5) == Option.some (Std.Stack.mk #[3, 2, 1, 5])
  #assert (EVMStack.setn? (K:=Nat) x 2 5) == Option.some (Std.Stack.mk #[3, 5, 1, 0])
  #assert (EVMStack.setn? (K:=Nat) x 5 5) == Option.none
end Test