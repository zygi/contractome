import Contractome.Interfaces
import Contractome.UInt256
import Std.Data.RBMap
import Std.Data.Stack

open EVM  
open Std (RBMap)

instance : Zero UInt256 := ⟨ 0 ⟩
instance : One UInt256 := ⟨ 1 ⟩

instance : Element UInt256 where
  add := UInt256.add
  mul := UInt256.mul
  sub := UInt256.sub
  div := UInt256.div
  sdiv := UInt256.sdiv
  mod := UInt256.mod
  smod := UInt256.smod
  addmod := fun a b N => (a + b) % N
  mulmod := fun a b N => (a * b) % N
  exp := UInt256.pow
  signextend := UInt256.signextend
  ltb := fun a b => match Ord.compare a b with | Ordering.lt => true | _ => false  
  gtb := fun a b => match Ord.compare a b with | Ordering.gt => true | _ => false  
  eq := fun a b => decide (a = b)
  iszero := fun a => decide (a = 0)
  sltb := UInt256.slt
  sgtb := UInt256.sgt
  byte := fun i x => (x <<< (i*8)) >>> (256 - 8)
  sar := UInt256.sar
  -- toNat : T -> Nat
  ofNat := UInt256.ofNat
  toNat := UInt256.toNat

abbrev lift2To256 (fn : UInt256 -> UInt256 -> UInt256) (a b : UInt8):= UInt256.toUInt8 $ fn (UInt256.ofUInt8 a) (UInt256.ofUInt8 b)
abbrev lift2To256' (fn : UInt256 -> UInt256 -> T) (a b : UInt8):= fn (UInt256.ofUInt8 a) (UInt256.ofUInt8 b)

instance : Element UInt8 where
  add := UInt8.add
  mul := UInt8.mul
  sub := UInt8.sub
  div := UInt8.div
  sdiv := lift2To256 UInt256.sdiv
  mod := UInt8.mod
  smod := lift2To256 UInt256.smod
  addmod := fun a b N => (a + b) % N
  mulmod := fun a b N => (a * b) % N
  exp := lift2To256 UInt256.pow
  signextend := sorry
  ltb := fun a b => match Ord.compare a b with | Ordering.lt => true | _ => false  
  gtb := fun a b => match Ord.compare a b with | Ordering.gt => true | _ => false  
  eq := fun a b => decide (a = b)
  iszero := fun a => decide (a = 0)
  sltb := lift2To256' UInt256.slt
  sgtb := lift2To256' UInt256.sgt
  byte := fun i x => (x <<< (i*8)) >>> (256 - 8)
  sar := lift2To256 UInt256.sar
  -- toNat : T -> Nat
  ofNat := UInt8.ofNat
  toNat := UInt8.toNat

abbrev ByteArray.extractL (a: ByteArray) (start: Nat) (length: Nat) := 
    a.copySlice start ByteArray.empty 0 length

instance [∀ n, OfNat Tw n] [DecidableEq Tw] [Element Tw] : SByteArray Tw UInt8 ByteArray where
  mkEmpty := ByteArray.empty
  get (a: ByteArray) (i : Tw) := a.get! $ Element.toNat i
  size (a: ByteArray) := Element.ofNat a.size 
  extract (a : ByteArray) (start : Tw) (length : Tw) : ByteArray :=
    ByteArray.extractL a (Element.toNat start) (Element.toNat length)
  extractTw (a : ByteArray) (start : Tw) : Tw :=
    let bytes := ByteArray.extractL a (Element.toNat start) 32
    Element.ofNat $ (UInt256.ofBytes! bytes).val
  toConcrete (a : ByteArray) : Option ByteArray := some a

instance : EVMMapDefault UInt256 UInt8 (Std.RBMap UInt256 UInt8 Ord.compare) where
  empty := Std.mkRBMap _ _ _
  get? m addr := m.find? addr
  set m addr val := m.insert addr val
  get m addr := m.findD addr 0
  
instance : EVMMapDefault UInt256 UInt256 (Std.RBMap UInt256 UInt256 Ord.compare) where
  empty := Std.mkRBMap _ _ _
  get? m addr := m.find? addr
  set m addr val := m.insert addr val
  get m addr := m.findD addr 0

instance : EVMMap UInt256 UInt8 (Std.RBMap UInt256 UInt8 Ord.compare) where
  get32 m addr : UInt256 := Id.run do
    let mut b := ByteArray.empty
    b := b.push $ m.find! $ addr+0
    b := b.push $ m.find! $ addr+1
    b := b.push $ m.find! $ addr+2
    b := b.push $ m.find! $ addr+3
    b := b.push $ m.find! $ addr+4
    b := b.push $ m.find! $ addr+5
    b := b.push $ m.find! $ addr+6
    b := b.push $ m.find! $ addr+7
    b := b.push $ m.find! $ addr+8
    b := b.push $ m.find! $ addr+9
    b := b.push $ m.find! $ addr+10
    b := b.push $ m.find! $ addr+11
    b := b.push $ m.find! $ addr+12
    b := b.push $ m.find! $ addr+13
    b := b.push $ m.find! $ addr+14
    b := b.push $ m.find! $ addr+15
    b := b.push $ m.find! $ addr+16
    b := b.push $ m.find! $ addr+17
    b := b.push $ m.find! $ addr+18
    b := b.push $ m.find! $ addr+19
    b := b.push $ m.find! $ addr+20
    b := b.push $ m.find! $ addr+21
    b := b.push $ m.find! $ addr+22
    b := b.push $ m.find! $ addr+23
    b := b.push $ m.find! $ addr+24
    b := b.push $ m.find! $ addr+25
    b := b.push $ m.find! $ addr+26
    b := b.push $ m.find! $ addr+27
    b := b.push $ m.find! $ addr+28
    b := b.push $ m.find! $ addr+29
    b := b.push $ m.find! $ addr+30
    b := b.push $ m.find! $ addr+31
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

instance : EVMMapSeq UInt256 UInt8 (Std.RBMap UInt256 UInt8 Ord.compare) (BA := ByteArray) where
  getRange m start length := Id.run do
    let mut r := ByteArray.empty
    let nl := length.toNat
    for (i:Nat) in [0:nl] do
      r := r.push $ m.find! (start + UInt256.ofNat i)
    r

  setRange origM start length content := Id.run do
    let mut m := origM
    let nl := length.toNat
    for (i:Nat) in [0:nl] do
      m := m.insert (start + UInt256.ofNat i) (content.get! i)
    m


deriving instance Repr for Std.Stack
instance : EVMStack UInt256 (Std.Stack UInt256) where
  empty := {}
  pop? a := match a.peek? with
  | Option.none => Option.none
  | Option.some s => (s, a.pop)
  peekn? a i := a.vals.get? (a.vals.size - 1 - i)
  setn? a i v := if a.vals.size <= i then Option.none else Option.some ⟨ a.vals.set ⟨ a.vals.size - 1 - i, sorry ⟩ v ⟩ 
  -- peekn? a i := a.vals.get? (a.vals.size - 1 - i)
  push a v := a.push v
  size a := a.vals.size