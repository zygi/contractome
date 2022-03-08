import Contractome.Interfaces

open EVM

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
  byte := fun x i => (x <<< (i*8)) >>> (256 - 8)
  sar := UInt256.sar
  -- toNat : T -> Nat
  ofNat := UInt256.ofNat
  toNat := UInt256.toNat

namespace Test
  open Element
  #assert (byte (T:=UInt256) 0 0) == (0:UInt256)
  #assert (byte (T:=UInt256) 0 0) == (0:UInt256)
  #assert (byte (T:=UInt256) 0xff 31) == (0xff:UInt256)
end Test

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
  byte := fun x i => (x <<< (i*8)) >>> (256 - 8)
  sar := lift2To256 UInt256.sar
  -- toNat : T -> Nat
  ofNat := UInt8.ofNat
  toNat := UInt8.toNat
