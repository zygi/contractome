import Contractome.Interfaces

open EVM

abbrev ByteArray.extractL (a: ByteArray) (start: Nat) (length: Nat) := 
    a.copySlice start ByteArray.empty 0 length
    
instance [∀ n, OfNat Tw n] [DecidableEq Tw] [Element Tw] : SByteArray Tw UInt8 ByteArray ByteArray.Iterator where
  mkEmpty := ByteArray.empty
  get (a: ByteArray) (i : Tw) := a.get! $ Element.toNat i
  size (a: ByteArray) := Element.ofNat a.size 
  extract (a : ByteArray) (start : Tw) (length : Tw) : ByteArray :=
    ByteArray.extractL a (Element.toNat start) (Element.toNat length)
  extractTw (a : ByteArray) (start : Tw) : Tw :=
    let bytes := ByteArray.extractL a (Element.toNat start) 32
    Element.ofNat $ (UInt256.ofBytes! bytes).val
  -- toConcrete (a : ByteArray) : Option ByteArray := some a
  -- push a v := a.push v
  toIterAt a n := ByteArray.Iterator.mk a $ Element.toNat n
  ofConcrete a := a


instance [∀ n, OfNat Tw n] [DecidableEq Tw] [Element Tw] : SByteArray Tw UInt8 (List UInt8) (List UInt8) where
  mkEmpty := List.nil
  get (a: List UInt8) (i : Tw) := a.get! $ Element.toNat i
  size (a: List UInt8) := Element.ofNat a.length 
  extract (a : List UInt8) (start : Tw) (length : Tw) : List UInt8 :=
    (a.drop (Element.toNat start)).take $ Element.toNat length
  extractTw (a : List UInt8) (start : Tw) : Tw :=
    let bytes := (a.drop (Element.toNat start)).take 32
    Element.ofNat $ (UInt256.ofBytesL! bytes).val
  ofConcrete (a : ByteArray) := a.data.toList
  toIterAt a n := a.drop $ Element.toNat n