import Contractome.UInt256

class ABIEncodable (T: Type u) where
  abiLength (t: T) : Nat
  abiEncode (t: T) : ByteArray

class ABIDecodable (T: Type u) where
  abiDecode (b: ByteArray) : T

instance : ABIEncodable UInt256 where
  abiLength _ := 32
  abiEncode x := x.toBytes

instance : ABIEncodable Bool where
  abiLength _ := 32
  abiEncode x := (if x then (1:UInt256) else 0).toBytes

instance : ABIEncodable Nat where
  abiLength _ := 32
  abiEncode x := (UInt256.ofNat x).toBytes

-- instance [ABIEncodable x] : ABIEncodable (Array x) where
--   abiLength 

