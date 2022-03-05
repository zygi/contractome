import Contractome.Interfaces
import Contractome.Instances
import Contractome.EVM
import Contractome.UInt256
import Std.Data.Stack
import Std.Data.RBMap

open EVM

def C : Cfg := {
  S := Std.Stack UInt256
  BA := ByteArray
  M := Std.RBMap UInt256 UInt8 Ord.compare
  AM := Std.RBMap UInt256 UInt256 Ord.compare
  BAM := Std.RBMap UInt256 ByteArray Ord.compare

  Tw := UInt256
  Tb := UInt8
}

instance : DecidableEq C.Tw := (inferInstance : DecidableEq UInt256)
instance : ∀ n, OfNat C.Tw n := (inferInstance : ∀ n, OfNat UInt256 n)
instance : Element C.Tw := (inferInstance : Element UInt256)

instance : DecidableEq C.Tb := (inferInstance : DecidableEq UInt8)
instance : ∀ n, OfNat C.Tb n := (inferInstance : ∀ n, OfNat UInt8 n)
instance : Element C.Tb := (inferInstance : Element UInt8)

instance : SByteArray C.Tw C.Tb C.BA := (inferInstance : SByteArray UInt256 UInt8 ByteArray)

instance : EVMStack C.Tw C.S := (inferInstance : EVMStack UInt256 (Std.Stack UInt256))
instance : EVMMapDefault C.Tw C.Tw C.AM := (inferInstance : EVMMapDefault UInt256 UInt256 (Std.RBMap UInt256 UInt256 Ord.compare))

instance : EVMMapSeq C.Tw C.Tb C.M (BA := C.BA) := (inferInstance : EVMMapSeq UInt256 UInt8 (Std.RBMap UInt256 UInt8 Ord.compare) (BA := ByteArray))

-- variable [EVMStack C.Tw C.S] [EVMMap C.Tw C.Tw C.AM] [EVMMapSeq C.Tw C.Tb C.M (instBA := instBA)]
-- variable [EVMMapBasic C.Tw C.BA C.BAM]

abbrev runEvm (v: @EVMM C α) (txCtx : TransactionContext) (chCtx : ChainContext) := EVMM.run (C:=C) v txCtx chCtx