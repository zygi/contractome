import Contractome.Interfaces
import Contractome.Instances
import Contractome.EVM
import Contractome.UInt256
import Std.Data.Stack
import Std.Data.RBMap
import Contractome.Utils

import Contractome.ABIEncoding

open EVM

def C : Cfg := {
  S := Std.Stack UInt256
  BA := ByteArray
  BAI := ByteArray.Iterator

  M := Std.RBMap UInt256 UInt8 Ord.compare
  AM := Std.RBMap UInt256 UInt256 Ord.compare
  BAM := Std.RBMap UInt256 ByteArray Ord.compare
  STM := Std.RBMap UInt256 (Std.RBMap UInt256 UInt8 Ord.compare) Ord.compare
  RS := Std.Stack (UInt256 × ByteArray)
  Tw := UInt256
  Tb := UInt8
}

deriving instance Repr for Std.Stack

-- instance : Repr ByteArray := ⟨ fun a _ => byteArrayToHex a ⟩ 

-- #eval UInt64

instance : Repr C.Tw := (inferInstance : Repr UInt256)
instance : Repr C.Tb := (inferInstance : Repr UInt8)
instance : Repr C.M := (inferInstance : Repr (Std.RBMap UInt256 UInt8 Ord.compare))
instance : Repr C.S := (inferInstance : Repr (Std.Stack UInt256))
instance : Repr C.BA := (inferInstance : Repr (ByteArray))
instance : Repr C.AM := (inferInstance : Repr (Std.RBMap UInt256 UInt256 Ord.compare))
instance : Repr C.BAM := (inferInstance : Repr (Std.RBMap UInt256 ByteArray Ord.compare))
instance : Repr C.STM := (inferInstance : Repr (Std.RBMap UInt256 (Std.RBMap UInt256 UInt8 Ord.compare) Ord.compare))
instance : Repr C.RS := (inferInstance : Repr (Std.Stack (UInt256 × ByteArray)))
-- deriving instance Repr for TransactionContext

instance : DecidableEq C.Tw := (inferInstance : DecidableEq UInt256)
instance : ∀ n, OfNat C.Tw n := (inferInstance : ∀ n, OfNat UInt256 n)
instance : Element C.Tw := (inferInstance : Element UInt256)

instance : DecidableEq C.Tb := (inferInstance : DecidableEq UInt8)
instance : ∀ n, OfNat C.Tb n := (inferInstance : ∀ n, OfNat UInt8 n)
instance : Element C.Tb := (inferInstance : Element UInt8)
instance : TakeBytes C.BAI := (inferInstance : TakeBytes ByteArray.Iterator)
instance : SByteArray C.Tw C.Tb C.BA C.BAI := (inferInstance : SByteArray UInt256 UInt8 ByteArray ByteArray.Iterator)

instance : Zero C.M := (inferInstance : Zero (Std.RBMap UInt256 UInt8 Ord.compare))
instance : EVMStack C.Tw C.S := (inferInstance : EVMStack UInt256 (Std.Stack UInt256))
instance : EVMStack (C.Tw × C.BA) C.RS := (inferInstance : EVMStack (UInt256 × ByteArray) (Std.Stack (UInt256 × ByteArray)))
instance : EVMMapDefault C.Tw C.Tw C.AM := (inferInstance : EVMMapDefault UInt256 UInt256 (Std.RBMap UInt256 UInt256 Ord.compare))
instance : EVMMapDefault C.Tw C.M C.STM := (inferInstance : EVMMapDefault UInt256 (Std.RBMap UInt256 UInt8 Ord.compare) (Std.RBMap UInt256 (Std.RBMap UInt256 UInt8 Ord.compare) Ord.compare))
instance : EVMMapBasic C.Tw C.BA C.BAM := (inferInstance : EVMMapBasic UInt256 ByteArray (Std.RBMap UInt256 ByteArray Ord.compare))

instance : EVMMapSeq C.Tw C.Tb C.M (BA := C.BA) (BAI := C.BAI) :=
  (inferInstance : EVMMapSeq UInt256 UInt8 ByteArray ByteArray.Iterator (Std.RBMap UInt256 UInt8 Ord.compare))

-- variable [EVMStack C.Tw C.S] [EVMMap C.Tw C.Tw C.AM] [EVMMapSeq C.Tw C.Tb C.M (instBA := instBA)]
-- variable [EVMMapBasic C.Tw C.BA C.BAM]

#assert (hexToByteArray! "604260005260206000F3") == (hexToByteArray!' "604260005260206000F3")

def basicInput := hexToByteArray!' "604260005260206000F3"


def emptySolcInput := hexToByteArray! "6080604052348015600f57600080fd5b50603f80601d6000396000f3fe6080604052600080fdfea2646970667358221220c852edbace7e3c9da7b9e566199d4b7f89d6c7c9e5d1029f0337839e993fa6fa64736f6c63430008070033"

def basicSolcInput := hexToByteArray! "6080604052348015600f57600080fd5b5060405160e338038060e38339818101604052810190602d9190604c565b80600081905550506097565b6000815190506046816083565b92915050565b600060208284031215605f57605e607e565b5b6000606b848285016039565b91505092915050565b6000819050919050565b600080fd5b608a816074565b8114609457600080fd5b50565b603f8060a46000396000f3fe6080604052600080fdfea26469706673582212209c130309b4505633bae9459145bea0f6138a99c38947f11384f39beca020bc9a64736f6c63430008070033"
def basicSolcInputWithArg := basicSolcInput ++ ABIEncodable.abiEncode 123

-- #eval basicSolcInput

#eval basicSolcInput.size

def initTC (bytecode : ByteArray) : TransactionContext (C:=C) := {
  address := 0
  origin := 0
  caller := 0
  callvalue := 0
  balances := Std.rbmapOf [ (0, 5) ] _
  calldata := ByteArray.empty
  returnData := Std.Stack.empty
  codes := Std.rbmapOf [ (0, bytecode) ] _
}

def initCC : ChainContext (C:=C) := {
  gasprice := 0
  blockhash := 0
  coinbase := 0
  timestamp := 0
  number := 0
  difficulty := 0
  gaslimit := 0
  chainid := 0
  basefee := 0
}

abbrev runEvm (v: EVMM (C:=C) α) (txCtx : TransactionContext (C:=C)) (chCtx : ChainContext (C:=C)) := EVMM.run' (C:=C) v txCtx chCtx

-- #eval EVM.decode basicInput
-- #eval basicInput
#eval EVM.decode ⟨ hexToByteArray! "604260005260206000F3", 123 ⟩ 

-- #eval 0x103

def stepN (n : Nat) : EVMM (C:=C) Unit := match n with
| 0 => pure ()
| n+1 => do
  if (← EVMM.isDone) then pure () else 
  EVMM.step; stepN n

#eval UInt256.ofBytes! $ hexToByteArray! "42"
-- #eval runEvm (EVMM.getNextInstr) initTC initCC

-- #eval 0x2d

#eval 0x7b

-- TODO note: not work


-- def hexToByteArray'(s: String): Option ByteArray := Id.run do
--   if s.length % 2 != 0 then return none
--   let mut res := ByteArray.mkEmpty $ s.length / 2
--   for i in [:((s.length)/2)] do
--     let v1 := hexChar (s[2*i])
--     let v2 := hexChar (s[2*i+1])
--     match (v1, v2) with 
--     | (some v1, some v2) => res := res.push $ ⟨ (16 * v1) + v2, sorry ⟩ 
--     | _ => return none
--   return res
-- set_option pp.all true

-- def codeInlined : ByteArray := {}

local instance : OfNat UInt8 n where
  -- ofNat := fofNat n
  ofNat := ⟨ n % 256, sorry ⟩

-- #reduce basicInput
set_option maxRecDepth 2000
-- #reduce initTC basicInput


-- set_option maxRecDepth 10000
-- #redComp (1 : UInt256)

-- set_option maxRecDepth 10000
-- #reduce codeInlined

-- local instance : OfNat UInt8 n where
--   ofNat := ⟨n % 256, sorry⟩

set_option maxHeartbeats 500000
-- #redComp emptySolcInput

-- #reduce initTC emptySolcInput

constant a : UInt8

-- #eval b[1, 2]

-- #reduce initTC b[a]

-- theorem test1 (tC : TransactionContext) (cC : ChainContext) := 

#reduce runEvm (EVMM.getNextInstr) (initTC basicInput) initCC
-- #eval runEvm (stepN 116) (initTC basicSolcInputWithArg) initCC