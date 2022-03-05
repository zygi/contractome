
structure PushArg where
  bytes : ByteArray
  pf : bytes.size > 0 ∧ bytes.size <= 32

deriving instance Repr for ByteArray

instance : Repr PushArg where
  reprPrec x n := reprPrec x.bytes n

inductive InstrExpr where
| IAdd
| IMul
| ISub
| IDiv
| ISdiv
| IMod
| ISmod
| IAddmod
| IMulmod
| IExp
| ISignextend
| ILt
| IGt
| ISlt
| ISgt
| IEq
| IIszero
| IAnd
| IOr
| IXor
| INot
| IByte
| IShl
| IShr
| ISar
| ISha3

inductive InstrCtxt where
| IAddress
| IBalance
| IOrigin
| ICaller
| ICallvalue
| ICalldataload
| ICalldatasize
| ICalldatacopy
| ICodesize
| ICodecopy
| IGasprice
| IExtcodesize
| IExtcodecopy
| IReturndatasize
| IReturndatacopy
| IExtcodehash
| IBlockhash
| ICoinbase
| ITimestamp
| INumber
| IDifficulty
| IGaslimit
| IChainid
| ISelfbalance
| IBasefee

inductive InstrMem where
| IPop
| IMload
| IMstore
| IMstore8
| ISload
| ISstore

inductive InstrOther where
| IStop
| IJump
| IJumpi
| IPc
| IMsize
| IGas
| IJumpdest
| IPush (arg: PushArg)
| IDup (idx: Fin 16)
| ISwap (idx: Fin 16)
| ILog (idx: Fin 5)
| ICreate
| ICall
| ICallcode
| IReturn
| IDelegatecall
| ICreate2
| IStaticcall
| IRevert
| IInvalid
| ISelfdestruct

inductive Instruction where
| expr (i : InstrExpr)
| ctxt (i : InstrCtxt)
| mem (i : InstrMem)
| other (i : InstrOther)