import Init.Classical
import AssertCmd
import Bytecode.ByteArrayIterator

namespace EVM

deriving instance Repr for ByteArray
deriving instance DecidableEq for ByteArray

structure PushArg where
  bytes : ByteArray
  -- pf : bytes.size > 0 ∧ bytes.size <= 32

instance : BEq PushArg := { beq := fun a b => a.bytes == b.bytes }

instance : Repr PushArg where
  reprPrec x n := reprPrec x.bytes n

-- instance 

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
deriving Repr, BEq

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
deriving Repr, BEq

inductive InstrMem where
| IPop
| IMload
| IMstore
| IMstore8
| ISload
| ISstore
deriving Repr, BEq

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
deriving Repr, BEq

inductive Instruction where
| expr (i : InstrExpr)
| ctxt (i : InstrCtxt)
| mem (i : InstrMem)
| other (i : InstrOther)
deriving Repr, BEq

#print Coe

instance : Coe InstrExpr Instruction := ⟨Instruction.expr⟩
instance : Coe InstrCtxt Instruction := ⟨Instruction.ctxt⟩
instance : Coe InstrMem Instruction := ⟨Instruction.mem⟩
instance : Coe InstrOther Instruction := ⟨Instruction.other⟩

open InstrExpr
open InstrCtxt
open InstrMem
open InstrOther


private def ofOne (u: UInt8) := ByteArray.mk #[u]

open Instruction
def encode (i: Instruction) : ByteArray := match i with
| Instruction.expr e => match e with
  | InstrExpr.IAdd => ofOne 0x01
  | InstrExpr.IMul => ofOne 0x02
  | InstrExpr.ISub => ofOne 0x03
  | InstrExpr.IDiv => ofOne 0x04
  | InstrExpr.ISdiv => ofOne 0x05
  | InstrExpr.IMod => ofOne 0x06
  | InstrExpr.ISmod => ofOne 0x07
  | InstrExpr.IAddmod => ofOne 0x08
  | InstrExpr.IMulmod => ofOne 0x09
  | InstrExpr.IExp => ofOne 0x0a
  | InstrExpr.ISignextend => ofOne 0x0b
  | InstrExpr.ILt => ofOne 0x10
  | InstrExpr.IGt => ofOne 0x11
  | InstrExpr.ISlt => ofOne 0x12
  | InstrExpr.ISgt => ofOne 0x13
  | InstrExpr.IEq => ofOne 0x14
  | InstrExpr.IIszero => ofOne 0x15
  | InstrExpr.IAnd => ofOne 0x16
  | InstrExpr.IOr => ofOne 0x17
  | InstrExpr.IXor => ofOne 0x18
  | InstrExpr.INot => ofOne 0x19
  | InstrExpr.IByte => ofOne 0x1a
  | InstrExpr.IShl => ofOne 0x1b
  | InstrExpr.IShr => ofOne 0x1c
  | InstrExpr.ISar => ofOne 0x1d
  | InstrExpr.ISha3 => ofOne 0x20
| Instruction.ctxt e => match e with
  | InstrCtxt.IAddress => ofOne 0x30
  | InstrCtxt.IBalance => ofOne 0x31
  | InstrCtxt.IOrigin => ofOne 0x32
  | InstrCtxt.ICaller => ofOne 0x33
  | InstrCtxt.ICallvalue => ofOne 0x34
  | InstrCtxt.ICalldataload => ofOne 0x35
  | InstrCtxt.ICalldatasize => ofOne 0x36
  | InstrCtxt.ICalldatacopy => ofOne 0x37
  | InstrCtxt.ICodesize => ofOne 0x38
  | InstrCtxt.ICodecopy => ofOne 0x39
  | InstrCtxt.IGasprice => ofOne 0x3a
  | InstrCtxt.IExtcodesize => ofOne 0x3b
  | InstrCtxt.IExtcodecopy => ofOne 0x3c
  | InstrCtxt.IReturndatasize => ofOne 0x3d
  | InstrCtxt.IReturndatacopy => ofOne 0x3e
  | InstrCtxt.IExtcodehash => ofOne 0x3f
  | InstrCtxt.IBlockhash => ofOne 0x40
  | InstrCtxt.ICoinbase => ofOne 0x41
  | InstrCtxt.ITimestamp => ofOne 0x42
  | InstrCtxt.INumber => ofOne 0x43
  | InstrCtxt.IDifficulty => ofOne 0x44
  | InstrCtxt.IGaslimit => ofOne 0x45
  | InstrCtxt.IChainid => ofOne 0x46
  | InstrCtxt.ISelfbalance => ofOne 0x47
  | InstrCtxt.IBasefee => ofOne 0x48
| Instruction.mem e => match e with
  | InstrMem.IPop => ofOne 0x50
  | InstrMem.IMload => ofOne 0x51
  | InstrMem.IMstore => ofOne 0x52
  | InstrMem.IMstore8 => ofOne 0x53
  | InstrMem.ISload => ofOne 0x54
  | InstrMem.ISstore => ofOne 0x55
| Instruction.other e => match e with
  | InstrOther.IStop => ofOne 0x00
  | InstrOther.IJump => ofOne 0x56
  | InstrOther.IJumpi => ofOne 0x57
  | InstrOther.IPc => ofOne 0x58
  | InstrOther.IMsize => ofOne 0x59
  | InstrOther.IGas => ofOne 0x5a
  | InstrOther.IJumpdest => ofOne 0x5b
  | InstrOther.IPush arg => (ofOne (0x60 + arg.bytes.size.toUInt8 - 1)) ++ arg.bytes
  | InstrOther.IDup n => ofOne (0x80 + n.val.toUInt8)
  | InstrOther.ISwap n => ofOne (0x90 + n.val.toUInt8)
  | InstrOther.ILog 0 => ofOne 0xa0
  | InstrOther.ILog 1 => ofOne 0xa1
  | InstrOther.ILog 2 => ofOne 0xa2
  | InstrOther.ILog 3 => ofOne 0xa3
  | InstrOther.ILog 4 => ofOne 0xa4
  | InstrOther.ICreate => ofOne 0xf0
  | InstrOther.ICall => ofOne 0xf1
  | InstrOther.ICallcode => ofOne 0xf2
  | InstrOther.IReturn => ofOne 0xf3
  | InstrOther.IDelegatecall => ofOne 0xf4
  | InstrOther.ICreate2 => ofOne 0xf5
  | InstrOther.IStaticcall => ofOne 0xfa
  | InstrOther.IRevert => ofOne 0xfd
  | InstrOther.IInvalid => ofOne 0xfe
  | InstrOther.ISelfdestruct => ofOne 0xff

-- #assert (Instruction.expr InstrExpr.IAdd) == ((Instruction.other InstrOther.IPush { bytes := sorry, pf := sorry }))

-- abbrev Iter := ByteArray.Iterator

class TakeBytes (α : Type u) where
  takeOne (a : α) : Option (UInt8 × α)
  takeN (a : α) (n : Nat) : Option (ByteArray × α)

private def extractn [TakeBytes α] (i : α) (n : Nat): (Option Instruction × Nat) := Id.run do
  let Option.some (c, i) := TakeBytes.takeN i n | return (none, 0)
  let instr := Instruction.other $ InstrOther.IPush { bytes := c}
  (instr, c.size+1)

set_option maxHeartbeats 200000
-- Returns instructions and delta
def decode [TakeBytes α] (i : α) : (Option Instruction × Nat) := Id.run do
  let Option.some (c, i) := TakeBytes.takeOne i | return (none, 0)
  let rest1 := 1
  match c with
  | 0x00 => (some IStop, rest1)
  | 0x01 => (some IAdd, rest1)
  | 0x02 => (some IMul, rest1)
  | 0x03 => (some ISub, rest1)
  | 0x04 => (some IDiv, rest1)
  | 0x05 => (some ISdiv, rest1)
  | 0x06 => (some IMod, rest1)
  | 0x07 => (some ISmod, rest1)
  | 0x08 => (some IAddmod, rest1)
  | 0x09 => (some IMulmod, rest1)
  | 0x0a => (some IExp, rest1)
  | 0x0b => (some ISignextend, rest1)

  | 0x10 => (some ILt, rest1)
  | 0x11 => (some IGt, rest1)
  | 0x12 => (some ISlt, rest1)
  | 0x13 => (some ISgt, rest1)
  | 0x14 => (some IEq, rest1)
  | 0x15 => (some IIszero, rest1)
  | 0x16 => (some IAnd, rest1)
  | 0x17 => (some IOr, rest1)
  | 0x18 => (some IXor, rest1)
  | 0x19 => (some INot, rest1)
  | 0x1a => (some IByte, rest1)
  | 0x1b => (some IShl, rest1)
  | 0x1c => (some IShr, rest1)
  | 0x1d => (some ISar, rest1)

  | 0x20 => (some ISha3, rest1)

  | 0x30 => (some IAddress, rest1)
  | 0x31 => (some IBalance, rest1)
  | 0x32 => (some IOrigin, rest1)
  | 0x33 => (some ICaller, rest1)
  | 0x34 => (some ICallvalue, rest1)
  | 0x35 => (some ICalldataload, rest1)
  | 0x36 => (some ICalldatasize, rest1)
  | 0x37 => (some ICalldatacopy, rest1)
  | 0x38 => (some ICodesize, rest1)
  | 0x39 => (some ICodecopy, rest1)
  | 0x3a => (some IGasprice, rest1)
  | 0x3b => (some IExtcodesize, rest1)
  | 0x3c => (some IExtcodecopy, rest1)
  | 0x3d => (some IReturndatasize, rest1)
  | 0x3e => (some IReturndatacopy, rest1)
  | 0x3f => (some IExtcodehash, rest1)

  | 0x40 => (some IBlockhash, rest1)
  | 0x41 => (some ICoinbase, rest1)
  | 0x42 => (some ITimestamp, rest1)
  | 0x43 => (some INumber, rest1)
  | 0x44 => (some IDifficulty, rest1)
  | 0x45 => (some IGaslimit, rest1)
  | 0x46 => (some IChainid, rest1)
  | 0x47 => (some ISelfbalance, rest1)
  | 0x48 => (some IBasefee, rest1)

  | 0x50 => (some IPop, rest1)
  | 0x51 => (some IMload, rest1)
  | 0x52 => (some IMstore, rest1)
  | 0x53 => (some IMstore8, rest1)
  | 0x54 => (some ISload, rest1)
  | 0x55 => (some ISstore, rest1)
  | 0x56 => (some IJump, rest1)
  | 0x57 => (some IJumpi, rest1)
  | 0x58 => (some IPc, rest1)
  | 0x59 => (some IMsize, rest1)
  | 0x5a => (some IGas, rest1)
  | 0x5b => (some IJumpdest, rest1)

  | 0x60 => extractn i 1
  | 0x61 => extractn i 2
  | 0x62 => extractn i 3
  | 0x63 => extractn i 4
  | 0x64 => extractn i 5
  | 0x65 => extractn i 6
  | 0x66 => extractn i 7
  | 0x67 => extractn i 8
  | 0x68 => extractn i 9
  | 0x69 => extractn i 10
  | 0x6a => extractn i 11
  | 0x6b => extractn i 12
  | 0x6c => extractn i 13
  | 0x6d => extractn i 14
  | 0x6e => extractn i 15
  | 0x6f => extractn i 16
  | 0x70 => extractn i 17
  | 0x71 => extractn i 18
  | 0x72 => extractn i 19
  | 0x73 => extractn i 20
  | 0x74 => extractn i 21
  | 0x75 => extractn i 22
  | 0x76 => extractn i 23
  | 0x77 => extractn i 24
  | 0x78 => extractn i 25
  | 0x79 => extractn i 26
  | 0x7a => extractn i 27
  | 0x7b => extractn i 28
  | 0x7c => extractn i 29
  | 0x7d => extractn i 30
  | 0x7e => extractn i 31
  | 0x7f => extractn i 32

  | 0x80 => (some $ IDup 0, rest1)
  | 0x81 => (some $ IDup 1, rest1)
  | 0x82 => (some $ IDup 2, rest1)
  | 0x83 => (some $ IDup 3, rest1)
  | 0x84 => (some $ IDup 4, rest1)
  | 0x85 => (some $ IDup 5, rest1)
  | 0x86 => (some $ IDup 6, rest1)
  | 0x87 => (some $ IDup 7, rest1)
  | 0x88 => (some $ IDup 8, rest1)
  | 0x89 => (some $ IDup 9, rest1)
  | 0x8a => (some $ IDup 10, rest1)
  | 0x8b => (some $ IDup 11, rest1)
  | 0x8c => (some $ IDup 12, rest1)
  | 0x8d => (some $ IDup 13, rest1)
  | 0x8e => (some $ IDup 14, rest1)
  | 0x8f => (some $ IDup 15, rest1)

  | 0x90 => (some $ ISwap 0, rest1)
  | 0x91 => (some $ ISwap 1, rest1)
  | 0x92 => (some $ ISwap 2, rest1)
  | 0x93 => (some $ ISwap 3, rest1)
  | 0x94 => (some $ ISwap 4, rest1)
  | 0x95 => (some $ ISwap 5, rest1)
  | 0x96 => (some $ ISwap 6, rest1)
  | 0x97 => (some $ ISwap 7, rest1)
  | 0x98 => (some $ ISwap 8, rest1)
  | 0x99 => (some $ ISwap 9, rest1)
  | 0x9a => (some $ ISwap 10, rest1)
  | 0x9b => (some $ ISwap 11, rest1)
  | 0x9c => (some $ ISwap 12, rest1)
  | 0x9d => (some $ ISwap 13, rest1)
  | 0x9e => (some $ ISwap 14, rest1)
  | 0x9f => (some $ ISwap 15, rest1)

  | 0xa0 => (some $ ILog 0, rest1)
  | 0xa1 => (some $ ILog 1, rest1)
  | 0xa2 => (some $ ILog 2, rest1)
  | 0xa3 => (some $ ILog 3, rest1)
  | 0xa4 => (some $ ILog 4, rest1)

  | 0xf0 => (some ICreate, rest1)
  | 0xf1 => (some ICall, rest1)
  | 0xf2 => (some ICallcode, rest1)
  | 0xf3 => (some IReturn, rest1)
  | 0xf4 => (some IDelegatecall, rest1)
  | 0xf5 => (some ICreate2, rest1)
  | 0xfa => (some IStaticcall, rest1)
  | 0xfd => (some IRevert, rest1)
  | 0xfe => (some IInvalid, rest1)
  | 0xff => (some ISelfdestruct, rest1)

  | _ => (none, 0)

instance : TakeBytes ByteArray.Iterator where
  takeOne i := if i.hasCurr then some (i.curr, i.next) else none
  takeN i n := if i.hasCurrN n then some (i.currn n, i.nextn n) else none

instance : TakeBytes (List UInt8) where
  takeOne i := match i with | List.cons l ls => (l, ls) | List.nil => none
  takeN i n := 
    let t := i.take n
    if t.length < n then none else (ByteArray.mk t.toArray, i.drop n)

namespace Test
  #assert (encode (IPush { bytes := ByteArray.mk #[0x01, 0x02, 0x02] } )).data == (ByteArray.mk #[0x62, 0x01, 0x02, 0x02]).data
  def i := ByteArray.Iterator.mk (ByteArray.mk #[0x62, 0x01, 0x02, 0x02]) 0  
  #assert (TakeBytes.takeOne i) == (Option.some ((0x62:UInt8), i.next))
  #assert (TakeBytes.takeN i 3) == (Option.some (ByteArray.mk #[0x62, 0x01, 0x02], i.nextn 3))
  #assert (TakeBytes.takeN i 4) == (Option.some (ByteArray.mk #[0x62, 0x01, 0x02, 0x02], i.nextn 4))
  #assert (decode i) == (Option.some (Instruction.other $ IPush { bytes := ByteArray.mk #[0x01, 0x02, 0x02] }), 4)

  def j : List UInt8 := [0x62, 0x01, 0x02, 0x02]
  #assert (TakeBytes.takeOne j) == (Option.some ((0x62:UInt8), j.drop 1))
  #assert (TakeBytes.takeN j 3) == (Option.some (ByteArray.mk #[0x62, 0x01, 0x02], j.drop 3))
  #assert (TakeBytes.takeN j 4) == (Option.some (ByteArray.mk #[0x62, 0x01, 0x02, 0x02], j.drop 4))
  #assert (decode j) == (Option.some (Instruction.other $ IPush { bytes := ByteArray.mk #[0x01, 0x02, 0x02] }), 4)
end Test


-- #eval String.Iterator