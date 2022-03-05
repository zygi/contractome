import Init.Classical

namespace EVM

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
deriving Repr

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
deriving Repr

inductive InstrMem where
| IPop
| IMload
| IMstore
| IMstore8
| ISload
| ISstore
deriving Repr

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
deriving Repr

inductive Instruction where
| expr (i : InstrExpr)
| ctxt (i : InstrCtxt)
| mem (i : InstrMem)
| other (i : InstrOther)
deriving Repr

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
  | InstrOther.IPush arg => (ofOne (0x60 + arg.bytes.size.toUInt8)) ++ arg.bytes
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

private def get? (b: ByteArray) (i: Nat) : Option UInt8 := dite (i < b.size) (fun p => b.get ⟨ i, p ⟩ ) (fun _ => none)


@[simp] private theorem Array.ofToSubarray (a: Array α) : Array.ofSubarray a.toSubarray = a := sorry


@[simp] private theorem extractSize (b: ByteArray) (n: Nat) (h: b.size >= n) a : (b.extract a n).size = n - a := by
  admit

@[simp] private theorem pff (b: ByteArray) n (h1: n <= 32) (h3: b.size >= n): (b.extract 1 n).size > 0 ∧ (b.extract 1 n).size <= 32 := by
  -- rw [extractSize b n h3 1]
  -- simp
  admit


private def btailn (b: ByteArray) n := b.extract n b.size

-- #eval btailn (ByteArray.mk #[0x00, 0x01]) 1 

private def taken? (b: ByteArray) n (h: n <= 32) : Option Instruction × ByteArray :=
  dite (b.size >= n)
    (fun pf => (Instruction.other $ InstrOther.IPush { bytes := b.extract 1 n, pf := pff b n h pf}, btailn b n ))
    (fun _ => (none, b)) 

private theorem t0lt32 : 0 <= 32 := by simp
private theorem t1lt32 : 1 <= 32 := by simp
private theorem t2lt32 : 2 <= 32 := by simp
private theorem t3lt32 : 3 <= 32 := by simp
private theorem t4lt32 : 4 <= 32 := by simp
private theorem t5lt32 : 5 <= 32 := by simp
private theorem t6lt32 : 6 <= 32 := by simp
private theorem t7lt32 : 7 <= 32 := by simp
private theorem t8lt32 : 8 <= 32 := by simp
private theorem t9lt32 : 9 <= 32 := by simp
private theorem t10lt32 : 10 <= 32 := by simp
private theorem t11lt32 : 11 <= 32 := by simp
private theorem t12lt32 : 12 <= 32 := by simp
private theorem t13lt32 : 13 <= 32 := by simp
private theorem t14lt32 : 14 <= 32 := by simp
private theorem t15lt32 : 15 <= 32 := by simp
private theorem t16lt32 : 16 <= 32 := by simp
private theorem t17lt32 : 17 <= 32 := by simp
private theorem t18lt32 : 18 <= 32 := by simp
private theorem t19lt32 : 19 <= 32 := by simp
private theorem t20lt32 : 20 <= 32 := by simp
private theorem t21lt32 : 21 <= 32 := by simp
private theorem t22lt32 : 22 <= 32 := by simp
private theorem t23lt32 : 23 <= 32 := by simp
private theorem t24lt32 : 24 <= 32 := by simp
private theorem t25lt32 : 25 <= 32 := by simp
private theorem t26lt32 : 26 <= 32 := by simp
private theorem t27lt32 : 27 <= 32 := by simp
private theorem t28lt32 : 28 <= 32 := by simp
private theorem t29lt32 : 29 <= 32 := by simp
private theorem t30lt32 : 30 <= 32 := by simp
private theorem t31lt32 : 31 <= 32 := by simp
private theorem t32lt32 : 32 <= 32 := by simp


set_option maxHeartbeats 200000
def decode (b: ByteArray) : Option Instruction × ByteArray :=
  let btail := btailn b 1
  match get? b 0 with
  | none => (none, b)
  | some v => match v.val.val with
    | 0x00 => (some IStop, btail)
    | 0x01 => (some IAdd, btail)
    | 0x02 => (some IMul, btail)
    | 0x03 => (some ISub, btail)
    | 0x04 => (some IDiv, btail)
    | 0x05 => (some ISdiv, btail)
    | 0x06 => (some IMod, btail)
    | 0x07 => (some ISmod, btail)
    | 0x08 => (some IAddmod, btail)
    | 0x09 => (some IMulmod, btail)
    | 0x0a => (some IExp, btail)
    | 0x0b => (some ISignextend, btail)

    | 0x10 => (some ILt, btail)
    | 0x11 => (some IGt, btail)
    | 0x12 => (some ISlt, btail)
    | 0x13 => (some ISgt, btail)
    | 0x14 => (some IEq, btail)
    | 0x15 => (some IIszero, btail)
    | 0x16 => (some IAnd, btail)
    | 0x17 => (some IOr, btail)
    | 0x18 => (some IXor, btail)
    | 0x19 => (some INot, btail)
    | 0x1a => (some IByte, btail)
    | 0x1b => (some IShl, btail)
    | 0x1c => (some IShr, btail)
    | 0x1d => (some ISar, btail)

    | 0x20 => (some ISha3, btail)

    | 0x30 => (some IAddress, btail)
    | 0x31 => (some IBalance, btail)
    | 0x32 => (some IOrigin, btail)
    | 0x33 => (some ICaller, btail)
    | 0x34 => (some ICallvalue, btail)
    | 0x35 => (some ICalldataload, btail)
    | 0x36 => (some ICalldatasize, btail)
    | 0x37 => (some ICalldatacopy, btail)
    | 0x38 => (some ICodesize, btail)
    | 0x39 => (some ICodecopy, btail)
    | 0x3a => (some IGasprice, btail)
    | 0x3b => (some IExtcodesize, btail)
    | 0x3c => (some IExtcodecopy, btail)
    | 0x3d => (some IReturndatasize, btail)
    | 0x3e => (some IReturndatacopy, btail)
    | 0x3f => (some IExtcodehash, btail)

    | 0x40 => (some IBlockhash, btail)
    | 0x41 => (some ICoinbase, btail)
    | 0x42 => (some ITimestamp, btail)
    | 0x43 => (some INumber, btail)
    | 0x44 => (some IDifficulty, btail)
    | 0x45 => (some IGaslimit, btail)
    | 0x46 => (some IChainid, btail)
    | 0x47 => (some ISelfbalance, btail)
    | 0x48 => (some IBasefee, btail)

    | 0x50 => (some IPop, btail)
    | 0x51 => (some IMload, btail)
    | 0x52 => (some IMstore, btail)
    | 0x53 => (some IMstore8, btail)
    | 0x54 => (some ISload, btail)
    | 0x55 => (some ISstore, btail)
    | 0x56 => (some IJump, btail)
    | 0x57 => (some IJumpi, btail)
    | 0x58 => (some IPc, btail)
    | 0x59 => (some IMsize, btail)
    | 0x5a => (some IGas, btail)
    | 0x5b => (some IJumpdest, btail)

    | 0x60 => taken? b 1 t1lt32
    | 0x61 => taken? b 2 t2lt32
    | 0x62 => taken? b 3 t3lt32
    | 0x63 => taken? b 4 t4lt32
    | 0x64 => taken? b 5 t5lt32
    | 0x65 => taken? b 6 t6lt32
    | 0x66 => taken? b 7 t7lt32
    | 0x67 => taken? b 8 t8lt32
    | 0x68 => taken? b 9 t9lt32
    | 0x69 => taken? b 10 t10lt32
    | 0x6a => taken? b 11 t11lt32
    | 0x6b => taken? b 12 t12lt32
    | 0x6c => taken? b 13 t13lt32
    | 0x6d => taken? b 14 t14lt32
    | 0x6e => taken? b 15 t15lt32
    | 0x6f => taken? b 16 t16lt32
    | 0x70 => taken? b 17 t17lt32
    | 0x71 => taken? b 18 t18lt32
    | 0x72 => taken? b 19 t19lt32
    | 0x73 => taken? b 20 t20lt32
    | 0x74 => taken? b 21 t21lt32
    | 0x75 => taken? b 22 t22lt32
    | 0x76 => taken? b 23 t23lt32
    | 0x77 => taken? b 24 t24lt32
    | 0x78 => taken? b 25 t25lt32
    | 0x79 => taken? b 26 t26lt32
    | 0x7a => taken? b 27 t27lt32
    | 0x7b => taken? b 28 t28lt32
    | 0x7c => taken? b 29 t29lt32
    | 0x7d => taken? b 30 t30lt32
    | 0x7e => taken? b 31 t31lt32
    | 0x7f => taken? b 32 t32lt32

    | 0x80 => (some $ IDup 0, btail)
    | 0x81 => (some $ IDup 1, btail)
    | 0x82 => (some $ IDup 2, btail)
    | 0x83 => (some $ IDup 3, btail)
    | 0x84 => (some $ IDup 4, btail)
    | 0x85 => (some $ IDup 5, btail)
    | 0x86 => (some $ IDup 6, btail)
    | 0x87 => (some $ IDup 7, btail)
    | 0x88 => (some $ IDup 8, btail)
    | 0x89 => (some $ IDup 9, btail)
    | 0x8a => (some $ IDup 10, btail)
    | 0x8b => (some $ IDup 11, btail)
    | 0x8c => (some $ IDup 12, btail)
    | 0x8d => (some $ IDup 13, btail)
    | 0x8e => (some $ IDup 14, btail)
    | 0x8f => (some $ IDup 15, btail)

    | 0x90 => (some $ ISwap 0, btail)
    | 0x91 => (some $ ISwap 1, btail)
    | 0x92 => (some $ ISwap 2, btail)
    | 0x93 => (some $ ISwap 3, btail)
    | 0x94 => (some $ ISwap 4, btail)
    | 0x95 => (some $ ISwap 5, btail)
    | 0x96 => (some $ ISwap 6, btail)
    | 0x97 => (some $ ISwap 7, btail)
    | 0x98 => (some $ ISwap 8, btail)
    | 0x99 => (some $ ISwap 9, btail)
    | 0x9a => (some $ ISwap 10, btail)
    | 0x9b => (some $ ISwap 11, btail)
    | 0x9c => (some $ ISwap 12, btail)
    | 0x9d => (some $ ISwap 13, btail)
    | 0x9e => (some $ ISwap 14, btail)
    | 0x9f => (some $ ISwap 15, btail)

    | 0xa0 => (some $ ILog 0, btail)
    | 0xa1 => (some $ ILog 1, btail)
    | 0xa2 => (some $ ILog 2, btail)
    | 0xa3 => (some $ ILog 3, btail)
    | 0xa4 => (some $ ILog 4, btail)

    | 0xf0 => (some ICreate, btail)
    | 0xf1 => (some ICall, btail)
    | 0xf2 => (some ICallcode, btail)
    | 0xf3 => (some IReturn, btail)
    | 0xf4 => (some IDelegatecall, btail)
    | 0xf5 => (some ICreate2, btail)
    | 0xfa => (some IStaticcall, btail)
    | 0xfd => (some IRevert, btail)
    | 0xfe => (some IInvalid, btail)
    | 0xff => (some ISelfdestruct, btail)

    | _ => (none, b)


@[simp] private def getFirstElem : (get? (ByteArray.mk #[a]) 0) = some a := rfl
@[simp] private def extractEmpty (b: ByteArray) n : ByteArray.extract b n n = ByteArray.empty := sorry 
@[simp] private def btailnSizeOne : btailn {data := #[a]} 1 = ByteArray.empty := by
  simp [btailn, ByteArray.size, Array.size, List.length]

private theorem finCases' (n : Fin 16) :
  (((n = 15 ∨ n = 14) ∨ (n = 13 ∨ n = 12)) ∨
  ((n = 11 ∨ n = 10) ∨ (n = 9 ∨ n = 8))) ∨
  (((n = 7 ∨ n = 6) ∨ (n = 5 ∨ n = 4)) ∨
  ((n = 3 ∨ n = 2) ∨ (n = 1 ∨ n = 0))) := match n with
  | Fin.mk n pf => by 
  by_cases h : n = 15; subst h; exact Or.inl $ Or.inl $ Or.inl $ Or.inl rfl
  have pf : n < 15 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 14; subst h; exact Or.inl $ Or.inl $ Or.inl $ Or.inr rfl
  have pf : n < 14 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 13; subst h; exact Or.inl $ Or.inl $ Or.inr $ Or.inl rfl
  have pf : n < 13 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 12; subst h; exact Or.inl $ Or.inl $ Or.inr $ Or.inr rfl
  have pf : n < 12 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 11; subst h; exact Or.inl $ Or.inr $ Or.inl $ Or.inl rfl
  have pf : n < 11 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 10; subst h; exact Or.inl $ Or.inr $ Or.inl $ Or.inr rfl
  have pf : n < 10 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 9; subst h; exact Or.inl $ Or.inr $ Or.inr $ Or.inl rfl
  have pf : n < 9 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 8; subst h; exact Or.inl $ Or.inr $ Or.inr $ Or.inr rfl
  have pf : n < 8 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 7; subst h; exact Or.inr $ Or.inl $ Or.inl $ Or.inl rfl
  have pf : n < 7 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 6; subst h; exact Or.inr $ Or.inl $ Or.inl $ Or.inr rfl
  have pf : n < 6 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 5; subst h; exact Or.inr $ Or.inl $ Or.inr $ Or.inl rfl
  have pf : n < 5 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 4; subst h; exact Or.inr $ Or.inl $ Or.inr $ Or.inr rfl
  have pf : n < 4 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 3; subst h; exact Or.inr $ Or.inr $ Or.inl $ Or.inl rfl
  have pf : n < 3 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 2; subst h; exact Or.inr $ Or.inr $ Or.inl $ Or.inr rfl
  have pf : n < 2 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 1; subst h; exact Or.inr $ Or.inr $ Or.inr $ Or.inl rfl
  have pf : n < 1 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  by_cases h : n = 0; subst h; exact Or.inr $ Or.inr $ Or.inr $ Or.inr rfl
  have pf : n < 0 := by apply Nat.lt_of_le_and_ne (Nat.le_of_lt_succ pf) h
  cases pf

private theorem finCases5 (motive: Fin 5 -> Prop) (n : Fin 5) 
  (f0 : motive 0) (f1 : motive 1) (f2 : motive 2) (f3 : motive 3)
  (f4 : motive 4) : motive n := match n with | Fin.mk n pf => match n with
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | 3 => f3
  | 4 => f4
  | Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ n' => by 
    repeat (have pf := Nat.lt_of_succ_lt_succ pf)
    cases pf

private theorem finCases16 (motive: Fin 16 -> Prop) (n : Fin 16) 
  (f0 : motive 0) (f1 : motive 1) (f2 : motive 2) (f3 : motive 3)
  (f4 : motive 4) (f5 : motive 5) (f6 : motive 6) (f7 : motive 7)
  (f8 : motive 8) (f9 : motive 9) (f10 : motive 10) (f11 : motive 11)
  (f12 : motive 12) (f13 : motive 13) (f14 : motive 14) (f15 : motive 15) : motive n := match n with | Fin.mk n pf => match n with
  | 0 => f0 | 1 => f1 | 2 => f2 | 3 => f3
  | 4 => f4 | 5 => f5 | 6 => f6 | 7 => f7
  | 8 => f8 | 9 => f9 | 10 => f10 | 11 => f11
  | 12 => f12 | 13 => f13 | 14 => f14 | 15 => f15
  | Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ 
    Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ 
    Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ 
    Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ $ n' => by 
    repeat (have pf := Nat.lt_of_succ_lt_succ pf)
    cases pf


@[simp] private theorem t1 : get? { data := #[a] } 0 = some a := by simp
@[simp] private theorem t2 : btailn { data := #[a] } 1 = ByteArray.empty := by simp

private theorem encDecIPush (n: PushArg) : decode (encode (IPush n)) = (some (Instruction.other $ IPush n), ByteArray.empty) := by
  simp [encode, ofOne]
  admit

#eval (encode (IPush { bytes := ByteArray.mk #[0x01, 0x02, 0x02], pf := sorry } )).data == (ByteArray.mk #[0x97, 0x01, 0x02, 0x02]).data
#eval decode (encode (IPush { bytes := ByteArray.mk #[0x01, 0x02, 0x02], pf := sorry } ))
-- #eval encode (IPush { bytes := ByteArray.mk #[0x00, 0x00, 0x00,], pf := sorry } )


private theorem encDecIDup (n: Fin 16) : decode (encode (IDup n)) = (some (Instruction.other $ IDup n), ByteArray.empty) := by
  simp [encode, ofOne]
  have h0 : 128 + (0: Fin 16).val.toUInt8 = 128 := by rfl
  have h1 : 128 + (1: Fin 16).val.toUInt8 = 129 := by rfl
  have h2 : 128 + (2: Fin 16).val.toUInt8 = 130 := by rfl
  have h3 : 128 + (3: Fin 16).val.toUInt8 = 131 := by rfl
  have h4 : 128 + (4: Fin 16).val.toUInt8 = 132 := by rfl
  have h5 : 128 + (5: Fin 16).val.toUInt8 = 133 := by rfl
  have h6 : 128 + (6: Fin 16).val.toUInt8 = 134 := by rfl
  have h7 : 128 + (7: Fin 16).val.toUInt8 = 135 := by rfl
  have h8 : 128 + (8: Fin 16).val.toUInt8 = 136 := by rfl
  have h9 : 128 + (9: Fin 16).val.toUInt8 = 137 := by rfl
  have h10 : 128 + (10: Fin 16).val.toUInt8 = 138 := by rfl
  have h11 : 128 + (11: Fin 16).val.toUInt8 = 139 := by rfl
  have h12 : 128 + (12: Fin 16).val.toUInt8 = 140 := by rfl
  have h13 : 128 + (13: Fin 16).val.toUInt8 = 141 := by rfl
  have h14 : 128 + (14: Fin 16).val.toUInt8 = 142 := by rfl
  have h15 : 128 + (15: Fin 16).val.toUInt8 = 143 := by rfl

  cases n using finCases16 <;> simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] <;> (unfold decode ; rw [t1, t2])
  
private theorem encDecISwap (n: Fin 16) : decode (encode (ISwap n)) = (some (Instruction.other $ ISwap n), ByteArray.empty) := by
  simp [encode, ofOne]
  have h0 : 144 + (0: Fin 16).val.toUInt8 = 144 := by rfl
  have h1 : 144 + (1: Fin 16).val.toUInt8 = 145 := by rfl
  have h2 : 144 + (2: Fin 16).val.toUInt8 = 146 := by rfl
  have h3 : 144 + (3: Fin 16).val.toUInt8 = 147 := by rfl
  have h4 : 144 + (4: Fin 16).val.toUInt8 = 148 := by rfl
  have h5 : 144 + (5: Fin 16).val.toUInt8 = 149 := by rfl
  have h6 : 144 + (6: Fin 16).val.toUInt8 = 150 := by rfl
  have h7 : 144 + (7: Fin 16).val.toUInt8 = 151 := by rfl
  have h8 : 144 + (8: Fin 16).val.toUInt8 = 152 := by rfl
  have h9 : 144 + (9: Fin 16).val.toUInt8 = 153 := by rfl
  have h10 : 144 + (10: Fin 16).val.toUInt8 = 154 := by rfl
  have h11 : 144 + (11: Fin 16).val.toUInt8 = 155 := by rfl
  have h12 : 144 + (12: Fin 16).val.toUInt8 = 156 := by rfl
  have h13 : 144 + (13: Fin 16).val.toUInt8 = 157 := by rfl
  have h14 : 144 + (14: Fin 16).val.toUInt8 = 158 := by rfl
  have h15 : 144 + (15: Fin 16).val.toUInt8 = 159 := by rfl

  cases n using finCases16 <;> simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] <;> (unfold decode ; rw [t1, t2])


private theorem encDecILog (n: Fin 5) : decode (encode (ILog n)) = (some (Instruction.other $ ILog n), ByteArray.empty) := by
  simp [encode, ofOne]
  have h0 : 144 + (0: Fin 16).val.toUInt8 = 144 := by rfl
  have h1 : 144 + (1: Fin 16).val.toUInt8 = 145 := by rfl
  have h2 : 144 + (2: Fin 16).val.toUInt8 = 146 := by rfl
  have h3 : 144 + (3: Fin 16).val.toUInt8 = 147 := by rfl
  have h4 : 144 + (4: Fin 16).val.toUInt8 = 148 := by rfl
  have h5 : 144 + (5: Fin 16).val.toUInt8 = 149 := by rfl
  have h6 : 144 + (6: Fin 16).val.toUInt8 = 150 := by rfl
  have h7 : 144 + (7: Fin 16).val.toUInt8 = 151 := by rfl
  have h8 : 144 + (8: Fin 16).val.toUInt8 = 152 := by rfl
  have h9 : 144 + (9: Fin 16).val.toUInt8 = 153 := by rfl
  have h10 : 144 + (10: Fin 16).val.toUInt8 = 154 := by rfl
  have h11 : 144 + (11: Fin 16).val.toUInt8 = 155 := by rfl
  have h12 : 144 + (12: Fin 16).val.toUInt8 = 156 := by rfl
  have h13 : 144 + (13: Fin 16).val.toUInt8 = 157 := by rfl
  have h14 : 144 + (14: Fin 16).val.toUInt8 = 158 := by rfl
  have h15 : 144 + (15: Fin 16).val.toUInt8 = 159 := by rfl

  cases n using finCases5 <;> simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] <;> (unfold decode ; rw [t1, t2])

#eval 0

macro "solvefast" : tactic => `(simp [encode, ofOne]; unfold decode; rw [t1, t2])

private theorem encodeDecodeIStop : decode (encode IStop) = (some $ Instruction.other $ IStop, ByteArray.empty) := by solvefast
private theorem encodeDecodeIAdd : decode (encode IAdd) = (some $ Instruction.expr $ IAdd, ByteArray.empty) := by solvefast
private theorem encodeDecodeIMul : decode (encode IMul) = (some $ Instruction.expr $ IMul, ByteArray.empty) := by solvefast
private theorem encodeDecodeISub : decode (encode ISub) = (some $ Instruction.expr $ ISub, ByteArray.empty) := by solvefast
private theorem encodeDecodeIDiv : decode (encode IDiv) = (some $ Instruction.expr $ IDiv, ByteArray.empty) := by solvefast
private theorem encodeDecodeISdiv : decode (encode ISdiv) = (some $ Instruction.expr $ ISdiv, ByteArray.empty) := by solvefast
private theorem encodeDecodeIMod : decode (encode IMod) = (some $ Instruction.expr $ IMod, ByteArray.empty) := by solvefast
private theorem encodeDecodeISmod : decode (encode ISmod) = (some $ Instruction.expr $ ISmod, ByteArray.empty) := by solvefast
private theorem encodeDecodeIAddmod : decode (encode IAddmod) = (some $ Instruction.expr $ IAddmod, ByteArray.empty) := by solvefast
private theorem encodeDecodeIMulmod : decode (encode IMulmod) = (some $ Instruction.expr $ IMulmod, ByteArray.empty) := by solvefast
private theorem encodeDecodeIExp : decode (encode IExp) = (some $ Instruction.expr $ IExp, ByteArray.empty) := by solvefast
private theorem encodeDecodeISignextend : decode (encode ISignextend) = (some $ Instruction.expr $ ISignextend, ByteArray.empty) := by solvefast
private theorem encodeDecodeILt : decode (encode ILt) = (some $ Instruction.expr $ ILt, ByteArray.empty) := by solvefast
private theorem encodeDecodeIGt : decode (encode IGt) = (some $ Instruction.expr $ IGt, ByteArray.empty) := by solvefast
private theorem encodeDecodeISlt : decode (encode ISlt) = (some $ Instruction.expr $ ISlt, ByteArray.empty) := by solvefast
private theorem encodeDecodeISgt : decode (encode ISgt) = (some $ Instruction.expr $ ISgt, ByteArray.empty) := by solvefast
private theorem encodeDecodeIEq : decode (encode IEq) = (some $ Instruction.expr $ IEq, ByteArray.empty) := by solvefast
private theorem encodeDecodeIIszero : decode (encode IIszero) = (some $ Instruction.expr $ IIszero, ByteArray.empty) := by solvefast
private theorem encodeDecodeIAnd : decode (encode IAnd) = (some $ Instruction.expr $ IAnd, ByteArray.empty) := by solvefast
private theorem encodeDecodeIOr : decode (encode IOr) = (some $ Instruction.expr $ IOr, ByteArray.empty) := by solvefast
private theorem encodeDecodeIXor : decode (encode IXor) = (some $ Instruction.expr $ IXor, ByteArray.empty) := by solvefast
private theorem encodeDecodeINot : decode (encode INot) = (some $ Instruction.expr $ INot, ByteArray.empty) := by solvefast
private theorem encodeDecodeIByte : decode (encode IByte) = (some $ Instruction.expr $ IByte, ByteArray.empty) := by solvefast
private theorem encodeDecodeIShl : decode (encode IShl) = (some $ Instruction.expr $ IShl, ByteArray.empty) := by solvefast
private theorem encodeDecodeIShr : decode (encode IShr) = (some $ Instruction.expr $ IShr, ByteArray.empty) := by solvefast
private theorem encodeDecodeISar : decode (encode ISar) = (some $ Instruction.expr $ ISar, ByteArray.empty) := by solvefast
private theorem encodeDecodeISha3 : decode (encode ISha3) = (some $ Instruction.expr $ ISha3, ByteArray.empty) := by solvefast
private theorem encodeDecodeIAddress : decode (encode IAddress) = (some $ Instruction.ctxt $ IAddress, ByteArray.empty) := by solvefast
private theorem encodeDecodeIBalance : decode (encode IBalance) = (some $ Instruction.ctxt $ IBalance, ByteArray.empty) := by solvefast
private theorem encodeDecodeIOrigin : decode (encode IOrigin) = (some $ Instruction.ctxt $ IOrigin, ByteArray.empty) := by solvefast
private theorem encodeDecodeICaller : decode (encode ICaller) = (some $ Instruction.ctxt $ ICaller, ByteArray.empty) := by solvefast
private theorem encodeDecodeICallvalue : decode (encode ICallvalue) = (some $ Instruction.ctxt $ ICallvalue, ByteArray.empty) := by solvefast
private theorem encodeDecodeICalldataload : decode (encode ICalldataload) = (some $ Instruction.ctxt $ ICalldataload, ByteArray.empty) := by solvefast
private theorem encodeDecodeICalldatasize : decode (encode ICalldatasize) = (some $ Instruction.ctxt $ ICalldatasize, ByteArray.empty) := by solvefast
private theorem encodeDecodeICalldatacopy : decode (encode ICalldatacopy) = (some $ Instruction.ctxt $ ICalldatacopy, ByteArray.empty) := by solvefast
private theorem encodeDecodeICodesize : decode (encode ICodesize) = (some $ Instruction.ctxt $ ICodesize, ByteArray.empty) := by solvefast
private theorem encodeDecodeICodecopy : decode (encode ICodecopy) = (some $ Instruction.ctxt $ ICodecopy, ByteArray.empty) := by solvefast
private theorem encodeDecodeIGasprice : decode (encode IGasprice) = (some $ Instruction.ctxt $ IGasprice, ByteArray.empty) := by solvefast
private theorem encodeDecodeIExtcodesize : decode (encode IExtcodesize) = (some $ Instruction.ctxt $ IExtcodesize, ByteArray.empty) := by solvefast
private theorem encodeDecodeIExtcodecopy : decode (encode IExtcodecopy) = (some $ Instruction.ctxt $ IExtcodecopy, ByteArray.empty) := by solvefast
private theorem encodeDecodeIReturndatasize : decode (encode IReturndatasize) = (some $ Instruction.ctxt $ IReturndatasize, ByteArray.empty) := by solvefast
private theorem encodeDecodeIReturndatacopy : decode (encode IReturndatacopy) = (some $ Instruction.ctxt $ IReturndatacopy, ByteArray.empty) := by solvefast
private theorem encodeDecodeIExtcodehash : decode (encode IExtcodehash) = (some $ Instruction.ctxt $ IExtcodehash, ByteArray.empty) := by solvefast
private theorem encodeDecodeIBlockhash : decode (encode IBlockhash) = (some $ Instruction.ctxt $ IBlockhash, ByteArray.empty) := by solvefast
private theorem encodeDecodeICoinbase : decode (encode ICoinbase) = (some $ Instruction.ctxt $ ICoinbase, ByteArray.empty) := by solvefast
private theorem encodeDecodeITimestamp : decode (encode ITimestamp) = (some $ Instruction.ctxt $ ITimestamp, ByteArray.empty) := by solvefast
private theorem encodeDecodeINumber : decode (encode INumber) = (some $ Instruction.ctxt $ INumber, ByteArray.empty) := by solvefast
private theorem encodeDecodeIDifficulty : decode (encode IDifficulty) = (some $ Instruction.ctxt $ IDifficulty, ByteArray.empty) := by solvefast
private theorem encodeDecodeIGaslimit : decode (encode IGaslimit) = (some $ Instruction.ctxt $ IGaslimit, ByteArray.empty) := by solvefast
private theorem encodeDecodeIChainid : decode (encode IChainid) = (some $ Instruction.ctxt $ IChainid, ByteArray.empty) := by solvefast
private theorem encodeDecodeISelfbalance : decode (encode ISelfbalance) = (some $ Instruction.ctxt $ ISelfbalance, ByteArray.empty) := by solvefast
private theorem encodeDecodeIBasefee : decode (encode IBasefee) = (some $ Instruction.ctxt $ IBasefee, ByteArray.empty) := by solvefast
private theorem encodeDecodeIPop : decode (encode IPop) = (some $ Instruction.mem $ IPop, ByteArray.empty) := by solvefast
private theorem encodeDecodeIMload : decode (encode IMload) = (some $ Instruction.mem $ IMload, ByteArray.empty) := by solvefast
private theorem encodeDecodeIMstore : decode (encode IMstore) = (some $ Instruction.mem $ IMstore, ByteArray.empty) := by solvefast
private theorem encodeDecodeIMstore8 : decode (encode IMstore8) = (some $ Instruction.mem $ IMstore8, ByteArray.empty) := by solvefast
private theorem encodeDecodeISload : decode (encode ISload) = (some $ Instruction.mem $ ISload, ByteArray.empty) := by solvefast
private theorem encodeDecodeISstore : decode (encode ISstore) = (some $ Instruction.mem $ ISstore, ByteArray.empty) := by solvefast
private theorem encodeDecodeIJump : decode (encode IJump) = (some $ Instruction.other $ IJump, ByteArray.empty) := by solvefast
private theorem encodeDecodeIJumpi : decode (encode IJumpi) = (some $ Instruction.other $ IJumpi, ByteArray.empty) := by solvefast
private theorem encodeDecodeIPc : decode (encode IPc) = (some $ Instruction.other $ IPc, ByteArray.empty) := by solvefast
private theorem encodeDecodeIMsize : decode (encode IMsize) = (some $ Instruction.other $ IMsize, ByteArray.empty) := by solvefast
private theorem encodeDecodeIGas : decode (encode IGas) = (some $ Instruction.other $ IGas, ByteArray.empty) := by solvefast
private theorem encodeDecodeIJumpdest : decode (encode IJumpdest) = (some $ Instruction.other $ IJumpdest, ByteArray.empty) := by solvefast
private theorem encodeDecodeICreate : decode (encode ICreate) = (some $ Instruction.other $ ICreate, ByteArray.empty) := by solvefast
private theorem encodeDecodeICall : decode (encode ICall) = (some $ Instruction.other $ ICall, ByteArray.empty) := by solvefast
private theorem encodeDecodeICallcode : decode (encode ICallcode) = (some $ Instruction.other $ ICallcode, ByteArray.empty) := by solvefast
private theorem encodeDecodeIReturn : decode (encode IReturn) = (some $ Instruction.other $ IReturn, ByteArray.empty) := by solvefast
private theorem encodeDecodeIDelegatecall : decode (encode IDelegatecall) = (some $ Instruction.other $ IDelegatecall, ByteArray.empty) := by solvefast
private theorem encodeDecodeICreate2 : decode (encode ICreate2) = (some $ Instruction.other $ ICreate2, ByteArray.empty) := by solvefast
private theorem encodeDecodeIStaticcall : decode (encode IStaticcall) = (some $ Instruction.other $ IStaticcall, ByteArray.empty) := by solvefast
private theorem encodeDecodeIRevert : decode (encode IRevert) = (some $ Instruction.other $ IRevert, ByteArray.empty) := by solvefast
private theorem encodeDecodeIInvalid : decode (encode IInvalid) = (some $ Instruction.other $ IInvalid, ByteArray.empty) := by solvefast
private theorem encodeDecodeISelfdestruct : decode (encode ISelfdestruct) = (some $ Instruction.other $ ISelfdestruct, ByteArray.empty) := by solvefast

theorem encodeDecode (i: Instruction) : decode (encode i) = (some i, ByteArray.empty) := 
match i with
| IStop => encodeDecodeIStop
| IAdd => encodeDecodeIAdd
| IMul => encodeDecodeIMul
| ISub => encodeDecodeISub
| IDiv => encodeDecodeIDiv
| ISdiv => encodeDecodeISdiv
| IMod => encodeDecodeIMod
| ISmod => encodeDecodeISmod
| IAddmod => encodeDecodeIAddmod
| IMulmod => encodeDecodeIMulmod
| IExp => encodeDecodeIExp
| ISignextend => encodeDecodeISignextend

| ILt => encodeDecodeILt
| IGt => encodeDecodeIGt
| ISlt => encodeDecodeISlt
| ISgt => encodeDecodeISgt
| IEq => encodeDecodeIEq
| IIszero => encodeDecodeIIszero
| IAnd => encodeDecodeIAnd
| IOr => encodeDecodeIOr
| IXor => encodeDecodeIXor
| INot => encodeDecodeINot
| IByte => encodeDecodeIByte
| IShl => encodeDecodeIShl
| IShr => encodeDecodeIShr
| ISar => encodeDecodeISar

| ISha3 => encodeDecodeISha3

| IAddress => encodeDecodeIAddress
| IBalance => encodeDecodeIBalance
| IOrigin => encodeDecodeIOrigin
| ICaller => encodeDecodeICaller
| ICallvalue => encodeDecodeICallvalue
| ICalldataload => encodeDecodeICalldataload
| ICalldatasize => encodeDecodeICalldatasize
| ICalldatacopy => encodeDecodeICalldatacopy
| ICodesize => encodeDecodeICodesize
| ICodecopy => encodeDecodeICodecopy
| IGasprice => encodeDecodeIGasprice
| IExtcodesize => encodeDecodeIExtcodesize
| IExtcodecopy => encodeDecodeIExtcodecopy
| IReturndatasize => encodeDecodeIReturndatasize
| IReturndatacopy => encodeDecodeIReturndatacopy
| IExtcodehash => encodeDecodeIExtcodehash

| IBlockhash => encodeDecodeIBlockhash
| ICoinbase => encodeDecodeICoinbase
| ITimestamp => encodeDecodeITimestamp
| INumber => encodeDecodeINumber
| IDifficulty => encodeDecodeIDifficulty
| IGaslimit => encodeDecodeIGaslimit
| IChainid => encodeDecodeIChainid
| ISelfbalance => encodeDecodeISelfbalance
| IBasefee => encodeDecodeIBasefee

| IPop => encodeDecodeIPop
| IMload => encodeDecodeIMload
| IMstore => encodeDecodeIMstore
| IMstore8 => encodeDecodeIMstore8
| ISload => encodeDecodeISload
| ISstore => encodeDecodeISstore
| IJump => encodeDecodeIJump
| IJumpi => encodeDecodeIJumpi
| IPc => encodeDecodeIPc
| IMsize => encodeDecodeIMsize
| IGas => encodeDecodeIGas
| IJumpdest => encodeDecodeIJumpdest

| IPush arg => encDecIPush arg

| IDup n => encDecIDup n

| ISwap n => encDecISwap n

| ILog n => encDecILog n

| ICreate => encodeDecodeICreate
| ICall => encodeDecodeICall
| ICallcode => encodeDecodeICallcode
| IReturn => encodeDecodeIReturn
| IDelegatecall => encodeDecodeIDelegatecall
| ICreate2 => encodeDecodeICreate2
| IStaticcall => encodeDecodeIStaticcall
| IRevert => encodeDecodeIRevert
| IInvalid => encodeDecodeIInvalid
| ISelfdestruct => encodeDecodeISelfdestruct


end EVM