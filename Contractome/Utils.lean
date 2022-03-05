import Bytecode

import Std.Data.RBMap
import Std.Data.Stack

import Mathlib.Tactic.Basic

import Smt.UInt256
import Smt.Interfaces
import Smt.AssertCommand

-- class TInhabited (α : Sort u) where
--   mk {} :: (default : α)

-- #print (EVMMem (.empty

-- class EVMMem (α : Type u) where
--   empty : α
--   get (m: α) (addr : UInt32) : UInt32
--   set (m: α) (addr : UInt32) (val : UInt32) : α
--   -- isSet (m: α) (addr : UInt32) : Bool
--   -- isSet_false_get_zero (m: α) (addr : UInt32) : (isSet m addr = false) -> get m addr = 0
--   empty_get (k : UInt32) : get empty k = 0
--   set_get (m: α) (k v : UInt32) : get (set m k v) k = v
--   set_diff_get (m: α) (k k' v: UInt32) (h : Not (k = k')) : get (set m k v) k' = get m k'
--   -- set_same_get (m: α) (k v v': UInt32) : get (set (set m k v') k v) k = Some 


instance [DecidableEq κ] [p: Ord κ] [Inhabited ω] : EVMMem (κ:=κ) (ω:=ω) (Std.RBMap κ ω Ord.compare) where
  empty := Std.RBMap.empty (α:=κ) (β:=ω) 
  get m addr := m.findD addr default
  set m addr val := m.insert addr val
  -- isSet m addr := m.contains addr
  -- isSet_get_zero _ _ := sorry
  set_diff_get _ _ _ _ _ := sorry
  set_get _ _ _ := sorry
  empty_get _ := sorry


-- structure Stack

deriving instance Repr for Std.Stack
instance : EVMStack (Std.Stack UInt256) where
  empty := {}
  pop? a := match a.peek? with
  | Option.none => Option.none
  | Option.some s => (s, a.pop)
  peekn? a i := a.vals.get? (a.vals.size - 1 - i)
  setn? a i v := if a.vals.size <= i then Option.none else Option.some ⟨ a.vals.set ⟨ a.vals.size - 1 - i, sorry ⟩ v ⟩ 
  -- peekn? a i := a.vals.get? (a.vals.size - 1 - i)
  push a v := a.push v
  size a := a.vals.size


-- instance : Inhabited (Std.RBMap UInt32 UInt32 Ord.compare) := ⟨ Std.RBMap.empty ⟩


structure EVMStateGen [EVMMem (κ:=UInt256) (ω:=UInt256 ) μ] {σ : Type} [EVMStack σ] where 
  stack : σ := EVMStack.empty
  memory : μ := EVMMem.empty UInt256 UInt256
  storage : μ := EVMMem.empty UInt256 UInt256
deriving Repr

structure EVMContext where
  program : Array UInt32

-- structure EVMState where 
--   pc : UInt32 := 0
--   stack : List UInt32 := []
--   memory : Std.RBMap UInt32 UInt32 Ord.compare := Std.RBMap.empty
--   storage : Std.RBMap UInt32 UInt32 Ord.compare := Std.RBMap.empty
-- deriving Repr


-- structure EVMState' where 
--   stack : List UInt32 := []
--   memory : Std.RBMap UInt32 UInt32 Ord.compare := Std.RBMap.empty
--   storage : Std.RBMap UInt32 UInt32 Ord.compare := Std.RBMap.empty
-- deriving Repr


-- abbrev EVMState := EVMStateGen (Std.RBMap UInt32 UInt32 Ord.compare)


inductive EVMException where
| test : String -> EVMException
| negativeStackError : EVMException
| notImplementedError : EVMException
deriving Repr, Inhabited, BEq

deriving instance BEq for Except

-- #eval (List.cons a []).head?


-- set_option maxRecDepth 4000


-- #print Decidable


#print EVMMem.empty



-- #eval (inferInstance : EVMMem MUInt32 MUInt32 (VAL MUInt32 MUInt32))


-- #reduce (EVMMem.empty (α := VAL MUInt32 MUInt32) MUInt32 MUInt32)
-- #reduce (EVMMem.set (EVMMem.empty (α := VAL MUInt32 MUInt32) MUInt32 MUInt32) a (1:MUInt32))
-- #reduce EVMMem.get (ω := MUInt32) (EVMMem.set (EVMMem.set (EVMMem.empty (α := VAL MUInt32 MUInt32) MUInt32 MUInt32) a (1:MUInt32)) b (2:MUInt32)) a

-- def TEVMMem := EVMMem UInt32 UInt32 (Std.RBMap UInt32 UInt32 Ord.compare)

abbrev EVMM {μ : Type} [EVMMem UInt256 UInt256 μ] {σ : Type} [EVMStack σ] := StateT (EVMStateGen (μ:=μ) (σ:=σ)) $ ExceptT EVMException Id

namespace EVMM
  variable [pμ : EVMMem UInt256 UInt256 μ]
  variable [pσ : EVMStack σ]
  variable [EmptyCollection (EVMStateGen (μ:=μ) (σ:=σ))]
  
  def run {α : Type 0} (v: EVMM (μ:=μ) (σ:=σ) α) (stack : σ) : Except EVMException (α × EVMStateGen (μ:=μ) (σ:=σ)) :=
    StateT.run v {stack := stack, memory := EVMMem.empty (self:=pμ), storage := EVMMem.empty (self:=pμ)} |> ExceptT.run

  -- Assert test helpers
  def RunOnStack (a : EVMM (μ:=Std.RBMap UInt256 UInt256 Ord.compare) (σ:=Std.Stack UInt256) Unit) (s : Array UInt256) : Except EVMException $ Array UInt256 :=
    let res := EVMM.run (μ:=Std.RBMap UInt256 UInt256 Ord.compare) a (Std.Stack.mk (α:=UInt256) s.reverse)
    match res with
    | Except.error e => Except.error e
    | Except.ok v => Except.ok v.snd.stack.vals.reverse

  def UA (a : Array UInt256) : Except EVMException (Array UInt256) := Except.ok a

  -- Semantics

  def popStack : EVMM (μ:=μ) (σ:=σ) UInt256 := do
    let st ← get 
    match EVMStack.pop? st.stack with
    | none => throw $ EVMException.negativeStackError
    | some ⟨s, stc'⟩ => 
    set {st with stack := stc'}
    s
  def peeknStack (n: Nat) : EVMM (μ:=μ) (σ:=σ) UInt256 := do match EVMStack.peekn? (← get).stack n with 
    | none => throw $ EVMException.negativeStackError
    | some a => a
  def pushStack (v: UInt256) : EVMM (μ:=μ) (σ:=σ) Unit := do
    modify $ fun st => {st with  stack := EVMStack.push st.stack v}    
  def setStack (i: Nat) (v: UInt256) : EVMM (μ:=μ) (σ:=σ) Unit := do
    let st ← get 
    match EVMStack.setn? st.stack i v with
    | none => throw $ EVMException.negativeStackError
    | some a => set {st with  stack := a}

  def mapStack1 (f: UInt256 -> UInt256) : EVMM (μ:=μ) (σ:=σ) Unit := popStack <&> f >>= pushStack
  def mapStack2 (f: UInt256 -> UInt256 -> UInt256) : EVMM (μ:=μ) (σ:=σ) Unit := do
    let v1 ← popStack
    let v2 ← popStack
    pushStack $ f v1 v2
  def mapStack3 (f: UInt256 -> UInt256 -> UInt256 -> UInt256) : EVMM (μ:=μ) (σ:=σ) Unit := do
    let v1 ← popStack
    let v2 ← popStack
    let v3 ← popStack
    pushStack $ f v1 v2 v3

  def i01_add : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 UInt256.add
  #assert (RunOnStack EVMM.i01_add #[10, 10]) == UA #[20]
  #assert (RunOnStack EVMM.i01_add #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 1]) == UA #[0]

  def i02_mul : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 UInt256.mul
  #assert (RunOnStack EVMM.i02_mul #[10, 10]) == UA #[100]
  #assert (RunOnStack EVMM.i02_mul #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2]) == UA #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE]

  def i03_sub : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 UInt256.sub
  #assert (RunOnStack EVMM.i03_sub #[10, 10]) == UA #[0]
  #assert (RunOnStack EVMM.i03_sub #[0, 1]) == UA #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF]

  def i04_div : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 UInt256.div
  #assert (RunOnStack EVMM.i04_div #[10, 10]) == UA #[1]
  #assert (RunOnStack EVMM.i04_div #[1, 2]) == UA #[0]
  #assert (RunOnStack EVMM.i04_div #[2, 1]) == UA #[2]
  #assert (RunOnStack EVMM.i04_div #[10, 2]) == UA #[5]

  def i05_sdiv : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 UInt256.sdiv
  #assert (RunOnStack EVMM.i05_sdiv #[10, 10]) == UA #[1]
  #assert (RunOnStack EVMM.i05_sdiv #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF]) == UA #[2]
  #assert (RunOnStack EVMM.i05_sdiv #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0x2]) == UA #[0]

  def i06_mod : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun x y => if y == 0 then 0 else UInt256.mod x y
  #assert (RunOnStack EVMM.i06_mod #[10, 3]) == UA #[1]
  #assert (RunOnStack EVMM.i06_mod #[17, 5]) == UA #[2]
  #assert (RunOnStack EVMM.i06_mod #[17, 0]) == UA #[0]

  def i07_smod : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun x y => if y == 0 then 0 else UInt256.smod x y
  #assert (RunOnStack EVMM.i07_smod #[10, 3]) == UA #[1]
  #assert (RunOnStack EVMM.i07_smod #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD]) == UA #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE]

  def i08_addmod : EVMM (μ:=μ) (σ:=σ) Unit := mapStack3 fun a b N => if N == 0 then 0 else UInt256.mk ((a.val + b.val) % N.val)
  #assert (RunOnStack EVMM.i08_addmod #[10, 10, 8]) == UA #[4]
  #assert (RunOnStack EVMM.i08_addmod #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2, 2]) == UA #[1]

  def i09_mulmod : EVMM (μ:=μ) (σ:=σ) Unit := mapStack3 fun a b N => if N == 0 then 0 else UInt256.mk ⟨ (a.val.val * b.val.val) % N.val.val, sorry ⟩ 
  #assert (RunOnStack EVMM.i09_mulmod #[10, 10, 8]) == UA #[4]
  #assert (RunOnStack EVMM.i09_mulmod #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 12]) == UA #[9]

  def i0a_exp : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 UInt256.pow
  #assert (RunOnStack EVMM.i0a_exp #[10, 2]) == UA #[100]
  #assert (RunOnStack EVMM.i0a_exp #[2, 2]) == UA #[4]

  def i0b_signextend : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun byteNum x =>
    if byteNum > 31 then x else
    let bitNum := byteNum*8+7
    let mask := ((1:UInt256) <<< bitNum) - 1
    let isBitSet := (x >>> bitNum) &&& 1 == 1
    if isBitSet then x ||| (~~~ mask) else x &&& mask
  #assert (RunOnStack EVMM.i0b_signextend #[0, 0xFF]) == UA #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF]
  #assert (RunOnStack EVMM.i0b_signextend #[0, 0x7F]) == UA #[0x7F]

  def ofBool (a : Bool) : UInt256 := if a then 1 else 0

  def i10_lt : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 $ fun a b => ofBool (a < b)
  #assert (RunOnStack EVMM.i10_lt #[9, 10]) == UA #[1]
  #assert (RunOnStack EVMM.i10_lt #[10, 10]) == UA #[0]

  def i11_gt : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun a b => ofBool (a > b)
  #assert (RunOnStack EVMM.i11_gt #[10, 9]) == UA #[1]
  #assert (RunOnStack EVMM.i11_gt #[10, 10]) == UA #[0]

  def i12_slt : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun a b => ofBool (a.slt b)
  #assert (RunOnStack EVMM.i12_slt #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0]) == UA #[1]
  #assert (RunOnStack EVMM.i12_slt #[10, 10]) == UA #[0]

  def i13_sgt : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun a b => ofBool (a.sgt b)
  #assert (RunOnStack EVMM.i13_sgt #[0, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF]) == UA #[1]
  #assert (RunOnStack EVMM.i13_sgt #[10, 10]) == UA #[0]

  def i14_eq : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun a b => ofBool (a == b)
  #assert (RunOnStack EVMM.i14_eq #[10, 10]) == UA #[1]
  #assert (RunOnStack EVMM.i14_eq #[10, 5]) == UA #[0]
  
  def i15_iszero : EVMM (μ:=μ) (σ:=σ) Unit := mapStack1 fun a => ofBool (a == 0)
  #assert (RunOnStack EVMM.i15_iszero #[10]) == UA #[0]
  #assert (RunOnStack EVMM.i15_iszero #[0]) == UA #[1]

  def i16_and : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun a b => a &&& b
  #assert (RunOnStack EVMM.i16_and #[0xF, 0xF]) == UA #[0xF]
  #assert (RunOnStack EVMM.i16_and #[0xFF, 0]) == UA #[0]

  def i17_or : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun a b => a ||| b
  #assert (RunOnStack EVMM.i17_or #[0xF0, 0xF]) == UA #[0xFF]
  #assert (RunOnStack EVMM.i17_or #[0xFF, 0xFF]) == UA #[0xFF]

  def i18_xor : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun a b => a ^^^ b
  #assert (RunOnStack EVMM.i18_xor #[0xF0, 0xF]) == UA #[0xFF]
  #assert (RunOnStack EVMM.i18_xor #[0xFF, 0xFF]) == UA #[0]

  def i19_not : EVMM (μ:=μ) (σ:=σ) Unit := mapStack1 fun a => ~~~ a
  #assert (RunOnStack EVMM.i19_not #[0]) == UA #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF]

  def i1a_byte : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun i x => (x <<< (i*8)) >>> (256 - 8)
  #assert (RunOnStack EVMM.i1a_byte #[31, 0xFF]) == UA #[0xFF]
  #assert (RunOnStack EVMM.i1a_byte #[30, 0xFF00]) == UA #[0xFF]

  def i1b_shl : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun shift value => value <<< shift
  #assert (RunOnStack EVMM.i1b_shl #[1, 1]) == UA #[2]
  #assert (RunOnStack EVMM.i1b_shl #[4, 0xFF00000000000000000000000000000000000000000000000000000000000000]) == UA #[0xF000000000000000000000000000000000000000000000000000000000000000]

  def i1c_shr : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun shift value => value >>> shift
  #assert (RunOnStack EVMM.i1c_shr #[1, 2]) == UA #[1]
  #assert (RunOnStack EVMM.i1c_shr #[4, 0xFF]) == UA #[0xF]

  def i1c_sar : EVMM (μ:=μ) (σ:=σ) Unit := mapStack2 fun shift value =>
    if value.isSpos then value >>> shift else
    let mask := UInt256.ones <<< (256 - shift)
    (value >>> shift) ||| mask
  #assert (RunOnStack EVMM.i1c_sar #[1, 2]) == UA #[1]
  #assert (RunOnStack EVMM.i1c_sar #[4, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0]) == UA #[0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF]

  def i20_sha3 : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i30_address : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i31_balance : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i32_origin : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i33_caller : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i34_callvalue : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i35_calldataload : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i36_calldatasize : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i37_calldatacopy : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i38_codesize : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i39_codecopy : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i3b_extcodesize : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i3c_extcodecopy : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i3d_returndatasize : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i3e_returndatacopy : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i3f_extcodehash : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i40_blockhash : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i41_coinbase : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i42_timestamp : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i43_number : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i44_difficulty : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i45_gaslimit : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i46_chainid : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i47_selfbalance : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i48_basefee : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError


  def i50_pop : EVMM (μ:=μ) (σ:=σ) Unit := do _ ← popStack; return
  #assert (RunOnStack EVMM.i50_pop #[1, 2]) == UA #[2]

  def i51_mload : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i52_mstore : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i53_mstore8 : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i54_sload : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i55_sstore : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i56_jump : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i57_jumpi : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i58_pc : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i59_msize : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i5a_gas : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError
  def i5b_jumpdest : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError

  -- def pushNBytes (l : Array Byte) : EVMM (μ:=μ) (σ:=σ) Unit := l.forM push
  def pushHelper (n : Nat) : EVMM (μ:=μ) (σ:=σ) Unit := do throw EVMException.notImplementedError

  def i60_push1 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 1
  def i61_push2 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 2
  def i62_push3 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 3
  def i63_push4 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 4
  def i64_push5 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 5
  def i65_push6 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 6
  def i66_push7 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 7
  def i67_push8 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 8
  def i68_push9 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 9
  def i69_push10 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 10
  def i6a_push11 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 11
  def i6b_push12 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 12
  def i6c_push13 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 13
  def i6d_push14 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 14
  def i6e_push15 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 15
  def i6f_push16 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 16
  def i70_push17 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 17
  def i71_push18 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 18
  def i72_push19 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 19
  def i73_push20 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 20
  def i74_push21 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 21
  def i75_push22 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 22
  def i76_push23 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 23
  def i77_push24 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 24
  def i78_push25 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 25
  def i79_push26 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 26
  def i7a_push27 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 27
  def i7b_push28 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 28
  def i7c_push29 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 29
  def i7d_push30 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 30
  def i7e_push31 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 31
  def i7f_push32 : EVMM (μ:=μ) (σ:=σ) Unit := pushHelper 32

  def dupHelper (i : Nat) : EVMM (μ:=μ) (σ:=σ) Unit := peeknStack (Nat.pred i) >>= pushStack

  def i80_dup1 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 1
  #assert (RunOnStack EVMM.i80_dup1 #[1, 2]) == UA #[1, 1, 2]
  def i81_dup2 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 2
  #assert (RunOnStack EVMM.i81_dup2 #[1, 2]) == UA #[2, 1, 2]
  def i82_dup3 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 3
  def i83_dup4 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 4
  def i84_dup5 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 5
  def i85_dup6 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 6
  def i86_dup7 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 7
  def i87_dup8 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 8
  def i88_dup9 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 9
  def i89_dup10 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 10
  def i8a_dup11 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 11
  def i8b_dup12 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 12
  def i8c_dup13 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 13
  def i8d_dup14 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 14
  def i8e_dup15 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 15
  def i8f_dup16 : EVMM (μ:=μ) (σ:=σ) Unit := dupHelper 16

  def swapHelper (i : Nat) : EVMM (μ:=μ) (σ:=σ) Unit := do
    let a ← peeknStack (Nat.pred i)
    let b ← peeknStack 0
    setStack (Nat.pred i) b
    setStack 0 a

  def i90_swap1 : EVMM (μ:=μ) (σ:=σ) Unit := swapHelper 1
  #assert (RunOnStack EVMM.i80_dup1 #[1, 2, 3]) == UA #[2, 1, 3]

#eval (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF:UInt256) * (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF:UInt256)
#eval (0xFF:UInt8) * (0xFF:UInt8)
    
end EVMM

abbrev EVMStateMapStack := EVMStateGen (μ:=Std.RBMap UInt256 UInt256 Ord.compare) (σ := Std.Stack UInt256)


-- example : (RunOnStack EVMM.i01_add #[10, 10] #[20]).fst = true := by rfl

-- #eval Assert $ RunOnStack EVMM.i01_add #[10, 10] #[20]
-- #eval RunOnStack EVMM.i01_add #[10, 10] #[20]

-- #eval (inferInstance : Repr $ Except EVMException (Unit × EVMStateGen (μ:=Std.RBMap UInt256 UInt256 Ord.compare) (σ := Std.Stack UInt256)))

#eval (EVMM.run (μ:=Std.RBMap UInt256 UInt256 Ord.compare) EVMM.i01_add (Std.Stack.mk (α:=UInt256) #[1231231, 312312321321312321312312312132]))

-- class TestClass (α : Type) where
--   empty : α

-- #check @TestClass.empty

-- structure Context (τ : Type) [Inhabited τ] where
--   obj : τ := default

-- instance a : TestClass String := ⟨ "asdf" ⟩

-- abbrev WithStringContextM := ReaderT (Context String) Id
-- set_option pp.raw true
-- set_option pp.raw.maxDepth 10


-- #reduce WithStringContextM

-- #reduce @WithStringContextM Nat


-- #reduce fun (α : Type) (m : WithStringContextM α ) => ReaderT.run m {}

-- set_option trace.Meta.isDefEq true
-- def WithStringContextM.run (m : WithStringContextM α ) : α := ReaderT.run m $ Context.mk (τ := String) default
-- def WithStringContextM.getX : WithStringContextM String := do
--   let x ← read
--   x.obj