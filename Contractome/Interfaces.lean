-- import Smt.UInt256
-- import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Bytecode.Instruction
import Contractome.UInt256

namespace EVM


-- local macro "ofNat_class" Class:ident n:num : command =>
--   let field := Lean.mkIdent <| Class.getId.eraseMacroScopes.getString!.toLower
--   `(class $Class:ident.{u} (α : Type u) where
--     $field:ident : α

--   instance {α} [$Class α] : OfNat α (nat_lit $n) where
--     ofNat := ‹$Class α›.1

--   instance {α} [OfNat α (nat_lit $n)] : $Class α where
--     $field:ident := $n)

-- ofNat_class Zero 0
-- ofNat_class One 1


-- instance : OfNat (Fin (no_index (n+1))) i where
--   ofNat := Fin.ofNat i

-- #check UInt32.ofNat

class Element (T : Type u) [DecidableEq T] [∀ n, OfNat T n]
  extends Zero T, One T, Inhabited T, Xor T, OrOp T, AndOp T, Complement T, ShiftLeft T, ShiftRight T, Ord T, HAdd T T T where
  add: T -> T -> T
  mul: T -> T -> T
  sub: T -> T -> T
  div: T -> T -> T
  sdiv: T -> T -> T
  mod: T -> T -> T
  smod: T -> T -> T
  addmod: T -> T -> T -> T
  mulmod: T -> T -> T -> T
  exp: T -> T -> T
  signextend: T -> T -> T
  ltb: T -> T -> Bool
  gtb: T -> T -> Bool
  sltb: T -> T -> Bool
  sgtb: T -> T -> Bool
  eq: T -> T -> Bool := fun a b => decide (a = b)
  iszero: T -> Bool := fun a => decide (a = 0)
  byte: (val : T) -> (byteIdx : T) -> T
  sar: T -> T -> T
  -- sha3: T -> T
  -- toNat : T -> Nat
  ofNat : Nat -> T
  toNat : T -> Nat
  ofBool: Bool -> T := fun x => if x then one else zero

class SByteArray (Tw: Type) (Tb: Type) (A: Type) (BAI : Type) [TakeBytes BAI] where
  mkEmpty : A
  get (a: A) (i : Tw) : Tb
  size (a: A) : Tw
  -- push (a : A) (v: Tb) : A
  extract (a : A) (start : Tw) (length : Tw) : A
  extractTw (a : A) (t : Tw) : Tw
  toIterAt (a : A) (n : Tw) : BAI 
  -- toConcrete (a : A) : Option ByteArray
  ofConcrete (ba : ByteArray) : A
  
class EVMMapBasic (K : Type) (V : Type) (M : Type) where
  empty : M
  get? (m: M) (addr : K) : Option V
  set (m: M) (addr : K) (val : V) : M

class EVMMapDefault (K : Type) (V : Type) [Zero V] (M : Type) extends EVMMapBasic K V M where
  get (m: M) (addr : K) : V

-- instance [EVMMapBasic K V M] [i :Zero V] : @EVMMapDefault K V M := {}

class EVMMap (K : Type) (V : Type) [Zero V] (M : Type) extends EVMMapDefault K V M where
  get32 (m: M) (addr : K) : K
  set32 (m: M) (addr : K) (val : K) : M

  maxKey (m: M) : K
  empty_get (k : K) : get empty k = Zero.zero
  set_get (m: M) (k : K) (v : V) : get (set m k v) k = v
  set_diff_get (m: M) (k k' : K) (v: V) (h : Not (k = k')) : get (set m k v) k' = get m k'
  -- isSet (m: M) (addr : UInt32) : Bool
  -- isSet_false_get_zero (m: M) (addr : UInt32) : (isSet m addr = false) -> get m addr = 0
  -- set_same_get (m: α) (k v v': UInt32) : get (set (set m k v') k v) k = Some 

class EVMMapSeq (K : Type) (V : Type) [Zero V] (BA : Type) (BAI : Type) [TakeBytes BAI] [instBA: SByteArray K V BA BAI] (M : Type) extends EVMMap K V M where
  getRange (m: M) (start : K) (length : K) : BA
  setRange (m: M) (start : K) (length : K) (content: BA) : M

class EVMStack (K : Type) (S : Type) where
  empty : S
  -- peek? (s : α) : Option UInt32
  pop? (s : S) : Option (K × S)
  -- peek? (s : S) : Option K
  peekn? (s : S) (n : Nat) : Option K
  setn? (s : S) (n : Nat) (v : K) : Option S
  push (s : S) (v : K) : S
  size (s : S) : Nat 
  push_pop (s : S) (k : K) : pop? (push s k) = some (k, s)

attribute [simp] EVMStack.push_pop 

-- variable (S : Type u) [EVMStack Tw S]
-- variable (M : Type u) [EVMMap Tw Tb M]
-- variable (Sr : Type u) [EVMMap Tw Tb Sr]

structure Cfg where
  -- stack type
  S : Type
  -- byte array type
  BA : Type
  -- byte array iterator type
  BAI : Type
  -- Word->byte map type
  M : Type
  -- word->word map type. AM because "address map"
  AM : Type
  -- word->bytearray map type
  BAM : Type

  -- storage : word -> (M) map 
  STM : Type 

  -- return data stack
  RS : Type

  Tw : Type
  Tb : Type


variable {C : Cfg} [DecidableEq C.Tw] [∀ n, OfNat C.Tw n] [Element C.Tw] [DecidableEq C.Tb] [∀ n, OfNat C.Tb n] [Element C.Tb]
variable [Repr C.BA]
variable [TakeBytes C.BAI]
variable [instBA : SByteArray C.Tw C.Tb C.BA C.BAI]
variable [EVMStack C.Tw C.S] [EVMMapDefault C.Tw C.Tw C.AM] [EVMMapSeq C.Tw C.Tb C.BA C.BAI C.M]
variable [Zero C.M] [EVMMapDefault C.Tw C.M C.STM]
variable [EVMMapBasic C.Tw C.BA C.BAM]
-- variable 

-- structure ReturnData [Repr C.Tw] [Repr C.Tb] [Repr C.BA] where
--   returnCode : C.Tw
--   returnData : C.BA
-- deriving Repr, Inhabited

variable [Repr C.Tw] [Repr C.Tb] [Repr C.BA] 
variable [EVMStack (C.Tw × C.BA) C.RS]

-- Context that doesn't change betwen calls
structure ChainContext [Repr C.Tw] where
  gasprice : C.Tw
  blockhash : C.Tw
  coinbase : C.Tw
  timestamp : C.Tw
  number : C.Tw
  difficulty : C.Tw
  gaslimit : C.Tw
  chainid : C.Tw
  basefee : C.Tw
deriving Repr

structure TransactionContext [Repr C.Tw] [Repr C.AM] [Repr C.BA] [Repr C.BAM] [Repr C.RS] where
  address : C.Tw
  origin : C.Tw
  caller : C.Tw
  callvalue : C.Tw
  balances : C.AM
  calldata : C.BA
  returnData : C.RS
  codes : C.BAM
deriving Repr

structure Context [Repr C.Tw] [Repr C.Tb] [Repr C.AM] [Repr C.BA] [Repr C.BAM] [Repr C.S] [Repr C.M] [Repr C.STM] [Repr C.RS] where 
  pc : C.Tw
  stack : C.S
  memory : C.M
  storageMap : C.STM
  returnData : Option $ (C.Tw × C.BA) := none

  txCtx : TransactionContext (C:=C)
  chainCtx : ChainContext (C:=C)
deriving Repr
  -- tc : TransactionContext (Tw:=Tw)C
-- deriving Repr

inductive EVMException : Type where
| test : String -> EVMException
| negativeStackError
| invalidInstructionError
| notImplementedError
| invalidJumpDestinationError
| alreadyReturnedError
| abstractValueError
| ownBytecodeNotFound
| noReturnDataError
| returnDataOOBError
deriving Repr, Inhabited, BEq

--  code : Std.RBMap Tw (Array Tb) Ord.compare



-- set_option quotPrecheck false
-- notation "FContext" => Context (S:=S) (M:=M) (Sr:=Sr)




-- #reduce (Context : Type _)

-- test x : {c}

-- set_option pp.all true
-- set_option  true
