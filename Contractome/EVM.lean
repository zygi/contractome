import Contractome.Interfaces

open EVM

variable {C : Cfg} [DecidableEq C.Tw] [∀ n, OfNat C.Tw n] [Element C.Tw] [DecidableEq C.Tb] [∀ n, OfNat C.Tb n] [Element C.Tb]
variable [TakeBytes C.BAI]
variable [instBA : SByteArray C.Tw C.Tb C.BA C.BAI]
variable [EVMStack C.Tw C.S] [EVMStack (C.Tw × C.BA) C.RS] [EVMMapDefault C.Tw C.Tw C.AM] [EVMMapSeq C.Tw C.Tb C.BA C.BAI C.M]
variable [EVMMapBasic C.Tw C.BA C.BAM]
variable [Zero C.M]
variable [EVMMapDefault C.Tw C.M C.STM]
variable [Repr C.Tw] [Repr C.Tb] [Repr C.M] [Repr C.S] [Repr C.BA] [Repr C.BAM] [Repr C.AM] [Repr C.BA] [Repr C.STM] [Repr C.RS]

abbrev EVMM := StateT (Context (C:=C)) $ ExceptT EVMException Id
-- notation "FEVMM" => EVMM (S:=S) (M:=M) (Sr:=Sr)

namespace EVMM  
  abbrev CStack := @EVMStack (K:=C.Tw)


  def runWithC (v: EVMM (C:=C) α) (c : Context (C:=C)):= show Except EVMException (α × Context) from
    StateT.run v c |> ExceptT.run

  def run (v: EVMM (C:=C) α) (txCtx : TransactionContext (C:=C)) (chCtx : ChainContext (C:=C)) := show Except EVMException (α × Context) from
    runWithC v {
      pc := 0,
      stack := EVMStack.empty C.Tw,
      memory := EVMMapBasic.empty C.Tw C.Tb,
      storageMap := EVMMapBasic.empty C.Tw C.M,
      txCtx := txCtx,
      chainCtx := chCtx }

  def runWithC' (v: EVMM (C:=C) α) (txCtx : TransactionContext (C:=C)) (chCtx : ChainContext (C:=C)) (c : Context (C:=C)):= 
  show Except EVMException α from
    StateT.run' v c |> ExceptT.run

  def run' (v: EVMM (C:=C) α) (txCtx : TransactionContext (C:=C)) (chCtx : ChainContext (C:=C)) := show Except EVMException α from
      runWithC' v txCtx chCtx {
        pc := 0,
        stack := EVMStack.empty C.Tw,
        memory := EVMMapBasic.empty C.Tw C.Tb,
        storageMap := EVMMapBasic.empty C.Tw C.M,
        txCtx := txCtx,
        chainCtx := chCtx }
  -- Assert test helpers
  -- def RunOnStack (a : FEVMM Unit) (s : Array UInt256) : Except EVMException $ Array UInt256 :=
  --   let res := EVMM.run a (Std.Stack.mk (α:=UInt256) s.reverse)
  --   match res with
  --   | Except.error e => Except.error e
  --   | Except.ok v => Except.ok v.snd.stack.vals.reverse

  def UA (a : Array UInt256) : Except EVMException (Array UInt256) := Except.ok a

  def popStack : EVMM (C:=C) C.Tw := do
    let st ← get 
    match EVMStack.pop? st.stack with
    | none => throw $ EVMException.negativeStackError
    | some ⟨s, stc'⟩ => 
    set {st with stack := stc'}
    pure s

  def withStack1M (fn : C.Tw -> EVMM (C:=C) Unit) : EVMM (C:=C) Unit := do
    fn (← popStack)

  def withStack2M (fn : C.Tw -> C.Tw -> EVMM (C:=C) Unit) : EVMM (C:=C) Unit := do
    fn (← popStack) (← popStack)

  def withStack3M (fn : C.Tw -> C.Tw -> C.Tw -> EVMM (C:=C) Unit) : EVMM (C:=C) Unit := do
    fn (← popStack) (← popStack) (← popStack)

  def peeknStack (n: Nat) : EVMM (C:=C) C.Tw := do 
    let st := (← get).stack
    match EVMStack.peekn? (K:=C.Tw) st n with 
      | none => throw $ EVMException.negativeStackError
      | some a => pure a

  def pushStack (v: C.Tw) : EVMM (C:=C) Unit := do
    modify $ fun st => {st with  stack := EVMStack.push st.stack v}    

  def setStack (i: Nat) (v: C.Tw) : EVMM (C:=C) Unit := do
    let st ← get 
    match EVMStack.setn? st.stack i v with
    | none => throw $ EVMException.negativeStackError
    | some a => set {st with  stack := a}

  def mapStack1 (f: C.Tw -> C.Tw) : EVMM (C:=C) Unit := popStack <&> f >>= pushStack
  def mapStack1M (f: C.Tw -> EVMM (C:=C) C.Tw) : EVMM (C:=C) Unit := popStack >>= f >>= pushStack
  def mapStack2 (f: C.Tw -> C.Tw -> C.Tw) : EVMM (C:=C) Unit := do
    let v1 ← popStack
    let v2 ← popStack
    pushStack $ f v1 v2
  def mapStack3 (f: C.Tw -> C.Tw -> C.Tw -> C.Tw) : EVMM (C:=C) Unit := do
    let v1 ← popStack
    let v2 ← popStack
    let v3 ← popStack
    pushStack $ f v1 v2 v3

  def getOwnBytecode : EVMM (C:=C) C.BA := do
    let st ← get
    let Option.some bc := EVMMapBasic.get? (V := C.BA) st.txCtx.codes st.txCtx.address | throw $ EVMException.ownBytecodeNotFound
    return bc

  def getOwnStorage : EVMM (C:=C) C.M := do
    let st ← get
    return EVMMapDefault.get (V:=C.M) st.storageMap st.txCtx.address

  def getBytecode (addr : C.Tw) : EVMM (C:=C) C.BA := do
    let st ← get
    return (EVMMapBasic.get? (V:=C.BA) st.txCtx.codes addr).getD $ SByteArray.mkEmpty C.Tw C.Tb C.BAI

  def returnWith (code : C.Tw) (returnData : C.BA) : EVMM (C:=C) Unit := do
    modify $ fun st => {st with returnData := some (code, returnData)}

  def jumpDest : C.Tb := Element.ofNat $ UInt8.toNat $ (EVM.encode $ InstrOther.IJumpdest).get! 0

  def jumpTo (newPc : C.Tw) : EVMM (C:=C) Unit := do
    modify $ fun st => {st with pc := newPc}
    -- let bcO : Option UInt8 := (← get).currentCode.data.get? newPc
    let bc : C.Tb := SByteArray.get C.BAI (← getOwnBytecode) newPc
    if bc != jumpDest then throw EVMException.invalidJumpDestinationError

  def stackFromTxCtx (fn : TransactionContext (C:=C) -> C.Tw) : EVMM (C:=C) Unit := do pushStack $ fn (← get).txCtx
  def stackFromChainCtx (fn : ChainContext (C:=C) -> C.Tw) : EVMM (C:=C) Unit := do pushStack $ fn (← get).chainCtx
    
  def i00_stop : EVMM (C:=C) Unit := returnWith 0 (SByteArray.ofConcrete C.Tw C.Tb C.BAI $ ByteArray.mk #[0])

  def i01_add : EVMM (C:=C) Unit := mapStack2 Element.add


  def i02_mul : EVMM (C:=C) Unit := mapStack2 Element.mul


  def i03_sub : EVMM (C:=C) Unit := mapStack2 Element.sub


  def i04_div : EVMM (C:=C) Unit := mapStack2 Element.div



  def i05_sdiv : EVMM (C:=C) Unit := mapStack2 Element.sdiv



  def i06_mod : EVMM (C:=C) Unit := mapStack2 fun (x y : C.Tw) => if x == 0 then 0 else Element.mod x y



  def i07_smod : EVMM (C:=C) Unit := mapStack2 fun (x y : C.Tw) => if y == 0 then 0 else Element.smod x y


  def i08_addmod : EVMM (C:=C) Unit := mapStack3 fun (a b N : C.Tw) => if N == 0 then 0 else Element.addmod a b N


  def i09_mulmod : EVMM (C:=C) Unit := mapStack3 fun (a b N : C.Tw) => if N == 0 then 0 else Element.mulmod a b N

  def i0a_exp : EVMM (C:=C) Unit := mapStack2 Element.exp


  def i0b_signextend : EVMM (C:=C) Unit := mapStack2 Element.signextend

  -- def ofBool (a : Bool) : UInt256 := if a then 1 else 0

  def i10_lt : EVMM (C:=C) Unit := mapStack2 $ fun a b => Element.ofBool $ Element.ltb a b

  def i11_gt : EVMM (C:=C) Unit := mapStack2 fun a b => Element.ofBool $ Element.gtb a b

  def i12_slt : EVMM (C:=C) Unit := mapStack2 fun a b => Element.ofBool $ Element.sltb a b

  def i13_sgt : EVMM (C:=C) Unit := mapStack2 fun a b => Element.ofBool $ Element.sgtb a b

  def i14_eq : EVMM (C:=C) Unit := mapStack2 fun a b => Element.ofBool (a == b)
  
  def i15_iszero : EVMM (C:=C) Unit := mapStack1 fun a => Element.ofBool (a == 0)

  def i16_and : EVMM (C:=C) Unit := mapStack2 (@AndOp.and C.Tw _)

  def i17_or : EVMM (C:=C) Unit := mapStack2 (@OrOp.or C.Tw _)

  def i18_xor : EVMM (C:=C) Unit := mapStack2 (@Xor.xor C.Tw _)

  def i19_not : EVMM (C:=C) Unit := mapStack1 (@Complement.complement C.Tw _)

  def i1a_byte : EVMM (C:=C) Unit := mapStack2 $ fun a b => Element.byte b a

  def i1b_shl : EVMM (C:=C) Unit := mapStack2 fun (shift value: C.Tw) => value <<< shift

  def i1c_shr : EVMM (C:=C) Unit := mapStack2 fun (shift value: C.Tw) => value >>> shift

  def i1d_sar : EVMM (C:=C) Unit := mapStack2 $ Element.sar

  def i20_sha3 : EVMM (C:=C) Unit := do throw EVMException.notImplementedError
  
  -- mapStack1 $ @Element.sha3 C.Tw _ _

  def i30_address : EVMM (C:=C) Unit := stackFromTxCtx $ fun ctx => ctx.address

  def i31_balance : EVMM (C:=C) Unit := do 
    let arg ← popStack
    stackFromTxCtx $ fun ctx => EVMMapDefault.get ctx.balances arg

  def i32_origin : EVMM (C:=C) Unit := stackFromTxCtx $ fun ctx => ctx.origin

  def i33_caller : EVMM (C:=C) Unit := stackFromTxCtx $ fun ctx => ctx.caller

  def i34_callvalue : EVMM (C:=C) Unit := stackFromTxCtx $ fun ctx => ctx.callvalue

  def i35_calldataload : EVMM (C:=C) Unit := mapStack1M $ fun arg => do
    pure $ SByteArray.extractTw C.Tb C.BAI (← get).txCtx.calldata arg

  def i36_calldatasize : EVMM (C:=C) Unit := stackFromTxCtx $ fun ctx => SByteArray.size C.Tb C.BAI ctx.calldata

  def baMemCopyHelper (source : EVMM (C:=C) C.BA) (destOffset offset size : C.Tw) : EVMM (C:=C) Unit := do
    let part := SByteArray.extract C.Tb C.BAI (← source) offset size
    modify $ fun st => {st with memory := EVMMapSeq.setRange C.Tb C.BAI st.memory destOffset size part}

  def i37_calldatacopy : EVMM (C:=C) Unit := withStack3M $ baMemCopyHelper (do return (← get).txCtx.calldata)

  -- def currentCode 

  def i38_codesize : EVMM (C:=C) Unit := do
    let bc ← getOwnBytecode
    pushStack $ SByteArray.size C.Tb C.BAI bc

  def i39_codecopy : EVMM (C:=C) Unit := withStack3M $ baMemCopyHelper getOwnBytecode

  def i3a_gasprice : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.gasprice

  def i3b_extcodesize : EVMM (C:=C) Unit := mapStack1M fun arg => do
    return SByteArray.size C.Tb (A:=C.BA) C.BAI (← getBytecode arg)

  def i3c_extcodecopy : EVMM (C:=C) Unit := do throw EVMException.notImplementedError

  def peekLastReturnData : EVMM (C:=C) (C.Tw × C.BA) := do
    let st ← get
    let Option.some (res : C.Tw × C.BA) := EVMStack.peekn? st.txCtx.returnData 0 | throw EVMException.noReturnDataError
    return res

  def i3d_returndatasize : EVMM (C:=C) Unit := do
    pushStack $ SByteArray.size C.Tb C.BAI (← peekLastReturnData).snd

  def i3e_returndatacopy : EVMM (C:=C) Unit := withStack3M fun destOffset offset size => do
    let (_, returnData) ← peekLastReturnData
    let endd := offset + size
    if Element.ltb (SByteArray.size C.Tb C.BAI returnData) endd then throw EVMException.returnDataOOBError
    baMemCopyHelper (pure returnData) destOffset offset size

  def i3f_extcodehash : EVMM (C:=C) Unit := do throw EVMException.notImplementedError

  def i40_blockhash : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.blockhash

  def i41_coinbase : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.coinbase

  def i42_timestamp : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.timestamp
  def i43_number : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.number
  def i44_difficulty : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.difficulty
  def i45_gaslimit : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.gaslimit
  def i46_chainid : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.chainid
  def i47_selfbalance : EVMM (C:=C) Unit := stackFromTxCtx $ fun ctx => EVMMapDefault.get ctx.balances ctx.address
  def i48_basefee : EVMM (C:=C) Unit := stackFromChainCtx $ fun ctx => ctx.basefee

  def i50_pop : EVMM (C:=C) Unit := do (_:C.Tw) ← popStack; return

  -- def loadFrom (mem: EVMM (C:=C) M) : EVMM (C:=C) C.Tw := do

  def i51_mload : EVMM (C:=C) Unit := do
    let offset ← popStack
    let st ← get
    let d := st.memory
    pushStack $ EVMMap.get32 C.Tb d offset

  def i52_mstore : EVMM (C:=C) Unit := withStack2M fun offset val => do
    modify $ fun st => {st with memory := EVMMap.set32 (K:=C.Tw) C.Tb st.memory offset val}

  def i53_mstore8 : EVMM (C:=C) Unit := withStack2M fun offset val => do
    let byteAsTw := Element.byte (T:=C.Tw) val (Element.ofNat (T:=C.Tw) 31)
    let byte := Element.ofNat (T:=C.Tb) $ Element.toNat byteAsTw
    modify $ fun st => {st with memory := EVMMapBasic.set (K:=C.Tw) (V:=C.Tb) st.memory offset byte}

  def i54_sload : EVMM (C:=C) Unit := do
    let offset ← popStack
    let st ← get
    let d ← getOwnStorage
    pushStack $ EVMMap.get32 C.Tb d offset

  def i55_sstore : EVMM (C:=C) Unit := withStack2M fun offset val => do
    let byteAsTw := Element.byte (T:=C.Tw) val (Element.ofNat (T:=C.Tw) 31)
    let byte := Element.ofNat (T:=C.Tb) $ Element.toNat byteAsTw
    let storage ← getOwnStorage
    modify $ fun st => {st with memory := EVMMapBasic.set (K:=C.Tw) (V:=C.Tb) storage offset byte}

  def i56_jump : EVMM (C:=C) Unit := do jumpTo (← popStack)
  def i57_jumpi : EVMM (C:=C) Unit := do 
        let addr ← popStack
        let condition ← popStack
        if ! Element.iszero condition then
          jumpTo addr

  def i58_pc : EVMM (C:=C) Unit := do pushStack (← get).pc

  def i59_msize : EVMM (C:=C) Unit := do pushStack $ EVMMap.maxKey C.Tb (← get).memory

  def i5a_gas : EVMM (C:=C) Unit := do throw EVMException.notImplementedError
  def i5b_jumpdest : EVMM (C:=C) Unit := pure ()

  -- def pushNBytes (l : Array Byte) : EVMM (C:=C) Unit := l.forM push
  def pushHelper (n : EVM.PushArg) : EVMM (C:=C) Unit := do pushStack $ Element.ofNat $ (UInt256.ofBytes! n.bytes).toNat

  def dupHelper (i : Nat) : EVMM (C:=C) Unit := do let x:C.Tw ← peeknStack i; pushStack x

  def i80_dup1 : EVMM (C:=C) Unit := dupHelper 1

  def i81_dup2 : EVMM (C:=C) Unit := dupHelper 2

  def i82_dup3 : EVMM (C:=C) Unit := dupHelper 3
  def i83_dup4 : EVMM (C:=C) Unit := dupHelper 4
  def i84_dup5 : EVMM (C:=C) Unit := dupHelper 5
  def i85_dup6 : EVMM (C:=C) Unit := dupHelper 6
  def i86_dup7 : EVMM (C:=C) Unit := dupHelper 7
  def i87_dup8 : EVMM (C:=C) Unit := dupHelper 8
  def i88_dup9 : EVMM (C:=C) Unit := dupHelper 9
  def i89_dup10 : EVMM (C:=C) Unit := dupHelper 10
  def i8a_dup11 : EVMM (C:=C) Unit := dupHelper 11
  def i8b_dup12 : EVMM (C:=C) Unit := dupHelper 12
  def i8c_dup13 : EVMM (C:=C) Unit := dupHelper 13
  def i8d_dup14 : EVMM (C:=C) Unit := dupHelper 14
  def i8e_dup15 : EVMM (C:=C) Unit := dupHelper 15
  def i8f_dup16 : EVMM (C:=C) Unit := dupHelper 16

  def swapHelper (i : Nat) : EVMM (C:=C) Unit := do
    let a ← peeknStack (i+1)
    let b ← peeknStack 0
    setStack (i+1) b
    setStack 0 a
    -- pure ()

  def logHelper (i : Fin 5) : EVMM (C:=C) Unit := do throw EVMException.notImplementedError

  def if3_return : EVMM (C:=C) Unit := withStack2M fun offset size => do
    let st ← get
    let bits := EVMMapSeq.getRange (BA:=C.BA) C.Tb C.BAI st.memory offset size
    returnWith 0 bits

  -- instance [SByteArray]

  def debug_getIter : EVMM (C:=C) C.BAI := do
    let st ← get
    return SByteArray.toIterAt C.Tb (← getOwnBytecode) st.pc

  def getNextInstr : EVMM (C:=C) (Instruction × C.Tw) := do
    let st ← get
    let bc : C.BAI := SByteArray.toIterAt C.Tb (← getOwnBytecode) st.pc
    let (instrO, pcDiff) := EVM.decode bc
    let Option.some instr := instrO | throw EVMException.invalidInstructionError
    return (instr, st.pc + Element.ofNat pcDiff)

  def setPC (val : C.Tw): EVMM (C:=C) Unit := do
    modify $ fun st => {st with pc := val}
  
  def isDone : EVMM (C:=C) Bool := do return (← get).returnData.isSome

  def step : EVMM (C:=C) Unit := do 
    if (← isDone) then throw EVMException.alreadyReturnedError
    let currPC := (← get).pc
    let (instr, newPC) ← getNextInstr
    setPC newPC
    -- dbgTrace s!"PC: {Element.toNat currPC}, instr: {repr instr}" fun () =>
    match instr with
    | Instruction.expr e => match e with
      | InstrExpr.IAdd => i01_add
      | InstrExpr.IMul => i02_mul
      | InstrExpr.ISub => i03_sub
      | InstrExpr.IDiv => i04_div
      | InstrExpr.ISdiv => i05_sdiv
      | InstrExpr.IMod => i06_mod
      | InstrExpr.ISmod => i07_smod
      | InstrExpr.IAddmod => i08_addmod
      | InstrExpr.IMulmod => i09_mulmod
      | InstrExpr.IExp => i0a_exp
      | InstrExpr.ISignextend => i0b_signextend
      | InstrExpr.ILt => i10_lt
      | InstrExpr.IGt => i11_gt
      | InstrExpr.ISlt => i12_slt
      | InstrExpr.ISgt => i13_sgt
      | InstrExpr.IEq => i14_eq
      | InstrExpr.IIszero => i15_iszero
      | InstrExpr.IAnd => i16_and
      | InstrExpr.IOr => i17_or
      | InstrExpr.IXor => i18_xor
      | InstrExpr.INot => i19_not
      | InstrExpr.IByte => i1a_byte
      | InstrExpr.IShl => i1b_shl
      | InstrExpr.IShr => i1c_shr
      | InstrExpr.ISar => i1d_sar
      | InstrExpr.ISha3 => i20_sha3
    | Instruction.ctxt e => match e with
      | InstrCtxt.IAddress => i30_address
      | InstrCtxt.IBalance => i31_balance
      | InstrCtxt.IOrigin => i32_origin
      | InstrCtxt.ICaller => i33_caller
      | InstrCtxt.ICallvalue => i34_callvalue
      | InstrCtxt.ICalldataload => i35_calldataload
      | InstrCtxt.ICalldatasize => i36_calldatasize
      | InstrCtxt.ICalldatacopy => i37_calldatacopy
      | InstrCtxt.ICodesize => i38_codesize
      | InstrCtxt.ICodecopy => i39_codecopy
      | InstrCtxt.IGasprice => i3a_gasprice
      | InstrCtxt.IExtcodesize => i3b_extcodesize
      | InstrCtxt.IExtcodecopy => i3c_extcodecopy
      | InstrCtxt.IReturndatasize => i3d_returndatasize
      | InstrCtxt.IReturndatacopy => i3e_returndatacopy
      | InstrCtxt.IExtcodehash => i3f_extcodehash
      | InstrCtxt.IBlockhash => i40_blockhash
      | InstrCtxt.ICoinbase => i41_coinbase
      | InstrCtxt.ITimestamp => i42_timestamp
      | InstrCtxt.INumber => i43_number
      | InstrCtxt.IDifficulty => i44_difficulty
      | InstrCtxt.IGaslimit => i45_gaslimit
      | InstrCtxt.IChainid => i46_chainid
      | InstrCtxt.ISelfbalance => i47_selfbalance
      | InstrCtxt.IBasefee => i48_basefee
    | Instruction.mem e => match e with
      | InstrMem.IPop => i50_pop
      | InstrMem.IMload => i51_mload
      | InstrMem.IMstore => i52_mstore
      | InstrMem.IMstore8 => i53_mstore8
      | InstrMem.ISload => i54_sload
      | InstrMem.ISstore => i55_sstore
    | Instruction.other e => match e with
      | InstrOther.IStop => i00_stop
      | InstrOther.IJump => i56_jump
      | InstrOther.IJumpi => i57_jumpi
      | InstrOther.IPc => i58_pc
      | InstrOther.IMsize => i59_msize
      | InstrOther.IGas => i5a_gas
      | InstrOther.IJumpdest => pure ()
      | InstrOther.IPush arg => pushHelper arg
      | InstrOther.IDup idx => dupHelper idx
      | InstrOther.ISwap idx => swapHelper idx
      | InstrOther.ILog idx => logHelper idx
      | InstrOther.ICreate => do throw EVMException.notImplementedError
      | InstrOther.ICall => do throw EVMException.notImplementedError
      | InstrOther.ICallcode => do throw EVMException.notImplementedError
      | InstrOther.IReturn => if3_return
      | InstrOther.IDelegatecall => do throw EVMException.notImplementedError
      | InstrOther.ICreate2 => do throw EVMException.notImplementedError
      | InstrOther.IStaticcall => do throw EVMException.notImplementedError
      | InstrOther.IRevert => do throw EVMException.notImplementedError
      | InstrOther.IInvalid => do throw EVMException.invalidInstructionError
      | InstrOther.ISelfdestruct => do throw EVMException.notImplementedError

    pure ()

end EVMM