import Contractome.Utils
import Contractome.UInt256

import Lean.Data.JsonRpc
import Lean.Data.Json.FromToJson

open Lean.JsonRpc
open Lean (FromJson Json)


-- structure setChainParamsArgs where
--   sealEngine : String
--   params: 

local instance : FromJson ByteArray where
  fromJson? j := match j with
  | Json.str s => Id.run do
    let cropped := if s.substrEq 0 "0x" 0 2 then s.drop 2 else s
    let Option.some r := hexToByteArray cropped | return Except.error "Invalid hex string when parsing bytearray"
    Except.ok r
  | _ => Except.error "Not a hex string"

local instance : FromJson UInt256 where
  fromJson? j := match j with
  | Json.str s => Id.run do
    let cropped := if s.substrEq 0 "0x" 0 2 then s.drop 2 else s
    let Option.some r := hexToByteArray cropped | return Except.error "Invalid hex string when parsing bytearray"
    Except.ok $ UInt256.ofBytes! r
  | _ => Except.error "Not a hex string"

structure AccountStatus where
  balance : ByteArray
  code : ByteArray
  nonce : UInt256
  -- params : TODO
deriving FromJson



structure GenesisStatus where
  author : UInt256
  difficulty : UInt256
  gasLimit : UInt256
  nonce : UInt256
  extraData : ByteArray
  timestamp : UInt256
  mixHash : UInt256
  number : UInt256
  -- TODO genesisSeal

def exampleString := "Asdfasdf"

def processMessage (m : Message) : (ExceptT String Id) String := match m with
  | Message.request id method params => 
    match method with
    | "test_setChainParams" => pure ""
    | _ => throw "asdf"
  | _ => throw "Not a request"


def toParams (s : String) : IO Message := do
  let msg ← IO.ofExcept $ Json.parse s
  let p ← IO.ofExcept $ FromJson.fromJson? msg
  -- let Except.ok p := FromJson.fromJson? s | return none
  return p