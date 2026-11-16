module

public import HelloWorld.Value

open Value

namespace CheckedLang

public structure FunctionSignature where
  inputs : List ValueTag
  output : ValueTag
deriving DecidableEq

public abbrev EnvironmentSymbols := Array (String × FunctionSignature)

@[expose] public def EnvironmentSymbols.get (env : EnvironmentSymbols) (slot : Fin env.size)
    : String × FunctionSignature :=
  env[slot.val]

public def EnvironmentSymbols.find? (env : EnvironmentSymbols) (name : String)
    : Option (Fin env.size) :=
  (Array.ofFn (fun slot : Fin env.size => (slot, env.get slot))).findSome?
    (fun entry => if entry.2.1 == name then some entry.1 else none)

public structure FunctionReference (symbols : EnvironmentSymbols) where
  debug_name : String
  function_slot : Fin symbols.size

@[expose] public def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

@[expose] public def listSet? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => (listSet? xs n v).map (x :: ·)

end CheckedLang
