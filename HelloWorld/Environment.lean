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

end CheckedLang
