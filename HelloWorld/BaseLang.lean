module

import Mathlib.Data.Nat.Bits
import Aesop

public import HelloWorld.Value
public import HelloWorld.BinOp

open Value

namespace BaseLang

public inductive Expr where
  | atom {tag : ValueTag} (val : Value tag)
  | allocate (n : Nat)
  | deallocate (n : Nat)
  | get (n : Nat)
  | set (n : Nat) (e : Expr)
  | binOp (op : BinOp) (lhs : Expr) (rhs : Expr)
  | branch (cmp : Expr) (lhs : Expr) (rhs : Expr) 
  | call (functionName : String) (arguments : List Expr)

end BaseLang
