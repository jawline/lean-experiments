module

import Mathlib.Data.Nat.Bits
import Aesop

public import HelloWorld.Value
public import HelloWorld.BinOp
public import HelloWorld.Comparison

open Value

namespace BaseLang

public inductive Expr where
  | atom {tag : ValueTag} (val : Value tag)
  | allocate (n : Nat)
  | deallocate (n : Nat)
  | get (n : Nat)
  | set (n : Nat) (e : Expr)
  | binOp (op : ArithmeticBinOp) (lhs : Expr) (rhs : Expr)
  | branch (cmp : Expr) (lhs : Expr) (rhs : Expr) 

end BaseLang
