module

import Mathlib.Data.Nat.Bits
import Aesop
public import HelloWorld.Value

open Value

namespace BaseLang

public inductive Expr where
  | atom (val : Value)
  | add (lhs : Expr) (rhs : Expr)
  | sub (lhs : Expr) (rhs : Expr)

end BaseLang
