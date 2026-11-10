module

import Mathlib.Data.Nat.Bits
import Aesop

public import HelloWorld.Value

open Value

namespace BaseLang

public inductive Expr where
  | atom {tag : ValueTag} (val : Value tag)
  | add (lhs : Expr) (rhs : Expr)
  | sub (lhs : Expr) (rhs : Expr)

end BaseLang
