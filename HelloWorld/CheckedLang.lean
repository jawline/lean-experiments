module

public import HelloWorld.Value
import HelloWorld.BaseLang
import Aesop

open Value
open BaseLang

namespace CheckedLang

-- A TypeChecked BaseLang.Expr
inductive CheckedExpr : ValueTag → Type where
  | atom (val : Value) : CheckedExpr val.tag
  | add {tag : ValueTag} (lhs : CheckedExpr tag) (rhs : CheckedExpr tag) (h : tag.is_arithmetic = true) : CheckedExpr tag
  | sub {tag : ValueTag} (lhs : CheckedExpr tag) (rhs : CheckedExpr tag) (h : tag.is_arithmetic = true) : CheckedExpr tag


structure TypedExpr where
  tag : ValueTag
  expr : CheckedExpr tag

 
def ensure (p : Prop) [Decidable p] (err : String) : Except String (PLift p) :=
  if h : p then Except.ok ⟨h⟩ else Except.error err

def ensureArithmetic (lhs rhs : ValueTag) :
    Except String (PLift (lhs = rhs ∧ lhs.is_arithmetic)) := do
  let ⟨h⟩ ← ensure (lhs = rhs) "Add is illegal on values of different types"
  let ⟨q⟩ ← ensure (lhs.is_arithmetic) "Add is illegal on bools"
  return ⟨⟨h, q⟩⟩

abbrev ArithCtor :=
  {tag : ValueTag} →
  CheckedExpr tag → CheckedExpr tag → tag.is_arithmetic = true → CheckedExpr tag

def constructArithmetic (mk : ArithCtor) (lhs rhs : TypedExpr) :
    Except String TypedExpr := do
  let ⟨lt, le⟩ := lhs
  let ⟨rt, re⟩ := rhs
  let ⟨h, q⟩ ← ensureArithmetic lt rt
  return ⟨lt, mk le (h.symm ▸ re) q⟩

def typecheck : Expr → Except String TypedExpr
  | .atom val => Except.ok (⟨val.tag, .atom val⟩)
  | .add lhs rhs => do
    constructArithmetic CheckedExpr.add (← typecheck lhs) (← typecheck rhs)
  | .sub lhs rhs => do
    constructArithmetic CheckedExpr.sub (← typecheck lhs) (← typecheck rhs)

def binOp (fi : Int32 → Int32 → Int32) (ff : Float32 → Float32 → Float32) :
    Value → Value → Value
  | .unit, .unit => .unit
  | .i32 a, .i32 b => .i32 (fi a b)
  | .f32 a, .f32 b => .f32 (ff a b)
  | _, _ => .unit

def evalChecked : {tag : ValueTag} → CheckedExpr tag → Value
  | _, .atom val => val
  | _, .add lhs rhs _ => binOp (· + ·) (· + ·) (evalChecked lhs) (evalChecked rhs)
  | _, .sub lhs rhs _ => binOp (· - ·) (· - ·) (evalChecked lhs) (evalChecked rhs)
  

def eval (k : TypedExpr) : Value :=
  evalChecked k.expr

end CheckedLang 
