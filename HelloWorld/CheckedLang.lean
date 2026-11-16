module

public import HelloWorld.Value
public import HelloWorld.BinOp
public import HelloWorld.Comparison

import HelloWorld.BaseLang
import Aesop

open Value
open BaseLang

namespace CheckedLang

-- A TypeChecked BaseLang.Expr
inductive CheckedExpr : ValueTag → Type where
  | atom {tag : ValueTag } (val : Value tag) : CheckedExpr tag
  | arithmeticBinOp {tag : ValueTag} (op : ArithmeticBinOp) (lhs : CheckedExpr tag)
    (rhs : CheckedExpr tag) (h : op.is_legal_operation_for_type tag = true)
    : CheckedExpr tag

structure TypedExpr where
  tag : ValueTag
  expr : CheckedExpr tag

def ensure (p : Prop) [Decidable p] (err : String) : Except String (PLift p) :=
  if h : p then Except.ok ⟨h⟩ else Except.error err

def ensureArithmetic (op : ArithmeticBinOp) (lhs rhs : ValueTag)
    : Except String (PLift (lhs = rhs ∧ op.is_legal_operation_for_type lhs = true)) := do
  let ⟨h⟩ ← ensure (lhs = rhs) "Arithmetic is illegal on values of different types"
  let ⟨q⟩ ← ensure (op.is_legal_operation_for_type lhs = true) "Arithmetic is illegal on bools"
  return ⟨⟨h, q⟩⟩

abbrev ArithCtor (op : ArithmeticBinOp) :=
  {tag : ValueTag}
  → CheckedExpr tag → CheckedExpr tag → op.is_legal_operation_for_type tag = true → CheckedExpr tag

def constructArithmetic (op : ArithmeticBinOp) (lhs rhs : TypedExpr)
    : Except String TypedExpr := do
  let ⟨lt, le⟩ := lhs
  let ⟨rt, re⟩ := rhs
  let ⟨h, q⟩ ← ensureArithmetic op lt rt
  return ⟨lt, .arithmeticBinOp op le (h.symm ▸ re) q⟩

def typecheck : Expr → Except String TypedExpr
  | .atom (tag := tag) val => Except.ok (⟨tag, .atom val⟩)
  | .binOp op lhs rhs => do
      constructArithmetic op (← typecheck lhs) (← typecheck rhs)
  | .allocate _ => sorry
  | .deallocate _ => sorry
  | .get _ => sorry
  | .set _ _ => sorry
  | .branch _ _ _ => sorry

def evalChecked : {tag : ValueTag} → CheckedExpr tag → Value tag
  | _, .atom val => val
  | _, .arithmeticBinOp op lhs rhs is_legal =>
      Value.binOp op (ArithmeticBinOp.implementation op) (evalChecked lhs) (evalChecked rhs)
        is_legal

def eval (k : TypedExpr) : Value k.tag :=
  evalChecked k.expr

end CheckedLang
