module

public import HelloWorld.Value
public import HelloWorld.BinOp

import HelloWorld.BaseLang
import Aesop

open Value
open BaseLang

namespace CheckedLang

-- A TypeChecked BaseLang.Expr
inductive CheckedExpr : ValueTag → Type where
  | atom {tag : ValueTag } (val : Value tag) : CheckedExpr tag
  | binOp {tag : ValueTag} (op : BinOp) (lhs : CheckedExpr tag)
    (rhs : CheckedExpr tag) (h : op.is_legal_operation_for_type tag = true)
    : CheckedExpr (op.resultTag tag)
  | allocate (n : Nat) : CheckedExpr .unit
  | deallocate (n : Nat) : CheckedExpr .unit
  | get {tag : ValueTag} (n : Nat) : CheckedExpr tag
  | set (n : Nat) {tag : ValueTag} (e : CheckedExpr tag) : CheckedExpr .unit
  | branch {tag : ValueTag} (cmp : CheckedExpr .bool)
    (lhs : CheckedExpr tag) (rhs : CheckedExpr tag) : CheckedExpr tag

structure FunctionReference where
  debug_name : String
  function_slot : Nat

structure TypedExpr where
  tag : ValueTag
  expr : CheckedExpr tag

/-- The types of the cells currently on the stack, with the top of the stack
at the head of the list. -/
abbrev StackCtx := List ValueTag

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

def listSet? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => (listSet? xs n v).map (x :: ·)

def ensure (p : Prop) [Decidable p] (err : String) : Except String (PLift p) :=
  if h : p then Except.ok ⟨h⟩ else Except.error err

def ensureBinOp (op : BinOp) (lhs rhs : ValueTag)
    : Except String (PLift (lhs = rhs ∧ op.is_legal_operation_for_type lhs = true)) := do
  let ⟨h⟩ ← ensure (lhs = rhs) "Binary operation is illegal on values of different types"
  let ⟨q⟩ ← ensure (op.is_legal_operation_for_type lhs = true) "Binary operation is illegal on this type"
  return ⟨⟨h, q⟩⟩

def constructBinOp (op : BinOp) (lhs rhs : TypedExpr)
    : Except String TypedExpr := do
  let ⟨lt, le⟩ := lhs
  let ⟨rt, re⟩ := rhs
  let ⟨h, q⟩ ← ensureBinOp op lt rt
  return ⟨op.resultTag lt, .binOp op le (h.symm ▸ re) q⟩

def typecheckWith (ctx : StackCtx) : Expr → Except String (TypedExpr × StackCtx)
  | .atom (tag := tag) val => Except.ok (⟨tag, .atom val⟩, ctx)
  | .allocate n =>
      Except.ok (⟨.unit, .allocate n⟩, List.replicate n .empty ++ ctx)
  | .deallocate n =>
      if n ≤ ctx.length then
        Except.ok (⟨.unit, .deallocate n⟩, ctx.drop n)
      else
        Except.error "Deallocate exceeds the current stack size"
  | .get n =>
      match listGet? ctx n with
      | none => Except.error "Get index is out of bounds"
      | some .empty => Except.error "Get on an empty cell"
      | some tag => Except.ok (⟨tag, .get n⟩, ctx)
  | .set n e => do
      let ⟨et, ctx1⟩ ← typecheckWith ctx e
      let ⟨etag, eexpr⟩ := et
      match listSet? ctx1 n etag with
      | none => Except.error "Set index is out of bounds"
      | some ctx' => Except.ok (⟨.unit, .set n eexpr⟩, ctx')
  | .binOp op lhs rhs => do
      let ⟨lhsT, ctx1⟩ ← typecheckWith ctx lhs
      let ⟨rhsT, ctx2⟩ ← typecheckWith ctx1 rhs
      let result ← constructBinOp op lhsT rhsT
      Except.ok (result, ctx2)
  | .branch cmp lhs rhs => do
      let ⟨⟨ct, cexpr⟩, ctx1⟩ ← typecheckWith ctx cmp
      let ⟨hbool⟩ ← ensure (ct = .bool) "Branch condition must be a bool"
      let cexpr : CheckedExpr .bool := hbool ▸ cexpr
      let ⟨⟨lt, lexpr⟩, lctx⟩ ← typecheckWith ctx1 lhs
      let ⟨⟨rt, rexpr⟩, rctx⟩ ← typecheckWith ctx1 rhs
      let ⟨htag⟩ ← ensure (lt = rt) "Branch arms must have the same type"
      let ⟨_hctx⟩ ← ensure (lctx = rctx) "Branch arms must leave the stack in the same state"
      return (⟨lt, .branch cexpr lexpr (htag.symm ▸ rexpr)⟩, lctx)

def typecheck (e : Expr) (ctx : StackCtx := []) : Except String (TypedExpr × StackCtx) :=
  typecheckWith ctx e

abbrev RuntimeCell := Option (Σ tag : ValueTag, Value tag)
abbrev RuntimeStack := List RuntimeCell

def evalChecked : {tag : ValueTag} → CheckedExpr tag → RuntimeStack
    → Except String (Value tag × RuntimeStack)
  | _, .atom val, stack => Except.ok (val, stack)
  | _, .binOp (tag := operandTag) op lhs rhs is_legal, stack => do
      let (lv, stack1) ← evalChecked lhs stack
      let (rv, stack2) ← evalChecked rhs stack1
      return (BinOp.implementation op operandTag is_legal lv rv, stack2)
  | _, .allocate n, stack =>
      Except.ok (.unitVal, List.replicate n (none : RuntimeCell) ++ stack)
  | _, .deallocate n, stack =>
      if n ≤ stack.length then
        Except.ok (.unitVal, stack.drop n)
      else
        Except.error "Deallocate exceeds the current stack size"
  | _, .get (tag := tag) n, stack =>
      match listGet? stack n with
      | none => Except.error "Get index is out of bounds"
      | some none => Except.error "Get on an empty cell"
      | some (some ⟨cellTag, val⟩) =>
          if h : cellTag = tag then
            Except.ok (h ▸ val, stack)
          else
            Except.error "Get found a value of the wrong type"
  | _, .set (tag := tag) n e, stack => do
      let (val, stack1) ← evalChecked e stack
      match listSet? stack1 n (some ⟨tag, val⟩ : RuntimeCell) with
      | none => Except.error "Set index is out of bounds"
      | some stack2 => Except.ok (.unitVal, stack2)
  | _, .branch cmp lhs rhs, stack => do
      let (cond, stack1) ← evalChecked cmp stack
      match cond with
      | .boolVal b =>
          if b then evalChecked lhs stack1 else evalChecked rhs stack1

def eval (k : TypedExpr) (stack : RuntimeStack := [])
    : Except String (Value k.tag × RuntimeStack) :=
  evalChecked k.expr stack

end CheckedLang
