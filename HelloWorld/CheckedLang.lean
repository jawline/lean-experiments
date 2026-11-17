module

public import HelloWorld.Value
public import HelloWorld.BinOp
public import HelloWorld.Environment
public import HelloWorld.BaseLang
public import HelloWorld.RuntimeStack

import Aesop

open Value
open BaseLang

namespace CheckedLang

public def Value.default : (tag : ValueTag) → tag ≠ .undefined → Value tag
  | .undefined, h => (h rfl).elim
  | .unit, _ => .unitVal
  | .i32, _ => .i32Val 0
  | .f32, _ => .f32Val 0
  | .bool, _ => .boolVal false

public theorem binOp_resultTag_ne_undefined {op : BinOp} {tag : ValueTag}
    (h : op.is_legal_operation_for_type tag = true) :
    op.resultTag tag ≠ .undefined := by
  cases op with
  | arithmeticBinOp aop =>
      cases tag with
      | undefined =>
          simp [BinOp.is_legal_operation_for_type,
            ArithmeticBinOp.is_legal_operation_for_type] at h
      | unit => simp [BinOp.resultTag]
      | i32 => simp [BinOp.resultTag]
      | f32 => simp [BinOp.resultTag]
      | bool =>
          simp [BinOp.is_legal_operation_for_type,
            ArithmeticBinOp.is_legal_operation_for_type] at h
  | comparisonBinOp cop => simp [BinOp.resultTag]

mutual
  public inductive CheckedExpr (symbols : EnvironmentSymbols) :
      StackCtx → ValueTag → StackCtx → Type where
    | atom {ctx : StackCtx} {tag : ValueTag} (val : Value tag) :
        CheckedExpr symbols ctx tag ctx
    | binOp {ctx ctx1 ctx2 : StackCtx} {tag : ValueTag} (op : BinOp)
        (lhs : CheckedExpr symbols ctx tag ctx1)
        (rhs : CheckedExpr symbols ctx1 tag ctx2)
        (h : op.is_legal_operation_for_type tag = true) :
        CheckedExpr symbols ctx (op.resultTag tag) ctx2
    | allocate {ctx : StackCtx} (n : Nat) :
        CheckedExpr symbols ctx .unit (List.replicate n .undefined ++ ctx)
    | deallocate {ctx : StackCtx} (n : Nat) (h : n ≤ ctx.length) :
        CheckedExpr symbols ctx .unit (ctx.drop n)
    | get {ctx : StackCtx} {tag : ValueTag} (n : Nat)
        (h : ctx[n]? = some tag) (hne : tag ≠ .undefined) :
        CheckedExpr symbols ctx tag ctx
    | set {ctx ctx1 : StackCtx} {tag : ValueTag} (n : Nat)
        (e : CheckedExpr symbols ctx tag ctx1)
        (hn : n < ctx1.length) :
        CheckedExpr symbols ctx .unit (ctx1.set n tag)
    | branch {ctx ctx1 ctx2 : StackCtx} {tag : ValueTag}
        (cmp : CheckedExpr symbols ctx .bool ctx1)
        (lhs : CheckedExpr symbols ctx1 tag ctx2)
        (rhs : CheckedExpr symbols ctx1 tag ctx2) :
        CheckedExpr symbols ctx tag ctx2
    | call {ctx ctx' : StackCtx} (function : FunctionReference symbols)
        (arguments : CheckedArgs symbols ctx (symbols.get function.function_slot).2.inputs ctx')
        (hout : (symbols.get function.function_slot).2.output ≠ .undefined) :
        CheckedExpr symbols ctx (symbols.get function.function_slot).2.output ctx'

  public inductive CheckedArgs (symbols : EnvironmentSymbols) :
      StackCtx → List ValueTag → StackCtx → Type where
    | nil {ctx : StackCtx} : CheckedArgs symbols ctx [] ctx
    | cons {ctx ctx1 ctx2 : StackCtx} {tag : ValueTag} {tags : List ValueTag}
        (arg : CheckedExpr symbols ctx tag ctx1)
        (rest : CheckedArgs symbols ctx1 tags ctx2) :
        CheckedArgs symbols ctx (tag :: tags) ctx2
end

public structure TypedExpr (symbols : EnvironmentSymbols) (ctx : StackCtx) where
  tag : ValueTag
  outputCtx : StackCtx
  expr : CheckedExpr symbols ctx tag outputCtx

public theorem CheckedExpr.nonemptyTag {symbols : EnvironmentSymbols}
    {ctx : StackCtx} {tag : ValueTag} {ctx' : StackCtx} :
    CheckedExpr symbols ctx tag ctx' → Nonempty (Value tag)
  | .atom val => ⟨val⟩
  | .binOp op _ _ h => ⟨Value.default _ (binOp_resultTag_ne_undefined h)⟩
  | .allocate _ => ⟨.unitVal⟩
  | .deallocate _ _ => ⟨.unitVal⟩
  | .get _ _ hne => ⟨Value.default _ hne⟩
  | .set _ _ _ => ⟨.unitVal⟩
  | .branch _ lhs _ => CheckedExpr.nonemptyTag lhs
  | .call _ _ hout => ⟨Value.default _ hout⟩

public def ensure (p : Prop) [Decidable p] (err : String) : Except String (PLift p) :=
  if h : p then Except.ok ⟨h⟩ else Except.error err

public def ensureBinOp (op : BinOp) (lhs rhs : ValueTag)
    : Except String (PLift (lhs = rhs ∧ op.is_legal_operation_for_type lhs = true)) := do
  let ⟨h⟩ ← ensure (lhs = rhs) "Binary operation is illegal on values of different types"
  let ⟨q⟩ ← ensure (op.is_legal_operation_for_type lhs = true) "Binary operation is illegal on this type"
  return ⟨⟨h, q⟩⟩

public def constructBinOp (symbols : EnvironmentSymbols) (op : BinOp) {ctx : StackCtx}
    (lhs : TypedExpr symbols ctx) (rhs : TypedExpr symbols lhs.outputCtx)
    : Except String (TypedExpr symbols ctx) := do
  let ⟨h, q⟩ ← ensureBinOp op lhs.tag rhs.tag
  let rhsExpr : CheckedExpr symbols lhs.outputCtx lhs.tag rhs.outputCtx :=
    h.symm ▸ rhs.expr
  return ⟨op.resultTag lhs.tag, rhs.outputCtx, .binOp op lhs.expr rhsExpr q⟩

public def typecheckWith (symbols : EnvironmentSymbols) (ctx : StackCtx) :
    Expr → Except String (TypedExpr symbols ctx)
  | .atom (tag := tag) val => Except.ok ⟨tag, ctx, .atom val⟩
  | .allocate n =>
      Except.ok ⟨.unit, List.replicate n .undefined ++ ctx, .allocate n⟩
  | .deallocate n =>
      if h : n ≤ ctx.length then
        Except.ok ⟨.unit, ctx.drop n, .deallocate n h⟩
      else
        Except.error "Deallocate exceeds the current frame size"
  | .get n =>
      match h : ctx[n]? with
      | none => Except.error "Get index is out of bounds"
      | some tag =>
          if hne : tag = .undefined then
            Except.error "Get on an undefined cell"
          else
            Except.ok ⟨tag, ctx, .get n h hne⟩
  | .set n e => do
      let eT ← typecheckWith symbols ctx e
      if hn : n < eT.outputCtx.length then
        Except.ok ⟨.unit, eT.outputCtx.set n eT.tag, .set n eT.expr hn⟩
      else
        Except.error "Set index is out of bounds"
  | .binOp op lhs rhs => do
      let lhsT ← typecheckWith symbols ctx lhs
      let rhsT ← typecheckWith symbols lhsT.outputCtx rhs
      constructBinOp symbols op lhsT rhsT
  | .branch cmp lhs rhs => do
      let cmpT ← typecheckWith symbols ctx cmp
      let ⟨hbool⟩ ← ensure (cmpT.tag = .bool) "Branch condition must be a bool"
      let cmpExpr : CheckedExpr symbols ctx .bool cmpT.outputCtx := hbool ▸ cmpT.expr
      let lhsT ← typecheckWith symbols cmpT.outputCtx lhs
      let rhsT ← typecheckWith symbols cmpT.outputCtx rhs
      let ⟨htag⟩ ← ensure (lhsT.tag = rhsT.tag) "Branch arms must have the same type"
      let ⟨hctx⟩ ← ensure (lhsT.outputCtx = rhsT.outputCtx)
        "Branch arms must leave the stack in the same state"
      let rhsExpr : CheckedExpr symbols cmpT.outputCtx lhsT.tag lhsT.outputCtx :=
        htag.symm ▸ hctx.symm ▸ rhsT.expr
      return ⟨lhsT.tag, lhsT.outputCtx, .branch cmpExpr lhsT.expr rhsExpr⟩
  | .call functionName arguments => do
      let slot ← match symbols.find? functionName with
        | some slot => Except.ok slot
        | none => Except.error s!"Unknown function: {functionName}"
      let sig := (symbols.get slot).2
      let rec go (args : List Expr) (expected : List ValueTag) (ctx : StackCtx) :
          Except String (Σ ctx' : StackCtx, CheckedArgs symbols ctx expected ctx') :=
        match args, expected with
        | [], [] => Except.ok ⟨ctx, .nil⟩
        | [], _ :: _ => Except.error "Too few arguments in call"
        | _ :: _, [] => Except.error "Too many arguments in call"
        | arg :: args, expectedTag :: expected => do
            let argT ← typecheckWith symbols ctx arg
            let ⟨h⟩ ← ensure (argT.tag = expectedTag)
              "Call argument type does not match the function signature"
            let ⟨ctx', rest⟩ ← go args expected argT.outputCtx
            let argExpr : CheckedExpr symbols ctx expectedTag argT.outputCtx :=
              h ▸ argT.expr
            return ⟨ctx', .cons argExpr rest⟩
      let ⟨ctx', checkedArgs⟩ ← go arguments sig.inputs ctx
      let ⟨hout⟩ ← ensure (sig.output ≠ .undefined) "Function output type cannot be undefined"
      let ref : FunctionReference symbols :=
        { debug_name := functionName, function_slot := slot }
      return ⟨sig.output, ctx', .call ref checkedArgs hout⟩

public def typecheck (symbols : EnvironmentSymbols) (e : Expr) (ctx : StackCtx := [])
    : Except String (TypedExpr symbols ctx) :=
  typecheckWith symbols ctx e

public def typecheckIn (symbols : EnvironmentSymbols) (e : Expr) (ctx : StackCtx := [])
    : Except String (TypedExpr symbols ctx) :=
  typecheckWith symbols ctx e

public structure CheckedFunction (symbols : EnvironmentSymbols) (sig : FunctionSignature) where
  outputCtx : StackCtx
  body : CheckedExpr symbols sig.inputs sig.output outputCtx

public def typecheckFunction (symbols : EnvironmentSymbols) (sig : FunctionSignature)
    (body : Expr) : Except String (CheckedFunction symbols sig) := do
  let typed ← typecheckWith symbols sig.inputs body
  let ⟨h⟩ ← ensure (typed.tag = sig.output)
    "Function body does not match its declared output type"
  let bodyExpr : CheckedExpr symbols sig.inputs sig.output typed.outputCtx :=
    h ▸ typed.expr
  return ⟨typed.outputCtx, bodyExpr⟩

public structure CheckedImplementation (symbols : EnvironmentSymbols) where
  slot : Fin symbols.size
  function : CheckedFunction symbols (symbols.get slot).2

public structure EnvironmentWithImplementation (symbols : EnvironmentSymbols) where
  implementations : Vector (CheckedImplementation symbols) symbols.size
  h_slot : ∀ (i : Fin symbols.size),
    (implementations[i.val]'i.isLt).slot = i

private structure AlignedImplementations (symbols : EnvironmentSymbols) (n : Nat)
    (h_n : n ≤ symbols.size) where
  implementations : Vector (CheckedImplementation symbols) n
  h_slot : ∀ (i : Fin n),
    (implementations[i.val]'i.isLt).slot =
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_n⟩

private def buildAlignedImplementations (symbols : EnvironmentSymbols) (bodies : Array Expr)
    (h_size : bodies.size = symbols.size) :
    (n : Nat) → (h_n : n ≤ symbols.size) →
      Except String (AlignedImplementations symbols n h_n)
  | 0, _h_n => Except.ok
      { implementations := Vector.mk #[] rfl
        h_slot := by intro i; exact i.elim0 }
  | n + 1, h_n => do
      let prev ← buildAlignedImplementations symbols bodies h_size n
        (Nat.le_of_succ_le h_n)
      let hn : n < symbols.size := Nat.lt_of_succ_le h_n
      let slot : Fin symbols.size := ⟨n, hn⟩
      let body := bodies[n]'(by simpa [h_size] using hn)
      let checked ← typecheckFunction symbols (symbols.get slot).2 body
      let implementation : CheckedImplementation symbols := ⟨slot, checked⟩
      let implementations := prev.implementations.push implementation
      return ({
        implementations := implementations
        h_slot := by
          intro i
          by_cases hi : i.val < n
          · have hget : (implementations[i.val]'i.isLt) =
                prev.implementations[i.val]'hi := by
              simp [implementations, Vector.getElem_push_lt, hi]
            rw [hget]
            have hprev := prev.h_slot ⟨i.val, hi⟩
            rw [hprev]
          · obtain ⟨iv, hiv⟩ := i
            have hival : iv = n := Nat.eq_of_lt_succ_of_not_lt hiv hi
            have hget : (implementations[iv]'hiv) = implementation := by
              subst hival
              simp [implementations, Vector.getElem_push_eq]
            rw [hget]
            apply Fin.ext
            exact hival.symm
      } : AlignedImplementations symbols (n + 1) h_n)

private def AlignedImplementations.toEnvironment {symbols : EnvironmentSymbols}
    (aligned : AlignedImplementations symbols symbols.size (Nat.le_refl _)) :
    EnvironmentWithImplementation symbols :=
  { implementations := aligned.implementations
    h_slot := by
      intro i
      have h := aligned.h_slot i
      simpa [Fin.eta] using h }

public def EnvironmentWithImplementation.get {symbols : EnvironmentSymbols}
    (env : EnvironmentWithImplementation symbols) (slot : Fin symbols.size)
    : CheckedFunction symbols (symbols.get slot).2 :=
  have hslot : (env.implementations[slot.val]'slot.isLt).slot = slot :=
    env.h_slot slot
  hslot ▸ (env.implementations[slot.val]'slot.isLt).function

public def EnvironmentWithImplementation.build (symbols : EnvironmentSymbols) (bodies : Array Expr)
    (h_size : bodies.size = symbols.size) : Except String (EnvironmentWithImplementation symbols) := do
  let aligned ← buildAlignedImplementations symbols bodies h_size symbols.size (Nat.le_refl _)
  return aligned.toEnvironment

mutual
  public partial def evalChecked {symbols : EnvironmentSymbols}
      (env : EnvironmentWithImplementation symbols)
      {ctx : StackCtx} {tag : ValueTag} {ctx' : StackCtx}
      [Nonempty (Value tag)] :
      CheckedExpr symbols ctx tag ctx' → RuntimeStack ctx → Value tag × RuntimeStack ctx'
    | .atom val, stack => (val, stack)
    | .binOp (tag := operandTag) op lhs rhs is_legal, stack =>
        haveI : Nonempty (Value operandTag) := CheckedExpr.nonemptyTag lhs
        let (lv, stack1) := evalChecked env lhs stack
        let (rv, stack2) := evalChecked env rhs stack1
        (BinOp.implementation op operandTag is_legal lv rv, stack2)
    | .allocate n, stack => (.unitVal, RuntimeStack.allocate stack n)
    | .deallocate n h, stack => (.unitVal, RuntimeStack.deallocate stack n h)
    | .get (tag := tag) n h hne, stack =>
        (RuntimeStack.get stack n tag h hne, stack)
    | .set (tag := tag) n e hn, stack =>
        haveI : Nonempty (Value tag) := CheckedExpr.nonemptyTag e
        let (v, stack1) := evalChecked env e stack
        (.unitVal, RuntimeStack.set stack1 n tag v hn)
    | .branch (tag := tag) cmp lhs rhs, stack =>
        haveI : Nonempty (Value tag) := CheckedExpr.nonemptyTag lhs
        haveI : Nonempty (Value .bool) := ⟨.boolVal false⟩
        let (cond, stack1) := evalChecked env cmp stack
        match cond with
        | .boolVal b => if b then evalChecked env lhs stack1 else evalChecked env rhs stack1
    | .call ref args hout, stack =>
        let (calleeStack, stack1) := evalArgs env args stack
        let checkedFunction := EnvironmentWithImplementation.get env ref.function_slot
        haveI : Nonempty (Value (symbols.get ref.function_slot).2.output) :=
          ⟨Value.default _ hout⟩
        let (result, _) := evalChecked env checkedFunction.body calleeStack
        (result, stack1)

  public partial def evalArgs {symbols : EnvironmentSymbols}
      (env : EnvironmentWithImplementation symbols)
      {ctx : StackCtx} {tags : List ValueTag} {ctx' : StackCtx} :
      CheckedArgs symbols ctx tags ctx' → RuntimeStack ctx →
        RuntimeStack tags × RuntimeStack ctx'
    | .nil, stack => (.nil, stack)
    | .cons (tag := tag) arg rest, stack =>
        haveI : Nonempty (Value tag) := CheckedExpr.nonemptyTag arg
        let (v, stack1) := evalChecked env arg stack
        let (calleeRest, stack2) := evalArgs env rest stack1
        (.value v calleeRest, stack2)
end

public def eval {symbols : EnvironmentSymbols} (env : EnvironmentWithImplementation symbols)
    {tag : ValueTag} {ctx' : StackCtx} (expr : CheckedExpr symbols [] tag ctx') :
    Value tag :=
  haveI : Nonempty (Value tag) := CheckedExpr.nonemptyTag expr
  (evalChecked env expr .nil).1

public def evalTyped {symbols : EnvironmentSymbols} (env : EnvironmentWithImplementation symbols)
    {ctx : StackCtx} (k : TypedExpr symbols ctx) (stack : RuntimeStack ctx) :
    Value k.tag × RuntimeStack k.outputCtx :=
  haveI : Nonempty (Value k.tag) := CheckedExpr.nonemptyTag k.expr
  evalChecked env k.expr stack

end CheckedLang
