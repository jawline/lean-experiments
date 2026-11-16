module

public import HelloWorld.Value
public import HelloWorld.Environment

open Value

namespace CheckedLang

public abbrev StackCtx := List ValueTag

public inductive Cell where
  | empty : Cell
  | value (tag : ValueTag) (v : Value tag) : Cell

public def Cell.tag : Cell → ValueTag
  | .empty => .empty
  | .value tag _ => tag

public structure RuntimeStack (ctx : StackCtx) where
  cells : Array Cell
  start : Nat
  h_len : start + ctx.length ≤ cells.size
  h_tags : ((cells.toList.drop start).take ctx.length).map Cell.tag = ctx

public def RuntimeStack.toCellList {ctx : StackCtx} (stack : RuntimeStack ctx) : List Cell :=
  (stack.cells.toList.drop stack.start).take ctx.length

public theorem RuntimeStack.toCellList_length {ctx : StackCtx} (stack : RuntimeStack ctx) :
    stack.toCellList.length = ctx.length := by
  simp only [RuntimeStack.toCellList, List.length_take, List.length_drop, Array.length_toList]
  apply Nat.min_eq_left
  have h : ctx.length + stack.start ≤ stack.cells.size := by
    simpa [Nat.add_comm] using stack.h_len
  exact Nat.le_sub_of_add_le h

public theorem listGet?_eq_getElem? {α : Type} :
    (xs : List α) → (n : Nat) → listGet? xs n = xs[n]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => listGet?_eq_getElem? xs n

public theorem listGet?_some_lt {α : Type} {xs : List α} {n : Nat} {x : α}
    (h : listGet? xs n = some x) : n < xs.length := by
  have h' : xs[n]? = some x := by
    simpa [listGet?_eq_getElem?] using h
  exact (List.getElem?_eq_some_iff.mp h').choose

public theorem listSet?_some_lt {α : Type} {xs : List α} {n : Nat} {x : α} {xs' : List α}
    (h : listSet? xs n x = some xs') : n < xs.length := by
  induction xs generalizing n xs' with
  | nil => simp [listSet?] at h
  | cons y ys ih =>
      cases n with
      | zero => simp
      | succ n =>
          simp [listSet?] at h
          rcases h with ⟨ys', hys', _⟩
          exact Nat.succ_lt_succ (ih hys')

public theorem listSet?_length {α : Type} {xs : List α} {n : Nat} {x : α} {xs' : List α}
    (h : listSet? xs n x = some xs') : xs'.length = xs.length := by
  induction xs generalizing n xs' with
  | nil => simp [listSet?] at h
  | cons y ys ih =>
      cases n with
      | zero =>
          simp [listSet?] at h
          subst xs'
          simp
      | succ n =>
          simp [listSet?] at h
          rcases h with ⟨ys', hys', hxs⟩
          subst xs'
          simp [ih hys']

public theorem listSet?_eq_set {α : Type} {xs : List α} {n : Nat} {x : α} {xs' : List α}
    (h : listSet? xs n x = some xs') : xs.set n x = xs' := by
  induction xs generalizing n xs' with
  | nil => simp [listSet?] at h
  | cons y ys ih =>
      cases n with
      | zero =>
          simp [listSet?] at h
          subst xs'
          rfl
      | succ n =>
          simp [listSet?] at h
          rcases h with ⟨ys', hys', hxs⟩
          subst xs'
          simp [List.set, ih hys']

public def RuntimeStack.nil : RuntimeStack [] where
  cells := #[]
  start := 0
  h_len := by simp
  h_tags := by simp

public def RuntimeStack.empty {ctx : StackCtx} (rest : RuntimeStack ctx) :
    RuntimeStack (.empty :: ctx) where
  cells := (Cell.empty :: rest.toCellList).toArray
  start := 0
  h_len := by
    simp [RuntimeStack.toCellList_length]
  h_tags := by
    simp [RuntimeStack.toCellList, Cell.tag, rest.h_tags]

public def RuntimeStack.value {ctx : StackCtx} {tag : ValueTag} (v : Value tag)
    (rest : RuntimeStack ctx) : RuntimeStack (tag :: ctx) where
  cells := (Cell.value tag v :: rest.toCellList).toArray
  start := 0
  h_len := by
    simp [RuntimeStack.toCellList_length]
  h_tags := by
    simp [RuntimeStack.toCellList, Cell.tag, rest.h_tags]

public theorem RuntimeStack.nonempty : (ctx : StackCtx) → Nonempty (RuntimeStack ctx)
  | [] => ⟨RuntimeStack.nil⟩
  | .empty :: ctx => ⟨RuntimeStack.empty (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .unit :: ctx => ⟨RuntimeStack.value .unitVal (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .i32 :: ctx => ⟨RuntimeStack.value (.i32Val 0) (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .f32 :: ctx => ⟨RuntimeStack.value (.f32Val 0) (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .bool :: ctx => ⟨RuntimeStack.value (.boolVal false) (Classical.choice (RuntimeStack.nonempty ctx))⟩

public instance : (ctx : StackCtx) → Nonempty (RuntimeStack ctx) :=
  RuntimeStack.nonempty

public def Cell.get {tag : ValueTag} (c : Cell) (h : Cell.tag c = tag)
    (hne : tag ≠ .empty) : Value tag :=
  match c with
  | .empty =>
      have h' : tag = .empty := by simpa [Cell.tag] using h.symm
      (hne h').elim
  | .value tag' v =>
      h ▸ v

public def RuntimeStack.get {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat)
    (tag : ValueTag) (hget : listGet? ctx n = some tag) (hne : tag ≠ .empty) : Value tag :=
  let hn : n < ctx.length := listGet?_some_lt hget
  let hlt : stack.start + n < stack.cells.size := by
    have hlen := stack.h_len
    omega
  let c := stack.cells[stack.start + n]'hlt
  have htag : Cell.tag c = tag := by
    have h := congrArg (fun l => l[n]?) stack.h_tags
    change ((stack.toCellList.map Cell.tag)[n]?) = ctx[n]? at h
    rw [List.getElem?_map] at h
    have hslice_len : n < stack.toCellList.length := by
      rw [stack.toCellList_length]
      exact hn
    rw [List.getElem?_eq_getElem hslice_len, Option.map_some] at h
    have hget' : ctx[n]? = some tag := by
      simpa [listGet?_eq_getElem?] using hget
    rw [hget'] at h
    have htag' : Cell.tag (stack.toCellList[n]'hslice_len) = tag := by
      simpa using h
    have hcell : stack.toCellList[n]'hslice_len = c := by
      simp only [RuntimeStack.toCellList]
      rw [List.getElem_take, List.getElem_drop]
      exact Array.getElem_toList hlt
    simpa [hcell] using htag'
  Cell.get c htag hne

public def RuntimeStack.set {ctx : StackCtx} (stack : RuntimeStack ctx) :
    (n : Nat) → (tag : ValueTag) → (v : Value tag) →
    (ctx' : StackCtx) → listSet? ctx n tag = some ctx' → RuntimeStack ctx' :=
  fun n tag v ctx' hset =>
    let hn : n < ctx.length := listSet?_some_lt hset
    let hlt : stack.start + n < stack.cells.size := by
      have hlen := stack.h_len
      omega
    let newCell : Cell := .value tag v
    let cells' := stack.cells.set (stack.start + n) newCell hlt
    have h_len' : stack.start + ctx'.length ≤ cells'.size := by
      rw [listSet?_length hset, Array.size_set hlt]
      exact stack.h_len
    have h_tags' : ((cells'.toList.drop stack.start).take ctx'.length).map Cell.tag = ctx' := by
      rw [Array.toList_set stack.cells (stack.start + n) newCell hlt]
      rw [List.drop_set]
      have hnot : ¬ (stack.start + n < stack.start) := by omega
      simp only [hnot, ite_false]
      have hsub : stack.start + n - stack.start = n := by omega
      rw [hsub, listSet?_length hset]
      rw [List.take_set]
      rw [List.map_set]
      rw [stack.h_tags]
      simp [newCell, Cell.tag]
      rw [listSet?_eq_set hset]
    ⟨cells', stack.start, h_len', h_tags'⟩

public def RuntimeStack.take {ctx : StackCtx} (n : Nat) (stack : RuntimeStack ctx) :
    RuntimeStack (ctx.take n) where
  cells := stack.cells
  start := stack.start
  h_len := by
    rw [List.length_take]
    have hmin : min n ctx.length ≤ ctx.length := Nat.min_le_right n ctx.length
    have h : stack.start + min n ctx.length ≤ stack.start + ctx.length :=
      Nat.add_le_add_left hmin stack.start
    exact Nat.le_trans h stack.h_len
  h_tags := by
    have h := congrArg (List.take n) stack.h_tags
    rw [← List.map_take] at h
    rw [List.take_take] at h
    simpa [List.length_take] using h

public def RuntimeStack.drop {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat)
    (hn : n ≤ ctx.length) : RuntimeStack (ctx.drop n) where
  cells := stack.cells
  start := stack.start + n
  h_len := by
    rw [List.length_drop]
    have hlen := stack.h_len
    omega
  h_tags := by
    have h := congrArg (List.drop n) stack.h_tags
    rw [← List.map_drop] at h
    rw [List.drop_take] at h
    rw [List.drop_drop] at h
    simpa using h

public def RuntimeStack.deallocate {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat)
    (hn : n ≤ ctx.length) : RuntimeStack (ctx.drop n) :=
  RuntimeStack.drop stack n hn

public def RuntimeStack.append {ctx1 ctx2 : StackCtx} (s1 : RuntimeStack ctx1)
    (s2 : RuntimeStack ctx2) : RuntimeStack (ctx1 ++ ctx2) where
  cells := (s1.toCellList ++ s2.toCellList).toArray
  start := 0
  h_len := by
    simp [List.size_toArray, List.length_append, s1.toCellList_length, s2.toCellList_length]
  h_tags := by
    simp [RuntimeStack.toCellList, List.map_append, s1.h_tags, s2.h_tags]
    rw [← List.length_append, List.take_length]

public def RuntimeStack.emptyStack (n : Nat) :
    RuntimeStack (List.replicate n ValueTag.empty) where
  cells := (List.replicate n Cell.empty).toArray
  start := 0
  h_len := by simp
  h_tags := by simp [Cell.tag]

public def RuntimeStack.allocate {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat) :
    RuntimeStack (List.replicate n ValueTag.empty ++ ctx) :=
  RuntimeStack.append (RuntimeStack.emptyStack n) stack

end CheckedLang
