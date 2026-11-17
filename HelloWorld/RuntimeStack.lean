module

public import HelloWorld.Value
public import HelloWorld.Environment

open Value

namespace CheckedLang

public abbrev StackCtx := List ValueTag

public inductive Cell where
  | undefined : Cell
  | value (tag : ValueTag) (v : Value tag) : Cell

public def Cell.tag : Cell → ValueTag
  | .undefined => .undefined
  | .value tag _ => tag

public def tagAgrees : Option ValueTag → Cell → Prop
  | none, _ => False
  | some tag, cell => tag = .undefined ∨ Cell.tag cell = tag

public structure RuntimeStack (ctx : StackCtx) where
  cells : Array Cell
  top : Nat
  h_bounds : top + ctx.length ≤ cells.size
  h_tags : ∀ (i : Nat), i < ctx.length →
    ∃ cell, cells[top + i]? = some cell ∧ tagAgrees ctx[i]? cell

public def RuntimeStack.slice {ctx : StackCtx} (stack : RuntimeStack ctx) : Array Cell :=
  stack.cells.extract stack.top (stack.top + ctx.length)

public theorem RuntimeStack.slice_length {ctx : StackCtx} (stack : RuntimeStack ctx) :
    stack.slice.size = ctx.length := by
  rw [RuntimeStack.slice, Array.size_extract]
  have hmin : min (stack.top + ctx.length) stack.cells.size = stack.top + ctx.length :=
    Nat.min_eq_left stack.h_bounds
  rw [hmin]
  omega

public theorem RuntimeStack.slice_getElem? {ctx : StackCtx} (stack : RuntimeStack ctx)
    {i : Nat} (hi : i < ctx.length) :
    stack.slice[i]? = stack.cells[stack.top + i]? := by
  rw [RuntimeStack.slice, Array.getElem?_extract]
  have hmin : min (stack.top + ctx.length) stack.cells.size = stack.top + ctx.length :=
    Nat.min_eq_left stack.h_bounds
  rw [hmin]
  have hsub : stack.top + ctx.length - stack.top = ctx.length := by omega
  rw [hsub]
  simp [hi]

public def RuntimeStack.toCellList {ctx : StackCtx} (stack : RuntimeStack ctx) : List Cell :=
  stack.slice.toList

public theorem RuntimeStack.toCellList_length {ctx : StackCtx} (stack : RuntimeStack ctx) :
    stack.toCellList.length = ctx.length := by
  rw [RuntimeStack.toCellList, Array.length_toList, stack.slice_length]

public def RuntimeStack.nil : RuntimeStack [] where
  cells := #[]
  top := 0
  h_bounds := by simp
  h_tags := by
    intro i hi
    simp at hi

public def RuntimeStack.undefined {ctx : StackCtx} (rest : RuntimeStack ctx) :
    RuntimeStack (.undefined :: ctx) where
  cells := #[Cell.undefined] ++ rest.slice
  top := 0
  h_bounds := by
    simp [Array.size_append, rest.slice_length]
    omega
  h_tags := by
    intro i hi
    cases i with
    | zero =>
        refine ⟨Cell.undefined, ?_, ?_⟩
        · rw [Array.getElem?_append_left (by simp)]
          simp
        · simp [tagAgrees]
    | succ j =>
        have hj : j < ctx.length := by simpa using hi
        obtain ⟨cell, hcell, htag⟩ := rest.h_tags j hj
        have hcell' : rest.slice[j]? = some cell := by
          rw [rest.slice_getElem? hj]
          exact hcell
        refine ⟨cell, ?_, ?_⟩
        · rw [Array.getElem?_append_right]
          · simpa using hcell'
          · simp
        · simpa using htag

public def RuntimeStack.value {ctx : StackCtx} {tag : ValueTag} (v : Value tag)
    (rest : RuntimeStack ctx) : RuntimeStack (tag :: ctx) where
  cells := #[Cell.value tag v] ++ rest.slice
  top := 0
  h_bounds := by
    simp [Array.size_append, rest.slice_length]
    omega
  h_tags := by
    intro i hi
    cases i with
    | zero =>
        refine ⟨Cell.value tag v, ?_, ?_⟩
        · rw [Array.getElem?_append_left (by simp)]
          simp
        · simp [tagAgrees, Cell.tag]
    | succ j =>
        have hj : j < ctx.length := by simpa using hi
        obtain ⟨cell, hcell, htag⟩ := rest.h_tags j hj
        have hcell' : rest.slice[j]? = some cell := by
          rw [rest.slice_getElem? hj]
          exact hcell
        refine ⟨cell, ?_, ?_⟩
        · rw [Array.getElem?_append_right]
          · simpa using hcell'
          · simp
        · simpa using htag

public theorem RuntimeStack.nonempty : (ctx : StackCtx) → Nonempty (RuntimeStack ctx)
  | [] => ⟨RuntimeStack.nil⟩
  | .undefined :: ctx =>
      ⟨RuntimeStack.undefined (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .unit :: ctx => ⟨RuntimeStack.value .unitVal (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .i32 :: ctx => ⟨RuntimeStack.value (.i32Val 0) (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .f32 :: ctx => ⟨RuntimeStack.value (.f32Val 0) (Classical.choice (RuntimeStack.nonempty ctx))⟩
  | .bool :: ctx => ⟨RuntimeStack.value (.boolVal false) (Classical.choice (RuntimeStack.nonempty ctx))⟩

public instance : (ctx : StackCtx) → Nonempty (RuntimeStack ctx) :=
  RuntimeStack.nonempty

public def Cell.get {tag : ValueTag} (c : Cell) (h : Cell.tag c = tag)
    (hne : tag ≠ .undefined) : Value tag :=
  match c with
  | .undefined =>
      have h' : tag = .undefined := by simpa [Cell.tag] using h.symm
      (hne h').elim
  | .value tag' v =>
      h ▸ v

public def RuntimeStack.get {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat)
    (tag : ValueTag) (hget : ctx[n]? = some tag) (hne : tag ≠ .undefined) : Value tag :=
  let hn : n < ctx.length := (List.getElem?_eq_some_iff.mp hget).choose
  let hlt : stack.top + n < stack.cells.size := by
    have hbounds := stack.h_bounds
    omega
  let c := stack.cells[stack.top + n]'hlt
  have hcell : Cell.tag c = tag := by
    obtain ⟨cell, hcell, htag⟩ := stack.h_tags n hn
    have hc : cell = c := by
      have h1 : stack.cells[stack.top + n]? = some c := Array.getElem?_eq_getElem hlt
      rw [h1] at hcell
      exact (Option.some.inj hcell).symm
    rw [hc] at htag
    rw [hget] at htag
    rcases htag with h | h
    · exact (hne h).elim
    · exact h
  Cell.get c hcell hne

public def RuntimeStack.set {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat)
    (tag : ValueTag) (v : Value tag) (hn : n < ctx.length) :
    RuntimeStack (ctx.set n tag) :=
  let hlt : stack.top + n < stack.cells.size := by
    have hbounds := stack.h_bounds
    omega
  let newCell : Cell := .value tag v
  let cells' := stack.cells.set (stack.top + n) newCell hlt
  have h_bounds' : stack.top + (ctx.set n tag).length ≤ cells'.size := by
    rw [List.length_set, Array.size_set hlt]
    exact stack.h_bounds
  have h_tags' : ∀ (i : Nat), i < (ctx.set n tag).length →
      ∃ cell, cells'[stack.top + i]? = some cell ∧ tagAgrees (ctx.set n tag)[i]? cell := by
    intro i hi
    have hi_ctx : i < ctx.length := by simpa [List.length_set] using hi
    by_cases hin : i = n
    · subst hin
      refine ⟨newCell, ?_, ?_⟩
      · rw [Array.getElem?_set hlt]
        simp
      · rw [List.getElem?_set_self hn]
        simp [tagAgrees, newCell, Cell.tag]
    · obtain ⟨cell, hcell, htag⟩ := stack.h_tags i hi_ctx
      have hni : n ≠ i := fun h => hin h.symm
      refine ⟨cell, ?_, ?_⟩
      · rw [Array.getElem?_set hlt]
        simp [hni]
        exact hcell
      · rw [List.getElem?_set_ne hni]
        exact htag
  ⟨cells', stack.top, h_bounds', h_tags'⟩

public def RuntimeStack.take {ctx : StackCtx} (n : Nat) (stack : RuntimeStack ctx) :
    RuntimeStack (ctx.take n) where
  cells := stack.cells
  top := stack.top
  h_bounds := by
    rw [List.length_take]
    have hmin : min n ctx.length ≤ ctx.length := Nat.min_le_right n ctx.length
    have h : stack.top + min n ctx.length ≤ stack.top + ctx.length :=
      Nat.add_le_add_left hmin stack.top
    exact Nat.le_trans h stack.h_bounds
  h_tags := by
    intro i hi
    have hi_ctx : i < ctx.length := by
      have hlen : (ctx.take n).length = min n ctx.length := List.length_take
      rw [hlen] at hi
      omega
    have hik : i < n := by
      have hlen : (ctx.take n).length = min n ctx.length := List.length_take
      rw [hlen] at hi
      omega
    obtain ⟨cell, hcell, htag⟩ := stack.h_tags i hi_ctx
    refine ⟨cell, ?_, ?_⟩
    · exact hcell
    · rw [List.getElem?_take]
      simp [hik]
      exact htag

public def RuntimeStack.drop {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat)
    (hn : n ≤ ctx.length) : RuntimeStack (ctx.drop n) where
  cells := stack.cells
  top := stack.top + n
  h_bounds := by
    rw [List.length_drop]
    have hbounds := stack.h_bounds
    omega
  h_tags := by
    intro i hi
    have hi_ctx : n + i < ctx.length := by
      have hlen : (ctx.drop n).length = ctx.length - n := List.length_drop
      rw [hlen] at hi
      omega
    obtain ⟨cell, hcell, htag⟩ := stack.h_tags (n + i) hi_ctx
    have hindex : stack.top + n + i = stack.top + (n + i) := by omega
    refine ⟨cell, ?_, ?_⟩
    · rw [hindex]
      exact hcell
    · rw [List.getElem?_drop]
      exact htag

public def RuntimeStack.deallocate {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat)
    (hn : n ≤ ctx.length) : RuntimeStack (ctx.drop n) :=
  RuntimeStack.drop stack n hn

public def RuntimeStack.append {ctx1 ctx2 : StackCtx} (s1 : RuntimeStack ctx1)
    (s2 : RuntimeStack ctx2) : RuntimeStack (ctx1 ++ ctx2) where
  cells := s1.slice ++ s2.slice
  top := 0
  h_bounds := by
    simp [Array.size_append, s1.slice_length, s2.slice_length, List.length_append]
  h_tags := by
    intro i hi
    by_cases hi1 : i < ctx1.length
    · obtain ⟨cell, hcell, htag⟩ := s1.h_tags i hi1
      have hcell' : s1.slice[i]? = some cell := by
        rw [s1.slice_getElem? hi1]
        exact hcell
      refine ⟨cell, ?_, ?_⟩
      · rw [Array.getElem?_append_left]
        · simpa using hcell'
        · simpa [s1.slice_length] using hi1
      · rw [List.getElem?_append_left hi1]
        exact htag
    · have hge : ctx1.length ≤ i := Nat.le_of_not_gt hi1
      have hi2 : i - ctx1.length < ctx2.length := by
        have hi_len : i < (ctx1 ++ ctx2).length := hi
        rw [List.length_append] at hi_len
        omega
      obtain ⟨cell, hcell, htag⟩ := s2.h_tags (i - ctx1.length) hi2
      have hcell' : s2.slice[i - ctx1.length]? = some cell := by
        rw [s2.slice_getElem? hi2]
        exact hcell
      refine ⟨cell, ?_, ?_⟩
      · rw [Array.getElem?_append_right]
        · simpa [s1.slice_length] using hcell'
        · simpa [s1.slice_length] using hge
      · rw [List.getElem?_append_right hge]
        exact htag

public def RuntimeStack.undefinedStack (n : Nat) :
    RuntimeStack (List.replicate n ValueTag.undefined) where
  cells := Array.replicate n Cell.undefined
  top := 0
  h_bounds := by simp
  h_tags := by
    intro i hi
    have hi' : i < n := by simpa using hi
    refine ⟨Cell.undefined, ?_, ?_⟩
    · rw [Array.getElem?_replicate]
      simp [hi']
    · rw [List.getElem?_replicate]
      simp [hi', tagAgrees]

public def RuntimeStack.allocate {ctx : StackCtx} (stack : RuntimeStack ctx) (n : Nat) :
    RuntimeStack (List.replicate n ValueTag.undefined ++ ctx) :=
  if h : n ≤ stack.top then
    { cells := stack.cells
      top := stack.top - n
      h_bounds := by
        rw [List.length_append, List.length_replicate]
        have hbounds := stack.h_bounds
        omega
      h_tags := by
        intro i hi
        by_cases hin : i < n
        · have hlt : stack.top - n + i < stack.cells.size := by
            have hbounds := stack.h_bounds
            omega
          refine ⟨stack.cells[stack.top - n + i]'hlt, ?_, ?_⟩
          · exact Array.getElem?_eq_getElem hlt
          · rw [List.getElem?_append_left (by simpa using hin)]
            rw [List.getElem?_replicate]
            simp [hin, tagAgrees]
        · have hge : n ≤ i := Nat.le_of_not_gt hin
          let j := i - n
          have hj : j < ctx.length := by
            have hi_len : i < n + ctx.length := by
              simpa [List.length_replicate, List.length_append] using hi
            omega
          obtain ⟨cell, hcell, htag⟩ := stack.h_tags j hj
          have hindex : stack.top - n + i = stack.top + j := by omega
          refine ⟨cell, ?_, ?_⟩
          · rw [hindex]
            exact hcell
          · have hctx : (List.replicate n ValueTag.undefined ++ ctx)[i]? = ctx[j]? := by
              rw [List.getElem?_append_right (by simpa using hge)]
              rw [List.length_replicate]
            rw [hctx]
            exact htag
    }
  else
    RuntimeStack.append (RuntimeStack.undefinedStack n) stack

end CheckedLang
