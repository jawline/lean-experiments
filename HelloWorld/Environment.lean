module

public import HelloWorld.Value

open Value

namespace CheckedLang

public structure FunctionSignature where
  inputs : List ValueTag
  output : ValueTag
deriving DecidableEq

public abbrev EnvironmentSymbols := Array (String × FunctionSignature)

@[expose] public def EnvironmentSymbols.get (env : EnvironmentSymbols) (slot : Fin env.size)
    : String × FunctionSignature :=
  env[slot.val]

public def EnvironmentSymbols.find? (env : EnvironmentSymbols) (name : String)
    : Option (Fin env.size) :=
  (Array.ofFn (fun slot : Fin env.size => (slot, env.get slot))).findSome?
    (fun entry => if entry.2.1 == name then some entry.1 else none)

public structure FunctionReference (symbols : EnvironmentSymbols) where
  debug_name : String
  function_slot : Fin symbols.size

public structure AlignedImplementations (symbols : EnvironmentSymbols) (Impl : Type)
    (slotOf : Impl → Fin symbols.size) (n : Nat) (h_n : n ≤ symbols.size) where
  implementations : Vector Impl n
  h_slot : ∀ (i : Fin n),
    slotOf (implementations[i.val]'i.isLt) =
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_n⟩

public def buildAlignedImplementations {symbols : EnvironmentSymbols} {Impl : Type}
    (slotOf : Impl → Fin symbols.size)
    (build : (slot : Fin symbols.size) →
      Except String { impl : Impl // slotOf impl = slot }) :
    (n : Nat) → (h_n : n ≤ symbols.size) →
      Except String (AlignedImplementations symbols Impl slotOf n h_n)
  | 0, _h_n => Except.ok
      { implementations := Vector.mk #[] rfl
        h_slot := by intro i; exact i.elim0 }
  | n + 1, h_n => do
      let prev ← buildAlignedImplementations slotOf build n
        (Nat.le_of_succ_le h_n)
      let hn : n < symbols.size := Nat.lt_of_succ_le h_n
      let slot : Fin symbols.size := ⟨n, hn⟩
      let ⟨implementation, hslot⟩ ← build slot
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
            rw [hslot]
            apply Fin.ext
            exact hival.symm
      } : AlignedImplementations symbols Impl slotOf (n + 1) h_n)

end CheckedLang
