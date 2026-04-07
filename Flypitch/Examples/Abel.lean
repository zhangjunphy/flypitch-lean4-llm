import Flypitch.FOL.Semantics
import Mathlib.Data.Int.Basic

namespace Flypitch
namespace abel

open fol

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

inductive Functions : Nat → Type
  | zero : Functions 0
  | plus : Functions 2

def LAbel : Language where
  functions := Functions
  relations := fun _ => PEmpty

def zeroTerm : term LAbel :=
  preterm.func Functions.zero

def addTerm (t₁ t₂ : term LAbel) : term LAbel :=
  apps (preterm.func Functions.plus) (t₁ :: t₂ :: [])

local infixl:65 " +' " => addTerm

def aAssoc : formula LAbel :=
  ∀' ∀' ∀' ((((&2 +' &1) +' &0) ≃ (&2 +' (&1 +' &0))))

def aZeroRight : formula LAbel :=
  ∀' (((&0 +' zeroTerm) ≃ &0))

def aZeroLeft : formula LAbel :=
  ∀' (((zeroTerm +' &0) ≃ &0))

def aInv : formula LAbel :=
  ∀' ex (fol.and (((&1 +' &0) ≃ zeroTerm)) (((&0 +' &1) ≃ zeroTerm)))

def aComm : formula LAbel :=
  ∀' ∀' (((&1 +' &0) ≃ (&0 +' &1)))

def TAb : Set (formula LAbel) :=
  insert aAssoc (insert aZeroRight (insert aZeroLeft (insert aInv (insert aComm ∅))))

def intStructure : Structure LAbel where
  carrier := Int
  fun_map := by
    intro n f
    cases f with
    | zero =>
        intro _
        exact 0
    | plus =>
        intro xs
        exact xs.nth 0 (by decide) + xs.nth 1 (by decide)
  rel_map := by
    intro n r
    cases r

@[reducible] instance : AddCommGroup intStructure.carrier := inferInstanceAs (AddCommGroup Int)

@[reducible] instance : OfNat intStructure.carrier 0 := inferInstanceAs (OfNat Int 0)

@[simp] theorem realize_zeroTerm (v : Nat → intStructure) :
    realize_term (M := intStructure) v zeroTerm [] = (0 : Int) :=
  rfl

@[simp] theorem intStructure_plus (x y : intStructure.carrier) :
    intStructure.fun_map Functions.plus (x :: y :: []) = x + y :=
  rfl

@[simp] theorem realize_addTerm (v : Nat → intStructure) (t₁ t₂ : term LAbel) :
    realize_term (M := intStructure) v (t₁ +' t₂) [] =
      (realize_term (M := intStructure) v t₁ [] + realize_term (M := intStructure) v t₂ []) := by
  rfl

theorem int_satisfies_assoc : satisfied_in intStructure aAssoc := by
  intro v x y z
  simpa [aAssoc] using add_assoc x y z

theorem int_satisfies_zeroRight : satisfied_in intStructure aZeroRight := by
  intro v x
  simp [aZeroRight, addTerm, apps, realize_term]
  rfl

theorem int_satisfies_zeroLeft : satisfied_in intStructure aZeroLeft := by
  intro v x
  simp [aZeroLeft, addTerm, apps, realize_term]
  rfl

theorem int_satisfies_inv : satisfied_in intStructure aInv := by
  intro v x hforall
  apply hforall (-x)
  intro himp
  have hleft : realize_formula ((v[x // 0])[-x // 0]) (((&1 +' &0) ≃ zeroTerm)) [] := by
    simp [addTerm, apps, realize_term]
    rfl
  have hright : realize_formula ((v[x // 0])[-x // 0]) (((&0 +' &1) ≃ zeroTerm)) [] := by
    simp [addTerm, apps, realize_term]
    rfl
  exact (himp hleft) hright

theorem int_satisfies_comm : satisfied_in intStructure aComm := by
  intro v x y
  simpa [aComm] using add_comm x y

theorem int_satisfies_TAb : all_satisfied_in intStructure TAb := by
  intro f hf
  simp [TAb, Set.mem_insert_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact int_satisfies_assoc
  · exact int_satisfies_zeroRight
  · exact int_satisfies_zeroLeft
  · exact int_satisfies_inv
  · exact int_satisfies_comm

theorem int_satisfies_of_prf {f : formula LAbel} (h : TAb ⊢ f) : satisfied_in intStructure f :=
  satisfied_in_trans int_satisfies_TAb (formula_soundness h)

end abel
end Flypitch
