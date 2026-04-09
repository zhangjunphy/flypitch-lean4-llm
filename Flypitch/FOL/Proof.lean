import Flypitch.FOL.Formula
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image

universe u

namespace Flypitch
namespace fol

/-!
`Flypitch.FOL.Proof` defines the natural-deduction proof system for the first-order language
developed in this repository, together with the structural operations on derivations that are
used throughout the completeness proof.
-/

variable {L : Language}

/-- Natural-deduction derivations from a set of assumptions. -/
inductive prf : Set (formula L) → formula L → Type u
  | axm {Γ A} : A ∈ Γ → prf Γ A
  | impI {Γ : Set (formula L)} {A B} : prf (insert A Γ) B → prf Γ (A ⟹ B)
  | impE {Γ} (A) {B} : prf Γ (A ⟹ B) → prf Γ A → prf Γ B
  | falsumE {Γ : Set (formula L)} {A} : prf (insert (∼A) Γ) ⊥ → prf Γ A
  | allI {Γ A} : prf (lift_formula1 '' Γ) A → prf Γ (∀' A)
  | allE₂ {Γ} (A : formula L) (t : term L) : prf Γ (∀' A) → prf Γ (subst_formula A t 0)
  | ref (Γ : Set (formula L)) (t : term L) : prf Γ (t ≃ t)
  | subst₂ {Γ} (s t : term L) (f : formula L) :
      prf Γ (s ≃ t) → prf Γ (subst_formula f s 0) → prf Γ (subst_formula f t 0)

infix:51 " ⊢ " => prf

/-- Propositional truncation of derivability. -/
def provable (T : Set (formula L)) (f : formula L) : Prop :=
  Nonempty (T ⊢ f)

infix:51 " ⊢' " => provable

/-- Eliminate a universal quantifier and rewrite to a chosen target formula. -/
noncomputable def allE {Γ : Set (formula L)} (A : formula L) (t : term L) {B : formula L}
    (h₁ : Γ ⊢ ∀' A) (h₂ : subst_formula A t 0 = B) : Γ ⊢ B := by
  cases h₂
  exact prf.allE₂ A t h₁

/-- Equality substitution followed by a rewrite to a chosen target formula. -/
noncomputable def subst {Γ : Set (formula L)} {s t : term L} (f₁ : formula L) {f₂ : formula L}
    (h₁ : Γ ⊢ s ≃ t) (h₂ : Γ ⊢ subst_formula f₁ s 0) (h₃ : subst_formula f₁ t 0 = f₂) :
    Γ ⊢ f₂ := by
  cases h₃
  exact prf.subst₂ s t f₁ h₁ h₂

/-- The most recently inserted assumption is available immediately. -/
noncomputable def axm1 {Γ : Set (formula L)} {A : formula L} : insert A Γ ⊢ A :=
  prf.axm (by simp)

/-- The second most recently inserted assumption is available immediately. -/
noncomputable def axm2 {Γ : Set (formula L)} {A B : formula L} : insert A (insert B Γ) ⊢ B :=
  prf.axm (by simp)

/-- Weakening of assumptions for derivations. -/
noncomputable def weakening {Γ Δ : Set (formula L)} {f : formula L}
    (h₁ : Γ ⊆ Δ) (h₂ : Γ ⊢ f) : Δ ⊢ f := by
  induction h₂ generalizing Δ with
  | axm h =>
      exact prf.axm (h₁ h)
  | impI h ih =>
      refine prf.impI ?_
      apply ih
      intro x hx
      simp only [Set.mem_insert_iff] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (h₁ hx)
  | impE A hImp hA ihImp ihA =>
      exact prf.impE A (ihImp h₁) (ihA h₁)
  | falsumE h ih =>
      refine prf.falsumE ?_
      apply ih
      intro x hx
      simp only [Set.mem_insert_iff] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (h₁ hx)
  | allI h ih =>
      refine prf.allI ?_
      apply ih
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact Set.mem_image_of_mem lift_formula1 (h₁ hx)
  | allE₂ A t h ih =>
      exact prf.allE₂ A t (ih h₁)
  | ref _ t =>
      exact prf.ref Δ t
  | subst₂ s t f hEq hSub ihEq ihSub =>
      exact prf.subst₂ s t f (ihEq h₁) (ihSub h₁)

/-- One-step weakening by adding an irrelevant assumption. -/
noncomputable def weakening1 {Γ : Set (formula L)} {f₁ f₂ : formula L}
    (h : Γ ⊢ f₂) : insert f₁ Γ ⊢ f₂ :=
  weakening (by
    intro x hx
    exact Or.inr hx) h

/-- Two-step weakening that preserves the distinguished first inserted assumption. -/
noncomputable def weakening2 {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (h : insert f₁ Γ ⊢ f₂) : insert f₁ (insert f₃ Γ) ⊢ f₂ :=
  weakening (by
    intro x hx
    simp only [Set.mem_insert_iff] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)) h

/-- Truncated implication introduction. -/
theorem impI' {Γ : Set (formula L)} {A B : formula L} (h : insert A Γ ⊢' B) :
    Γ ⊢' (A ⟹ B) := by
  rcases h with ⟨h⟩
  exact ⟨prf.impI h⟩

/-- Truncated implication elimination. -/
theorem impE' {Γ : Set (formula L)} (A : formula L) {B : formula L}
    (h₁ : Γ ⊢' (A ⟹ B)) (h₂ : Γ ⊢' A) : Γ ⊢' B := by
  rcases h₁ with ⟨h₁⟩
  rcases h₂ with ⟨h₂⟩
  exact ⟨prf.impE A h₁ h₂⟩

/-- Truncated ex falso rule under an explicit negated assumption. -/
theorem falsumE' {Γ : Set (formula L)} {A : formula L} (h : insert (∼A) Γ ⊢' ⊥) :
    Γ ⊢' A := by
  rcases h with ⟨h⟩
  exact ⟨prf.falsumE h⟩

/-- Truncated universal introduction. -/
theorem allI' {Γ : Set (formula L)} {A : formula L} (h : lift_formula1 '' Γ ⊢' A) :
    Γ ⊢' ∀' A := by
  rcases h with ⟨h⟩
  exact ⟨prf.allI h⟩

/-- Truncated universal elimination. -/
theorem allE₂' {Γ : Set (formula L)} {A : formula L} {t : term L} (h : Γ ⊢' ∀' A) :
    Γ ⊢' subst_formula A t 0 := by
  rcases h with ⟨h⟩
  exact ⟨prf.allE₂ A t h⟩

/-- Truncated reflexivity of equality. -/
theorem ref' (Γ : Set (formula L)) (t : term L) : Γ ⊢' (t ≃ t) :=
  ⟨prf.ref Γ t⟩

/-- Truncated equality substitution. -/
theorem subst₂' {Γ : Set (formula L)} (s t : term L) (f : formula L)
    (h₁ : Γ ⊢' (s ≃ t)) (h₂ : Γ ⊢' subst_formula f s 0) : Γ ⊢' subst_formula f t 0 := by
  rcases h₁ with ⟨h₁⟩
  rcases h₂ with ⟨h₂⟩
  exact ⟨prf.subst₂ s t f h₁ h₂⟩

/-- Weakening for truncated derivations. -/
theorem weakening' {Γ Δ : Set (formula L)} {f : formula L} (h₁ : Γ ⊆ Δ)
    (h₂ : Γ ⊢' f) : Δ ⊢' f := by
  rcases h₂ with ⟨h₂⟩
  exact ⟨weakening h₁ h₂⟩

/-- One-step weakening for truncated derivations. -/
theorem weakening1' {Γ : Set (formula L)} {f₁ f₂ : formula L} (h : Γ ⊢' f₂) :
    insert f₁ Γ ⊢' f₂ := by
  rcases h with ⟨h⟩
  exact ⟨weakening1 h⟩

/-- Two-step weakening for truncated derivations. -/
theorem weakening2' {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (h : insert f₁ Γ ⊢' f₂) : insert f₁ (insert f₃ Γ) ⊢' f₂ := by
  rcases h with ⟨h⟩
  exact ⟨weakening2 h⟩

/-- Modus ponens with the antecedent inserted as an extra assumption. -/
noncomputable def deduction {Γ : Set (formula L)} {A B : formula L} (h : Γ ⊢ (A ⟹ B)) :
    insert A Γ ⊢ B :=
  prf.impE A (weakening1 h) axm1

/-- Derive any formula from falsum. -/
noncomputable def exfalso {Γ : Set (formula L)} {A : formula L} (h : Γ ⊢ (⊥ : formula L)) :
    Γ ⊢ A :=
  prf.falsumE (weakening1 h)

/-- Truncated version of `exfalso`. -/
theorem exfalso' {Γ : Set (formula L)} {A : formula L} (h : Γ ⊢' (⊥ : formula L)) :
    Γ ⊢' A := by
  rcases h with ⟨h⟩
  exact ⟨exfalso h⟩

/-- Repackage a proof of `A ⟹ ⊥` as a proof of `∼A`. -/
noncomputable def notI {Γ : Set (formula L)} {A : formula L} (h : Γ ⊢ (A ⟹ (⊥ : formula L))) :
    Γ ⊢ (∼A) := by
  simpa [fol.not] using h

/-- Conjunction introduction. -/
noncomputable def andI {Γ : Set (formula L)} {f₁ f₂ : formula L}
    (h₁ : Γ ⊢ f₁) (h₂ : Γ ⊢ f₂) : Γ ⊢ and f₁ f₂ := by
  apply prf.impI
  apply prf.impE f₂
  · apply prf.impE f₁
    · exact axm1
    · exact weakening1 h₁
  · exact weakening1 h₂

/-- Left projection from a conjunction. -/
noncomputable def andE1 {Γ : Set (formula L)} {f₁ : formula L} (f₂ : formula L)
    (h : Γ ⊢ and f₁ f₂) : Γ ⊢ f₁ := by
  apply prf.falsumE
  apply prf.impE (f₁ ⟹ ∼f₂) (weakening1 h)
  apply prf.impI
  apply exfalso
  exact prf.impE f₁ axm2 axm1

/-- Right projection from a conjunction. -/
noncomputable def andE2 {Γ : Set (formula L)} (f₁ : formula L) {f₂ : formula L}
    (h : Γ ⊢ and f₁ f₂) : Γ ⊢ f₂ := by
  apply prf.falsumE
  apply prf.impE (f₁ ⟹ ∼f₂) (weakening1 h)
  apply prf.impI
  exact axm2

/-- Left introduction rule for disjunction. -/
noncomputable def orI1 {Γ : Set (formula L)} {A B : formula L} (h : Γ ⊢ A) :
    Γ ⊢ or A B := by
  apply prf.impI
  apply exfalso
  exact prf.impE _ axm1 (weakening1 h)

/-- Right introduction rule for disjunction. -/
noncomputable def orI2 {Γ : Set (formula L)} {A B : formula L} (h : Γ ⊢ B) :
    Γ ⊢ or A B := by
  simpa [fol.or] using prf.impI (weakening1 h)

/-- Disjunction elimination. -/
noncomputable def orE {Γ : Set (formula L)} {A B C : formula L}
    (h₁ : Γ ⊢ or A B) (h₂ : insert A Γ ⊢ C) (h₃ : insert B Γ ⊢ C) : Γ ⊢ C := by
  apply prf.falsumE
  apply prf.impE C
  · exact axm1
  · apply prf.impE B
    · exact prf.impI (weakening2 h₃)
    · apply prf.impE _ (weakening1 h₁)
      exact prf.impI (prf.impE _ axm2 (weakening2 h₂))

/-- Biconditional introduction. -/
noncomputable def biimpI {Γ : Set (formula L)} {f₁ f₂ : formula L}
    (h₁ : insert f₁ Γ ⊢ f₂) (h₂ : insert f₂ Γ ⊢ f₁) : Γ ⊢ biimp f₁ f₂ := by
  apply andI
  · exact prf.impI h₁
  · exact prf.impI h₂

/-- Extract the forward implication from a biconditional. -/
noncomputable def biimpE1 {Γ : Set (formula L)} {f₁ f₂ : formula L}
    (h : Γ ⊢ biimp f₁ f₂) : insert f₁ Γ ⊢ f₂ :=
  deduction (andE1 (f₂ := (f₂ ⟹ f₁)) h)

/-- Extract the backward implication from a biconditional. -/
noncomputable def biimpE2 {Γ : Set (formula L)} {f₁ f₂ : formula L}
    (h : Γ ⊢ biimp f₁ f₂) : insert f₂ Γ ⊢ f₁ :=
  deduction (andE2 (f₁ := (f₁ ⟹ f₂)) h)

/-- Existential introduction by providing a witness term. -/
noncomputable def exI {Γ : Set (formula L)} {f : formula L} (t : term L)
    (h : Γ ⊢ subst_formula f t 0) : Γ ⊢ ex f := by
  apply prf.impI
  apply prf.impE (subst_formula f t 0)
  · exact prf.allE₂ (∼f) t axm1
  · exact weakening1 h

/-- Existential elimination using a lifted derivation from a fresh witness. -/
noncomputable def exE {Γ : Set (formula L)} {f₁ f₂ : formula L} (h₁ : Γ ⊢ ex f₁)
    (h₂ : insert f₁ (lift_formula1 '' Γ) ⊢ lift_formula1 f₂) : Γ ⊢ f₂ := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 h₁)
  apply prf.allI
  apply prf.impI
  rw [Set.image_insert_eq]
  exact prf.impE _ axm2 (weakening2 h₂)

/-- Lift every formula appearing in a derivation by the same shift. -/
noncomputable def prf_lift {Γ : Set (formula L)} {f : formula L} (n m : Nat) (h : Γ ⊢ f) :
    Set.image (fun g : formula L => lift_formula_at g n m) Γ ⊢ lift_formula_at f n m := by
  induction h generalizing m with
  | axm hmem =>
      exact prf.axm (Set.mem_image_of_mem (fun g : formula L => lift_formula_at g n m) hmem)
  | impI h ih =>
      rename_i G A B
      have h' :
          insert (lift_formula_at A n m) (Set.image (fun g : formula L => lift_formula_at g n m) G) ⊢
            lift_formula_at B n m := by
        simpa [Set.image_insert_eq] using (ih (m := m))
      exact prf.impI h'
  | impE A hImp hA ihImp ihA =>
      exact prf.impE (lift_formula_at A n m) (ihImp (m := m)) (ihA (m := m))
  | falsumE h ih =>
      rename_i G A
      have h' :
          insert (∼(lift_formula_at A n m))
            (Set.image (fun g : formula L => lift_formula_at g n m) G) ⊢ (⊥ : formula L) := by
        simpa [Set.image_insert_eq, fol.not] using (ih (m := m))
      exact prf.falsumE h'
  | allI h ih =>
      rename_i G A
      have h' :
          Set.image lift_formula1 (Set.image (fun g : formula L => lift_formula_at g n m) G) ⊢
            lift_formula_at A n (m + 1) := by
        simpa [Set.image_image, Function.comp, lift_formula1, lift_formula, lift_formula1_lift_formula_at]
          using (ih (m := m + 1))
      exact prf.allI h'
  | allE₂ A t h ih =>
      exact allE (A := lift_formula_at A n (m + 1)) (t := t ↑' n # m) (ih (m := m))
        (lift_at_subst_formula_small0 (f := A) (s := t) n m)
  | ref G t =>
      exact prf.ref _ (t ↑' n # m)
  | subst₂ s t f hEq hSub ihEq ihSub =>
      exact subst (f₁ := lift_formula_at f n (m + 1)) (ihEq (m := m))
        (by simpa using (ihSub (m := m)))
        (lift_at_subst_formula_small0 (f := f) (s := t) n m)

/-- Substitute a term throughout a derivation and all of its assumptions. -/
noncomputable def substitution {Γ : Set (formula L)} {f : formula L} (t : term L) (n : Nat)
    (h : Γ ⊢ f) :
    Set.image (fun g : formula L => subst_formula g t n) Γ ⊢ subst_formula f t n := by
  induction h generalizing n with
  | axm hmem =>
      exact prf.axm (Set.mem_image_of_mem (fun g : formula L => subst_formula g t n) hmem)
  | impI h ih =>
      rename_i G A B
      have h' :
          insert (subst_formula A t n) (Set.image (fun g : formula L => subst_formula g t n) G) ⊢
            subst_formula B t n := by
        simpa [Set.image_insert_eq] using (ih (n := n))
      exact prf.impI h'
  | impE A hImp hA ihImp ihA =>
      exact prf.impE (subst_formula A t n) (ihImp (n := n)) (ihA (n := n))
  | falsumE h ih =>
      rename_i G A
      have h' :
          insert (∼(subst_formula A t n))
            (Set.image (fun g : formula L => subst_formula g t n) G) ⊢ (⊥ : formula L) := by
        simpa [Set.image_insert_eq, fol.not] using (ih (n := n))
      exact prf.falsumE h'
  | allI h ih =>
      rename_i G A
      have hset :
          Set.image (fun g : formula L => subst_formula (lift_formula1 g) t (n + 1)) G =
            Set.image lift_formula1 (Set.image (fun g : formula L => subst_formula g t n) G) := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, rfl⟩
          refine ⟨subst_formula y t n, ?_, ?_⟩
          · exact Set.mem_image_of_mem (fun g : formula L => subst_formula g t n) hy
          · simpa [lift_formula1, lift_formula] using
              (lift_formula1_subst_shift (f := y) (s := t) (n := n)).symm
        · intro hx
          rcases hx with ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          refine ⟨z, hz, ?_⟩
          simpa [lift_formula1, lift_formula] using
            (lift_formula1_subst_shift (f := z) (s := t) (n := n))
      have htemp := ih (n := n + 1)
      have ih' :
          Set.image (fun g : formula L => subst_formula (lift_formula1 g) t (n + 1)) G ⊢
            subst_formula A t (n + 1) := by
        simpa [Set.image_image, Function.comp, lift_formula1, lift_formula] using htemp
      have h' :
          Set.image lift_formula1 (Set.image (fun g : formula L => subst_formula g t n) G) ⊢
            subst_formula A t (n + 1) := by
        simpa [hset] using ih'
      exact prf.allI h'
  | allE₂ A u h ih =>
      exact allE (A := subst_formula A t (n + 1)) (t := subst_term u t n) (ih (n := n))
        (subst_formula2_zero (f := A) (s₁ := u) (s₂ := t) n).symm
  | ref G u =>
      exact prf.ref _ (u[t // n])
  | subst₂ s u f hEq hSub ihEq ihSub =>
      exact subst (f₁ := subst_formula f t (n + 1)) (ihEq (n := n))
        (by simpa [subst_formula2_zero (f := f) (s₁ := s) (s₂ := t) n] using (ihSub (n := n)))
        (subst_formula2_zero (f := f) (s₁ := u) (s₂ := t) n).symm

/-- Cancel a single lifting step by substituting the fresh variable back in. -/
noncomputable def reflect_prf_lift1 {Γ : Set (formula L)} {f : formula L}
    (h : lift_formula1 '' Γ ⊢ lift_formula f 1) : Γ ⊢ f := by
  have h' := substitution (&0 : term L) 0 h
  have h''₀ : Set.image (fun g : formula L => subst_formula (lift_formula1 g) (&0) 0) Γ ⊢
      subst_formula (lift_formula f 1) (&0) 0 := by
    simpa [Set.image_image, Function.comp, lift_formula1, lift_formula] using h'
  have hf : subst_formula (lift_formula f 1) (&0) 0 = f := by
    simpa [lift_formula1, lift_formula] using (lift_formula1_subst (f := f) (s := (&0 : term L)))
  have h'' : Set.image (fun g : formula L => subst_formula (lift_formula1 g) (&0) 0) Γ ⊢ f := by
    exact cast (by rw [hf]) h''₀
  have hset : Set.image (fun g : formula L => subst_formula (lift_formula1 g) (&0) 0) Γ = Γ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy' : subst_formula (lift_formula1 y) (&0) 0 = y := by
        simpa [lift_formula1, lift_formula] using
          (lift_formula1_subst (f := y) (s := (&0 : term L)))
      simpa [hy'] using hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      simpa [lift_formula1, lift_formula] using
        (lift_formula1_subst (f := x) (s := (&0 : term L)))
  simpa [hset] using h''

end fol
end Flypitch
