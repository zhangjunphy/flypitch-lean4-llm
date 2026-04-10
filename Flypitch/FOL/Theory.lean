import Flypitch.FOL.Semantics

universe u

namespace Flypitch
namespace fol

/-!
`Flypitch.FOL.Theory` packages closed formulas into theories and records the proof-theoretic
and semantic notions attached to them. It also defines consistency, completeness, and the
basic operations for working inside a theory rather than an arbitrary set of formulas.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false
set_option linter.style.openClassical false

open Classical

variable {L : Language.{u}}

/-- `bounded_term_at t n` means that every free variable of `t` is strictly below `n`. -/
@[simp] def bounded_term_at : {l : Nat} → preterm L l → Nat → Prop
  | _, .var k, n => k < n
  | _, .func _, _ => True
  | _, .app t₁ t₂, n => bounded_term_at t₁ n ∧ bounded_term_at t₂ n

/-- `bounded_formula_at f n` means that every free variable of `f` is strictly below `n`. -/
@[simp] def bounded_formula_at : {l : Nat} → preformula L l → Nat → Prop
  | _, .falsum, _ => True
  | _, .equal t₁ t₂, n => bounded_term_at t₁ n ∧ bounded_term_at t₂ n
  | _, .rel _, _ => True
  | _, .apprel f t, n => bounded_formula_at f n ∧ bounded_term_at t n
  | _, .imp f₁ f₂, n => bounded_formula_at f₁ n ∧ bounded_formula_at f₂ n
  | _, .all f, n => bounded_formula_at f (n + 1)

/-- Increasing the bound preserves boundedness of terms. -/
theorem bounded_term_at_mono : {l : Nat} → (t : preterm L l) → {n m : Nat} →
    bounded_term_at t n → n ≤ m → bounded_term_at t m
  | _, .var _, _, _, hk, hnm => lt_of_lt_of_le hk hnm
  | _, .func _, _, _, _, _ => trivial
  | _, .app t₁ t₂, _, _, h, hnm =>
      ⟨bounded_term_at_mono t₁ h.1 hnm, bounded_term_at_mono t₂ h.2 hnm⟩

/-- Increasing the bound preserves boundedness of formulas. -/
theorem bounded_formula_at_mono : {l : Nat} → (f : preformula L l) → {n m : Nat} →
    bounded_formula_at f n → n ≤ m → bounded_formula_at f m
  | _, .falsum, _, _, _, _ => trivial
  | _, .equal t₁ t₂, _, _, h, hnm =>
      ⟨bounded_term_at_mono t₁ h.1 hnm, bounded_term_at_mono t₂ h.2 hnm⟩
  | _, .rel _, _, _, _, _ => trivial
  | _, .apprel f t, _, _, h, hnm =>
      ⟨bounded_formula_at_mono f h.1 hnm, bounded_term_at_mono t h.2 hnm⟩
  | _, .imp f₁ f₂, _, _, h, hnm =>
      ⟨bounded_formula_at_mono f₁ h.1 hnm, bounded_formula_at_mono f₂ h.2 hnm⟩
  | _, .all f, _, _, h, hnm =>
      bounded_formula_at_mono f h (Nat.add_le_add_right hnm 1)

/-- Lifting above a bound already respected by a term has no effect. -/
theorem bounded_term_at_lift_irrel : {l : Nat} → (t : preterm L l) → (n m : Nat) →
    bounded_term_at t m → lift_term_at t n m = t
  | _, .var _, _, _, hk => by
      have hmk : ¬ _ ≤ _ := Nat.not_le_of_gt hk
      simp [lift_term_at, hmk]
  | _, .func _, _, _, _ => rfl
  | _, .app t₁ t₂, n, m, h => by
      simp [lift_term_at, bounded_term_at_lift_irrel t₁ n m h.1, bounded_term_at_lift_irrel t₂ n m h.2]

/-- Lifting above a bound already respected by a formula has no effect. -/
theorem bounded_formula_at_lift_irrel : {l : Nat} → (f : preformula L l) → (n m : Nat) →
    bounded_formula_at f m → lift_formula_at f n m = f
  | _, .falsum, _, _, _ => rfl
  | _, .equal t₁ t₂, n, m, h => by
      simp [lift_formula_at, bounded_term_at_lift_irrel t₁ n m h.1, bounded_term_at_lift_irrel t₂ n m h.2]
  | _, .rel _, _, _, _ => rfl
  | _, .apprel f t, n, m, h => by
      simp [lift_formula_at, bounded_formula_at_lift_irrel f n m h.1, bounded_term_at_lift_irrel t n m h.2]
  | _, .imp f₁ f₂, n, m, h => by
      simp [lift_formula_at, bounded_formula_at_lift_irrel f₁ n m h.1, bounded_formula_at_lift_irrel f₂ n m h.2]
  | _, .all f, n, m, h => by
      simpa [lift_formula_at] using bounded_formula_at_lift_irrel f n (m + 1) h

/-- Substituting at a variable bound already respected by a term has no effect. -/
theorem bounded_term_at_subst_irrel : {l : Nat} → (t : preterm L l) → {n : Nat} →
    bounded_term_at t n → (s : term L) → subst_term t s n = t
  | _, .var k, _, hk, s => by
      simpa using (subst_term_var_lt (L := L) (s := s) hk)
  | _, .func _, _, _, _ => rfl
  | _, .app t₁ t₂, _, h, s => by
      simp [subst_term, bounded_term_at_subst_irrel t₁ h.1 s, bounded_term_at_subst_irrel t₂ h.2 s]

/-- Substituting at a variable bound already respected by a formula has no effect. -/
theorem bounded_formula_at_subst_irrel : {l : Nat} → (f : preformula L l) → {n : Nat} →
    bounded_formula_at f n → (s : term L) → subst_formula f s n = f
  | _, .falsum, _, _, _ => rfl
  | _, .equal t₁ t₂, _, h, s => by
      simp [subst_formula, bounded_term_at_subst_irrel t₁ h.1 s, bounded_term_at_subst_irrel t₂ h.2 s]
  | _, .rel _, _, _, _ => rfl
  | _, .apprel f t, _, h, s => by
      simp [subst_formula, bounded_formula_at_subst_irrel f h.1 s, bounded_term_at_subst_irrel t h.2 s]
  | _, .imp f₁ f₂, _, h, s => by
      simp [subst_formula, bounded_formula_at_subst_irrel f₁ h.1 s, bounded_formula_at_subst_irrel f₂ h.2 s]
  | _, .all f, _, h, s => by
      simpa [subst_formula] using bounded_formula_at_subst_irrel f h s

/-- Substituting a closed term into a term bounded by `n + 1` lowers the bound to `n`. -/
theorem bounded_term_at_subst_closed : {l : Nat} → (t : preterm L l) → {n : Nat} → {s : term L} →
    bounded_term_at t (n + 1) → bounded_term_at s 0 → bounded_term_at (subst_term t s n) n
  | _, .var k, n, s, hk, hs => by
      by_cases hlt : k < n
      · simpa [subst_term, subst_realize, hlt] using hlt
      · by_cases hgt : n < k
        · exfalso
          exact Nat.not_lt_of_ge (Nat.le_of_lt_succ hk) hgt
        · have hEq : k = n := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
          subst k
          have hs' : bounded_term_at (lift_term s n) n := by
            have hlift : lift_term s n = s := by
              simpa [lift_term] using bounded_term_at_lift_irrel (t := s) n 0 hs
            simpa [hlift] using bounded_term_at_mono (t := s) hs (Nat.zero_le n)
          simpa [subst_term, subst_realize, hlt, hgt] using hs'
  | _, .func _, _, _, _, _ => trivial
  | _, .app t₁ t₂, _, s, ht, hs => by
      exact ⟨bounded_term_at_subst_closed t₁ ht.1 hs, bounded_term_at_subst_closed t₂ ht.2 hs⟩

/-- Substituting a closed term into a formula bounded by `n + 1` lowers the bound to `n`. -/
theorem bounded_formula_at_subst_closed : {l : Nat} → (f : preformula L l) → {n : Nat} → {s : term L} →
    bounded_formula_at f (n + 1) → bounded_term_at s 0 → bounded_formula_at (subst_formula f s n) n
  | _, .falsum, n, s, _, _ => trivial
  | _, .equal t₁ t₂, n, s, hf, hs => by
      exact ⟨bounded_term_at_subst_closed t₁ hf.1 hs, bounded_term_at_subst_closed t₂ hf.2 hs⟩
  | _, .rel _, n, s, _, _ => trivial
  | _, .apprel f t, n, s, hf, hs => by
      exact ⟨bounded_formula_at_subst_closed f hf.1 hs, bounded_term_at_subst_closed t hf.2 hs⟩
  | _, .imp f₁ f₂, n, s, hf, hs => by
      exact ⟨bounded_formula_at_subst_closed f₁ hf.1 hs, bounded_formula_at_subst_closed f₂ hf.2 hs⟩
  | _, .all f, n, s, hf, hs => by
      simpa [subst_formula] using bounded_formula_at_subst_closed (f := f) (n := n + 1) (s := s) hf hs

/-- Lifting above a bound and then substituting the new variable back in cancels for terms. -/
theorem lift_subst_term_cancel : {l : Nat} → (t : preterm L l) → (n : Nat) →
    subst_term (lift_term_at t 1 (n + 1)) (&0 : term L) n = t
  | _, .var k, n => by
      by_cases hlt : n < k
      · have hle : n + 1 ≤ k := Nat.succ_le_of_lt hlt
        have hgt : n < k + 1 := Nat.lt_succ_of_lt hlt
        simp [lift_term_at, hle, subst_term_var_gt, hgt]
      · by_cases heq : k = n
        · subst k
          have hnot : ¬ (n + 1 ≤ n) := Nat.not_succ_le_self n
          simp [lift_term_at, hnot, subst_term_var_eq]
        · have hklt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) heq
          have hnot : ¬ (n + 1 ≤ k) := Nat.not_le_of_gt (Nat.lt_succ_of_lt hklt)
          simp [lift_term_at, hnot, subst_term_var_lt, hklt]
  | _, .func _, _ => rfl
  | _, .app t₁ t₂, n => by
      simp [subst_term, lift_subst_term_cancel t₁ n, lift_subst_term_cancel t₂ n]

/-- Lifting above a bound and then substituting the new variable back in cancels for formulas. -/
theorem lift_subst_formula_cancel : {l : Nat} → (f : preformula L l) → (n : Nat) →
    subst_formula (lift_formula_at f 1 (n + 1)) (&0 : term L) n = f
  | _, .falsum, _ => rfl
  | _, .equal t₁ t₂, n => by
      simp [lift_formula_at, subst_formula, lift_subst_term_cancel t₁ n, lift_subst_term_cancel t₂ n]
  | _, .rel _, _ => rfl
  | _, .apprel f t, n => by
      simp [lift_formula_at, subst_formula, lift_subst_formula_cancel f n, lift_subst_term_cancel t n]
  | _, .imp f₁ f₂, n => by
      simp [lift_formula_at, subst_formula, lift_subst_formula_cancel f₁ n, lift_subst_formula_cancel f₂ n]
  | _, .all f, n => by
      simpa [lift_formula_at, subst_formula] using lift_subst_formula_cancel (f := f) (n := n + 1)

/-- Closed formulas, represented as formulas with no free variables. -/
def sentence (L : Language.{u}) : Type u :=
  {f : formula L // bounded_formula_at f 0}

instance : Coe (sentence L) (formula L) where
  coe f := f.1

instance : Bot (sentence L) where
  bot := ⟨⊥, trivial⟩

/-- Implication of closed formulas. -/
def sentence.imp (f₁ f₂ : sentence L) : sentence L :=
  ⟨(f₁ : formula L) ⟹ (f₂ : formula L), ⟨f₁.2, f₂.2⟩⟩

infixr:62 " ⟹ " => sentence.imp

/-- Negation of a sentence. -/
def sentence.not (f : sentence L) : sentence L :=
  f ⟹ (⊥ : sentence L)

prefix:max "∼" => sentence.not

instance : Top (sentence L) where
  top := ∼(⊥ : sentence L)

/-- Conjunction of sentences. -/
def sentence.and (f₁ f₂ : sentence L) : sentence L :=
  ∼(f₁ ⟹ ∼f₂)

/-- Disjunction of sentences. -/
def sentence.or (f₁ f₂ : sentence L) : sentence L :=
  ∼f₁ ⟹ f₂

/-- Biconditional of sentences. -/
def sentence.biimp (f₁ f₂ : sentence L) : sentence L :=
  sentence.and (f₁ ⟹ f₂) (f₂ ⟹ f₁)

/-- Universal quantification of a sentence, viewed as opening one bound variable. -/
def sentence.all (f : sentence L) : sentence L :=
  ⟨∀' (f : formula L), by
    simpa using bounded_formula_at_mono (f := (f : formula L)) f.2 (Nat.zero_le 1)⟩

/-- Existential quantification of a sentence. -/
def sentence.ex (f : sentence L) : sentence L :=
  ∼(sentence.all (∼f))

/-- Lifting a closed formula is definitionally irrelevant. -/
theorem lift_sentence_irrel (f : sentence L) : lift_formula1 (f : formula L) = f := by
  simpa [lift_formula1, lift_formula] using bounded_formula_at_lift_irrel (f := (f : formula L)) 1 0 f.2

/-- Substituting into a closed formula is definitionally irrelevant. -/
theorem subst_sentence_irrel (f : sentence L) (s : term L) :
    subst_formula (f : formula L) s 0 = f := by
  simpa using bounded_formula_at_subst_irrel (f := (f : formula L)) (n := 0) f.2 s

/-- A theory is a set of closed formulas. -/
structure Theory (L : Language.{u}) : Type (u + 1) where
  carrier : Set (sentence L)

namespace Theory

instance : Membership (sentence L) (Theory L) where
  mem T x := x ∈ T.carrier

instance : EmptyCollection (Theory L) where
  emptyCollection := ⟨∅⟩

instance : Insert (sentence L) (Theory L) where
  insert a T := ⟨Set.insert a T.carrier⟩

instance : Singleton (sentence L) (Theory L) where
  singleton a := ⟨{a}⟩

instance : Union (Theory L) where
  union T T' := ⟨T.carrier ∪ T'.carrier⟩

instance : Coe (Set (sentence L)) (Theory L) where
  coe S := ⟨S⟩

/-- Inclusion of theories. -/
def Subset (T T' : Theory L) : Prop :=
  T.carrier ⊆ T'.carrier

@[ext] theorem ext {T T' : Theory L} (h : ∀ x : sentence L, x ∈ T ↔ x ∈ T') : T = T' := by
  cases T with
  | mk Tc =>
      cases T' with
      | mk Tc' =>
          have h' : Tc = Tc' := by
            ext x
            exact h x
          cases h'
          rfl

@[reducible] def fst (T : Theory L) : Set (formula L) :=
  Subtype.val '' T.carrier

/-- Inclusion of theories induces inclusion of the underlying sets of formulas. -/
theorem image_subset {T T' : Theory L} (h : Subset T T') : T.fst ⊆ T'.fst := by
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩
  exact ⟨g, h hg, rfl⟩

@[simp] theorem fst_insert (A : sentence L) (T : Theory L) : (insert A T).fst = Set.insert (A : formula L) T.fst := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨g, hg, rfl⟩
    change g = A ∨ g ∈ T.carrier at hg
    rcases hg with rfl | hg
    · exact Or.inl rfl
    · exact Or.inr ⟨g, hg, rfl⟩
  · intro hf
    rcases hf with rfl | hf
    · exact ⟨A, Or.inl rfl, rfl⟩
    · rcases hf with ⟨g, hg, rfl⟩
      exact ⟨g, Or.inr hg, rfl⟩

end Theory

/-- Lifting does nothing on the underlying formulas of a theory of sentences. -/
lemma lift_Theory_irrel (T : Theory L) : Set.image lift_formula1 (Theory.fst T) = Theory.fst T := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨g, hg, rfl⟩
    rcases hg with ⟨s, hs, rfl⟩
    exact ⟨s, hs, (lift_sentence_irrel s).symm⟩
  · intro hf
    rcases hf with ⟨s, hs, rfl⟩
    refine ⟨(s : formula L), ⟨s, hs, rfl⟩, ?_⟩
    exact lift_sentence_irrel s

/-- Proofs from a theory, viewed through its underlying set of formulas. -/
abbrev sprf (T : Theory L) (f : sentence L) : Type u :=
  Theory.fst T ⊢ (f : formula L)

infix:51 " ⊢ " => sprf

/-- Truncated provability from a theory. -/
abbrev sprovable (T : Theory L) (f : sentence L) : Prop :=
  Nonempty (T ⊢ f)

infix:51 " ⊢' " => sprovable

/-- Any sentence already in the theory is provable from it. -/
def saxm {T : Theory L} {A : sentence L} (h : A ∈ T) : T ⊢ A :=
  prf.axm (show (A : formula L) ∈ Theory.fst T from ⟨A, h, rfl⟩)

/-- The newest inserted sentence is provable immediately. -/
def saxm1 {T : Theory L} {A : sentence L} : insert A T ⊢ A :=
  saxm (by
    change A ∈ (insert A T).carrier
    exact Or.inl rfl)

/-- The second newest inserted sentence is provable immediately. -/
def saxm2 {T : Theory L} {A B : sentence L} : insert A (insert B T) ⊢ B :=
  saxm (by
    change B ∈ (insert A (insert B T)).carrier
    exact Or.inr (Or.inl rfl))

/-- Implication introduction internal to theories. -/
def simpI {T : Theory L} {A B : sentence L} (h : insert A T ⊢ B) : T ⊢ (A ⟹ B) := by
  apply prf.impI
  simpa [sprf, Theory.fst_insert] using h

/-- Truncated implication introduction internal to theories. -/
lemma simpI' {T : Theory L} {A B : sentence L} (h : insert A T ⊢' B) : T ⊢' (A ⟹ B) := by
  rcases h with ⟨h⟩
  exact ⟨simpI h⟩

/-- Implication elimination internal to theories. -/
def simpE {T : Theory L} (A : sentence L) {B : sentence L} (h₁ : T ⊢ (A ⟹ B)) (h₂ : T ⊢ A) :
    T ⊢ B :=
  prf.impE (A : formula L) h₁ h₂

/-- Ex falso internal to theories using an explicit negated assumption. -/
def sfalsumE {T : Theory L} {A : sentence L} (h : insert (∼A) T ⊢ (⊥ : sentence L)) : T ⊢ A := by
  apply prf.falsumE
  simpa [sprf, Theory.fst_insert] using h

theorem sfalsumE' {T : Theory L} {A : sentence L} (h : insert (∼A) T ⊢' (⊥ : sentence L)) : T ⊢' A := by
  rcases h with ⟨h⟩
  exact ⟨sfalsumE h⟩

/-- Weakening of theory proofs along inclusion of theories. -/
noncomputable def sweakening {T T' : Theory L} (hsub : Theory.Subset T' T) {ψ : sentence L} (h : T' ⊢ ψ) : T ⊢ ψ :=
  weakening (Theory.image_subset hsub) h

/-- One-step weakening for theory proofs. -/
noncomputable def sweakening1 {T : Theory L} {ψ₁ ψ₂ : sentence L} (h : T ⊢ ψ₂) : insert ψ₁ T ⊢ ψ₂ :=
  sweakening (by
    intro x hx
    exact Or.inr hx) h

/-- Two-step weakening for theory proofs. -/
noncomputable def sweakening2 {T : Theory L} {ψ₁ ψ₂ ψ₃ : sentence L} (h : insert ψ₁ T ⊢ ψ₃) :
    insert ψ₁ (insert ψ₂ T) ⊢ ψ₃ :=
  sweakening (by
    intro x hx
    change x = ψ₁ ∨ x ∈ T.carrier at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)) h

/-- Truncated implication elimination internal to theories. -/
lemma simpE' {T : Theory L} (A : sentence L) {B : sentence L} (h₁ : T ⊢' (A ⟹ B)) (h₂ : T ⊢' A) :
    T ⊢' B := by
  rcases h₁ with ⟨h₁⟩
  rcases h₂ with ⟨h₂⟩
  exact ⟨simpE A h₁ h₂⟩

/-- A sentence and its negation yield falsum. -/
lemma snot_and_self'' {T : Theory L} {A : sentence L} (h₁ : T ⊢' A) (h₂ : T ⊢' ∼A) :
    T ⊢' (⊥ : sentence L) :=
  simpE' A h₂ h₁

/-- Proof by cases inside a theory. -/
lemma sprf_by_cases {Γ : Theory L} (f₁ : sentence L) {f₂ : sentence L}
    (h₁ : insert f₁ Γ ⊢' f₂) (h₂ : insert (∼f₁) Γ ⊢' f₂) : Γ ⊢' f₂ := by
  apply sfalsumE'
  have hF1 : insert (∼f₂) Γ ⊢' f₁ := by
    apply sfalsumE'
    have h₂' : insert (∼f₁) (insert (∼f₂) Γ) ⊢' f₂ := by
      rcases h₂ with ⟨h₂⟩
      exact ⟨sweakening2 h₂⟩
    have hNotF2 : insert (∼f₁) (insert (∼f₂) Γ) ⊢' ∼f₂ := ⟨saxm2⟩
    exact snot_and_self'' h₂' hNotF2
  have hImp : insert (∼f₂) Γ ⊢' (f₁ ⟹ f₂) := by
    rcases h₁ with ⟨h₁⟩
    exact ⟨sweakening1 (simpI h₁)⟩
  have hF2 : insert (∼f₂) Γ ⊢' f₂ := simpE' f₁ hImp hF1
  have hNotF2 : insert (∼f₂) Γ ⊢' ∼f₂ := ⟨saxm1⟩
  exact snot_and_self'' hF2 hNotF2

/-- Reinterpret a formula-level proof as a sentence-level proof. -/
def sprovable_of_provable {T : Theory L} {f : sentence L} (h : Theory.fst T ⊢ (f : formula L)) : T ⊢ f := h

/-- Forget that a sentence-level proof came from a theory. -/
def provable_of_sprovable {T : Theory L} {f : sentence L} (h : T ⊢ f) : Theory.fst T ⊢ (f : formula L) := h

theorem sprovable_of_sprf {T : Theory L} {f : sentence L} (h : T ⊢ f) : T ⊢' f := ⟨h⟩

/-- Eliminate the truncation in `sprovable`. -/
theorem sprovable.elim {P : Prop} {T : Theory L} {f : sentence L} (ih : T ⊢ f → P) (h : T ⊢' f) : P := by
  rcases h with ⟨h⟩
  exact ih h

/-- Satisfaction of a sentence in a structure. -/
abbrev realize_sentence (M : Structure L) (f : sentence L) : Prop :=
  satisfied_in M (f : formula L)

/-- Every sentence in `T` is satisfied in `M`. -/
abbrev all_realize_sentence (M : Structure L) (T : Theory L) : Prop :=
  ∀ ⦃f : sentence L⦄, f ∈ T → realize_sentence M f

/-- Satisfaction is monotone along inclusion of theories. -/
lemma all_realize_sentence_of_subset {M : Structure L} {T₁ T₂ : Theory L} (h : all_realize_sentence M T₂)
    (hsub : Theory.Subset T₁ T₂) : all_realize_sentence M T₁ := by
  intro f hf
  exact h (hsub hf)

/-- Satisfaction of an inserted sentence splits into the new axiom and the old theory. -/
lemma all_realize_sentence_axm {M : Structure L} {f : sentence L} {T : Theory L}
    (h : all_realize_sentence M (insert f T)) : realize_sentence M f ∧ all_realize_sentence M T := by
  refine ⟨h (by
    change f ∈ (insert f T).carrier
    exact Or.inl rfl), ?_⟩
  intro g hg
  exact h (by
    change g ∈ (insert f T).carrier
    exact Or.inr hg)

/-- Rewriting version of `all_realize_sentence_axm`. -/
@[simp] lemma all_realize_sentence_axm_rw {M : Structure L} {f : sentence L} {T : Theory L} :
    all_realize_sentence M (insert f T) ↔ realize_sentence M f ∧ all_realize_sentence M T := by
  constructor
  · exact all_realize_sentence_axm
  · rintro ⟨hf, hT⟩ g hg
    change g ∈ (insert f T).carrier at hg
    rcases hg with rfl | hg
    · exact hf
    · exact hT hg

/-- A singleton theory is satisfied exactly when its unique sentence is. -/
@[simp] lemma all_realize_sentence_singleton {M : Structure L} {f : sentence L} :
    all_realize_sentence M ({f} : Theory L) ↔ realize_sentence M f := by
  constructor
  · intro h
    exact h (by
      change f ∈ ({f} : Theory L).carrier
      exact rfl)
  · intro h g hg
    change g ∈ ({f} : Theory L).carrier at hg
    have hg' : g = f := hg
    simpa [hg'] using h

/-- Extract satisfaction of a particular member of a theory. -/
lemma realize_sentence_of_mem {M : Structure L} {T : Theory L} {f : sentence L}
    (h : all_realize_sentence M T) (hf : f ∈ T) : realize_sentence M f :=
  h hf

/-- Semantic consequence between theories and sentences. -/
def ssatisfied (T : Theory L) (f : sentence L) : Prop :=
  ∀ {M : Structure L}, Nonempty M → all_realize_sentence M T → realize_sentence M f

/-- Any sentence already in a theory is a semantic consequence of it. -/
lemma ssatisfied_of_mem {T : Theory L} {f : sentence L} (hf : f ∈ T) : ssatisfied T f := by
  intro M _ hT
  exact hT hf

/-- A theory is consistent when it does not prove falsum. -/
def is_consistent (T : Theory L) : Prop :=
  ¬ T ⊢' (⊥ : sentence L)

protected theorem is_consistent.intro {T : Theory L} (h : ¬ T ⊢' (⊥ : sentence L)) : is_consistent T := h
protected theorem is_consistent.elim {T : Theory L} (h : is_consistent T) : ¬ T ⊢' (⊥ : sentence L) := h

/-- If `f` is not provable, adjoining `¬f` preserves consistency. -/
lemma consis_not_of_not_provable {T : Theory L} {f : sentence L} (h₁ : ¬ T ⊢' f) :
    is_consistent (T ∪ ({∼f} : Theory L)) := by
  intro h₂
  apply h₁
  have hEq : T ∪ ({∼f} : Theory L) = insert (∼f) T := by
    ext x
    change x ∈ T.carrier ∪ ({∼f} : Theory L).carrier ↔ x ∈ (insert (∼f) T).carrier
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact Or.inr hx
      · exact Or.inl hx
    · intro hx
      rcases hx with hx | hx
      · exact Or.inr hx
      · exact Or.inl hx
  have h₂' : insert (∼f) T ⊢' (⊥ : sentence L) := by
    simpa [hEq] using h₂
  exact sfalsumE' h₂'

/-- A complete theory is consistent and decides every sentence. -/
def is_complete (T : Theory L) : Prop :=
  is_consistent T ∧ ∀ f : sentence L, f ∈ T ∨ ∼f ∈ T

/-- In a complete theory, every provable sentence is already an axiom. -/
theorem mem_of_sprf {T : Theory L} (h : is_complete T) {f : sentence L} (hf : T ⊢ f) : f ∈ T := by
  rcases h.2 f with hfT | hnfT
  · exact hfT
  · exfalso
    exact h.1 ⟨simpE f (saxm hnfT) hf⟩

/-- Truncated version of `mem_of_sprf`. -/
theorem mem_of_sprovable {T : Theory L} (h : is_complete T) {f : sentence L} (hf : T ⊢' f) : f ∈ T := by
  rcases hf with ⟨hf⟩
  exact mem_of_sprf h hf

/-- In a complete theory, implication can be introduced from a meta-level implication on provability. -/
theorem impI_of_is_complete {T : Theory L} (h : is_complete T) {f₁ f₂ : sentence L}
    (hf : T ⊢' f₁ → T ⊢' f₂) : T ⊢' (f₁ ⟹ f₂) := by
  apply simpI'
  rcases h.2 f₁ with hf₁ | hnf₁
  · exact ⟨sweakening1 (Classical.choice (hf ⟨saxm hf₁⟩))⟩
  · apply sfalsumE'
    let hbot : insert f₁ T ⊢' (⊥ : sentence L) := simpE' f₁ ⟨sweakening1 (saxm hnf₁)⟩ ⟨saxm1⟩
    exact ⟨sweakening1 (Classical.choice hbot)⟩

/-- In a complete theory, non-provability of `f` yields provability of `¬f`. -/
theorem notI_of_is_complete {T : Theory L} (h : is_complete T) {f : sentence L}
    (hf : ¬ T ⊢' f) : T ⊢' ∼f := by
  apply impI_of_is_complete h
  intro hf'
  exact False.elim (hf hf')

/-- Synonym for `is_consistent` under the `Theory` namespace. -/
abbrev Theory.Consistent (T : Theory L) : Prop := is_consistent T
/-- Synonym for `is_complete` under the `Theory` namespace. -/
abbrev Theory.Complete (T : Theory L) : Prop := is_complete T

/-- Consistent theory extensions ordered by inclusion. -/
def TheoryOver (T : Theory L) (hT : is_consistent T) : Type (u + 1) :=
  let _ := hT
  {T' : Theory L // Theory.Subset T T' ∧ is_consistent T'}

/-- The base theory regarded as an extension of itself. -/
def over_self (T : Theory L) (hT : is_consistent T) : TheoryOver T hT :=
  ⟨T, ⟨by intro x hx; exact hx, hT⟩⟩

/-- Alias used when completeness is the relevant viewpoint. -/
abbrev complete_theory (T : Theory L) : Prop :=
  is_complete T

end fol
end Flypitch
