import Flypitch.FOL.Semantics

universe u

namespace Flypitch
namespace fol

open Classical

variable {L : Language.{u}}

@[simp] def bounded_term_at : {l : Nat} → preterm L l → Nat → Prop
  | _, .var k, n => k < n
  | _, .func _, _ => True
  | _, .app t₁ t₂, n => bounded_term_at t₁ n ∧ bounded_term_at t₂ n

@[simp] def bounded_formula_at : {l : Nat} → preformula L l → Nat → Prop
  | _, .falsum, _ => True
  | _, .equal t₁ t₂, n => bounded_term_at t₁ n ∧ bounded_term_at t₂ n
  | _, .rel _, _ => True
  | _, .apprel f t, n => bounded_formula_at f n ∧ bounded_term_at t n
  | _, .imp f₁ f₂, n => bounded_formula_at f₁ n ∧ bounded_formula_at f₂ n
  | _, .all f, n => bounded_formula_at f (n + 1)

theorem bounded_term_at_mono : {l : Nat} → (t : preterm L l) → {n m : Nat} →
    bounded_term_at t n → n ≤ m → bounded_term_at t m
  | _, .var _, _, _, hk, hnm => lt_of_lt_of_le hk hnm
  | _, .func _, _, _, _, _ => trivial
  | _, .app t₁ t₂, _, _, h, hnm =>
      ⟨bounded_term_at_mono t₁ h.1 hnm, bounded_term_at_mono t₂ h.2 hnm⟩

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

theorem bounded_term_at_lift_irrel : {l : Nat} → (t : preterm L l) → (n m : Nat) →
    bounded_term_at t m → lift_term_at t n m = t
  | _, .var _, _, _, hk => by
      have hmk : ¬ _ ≤ _ := Nat.not_le_of_gt hk
      simp [lift_term_at, hmk]
  | _, .func _, _, _, _ => rfl
  | _, .app t₁ t₂, n, m, h => by
      simp [lift_term_at, bounded_term_at_lift_irrel t₁ n m h.1, bounded_term_at_lift_irrel t₂ n m h.2]

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

/-- Closed formulas, represented as formulas with no free variables. -/
def sentence (L : Language.{u}) : Type u :=
  {f : formula L // bounded_formula_at f 0}

instance : Coe (sentence L) (formula L) where
  coe f := f.1

instance : Bot (sentence L) where
  bot := ⟨⊥, trivial⟩

def sentence.imp (f₁ f₂ : sentence L) : sentence L :=
  ⟨(f₁ : formula L) ⟹ (f₂ : formula L), ⟨f₁.2, f₂.2⟩⟩

infixr:62 " ⟹ " => sentence.imp

def sentence.not (f : sentence L) : sentence L :=
  f ⟹ (⊥ : sentence L)

prefix:max "∼" => sentence.not

instance : Top (sentence L) where
  top := ∼(⊥ : sentence L)

def sentence.and (f₁ f₂ : sentence L) : sentence L :=
  ∼(f₁ ⟹ ∼f₂)

def sentence.or (f₁ f₂ : sentence L) : sentence L :=
  ∼f₁ ⟹ f₂

def sentence.biimp (f₁ f₂ : sentence L) : sentence L :=
  sentence.and (f₁ ⟹ f₂) (f₂ ⟹ f₁)

def sentence.all (f : sentence L) : sentence L :=
  ⟨∀' (f : formula L), by
    simpa using bounded_formula_at_mono (f := (f : formula L)) f.2 (Nat.zero_le 1)⟩

def sentence.ex (f : sentence L) : sentence L :=
  ∼(sentence.all (∼f))

theorem lift_sentence_irrel (f : sentence L) : lift_formula1 (f : formula L) = f := by
  simpa [lift_formula1, lift_formula] using bounded_formula_at_lift_irrel (f := (f : formula L)) 1 0 f.2

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

abbrev sprf (T : Theory L) (f : sentence L) : Type u :=
  Theory.fst T ⊢ (f : formula L)

infix:51 " ⊢ " => sprf

abbrev sprovable (T : Theory L) (f : sentence L) : Prop :=
  Nonempty (T ⊢ f)

infix:51 " ⊢' " => sprovable

def saxm {T : Theory L} {A : sentence L} (h : A ∈ T) : T ⊢ A :=
  prf.axm (show (A : formula L) ∈ Theory.fst T from ⟨A, h, rfl⟩)

def saxm1 {T : Theory L} {A : sentence L} : insert A T ⊢ A :=
  saxm (by
    change A ∈ (insert A T).carrier
    exact Or.inl rfl)

def saxm2 {T : Theory L} {A B : sentence L} : insert A (insert B T) ⊢ B :=
  saxm (by
    change B ∈ (insert A (insert B T)).carrier
    exact Or.inr (Or.inl rfl))

def simpI {T : Theory L} {A B : sentence L} (h : insert A T ⊢ B) : T ⊢ (A ⟹ B) := by
  apply prf.impI
  simpa [sprf, Theory.fst_insert] using h

lemma simpI' {T : Theory L} {A B : sentence L} (h : insert A T ⊢' B) : T ⊢' (A ⟹ B) := by
  rcases h with ⟨h⟩
  exact ⟨simpI h⟩

def simpE {T : Theory L} (A : sentence L) {B : sentence L} (h₁ : T ⊢ (A ⟹ B)) (h₂ : T ⊢ A) :
    T ⊢ B :=
  prf.impE (A : formula L) h₁ h₂

def sfalsumE {T : Theory L} {A : sentence L} (h : insert (∼A) T ⊢ (⊥ : sentence L)) : T ⊢ A := by
  apply prf.falsumE
  simpa [sprf, Theory.fst_insert] using h

@[reducible] def sfalsumE' {T : Theory L} {A : sentence L} (h : insert (∼A) T ⊢' (⊥ : sentence L)) : T ⊢' A := by
  rcases h with ⟨h⟩
  exact ⟨sfalsumE h⟩

noncomputable def sweakening {T T' : Theory L} (hsub : Theory.Subset T' T) {ψ : sentence L} (h : T' ⊢ ψ) : T ⊢ ψ :=
  weakening (Theory.image_subset hsub) h

noncomputable def sweakening1 {T : Theory L} {ψ₁ ψ₂ : sentence L} (h : T ⊢ ψ₂) : insert ψ₁ T ⊢ ψ₂ :=
  sweakening (by
    intro x hx
    exact Or.inr hx) h

noncomputable def sweakening2 {T : Theory L} {ψ₁ ψ₂ ψ₃ : sentence L} (h : insert ψ₁ T ⊢ ψ₃) :
    insert ψ₁ (insert ψ₂ T) ⊢ ψ₃ :=
  sweakening (by
    intro x hx
    change x = ψ₁ ∨ x ∈ T.carrier at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)) h

lemma simpE' {T : Theory L} (A : sentence L) {B : sentence L} (h₁ : T ⊢' (A ⟹ B)) (h₂ : T ⊢' A) :
    T ⊢' B := by
  rcases h₁ with ⟨h₁⟩
  rcases h₂ with ⟨h₂⟩
  exact ⟨simpE A h₁ h₂⟩

lemma snot_and_self'' {T : Theory L} {A : sentence L} (h₁ : T ⊢' A) (h₂ : T ⊢' ∼A) :
    T ⊢' (⊥ : sentence L) :=
  simpE' A h₂ h₁

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

def sprovable_of_provable {T : Theory L} {f : sentence L} (h : Theory.fst T ⊢ (f : formula L)) : T ⊢ f := h

def provable_of_sprovable {T : Theory L} {f : sentence L} (h : T ⊢ f) : Theory.fst T ⊢ (f : formula L) := h

@[reducible] def sprovable_of_sprf {T : Theory L} {f : sentence L} (h : T ⊢ f) : T ⊢' f := ⟨h⟩

theorem sprovable.elim {P : Prop} {T : Theory L} {f : sentence L} (ih : T ⊢ f → P) (h : T ⊢' f) : P := by
  rcases h with ⟨h⟩
  exact ih h

abbrev realize_sentence (M : Structure L) (f : sentence L) : Prop :=
  satisfied_in M (f : formula L)

abbrev all_realize_sentence (M : Structure L) (T : Theory L) : Prop :=
  ∀ ⦃f : sentence L⦄, f ∈ T → realize_sentence M f

lemma all_realize_sentence_of_subset {M : Structure L} {T₁ T₂ : Theory L} (h : all_realize_sentence M T₂)
    (hsub : Theory.Subset T₁ T₂) : all_realize_sentence M T₁ := by
  intro f hf
  exact h (hsub hf)

lemma all_realize_sentence_axm {M : Structure L} {f : sentence L} {T : Theory L}
    (h : all_realize_sentence M (insert f T)) : realize_sentence M f ∧ all_realize_sentence M T := by
  refine ⟨h (by
    change f ∈ (insert f T).carrier
    exact Or.inl rfl), ?_⟩
  intro g hg
  exact h (by
    change g ∈ (insert f T).carrier
    exact Or.inr hg)

@[simp] lemma all_realize_sentence_axm_rw {M : Structure L} {f : sentence L} {T : Theory L} :
    all_realize_sentence M (insert f T) ↔ realize_sentence M f ∧ all_realize_sentence M T := by
  constructor
  · exact all_realize_sentence_axm
  · rintro ⟨hf, hT⟩ g hg
    change g ∈ (insert f T).carrier at hg
    rcases hg with rfl | hg
    · exact hf
    · exact hT hg

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

lemma realize_sentence_of_mem {M : Structure L} {T : Theory L} {f : sentence L}
    (h : all_realize_sentence M T) (hf : f ∈ T) : realize_sentence M f :=
  h hf

def ssatisfied (T : Theory L) (f : sentence L) : Prop :=
  ∀ {M : Structure L}, Nonempty M → all_realize_sentence M T → realize_sentence M f

lemma ssatisfied_of_mem {T : Theory L} {f : sentence L} (hf : f ∈ T) : ssatisfied T f := by
  intro M _ hT
  exact hT hf

def is_consistent (T : Theory L) : Prop :=
  ¬ T ⊢' (⊥ : sentence L)

protected theorem is_consistent.intro {T : Theory L} (h : ¬ T ⊢' (⊥ : sentence L)) : is_consistent T := h
protected theorem is_consistent.elim {T : Theory L} (h : is_consistent T) : ¬ T ⊢' (⊥ : sentence L) := h

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

def is_complete (T : Theory L) : Prop :=
  is_consistent T ∧ ∀ f : sentence L, f ∈ T ∨ ∼f ∈ T

def mem_of_sprf {T : Theory L} (h : is_complete T) {f : sentence L} (hf : T ⊢ f) : f ∈ T := by
  rcases h.2 f with hfT | hnfT
  · exact hfT
  · exfalso
    exact h.1 ⟨simpE f (saxm hnfT) hf⟩

def mem_of_sprovable {T : Theory L} (h : is_complete T) {f : sentence L} (hf : T ⊢' f) : f ∈ T := by
  rcases hf with ⟨hf⟩
  exact mem_of_sprf h hf

abbrev Theory.Consistent (T : Theory L) : Prop := is_consistent T
abbrev Theory.Complete (T : Theory L) : Prop := is_complete T

def TheoryOver (T : Theory L) (_hT : is_consistent T) : Type (u + 1) :=
  {T' : Theory L // Theory.Subset T T' ∧ is_consistent T'}

def over_self (T : Theory L) (hT : is_consistent T) : TheoryOver T hT :=
  ⟨T, ⟨by intro x hx; exact hx, hT⟩⟩

abbrev complete_theory (T : Theory L) : Prop :=
  is_complete T

end fol
end Flypitch
