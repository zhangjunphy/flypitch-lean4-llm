import Flypitch.Compactness
import Mathlib.Order.Zorn

universe u

namespace Flypitch
namespace fol

open Classical

variable {L : Language.{u}}

@[simp] theorem Theory.union_singleton_eq_insert (T : Theory L) (f : sentence L) :
    T ∪ ({f} : Theory L) = insert f T := by
  ext x
  change x ∈ T.carrier ∪ ({f} : Theory L).carrier ↔ x ∈ (insert f T).carrier
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (by simpa using hx)
  · intro hx
    rcases hx with hx | hx
    · exact Or.inr (by simpa using hx)
    · exact Or.inl hx

lemma inconsis_not_of_provable {T : Theory L} {f : sentence L} :
    T ⊢' f → ¬ is_consistent (T ∪ ({∼f} : Theory L)) := by
  intro hf hcons
  have hF : T ∪ ({∼f} : Theory L) ⊢' f := by
    rcases hf with ⟨hf⟩
    exact ⟨sweakening (by
      intro x hx
      exact Or.inl hx) hf⟩
  have hNotF : T ∪ ({∼f} : Theory L) ⊢' ∼f := by
    exact ⟨saxm (by
      exact Or.inr rfl)⟩
  exact hcons (snot_and_self'' hF hNotF)

lemma provable_of_inconsis_not {T : Theory L} {f : sentence L} :
    ¬ is_consistent (T ∪ ({∼f} : Theory L)) → T ⊢' f := by
  intro h
  by_contra h'
  exact h (consis_not_of_not_provable h')

/-- Given a theory `T` and a sentence `ψ`, either `T ∪ {ψ}` or `T ∪ {∼ψ}` is consistent. -/
lemma can_extend (T : Theory L) (ψ : sentence L) (h : is_consistent T) :
    is_consistent (T ∪ ({ψ} : Theory L)) ∨ is_consistent (T ∪ ({∼ψ} : Theory L)) := by
  by_contra hbad
  push Not at hbad
  have hNot : T ⊢' ∼ψ := by
    have h₁ : insert ψ T ⊢' (⊥ : sentence L) := by
      by_contra h₁'
      have hCons : is_consistent (insert ψ T) := by
        unfold is_consistent
        exact h₁'
      exact hbad.1 (by simpa [Theory.union_singleton_eq_insert] using hCons)
    exact simpI' h₁
  have hNotNot : T ⊢' ∼∼ψ := by
    have h₂ : insert (∼ψ) T ⊢' (⊥ : sentence L) := by
      by_contra h₂'
      have hCons : is_consistent (insert (∼ψ) T) := by
        unfold is_consistent
        exact h₂'
      exact hbad.2 (by simpa [Theory.union_singleton_eq_insert] using hCons)
    exact simpI' h₂
  exact h (snot_and_self'' hNot hNotNot)

abbrev Theory_over (T : Theory L) (hT : is_consistent T) : Type (u + 1) :=
  TheoryOver T hT

def TheoryOverSubset {T : Theory L} {hT : is_consistent T} :
    TheoryOver T hT → TheoryOver T hT → Prop :=
  fun T₁ T₂ => Theory.Subset T₁.1 T₂.1

abbrev Theory_over_subset {T : Theory L} {hT : is_consistent T} :=
  TheoryOverSubset (T := T) (hT := hT)

instance {T : Theory L} {hT : is_consistent T} : HasSubset (TheoryOver T hT) where
  Subset := TheoryOverSubset

local instance {T : Theory L} {hT : is_consistent T} :
    Std.Refl (TheoryOverSubset (T := T) (hT := hT)) where
  refl := by
    intro U ψ hψ
    exact hψ

def chainTheoryUnion {T : Theory L} {hT : is_consistent T} (c : Set (TheoryOver T hT)) :
    Theory L :=
  ⟨Set.sUnion ((fun U : TheoryOver T hT => U.1.carrier) '' c)⟩

def limitTheory {T : Theory L} {hT : is_consistent T} (c : Set (TheoryOver T hT)) :
    Theory L :=
  T ∪ chainTheoryUnion c

lemma mem_chainTheoryUnion_iff {T : Theory L} {hT : is_consistent T} {c : Set (TheoryOver T hT)}
    {ψ : sentence L} :
    ψ ∈ chainTheoryUnion c ↔ ∃ U ∈ c, ψ ∈ U.1 := by
  constructor
  · intro hψ
    change ψ ∈ Set.sUnion ((fun U : TheoryOver T hT => U.1.carrier) '' c) at hψ
    rcases hψ with ⟨S, hS, hψS⟩
    rcases hS with ⟨U, hU, rfl⟩
    exact ⟨U, hU, hψS⟩
  · rintro ⟨U, hU, hψU⟩
    change ψ ∈ Set.sUnion ((fun U : TheoryOver T hT => U.1.carrier) '' c)
    exact ⟨U.1.carrier, ⟨U, hU, rfl⟩, hψU⟩

lemma finite_subset_limitTheory {T : Theory L} {hT : is_consistent T}
    {c : Set (TheoryOver T hT)} (hc : IsChain (TheoryOverSubset (T := T) (hT := hT)) c)
    (hcne : c.Nonempty) (Γ : Finset (sentence L))
    (hΓ : ((Γ : Set (sentence L)) ⊆ (limitTheory (T := T) (hT := hT) c).carrier)) :
    ∃ U ∈ c, ((Γ : Set (sentence L)) ⊆ U.1.carrier) := by
  classical
  induction Γ using Finset.induction_on with
  | empty =>
      rcases hcne with ⟨U, hU⟩
      exact ⟨U, hU, by
        intro ψ hψ
        simp at hψ⟩
  | @insert ψ s hψs ih =>
      have hs : ((s : Set (sentence L)) ⊆ (limitTheory (T := T) (hT := hT) c).carrier) := by
        intro φ hφ
        exact hΓ (by simp [hφ])
      rcases ih hs with ⟨Us, hUs, hsUs⟩
      have hψLimit : ψ ∈ limitTheory (T := T) (hT := hT) c := hΓ (by simp)
      rcases hψLimit with hψT | hψUnion
      · exact ⟨Us, hUs, by
          intro φ hφ
          rcases Finset.mem_insert.mp hφ with rfl | hφs
          · exact Us.2.1 hψT
          · exact hsUs hφs⟩
      · rcases (mem_chainTheoryUnion_iff (T := T) (hT := hT) (c := c)).mp hψUnion with
          ⟨Uψ, hUψ, hψUψ⟩
        rcases hc.total hUψ hUs with hUψUs | hUsUψ
        · exact ⟨Us, hUs, by
            intro φ hφ
            rcases Finset.mem_insert.mp hφ with rfl | hφs
            · exact hUψUs hψUψ
            · exact hsUs hφs⟩
        · exact ⟨Uψ, hUψ, by
            intro φ hφ
            rcases Finset.mem_insert.mp hφ with rfl | hφs
            · exact hψUψ
            · exact hUsUψ (hsUs hφs)⟩

lemma consis_limit {T : Theory L} {hT : is_consistent T}
    (c : Set (TheoryOver T hT)) (hc : IsChain (TheoryOverSubset (T := T) (hT := hT)) c) :
    is_consistent (limitTheory (T := T) (hT := hT) c) := by
  classical
  intro hbad
  by_cases hcne : c.Nonempty
  · rcases theory_proof_compactness (T := limitTheory (T := T) (hT := hT) c)
      (ψ := (⊥ : sentence L)) hbad with ⟨Γ, hΓ, hΓsub⟩
    rcases finite_subset_limitTheory (T := T) (hT := hT) hc hcne Γ hΓsub with ⟨U, hU, hΓU⟩
    have hUbad : U.1 ⊢' (⊥ : sentence L) := by
      rcases hΓ with ⟨hΓ⟩
      exact ⟨sweakening hΓU hΓ⟩
    exact U.2.2 hUbad
  · have hcempty : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hcne
    have hEq : limitTheory (T := T) (hT := hT) c = T := by
      ext ψ
      constructor
      · intro hψ
        rcases hψ with hψT | hψUnion
        · exact hψT
        · rcases (mem_chainTheoryUnion_iff (T := T) (hT := hT) (c := c)).mp hψUnion with ⟨U, hU, _⟩
          simp [hcempty] at hU
      · intro hψ
        exact Or.inl hψ
    exact hT (by simpa [hEq] using hbad)

noncomputable def limit_theory {T : Theory L} {hT : is_consistent T}
    (c : Set (TheoryOver T hT)) (hc : IsChain (TheoryOverSubset (T := T) (hT := hT)) c) :
    Σ' U : TheoryOver T hT, ∀ U' ∈ c, TheoryOverSubset (T := T) (hT := hT) U' U := by
  refine ⟨⟨limitTheory (T := T) (hT := hT) c, ?_⟩, ?_⟩
  · refine ⟨by
      intro ψ hψ
      exact Or.inl hψ, consis_limit (T := T) (hT := hT) c hc⟩
  · intro U' hU' ψ hψ
    exact Or.inr ((mem_chainTheoryUnion_iff (T := T) (hT := hT) (c := c)).2 ⟨U', hU', hψ⟩)

lemma can_use_zorn {T : Theory L} {hT : is_consistent T} :
    (∀ c : Set (TheoryOver T hT),
      IsChain (TheoryOverSubset (T := T) (hT := hT)) c →
      ∃ ub : TheoryOver T hT, ∀ a ∈ c, TheoryOverSubset (T := T) (hT := hT) a ub) ∧
    (∀ a b c : TheoryOver T hT,
      TheoryOverSubset (T := T) (hT := hT) a b →
      TheoryOverSubset (T := T) (hT := hT) b c →
      TheoryOverSubset (T := T) (hT := hT) a c) := by
  constructor
  · intro c hc
    exact ⟨(limit_theory (T := T) (hT := hT) c hc).1, (limit_theory (T := T) (hT := hT) c hc).2⟩
  · intro a b c hab hbc ψ hψ
    exact hbc (hab hψ)

/-- Given a consistent theory, return a maximal consistent extension of it. -/
noncomputable def maximal_extension (T : Theory L) (hT : is_consistent T) :
    Σ' T_max : TheoryOver T hT,
      ∀ T' : TheoryOver T hT,
        TheoryOverSubset (T := T) (hT := hT) T_max T' →
        TheoryOverSubset (T := T) (hT := hT) T' T_max := by
  rcases can_use_zorn (T := T) (hT := hT) with ⟨hchains, htrans⟩
  let hmax :=
    Classical.choose <| exists_maximal_of_chains_bounded
      (r := TheoryOverSubset (T := T) (hT := hT)) hchains
      (by
        intro a b c hab hbc
        exact htrans a b c hab hbc)
  exact ⟨hmax, Classical.choose_spec <| exists_maximal_of_chains_bounded
    (r := TheoryOverSubset (T := T) (hT := hT)) hchains
    (by
      intro a b c hab hbc
      exact htrans a b c hab hbc)⟩

lemma cannot_extend_maximal_extension {T : Theory L} {hT : is_consistent T}
    (T_max' : Σ' T_max : TheoryOver T hT,
      ∀ T' : TheoryOver T hT,
        TheoryOverSubset (T := T) (hT := hT) T_max T' →
        TheoryOverSubset (T := T) (hT := hT) T' T_max)
    (ψ : sentence L) (hCons : is_consistent (T_max'.1.1 ∪ ({ψ} : Theory L)))
    (hNot : ψ ∉ T_max'.1.1) : False := by
  let T_bad : TheoryOver T hT :=
    ⟨T_max'.1.1 ∪ ({ψ} : Theory L), ⟨by
      intro φ hφ
      exact Or.inl (T_max'.1.2.1 hφ), hCons⟩⟩
  have hmax := T_max'.2 T_bad (by
    intro φ hφ
    exact Or.inl hφ)
  apply hNot
  exact hmax (by
    exact Or.inr rfl)

lemma complete_maximal_extension_of_consis {T : Theory L} {hT : is_consistent T} :
    is_complete (maximal_extension (L := L) T hT).1.1 := by
  refine ⟨(maximal_extension (L := L) T hT).1.2.2, ?_⟩
  intro ψ
  by_cases hψ : ψ ∈ (maximal_extension (L := L) T hT).1.1
  · exact Or.inl hψ
  · by_cases hNotψ : ∼ψ ∈ (maximal_extension (L := L) T hT).1.1
    · exact Or.inr hNotψ
    · have hFalse : False := by
        rcases can_extend ((maximal_extension (L := L) T hT).1.1) ψ
            (maximal_extension (L := L) T hT).1.2.2 with hCons | hCons
        · exact cannot_extend_maximal_extension
            (T_max' := maximal_extension (L := L) T hT) ψ hCons hψ
        · exact cannot_extend_maximal_extension
            (T_max' := maximal_extension (L := L) T hT) (∼ψ) hCons hNotψ
      exact False.elim hFalse

/-- Given a consistent theory, return a complete extension of it. -/
noncomputable def completion_of_consis (T : Theory L) (h_consis : is_consistent T) :
    Σ' T' : TheoryOver T h_consis, is_complete T'.1 := by
  exact ⟨(maximal_extension (L := L) T h_consis).1,
    complete_maximal_extension_of_consis (L := L) (T := T) (hT := h_consis)⟩

end fol
end Flypitch
