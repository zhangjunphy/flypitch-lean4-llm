import Flypitch.FOL.Theory
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Basic

universe u v

namespace Flypitch

open Classical

def list_except {α : Type u} [DecidableEq α] (xs : List α) (x : α) (T : Set α)
    (h : ∀ y ∈ xs, y ≠ x → y ∈ T) :
    Σ' ys : List α, ({ϕ | ϕ ∈ ys} ⊆ T ∧ (∀ y ∈ ys, y ≠ x)) ∧ (∀ y ∈ xs, y ≠ x → y ∈ ys) := by
  refine ⟨xs.filter (fun y => decide (y ≠ x)), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro y hy
      have hyx : y ≠ x := by
        let hyb := (List.mem_filter.mp hy).2
        by_cases hxy : y ≠ x
        · exact hxy
        · simp [hxy] at hyb
      exact h y (List.mem_of_mem_filter hy) hyx
    · intro y hy
      let hyb := (List.mem_filter.mp hy).2
      by_cases hxy : y ≠ x
      · exact hxy
      · simp [hxy] at hyb
  · intro y hy hyx
    exact List.mem_filter.mpr ⟨hy, by simpa [hyx]⟩

namespace fol

@[reducible] def finTheory {L : Language.{u}} (Γ : Finset (sentence L)) : Theory L :=
  ⟨(Γ : Set (sentence L))⟩

noncomputable def image_lift {α : Type u} {β : Type v} {f : α → β} {S : Set α} {x : β}
    (hx : x ∈ f '' S) : Σ' x' : α, x' ∈ S ∧ f x' = x := by
  let h' : ∃ x' : α, x' ∈ S ∧ f x' = x := by simpa using hx
  exact ⟨Classical.choose h', Classical.choose_spec h'⟩

noncomputable def image_lift_list {α : Type u} {β : Type v} {f : α → β} {S : Set α} :
    {xs : List β} → ({x | x ∈ xs} ⊆ f '' S) →
      Σ' ys : List α, ({y' | y' ∈ ys} ⊆ S) ∧ f '' {y | y ∈ ys} = {x | x ∈ xs}
  | [], _ => by
      refine ⟨[], ?_⟩
      refine ⟨?_, ?_⟩
      · intro y hy
        cases hy
      · ext x
        simp
  | x :: xs, hsub => by
      rcases image_lift (x := x) (hsub (by simp)) with ⟨y, hyS, hyEq⟩
      rcases image_lift_list (xs := xs) (by
        intro z hz
        exact hsub (by
          simpa [Set.mem_setOf_eq] using (Or.inr hz : z = x ∨ z ∈ xs))) with ⟨ys, hysS, hysImage⟩
      refine ⟨y :: ys, ?_⟩
      refine ⟨?_, ?_⟩
      · intro z hz
        simp at hz
        rcases hz with rfl | hz
        · exact hyS
        · exact hysS hz
      · ext z
        constructor
        · intro hz
          rcases hz with ⟨a, ha, hfa⟩
          have ha' : a = y ∨ a ∈ ys := by simpa [Set.mem_setOf_eq] using ha
          rcases ha' with rfl | ha
          · have hz' : z = x := by simpa [hyEq] using hfa.symm
            simpa [Set.mem_setOf_eq, hz']
          · right
            have hz' : z ∈ ({x | x ∈ xs} : Set β) := by
              rw [← hysImage]
              exact ⟨a, ha, hfa⟩
            simpa [Set.mem_setOf_eq] using hz'
        · intro hz
          have hz' : z = x ∨ z ∈ xs := by simpa [Set.mem_setOf_eq] using hz
          rcases hz' with rfl | hz'
          · exact ⟨y, by simp, hyEq⟩
          · have hz'' : z ∈ f '' {y | y ∈ ys} := by
              rw [hysImage]
              simpa [Set.mem_setOf_eq] using hz'
            rcases hz'' with ⟨a, ha, hfa⟩
            refine ⟨a, ?_, hfa⟩
            simpa [Set.mem_setOf_eq] using (Or.inr ha : a = y ∨ a ∈ ys)

theorem proof_compactness {L : Language.{u}} {ψ : formula L} {T : Set (formula L)} :
    T ⊢' ψ → ∃ Γ : Finset (formula L), ((Γ : Set (formula L)) ⊢' ψ) ∧ ((Γ : Set (formula L)) ⊆ T) := by
  classical
  intro h
  rcases h with ⟨p⟩
  induction p with
  | axm hmem =>
      rename_i Γ A
      refine ⟨{A}, ?_, ?_⟩
      · exact ⟨prf.axm (by simp)⟩
      · intro x hx
        have hxA : x = A := by simpa using hx
        simpa [hxA] using hmem
  | impI h ih =>
      rename_i Γ A B
      rcases ih with ⟨Δ, hΔ, hsub⟩
      refine ⟨Δ.erase A, ?_, ?_⟩
      · apply impI'
        apply weakening'
        · intro x hx
          by_cases hxa : x = A
          · exact Or.inl hxa
          · exact Or.inr (by
              have hx' : x ∈ Δ ∧ x ≠ A := ⟨hx, hxa⟩
              exact by simpa [Finset.mem_erase] using hx')
        · exact hΔ
      · intro x hx
        have hx' : x ∈ Δ ∧ x ≠ A := by simpa [Finset.mem_erase] using hx
        exact (hsub hx'.1).resolve_left hx'.2
  | impE A hImp hA ihImp ihA =>
      rcases ihImp with ⟨Δ₁, h₁, hsub₁⟩
      rcases ihA with ⟨Δ₂, h₂, hsub₂⟩
      refine ⟨Δ₁ ∪ Δ₂, ?_, ?_⟩
      · exact impE' A
          (weakening' (by intro x hx; simp [hx]) h₁)
          (weakening' (by intro x hx; simp [hx]) h₂)
      · intro x hx
        simp at hx
        exact hx.elim (fun hx₁ => hsub₁ hx₁) (fun hx₂ => hsub₂ hx₂)
  | falsumE h ih =>
      rename_i Γ A
      rcases ih with ⟨Δ, hΔ, hsub⟩
      refine ⟨Δ.erase (∼A), ?_, ?_⟩
      · apply falsumE'
        apply weakening'
        · intro x hx
          by_cases hxa : x = ∼A
          · exact Or.inl hxa
          · exact Or.inr (by
              have hx' : x ∈ Δ ∧ x ≠ ∼A := ⟨hx, hxa⟩
              exact by simpa [Finset.mem_erase] using hx')
        · exact hΔ
      · intro x hx
        have hx' : x ∈ Δ ∧ x ≠ ∼A := by simpa [Finset.mem_erase] using hx
        exact (hsub hx'.1).resolve_left hx'.2
  | allI h ih =>
      rename_i Γ A
      rcases ih with ⟨Δ, hΔ, hsub⟩
      let pre : {x // x ∈ (Δ : Set (formula L))} → formula L :=
        fun x => Classical.choose (hsub x.property)
      let Δ' : Finset (formula L) := Δ.attach.image pre
      have hΔ'sub : ((Δ' : Finset (formula L)) : Set (formula L)) ⊆ Γ := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        exact (Classical.choose_spec (hsub y.property)).1
      have himage : lift_formula1 '' (((Δ' : Finset (formula L)) : Set (formula L))) = (Δ : Set (formula L)) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
          have hz' : lift_formula1 (pre z) = z := (Classical.choose_spec (hsub z.property)).2
          simpa [hz'] using z.property
        · intro hx
          let z : {x // x ∈ (Δ : Set (formula L))} := ⟨x, hx⟩
          refine ⟨pre z, ?_, ?_⟩
          · change pre z ∈ Δ.attach.image pre
            exact Finset.mem_image.mpr ⟨z, by simp [z], rfl⟩
          · exact (Classical.choose_spec (hsub hx)).2
      have hΔ' : lift_formula1 '' (((Δ' : Finset (formula L)) : Set (formula L))) ⊢' A := by
        simpa [himage] using hΔ
      exact ⟨Δ', allI' hΔ', hΔ'sub⟩
  | allE₂ A t h ih =>
      rcases ih with ⟨Δ, hΔ, hsub⟩
      exact ⟨Δ, allE₂' hΔ, hsub⟩
  | ref Γ t =>
      exact ⟨∅, by simpa using ref' (∅ : Set (formula L)) t, by simp⟩
  | subst₂ s t f hEq hSub ihEq ihSub =>
      rcases ihEq with ⟨Δ₁, h₁, hsub₁⟩
      rcases ihSub with ⟨Δ₂, h₂, hsub₂⟩
      refine ⟨Δ₁ ∪ Δ₂, ?_, ?_⟩
      · exact subst₂' s t f
          (weakening' (by intro x hx; simp [hx]) h₁)
          (weakening' (by intro x hx; simp [hx]) h₂)
      · intro x hx
        simp at hx
        exact hx.elim (fun hx₁ => hsub₁ hx₁) (fun hx₂ => hsub₂ hx₂)

theorem theory_proof_compactness {L : Language.{u}} {T : Theory L} {ψ : sentence L} (hψ : T ⊢' ψ) :
    ∃ Γ : Finset (sentence L), (finTheory Γ ⊢' ψ) ∧ ((Γ : Set (sentence L)) ⊆ T.carrier) := by
  classical
  haveI : DecidableEq (sentence L) := Classical.decEq _
  rcases proof_compactness (ψ := (ψ : formula L)) (T := Theory.fst T) hψ with ⟨Δ, hΔ, hsub⟩
  let pre : {x // x ∈ (Δ : Set (formula L))} → sentence L :=
    fun x => Classical.choose (hsub x.property)
  let Γ : Finset (sentence L) := by
    classical
    exact Δ.attach.image pre
  have hΓsub : (Γ : Set (sentence L)) ⊆ T.carrier := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨x, hx, rfl⟩
    exact (Classical.choose_spec (hsub x.property)).1
  have hImage : Theory.fst (finTheory Γ) = (Δ : Set (formula L)) := by
    ext x
    constructor
    · rintro ⟨s, hs, hsx⟩
      have hs' : s ∈ Set.range pre := by
        simpa [finTheory, Γ] using hs
      rcases hs' with ⟨y : {x // x ∈ (Δ : Set (formula L))}, rfl⟩
      have hy' : ((pre y : sentence L) : formula L) = y := (Classical.choose_spec (hsub y.property)).2
      have hxEq : x = (y : formula L) := by
        simpa [hy'] using hsx.symm
      simpa [hxEq] using y.property
    · intro hx
      let y : {x // x ∈ (Δ : Set (formula L))} := ⟨x, hx⟩
      refine ⟨pre y, ?_, (Classical.choose_spec (hsub hx)).2⟩
      change pre y ∈ (Γ : Set (sentence L))
      simpa [Γ]
  have hΓ : finTheory Γ ⊢' ψ := by
    change Nonempty (Theory.fst (finTheory Γ) ⊢ (ψ : formula L))
    simpa [sprf, finTheory, hImage] using (hΔ : ((Δ : Set (formula L)) ⊢' (ψ : formula L)))
  exact ⟨Γ, hΓ, hΓsub⟩

theorem theory_proof_compactness_iff {L : Language.{u}} {T : Theory L} {ψ : sentence L} :
    T ⊢' ψ ↔ ∃ Γ : Finset (sentence L), (finTheory Γ ⊢' ψ) ∧ ((Γ : Set (sentence L)) ⊆ T.carrier) := by
  constructor
  · exact theory_proof_compactness
  · rintro ⟨Γ, hΓ, hsub⟩
    rcases hΓ with ⟨hΓ⟩
    exact ⟨sweakening hsub hΓ⟩

theorem is_consistent_union {L : Language.{u}} {T₁ T₂ : Theory L} (h₁ : is_consistent T₁)
    (h₂ : ∀ ψ, ψ ∈ T₂ → insert (∼ψ) T₁ ⊢' (⊥ : sentence L)) : is_consistent (T₁ ∪ T₂) := by
  classical
  have lem : ∀ T₀ : Finset (sentence L), ((T₀ : Set (sentence L)) ⊆ T₂.carrier) → is_consistent (T₁ ∪ finTheory T₀) := by
    intro T₀
    refine Finset.induction_on T₀ ?_ ?_
    · intro _
      have hEq : T₁ ∪ finTheory (∅ : Finset (sentence L)) = T₁ := by
        ext x
        change x ∈ T₁.carrier ∪ (finTheory (∅ : Finset (sentence L))).carrier ↔ x ∈ T₁.carrier
        constructor
        · intro hx
          exact hx.elim id (fun hFalse => by cases hFalse)
        · intro hx
          exact Or.inl hx
      simpa [hEq] using h₁
    · intro ψ s hψ ih hs
      have hsTail : ((s : Set (sentence L)) ⊆ T₂.carrier) := by
        intro x hx
        exact hs (by simp [hx])
      have hsψ : ψ ∈ T₂ := hs (by simp)
      have ih' : is_consistent (T₁ ∪ finTheory s) := ih hsTail
      intro hBad
      have hPosEq : T₁ ∪ finTheory (insert ψ s) = insert ψ (T₁ ∪ finTheory s) := by
        ext x
        change x ∈ T₁.carrier ∪ (finTheory (insert ψ s)).carrier ↔ x ∈ (insert ψ (T₁ ∪ finTheory s)).carrier
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inl hx)
          · have hx' : x = ψ ∨ x ∈ s := by
              have hxs : x ∈ ((insert ψ s : Finset (sentence L)) : Set (sentence L)) := by
                simpa [finTheory] using hx
              simpa using hxs
            rcases hx' with rfl | hx
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hx)
        · intro hx
          change x = ψ ∨ x ∈ (T₁ ∪ finTheory s).carrier at hx
          rcases hx with rfl | hx
          · exact Or.inr (by simp [finTheory])
          · rcases hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (by
                change x ∈ ((insert ψ s : Finset (sentence L)) : Set (sentence L))
                simp [hx])
      have hPos : insert ψ (T₁ ∪ finTheory s) ⊢' (⊥ : sentence L) := by
        simpa [hPosEq] using hBad
      have hNegBase : insert (∼ψ) T₁ ⊢' (⊥ : sentence L) := h₂ ψ hsψ
      have hNeg : insert (∼ψ) (T₁ ∪ finTheory s) ⊢' (⊥ : sentence L) := by
        rcases hNegBase with ⟨hNegBase⟩
        exact ⟨sweakening (by
          intro x hx
          change x ∈ (insert (∼ψ) T₁).carrier at hx
          change x ∈ (insert (∼ψ) (T₁ ∪ finTheory s)).carrier
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hx)) hNegBase⟩
      exact ih' (Flypitch.fol.sprf_by_cases ψ hPos hNeg)
  intro hBad
  rcases theory_proof_compactness hBad with ⟨T₀, h₀, hT⟩
  let T₀' : Finset (sentence L) := T₀.filter fun x => decide (x ∉ T₁)
  have hT₀' : ((T₀' : Set (sentence L)) ⊆ T₂.carrier) := by
    intro x hx
    have hx' : x ∈ T₀ ∧ x ∉ T₁ := by simpa [T₀'] using hx
    exact (hT hx'.1).resolve_left hx'.2
  have hSmall : T₁ ∪ finTheory T₀' ⊢' (⊥ : sentence L) := by
    rcases h₀ with ⟨h₀⟩
    exact ⟨sweakening (by
      intro x hx
      change x ∈ (finTheory T₀).carrier at hx
      have hxT₀ : x ∈ T₀ := hx
      have hxUnion : x ∈ (T₁ ∪ T₂) := hT hx
      by_cases hxT₁ : x ∈ T₁
      · exact Or.inl hxT₁
      · have hxT₀' : x ∈ T₀' := by
          simp [T₀', hxT₀, hxT₁]
        exact Or.inr hxT₀') h₀⟩
  exact (lem T₀' hT₀') hSmall

end fol
end Flypitch
