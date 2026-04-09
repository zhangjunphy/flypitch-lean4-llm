import Flypitch.FOL.Proof
import Mathlib.Data.Set.Image

universe u

namespace Flypitch
namespace fol

/-!
`Flypitch.FOL.Semantics` interprets the syntax and proof system from the preceding files in
first-order structures. It defines term and formula realization, semantic consequence, and
proves the soundness of the natural-deduction rules.
-/

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

variable {L : Language.{u}}

/-- An `L`-structure consists of a carrier type and interpretations of the symbols of `L`. -/
structure Structure (L : Language.{u}) where
  carrier : Type u
  fun_map : {n : Nat} → L.functions n → dvector carrier n → carrier
  rel_map : {n : Nat} → L.relations n → dvector carrier n → Prop

instance : CoeSort (Structure L) (Type u) where
  coe S := S.carrier

/-- Interpret a partially applied term in a structure under a valuation. -/
@[simp] def realize_term {M : Structure L} (v : Nat → M) :
    {l : Nat} → preterm L l → dvector M l → M
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => M.fun_map f xs
  | _, preterm.app t₁ t₂, xs => realize_term v t₁ (realize_term v t₂ [] :: xs)

/-- Realization depends only on the values of the valuation on free variables of the term. -/
theorem realize_term_congr {M : Structure L} {v v' : Nat → M} (h : ∀ n, v n = v' n) :
    {l : Nat} → (t : preterm L l) → (xs : dvector M l) → realize_term v t xs = realize_term v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      have ht₂ : realize_term v t₂ [] = realize_term v' t₂ [] :=
        realize_term_congr (h := h) (t := t₂) (xs := [])
      simpa [realize_term, ht₂] using
        (realize_term_congr (h := h) (t := t₁) (xs := realize_term v t₂ [] :: xs))

/-- Semantic substitution for terms is computed by changing the valuation at the substituted variable. -/
theorem realize_term_subst {M : Structure L} (v : Nat → M) :
    {l : Nat} → (n : Nat) → (t : preterm L l) → (s : term L) → (xs : dvector M l) →
      realize_term (v[realize_term v (s ↑ n) [] // n]) t xs = realize_term v (t[s // n]) xs
  | _, n, preterm.var k, s, [] => by
      by_cases hlt : k < n
      · simp [subst_term, subst_realize, hlt]
      · by_cases hgt : n < k
        · simp [subst_term, subst_realize, hlt, hgt]
        · have hk : k = n := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
          subst hk
          simp [subst_term, subst_realize, lift_term]
  | _, _, preterm.func _, _, _ => rfl
  | _, n, preterm.app t₁ t₂, s, xs => by
      have ht₂ :
          realize_term (v[realize_term v (s ↑ n) [] // n]) t₂ [] =
            realize_term v (subst_term t₂ s n) [] :=
        realize_term_subst (v := v) (n := n) (t := t₂) (s := s) (xs := [])
      simpa [realize_term, subst_term, ht₂] using
        (realize_term_subst (v := v) (n := n) (t := t₁) (s := s)
          (xs := realize_term v (subst_term t₂ s n) [] :: xs))

/-- Lifting a term corresponds semantically to extending the valuation by a fresh element. -/
theorem realize_term_subst_lift {M : Structure L} (v : Nat → M) (x : M) (m : Nat) :
    {l : Nat} → (t : preterm L l) → (xs : dvector M l) →
      realize_term (v[x // m]) (t ↑' 1 # m) xs = realize_term v t xs
  | _, preterm.var k, [] => by
      by_cases h : m ≤ k
      · have hk : m < k + 1 := Nat.lt_succ_of_le h
        simp [lift_term_at, h, subst_realize_gt, hk]
      · have hk : k < m := lt_of_not_ge h
        simp [lift_term_at, h, subst_realize_lt, hk]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      have ht₂ : realize_term (v[x // m]) (t₂ ↑' 1 # m) [] = realize_term v t₂ [] :=
        realize_term_subst_lift (v := v) (x := x) (m := m) (t := t₂) (xs := [])
      simpa [realize_term, lift_term_at, ht₂] using
        (realize_term_subst_lift (v := v) (x := x) (m := m) (t := t₁)
          (xs := realize_term v t₂ [] :: xs))

/-- Interpret a preformula under a valuation and arguments for its unapplied relation slots. -/
@[simp] def realize_formula {M : Structure L} :
    {l : Nat} → (Nat → M) → preformula L l → dvector M l → Prop
  | _, _, .falsum, _ => False
  | _, v, .equal t₁ t₂, xs => realize_term v t₁ xs = realize_term v t₂ xs
  | _, _, .rel R, xs => M.rel_map R xs
  | _, v, .apprel f t, xs => realize_formula v f (realize_term v t [] :: xs)
  | _, v, .imp f₁ f₂, xs => realize_formula v f₁ xs → realize_formula v f₂ xs
  | _, v, .all f, xs => ∀ x : M, realize_formula (v[x // 0]) f xs

/-- Realization of formulas is invariant under pointwise-equal valuations. -/
theorem realize_formula_congr {M : Structure L} :
    {l : Nat} → {v v' : Nat → M} → (h : ∀ n, v n = v' n) → (f : preformula L l) →
      (xs : dvector M l) → realize_formula v f xs ↔ realize_formula v' f xs
  | _, _, _, _, .falsum, _ => Iff.rfl
  | _, v, v', h, .equal t₁ t₂, xs => by
      rw [show realize_formula v (t₁ ≃ t₂) xs =
          (realize_term v t₁ xs = realize_term v t₂ xs) by rfl]
      rw [show realize_formula v' (t₁ ≃ t₂) xs =
          (realize_term v' t₁ xs = realize_term v' t₂ xs) by rfl]
      rw [realize_term_congr (h := h) (t := t₁) (xs := xs),
        realize_term_congr (h := h) (t := t₂) (xs := xs)]
  | _, v, v', h, .apprel f t, xs => by
      have ht : realize_term v t [] = realize_term v' t [] :=
        realize_term_congr (h := h) (t := t) (xs := [])
      simpa [realize_formula, ht] using
        (realize_formula_congr (v := v) (v' := v') (h := h) (f := f)
          (xs := realize_term v t [] :: xs))
  | _, _, _, _, .rel _, _ => Iff.rfl
  | _, _, _, h, .imp f₁ f₂, xs => by
      constructor <;> intro hf h₁
      · exact (realize_formula_congr (h := h) (f := f₂) (xs := xs)).mp
          (hf ((realize_formula_congr (h := h) (f := f₁) (xs := xs)).mpr h₁))
      · exact (realize_formula_congr (h := h) (f := f₂) (xs := xs)).mpr
          (hf ((realize_formula_congr (h := h) (f := f₁) (xs := xs)).mp h₁))
  | _, _, _, h, .all f, xs => by
      constructor
      · intro hf x
        exact (realize_formula_congr
          (h := fun n => subst_realize_congr h x 0 n)
          (f := f) (xs := xs)).mp (hf x)
      · intro hf x
        exact (realize_formula_congr
          (h := fun n => subst_realize_congr h x 0 n)
          (f := f) (xs := xs)).mpr (hf x)

/-- Formula substitution is semantically the same as updating the valuation at the substituted variable. -/
theorem realize_formula_subst {M : Structure L} :
    {l : Nat} → (v : Nat → M) → (n : Nat) → (f : preformula L l) → (s : term L) →
      (xs : dvector M l) →
      realize_formula (v[realize_term v (s ↑ n) [] // n]) f xs ↔
        realize_formula v (subst_formula f s n) xs
  | _, _, _, .falsum, _, _ => Iff.rfl
  | _, v, n, .equal t₁ t₂, s, xs => by
      simp [realize_formula, realize_term_subst]
  | _, _, _, .rel _, _, _ => Iff.rfl
  | _, v, n, .apprel f t, s, xs => by
      have ht :
          realize_term (v[realize_term v (s ↑ n) [] // n]) t [] =
            realize_term v (subst_term t s n) [] :=
        realize_term_subst (v := v) (n := n) (t := t) (s := s) (xs := [])
      simpa [realize_formula, subst_formula, ht] using
        (realize_formula_subst (v := v) (n := n) (f := f) (s := s)
          (xs := realize_term v (subst_term t s n) [] :: xs))
  | _, v, n, .imp f₁ f₂, s, xs => by
      constructor
      · intro hf h₁
        exact (realize_formula_subst (v := v) (n := n) (f := f₂) (s := s) (xs := xs)).mp
          (hf ((realize_formula_subst (v := v) (n := n) (f := f₁) (s := s) (xs := xs)).mpr h₁))
      · intro hf h₁
        exact (realize_formula_subst (v := v) (n := n) (f := f₂) (s := s) (xs := xs)).mpr
          (hf ((realize_formula_subst (v := v) (n := n) (f := f₁) (s := s) (xs := xs)).mp h₁))
  | _, v, n, .all f, s, xs => by
      constructor
      · intro hf x
        have hx :
            realize_formula (v[realize_term v (s ↑ n) [] // n][x // 0]) f xs := hf x
        have h₁ :
            realize_term (v[x // 0]) ((s ↑ n) ↑ 1) [] = realize_term v (s ↑ n) [] := by
          simpa [lift_term] using
            (realize_term_subst_lift (v := v) (x := x) (m := 0) (t := s ↑ n) (xs := []))
        have hrt :
            realize_term v (s ↑ n) [] = realize_term (v[x // 0]) (s ↑ (n + 1)) [] := by
          simpa [lift_term_succ] using h₁.symm
        have hval :
            ∀ k,
              (v[realize_term v (s ↑ n) [] // n][x // 0]) k =
                (v[x // 0][realize_term (v[x // 0]) (s ↑ (n + 1)) [] // (n + 1)]) k := by
          intro k
          simpa [hrt] using
            (subst_realize2_0 (v := v) (x := x) (x' := realize_term v (s ↑ n) []) (n := n) (k := k))
        have hx' :
            realize_formula (v[x // 0][realize_term (v[x // 0]) (s ↑ (n + 1)) [] // (n + 1)]) f xs := by
          exact (realize_formula_congr (h := hval) (f := f) (xs := xs)).mp hx
        exact (realize_formula_subst (v := v[x // 0]) (n := n + 1) (f := f) (s := s) (xs := xs)).mp hx'
      · intro hf x
        have hx :
            realize_formula (v[x // 0]) (subst_formula f s (n + 1)) xs := hf x
        have hx' :
            realize_formula (v[x // 0][realize_term (v[x // 0]) (s ↑ (n + 1)) [] // (n + 1)]) f xs := by
          exact (realize_formula_subst (v := v[x // 0]) (n := n + 1) (f := f) (s := s) (xs := xs)).mpr hx
        have h₁ :
            realize_term (v[x // 0]) ((s ↑ n) ↑ 1) [] = realize_term v (s ↑ n) [] := by
          simpa [lift_term] using
            (realize_term_subst_lift (v := v) (x := x) (m := 0) (t := s ↑ n) (xs := []))
        have hrt :
            realize_term v (s ↑ n) [] = realize_term (v[x // 0]) (s ↑ (n + 1)) [] := by
          simpa [lift_term_succ] using h₁.symm
        have hval :
            ∀ k,
              (v[realize_term v (s ↑ n) [] // n][x // 0]) k =
                (v[x // 0][realize_term (v[x // 0]) (s ↑ (n + 1)) [] // (n + 1)]) k := by
          intro k
          simpa [hrt] using
            (subst_realize2_0 (v := v) (x := x) (x' := realize_term v (s ↑ n) []) (n := n) (k := k))
        exact (realize_formula_congr (h := hval) (f := f) (xs := xs)).mpr hx'

/-- Specialization of `realize_formula_subst` to substitution at variable `0`. -/
theorem realize_formula_subst0 {M : Structure L} {l : Nat} (v : Nat → M) (f : preformula L l)
    (s : term L) (xs : dvector M l) :
    realize_formula (v[realize_term v s [] // 0]) f xs ↔ realize_formula v (subst_formula f s 0) xs := by
  simpa using realize_formula_subst (v := v) (n := 0) (f := f) (s := s) (xs := xs)

/-- Lifting a formula is semantically neutral when the valuation is extended at the lifted index. -/
theorem realize_formula_subst_lift {M : Structure L} :
    {l : Nat} → (v : Nat → M) → (x : M) → (m : Nat) → (f : preformula L l) →
      (xs : dvector M l) →
      realize_formula (v[x // m]) (lift_formula_at f 1 m) xs = realize_formula v f xs
  | _, _, _, _, .falsum, _ => rfl
  | _, v, x, m, .equal t₁ t₂, xs => by
      simp [realize_formula, lift_formula_at, realize_term_subst_lift]
  | _, _, _, _, .rel _, _ => rfl
  | _, v, x, m, .apprel f t, xs => by
      have ht : realize_term (v[x // m]) (lift_term_at t 1 m) [] = realize_term v t [] :=
        realize_term_subst_lift (v := v) (x := x) (m := m) (t := t) (xs := [])
      simpa [realize_formula, lift_formula_at, ht] using
        (realize_formula_subst_lift (v := v) (x := x) (m := m) (f := f)
          (xs := realize_term v t [] :: xs))
  | _, v, x, m, .imp f₁ f₂, xs => by
      simp [realize_formula, lift_formula_at, realize_formula_subst_lift]
  | _, v, x, m, .all f, xs => by
      apply propext
      constructor
      · intro hf x'
        have hval : ∀ k, (v[x // m][x' // 0]) k = (v[x' // 0][x // (m + 1)]) k := by
          intro k
          simpa [Nat.add_comm] using
            (subst_realize2_0 (v := v) (x := x') (x' := x) (n := m) (k := k))
        have hx :
            realize_formula (v[x' // 0][x // (m + 1)]) (lift_formula_at f 1 (m + 1)) xs := by
          exact (realize_formula_congr (h := hval) (f := lift_formula_at f 1 (m + 1)) (xs := xs)).mp (hf x')
        exact (realize_formula_subst_lift (v := v[x' // 0]) (x := x) (m := m + 1) (f := f) (xs := xs)).mp hx
      · intro hf x'
        have hx :
            realize_formula (v[x' // 0][x // (m + 1)]) (lift_formula_at f 1 (m + 1)) xs := by
          exact (realize_formula_subst_lift (v := v[x' // 0]) (x := x) (m := m + 1) (f := f) (xs := xs)).mpr (hf x')
        have hval : ∀ k, (v[x // m][x' // 0]) k = (v[x' // 0][x // (m + 1)]) k := by
          intro k
          simpa [Nat.add_comm] using
            (subst_realize2_0 (v := v) (x := x') (x' := x) (n := m) (k := k))
        exact (realize_formula_congr (h := hval) (f := lift_formula_at f 1 (m + 1)) (xs := xs)).mpr hx

/-- A closed formula is satisfied in `M` when every valuation realizes it. -/
def satisfied_in (M : Structure L) (f : formula L) : Prop :=
  ∀ v : Nat → M.carrier, realize_formula v f []

/-- Every formula in `T` is satisfied in `M`. -/
def all_satisfied_in (M : Structure L) (T : Set (formula L)) : Prop :=
  ∀ ⦃f : formula L⦄, f ∈ T → satisfied_in M f

/-- Semantic consequence of a single formula from a set of assumptions. -/
def satisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (M : Structure L) (v : Nat → M.carrier),
    (∀ g : formula L, g ∈ T → realize_formula v g []) →
    realize_formula v f []

/-- Semantic consequence of every formula in `T'` from `T`. -/
def all_satisfied (T T' : Set (formula L)) : Prop :=
  ∀ ⦃f : formula L⦄, f ∈ T' → satisfied T f

infix:51 " ⊨ " => satisfied

/-- Semantic consequence can be composed with satisfaction in a specific structure. -/
theorem satisfied_in_trans {M : Structure L} {T : Set (formula L)} {f : formula L}
    (hMT : all_satisfied_in M T) (hTf : satisfied T f) : satisfied_in M f :=
  fun v => hTf M v (fun g hg => hMT hg v)

/-- Satisfaction of a theory in a structure is closed under semantic consequence. -/
theorem all_satisfied_in_trans {M : Structure L} {T T' : Set (formula L)}
    (hMT : all_satisfied_in M T) (hTT' : all_satisfied T T') : all_satisfied_in M T' :=
  by
    intro f hf
    exact satisfied_in_trans hMT (hTT' hf)

/-- Any member of a theory is a semantic consequence of that theory. -/
theorem satisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) : satisfied T f :=
  fun _ _ hT => hT f hf

/-- Semantic consequence is monotone in the conclusion set. -/
theorem all_satisfied_of_subset {T T' : Set (formula L)} (h : T' ⊆ T) : all_satisfied T T' :=
  by
    intro f hf
    exact satisfied_of_mem (h hf)

/-- Semantic consequence composes transitively. -/
theorem satisfied_trans {T₁ T₂ : Set (formula L)} {f : formula L}
    (h₁₂ : all_satisfied T₁ T₂) (h₂f : satisfied T₂ f) : satisfied T₁ f :=
  fun M v hT₁ => h₂f M v (fun g hg => h₁₂ hg M v hT₁)

/-- Pointwise semantic consequence composes transitively. -/
theorem all_satisfied_trans {T₁ T₂ T₃ : Set (formula L)}
    (h₁₂ : all_satisfied T₁ T₂) (h₂₃ : all_satisfied T₂ T₃) : all_satisfied T₁ T₃ :=
  by
    intro f hf
    exact satisfied_trans h₁₂ (h₂₃ hf)

/-- Weakening assumptions preserves semantic consequence. -/
theorem satisfied_weakening {T T' : Set (formula L)} (h : T ⊆ T') {f : formula L}
    (hTf : satisfied T f) : satisfied T' f :=
  fun M v hT' => hTf M v (fun g hg => hT' g (h hg))

/-- Every derivable formula is semantically valid from the same assumptions. -/
theorem formula_soundness {Γ : Set (formula L)} {A : formula L} (h : Γ ⊢ A) : Γ ⊨ A := by
  intro M
  induction h with
  | axm hmem =>
      intro v hΓ
      exact hΓ _ hmem
  | impI h ih =>
      intro v hΓ hA
      exact ih v (by
        intro f hf
        simp only [Set.mem_insert_iff] at hf
        rcases hf with rfl | hf
        · exact hA
        · exact hΓ _ hf)
  | impE B hImp hA ihImp ihA =>
      intro v hΓ
      exact (ihImp v hΓ) (ihA v hΓ)
  | falsumE h ih =>
      classical
      intro v hΓ
      by_contra hA
      have hbot : realize_formula v (⊥ : formula L) [] := ih v (by
        intro f hf
        simp only [Set.mem_insert_iff] at hf
        rcases hf with rfl | hf
        · exact hA
        · exact hΓ _ hf)
      simpa [realize_formula] using hbot
  | allI h ih =>
      intro v hΓ x
      apply ih (v := v[x // 0])
      intro f hf
      rcases hf with ⟨g, hg, rfl⟩
      have hLift : realize_formula (v[x // 0]) (lift_formula1 g) [] = realize_formula v g [] := by
        simpa [lift_formula1, lift_formula] using
          (realize_formula_subst_lift (v := v) (x := x) (m := 0) (f := g) (xs := []))
      simpa [hLift] using hΓ g hg
  | allE₂ A t h ih =>
      intro v hΓ
      exact (realize_formula_subst0 (v := v) (f := A) (s := t) (xs := [])).mp
        (ih v hΓ (realize_term v t []))
  | ref _ t =>
      intro v _
      simp [realize_formula]
  | subst₂ s t f hEq hSub ihEq ihSub =>
      intro v hΓ
      have hEqv : realize_formula v (s ≃ t) [] := ihEq v hΓ
      have hSubv : realize_formula v (subst_formula f s 0) [] := ihSub v hΓ
      have hs : realize_formula (v[realize_term v s [] // 0]) f [] := by
        exact (realize_formula_subst0 (v := v) (f := f) (s := s) (xs := [])).mpr hSubv
      have hst : realize_term v s [] = realize_term v t [] := by
        simpa [realize_formula] using hEqv
      have ht : realize_formula (v[realize_term v t [] // 0]) f [] := by
        simpa [hst] using hs
      exact (realize_formula_subst0 (v := v) (f := f) (s := t) (xs := [])).mp ht

end fol
end Flypitch
