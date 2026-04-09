import Flypitch.FOL.Bounded

universe u

namespace Flypitch
namespace fol

open Set

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

namespace Language

def Lconstants (α : Type u) : Language :=
  ⟨fun n => match n with | 0 => α | _ + 1 => PEmpty, fun _ => PEmpty⟩

protected def sum (L L' : Language) : Language :=
  ⟨fun n => L.functions n ⊕ L'.functions n, fun n => L.relations n ⊕ L'.relations n⟩

def symbols (L : Language) := (Σ l, L.functions l) ⊕ (Σ l, L.relations l)

end Language

section Symbols

variable {L : Language.{u}}

@[simp] def symbols_in_term : {l : Nat} → preterm L l → Set L.symbols
  | _, .var _ => ∅
  | l, .func f => {Sum.inl ⟨l, f⟩}
  | _, .app t₁ t₂ => symbols_in_term t₁ ∪ symbols_in_term t₂

@[simp] def symbols_in_formula : {l : Nat} → preformula L l → Set L.symbols
  | _, .falsum => ∅
  | _, .equal t₁ t₂ => symbols_in_term t₁ ∪ symbols_in_term t₂
  | l, .rel R => {Sum.inr ⟨l, R⟩}
  | _, .apprel f t => symbols_in_formula f ∪ symbols_in_term t
  | _, .imp f₁ f₂ => symbols_in_formula f₁ ∪ symbols_in_formula f₂
  | _, .all f => symbols_in_formula f

@[simp] theorem symbols_in_term_lift_at (n m : Nat) : {l : Nat} → (t : preterm L l) →
    symbols_in_term (lift_term_at t n m) = symbols_in_term t
  | _, .var k => by
      by_cases h : m ≤ k <;> simp [lift_term_at, h]
  | _, .func _ => rfl
  | _, .app t₁ t₂ => by
      simp [lift_term_at, symbols_in_term_lift_at n m]

@[simp] theorem symbols_in_term_lift (n : Nat) {l : Nat} (t : preterm L l) :
    symbols_in_term (lift_term t n) = symbols_in_term t := by
  simpa [lift_term] using symbols_in_term_lift_at (L := L) n 0 t

theorem symbols_in_term_subst (s : term L) (n : Nat) : {l : Nat} → (t : preterm L l) →
    symbols_in_term (subst_term t s n) ⊆ symbols_in_term t ∪ symbols_in_term s
  | _, .var k => by
      by_cases hkn : k < n
      · simpa [subst_term, subst_realize, hkn] using fun x hx => (Or.inl hx : x ∈ ({x | False} ∪ symbols_in_term s))
      · by_cases hnk : n < k
        · simpa [subst_term, subst_realize, hkn, hnk] using
            fun x hx => (Or.inl hx : x ∈ ({x | False} ∪ symbols_in_term s))
        · simpa [subst_term, subst_realize, hkn, hnk] using
            fun x hx => (Or.inr hx : x ∈ (∅ ∪ symbols_in_term s))
  | _, .func _ => by
      intro x hx
      exact Or.inl hx
  | _, .app t₁ t₂ => by
      intro x hx
      rcases hx with hx | hx
      · rcases symbols_in_term_subst (l := _) s n t₁ hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
      · rcases symbols_in_term_subst (l := _) s n t₂ hx with hx | hx
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx

theorem symbols_in_formula_subst : {l : Nat} → (f : preformula L l) → (s : term L) → (n : Nat) →
    symbols_in_formula (subst_formula f s n) ⊆ symbols_in_formula f ∪ symbols_in_term s
  | _, .falsum, _, _ => by intro x hx; cases hx
  | _, .equal t₁ t₂, s, n => by
      intro x hx
      rcases hx with hx | hx
      · rcases symbols_in_term_subst (l := 0) s n t₁ hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
      · rcases symbols_in_term_subst (l := 0) s n t₂ hx with hx | hx
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
  | _, .rel _, _, _ => by
      intro x hx
      exact Or.inl hx
  | _, .apprel f t, s, n => by
      intro x hx
      rcases hx with hx | hx
      · rcases symbols_in_formula_subst (l := _) f s n hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
      · rcases symbols_in_term_subst (l := 0) s n t hx with hx | hx
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
  | _, .imp f₁ f₂, s, n => by
      intro x hx
      rcases hx with hx | hx
      · rcases symbols_in_formula_subst (l := 0) f₁ s n hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
      · rcases symbols_in_formula_subst (l := 0) f₂ s n hx with hx | hx
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
  | _, .all f, s, n => by
      simpa using symbols_in_formula_subst (l := 0) f s (n + 1)

end Symbols

structure Lhom (L L' : Language.{u}) where
  on_function : {n : Nat} → L.functions n → L'.functions n
  on_relation : {n : Nat} → L.relations n → L'.relations n

infix:10 " →ᴸ " => Lhom

namespace Lhom

variable {L : Language.{u}} {L' : Language.{u}} {L₁ : Language.{u}} {L₂ : Language.{u}}
  {L₃ : Language.{u}}

protected def id (L : Language.{u}) : L →ᴸ L :=
  ⟨fun {n} x => x, fun {n} x => x⟩

protected def sum_inl {L L' : Language.{u}} : L →ᴸ L.sum L' :=
  ⟨fun {n} f => Sum.inl f, fun {n} R => Sum.inl R⟩

protected def sum_inr {L L' : Language.{u}} : L' →ᴸ L.sum L' :=
  ⟨fun {n} f => Sum.inr f, fun {n} R => Sum.inr R⟩

  @[reducible] def comp (g : L₂ →ᴸ L₃) (f : L₁ →ᴸ L₂) : L₁ →ᴸ L₃ :=
  ⟨fun {n} x => g.on_function (f.on_function x), fun {n} x => g.on_relation (f.on_relation x)⟩

  local infixr:80 " ∘ᴸ " => Lhom.comp

  theorem Lhom_funext {F G : L₁ →ᴸ L₂}
      (h_fun : ∀ n x, @Lhom.on_function _ _ F n x = @Lhom.on_function _ _ G n x)
      (h_rel : ∀ n x, @Lhom.on_relation _ _ F n x = @Lhom.on_relation _ _ G n x) : F = G := by
    cases F with
    | mk onfF onrF =>
        cases G with
        | mk onfG onrG =>
            have hF := funext (fun n => funext (fun x => h_fun n x))
            have hR := funext (fun n => funext (fun x => h_rel n x))
            cases hF
            cases hR
            rfl

  @[ext] theorem ext {F G : L₁ →ᴸ L₂}
      (h_fun : ∀ n x, @Lhom.on_function _ _ F n x = @Lhom.on_function _ _ G n x)
      (h_rel : ∀ n x, @Lhom.on_relation _ _ F n x = @Lhom.on_relation _ _ G n x) : F = G := by
    exact Lhom_funext h_fun h_rel

  @[simp] theorem id_is_left_identity {F : L₁ →ᴸ L₂} : (Lhom.id L₂) ∘ᴸ F = F := by
    cases F
    rfl

  @[simp] theorem id_is_right_identity {F : L₁ →ᴸ L₂} : F ∘ᴸ (Lhom.id L₁) = F := by
    cases F
    rfl

  @[simp] theorem comp_assoc {L₀ : Language.{u}} (g : L₂ →ᴸ L₃) (f : L₁ →ᴸ L₂) (e : L₀ →ᴸ L₁) :
      (g ∘ᴸ f) ∘ᴸ e = g ∘ᴸ (f ∘ᴸ e) := by
    rfl

  @[simp] theorem comp_on_function (g : L₂ →ᴸ L₃) (f : L₁ →ᴸ L₂) {n : Nat}
      (x : L₁.functions n) :
      (g ∘ᴸ f).on_function x = g.on_function (f.on_function x) :=
    rfl

  @[simp] theorem comp_on_relation (g : L₂ →ᴸ L₃) (f : L₁ →ᴸ L₂) {n : Nat}
      (x : L₁.relations n) :
      (g ∘ᴸ f).on_relation x = g.on_relation (f.on_relation x) :=
    rfl

structure is_injective (ϕ : L →ᴸ L') : Prop where
  on_function : {n : Nat} → Function.Injective (@Lhom.on_function _ _ ϕ n)
  on_relation : {n : Nat} → Function.Injective (@Lhom.on_relation _ _ ϕ n)

class has_decidable_range (ϕ : L →ᴸ L') : Type u where
  on_function : {n : Nat} → DecidablePred (Set.range (@Lhom.on_function _ _ ϕ n))
  on_relation : {n : Nat} → DecidablePred (Set.range (@Lhom.on_relation _ _ ϕ n))

attribute [reducible, instance] has_decidable_range.on_function has_decidable_range.on_relation

@[simp] def on_symbol (ϕ : L →ᴸ L') : L.symbols → L'.symbols
  | Sum.inl ⟨l, f⟩ => Sum.inl ⟨l, ϕ.on_function f⟩
  | Sum.inr ⟨l, R⟩ => Sum.inr ⟨l, ϕ.on_relation R⟩

@[simp] def on_term (ϕ : L →ᴸ L') : {l : Nat} → preterm L l → preterm L' l
  | _, .var k => &k
  | _, .func f => preterm.func (ϕ.on_function f)
  | _, .app t₁ t₂ => preterm.app (on_term ϕ t₁) (on_term ϕ t₂)

@[simp] theorem on_term_lift_at (ϕ : L →ᴸ L') : {l : Nat} → (t : preterm L l) → (n m : Nat) →
    on_term ϕ (lift_term_at t n m) = lift_term_at (on_term ϕ t) n m
  | _, .var k, n, m => by
      by_cases h : m ≤ k <;> simp [lift_term_at, h]
  | _, .func _, _, _ => rfl
  | _, .app t₁ t₂, n, m => by
      simp [lift_term_at, on_term_lift_at]

@[simp] theorem on_term_lift (ϕ : L →ᴸ L') {l : Nat} (n : Nat) (t : preterm L l) :
    on_term ϕ (lift_term t n) = lift_term (on_term ϕ t) n := by
  simpa [lift_term] using on_term_lift_at (ϕ := ϕ) t n 0

@[simp] theorem on_term_subst (ϕ : L →ᴸ L') : {l : Nat} → (t : preterm L l) → (s : term L) → (n : Nat) →
    on_term ϕ (subst_term t s n) = subst_term (on_term ϕ t) (on_term ϕ s) n
  | _, .var k, s, n => by
      by_cases hkn : k < n
      · simp [subst_term, subst_realize, hkn]
      · by_cases hnk : n < k
        · simp [subst_term, subst_realize, hkn, hnk]
        · have hk : k = n := Nat.le_antisymm (Nat.le_of_not_gt hnk) (Nat.le_of_not_gt hkn)
          subst hk
          simpa [subst_term, subst_realize] using on_term_lift_at (ϕ := ϕ) s n 0
  | _, .func _, _, _ => rfl
  | _, .app t₁ t₂, s, n => by
      simp [subst_term, on_term_subst]

  @[simp] theorem on_term_apps (ϕ : L →ᴸ L') : {l : Nat} → (t : preterm L l) → (ts : dvector (term L) l) →
    on_term ϕ (apps t ts) = apps (on_term ϕ t) (ts.map (on_term ϕ))
  | _, t, [] => rfl
  | _, t, x :: xs => by
      simp [apps, on_term_apps]

  @[simp] theorem on_term_comp (ψ : L' →ᴸ L₂) (ϕ : L →ᴸ L') : {l : Nat} → (t : preterm L l) →
      on_term (ψ ∘ᴸ ϕ) t = on_term ψ (on_term ϕ t)
    | _, .var _ => rfl
    | _, .func _ => rfl
    | _, .app t₁ t₂ => by
        simp [on_term_comp]

  @[simp] theorem on_term_id : {l : Nat} → (t : preterm L l) →
      on_term (Lhom.id L) t = t
    | _, .var _ => rfl
    | _, .func _ => rfl
    | _, .app t₁ t₂ => by
        simp [on_term_id]

theorem not_mem_symbols_in_term_on_term (ϕ : L →ᴸ L') {s : L'.symbols}
    (h : s ∉ Set.range (on_symbol ϕ)) : {l : Nat} → (t : preterm L l) →
    s ∉ symbols_in_term (on_term ϕ t)
  | _, .var _ => by
      intro hs
      cases hs
  | l, .func f => by
      intro hs
      have hs' : s = Sum.inl ⟨l, ϕ.on_function f⟩ := eq_of_mem_singleton hs
      apply h
      subst hs'
      exact ⟨Sum.inl ⟨l, f⟩, rfl⟩
  | _, .app t₁ t₂ => by
      intro hs
      rcases hs with hs | hs
      · exact not_mem_symbols_in_term_on_term (ϕ := ϕ) h t₁ hs
      · exact not_mem_symbols_in_term_on_term (ϕ := ϕ) h t₂ hs

@[simp] def on_formula (ϕ : L →ᴸ L') : {l : Nat} → preformula L l → preformula L' l
  | _, .falsum => ⊥
  | _, .equal t₁ t₂ => on_term ϕ t₁ ≃ on_term ϕ t₂
  | _, .rel R => preformula.rel (ϕ.on_relation R)
  | _, .apprel f t => preformula.apprel (on_formula ϕ f) (on_term ϕ t)
  | _, .imp f₁ f₂ => on_formula ϕ f₁ ⟹ on_formula ϕ f₂
  | _, .all f => ∀' on_formula ϕ f

@[simp] theorem on_formula_lift_at (ϕ : L →ᴸ L') : {l : Nat} → (n m : Nat) → (f : preformula L l) →
    on_formula ϕ (lift_formula_at f n m) = lift_formula_at (on_formula ϕ f) n m
  | _, _, _, .falsum => rfl
  | _, _, _, .equal t₁ t₂ => by
      simp [lift_formula_at, on_term_lift_at]
  | _, _, _, .rel _ => rfl
  | _, _, _, .apprel f t => by
      simp [lift_formula_at, on_formula_lift_at, on_term_lift_at]
  | _, _, _, .imp f₁ f₂ => by
      simp [lift_formula_at, on_formula_lift_at]
  | _, _, _, .all f => by
      simp [lift_formula_at, on_formula_lift_at]

@[simp] theorem on_formula_lift (ϕ : L →ᴸ L') {l : Nat} (n : Nat) (f : preformula L l) :
    on_formula ϕ (lift_formula f n) = lift_formula (on_formula ϕ f) n := by
  simpa [lift_formula] using on_formula_lift_at (ϕ := ϕ) n 0 f

@[simp] theorem on_formula_subst (ϕ : L →ᴸ L') : {l : Nat} → (f : preformula L l) → (s : term L) → (n : Nat) →
    on_formula ϕ (subst_formula f s n) = subst_formula (on_formula ϕ f) (on_term ϕ s) n
  | _, .falsum, _, _ => rfl
  | _, .equal t₁ t₂, s, n => by
      simp [subst_formula, on_term_subst]
  | _, .rel _, _, _ => rfl
  | _, .apprel f t, s, n => by
      simp [subst_formula, on_formula_subst, on_term_subst]
  | _, .imp f₁ f₂, s, n => by
      simp [subst_formula, on_formula_subst]
  | _, .all f, s, n => by
      simp [subst_formula, on_formula_subst]

  @[simp] theorem on_formula_apps_rel (ϕ : L →ᴸ L') : {l : Nat} → (f : preformula L l) → (ts : dvector (term L) l) →
    on_formula ϕ (apps_rel f ts) = apps_rel (on_formula ϕ f) (ts.map (on_term ϕ))
  | _, f, [] => rfl
  | _, f, x :: xs => by
      simp [apps_rel, on_formula_apps_rel]

  @[simp] theorem on_formula_comp (ψ : L' →ᴸ L₂) (ϕ : L →ᴸ L') : {l : Nat} → (f : preformula L l) →
      on_formula (ψ ∘ᴸ ϕ) f = on_formula ψ (on_formula ϕ f)
    | _, .falsum => rfl
    | _, .equal _ _ => by
        simp [on_formula, on_term_comp]
    | _, .rel _ => rfl
    | _, .apprel f t => by
        simp [on_formula_comp]
    | _, .imp f₁ f₂ => by
        simp [on_formula_comp]
    | _, .all f => by
        simp [on_formula_comp]

  @[simp] theorem on_formula_id : {l : Nat} → (f : preformula L l) →
      on_formula (Lhom.id L) f = f
    | _, .falsum => rfl
    | _, .equal _ _ => by simp
    | _, .rel _ => rfl
    | _, .apprel f t => by
        simp [on_formula_id]
    | _, .imp f₁ f₂ => by
        simp [on_formula_id]
    | _, .all f => by
        simp [on_formula_id]

theorem not_mem_symbols_in_formula_on_formula (ϕ : L →ᴸ L') {s : L'.symbols}
    (h : s ∉ Set.range (on_symbol ϕ)) : {l : Nat} → (f : preformula L l) →
    s ∉ symbols_in_formula (on_formula ϕ f)
  | _, .falsum => by
      intro hs
      cases hs
  | _, .equal t₁ t₂ => by
      intro hs
      rcases hs with hs | hs
      · exact not_mem_symbols_in_term_on_term (ϕ := ϕ) h t₁ hs
      · exact not_mem_symbols_in_term_on_term (ϕ := ϕ) h t₂ hs
  | l, .rel R => by
      intro hs
      have hs' : s = Sum.inr ⟨l, ϕ.on_relation R⟩ := eq_of_mem_singleton hs
      apply h
      subst hs'
      exact ⟨Sum.inr ⟨l, R⟩, rfl⟩
  | _, .apprel f t => by
      intro hs
      rcases hs with hs | hs
      · exact not_mem_symbols_in_formula_on_formula (ϕ := ϕ) h f hs
      · exact not_mem_symbols_in_term_on_term (ϕ := ϕ) h t hs
  | _, .imp f₁ f₂ => by
      intro hs
      rcases hs with hs | hs
      · exact not_mem_symbols_in_formula_on_formula (ϕ := ϕ) h f₁ hs
      · exact not_mem_symbols_in_formula_on_formula (ϕ := ϕ) h f₂ hs
  | _, .all f => by
      intro hs
      exact not_mem_symbols_in_formula_on_formula (ϕ := ϕ) h f hs

theorem not_mem_function_in_formula_on_formula (ϕ : L →ᴸ L') {l' : Nat} {f' : L'.functions l'}
    (h : f' ∉ Set.range (@Lhom.on_function _ _ ϕ l')) {l : Nat} (f : preformula L l) :
    (Sum.inl ⟨l', f'⟩ : L'.symbols) ∉ symbols_in_formula (on_formula ϕ f) := by
  apply not_mem_symbols_in_formula_on_formula (ϕ := ϕ)
  intro hs
  apply h
  rcases hs with ⟨a, ha⟩
  cases a with
  | inl af =>
      cases af with
      | mk n g =>
          dsimp [on_symbol] at ha
          cases ha
          exact ⟨g, rfl⟩
  | inr ar =>
      cases ar with
      | mk n R =>
          dsimp [on_symbol] at ha
          cases ha

theorem bounded_term_at_on_term (ϕ : L →ᴸ L') : {l : Nat} → {t : preterm L l} → {n : Nat} →
    bounded_term_at t n → bounded_term_at (on_term ϕ t) n
  | _, .var _, _, h => h
  | _, .func _, _, _ => trivial
  | _, .app t₁ t₂, _, h => ⟨bounded_term_at_on_term (ϕ := ϕ) h.1, bounded_term_at_on_term (ϕ := ϕ) h.2⟩

theorem bounded_formula_at_on_formula (ϕ : L →ᴸ L') : {l : Nat} → {f : preformula L l} → {n : Nat} →
    bounded_formula_at f n → bounded_formula_at (on_formula ϕ f) n
  | _, f, n, h => by
      induction f generalizing n with
      | falsum =>
          trivial
      | equal t₁ t₂ =>
          exact ⟨bounded_term_at_on_term (ϕ := ϕ) h.1, bounded_term_at_on_term (ϕ := ϕ) h.2⟩
      | rel R =>
          trivial
      | apprel f t ih =>
          exact ⟨ih (n := n) h.1, bounded_term_at_on_term (ϕ := ϕ) h.2⟩
      | imp f₁ f₂ ih₁ ih₂ =>
          exact ⟨ih₁ (n := n) h.1, ih₂ (n := n) h.2⟩
      | all f ih =>
          simpa [on_formula] using (ih (n := n + 1) h)

@[simp] def on_bounded_term (ϕ : L →ᴸ L') {n l : Nat} (t : bounded_preterm L n l) : bounded_preterm L' n l :=
  ⟨on_term ϕ t.1, bounded_term_at_on_term (ϕ := ϕ) t.2⟩

  @[simp] theorem on_bounded_term_fst (ϕ : L →ᴸ L') {n l : Nat} (t : bounded_preterm L n l) :
    (on_bounded_term ϕ t).fst = on_term ϕ t.fst :=
  rfl

  @[simp] theorem on_bounded_term_comp (ψ : L' →ᴸ L₂) (ϕ : L →ᴸ L') {n l : Nat}
      (t : bounded_preterm L n l) :
      on_bounded_term (ψ ∘ᴸ ϕ) t = on_bounded_term ψ (on_bounded_term ϕ t) := by
    apply Subtype.ext
    simp

  @[simp] theorem on_bounded_term_id {n l : Nat} (t : bounded_preterm L n l) :
      on_bounded_term (Lhom.id L) t = t := by
    apply Subtype.ext
    simp

  @[simp] def on_bounded_formula (ϕ : L →ᴸ L') {n l : Nat} (f : bounded_preformula L n l) :
    bounded_preformula L' n l :=
  ⟨on_formula ϕ f.1, bounded_formula_at_on_formula (ϕ := ϕ) f.2⟩

  @[simp] theorem on_bounded_formula_fst (ϕ : L →ᴸ L') {n l : Nat} (f : bounded_preformula L n l) :
    (on_bounded_formula ϕ f).fst = on_formula ϕ f.fst :=
  rfl

  @[simp] theorem on_bounded_formula_comp (ψ : L' →ᴸ L₂) (ϕ : L →ᴸ L') {n l : Nat}
      (f : bounded_preformula L n l) :
      on_bounded_formula (ψ ∘ᴸ ϕ) f = on_bounded_formula ψ (on_bounded_formula ϕ f) := by
    apply Subtype.ext
    simp

  @[simp] theorem on_bounded_formula_id {n l : Nat} (f : bounded_preformula L n l) :
      on_bounded_formula (Lhom.id L) f = f := by
    apply Subtype.ext
    simp

@[simp] def on_closed_term (ϕ : L →ᴸ L') (t : closed_term L) : closed_term L' :=
  on_bounded_term ϕ t

@[simp] def on_sentence (ϕ : L →ᴸ L') (f : sentence L) : sentence L' :=
  ⟨on_formula ϕ f.1, bounded_formula_at_on_formula (ϕ := ϕ) f.2⟩

@[simp] theorem on_sentence_fst (ϕ : L →ᴸ L') (f : sentence L) :
    ((on_sentence ϕ f : sentence L') : formula L') = on_formula ϕ (f : formula L) :=
  rfl

section FilterSymbols

@[reducible] def filter_symbols (p : L.symbols → Prop) : Language :=
  ⟨fun l => { f : L.functions l // p (Sum.inl ⟨l, f⟩) },
    fun l => { R : L.relations l // p (Sum.inr ⟨l, R⟩) }⟩

def filter_symbols_Lhom (p : L.symbols → Prop) : filter_symbols p →ᴸ L :=
  ⟨fun {n} f => f.1, fun {n} R => R.1⟩

def is_injective_filter_symbols_Lhom (p : L.symbols → Prop) :
    is_injective (filter_symbols_Lhom p) :=
  ⟨fun {n} => Subtype.val_injective, fun {n} => Subtype.val_injective⟩

def find_term_filter_symbols (p : L.symbols → Prop) :
    {l : Nat} → (t : preterm L l) → symbols_in_term t ⊆ { s | p s } →
      Σ' t' : preterm (filter_symbols p) l, on_term (filter_symbols_Lhom p) t' = t
  | _, .var k, _ => ⟨&k, rfl⟩
  | l, .func f, h => by
      refine ⟨preterm.func ⟨f, ?_⟩, ?_⟩
      have hs : (Sum.inl ⟨l, f⟩ : L.symbols) ∈ symbols_in_term (preterm.func f) := by
        exact Set.mem_singleton _
      exact h hs
      simp [on_term, filter_symbols_Lhom]
  | _, .app t₁ t₂, h => by
      rcases find_term_filter_symbols p t₁ (by
        intro x hx
        exact h (Or.inl hx)) with ⟨t₁', ht₁⟩
      rcases find_term_filter_symbols p t₂ (by
        intro x hx
        exact h (Or.inr hx)) with ⟨t₂', ht₂⟩
      refine ⟨preterm.app t₁' t₂', ?_⟩
      simp [on_term, ht₁, ht₂]

def find_formula_filter_symbols (p : L.symbols → Prop) :
    {l : Nat} → (f : preformula L l) → symbols_in_formula f ⊆ { s | p s } →
      Σ' f' : preformula (filter_symbols p) l, on_formula (filter_symbols_Lhom p) f' = f
  | _, .falsum, _ => ⟨⊥, rfl⟩
  | _, .equal t₁ t₂, h => by
      rcases find_term_filter_symbols p t₁ (by
        intro x hx
        exact h (Or.inl hx)) with ⟨t₁', ht₁⟩
      rcases find_term_filter_symbols p t₂ (by
        intro x hx
        exact h (Or.inr hx)) with ⟨t₂', ht₂⟩
      refine ⟨t₁' ≃ t₂', ?_⟩
      simp [on_formula, ht₁, ht₂]
  | l, .rel R, h => by
      refine ⟨preformula.rel ⟨R, ?_⟩, ?_⟩
      have hs : (Sum.inr ⟨l, R⟩ : L.symbols) ∈ symbols_in_formula (preformula.rel R) := by
        exact Set.mem_singleton _
      exact h hs
      simp [on_formula, filter_symbols_Lhom]
  | _, .apprel f t, h => by
      rcases find_formula_filter_symbols p f (by
        intro x hx
        exact h (Or.inl hx)) with ⟨f', hf⟩
      rcases find_term_filter_symbols p t (by
        intro x hx
        exact h (Or.inr hx)) with ⟨t', ht⟩
      refine ⟨preformula.apprel f' t', ?_⟩
      simp [on_formula, hf, ht]
  | _, .imp f₁ f₂, h => by
      rcases find_formula_filter_symbols p f₁ (by
        intro x hx
        exact h (Or.inl hx)) with ⟨f₁', hf₁⟩
      rcases find_formula_filter_symbols p f₂ (by
        intro x hx
        exact h (Or.inr hx)) with ⟨f₂', hf₂⟩
      refine ⟨f₁' ⟹ f₂', ?_⟩
      simp [on_formula, hf₁, hf₂]
  | _, .all f, h => by
      rcases find_formula_filter_symbols p f h with ⟨f', hf⟩
      refine ⟨∀' f', ?_⟩
      simp [on_formula, hf]

end FilterSymbols

noncomputable def on_prf (ϕ : L →ᴸ L') {Γ : Set (formula L)} {f : formula L}
    (h : Γ ⊢ f) : (on_formula ϕ '' Γ) ⊢ on_formula ϕ f := by
  induction h with
  | axm h =>
      exact prf.axm (Set.mem_image_of_mem _ h)
  | impI h ih =>
      refine prf.impI ?_
      simpa [Set.image_insert_eq] using ih
  | impE A h₁ h₂ ih₁ ih₂ =>
      exact prf.impE (on_formula ϕ A) ih₁ ih₂
  | falsumE h ih =>
      refine prf.falsumE ?_
      simpa [Set.image_insert_eq, fol.not] using ih
  | allI h ih =>
      refine prf.allI ?_
      simpa [Set.image_image, Function.comp, lift_formula1, lift_formula] using ih
  | allE₂ A t h ih =>
      exact allE (A := on_formula ϕ A) (t := on_term ϕ t) ih
        (by simpa using (on_formula_subst ϕ A t 0))
  | ref Γ t =>
      exact prf.ref _ (on_term ϕ t)
  | subst₂ s t f hEq hSub ihEq ihSub =>
      exact subst (f₁ := on_formula ϕ f) ihEq
        (by simpa using ihSub)
        (by simpa using (on_formula_subst ϕ f t 0))

@[reducible] def Theory_induced (ϕ : L →ᴸ L') (T : Theory L) : Theory L' :=
  (on_sentence ϕ '' T.carrier : Theory L')

@[simp] theorem Theory_induced_fst (ϕ : L →ᴸ L') (T : Theory L) :
    Theory.fst (Theory_induced ϕ T) = on_formula ϕ '' Theory.fst T := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨s, hs, rfl⟩
    rcases hs with ⟨t, ht, rfl⟩
    refine ⟨(t : formula L), ?_, ?_⟩
    · exact ⟨t, ht, rfl⟩
    · simpa using (on_sentence_fst ϕ t)
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨t, ht, rfl⟩
    refine ⟨on_sentence ϕ t, ?_, ?_⟩
    · exact ⟨t, ht, rfl⟩
    · simpa using hxy

noncomputable def on_sprf (ϕ : L →ᴸ L') {T : Theory L} {f : sentence L} (h : T ⊢ f) :
    Theory_induced ϕ T ⊢ on_sentence ϕ f := by
  have h' := on_prf ϕ h
  simpa [sprf, Theory_induced_fst, on_sentence_fst] using h'

theorem on_term_inj {ϕ : L →ᴸ L'} (h : is_injective ϕ) :
    {l : Nat} → Function.Injective (@on_term L L' ϕ l)
  | _, .var k, .var k', hxy => by simpa using hxy
  | _, .var _, .func _, hxy => by cases hxy
  | _, .var _, .app _ _, hxy => by cases hxy
  | _, .func _, .var _, hxy => by cases hxy
  | _, .func f, .func g, hxy => by
      have hf : ϕ.on_function f = ϕ.on_function g := by simpa using hxy
      have : f = g := h.on_function hf
      cases this
      rfl
  | _, .func _, .app _ _, hxy => by cases hxy
  | _, .app _ _, .var _, hxy => by cases hxy
  | _, .app _ _, .func _, hxy => by cases hxy
  | _, .app t₁ s₁, .app t₂ s₂, hxy => by
      injection hxy with _ ht hs
      have ht' := on_term_inj h ht
      have hs' := on_term_inj h hs
      cases ht'
      cases hs'
      rfl

theorem on_formula_inj {ϕ : L →ᴸ L'} (h : is_injective ϕ) :
    {l : Nat} → Function.Injective (@on_formula L L' ϕ l)
  | _, .falsum, .falsum, hxy => by cases hxy; rfl
  | _, .falsum, .equal _ _, hxy => by cases hxy
  | _, .falsum, .rel _, hxy => by cases hxy
  | _, .falsum, .apprel _ _, hxy => by cases hxy
  | _, .falsum, .imp _ _, hxy => by cases hxy
  | _, .falsum, .all _, hxy => by cases hxy
  | _, .equal _ _, .falsum, hxy => by cases hxy
  | _, .equal t₁ t₂, .equal s₁ s₂, hxy => by
      injection hxy with ht hs
      have ht' := on_term_inj h ht
      have hs' := on_term_inj h hs
      cases ht'
      cases hs'
      rfl
  | _, .equal _ _, .rel _, hxy => by cases hxy
  | _, .equal _ _, .apprel _ _, hxy => by cases hxy
  | _, .equal _ _, .imp _ _, hxy => by cases hxy
  | _, .equal _ _, .all _, hxy => by cases hxy
  | _, .rel _, .falsum, hxy => by cases hxy
  | _, .rel R, .rel S, hxy => by
      have hR : ϕ.on_relation R = ϕ.on_relation S := by simpa using hxy
      have : R = S := h.on_relation hR
      cases this
      rfl
  | _, .rel _, .equal _ _, hxy => by cases hxy
  | _, .rel _, .apprel _ _, hxy => by cases hxy
  | _, .rel _, .imp _ _, hxy => by cases hxy
  | _, .rel _, .all _, hxy => by cases hxy
  | _, .apprel _ _, .falsum, hxy => by cases hxy
  | _, .apprel _ _, .equal _ _, hxy => by cases hxy
  | _, .apprel _ _, .rel _, hxy => by cases hxy
  | _, .apprel f t, .apprel g s, hxy => by
      injection hxy with _ hf ht
      have hf' := on_formula_inj h hf
      have ht' := on_term_inj h ht
      cases hf'
      cases ht'
      rfl
  | _, .apprel _ _, .imp _ _, hxy => by cases hxy
  | _, .apprel _ _, .all _, hxy => by cases hxy
  | _, .imp _ _, .falsum, hxy => by cases hxy
  | _, .imp _ _, .equal _ _, hxy => by cases hxy
  | _, .imp _ _, .rel _, hxy => by cases hxy
  | _, .imp _ _, .apprel _ _, hxy => by cases hxy
  | _, .imp f₁ f₂, .imp g₁ g₂, hxy => by
      injection hxy with hf hg
      have hf' := on_formula_inj h hf
      have hg' := on_formula_inj h hg
      cases hf'
      cases hg'
      rfl
  | _, .imp _ _, .all _, hxy => by cases hxy
  | _, .all _, .falsum, hxy => by cases hxy
  | _, .all _, .equal _ _, hxy => by cases hxy
  | _, .all _, .rel _, hxy => by cases hxy
  | _, .all _, .apprel _ _, hxy => by cases hxy
  | _, .all _, .imp _ _, hxy => by cases hxy
  | _, .all f, .all g, hxy => by
      injection hxy with hf
      have hf' := on_formula_inj h hf
      cases hf'
      rfl

theorem on_bounded_term_inj {ϕ : L →ᴸ L'} (h : is_injective ϕ) {n l : Nat} :
    Function.Injective (@on_bounded_term L L' ϕ n l) := by
  intro x y hxy
  apply Subtype.ext
  exact on_term_inj h (congrArg Subtype.val hxy)

theorem on_bounded_formula_inj {ϕ : L →ᴸ L'} (h : is_injective ϕ) {n l : Nat} :
    Function.Injective (@on_bounded_formula L L' ϕ n l) := by
  intro x y hxy
  apply Subtype.ext
  exact on_formula_inj h (congrArg Subtype.val hxy)

def reduct (ϕ : L →ᴸ L') (M : Structure L') : Structure L :=
  ⟨M.carrier, fun f xs => M.fun_map (ϕ.on_function f) xs, fun R xs => M.rel_map (ϕ.on_relation R) xs⟩

@[simp] theorem reduct_coe (ϕ : L →ᴸ L') (M : Structure L') : ↥(reduct ϕ M) = M := rfl

@[simp] theorem reduct_term_eq (ϕ : L →ᴸ L') {M : Structure L'} : {l : Nat} →
    (v : Nat → M) → (t : preterm L l) → (xs : dvector M l) →
    realize_term v (on_term ϕ t) xs = realize_term (M := reduct ϕ M) v t xs
  | _, _, .var _, _ => rfl
  | _, _, .func _, _ => rfl
  | _, v, .app t₁ t₂, xs => by
      simp [realize_term, reduct_term_eq (ϕ := ϕ) (v := v) (t := t₁),
        reduct_term_eq (ϕ := ϕ) (v := v) (t := t₂)]

theorem reduct_formula_iff (ϕ : L →ᴸ L') {M : Structure L'} : {l : Nat} →
    (v : Nat → M) → (f : preformula L l) → (xs : dvector M l) →
    realize_formula v (on_formula ϕ f) xs ↔ realize_formula (M := reduct ϕ M) v f xs
  | _, _, .falsum, _ => Iff.rfl
  | _, v, .equal t₁ t₂, xs => by
      simp [realize_formula, reduct_term_eq (ϕ := ϕ) (v := v)]
  | _, _, .rel _, _ => Iff.rfl
  | _, v, .apprel f t, xs => by
      simp [realize_formula, reduct_formula_iff (ϕ := ϕ) (v := v) (f := f),
        reduct_term_eq (ϕ := ϕ) (v := v) (t := t)]
  | _, v, .imp f₁ f₂, xs => by
      simp [realize_formula, reduct_formula_iff (ϕ := ϕ) (v := v) (f := f₁),
        reduct_formula_iff (ϕ := ϕ) (v := v) (f := f₂)]
  | _, v, .all f, xs => by
      constructor
      · intro h x
        simpa [realize_formula] using (reduct_formula_iff (ϕ := ϕ) (v := v[x // 0]) (f := f) (xs := xs)).mp (h x)
      · intro h x
        simpa [realize_formula] using (reduct_formula_iff (ϕ := ϕ) (v := v[x // 0]) (f := f) (xs := xs)).mpr (h x)

theorem reduct_realize_sentence (ϕ : L →ᴸ L') {M : Structure L'} {f : sentence L} :
    realize_sentence M (on_sentence ϕ f) ↔ realize_sentence (reduct ϕ M) f := by
  constructor <;> intro h v
  · simpa [realize_sentence, on_sentence_fst] using
      (reduct_formula_iff (ϕ := ϕ) (v := v) (f := (f : formula L)) (xs := ([] : dvector M 0))).mp (h v)
  · simpa [realize_sentence, on_sentence_fst] using
      (reduct_formula_iff (ϕ := ϕ) (v := v) (f := (f : formula L)) (xs := ([] : dvector M 0))).mpr (h v)

theorem reduct_all_realize_sentence (ϕ : L →ᴸ L') {M : Structure L'} {T : Theory L}
    (h : all_realize_sentence M (Theory_induced ϕ T)) : all_realize_sentence (reduct ϕ M) T := by
  intro f hf
  apply (reduct_realize_sentence (ϕ := ϕ)).mp
  exact h (Set.mem_image_of_mem _ hf)

theorem reduct_nonempty_of_nonempty (ϕ : L →ᴸ L') {M : Structure L'} (h : Nonempty M) :
    Nonempty (reduct ϕ M) := h

noncomputable def reflect_term (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (t : term L') (m : Nat) : term L :=
  by
    classical
    exact
      term.elim
        (fun k => (&k : term L) ↑' 1 # m)
        (fun {l} f' ts' ts =>
          if hf' : f' ∈ Set.range (@Lhom.on_function _ _ ϕ l) then
            apps (preterm.func (Classical.choose hf')) ts
          else
            &m) t

lemma reflect_term_apps_pos (ϕ : L →ᴸ L') [has_decidable_range ϕ] {l : Nat} {f : L'.functions l}
    (hf : f ∈ Set.range (@Lhom.on_function _ _ ϕ l)) (ts : dvector (term L') l) (m : Nat) :
    reflect_term ϕ (apps (preterm.func f) ts) m =
      apps (preterm.func (Classical.choose hf)) (ts.map fun t => reflect_term ϕ t m) := by
  classical
  unfold reflect_term
  rw [term.elim_apps]
  simp [Set.mem_range, hf]

lemma reflect_term_apps_neg (ϕ : L →ᴸ L') [has_decidable_range ϕ] {l : Nat} {f : L'.functions l}
    (hf : f ∉ Set.range (@Lhom.on_function _ _ ϕ l)) (ts : dvector (term L') l) (m : Nat) :
    reflect_term ϕ (apps (preterm.func f) ts) m = &m := by
  classical
  unfold reflect_term
  rw [term.elim_apps]
  simp [Set.mem_range, hf]

lemma reflect_term_const_pos (ϕ : L →ᴸ L') [has_decidable_range ϕ] {c : L'.constants}
    (hf : c ∈ Set.range (@Lhom.on_function _ _ ϕ 0)) (m : Nat) :
    reflect_term ϕ (preterm.func c) m = preterm.func (Classical.choose hf) := by
  simpa using reflect_term_apps_pos (ϕ := ϕ) hf ([] : dvector (term L') 0) m

lemma reflect_term_const_neg (ϕ : L →ᴸ L') [has_decidable_range ϕ] {c : L'.constants}
    (hf : c ∉ Set.range (@Lhom.on_function _ _ ϕ 0)) (m : Nat) :
    reflect_term ϕ (preterm.func c) m = &m := by
  simpa using reflect_term_apps_neg (ϕ := ϕ) hf ([] : dvector (term L') 0) m

@[simp] lemma reflect_term_var (ϕ : L →ᴸ L') [has_decidable_range ϕ] (k m : Nat) :
    reflect_term ϕ (&k : term L') m = (&k : term L) ↑' 1 # m := by
  rfl

@[simp] lemma reflect_term_on_term (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) (t : term L) (m : Nat) :
    reflect_term ϕ (on_term ϕ t) m = t ↑' 1 # m := by
  classical
  refine term.rec (C := fun t : term L => reflect_term ϕ (on_term ϕ t) m = t ↑' 1 # m) ?_ ?_ t
  · intro k
    rfl
  · intro l f ts ih_ts
    have hf : ϕ.on_function f ∈ Set.range (@Lhom.on_function _ _ ϕ l) := ⟨f, rfl⟩
    have hchoose : Classical.choose hf = f := by
      apply hϕ.on_function
      exact Classical.choose_spec hf
    simp [reflect_term_apps_pos, hf, hchoose, dvector.map_congr_pmem ih_ts]

lemma reflect_term_lift_at (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {n m m' : Nat} (h : m ≤ m') (t : term L') :
    reflect_term ϕ (t ↑' n # m) (m' + n) = reflect_term ϕ t m' ↑' n # m := by
  classical
  refine term.rec (C := fun t : term L' =>
    reflect_term ϕ (t ↑' n # m) (m' + n) = reflect_term ϕ t m' ↑' n # m) ?_ ?_ t
  · intro k
    by_cases hm'k : m' ≤ k
    · have hmk : m ≤ k := le_trans h hm'k
      have hmkn : m ≤ k + 1 := le_trans hmk (Nat.le_succ _)
      have hm'kn : m' + n ≤ k + n := Nat.add_le_add_right hm'k n
      simp [reflect_term_var, lift_term_at, hmk, hm'k, hmkn, hm'kn, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]
    · by_cases hmk : m ≤ k
      · have hm'kn : ¬ m' + n ≤ k + n := by
          intro hm'kn
          exact hm'k (Nat.le_of_add_le_add_right hm'kn)
        simp [reflect_term_var, lift_term_at, hmk, hm'k, hm'kn, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]
      · have hm'kn : ¬ m' + n ≤ k := by
          intro hm'kn
          exact hm'k (le_trans (Nat.le_add_right m' n) hm'kn)
        have hlt : k < m' + n := by
          omega
        have hlt' : k < n + m' := by
          simpa [Nat.add_comm] using hlt
        simp [reflect_term_var, lift_term_at, hmk, hm'k, hm'kn, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm, hlt']
  · intro l f ts ih_ts
    by_cases h' : f ∈ Set.range (@Lhom.on_function _ _ ϕ l)
    · have hmap :
          ts.map (fun x => reflect_term ϕ (x ↑' n # m) (m' + n)) =
            ts.map (fun x => reflect_term ϕ x m' ↑' n # m) := dvector.map_congr_pmem ih_ts
      simpa [reflect_term_apps_pos, h', Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
        congrArg (apps (preterm.func (Classical.choose h'))) hmap
    · have hnot : ¬ m' < m := Nat.not_lt_of_ge h
      simp [reflect_term_apps_neg, h', Nat.add_comm, Nat.add_assoc, Nat.add_left_comm, hnot]

lemma reflect_term_lift (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {n m : Nat} (t : term L') :
    reflect_term ϕ (t ↑ n) (m + n) = (reflect_term ϕ t m) ↑ n :=
  reflect_term_lift_at (ϕ := ϕ) hϕ (m := 0) (m' := m) (Nat.zero_le m) t

noncomputable def reflect_formula (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (f : formula L') : Nat → formula L :=
  by
    classical
    exact
      formula.rec (L := L') (C := fun _ => Nat → formula L)
        (fun _ => (⊥ : formula L))
        (fun t₁ t₂ m => reflect_term ϕ t₁ m ≃ reflect_term ϕ t₂ m)
        (fun {l} R' xs' m =>
          if hR' : R' ∈ Set.range (@Lhom.on_relation _ _ ϕ l) then
            apps_rel (preformula.rel (Classical.choose hR')) (xs'.map fun t => reflect_term ϕ t m)
          else
            ⊥)
        (fun h₁ h₂ m => h₁ m ⟹ h₂ m)
        (fun h m => ∀' h (m + 1))
        f

lemma reflect_formula_apps_rel_pos (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    {l : Nat} {R : L'.relations l} (hR : R ∈ Set.range (@Lhom.on_relation _ _ ϕ l))
    (ts : dvector (term L') l) (m : Nat) :
    reflect_formula ϕ (apps_rel (preformula.rel R) ts) m =
      apps_rel (preformula.rel (Classical.choose hR)) (ts.map fun t => reflect_term ϕ t m) := by
  classical
  unfold reflect_formula
  rw [formula.rec_apps_rel]
  simp [Set.mem_range, hR]

lemma reflect_formula_apps_rel_neg (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    {l : Nat} {R : L'.relations l} (hR : R ∉ Set.range (@Lhom.on_relation _ _ ϕ l))
    (ts : dvector (term L') l) (m : Nat) :
    reflect_formula ϕ (apps_rel (preformula.rel R) ts) m = ⊥ := by
  classical
  unfold reflect_formula
  rw [formula.rec_apps_rel]
  simp [Set.mem_range, hR]

@[simp] lemma reflect_formula_equal (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (t₁ t₂ : term L') (m : Nat) :
    reflect_formula ϕ (t₁ ≃ t₂) m = reflect_term ϕ t₁ m ≃ reflect_term ϕ t₂ m := by
  rfl

@[simp] lemma reflect_formula_imp (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (f₁ f₂ : formula L') (m : Nat) :
    reflect_formula ϕ (f₁ ⟹ f₂) m = reflect_formula ϕ f₁ m ⟹ reflect_formula ϕ f₂ m := by
  rfl

@[simp] lemma reflect_formula_all (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (f : formula L') (m : Nat) :
    reflect_formula ϕ (∀' f) m = ∀' (reflect_formula ϕ f (m + 1)) := by
  rfl

@[simp] lemma reflect_formula_on_formula (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) (m : Nat) (f : formula L) :
    reflect_formula ϕ (on_formula ϕ f) m = lift_formula_at f 1 m := by
  classical
  refine formula.rec
    (C := fun f : formula L => ∀ m, reflect_formula ϕ (on_formula ϕ f) m = lift_formula_at f 1 m) ?_ ?_ ?_ ?_ ?_ f m
  · intro m
    rfl
  · intro t₁ t₂ m
    simp [hϕ]
  · intro l R ts m
    have hR : ϕ.on_relation R ∈ Set.range (@Lhom.on_relation _ _ ϕ l) := ⟨R, rfl⟩
    have hchoose : Classical.choose hR = R := by
      apply hϕ.on_relation
      exact Classical.choose_spec hR
    simpa [reflect_formula_apps_rel_pos, hR, hchoose, hϕ, lift_formula_at_apps_rel]
      using rfl
  · intro f₁ f₂ ih₁ ih₂ m
    simp [ih₁, ih₂]
  · intro f ih m
    simp [ih]

lemma reflect_formula_lift_at (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {n m m' : Nat} (h : m ≤ m') (f : formula L') :
    reflect_formula ϕ (lift_formula_at f n m) (m' + n) =
      lift_formula_at (reflect_formula ϕ f m') n m := by
  classical
  refine formula.rec
    (C := fun f : formula L' => ∀ {m m' : Nat}, m ≤ m' →
      reflect_formula ϕ (lift_formula_at f n m) (m' + n) =
        lift_formula_at (reflect_formula ϕ f m') n m) ?_ ?_ ?_ ?_ ?_ f h
  · intro m m' h
    rfl
  · intro t₁ t₂ m m' h
    simp [lift_formula_at, reflect_term_lift_at (ϕ := ϕ) hϕ h]
  · intro l R ts m m' h
    by_cases hR : R ∈ Set.range (@Lhom.on_relation _ _ ϕ l)
    · have hmap :
          ts.map (fun t => reflect_term ϕ (t ↑' n # m) (m' + n)) =
            ts.map (fun t => reflect_term ϕ t m' ↑' n # m) := by
        exact dvector.map_congr_pmem (fun t ht =>
          reflect_term_lift_at (ϕ := ϕ) hϕ (n := n) (m := m) (m' := m') h t)
      calc
        reflect_formula ϕ (lift_formula_at (apps_rel (preformula.rel R) ts) n m) (m' + n) =
            apps_rel (preformula.rel (Classical.choose hR))
              ((ts.map fun t => t ↑' n # m).map fun t => reflect_term ϕ t (m' + n)) := by
              simpa [lift_formula_at_apps_rel] using
                reflect_formula_apps_rel_pos (ϕ := ϕ) hR (ts.map fun t => t ↑' n # m) (m' + n)
        _ = apps_rel (preformula.rel (Classical.choose hR))
            (ts.map fun t => reflect_term ϕ t m' ↑' n # m) := by
              simpa [dvector.map_map] using
                congrArg (apps_rel (preformula.rel (Classical.choose hR))) hmap
        _ = lift_formula_at
            (apps_rel (preformula.rel (Classical.choose hR)) (ts.map fun t => reflect_term ϕ t m'))
            n m := by
              symm
              simpa [lift_formula_at_apps_rel]
        _ = lift_formula_at (reflect_formula ϕ (apps_rel (preformula.rel R) ts) m') n m := by
              rw [reflect_formula_apps_rel_pos (ϕ := ϕ) hR ts m']
    · rw [reflect_formula_apps_rel_neg (ϕ := ϕ) hR ts m']
      simpa [lift_formula_at_apps_rel, lift_formula_at] using
        reflect_formula_apps_rel_neg (ϕ := ϕ) hR (ts.map fun t => t ↑' n # m) (m' + n)
  · intro f₁ f₂ ih₁ ih₂ m m' h
    simp [lift_formula_at, ih₁ h, ih₂ h]
  · intro f ih m m' h
    simpa [lift_formula_at, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (m := m + 1) (m' := m' + 1) (Nat.add_le_add_right h 1)

lemma reflect_formula_lift (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {n m : Nat} (f : formula L') :
    reflect_formula ϕ (lift_formula f n) (m + n) = lift_formula (reflect_formula ϕ f m) n := by
  simpa [lift_formula] using
    reflect_formula_lift_at (ϕ := ϕ) hϕ (n := n) (m := 0) (m' := m) (Nat.zero_le m) f

@[simp] lemma reflect_formula_lift1 (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) (f : formula L') (m : Nat) :
    reflect_formula ϕ (lift_formula1 f) (m + 1) = lift_formula1 (reflect_formula ϕ f m) := by
  simpa [lift_formula1, lift_formula] using
    reflect_formula_lift (ϕ := ϕ) hϕ (n := 1) (m := m) f

lemma reflect_term_subst (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) (t s : term L') (n m : Nat) :
    reflect_term ϕ (subst_term t s n) (m + n) =
      subst_term (reflect_term ϕ t (m + n + 1)) (reflect_term ϕ s m) n := by
  classical
  refine term.rec
    (C := fun t : term L' => ∀ n m,
      reflect_term ϕ (subst_term t s n) (m + n) =
        subst_term (reflect_term ϕ t (m + n + 1)) (reflect_term ϕ s m) n) ?_ ?_ t n m
  · intro k n m
    by_cases hlt : k < n
    · have hcut : ¬ m + n ≤ k := by
        omega
      have hcut' : ¬ m + n + 1 ≤ k := by
        omega
      calc
        reflect_term ϕ (subst_term (&k : term L') s n) (m + n) = (&k : term L) := by
          simp [subst_term, subst_realize, hlt, reflect_term_var, lift_term_at, hcut]
        _ = subst_term (&k : term L) (reflect_term ϕ s m) n := by
          symm
          simpa using
            (subst_term_var_lt (L := L) (s := reflect_term ϕ s m) (k := k) (n := n) hlt)
        _ = subst_term (reflect_term ϕ (&k : term L') (m + n + 1)) (reflect_term ϕ s m) n := by
          simp [reflect_term_var, lift_term_at, hcut']
    · by_cases hgt : n < k
      · by_cases hcut : m + n ≤ k - 1
        · have hcut' : m + n + 1 ≤ k := by
            omega
          rw [subst_term_var_gt (L := L') (s := s) (k := k) (n := n) hgt]
          have href : reflect_term ϕ (&k : term L') (m + n + 1) = (&(k + 1) : term L) := by
            simp [reflect_term_var, lift_term_at, hcut']
          rw [href]
          have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le n) hgt
          have hleft : reflect_term ϕ (&(k - 1) : term L') (m + n) = (&k : term L) := by
            simp [reflect_term_var, lift_term_at, hcut, Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)]
          have hright :
              subst_term (&(k + 1) : term L) (reflect_term ϕ s m) n = (&k : term L) := by
            simpa [Nat.succ_eq_add_one] using
              (subst_term_var_gt (L := L) (s := reflect_term ϕ s m) (k := k + 1) (n := n)
                (Nat.lt_succ_of_lt hgt))
          rw [hleft, hright]
        · have hcut' : ¬ m + n + 1 ≤ k := by
            omega
          rw [subst_term_var_gt (L := L') (s := s) (k := k) (n := n) hgt]
          have href : reflect_term ϕ (&k : term L') (m + n + 1) = (&k : term L) := by
            simp [reflect_term_var, lift_term_at, hcut']
          rw [href]
          have hleft : reflect_term ϕ (&(k - 1) : term L') (m + n) = (&(k - 1) : term L) := by
            simp [reflect_term_var, lift_term_at, hcut]
          have hright :
              subst_term (&k : term L) (reflect_term ϕ s m) n = (&(k - 1) : term L) := by
            simpa using
              (subst_term_var_gt (L := L) (s := reflect_term ϕ s m) (k := k) (n := n) hgt)
          rw [hleft, hright]
      · have hk : k = n := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
        subst n
        calc
          reflect_term ϕ (subst_term (&k : term L') s k) (m + k) =
              reflect_term ϕ (s ↑' k # 0) (m + k) := by
                simp [subst_term, subst_realize]
          _ = reflect_term ϕ s m ↑' k # 0 := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  (reflect_term_lift_at (ϕ := ϕ) hϕ (n := k) (m := 0) (m' := m) (Nat.zero_le m) s)
          _ = subst_term (&k : term L) (reflect_term ϕ s m) k := by
                symm
                simpa using (subst_term_var_eq (L := L) (s := reflect_term ϕ s m) k)
          _ = subst_term (reflect_term ϕ (&k : term L') (m + k + 1)) (reflect_term ϕ s m) k := by
                have hcut : ¬ m + k + 1 ≤ k := by
                  omega
                simp [reflect_term_var, lift_term_at, hcut]
  · intro l f ts ih_ts n m
    by_cases hf : f ∈ Set.range (@Lhom.on_function _ _ ϕ l)
    · have hmap :
          ts.map (fun x => reflect_term ϕ (subst_term x s n) (m + n)) =
            ts.map (fun x =>
              subst_term (reflect_term ϕ x (m + n + 1)) (reflect_term ϕ s m) n) := by
        exact dvector.map_congr_pmem (fun x hx => ih_ts x hx n m)
      calc
        reflect_term ϕ (subst_term (apps (preterm.func f) ts) s n) (m + n) =
            apps (preterm.func (Classical.choose hf))
              ((ts.map fun x => subst_term x s n).map fun x => reflect_term ϕ x (m + n)) := by
              simpa [subst_term_apps] using
                reflect_term_apps_pos (ϕ := ϕ) hf (ts.map fun x => subst_term x s n) (m + n)
        _ = apps (preterm.func (Classical.choose hf))
            (ts.map fun x =>
              subst_term (reflect_term ϕ x (m + n + 1)) (reflect_term ϕ s m) n) := by
              simpa [dvector.map_map] using
                congrArg (apps (preterm.func (Classical.choose hf))) hmap
        _ = subst_term
            (apps (preterm.func (Classical.choose hf)) (ts.map fun x => reflect_term ϕ x (m + n + 1)))
            (reflect_term ϕ s m) n := by
              calc
                apps (preterm.func (Classical.choose hf))
                    (ts.map fun x => subst_term (reflect_term ϕ x (m + n + 1)) (reflect_term ϕ s m) n) =
                  apps (preterm.func (Classical.choose hf))
                    ((ts.map fun x => reflect_term ϕ x (m + n + 1)).map
                      fun x => subst_term x (reflect_term ϕ s m) n) := by
                        simpa [dvector.map_map]
                _ = subst_term
                    (apps (preterm.func (Classical.choose hf)) (ts.map fun x => reflect_term ϕ x (m + n + 1)))
                    (reflect_term ϕ s m) n := by
                      simpa [subst_term_apps, subst_term]
        _ = subst_term (reflect_term ϕ (apps (preterm.func f) ts) (m + n + 1))
            (reflect_term ϕ s m) n := by
              rw [reflect_term_apps_pos (ϕ := ϕ) hf ts (m + n + 1)]
    · have hmn : n < m + n + 1 := by
        omega
      calc
        reflect_term ϕ (subst_term (apps (preterm.func f) ts) s n) (m + n) = &(m + n) := by
          simpa [subst_term_apps] using
            reflect_term_apps_neg (ϕ := ϕ) hf (ts.map fun x => subst_term x s n) (m + n)
        _ = subst_term (&(m + n + 1) : term L) (reflect_term ϕ s m) n := by
          symm
          simpa using
            (subst_term_var_gt (L := L) (s := reflect_term ϕ s m) (k := m + n + 1) (n := n) hmn)
        _ = subst_term (reflect_term ϕ (apps (preterm.func f) ts) (m + n + 1))
            (reflect_term ϕ s m) n := by
              rw [reflect_term_apps_neg (ϕ := ϕ) hf ts (m + n + 1)]

lemma reflect_formula_subst (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) (f : formula L') (t : term L') (n m : Nat) :
    reflect_formula ϕ (subst_formula f t n) (m + n) =
      subst_formula (reflect_formula ϕ f (m + n + 1)) (reflect_term ϕ t m) n := by
  classical
  refine formula.rec
    (C := fun f : formula L' => ∀ t n m,
      reflect_formula ϕ (subst_formula f t n) (m + n) =
        subst_formula (reflect_formula ϕ f (m + n + 1)) (reflect_term ϕ t m) n) ?_ ?_ ?_ ?_ ?_
    f t n m
  · intro t n m
    rfl
  · intro t₁ t₂ t n m
    simp [subst_formula, reflect_term_subst, hϕ]
  · intro l R ts t n m
    by_cases hR : R ∈ Set.range (@Lhom.on_relation _ _ ϕ l)
    · have hmap :
          ts.map (fun x => reflect_term ϕ (subst_term x t n) (m + n)) =
            ts.map (fun x =>
              subst_term (reflect_term ϕ x (m + n + 1)) (reflect_term ϕ t m) n) := by
        exact dvector.map_congr_pmem (fun x hx => reflect_term_subst (ϕ := ϕ) hϕ x t n m)
      calc
        reflect_formula ϕ (subst_formula (apps_rel (preformula.rel R) ts) t n) (m + n) =
            apps_rel (preformula.rel (Classical.choose hR))
              ((ts.map fun x => subst_term x t n).map fun x => reflect_term ϕ x (m + n)) := by
              simpa [subst_formula_apps_rel] using
                reflect_formula_apps_rel_pos (ϕ := ϕ) hR (ts.map fun x => subst_term x t n) (m + n)
        _ = apps_rel (preformula.rel (Classical.choose hR))
            (ts.map fun x =>
              subst_term (reflect_term ϕ x (m + n + 1)) (reflect_term ϕ t m) n) := by
              simpa [dvector.map_map] using
                congrArg (apps_rel (preformula.rel (Classical.choose hR))) hmap
        _ = subst_formula
            (apps_rel (preformula.rel (Classical.choose hR))
              (ts.map fun x => reflect_term ϕ x (m + n + 1)))
            (reflect_term ϕ t m) n := by
              symm
              simpa [subst_formula_apps_rel]
        _ = subst_formula
            (reflect_formula ϕ (apps_rel (preformula.rel R) ts) (m + n + 1))
            (reflect_term ϕ t m) n := by
              rw [reflect_formula_apps_rel_pos (ϕ := ϕ) hR ts (m + n + 1)]
    · rw [reflect_formula_apps_rel_neg (ϕ := ϕ) hR ts (m + n + 1)]
      simpa [subst_formula_apps_rel, subst_formula] using
        reflect_formula_apps_rel_neg (ϕ := ϕ) hR (ts.map fun x => subst_term x t n) (m + n)
  · intro f₁ f₂ ih₁ ih₂ t n m
    simp [subst_formula, ih₁ t n m, ih₂ t n m]
  · intro f ih t n m
    simpa [subst_formula, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih t (n + 1) m

@[simp] lemma reflect_formula_subst0 (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) (f : formula L') (t : term L') (m : Nat) :
    reflect_formula ϕ (subst_formula f t 0) m =
      subst_formula (reflect_formula ϕ f (m + 1)) (reflect_term ϕ t m) 0 := by
  simpa using reflect_formula_subst (ϕ := ϕ) hϕ f t 0 m

noncomputable def reflect_prf_gen (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {Γ : Set (formula L')} {f : formula L'} (m : Nat)
    (h : Γ ⊢ f) :
    (Set.image (fun g : formula L' => reflect_formula ϕ g m) Γ) ⊢ reflect_formula ϕ f m := by
  induction h generalizing m with
  | axm hmem =>
      exact prf.axm (Set.mem_image_of_mem _ hmem)
  | impI h ih =>
      refine prf.impI ?_
      simpa [Set.image_insert_eq] using ih (m := m)
  | impE A hImp hA ihImp ihA =>
      exact prf.impE (reflect_formula ϕ A m) (ihImp (m := m)) (ihA (m := m))
  | falsumE h ih =>
      rename_i G A
      have h' :
          insert (∼(reflect_formula ϕ A m))
            (Set.image (fun g : formula L' => reflect_formula ϕ g m) G) ⊢ (⊥ : formula L) := by
        simpa [Set.image_insert_eq, fol.not] using ih (m := m)
      exact prf.falsumE h'
  | allI h ih =>
      rename_i G A
      have h' :
          Set.image (fun g : formula L' => reflect_formula ϕ (lift_formula1 g) (m + 1)) G ⊢
            reflect_formula ϕ A (m + 1) := by
        simpa [Set.image_image, Function.comp] using ih (m := m + 1)
      have hset :
          Set.image (fun g : formula L' => reflect_formula ϕ (lift_formula1 g) (m + 1)) G =
            Set.image lift_formula1 (Set.image (fun g : formula L' => reflect_formula ϕ g m) G) := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, rfl⟩
          refine ⟨reflect_formula ϕ y m, Set.mem_image_of_mem _ hy, ?_⟩
          simpa using (reflect_formula_lift1 (ϕ := ϕ) hϕ y m).symm
        · intro hx
          rcases hx with ⟨y, ⟨z, hz, rfl⟩, hxy⟩
          refine ⟨z, hz, ?_⟩
          simpa using (reflect_formula_lift1 (ϕ := ϕ) hϕ z m).trans hxy
      have h'' :
          Set.image lift_formula1 (Set.image (fun g : formula L' => reflect_formula ϕ g m) G) ⊢
            reflect_formula ϕ A (m + 1) := by
        simpa [hset] using h'
      exact prf.allI h''
  | allE₂ A t h ih =>
      exact allE (A := reflect_formula ϕ A (m + 1)) (t := reflect_term ϕ t m) (ih (m := m))
        (reflect_formula_subst0 (ϕ := ϕ) hϕ A t m).symm
  | ref Γ t =>
      exact prf.ref _ (reflect_term ϕ t m)
  | subst₂ s t f hEq hSub ihEq ihSub =>
      exact subst (f₁ := reflect_formula ϕ f (m + 1)) (ihEq (m := m))
        (by simpa using (reflect_formula_subst0 (ϕ := ϕ) hϕ f s m).symm ▸ ihSub (m := m))
        (reflect_formula_subst0 (ϕ := ϕ) hϕ f t m).symm

noncomputable def reflect_prf (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {Γ : Set (formula L)} {f : formula L}
    (h : on_formula ϕ '' Γ ⊢ on_formula ϕ f) : Γ ⊢ f := by
  have h' := reflect_prf_gen (ϕ := ϕ) hϕ 0 h
  have hset :
      Set.image (fun g : formula L' => reflect_formula ϕ g 0) (on_formula ϕ '' Γ) =
        lift_formula1 '' Γ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, ⟨z, hz, rfl⟩, hxy⟩
      refine ⟨z, hz, ?_⟩
      simpa [lift_formula1] using
        (reflect_formula_on_formula (ϕ := ϕ) hϕ 0 z).symm.trans hxy
    · intro hx
      rcases hx with ⟨z, hz, rfl⟩
      refine ⟨on_formula ϕ z, ⟨z, hz, rfl⟩, ?_⟩
      simpa [lift_formula1] using reflect_formula_on_formula (ϕ := ϕ) hϕ 0 z
  have hf : reflect_formula ϕ (on_formula ϕ f) 0 = lift_formula1 f := by
    simpa [lift_formula1] using reflect_formula_on_formula (ϕ := ϕ) hϕ 0 f
  have h'' : lift_formula1 '' Γ ⊢ lift_formula1 f := by
    exact cast (by rw [hset, hf]) h'
  exact reflect_prf_lift1 h''

noncomputable def reflect_sprf (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {T : Theory L} {f : sentence L}
    (h : Theory_induced ϕ T ⊢ on_sentence ϕ f) : T ⊢ f := by
  have h' : on_formula ϕ '' Theory.fst T ⊢ on_formula ϕ (f : formula L) := by
    simpa [sprf, Theory_induced_fst, on_sentence_fst] using h
  have h'' := reflect_prf (ϕ := ϕ) hϕ h'
  simpa [sprf] using h''

lemma is_consistent_Theory_induced (ϕ : L →ᴸ L') [has_decidable_range ϕ]
    (hϕ : is_injective ϕ) {T : Theory L} (hT : is_consistent T) :
    is_consistent (Theory_induced ϕ T) := by
  intro h
  rcases h with ⟨h⟩
  exact hT ⟨reflect_sprf (ϕ := ϕ) hϕ h⟩

end Lhom

end fol
end Flypitch
