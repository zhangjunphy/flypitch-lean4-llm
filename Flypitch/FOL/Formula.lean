import Flypitch.FOL.Syntax

universe u v

namespace Flypitch
namespace fol

/-!
`Flypitch.FOL.Formula` defines formulas over a first-order language together with the
derived connectives, recursors, and the lifting/substitution lemmas used to manage
de Bruijn variables.
-/

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

variable (L : Language)

/-- Formulas with `l` relation arguments still to be supplied. -/
inductive preformula : Nat → Type u
  | falsum : preformula 0
  | equal : term L → term L → preformula 0
  | rel : {l : Nat} → L.relations l → preformula l
  | apprel : {l : Nat} → preformula (l + 1) → term L → preformula l
  | imp : preformula 0 → preformula 0 → preformula 0
  | all : preformula 0 → preformula 0

/-- Closed formulas. -/
abbrev formula := preformula L 0

variable {L}

instance : Bot (formula L) where
  bot := preformula.falsum

infix:88 " ≃ " => preformula.equal
infixr:62 " ⟹ " => preformula.imp
prefix:110 "∀' " => preformula.all

/-- Derived negation. -/
def not (f : formula L) : formula L :=
  f ⟹ ⊥

prefix:max "∼" => fol.not

instance : Top (formula L) where
  top := ∼(⊥ : formula L)

/-- Derived conjunction. -/
def and (f₁ f₂ : formula L) : formula L :=
  ∼(f₁ ⟹ ∼f₂)

/-- Derived disjunction. -/
def or (f₁ f₂ : formula L) : formula L :=
  ∼f₁ ⟹ f₂

/-- Derived biconditional. -/
def biimp (f₁ f₂ : formula L) : formula L :=
  and (f₁ ⟹ f₂) (f₂ ⟹ f₁)

/-- Derived existential quantification. -/
def ex (f : formula L) : formula L :=
  ∼(∀' ∼f)

/-- Fully apply a relation formula to a tuple of term arguments. -/
@[simp] def apps_rel : {l : Nat} → preformula L l → dvector (term L) l → formula L
  | 0, f, [] => f
  | _ + 1, f, t :: ts => apps_rel (preformula.apprel f t) ts

@[simp] theorem apps_rel_zero (f : formula L) (ts : dvector (term L) 0) : apps_rel f ts = f := by
  cases ts
  simp [apps_rel]

/-- View a relation symbol as an `arity'`-valued formula constructor. -/
def formula_of_relation {l : Nat} (R : L.relations l) : arity' (term L) (formula L) l :=
  arity'.ofDVectorMap (fun ts => apps_rel (preformula.rel R) ts)

/-- Recursor for formulas presented as fully applied formulas. -/
def formula.rec' {C : formula L → Sort v}
    (hfalsum : C ⊥)
    (hequal : Π t₁ t₂ : term L, C (t₁ ≃ t₂))
    (hrel : Π {l : Nat} (R : L.relations l) (ts : dvector (term L) l),
      C (apps_rel (preformula.rel R) ts))
    (himp : Π {f₁ f₂ : formula L}, C f₁ → C f₂ → C (f₁ ⟹ f₂))
    (hall : Π {f : formula L}, C f → C (∀' f)) :
    ∀ {l : Nat} (f : preformula L l) (ts : dvector (term L) l), C (apps_rel f ts)
  | _, .falsum, ts => by
      cases ts
      simpa using hfalsum
  | _, .equal t₁ t₂, ts => by
      cases ts
      simpa using hequal t₁ t₂
  | _, .rel R, ts => by
      simpa using hrel R ts
  | _, .apprel f t, ts => by
      simpa [apps_rel] using formula.rec' hfalsum hequal hrel himp hall f (t :: ts)
  | _, .imp f₁ f₂, ts => by
      cases ts
      simpa using himp (formula.rec' hfalsum hequal hrel himp hall f₁ [])
        (formula.rec' hfalsum hequal hrel himp hall f₂ [])
  | _, .all f, ts => by
      cases ts
      simpa using hall (formula.rec' hfalsum hequal hrel himp hall f [])

/-- Recursor on closed formulas. -/
def formula.rec {C : formula L → Sort v}
    (hfalsum : C ⊥)
    (hequal : Π t₁ t₂ : term L, C (t₁ ≃ t₂))
    (hrel : Π {l : Nat} (R : L.relations l) (ts : dvector (term L) l),
      C (apps_rel (preformula.rel R) ts))
    (himp : Π {f₁ f₂ : formula L}, C f₁ → C f₂ → C (f₁ ⟹ f₂))
    (hall : Π {f : formula L}, C f → C (∀' f)) :
    ∀ f : formula L, C f :=
  fun f => formula.rec' hfalsum hequal hrel himp hall f []

/-- Compatibility of `formula.rec'` with `apps_rel`. -/
theorem formula.rec'_apps_rel {C : formula L → Sort v}
    (hfalsum : C ⊥)
    (hequal : Π t₁ t₂ : term L, C (t₁ ≃ t₂))
    (hrel : Π {l : Nat} (R : L.relations l) (ts : dvector (term L) l),
      C (apps_rel (preformula.rel R) ts))
    (himp : Π {f₁ f₂ : formula L}, C f₁ → C f₂ → C (f₁ ⟹ f₂))
    (hall : Π {f : formula L}, C f → C (∀' f))
    {l : Nat} (f : preformula L l) (ts : dvector (term L) l) :
    @formula.rec' _ _ hfalsum hequal hrel himp hall 0 (apps_rel f ts) [] =
      @formula.rec' _ _ hfalsum hequal hrel himp hall l f ts := by
  induction ts with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [apps_rel, formula.rec', ih]

/-- Compatibility of `formula.rec` with relation application. -/
theorem formula.rec_apps_rel {C : formula L → Sort v}
    (hfalsum : C ⊥)
    (hequal : Π t₁ t₂ : term L, C (t₁ ≃ t₂))
    (hrel : Π {l : Nat} (R : L.relations l) (ts : dvector (term L) l),
      C (apps_rel (preformula.rel R) ts))
    (himp : Π {f₁ f₂ : formula L}, C f₁ → C f₂ → C (f₁ ⟹ f₂))
    (hall : Π {f : formula L}, C f → C (∀' f))
    {l : Nat} (R : L.relations l) (ts : dvector (term L) l) :
    @formula.rec _ _ hfalsum hequal hrel himp hall (apps_rel (preformula.rel R) ts) = hrel R ts := by
  dsimp [formula.rec]
  rw [formula.rec'_apps_rel]
  rfl

/-- Raise every free variable of index at least `m` in a formula by `n`. -/
@[simp] def lift_formula_at : {l : Nat} → preformula L l → Nat → Nat → preformula L l
  | _, .falsum, _, _ => .falsum
  | _, .equal t₁ t₂, n, m => .equal (t₁ ↑' n # m) (t₂ ↑' n # m)
  | _, .rel R, _, _ => .rel R
  | _, .apprel f t, n, m => .apprel (lift_formula_at f n m) (t ↑' n # m)
  | _, .imp f₁ f₂, n, m => .imp (lift_formula_at f₁ n m) (lift_formula_at f₂ n m)
  | _, .all f, n, m => .all (lift_formula_at f n (m + 1))

/-- Lift every free variable in a formula by `n`. -/
def lift_formula : {l : Nat} → preformula L l → Nat → preformula L l
  | _, f, n => lift_formula_at f n 0

/-- Lift every free variable in a formula by one. -/
def lift_formula1 : {l : Nat} → preformula L l → preformula L l
  | _, f => lift_formula f 1

/-- `lift_formula` is `lift_formula_at` specialized to `m = 0`. -/
theorem lift_formula_def {l : Nat} (f : preformula L l) (n : Nat) :
    lift_formula_at f n 0 = lift_formula f n := rfl

/-- Lifting by zero leaves a formula unchanged. -/
theorem lift_formula_at_zero : {l : Nat} → (f : preformula L l) → (m : Nat) →
    lift_formula_at f 0 m = f
  | _, .falsum, _ => rfl
  | _, .equal t₁ t₂, _ => by simp [lift_formula_at]
  | _, .rel _, _ => rfl
  | _, .apprel f t, _ => by simp [lift_formula_at, lift_formula_at_zero]
  | _, .imp f₁ f₂, _ => by simp [lift_formula_at, lift_formula_at_zero]
  | _, .all f, _ => by simp [lift_formula_at, lift_formula_at_zero]

/-- Lifting commutes with relation application. -/
theorem lift_formula_at_apps_rel {l : Nat} (f : preformula L l) (ts : dvector (term L) l)
    (n m : Nat) :
    lift_formula_at (apps_rel f ts) n m =
      apps_rel (lift_formula_at f n m) (ts.map fun x => lift_term_at x n m) := by
  induction ts with
  | nil =>
      simp [apps_rel]
  | cons t ts ih =>
      simp [apps_rel, ih, lift_formula_at]

/-- Substitute a term for variable `n` throughout a formula. -/
@[simp] def subst_formula : {l : Nat} → preformula L l → term L → Nat → preformula L l
  | _, .falsum, _, _ => .falsum
  | _, .equal t₁ t₂, s, n => .equal (t₁[s // n]) (t₂[s // n])
  | _, .rel R, _, _ => .rel R
  | _, .apprel f t, s, n => .apprel (subst_formula f s n) (t[s // n])
  | _, .imp f₁ f₂, s, n => .imp (subst_formula f₁ s n) (subst_formula f₂ s n)
  | _, .all f, s, n => .all (subst_formula f s (n + 1))

@[simp] theorem subst_formula_equal (t₁ t₂ s : term L) (n : Nat) :
    subst_formula (t₁ ≃ t₂) s n = (t₁[s // n] ≃ t₂[s // n]) := rfl

/-- Substitution commutes with relation application. -/
theorem subst_formula_apps_rel {l : Nat} (f : preformula L l) (ts : dvector (term L) l)
    (s : term L) (n : Nat) :
    subst_formula (apps_rel f ts) s n =
      apps_rel (subst_formula f s n) (ts.map fun x => subst_term x s n) := by
  induction ts with
  | nil =>
      simp [apps_rel]
  | cons t ts ih =>
      simp [apps_rel, ih, subst_formula]

/-- Commute two lifts when the second cutoff is no larger than the first. -/
theorem lift_formula_at2_small : ∀ {l : Nat} (f : preformula L l) (n n' : Nat) {m m' : Nat},
    m' ≤ m →
    lift_formula_at (lift_formula_at f n m) n' m' =
      lift_formula_at (lift_formula_at f n' m') n (m + n')
  | _, .falsum, _, _, _, _, _ => rfl
  | _, .equal t₁ t₂, n, n', m, m', h => by
      simp [lift_formula_at, lift_term_at2_small, h]
  | _, .rel R, _, _, _, _, _ => rfl
  | _, .apprel f t, n, n', m, m', h => by
      simp [lift_formula_at, lift_formula_at2_small, lift_term_at2_small, h]
  | _, .imp f₁ f₂, n, n', m, m', h => by
      simp [lift_formula_at, lift_formula_at2_small, h]
  | _, .all f, n, n', m, m', h => by
      simpa [lift_formula_at, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        lift_formula_at2_small (f := f) n n' (m := m + 1) (m' := m' + 1) (Nat.add_le_add_right h 1)

/-- A single lift can be moved past another lift by adjusting the cutoff. -/
@[simp] theorem lift_formula1_lift_formula_at {l : Nat} (f : preformula L l) (n m : Nat) :
    lift_formula_at (lift_formula_at f n m) 1 0 = lift_formula_at (lift_formula f 1) n (m + 1) := by
  simpa [lift_formula] using
    lift_formula_at2_small (f := f) n 1 (m := m) (m' := 0) (Nat.zero_le _)

/-- Substituting above the lift cutoff commutes with lifting. -/
theorem lift_at_subst_formula_large : ∀ {l : Nat} (f : preformula L l) (s : term L)
    {n₁ : Nat} (n₂ : Nat) {m : Nat}, m ≤ n₁ →
    subst_formula (lift_formula_at f n₂ m) s (n₁ + n₂) =
      lift_formula_at (subst_formula f s n₁) n₂ m
  | _, .falsum, _, _, _, _, _ => rfl
  | _, .equal t₁ t₂, s, n₁, n₂, m, h => by
      simp [lift_formula_at, subst_formula, lift_at_subst_term_large, h]
  | _, .rel R, _, _, _, _, _ => rfl
  | _, .apprel f t, s, n₁, n₂, m, h => by
      simp [lift_formula_at, subst_formula, lift_at_subst_formula_large, lift_at_subst_term_large, h]
  | _, .imp f₁ f₂, s, n₁, n₂, m, h => by
      simp [lift_formula_at, subst_formula, lift_at_subst_formula_large, h]
  | _, .all f, s, n₁, n₂, m, h => by
      simpa [lift_formula_at, subst_formula, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        lift_at_subst_formula_large (f := f) (s := s) (n₁ := n₁ + 1) n₂ (m := m + 1)
          (Nat.add_le_add_right h 1)

/-- Global lifting commutes with substitution above the lifted block. -/
theorem lift_subst_formula_large {l : Nat} (f : preformula L l) (s : term L) (n₁ n₂ : Nat) :
    subst_formula (lift_formula f n₂) s (n₁ + n₂) = lift_formula (subst_formula f s n₁) n₂ := by
  simpa [lift_formula] using
    lift_at_subst_formula_large (f := f) (s := s) (n₁ := n₁) n₂ (m := 0) (Nat.zero_le _)

/-- Commuting version of `lift_subst_formula_large` with the indices swapped. -/
theorem lift_subst_formula_large' {l : Nat} (f : preformula L l) (s : term L) (n₁ n₂ : Nat) :
    subst_formula (lift_formula f n₂) s (n₂ + n₁) = lift_formula (subst_formula f s n₁) n₂ := by
  simpa [Nat.add_comm] using lift_subst_formula_large (f := f) (s := s) n₁ n₂

@[simp] theorem lift_formula1_subst_shift {l : Nat} (f : preformula L l) (s : term L) (n : Nat) :
    subst_formula (lift_formula f 1) s (n + 1) = lift_formula (subst_formula f s n) 1 := by
  simpa [Nat.add_comm] using lift_subst_formula_large' (f := f) (s := s) n 1

/-- Substituting inside the lifted block lowers the lift amount by one. -/
theorem lift_at_subst_formula_medium : ∀ {l : Nat} (f : preformula L l) (s : term L)
    {n₁ n₂ m : Nat}, m ≤ n₂ → n₂ ≤ m + n₁ →
    subst_formula (lift_formula_at f (n₁ + 1) m) s n₂ = lift_formula_at f n₁ m
  | _, .falsum, _, _, _, _, _, _ => rfl
  | _, .equal t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
      simp [lift_formula_at, subst_formula, lift_at_subst_term_medium, h₁, h₂]
  | _, .rel R, _, _, _, _, _, _ => rfl
  | _, .apprel f t, s, n₁, n₂, m, h₁, h₂ => by
      simp [lift_formula_at, subst_formula, lift_at_subst_formula_medium, lift_at_subst_term_medium, h₁, h₂]
  | _, .imp f₁ f₂, s, n₁, n₂, m, h₁, h₂ => by
      simp [lift_formula_at, subst_formula, lift_at_subst_formula_medium, h₁, h₂]
  | _, .all f, s, n₁, n₂, m, h₁, h₂ => by
      simpa [lift_formula_at, subst_formula, Nat.add_assoc] using
        lift_at_subst_formula_medium (f := f) (s := s) (n₁ := n₁) (n₂ := n₂ + 1) (m := m + 1)
          (Nat.add_le_add_right h₁ 1) (by omega)

/-- Lifting once and substituting at the cutoff cancels out. -/
theorem lift_at_subst_formula_eq {l : Nat} (f : preformula L l) (s : term L) (n : Nat) :
    subst_formula (lift_formula_at f 1 n) s n = f := by
  simpa [lift_formula_at_zero] using
    lift_at_subst_formula_medium (f := f) (s := s) (n₁ := 0) (n₂ := n) (m := n)
    (le_rfl) (by simp)

@[simp] theorem lift_formula1_subst {l : Nat} (f : preformula L l) (s : term L) :
    subst_formula (lift_formula f 1) s 0 = f := by
  simpa [lift_formula] using lift_at_subst_formula_eq (f := f) (s := s) 0

/-- Substituting below the lift cutoff commutes with lifting the substituted term. -/
theorem lift_at_subst_formula_small : ∀ {l : Nat} (f : preformula L l) (s : term L)
    (n₁ n₂ m : Nat),
    subst_formula (lift_formula_at f n₁ (m + n₂ + 1)) (lift_term_at s n₁ m) n₂ =
      lift_formula_at (subst_formula f s n₂) n₁ (m + n₂)
  | _, .falsum, _, _, _, _ => rfl
  | _, .equal t₁ t₂, s, n₁, n₂, m => by
      simp [lift_formula_at, subst_formula, lift_at_subst_term_small]
  | _, .rel R, _, _, _, _ => rfl
  | _, .apprel f t, s, n₁, n₂, m => by
      simp [lift_formula_at, subst_formula, lift_at_subst_formula_small, lift_at_subst_term_small]
  | _, .imp f₁ f₂, s, n₁, n₂, m => by
      simp [lift_formula_at, subst_formula, lift_at_subst_formula_small]
  | _, .all f, s, n₁, n₂, m => by
      simpa [lift_formula_at, subst_formula, Nat.add_assoc] using
        lift_at_subst_formula_small (f := f) (s := s) n₁ (n₂ + 1) m

/-- Special case of `lift_at_subst_formula_small` at variable `0`. -/
@[simp] theorem lift_at_subst_formula_small0 {l : Nat} (f : preformula L l) (s : term L)
    (n₁ m : Nat) :
    subst_formula (lift_formula_at f n₁ (m + 1)) (lift_term_at s n₁ m) 0 =
      lift_formula_at (subst_formula f s 0) n₁ m := by
  simpa using lift_at_subst_formula_small (f := f) (s := s) n₁ 0 m

/-- Composition law for two substitutions into a formula. -/
theorem subst_formula2 : ∀ {l : Nat} (f : preformula L l) (s₁ s₂ : term L) (n₁ n₂ : Nat),
    subst_formula (subst_formula f s₁ n₁) s₂ (n₁ + n₂) =
      subst_formula (subst_formula f s₂ (n₁ + n₂ + 1)) (subst_term s₁ s₂ n₂) n₁
  | _, .falsum, _, _, _, _ => rfl
  | _, .equal t₁ t₂, s₁, s₂, n₁, n₂ => by
      simp [subst_formula, subst_term2]
  | _, .rel R, _, _, _, _ => rfl
  | _, .apprel f t, s₁, s₂, n₁, n₂ => by
      simp [subst_formula, subst_formula2, subst_term2]
  | _, .imp f₁ f₂, s₁, s₂, n₁, n₂ => by
      simp [subst_formula, subst_formula2]
  | _, .all f, s₁, s₂, n₁, n₂ => by
      simpa [subst_formula, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        subst_formula2 (f := f) (s₁ := s₁) (s₂ := s₂) (n₁ := n₁ + 1) (n₂ := n₂)

/-- Specialization of `subst_formula2` with the first substitution at variable `0`. -/
@[simp] theorem subst_formula2_zero {l : Nat} (f : preformula L l) (s₁ s₂ : term L) (n : Nat) :
    subst_formula (subst_formula f s₁ 0) s₂ n =
      subst_formula (subst_formula f s₂ (n + 1)) (subst_term s₁ s₂ n) 0 := by
  simpa using subst_formula2 (f := f) (s₁ := s₁) (s₂ := s₂) (n₁ := 0) (n₂ := n)

/-- Count the number of quantifiers appearing in a formula. -/
@[simp] def count_quantifiers : {l : Nat} → preformula L l → Nat
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ => 0
  | _, .apprel _ _ => 0
  | _, .imp f₁ f₂ => count_quantifiers f₁ + count_quantifiers f₂
  | _, .all f => count_quantifiers f + 1

@[simp] theorem count_quantifiers_succ {l : Nat} (f : preformula L (l + 1)) :
    count_quantifiers f = 0 := by
  cases f <;> rfl

/-- Predicate asserting that a formula contains no quantifiers. -/
def quantifier_free {l : Nat} (f : preformula L l) : Prop :=
  count_quantifiers f = 0

end fol
end Flypitch
