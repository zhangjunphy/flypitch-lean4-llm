import Mathlib
import Flypitch.Compat.Core

universe u

namespace Flypitch
namespace fol

open Nat

variable {S : Type u}

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

/-- Given a valuation `v`, replace the variable at index `n` by `x`. -/
def subst_realize (v : Nat → S) (x : S) (n k : Nat) : S :=
  if k < n then
    v k
  else if n < k then
    v (k - 1)
  else
    x

notation:95 v "[" x " // " n "]" => subst_realize v x n

@[simp] theorem subst_realize_lt (v : Nat → S) (x : S) {n k : Nat} (h : k < n) :
    subst_realize v x n k = v k := by
  simp [subst_realize, h]

@[simp] theorem subst_realize_gt (v : Nat → S) (x : S) {n k : Nat} (h : n < k) :
    subst_realize v x n k = v (k - 1) := by
  have h' : ¬k < n := Nat.not_lt_of_ge h.le
  simp [subst_realize, h, h']

@[simp] theorem subst_realize_var_eq (v : Nat → S) (x : S) (n : Nat) :
    subst_realize v x n n = x := by
  simp [subst_realize]

theorem subst_realize_congr {v v' : Nat → S} (hv : ∀ k, v k = v' k) (x : S)
    (n k : Nat) : subst_realize v x n k = subst_realize v' x n k := by
  by_cases hk : k < n
  · simp [subst_realize, hk, hv]
  · by_cases hn : n < k
    · simp [subst_realize, hk, hn, hv]
    · simp [subst_realize, hk, hn]

theorem subst_realize2_0 (v : Nat → S) (x x' : S) (n k : Nat) :
    subst_realize (subst_realize v x' n) x 0 k =
      subst_realize (subst_realize v x 0) x' (n + 1) k := by
  cases k with
  | zero =>
      simp [subst_realize]
  | succ k =>
      by_cases hlt : k < n
      · have hs : k + 1 < n + 1 := Nat.succ_lt_succ hlt
        simp [subst_realize, hlt, hs, Nat.succ_ne_zero]
      · by_cases heq : k = n
        · subst heq
          simp [subst_realize, Nat.succ_ne_zero]
        · have hgt : n < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
          have hs : n + 1 < k + 1 := Nat.succ_lt_succ hgt
          have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le n) hgt
          simp [subst_realize, hlt, hgt, hs, hkpos, Nat.succ_ne_zero]

structure Language : Type (u + 1) where
  functions : Nat → Type u
  relations : Nat → Type u

def Language.constants (L : Language) : Type u :=
  L.functions 0

variable (L : Language)

/-- `preterm L l` is a partially applied term requiring `l` more arguments. -/
inductive preterm : Nat → Type u
  | var : Nat → preterm 0
  | func : {l : Nat} → L.functions l → preterm l
  | app : {l : Nat} → preterm (l + 1) → preterm 0 → preterm l

abbrev term := preterm L 0

variable {L}

prefix:max "&" => preterm.var

@[simp] def apps : {l : Nat} → preterm L l → dvector (term L) l → term L
  | _, t, [] => t
  | _, t, x :: xs => apps (preterm.app t x) xs

@[simp] theorem apps_zero (t : term L) (ts : dvector (term L) 0) : apps t ts = t := by
  cases ts
  simp [apps]

theorem apps_eq_app {l : Nat} (t : preterm L (l + 1)) (s : term L) (ts : dvector (term L) l) :
    ∃ t' s', apps t (s :: ts) = preterm.app t' s' := by
  induction ts generalizing s with
  | nil =>
      exact ⟨t, s, by simp [apps]⟩
  | cons x xs ih =>
      simpa [apps] using ih (preterm.app t s) x

namespace preterm

@[simp] def change_arity' : {l l' : Nat} → l = l' → preterm L l → preterm L l'
  | _, _, rfl, var k => var k
  | _, _, rfl, func f => func f
  | _, _, rfl, app t₁ t₂ => app (change_arity' rfl t₁) t₂

@[simp] theorem change_arity'_rfl : (t : preterm L l) → change_arity' rfl t = t
  | var _ => rfl
  | func _ => rfl
  | app t₁ t₂ => by simp [change_arity'_rfl, change_arity']

end preterm

theorem apps_ne_var {l : Nat} {f : L.functions l} {ts : dvector (term L) l} {k : Nat} :
    apps (preterm.func f) ts ≠ &k := by
  intro h
  cases ts with
  | nil =>
      cases h
  | cons s ss =>
      obtain ⟨t', s', hs⟩ := apps_eq_app (L := L) (t := preterm.func f) (s := s) (ts := ss)
      cases hs.symm.trans h

/-- `lift_term_at t n m` raises variables in `t` at or above `m` by `n`. -/
@[simp] def lift_term_at : {l : Nat} → preterm L l → Nat → Nat → preterm L l
  | _, .var k, n, m => if m ≤ k then .var (k + n) else .var k
  | _, .func f, _, _ => .func f
  | _, .app t₁ t₂, n, m => .app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

def lift_term : {l : Nat} → preterm L l → Nat → preterm L l
  | _, t, n => lift_term_at t n 0

def lift_term1 : {l : Nat} → preterm L l → preterm L l
  | _, t => lift_term t 1

notation:90 t " ↑' " n " # " m => lift_term_at t n m
infix:100 " ↑ " => lift_term

theorem lift_term_def {l : Nat} (t : preterm L l) (n : Nat) :
    lift_term_at t n 0 = lift_term t n := rfl

@[simp] theorem lift_term_at_zero : {l : Nat} → (t : preterm L l) → (m : Nat) →
    lift_term_at t 0 m = t
  | _, .var k, m => by
      by_cases h : m ≤ k
      · simp [lift_term_at, h]
      · simp [lift_term_at, h]
  | _, .func _, _ => rfl
  | _, .app t₁ t₂, m => by
      simp [lift_term_at, lift_term_at_zero]

@[simp] theorem lift_term_at_apps {l : Nat} (t : preterm L l) (ts : dvector (term L) l)
    (n m : Nat) :
    lift_term_at (apps t ts) n m =
      apps (lift_term_at t n m) (ts.map fun x => lift_term_at x n m) := by
  induction ts with
  | nil =>
      simp [apps]
  | cons t' ts ih =>
      simp [apps, ih, lift_term_at]

/-- Substitute `s` for variable `n`, lowering higher variables by one. -/
def subst_term : {l : Nat} → preterm L l → term L → Nat → preterm L l
  | _, .var k, s, n => subst_realize preterm.var (lift_term_at s n 0) n k
  | _, .func f, _, _ => .func f
  | _, .app t₁ t₂, s, n => .app (subst_term t₁ s n) (subst_term t₂ s n)

notation:95 t "[" s " // " n "]" => subst_term t s n

@[simp] theorem subst_term_var_lt (s : term L) {k n : Nat} (h : k < n) :
    subst_term (&k : term L) s n = (&k : term L) := by
  simp [subst_term, subst_realize_lt, h]

@[simp] theorem subst_term_var_gt (s : term L) {k n : Nat} (h : n < k) :
    subst_term (&k : term L) s n = (&(k - 1) : term L) := by
  simp [subst_term, subst_realize_gt, h]

@[simp] theorem subst_term_var_eq (s : term L) (n : Nat) :
    subst_term (&n : term L) s n = lift_term_at s n 0 := by
  simp [subst_term, subst_realize_var_eq]

@[simp] theorem subst_term_apps {l : Nat} (t : preterm L l) (ts : dvector (term L) l) (s : term L)
    (n : Nat) :
    subst_term (apps t ts) s n = apps (subst_term t s n) (ts.map fun x => subst_term x s n) := by
  induction ts with
  | nil =>
      simp [apps]
  | cons t' ts ih =>
      simp [apps, subst_term, ih]

@[simp] theorem lift_term1_lift_term_at {l : Nat} (t : preterm L l) (n m : Nat) :
    (t ↑' n # m) ↑ 1 = (t ↑ 1) ↑' n # (m + 1) := by
  induction t with
  | var k =>
      by_cases h : m ≤ k
      · have hk : m + 1 ≤ k + 1 := Nat.succ_le_succ h
        simp [lift_term, lift_term_at, h, hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have hk : ¬m + 1 ≤ k + 1 := by
          intro hk
          exact h (Nat.succ_le_succ_iff.mp hk)
        simp [lift_term, lift_term_at, h, hk]
  | func f =>
      rfl
  | app t₁ t₂ ih₁ ih₂ =>
      change preterm.app (((t₁ ↑' n # m) ↑ 1)) (((t₂ ↑' n # m) ↑ 1)) =
        preterm.app (((t₁ ↑ 1) ↑' n # (m + 1))) (((t₂ ↑ 1) ↑' n # (m + 1)))
      rw [ih₁, ih₂]

@[simp] theorem lift_term_succ {l : Nat} (t : preterm L l) (n : Nat) :
    (t ↑ n) ↑ 1 = t ↑ (n + 1) := by
  induction t with
  | var k =>
      simp [lift_term, lift_term_at, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | func f =>
      rfl
  | app t₁ t₂ ih₁ ih₂ =>
      change preterm.app (((t₁ ↑ n) ↑ 1)) (((t₂ ↑ n) ↑ 1)) =
        preterm.app (t₁ ↑ (n + 1)) (t₂ ↑ (n + 1))
      rw [ih₁, ih₂]

@[simp] theorem lift_term_zero {l : Nat} (t : preterm L l) : t ↑ 0 = t := by
  induction t with
  | var k =>
      simp [lift_term, lift_term_at]
  | func f =>
      rfl
  | app t₁ t₂ ih₁ ih₂ =>
      simp [lift_term, lift_term_at, ih₁, ih₂]

theorem lift_term_at2_small : ∀ {l : Nat} (t : preterm L l) (n n' : Nat) {m m' : Nat}, m' ≤ m →
    lift_term_at (lift_term_at t n m) n' m' = lift_term_at (lift_term_at t n' m') n (m + n')
  | _, &k, n, n', m, m', h => by
      by_cases hmk : m ≤ k
      · have hm'k : m' ≤ k := le_trans h hmk
        have hm'kn : m' ≤ k + n := le_trans hm'k (Nat.le_add_right k n)
        simp [lift_term_at, hmk, hm'k, hm'kn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        omega
      · by_cases hm'k : m' ≤ k
        · have hfalse : ¬m + n' ≤ k + n' := by
            intro hk
            exact hmk (Nat.le_of_add_le_add_right hk)
          have hfalse' : ¬m + n' ≤ k := by
            intro hk
            exact hfalse (le_trans hk (Nat.le_add_right k n'))
          simp [lift_term_at, hmk, hm'k, hfalse, hfalse', Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
          omega
        · simp [lift_term_at, hmk, hm'k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          omega
  | _, .func f, n, n', m, m', h => rfl
  | _, .app t₁ t₂, n, n', m, m', h => by
      change preterm.app (lift_term_at (lift_term_at t₁ n m) n' m') (lift_term_at (lift_term_at t₂ n m) n' m') =
        preterm.app (lift_term_at (lift_term_at t₁ n' m') n (m + n')) (lift_term_at (lift_term_at t₂ n' m') n (m + n'))
      rw [lift_term_at2_small t₁ n n' h, lift_term_at2_small t₂ n n' h]

theorem lift_term_at2_medium : ∀ {l : Nat} (t : preterm L l) {n : Nat} (n' : Nat)
    {m m' : Nat}, m ≤ m' → m' ≤ m + n →
    lift_term_at (lift_term_at t n m) n' m' = lift_term_at t (n + n') m
  | _, &k, n, n', m, m', h₁, h₂ => by
      by_cases h : m ≤ k
      · have h₁' : m' ≤ k + n := le_trans h₂ (Nat.add_le_add_right h n)
        simp [lift_term_at, h, h₁', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have h₁' : ¬m' ≤ k := by
          intro hk
          exact h (le_trans h₁ hk)
        simp [lift_term_at, h, h₁', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | _, .func f, n, n', m, m', h₁, h₂ => rfl
  | _, .app t₁ t₂, n, n', m, m', h₁, h₂ => by
      change preterm.app (lift_term_at (lift_term_at t₁ n m) n' m') (lift_term_at (lift_term_at t₂ n m) n' m') =
        preterm.app (lift_term_at t₁ (n + n') m) (lift_term_at t₂ (n + n') m)
      rw [lift_term_at2_medium t₁ n' h₁ h₂, lift_term_at2_medium t₂ n' h₁ h₂]

theorem lift_term2_medium {l : Nat} (t : preterm L l) {n : Nat} (n' : Nat) {m' : Nat}
    (h : m' ≤ n) : lift_term_at (lift_term t n) n' m' = lift_term t (n + n') := by
  simpa [lift_term] using lift_term_at2_medium (t := t) (n := n) n' (m := 0) (m' := m')
    (Nat.zero_le _) (by simpa using h)

theorem lift_term2 {l : Nat} (t : preterm L l) (n n' : Nat) :
    lift_term (lift_term t n) n' = lift_term t (n + n') := by
  simpa [lift_term] using lift_term2_medium (t := t) (n := n) n' (m' := 0) (Nat.zero_le _)

theorem lift_term_at2_eq {l : Nat} (t : preterm L l) (n n' m : Nat) :
    lift_term_at (lift_term_at t n m) n' (m + n) = lift_term_at t (n + n') m := by
  simpa using lift_term_at2_medium (t := t) (n := n) n' (m := m) (m' := m + n)
    (Nat.le_add_right m n) (le_rfl)

theorem lift_term_at2_large {l : Nat} (t : preterm L l) {n : Nat} (n' : Nat)
    {m m' : Nat} (h : m + n ≤ m') :
    lift_term_at (lift_term_at t n m) n' m' = lift_term_at (lift_term_at t n' (m' - n)) n m := by
  have hn : n ≤ m' := le_trans (Nat.le_add_left n m) h
  have hm : m ≤ m' - n := Nat.le_sub_of_add_le h
  rw [lift_term_at2_small (t := t) (n := n') (n' := n) (m := m' - n) (m' := m) hm]
  simpa [Nat.sub_add_cancel hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem lift_at_subst_term_large : ∀ {l : Nat} (t : preterm L l) (s : term L) {n₁ : Nat}
    (n₂ : Nat) {m : Nat}, m ≤ n₁ →
    (t ↑' n₂ # m)[s // (n₁ + n₂)] = (t[s // n₁]) ↑' n₂ # m
  | _, &k, s, n₁, n₂, m, h => by
      by_cases hlt : k < n₁
      · by_cases hm : m ≤ k
        · have hkLift : ((&k : term L) ↑' n₂ # m) = (&(k + n₂) : term L) := by
            simp [lift_term_at, hm]
          have hkSub : ((&(k + n₂) : term L)[s // (n₁ + n₂)]) = (&(k + n₂) : term L) := by
            simpa using (subst_term_var_lt (L := L) (s := s) (k := k + n₂) (n := n₁ + n₂) (by omega))
          have hkBase : ((&k : term L)[s // n₁]) = (&k : term L) := by
            simpa using (subst_term_var_lt (L := L) (s := s) (k := k) (n := n₁) hlt)
          rw [hkLift, hkSub, hkBase]
          simp [lift_term_at, hm]
        · have hkNoLift : ((&k : term L) ↑' n₂ # m) = (&k : term L) := by
            simp [lift_term_at, hm]
          have hkSub : ((&k : term L)[s // (n₁ + n₂)]) = (&k : term L) := by
            simpa using (subst_term_var_lt (L := L) (s := s) (k := k) (n := n₁ + n₂) (by omega))
          have hkBase : ((&k : term L)[s // n₁]) = (&k : term L) := by
            simpa using (subst_term_var_lt (L := L) (s := s) (k := k) (n := n₁) hlt)
          rw [hkNoLift, hkSub, hkBase]
          simp [lift_term_at, hm]
      · by_cases heq : k = n₁
        · subst k
          have hkL : ((&n₁ : term L) ↑' n₂ # m)[s // (n₁ + n₂)] = s ↑ (n₁ + n₂) := by
            simp [lift_term_at, subst_term, subst_realize_var_eq, lift_term, h]
          have hkR : (((&n₁ : term L)[s // n₁]) ↑' n₂ # m) = lift_term_at (lift_term s n₁) n₂ m := by
            simp [subst_term, subst_realize_var_eq, lift_term]
          rw [hkL, hkR]
          simpa [lift_term] using (lift_term2_medium (t := s) (n := n₁) n₂ (m' := m) h).symm
        · have hgt : n₁ < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
          have hm : m ≤ k := le_trans h (Nat.le_of_lt hgt)
          have hsub : n₁ + n₂ < k + n₂ := Nat.add_lt_add_right hgt n₂
          have hm' : m ≤ k - 1 := by omega
          have hkLift : ((&k : term L) ↑' n₂ # m) = (&(k + n₂) : term L) := by
            simp [lift_term_at, hm]
          have hkSub : ((&(k + n₂) : term L)[s // (n₁ + n₂)]) = (&(k + n₂ - 1) : term L) := by
            simpa using (subst_term_var_gt (L := L) (s := s) (k := k + n₂) (n := n₁ + n₂) hsub)
          have hkBase : ((&k : term L)[s // n₁]) = (&(k - 1) : term L) := by
            simpa using (subst_term_var_gt (L := L) (s := s) (k := k) (n := n₁) hgt)
          have hkLift2 : ((&(k - 1) : term L) ↑' n₂ # m) = (&((k - 1) + n₂) : term L) := by
            simp [lift_term_at, hm']
          rw [hkLift, hkSub, hkBase, hkLift2]
          congr
          omega
  | _, .func f, s, n₁, n₂, m, h => rfl
  | _, .app t₁ t₂, s, n₁, n₂, m, h => by
      change preterm.app ((t₁ ↑' n₂ # m)[s // (n₁ + n₂)]) ((t₂ ↑' n₂ # m)[s // (n₁ + n₂)]) =
        preterm.app ((t₁[s // n₁]) ↑' n₂ # m) ((t₂[s // n₁]) ↑' n₂ # m)
      rw [lift_at_subst_term_large t₁ s n₂ h, lift_at_subst_term_large t₂ s n₂ h]

theorem lift_subst_term_large {l : Nat} (t : preterm L l) (s : term L) (n₁ n₂ : Nat) :
    (t ↑ n₂)[s // (n₁ + n₂)] = (t[s // n₁]) ↑ n₂ := by
  simpa [lift_term] using lift_at_subst_term_large (t := t) (s := s) (n₁ := n₁) n₂ (m := 0) (Nat.zero_le _)

theorem lift_subst_term_large' {l : Nat} (t : preterm L l) (s : term L) (n₁ n₂ : Nat) :
    (t ↑ n₂)[s // (n₂ + n₁)] = (t[s // n₁]) ↑ n₂ := by
  simpa [Nat.add_comm] using lift_subst_term_large (t := t) (s := s) n₁ n₂

theorem lift_at_subst_term_medium : ∀ {l : Nat} (t : preterm L l) (s : term L)
    {n₁ n₂ m : Nat}, m ≤ n₂ → n₂ ≤ m + n₁ →
    (t ↑' (n₁ + 1) # m)[s // n₂] = t ↑' n₁ # m
  | _, &k, s, n₁, n₂, m, h₁, h₂ => by
      by_cases hm : m ≤ k
      · have hbound : n₂ < k + (n₁ + 1) := by omega
        have hkLift : ((&k : term L) ↑' (n₁ + 1) # m) = (&(k + (n₁ + 1)) : term L) := by
          simp [lift_term_at, hm]
        have hkSub : ((&(k + (n₁ + 1)) : term L)[s // n₂]) = (&(k + n₁) : term L) := by
          simpa using (subst_term_var_gt (L := L) (s := s) (k := k + (n₁ + 1)) (n := n₂) hbound)
        have hkR : ((&k : term L) ↑' n₁ # m) = (&(k + n₁) : term L) := by
          simp [lift_term_at, hm]
        rw [hkLift, hkSub, hkR]
      · have hlt : k < n₂ := lt_of_lt_of_le (lt_of_not_ge hm) h₁
        have hkLift : ((&k : term L) ↑' (n₁ + 1) # m) = (&k : term L) := by
          simp [lift_term_at, hm]
        have hkSub : ((&k : term L)[s // n₂]) = (&k : term L) := by
          simpa using (subst_term_var_lt (L := L) (s := s) (k := k) (n := n₂) hlt)
        have hkR : ((&k : term L) ↑' n₁ # m) = (&k : term L) := by
          simp [lift_term_at, hm]
        rw [hkLift, hkSub, hkR]
  | _, .func f, s, n₁, n₂, m, h₁, h₂ => rfl
  | _, .app t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
      change preterm.app ((t₁ ↑' (n₁ + 1) # m)[s // n₂]) ((t₂ ↑' (n₁ + 1) # m)[s // n₂]) =
        preterm.app (t₁ ↑' n₁ # m) (t₂ ↑' n₁ # m)
      rw [lift_at_subst_term_medium t₁ s h₁ h₂, lift_at_subst_term_medium t₂ s h₁ h₂]

theorem lift_subst_term_medium {l : Nat} (t : preterm L l) (s : term L) (n₁ n₂ : Nat) :
    (t ↑ ((n₁ + n₂) + 1))[s // n₁] = t ↑ (n₁ + n₂) := by
  simpa [lift_term] using
    (lift_at_subst_term_medium (t := t) (s := s) (n₁ := n₁ + n₂) (n₂ := n₁) (m := 0)
      (Nat.zero_le _) (by omega))

theorem lift_at_subst_term_eq {l : Nat} (t : preterm L l) (s : term L) (n : Nat) :
    (t ↑' 1 # n)[s // n] = t := by
  simpa using lift_at_subst_term_medium (t := t) (s := s) (n₁ := 0) (n₂ := n) (m := n)
    (le_rfl) (by simp)

theorem subst_term2 : ∀ {l : Nat} (t : preterm L l) (s₁ s₂ : term L) (n₁ n₂ : Nat),
    t[s₁ // n₁][s₂ // (n₁ + n₂)] = t[s₂ // (n₁ + n₂ + 1)][s₁[s₂ // n₂] // n₁]
  | _, &k, s₁, s₂, n₁, n₂ => by
      by_cases hlt : k < n₁
      · have hk1 : k < n₁ + n₂ := lt_of_lt_of_le hlt (Nat.le_add_right _ _)
        have hk2 : k < n₁ + n₂ + 1 := lt_of_lt_of_le hk1 (Nat.le_succ _)
        simp [subst_term, subst_realize_lt, hlt, hk1, hk2]
      · by_cases heq : k = n₁
        · subst k
          have hL :
              ((&n₁ : term L)[s₁ // n₁][s₂ // (n₁ + n₂)]) = (s₁[s₂ // n₂]) ↑ n₁ := by
            simpa [lift_term, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (lift_subst_term_large' (t := s₁) (s := s₂) n₂ n₁)
          have hlt : n₁ < n₁ + n₂ + 1 := by omega
          have hR :
              ((&n₁ : term L)[s₂ // (n₁ + n₂ + 1)][s₁[s₂ // n₂] // n₁]) = (s₁[s₂ // n₂]) ↑ n₁ := by
            rw [subst_term_var_lt (L := L) (s := s₂) (k := n₁) (n := n₁ + n₂ + 1) hlt]
            simp [subst_term, subst_realize_var_eq, lift_term]
          rw [hL, hR]
        · by_cases hmid : k < n₁ + n₂ + 1
          · have hkLeft1 : ((&k : term L)[s₁ // n₁]) = (&(k - 1) : term L) := by
              simpa using
                (subst_term_var_gt (L := L) (s := s₁) (k := k) (n := n₁)
                  (lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)))
            have hkLeft2 : ((&(k - 1) : term L)[s₂ // (n₁ + n₂)]) = (&(k - 1) : term L) := by
              have hk : k - 1 < n₁ + n₂ := by omega
              simpa using (subst_term_var_lt (L := L) (s := s₂) (k := k - 1) (n := n₁ + n₂) hk)
            have hkRight1 : ((&k : term L)[s₂ // (n₁ + n₂ + 1)]) = (&k : term L) := by
              simpa using (subst_term_var_lt (L := L) (s := s₂) (k := k) (n := n₁ + n₂ + 1) hmid)
            have hkRight2 : ((&k : term L)[s₁[s₂ // n₂] // n₁]) = (&(k - 1) : term L) := by
              have hk : n₁ < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
              simpa using (subst_term_var_gt (L := L) (s := s₁[s₂ // n₂]) (k := k) (n := n₁) hk)
            rw [hkLeft1, hkLeft2, hkRight1, hkRight2]
          · by_cases heq2 : k = n₁ + n₂ + 1
            · subst k
              have hkL1 : ((&(n₁ + n₂ + 1) : term L)[s₁ // n₁]) = (&(n₁ + n₂) : term L) := by
                simpa using
                  (subst_term_var_gt (L := L) (s := s₁) (k := n₁ + n₂ + 1) (n := n₁) (by omega))
              have hkL2 : ((&(n₁ + n₂) : term L)[s₂ // (n₁ + n₂)]) = s₂ ↑ (n₁ + n₂) := by
                simp [subst_term, subst_realize_var_eq, lift_term]
              have hkR1 : ((&(n₁ + n₂ + 1) : term L)[s₂ // (n₁ + n₂ + 1)]) = s₂ ↑ (n₁ + n₂ + 1) := by
                simp [subst_term, subst_realize_var_eq, lift_term]
              rw [hkL1, hkL2, hkR1]
              exact (lift_subst_term_medium (t := s₂) (s := s₁[s₂ // n₂]) n₁ n₂).symm
            · have hgt : n₁ + n₂ + 1 < k := lt_of_le_of_ne (Nat.le_of_not_gt hmid) (Ne.symm heq2)
              have hk1 : n₁ < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
              have hk2 : n₁ + n₂ < k - 1 := by omega
              have hk3 : n₁ < k - 1 := by omega
              have hkLeft1 : ((&k : term L)[s₁ // n₁]) = (&(k - 1) : term L) := by
                simpa using (subst_term_var_gt (L := L) (s := s₁) (k := k) (n := n₁) hk1)
              have hkLeft2 : ((&(k - 1) : term L)[s₂ // (n₁ + n₂)]) = (&(k - 2) : term L) := by
                simpa using
                  (subst_term_var_gt (L := L) (s := s₂) (k := k - 1) (n := n₁ + n₂) hk2)
              have hkRight1 : ((&k : term L)[s₂ // (n₁ + n₂ + 1)]) = (&(k - 1) : term L) := by
                simpa using
                  (subst_term_var_gt (L := L) (s := s₂) (k := k) (n := n₁ + n₂ + 1) hgt)
              have hkRight2 : ((&(k - 1) : term L)[s₁[s₂ // n₂] // n₁]) = (&(k - 2) : term L) := by
                simpa using
                  (subst_term_var_gt (L := L) (s := s₁[s₂ // n₂]) (k := k - 1) (n := n₁) hk3)
              rw [hkLeft1, hkLeft2, hkRight1, hkRight2]
  | _, .func f, s₁, s₂, n₁, n₂ => rfl
  | _, .app t₁ t₂, s₁, s₂, n₁, n₂ => by
      change preterm.app (t₁[s₁ // n₁][s₂ // (n₁ + n₂)]) (t₂[s₁ // n₁][s₂ // (n₁ + n₂)]) =
        preterm.app (t₁[s₂ // (n₁ + n₂ + 1)][s₁[s₂ // n₂] // n₁])
          (t₂[s₂ // (n₁ + n₂ + 1)][s₁[s₂ // n₂] // n₁])
      rw [subst_term2 t₁ s₁ s₂ n₁ n₂, subst_term2 t₂ s₁ s₂ n₁ n₂]

@[simp] theorem lift_term1_subst_shift {l : Nat} (t : preterm L l) (s : term L) (n : Nat) :
    (t ↑ 1)[s // (n + 1)] = (t[s // n]) ↑ 1 := by
  induction t with
  | var k =>
      by_cases hlt : k < n
      · have hlt' : k + 1 < n + 1 := Nat.succ_lt_succ hlt
        simp [lift_term, lift_term_at, subst_term, subst_realize_lt, hlt, hlt']
      · by_cases heq : k = n
        · subst heq
          simpa [subst_term, subst_realize_var_eq, lift_term, lift_term_at] using
            (lift_term_succ (t := s) (n := k)).symm
        · have hgt : n < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
          have hgt' : n + 1 < k + 1 := Nat.succ_lt_succ hgt
          have hk : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ n) (Nat.succ_le_of_lt hgt)
          simp [lift_term, lift_term_at, subst_term, subst_realize_gt, hgt, hgt']
          omega
  | func f =>
      rfl
  | app t₁ t₂ ih₁ ih₂ =>
      change preterm.app ((t₁ ↑ 1)[s // (n + 1)]) ((t₂ ↑ 1)[s // (n + 1)]) =
        preterm.app ((t₁[s // n]) ↑ 1) ((t₂[s // n]) ↑ 1)
      rw [ih₁, ih₂]

@[simp] theorem lift_term1_subst_term {l : Nat} (t : preterm L l) (s : term L) :
    (t ↑ 1)[s // 0] = t := by
  induction t with
  | var k =>
      simpa [lift_term, lift_term_at] using
        (subst_term_var_gt (L := L) (s := s) (k := k + 1) (n := 0) (Nat.succ_pos k))
  | func f =>
      rfl
  | app t₁ t₂ ih₁ ih₂ =>
      change preterm.app ((t₁ ↑ 1)[s // 0]) ((t₂ ↑ 1)[s // 0]) = preterm.app t₁ t₂
      rw [ih₁, ih₂]

@[simp] theorem lift_at_subst_term_small0 {l : Nat} (t : preterm L l) (s : term L) (n m : Nat) :
    (t ↑' n # (m + 1))[s ↑' n # m // 0] = (t[s // 0]) ↑' n # m := by
  induction t with
  | var k =>
      by_cases hmk : m + 1 ≤ k
      · have hk : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ m) hmk
        have hkn : 0 < k + n := lt_of_lt_of_le hk (Nat.le_add_right k n)
        have hm' : m ≤ k - 1 := Nat.le_sub_of_add_le hmk
        have hkLift : ((&k : term L) ↑' n # (m + 1)) = (&(k + n) : term L) := by
          simp [lift_term_at, hmk]
        have hk1 : ((&(k + n) : term L)[s ↑' n # m // 0]) = (&(k + n - 1) : term L) := by
          simpa using
            (subst_term_var_gt (L := L) (s := s ↑' n # m) (k := k + n) (n := 0) hkn)
        have hk2 : ((&(k - 1) : term L) ↑' n # m) = (&((k - 1) + n) : term L) := by
          simp [lift_term_at, hm']
        rw [hkLift]
        rw [show (&k : term L)[s // 0] = (&(k - 1) : term L) by
              simpa using (subst_term_var_gt (L := L) (s := s) (k := k) (n := 0) hk)]
        rw [hk1, hk2]
        congr
        omega
      · by_cases hk0 : k = 0
        · subst hk0
          simp [lift_term, lift_term_at, subst_term, subst_realize_var_eq]
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hkm : k ≤ m := Nat.lt_succ_iff.mp (lt_of_not_ge hmk)
          have hpred : k - 1 < m := lt_of_lt_of_le (Nat.pred_lt hk0) hkm
          simp [lift_term, lift_term_at, subst_term, subst_realize_gt, hkpos, hmk,
            Nat.not_le_of_gt hpred]
  | func f =>
      rfl
  | app t₁ t₂ ih₁ ih₂ =>
      change preterm.app ((t₁ ↑' n # (m + 1))[s ↑' n # m // 0]) ((t₂ ↑' n # (m + 1))[s ↑' n # m // 0]) =
        preterm.app ((t₁[s // 0]) ↑' n # m) ((t₂[s // 0]) ↑' n # m)
      rw [ih₁, ih₂]

theorem lift_at_subst_term_small : ∀ {l : Nat} (t : preterm L l) (s : term L) (n₁ n₂ m : Nat),
    (t ↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m // n₂] = (t[s // n₂]) ↑' n₁ # (m + n₂)
  | _, &k, s, n₁, n₂, m => by
      by_cases hbig : m + n₂ + 1 ≤ k
      · have hn₂k : n₂ < k := lt_of_le_of_lt (Nat.le_add_left n₂ m) (lt_of_lt_of_le (Nat.lt_succ_self _) hbig)
        have hkn : n₂ < k + n₁ := lt_of_lt_of_le hn₂k (Nat.le_add_right k n₁)
        have hm : m + n₂ ≤ k - 1 := Nat.le_sub_of_add_le hbig
        have hk : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ _) hbig
        have hkLift : ((&k : term L) ↑' n₁ # (m + n₂ + 1)) = (&(k + n₁) : term L) := by
          simp [lift_term_at, hbig]
        have hkSub : ((&(k + n₁) : term L)[s ↑' n₁ # m // n₂]) = (&(k + n₁ - 1) : term L) := by
          simpa using (subst_term_var_gt (L := L) (s := s ↑' n₁ # m) (k := k + n₁) (n := n₂) hkn)
        have hkBase : ((&k : term L)[s // n₂]) = (&(k - 1) : term L) := by
          simpa using (subst_term_var_gt (L := L) (s := s) (k := k) (n := n₂) hn₂k)
        have hkLift2 : ((&(k - 1) : term L) ↑' n₁ # (m + n₂)) = (&((k - 1) + n₁) : term L) := by
          simp [lift_term_at, hm]
        rw [hkLift, hkSub, hkBase, hkLift2]
        congr
        omega
      · by_cases hlt : k < n₂
        · have hkNoLift : ((&k : term L) ↑' n₁ # (m + n₂ + 1)) = (&k : term L) := by
            have : k < m + n₂ + 1 := lt_of_not_ge hbig
            simp [lift_term_at, Nat.not_le_of_gt this]
          have hkSub : ((&k : term L)[s ↑' n₁ # m // n₂]) = (&k : term L) := by
            simpa using (subst_term_var_lt (L := L) (s := s ↑' n₁ # m) (k := k) (n := n₂) hlt)
          have hkBase : ((&k : term L)[s // n₂]) = (&k : term L) := by
            simpa using (subst_term_var_lt (L := L) (s := s) (k := k) (n := n₂) hlt)
          have hkNoLift2 : ((&k : term L) ↑' n₁ # (m + n₂)) = (&k : term L) := by
            have : k < m + n₂ := lt_of_lt_of_le hlt (Nat.le_add_left n₂ m)
            simp [lift_term_at, Nat.not_le_of_gt this]
          rw [hkNoLift, hkSub, hkBase, hkNoLift2]
        · by_cases heq : k = n₂
          · subst k
            have hkNoLift : ((&n₂ : term L) ↑' n₁ # (m + n₂ + 1)) = (&n₂ : term L) := by
              have : n₂ < m + n₂ + 1 := by omega
              simp [lift_term_at, Nat.not_le_of_gt this]
            have hkSub : ((&n₂ : term L)[s ↑' n₁ # m // n₂]) = (s ↑' n₁ # m) ↑ n₂ := by
              simp [subst_term, subst_realize_var_eq, lift_term]
            have hkBase : ((&n₂ : term L)[s // n₂]) = s ↑ n₂ := by
              simp [subst_term, subst_realize_var_eq, lift_term]
            rw [hkNoLift, hkSub, hkBase]
            simpa [lift_term, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (lift_term_at2_small (t := s) (n := n₁) (n' := n₂) (m := m) (m' := 0) (Nat.zero_le m))
          · have hgt : n₂ < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
            have hkNoLift : ((&k : term L) ↑' n₁ # (m + n₂ + 1)) = (&k : term L) := by
              have : k < m + n₂ + 1 := lt_of_not_ge hbig
              simp [lift_term_at, Nat.not_le_of_gt this]
            have hkSub : ((&k : term L)[s ↑' n₁ # m // n₂]) = (&(k - 1) : term L) := by
              simpa using (subst_term_var_gt (L := L) (s := s ↑' n₁ # m) (k := k) (n := n₂) hgt)
            have hkBase : ((&k : term L)[s // n₂]) = (&(k - 1) : term L) := by
              simpa using (subst_term_var_gt (L := L) (s := s) (k := k) (n := n₂) hgt)
            have hkNoLift2 : ((&(k - 1) : term L) ↑' n₁ # (m + n₂)) = (&(k - 1) : term L) := by
              have : k - 1 < m + n₂ := by omega
              simp [lift_term_at, Nat.not_le_of_gt this]
            rw [hkNoLift, hkSub, hkBase, hkNoLift2]
  | _, .func f, s, n₁, n₂, m => rfl
  | _, .app t₁ t₂, s, n₁, n₂, m => by
      change preterm.app ((t₁ ↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m // n₂])
          ((t₂ ↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m // n₂]) =
        preterm.app ((t₁[s // n₂]) ↑' n₁ # (m + n₂)) ((t₂[s // n₂]) ↑' n₁ # (m + n₂))
      rw [lift_at_subst_term_small t₁ s n₁ n₂ m, lift_at_subst_term_small t₂ s n₁ n₂ m]

@[simp] theorem subst_term2_zero {l : Nat} (t : preterm L l) (s₁ s₂ : term L) (n : Nat) :
    t[s₁ // 0][s₂ // n] = t[s₂ // (n + 1)][s₁[s₂ // n] // 0] := by
  induction t with
  | var k =>
      by_cases hk0 : k = 0
      · subst hk0
        have hlt : 0 < n + 1 := Nat.zero_lt_succ n
        simp [subst_term, subst_realize_var_eq, subst_realize_lt, hlt, lift_term_zero]
      · by_cases hlt : k < n + 1
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hpred : k - 1 < n := by
            omega
          simp [subst_term, subst_realize_gt, subst_realize_lt, hkpos, hlt, hpred]
        · have hge : n + 1 ≤ k := Nat.le_of_not_gt hlt
          by_cases heq : k = n + 1
          · subst heq
            have hkL : ((&(n + 1) : term L)[s₁ // 0][s₂ // n]) = s₂ ↑ n := by
              simp [subst_term, subst_realize_var_eq, lift_term]
            have hkR : ((&(n + 1) : term L)[s₂ // (n + 1)][s₁[s₂ // n] // 0]) =
                (s₂ ↑ (n + 1))[s₁[s₂ // n] // 0] := by
              simp [subst_term, subst_realize_var_eq, lift_term]
            rw [hkL, hkR]
            rw [← lift_term_succ (t := s₂) (n := n)]
            simpa using (lift_term1_subst_term (t := s₂ ↑ n) (s := s₁[s₂ // n])).symm
          · have hgt : n + 1 < k := lt_of_le_of_ne hge (Ne.symm heq)
            have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
            have hkpred : 0 < k - 1 := by
              omega
            have hgt' : n < k - 1 := by
              omega
            simp [subst_term, subst_realize_gt, hkpos, hkpred, hgt, hgt',
              Nat.succ_pred_eq_of_pos hkpos, Nat.succ_pred_eq_of_pos hkpred]
  | func f =>
      rfl
  | app t₁ t₂ ih₁ ih₂ =>
      change preterm.app (t₁[s₁ // 0][s₂ // n]) (t₂[s₁ // 0][s₂ // n]) =
        preterm.app (t₁[s₂ // (n + 1)][s₁[s₂ // n] // 0]) (t₂[s₂ // (n + 1)][s₁[s₂ // n] // 0])
      rw [ih₁, ih₂]


end fol
end Flypitch
