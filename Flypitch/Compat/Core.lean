import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

universe u v w

namespace Flypitch

theorem Function.Injective.ne_iff {α β : Sort _} {f : α → β} (hf : Function.Injective f)
    {a₁ a₂ : α} : f a₁ ≠ f a₂ ↔ a₁ ≠ a₂ :=
  not_congr hf.eq_iff

inductive dvector (α : Type u) : Nat → Type u
  | nil : dvector α 0
  | cons : {n : Nat} → α → dvector α n → dvector α (n + 1)

inductive dfin : Nat → Type
  | fz : {n : Nat} → dfin (n + 1)
  | fs : {n : Nat} → dfin n → dfin (n + 1)

instance {n : Nat} : OfNat (dfin (n + 1)) (nat_lit 0) where
  ofNat := dfin.fz

namespace dvector

variable {α : Type u} {β : Type v} {γ : Type w} {n : Nat}

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

@[simp] theorem zero_eq : (xs : dvector α 0) → xs = []
  | [] => rfl

@[simp] def concat : {n : Nat} → dvector α n → α → dvector α (n + 1)
  | _, [], x => x :: []
  | _, y :: ys, x => y :: concat ys x

@[simp] def nth : {n : Nat} → (xs : dvector α n) → (m : Nat) → m < n → α
  | _, [], m, h => False.elim (Nat.not_lt_zero m h)
  | _, x :: _, 0, _ => x
  | _, _ :: xs, m + 1, h => nth xs m (Nat.lt_of_succ_lt_succ h)

@[simp] theorem nth_cons (x : α) (xs : dvector α n) (m : Nat) (h : m < n) :
    nth (x :: xs) (m + 1) (Nat.succ_lt_succ h) = nth xs m h := by
  simp [nth]

@[reducible, simp] def last (xs : dvector α (n + 1)) : α :=
  nth xs n (Nat.lt_succ_self n)

def nth' (xs : dvector α n) (m : Fin n) : α :=
  nth xs m.1 m.2

def nth'' : {n : Nat} → dvector α n → dfin n → α
  | _, x :: _, .fz => x
  | _, _ :: xs, .fs m => nth'' xs m

def mem (x : α) : {n : Nat} → dvector α n → Prop
  | _, [] => False
  | _, y :: ys => x = y ∨ mem x ys

instance : Membership α (dvector α n) where
  mem xs x := mem x xs

def pmem (x : α) : {n : Nat} → dvector α n → Type _
  | _, [] => Empty
  | _, y :: ys => PSum (x = y) (pmem x ys)

theorem mem_of_pmem {x : α} : {n : Nat} → {xs : dvector α n} → xs.pmem x → x ∈ xs
  | _, [], h => nomatch h
  | _, _ :: _, h =>
      match h with
      | PSum.inl h' => Or.inl h'
      | PSum.inr h' => Or.inr (mem_of_pmem h')

@[simp] def map (f : α → β) : {n : Nat} → dvector α n → dvector β n
  | _, [] => []
  | _, x :: xs => f x :: map f xs

@[simp] theorem map_congr_pmem {f g : α → β} :
    {n : Nat} → {xs : dvector α n} →
      (h : ∀ x, xs.pmem x → f x = g x) → xs.map f = xs.map g
  | _, [], _ => rfl
  | _, x :: xs, h => by
      have hs : xs.map f = xs.map g := map_congr_pmem (xs := xs) (fun y hy => h y (PSum.inr hy))
      simp [map, hs, h x (PSum.inl rfl)]

@[simp] theorem map_congr_mem {f g : α → β} {n : Nat} {xs : dvector α n}
    (h : ∀ x, x ∈ xs → f x = g x) : xs.map f = xs.map g :=
  map_congr_pmem (xs := xs) (fun x hx => h x (mem_of_pmem hx))

@[simp] theorem map_id : {n : Nat} → (xs : dvector α n) → xs.map (fun x => x) = xs
  | _, [] => rfl
  | _, _ :: _ => by simp [map_id]

@[simp] theorem map_map (g : β → γ) (f : α → β) :
    {n : Nat} → (xs : dvector α n) → (xs.map f).map g = xs.map (fun x => g (f x))
  | _, [] => rfl
  | _, _ :: _ => by simp [map_map]

@[simp] theorem map_nth (f : α → β) :
    {n : Nat} → (xs : dvector α n) → (m : Nat) → (h : m < n) →
      (xs.map f).nth m h = f (xs.nth m h)
  | _, [], m, h => False.elim (Nat.not_lt_zero m h)
  | _, _ :: _, 0, _ => rfl
  | _, _ :: xs, m + 1, h => map_nth f xs m (Nat.lt_of_succ_lt_succ h)

end dvector

/-- The type `α → (α → ... (α → β)...)` with `n` copies of `α`. -/
def arity' (α β : Type u) : Nat → Type u
  | 0 => β
  | n + 1 => α → arity' α β n

namespace arity'

variable {α : Type u} {β : Type u} {γ : Type u}

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

def constant : {n : Nat} → β → arity' α β n
  | 0, b => b
  | _ + 1, b => fun _ => constant b

@[simp] def ofDVectorMap : {l : Nat} → ((xs : dvector α l) → β) → arity' α β l
  | 0, f => f []
  | _ + 1, f => fun x => ofDVectorMap (fun xs => f (x :: xs))

@[simp] def app : {l : Nat} → arity' α β l → dvector α l → β
  | 0, b, [] => b
  | _ + 1, f, x :: xs => app (f x) xs

@[simp] theorem app_zero (f : arity' α β 0) (xs : dvector α 0) : app f xs = f := by
  cases xs
  simp [app]

def postcompose (g : β → γ) : {n : Nat} → arity' α β n → arity' α γ n
  | 0, b => g b
  | _ + 1, f => fun x => postcompose g (f x)

def precompose : {n : Nat} → arity' β γ n → (α → β) → arity' α γ n
  | 0, g, _ => g
  | _ + 1, g, f => fun x => precompose (g (f x)) f

end arity'

end Flypitch
