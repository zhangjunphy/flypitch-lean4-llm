import Flypitch.FOL.Theory

universe u

namespace Flypitch
namespace fol

local notation "[]" => dvector.nil
local infixr:67 " :: " => dvector.cons

/-- Terms with free variables bounded by `n`. -/
def bounded_preterm (L : Language.{u}) (n : Nat) (l : Nat) : Type u :=
  { t : preterm L l // bounded_term_at t n }

abbrev bounded_term (L : Language.{u}) (n : Nat) : Type u :=
  bounded_preterm L n 0

abbrev closed_preterm (L : Language.{u}) (l : Nat) : Type u :=
  bounded_preterm L 0 l

abbrev closed_term (L : Language.{u}) : Type u :=
  bounded_term L 0

namespace bounded_preterm

variable {L : Language.{u}} {n m l : Nat}

instance : CoeOut (bounded_preterm L n l) (preterm L l) where
  coe := Subtype.val

@[simp] def fst (t : bounded_preterm L n l) : preterm L l :=
  t.1

@[simp] theorem eta (t : bounded_preterm L n l) : Subtype.mk t.1 t.2 = t := by
  cases t
  rfl

def cast (h : n ≤ m) (t : bounded_preterm L n l) : bounded_preterm L m l :=
  ⟨t.1, bounded_term_at_mono t.1 t.2 h⟩

def cast1 (t : bounded_preterm L n l) : bounded_preterm L (n + 1) l :=
  cast (Nat.le_succ n) t

@[simp] theorem cast_fst (h : n ≤ m) (t : bounded_preterm L n l) :
    (t.cast h).fst = t.fst :=
  rfl

@[simp] theorem cast1_fst (t : bounded_preterm L n l) :
    (t.cast1).fst = t.fst :=
  rfl

end bounded_preterm

variable {L : Language.{u}}

def bd_var {n : Nat} (k : Fin n) : bounded_term L n :=
  ⟨&k.1, k.2⟩

def bd_func {n l : Nat} (f : L.functions l) : bounded_preterm L n l :=
  ⟨preterm.func f, trivial⟩

def bd_app {n l : Nat} (t : bounded_preterm L n (l + 1)) (s : bounded_term L n) :
    bounded_preterm L n l :=
  ⟨preterm.app t.1 s.1, ⟨t.2, s.2⟩⟩

def bd_const {n : Nat} (c : L.constants) : bounded_term L n :=
  bd_func c

@[simp] def bd_apps : {n l : Nat} → bounded_preterm L n l →
    dvector (bounded_term L n) l → bounded_term L n
  | _, 0, t, [] => t
  | _, _ + 1, t, s :: ts => bd_apps (bd_app t s) ts

/-- Formulas with free variables bounded by `n`. -/
def bounded_preformula (L : Language.{u}) (n : Nat) (l : Nat) : Type u :=
  { f : preformula L l // bounded_formula_at f n }

abbrev bounded_formula (L : Language.{u}) (n : Nat) : Type u :=
  bounded_preformula L n 0

abbrev presentence (L : Language.{u}) (l : Nat) : Type u :=
  bounded_preformula L 0 l

namespace bounded_preformula

variable {L : Language.{u}} {n m l : Nat}

instance : CoeOut (bounded_preformula L n l) (preformula L l) where
  coe := Subtype.val

@[simp] def fst (f : bounded_preformula L n l) : preformula L l :=
  f.1

@[simp] theorem eta (f : bounded_preformula L n l) : Subtype.mk f.1 f.2 = f := by
  cases f
  rfl

def cast (h : n ≤ m) (f : bounded_preformula L n l) : bounded_preformula L m l :=
  ⟨f.1, bounded_formula_at_mono f.1 f.2 h⟩

def cast1 (f : bounded_preformula L n l) : bounded_preformula L (n + 1) l :=
  cast (Nat.le_succ n) f

@[simp] theorem cast_fst (h : n ≤ m) (f : bounded_preformula L n l) :
    (f.cast h).fst = f.fst :=
  rfl

@[simp] theorem cast1_fst (f : bounded_preformula L n l) :
    (f.cast1).fst = f.fst :=
  rfl

end bounded_preformula

variable {L : Language.{u}}

def bd_falsum {n : Nat} : bounded_formula L n :=
  ⟨⊥, trivial⟩

def bd_equal {n : Nat} (t₁ t₂ : bounded_term L n) : bounded_formula L n :=
  ⟨t₁.1 ≃ t₂.1, ⟨t₁.2, t₂.2⟩⟩

def bd_rel {n l : Nat} (R : L.relations l) : bounded_preformula L n l :=
  ⟨preformula.rel R, trivial⟩

def bd_apprel {n l : Nat} (f : bounded_preformula L n (l + 1)) (t : bounded_term L n) :
    bounded_preformula L n l :=
  ⟨preformula.apprel f.1 t.1, ⟨f.2, t.2⟩⟩

def bd_imp {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  ⟨f₁.1 ⟹ f₂.1, ⟨f₁.2, f₂.2⟩⟩

def bd_all {n : Nat} (f : bounded_formula L (n + 1)) : bounded_formula L n :=
  ⟨∀' f.1, f.2⟩

instance {n : Nat} : Bot (bounded_formula L n) where
  bot := bd_falsum

def bd_not {n : Nat} (f : bounded_formula L n) : bounded_formula L n :=
  bd_imp f bd_falsum

def bd_and {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_not (bd_imp f₁ (bd_not f₂))

def bd_or {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_imp (bd_not f₁) f₂

def bd_biimp {n : Nat} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_and (bd_imp f₁ f₂) (bd_imp f₂ f₁)

def bd_ex {n : Nat} (f : bounded_formula L (n + 1)) : bounded_formula L n :=
  bd_not (bd_all (bd_not f))

@[simp] def bd_apps_rel : {n l : Nat} → bounded_preformula L n l →
    dvector (bounded_term L n) l → bounded_formula L n
  | _, 0, f, [] => f
  | _, _ + 1, f, t :: ts => bd_apps_rel (bd_apprel f t) ts

@[simp] theorem bd_var_fst {n : Nat} (k : Fin n) :
    (bd_var (L := L) k).fst = (&k.1 : term L) :=
  rfl

@[simp] theorem bd_func_fst {n l : Nat} (f : L.functions l) :
    (bd_func (L := L) (n := n) f).fst = preterm.func f :=
  rfl

@[simp] theorem bd_app_fst {n l : Nat} (t : bounded_preterm L n (l + 1)) (s : bounded_term L n) :
    (bd_app t s).fst = preterm.app t.fst s.fst :=
  rfl

@[simp] theorem bd_equal_fst {n : Nat} (t₁ t₂ : bounded_term L n) :
    (bd_equal t₁ t₂).fst = (t₁.fst ≃ t₂.fst) :=
  rfl

@[simp] theorem bd_rel_fst {n l : Nat} (R : L.relations l) :
    (bd_rel (L := L) (n := n) R).fst = preformula.rel R :=
  rfl

@[simp] theorem bd_apprel_fst {n l : Nat} (f : bounded_preformula L n (l + 1))
    (t : bounded_term L n) :
    (bd_apprel f t).fst = preformula.apprel f.fst t.fst :=
  rfl

@[simp] theorem bd_imp_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_imp f₁ f₂).fst = (f₁.fst ⟹ f₂.fst) :=
  rfl

@[simp] theorem bd_all_fst {n : Nat} (f : bounded_formula L (n + 1)) :
    (bd_all f).fst = ∀' f.fst :=
  rfl

@[simp] theorem bd_not_fst {n : Nat} (f : bounded_formula L n) :
    (bd_not f).fst = ∼f.fst :=
  rfl

@[simp] theorem bd_and_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_and f₁ f₂).fst = and f₁.fst f₂.fst :=
  rfl

@[simp] theorem bd_or_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_or f₁ f₂).fst = or f₁.fst f₂.fst :=
  rfl

@[simp] theorem bd_biimp_fst {n : Nat} (f₁ f₂ : bounded_formula L n) :
    (bd_biimp f₁ f₂).fst = biimp f₁.fst f₂.fst :=
  rfl

@[simp] theorem bd_ex_fst {n : Nat} (f : bounded_formula L (n + 1)) :
    (bd_ex f).fst = ex f.fst :=
  rfl

end fol
end Flypitch
