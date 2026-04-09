import Mathlib
import Flypitch.Compat.Core

universe u v w

namespace Flypitch
namespace colimit

/-!
`Flypitch.Colimit` develops directed colimits for the concrete types used in the completeness
argument. It packages directed diagrams, their quotient colimits, and the universal maps needed
later for Henkin languages and their associated syntax.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.dupNamespace false

structure directed_type : Type (u + 1) where
  carrier : Type u
  rel : carrier → carrier → Prop
  h_reflexive : ∀ x, rel x x
  h_transitive : ∀ {x y z}, rel x y → rel y z → rel x z
  h_directed : ∀ x y, ∃ z : carrier, rel x z ∧ rel y z

lemma trans {D : directed_type} {i j k : D.carrier} (h₁ : D.rel i j) (h₂ : D.rel j k) :
    D.rel i k :=
  D.h_transitive h₁ h₂

structure directed_diagram (D : directed_type.{u}) : Type (max u v + 1) where
  obj : D.carrier → Type v
  mor : ∀ {x y}, D.rel x y → obj x → obj y
  h_mor : ∀ {x y z} {f₁ : D.rel x y} {f₂ : D.rel y z} {f₃ : D.rel x z},
    mor f₃ = mor f₂ ∘ mor f₁

/-- The directed type whose objects are natural numbers ordered by `≤`. -/
@[reducible] def directed_type_of_nat : directed_type :=
  { carrier := Nat
    rel := (· ≤ ·)
    h_reflexive := fun _ => le_rfl
    h_transitive := fun {_ _ _} h₁ h₂ => Nat.le_trans h₁ h₂
    h_directed := fun x y => ⟨max x y, le_max_left _ _, le_max_right _ _⟩ }

notation "ℕ'" => directed_type_of_nat

@[simp] lemma ℕ_of_ℕ'.carrier : (ℕ').carrier = Nat := rfl
@[simp] lemma le_of_ℕ'.rel : (ℕ').rel = Nat.le := rfl

def constant_functor (D : directed_type.{u}) (A : Type v) : directed_diagram D :=
  { obj := fun _ => A
    mor := fun _ => id
    h_mor := by intros; rfl }

def coproduct_of_directed_diagram {D : directed_type.{u}} (F : directed_diagram D) :=
  Σ a : D.carrier, F.obj a

def canonical_inclusion_coproduct {D : directed_type.{u}} {F : directed_diagram D}
    (i : D.carrier) :
    F.obj i → coproduct_of_directed_diagram F :=
  fun x => ⟨i, x⟩

def germ_relation {D : directed_type.{u}} (F : directed_diagram D) :
    coproduct_of_directed_diagram F → coproduct_of_directed_diagram F → Prop
  | ⟨i, x⟩, ⟨j, y⟩ =>
      ∃ k : D.carrier, ∃ z : F.obj k, ∃ f_x : D.rel i k, ∃ f_y : D.rel j k,
        F.mor f_x x = z ∧ F.mor f_y y = z

lemma germ_equivalence {D : directed_type.{u}} (F : directed_diagram D) :
    Equivalence (germ_relation F) := by
  constructor
  · intro a
    rcases a with ⟨i, x⟩
    refine ⟨i, F.mor (D.h_reflexive i) x, D.h_reflexive i, D.h_reflexive i, rfl, rfl⟩
  · intro a b h
    rcases a with ⟨i, x⟩
    rcases b with ⟨j, y⟩
    rcases h with ⟨k, z, f_x, f_y, hx, hy⟩
    exact ⟨k, z, f_y, f_x, hy, hx⟩
  · intro a b c hab hbc
    rcases a with ⟨i, x⟩
    rcases b with ⟨j, y⟩
    rcases c with ⟨k, z⟩
    rcases hab with ⟨ℓ₁, z₁, fi, fj₁, hix, hjy₁⟩
    rcases hbc with ⟨ℓ₂, z₂, fj₂, fk, hjy₂, hkz⟩
    rcases D.h_directed ℓ₁ ℓ₂ with ⟨ℓ₃, g₁, g₂⟩
    let f₁ : D.rel i ℓ₃ := D.h_transitive fi g₁
    let f₂l : D.rel j ℓ₃ := D.h_transitive fj₁ g₁
    let f₂r : D.rel j ℓ₃ := D.h_transitive fj₂ g₂
    let f₃ : D.rel k ℓ₃ := D.h_transitive fk g₂
    have h₁ : F.mor f₁ = F.mor g₁ ∘ F.mor fi := F.h_mor
    have h₂l : F.mor f₂l = F.mor g₁ ∘ F.mor fj₁ := F.h_mor
    have h₂r : F.mor f₂r = F.mor g₂ ∘ F.mor fj₂ := F.h_mor
    have h₃ : F.mor f₃ = F.mor g₂ ∘ F.mor fk := F.h_mor
    have hy : F.mor fi x = F.mor fj₁ y := by
      calc
        F.mor fi x = z₁ := hix
        _ = F.mor fj₁ y := hjy₁.symm
    have hz : F.mor fk z = F.mor fj₂ y := by
      calc
        F.mor fk z = z₂ := hkz
        _ = F.mor fj₂ y := hjy₂.symm
    have hf₂ : f₂l = f₂r := Subsingleton.elim _ _
    refine ⟨ℓ₃, F.mor f₂l y, f₁, f₃, ?_, ?_⟩
    · calc
        F.mor f₁ x = (F.mor g₁ ∘ F.mor fi) x := by rw [h₁]
        _ = F.mor g₁ (F.mor fi x) := rfl
        _ = F.mor g₁ (F.mor fj₁ y) := by rw [hy]
        _ = (F.mor g₁ ∘ F.mor fj₁) y := rfl
        _ = F.mor f₂l y := by rw [h₂l]
    · calc
        F.mor f₃ z = (F.mor g₂ ∘ F.mor fk) z := by rw [h₃]
        _ = F.mor g₂ (F.mor fk z) := rfl
        _ = F.mor g₂ (F.mor fj₂ y) := by rw [hz]
        _ = (F.mor g₂ ∘ F.mor fj₂) y := rfl
        _ = F.mor f₂r y := by rw [h₂r]
        _ = F.mor f₂l y := by simpa [hf₂]

instance coproduct_setoid {D : directed_type.{u}} (F : directed_diagram D) :
    Setoid (coproduct_of_directed_diagram F) :=
  ⟨germ_relation F, germ_equivalence F⟩

abbrev colimit {D : directed_type.{u}} (F : directed_diagram D) :=
  Quotient (coproduct_setoid F)

def canonical_map {D : directed_type.{u}} {F : directed_diagram D} (i : D.carrier) :
    F.obj i → colimit F :=
  fun x => Quotient.mk'' (⟨i, x⟩ : coproduct_of_directed_diagram F)

lemma canonical_map_inj_of_transition_maps_inj {D : directed_type.{u}} {F : directed_diagram D}
    (i : D.carrier) (H : ∀ {i j}, ∀ h : D.rel i j, Function.Injective (F.mor h)) :
    Function.Injective (@canonical_map D F i) := by
  intro x y hxy
  change
    (Quotient.mk'' (⟨i, x⟩ : coproduct_of_directed_diagram F) :
      Quotient (coproduct_setoid F)) =
    Quotient.mk'' (⟨i, y⟩ : coproduct_of_directed_diagram F) at hxy
  have hrel : germ_relation F ⟨i, x⟩ ⟨i, y⟩ := Quotient.exact hxy
  rcases hrel with ⟨j, z, edge₁, edge₂, h₁, h₂⟩
  have hedge : edge₁ = edge₂ := Subsingleton.elim _ _
  subst edge₂
  exact H edge₁ <| by
    calc
      F.mor edge₁ x = z := h₁
      _ = F.mor edge₁ y := h₂.symm

structure cocone {D : directed_type.{u}} (F : directed_diagram D) where
  vertex : Type w
  map : Π i : D.carrier, F.obj i → vertex
  h_compat : ∀ {i j}, ∀ h : D.rel i j, map i = map j ∘ F.mor h

def cocone_of_colimit {D : directed_type.{u}} (F : directed_diagram D) : cocone F := by
  refine ⟨colimit F, canonical_map, ?_⟩
  intro i j h
  funext x
  apply Quotient.sound
  have h_refl : D.rel j j := D.h_reflexive j
  refine ⟨j, F.mor h x, h, h_refl, rfl, ?_⟩
  have hmor : F.mor h = F.mor h_refl ∘ F.mor h := F.h_mor
  simpa [Function.comp] using congrArg (fun g => g x) hmor.symm

def universal_map {D : directed_type.{u}} {F : directed_diagram D} {V : cocone F} :
    colimit F → V.vertex := by
  refine Quotient.lift (fun p => V.map p.1 p.2) ?_
  intro p q hpq
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  rcases hpq with ⟨k, z, f₁, f₂, h₁, h₂⟩
  calc
    V.map i x = V.map k (F.mor f₁ x) := by
      simpa [Function.comp] using congrArg (fun g => g x) (V.h_compat f₁)
    _ = V.map k z := by rw [h₁]
    _ = V.map k (F.mor f₂ y) := by rw [h₂]
    _ = V.map j y := by
      simpa [Function.comp] using congrArg (fun g => g y) (V.h_compat f₂).symm

@[simp] lemma universal_map_property {D : directed_type.{u}} {F : directed_diagram D}
    {V : cocone F}
    (i : D.carrier) (x) : universal_map ((canonical_map i) x) = V.map i x :=
  rfl

lemma universal_map_inj_of_components_inj {D : directed_type.{u}} {F : directed_diagram D}
    {V : cocone F} (h_inj : ∀ i : D.carrier, Function.Injective (V.map i)) :
    Function.Injective (universal_map : colimit F → V.vertex) := by
  intro a b hab
  revert hab
  refine Quotient.inductionOn₂ a b ?_
  intro p q hpq
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  rcases D.h_directed i j with ⟨k, hik, hjk⟩
  apply Quotient.sound
  have hcomp_i : V.map i x = V.map k (F.mor hik x) := by
    simpa [Function.comp] using congrArg (fun g => g x) (V.h_compat hik)
  have hcomp_j : V.map j y = V.map k (F.mor hjk y) := by
    simpa [Function.comp] using congrArg (fun g => g y) (V.h_compat hjk)
  have hmor : F.mor hik x = F.mor hjk y := by
    apply h_inj k
    calc
      V.map k (F.mor hik x) = V.map i x := hcomp_i.symm
      _ = V.map j y := by simpa [universal_map, canonical_map] using hpq
      _ = V.map k (F.mor hjk y) := hcomp_j
  exact ⟨k, F.mor hik x, hik, hjk, rfl, hmor.symm⟩

noncomputable def germ_rep {D : directed_type.{u}} {F : directed_diagram D} (a : colimit F) :
    Σ' x : coproduct_of_directed_diagram F, (⟦x⟧ : colimit F) = a := by
  classical
  let q : Quotient (coproduct_setoid F) := a
  refine ⟨Classical.choose (Quotient.exists_rep q), ?_⟩
  simpa [q] using Classical.choose_spec (Quotient.exists_rep q)

@[simp] lemma canonical_map_quotient {D : directed_type.{u}} {F : directed_diagram D}
    (a : coproduct_of_directed_diagram F) :
    canonical_map a.1 a.2 = (Quotient.mk'' a : Quotient (coproduct_setoid F)) :=
  rfl

@[simp] lemma eq_mor_of_same_fiber {D : directed_type.{u}} {F : directed_diagram D}
    (a b : coproduct_of_directed_diagram F) {z : colimit F}
    (ha : (Quotient.mk'' a : Quotient (coproduct_setoid F)) = z)
    (hb : (Quotient.mk'' b : Quotient (coproduct_setoid F)) = z)
    (h_inj : ∀ i : D.carrier, Function.Injective (@canonical_map D F i)) (h_rel : D.rel a.1 b.1) :
    F.mor h_rel a.2 = b.2 := by
  have hz : canonical_map b.1 (F.mor h_rel a.2) = z := by
    calc
      canonical_map b.1 (F.mor h_rel a.2) = canonical_map a.1 a.2 := by
        simpa [Function.comp] using congrArg (fun g => g a.2) ((cocone_of_colimit F).h_compat h_rel).symm
      _ = z := ha
  apply h_inj b.1
  calc
    canonical_map b.1 (F.mor h_rel a.2) = z := hz
    _ = canonical_map b.1 b.2 := hb.symm

lemma eq_mor_of_same_fiber' {D : directed_type.{u}} {F : directed_diagram D}
    (a_fst b_fst : D.carrier) (a_snd : F.obj a_fst) (b_snd : F.obj b_fst) {z : colimit F}
    (ha : (Quotient.mk'' (⟨a_fst, a_snd⟩ : coproduct_of_directed_diagram F) :
      Quotient (coproduct_setoid F)) = z)
    (hb : (Quotient.mk'' (⟨b_fst, b_snd⟩ : coproduct_of_directed_diagram F) :
      Quotient (coproduct_setoid F)) = z)
    (h_inj : ∀ i : D.carrier, Function.Injective (@canonical_map D F i)) (h_rel : D.rel a_fst b_fst) :
    F.mor h_rel a_snd = b_snd := by
  let a : coproduct_of_directed_diagram F := ⟨a_fst, a_snd⟩
  let b : coproduct_of_directed_diagram F := ⟨b_fst, b_snd⟩
  simpa [a, b] using eq_mor_of_same_fiber (F := F) a b ha hb h_inj h_rel

@[reducible] def push_to_sum_r {F : directed_diagram ℕ'} {i : Nat} (x : F.obj i) (j : Nat) :
    F.obj (i + j) :=
  F.mor (by simp) x

@[reducible] def push_to_sum_l {F : directed_diagram ℕ'} {j : Nat} (x : F.obj j) (i : Nat) :
    F.obj (i + j) :=
  F.mor (by simpa [Nat.add_comm]) x

lemma same_fiber_as_push_to_r {F : directed_diagram ℕ'} {i : Nat} (x : F.obj i) (j : Nat) :
    canonical_map (F := F) i x = canonical_map (F := F) (i + j) (push_to_sum_r x j) := by
  simpa [push_to_sum_r, Function.comp] using
    congrArg (fun g => g x) ((cocone_of_colimit F).h_compat (by simp))

lemma same_fiber_as_push_to_l {F : directed_diagram ℕ'} {j : Nat} (x : F.obj j) (i : Nat) :
    canonical_map (F := F) j x = canonical_map (F := F) (i + j) (push_to_sum_l x i) := by
  simpa [push_to_sum_l, Function.comp, Nat.add_comm] using
    congrArg (fun g => g x) ((cocone_of_colimit F).h_compat (by simpa [Nat.add_comm]))

end colimit

namespace omega_colimit

open colimit

/- Facts about directed colimits indexed by `ℕ'`. -/

end omega_colimit
end Flypitch
