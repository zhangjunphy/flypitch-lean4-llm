import Flypitch.Colimit
import Flypitch.Completion
import Flypitch.LanguageExtension

universe u v

namespace Flypitch

open fol

/-!
`Flypitch.Henkin` constructs the omega-chain of language extensions that adjoin witness
constants, forms its colimit language `LInfty`, and compares the colimit syntax with the
bounded syntax already present in the tower. The later part of the file packages these maps
into the Henkin theory used by the completeness argument.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace colimit

local infixr:80 " ∘ᴸ " => fol.Lhom.comp

private theorem hom_ext {L₁ L₂ : Language} {F G : L₁ →ᴸ L₂}
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

structure directed_diagram_language (D : directed_type.{u}) : Type (max u v + 1) where
  obj : D.carrier → Language.{v}
  mor : ∀ {x y}, D.rel x y → ((obj x) →ᴸ (obj y))
  h_mor : ∀ {x y z} {f₁ : D.rel x y} {f₂ : D.rel y z} {f₃ : D.rel x z},
    mor f₃ = mor f₂ ∘ᴸ mor f₁

@[reducible] def diagram_functions {D : directed_type.{u}} {F : directed_diagram_language D}
    (n : Nat) : directed_diagram D :=
  { obj := fun x => (F.obj x).functions n
    mor := fun h => (F.mor h).on_function
    h_mor := by
      intro x y z f₁ f₂ f₃
      funext a
      simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n a)
        (F.h_mor (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)) }

@[reducible] def diagram_relations {D : directed_type.{u}} {F : directed_diagram_language D}
    (n : Nat) : directed_diagram D :=
  { obj := fun x => (F.obj x).relations n
    mor := fun h => (F.mor h).on_relation
    h_mor := by
      intro x y z f₁ f₂ f₃
      funext a
      simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n a)
        (F.h_mor (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)) }

def colimit_language {D : directed_type.{u}} (F : directed_diagram_language D) : Language :=
  ⟨fun n => colimit (diagram_functions (F := F) n), fun n => colimit (diagram_relations (F := F) n)⟩

def canonical_map_language {D : directed_type.{u}} {F : directed_diagram_language D}
    (i : D.carrier) : F.obj i →ᴸ colimit_language F :=
  ⟨fun {n} => canonical_map (F := diagram_functions (F := F) n) i,
    fun {n} => canonical_map (F := diagram_relations (F := F) n) i⟩

structure cocone_language {D : directed_type.{u}} (F : directed_diagram_language D) where
  vertex : Language
  map : Π i : D.carrier, F.obj i →ᴸ vertex
  h_compat : ∀ {i j}, ∀ h : D.rel i j, map i = map j ∘ᴸ F.mor h

def cocone_of_colimit_language {D : directed_type.{u}} (F : directed_diagram_language D) :
    cocone_language F := by
  refine ⟨colimit_language F, canonical_map_language, ?_⟩
  intro i j h
  apply hom_ext
  · intro n x
    apply Quotient.sound
    have h_refl : D.rel j j := D.h_reflexive j
    refine ⟨j, (F.mor h).on_function x, h, h_refl, rfl, ?_⟩
    have hmor := congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n x)
      (F.h_mor (f₁ := h) (f₂ := h_refl) (f₃ := h))
    simpa [Lhom.comp] using hmor.symm
  · intro n x
    apply Quotient.sound
    have h_refl : D.rel j j := D.h_reflexive j
    refine ⟨j, (F.mor h).on_relation x, h, h_refl, rfl, ?_⟩
    have hmor := congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n x)
      (F.h_mor (f₁ := h) (f₂ := h_refl) (f₃ := h))
    simpa [Lhom.comp] using hmor.symm

def universal_map_language {D : directed_type.{u}} {F : directed_diagram_language D}
    {V : cocone_language F} : colimit_language F →ᴸ V.vertex := by
  refine ⟨?_, ?_⟩
  · intro n
    refine Quotient.lift (fun p => (V.map p.1).on_function p.2) ?_
    intro p q hpq
    rcases p with ⟨i, x⟩
    rcases q with ⟨j, y⟩
    rcases hpq with ⟨k, z, f₁, f₂, h₁, h₂⟩
    calc
      (V.map i).on_function x = (V.map k).on_function ((F.mor f₁).on_function x) := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n x) (V.h_compat f₁)
      _ = (V.map k).on_function z := by
        simpa using congrArg (fun t => (V.map k).on_function t) h₁
      _ = (V.map k).on_function ((F.mor f₂).on_function y) := by
        simpa using congrArg (fun t => (V.map k).on_function t) h₂.symm
      _ = (V.map j).on_function y := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_function _ _ ϕ n y) (V.h_compat f₂).symm
  · intro n
    refine Quotient.lift (fun p => (V.map p.1).on_relation p.2) ?_
    intro p q hpq
    rcases p with ⟨i, x⟩
    rcases q with ⟨j, y⟩
    rcases hpq with ⟨k, z, f₁, f₂, h₁, h₂⟩
    calc
      (V.map i).on_relation x = (V.map k).on_relation ((F.mor f₁).on_relation x) := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n x) (V.h_compat f₁)
      _ = (V.map k).on_relation z := by
        simpa using congrArg (fun t => (V.map k).on_relation t) h₁
      _ = (V.map k).on_relation ((F.mor f₂).on_relation y) := by
        simpa using congrArg (fun t => (V.map k).on_relation t) h₂.symm
      _ = (V.map j).on_relation y := by
        simpa [Lhom.comp] using congrArg (fun ϕ => @Lhom.on_relation _ _ ϕ n y) (V.h_compat f₂).symm

end colimit

namespace henkin

open colimit

local infixr:80 " ∘ᴸ " => Lhom.comp

inductive languageFunctions (L : Language.{u}) : Nat → Type u
  | inc : ∀ {n}, L.functions n → languageFunctions L n
  | wit : bounded_formula L 1 → languageFunctions L 0

@[reducible] def languageStep (L : Language.{u}) : Language.{u} :=
  ⟨languageFunctions L, L.relations⟩

def wit' {L : Language.{u}} : bounded_formula L 1 → (languageStep L).constants :=
  languageFunctions.wit

def inclusion {L : Language.{u}} : L →ᴸ languageStep L :=
  ⟨fun {_n} f => languageFunctions.inc f, fun {_n} R => R⟩

lemma inclusion_inj {L : Language.{u}} : Lhom.is_injective (@inclusion L) := by
  refine ⟨?_, ?_⟩
  · intro n x y hxy
    exact languageFunctions.inc.inj hxy
  · intro n x y hxy
    exact hxy

@[reducible] def chainObjects (L : Language.{u}) : Nat → Language.{u}
  | 0 => L
  | n + 1 => languageStep (chainObjects L n)

def chainMaps (L : Language.{u}) : ∀ x y, x ≤ y → ((chainObjects L x) →ᴸ (chainObjects L y))
  | x, 0, h => by
      have hx : x = 0 := Nat.eq_zero_of_le_zero h
      subst hx
      exact Lhom.id L
  | x, y + 1, h => by
      by_cases hxy : x = y + 1
      · subst hxy
        exact Lhom.id (chainObjects L (y + 1))
      · exact inclusion ∘ᴸ chainMaps L x y (Nat.lt_succ_iff.mp (lt_of_le_of_ne h hxy))

lemma chainMaps_comp (L : Language.{u}) :
    ∀ {x y z : Nat} (f₁ : x ≤ y) (f₂ : y ≤ z),
      chainMaps L x z (Nat.le_trans f₁ f₂) = chainMaps L y z f₂ ∘ᴸ chainMaps L x y f₁
  | x, y, 0, f₁, f₂ => by
      have hy : y = 0 := Nat.eq_zero_of_le_zero f₂
      have hx : x = 0 := Nat.eq_zero_of_le_zero (hy ▸ f₁)
      subst hy
      subst hx
      simp [chainMaps]
  | x, y, z + 1, f₁, f₂ => by
      by_cases hy : y = z + 1
      · subst hy
        by_cases hx : x = z + 1
        · subst hx
          simp [chainMaps]
        · simp [chainMaps, hx]
      · have hy' : y ≤ z := Nat.lt_succ_iff.mp (lt_of_le_of_ne f₂ hy)
        have hx : x ≠ z + 1 := by
          intro hx
          have hle : z + 1 ≤ z := by
            simpa [hx] using Nat.le_trans f₁ hy'
          exact Nat.not_succ_le_self z hle
        rw [chainMaps, dif_neg hx, chainMaps, dif_neg hy]
        rw [chainMaps_comp (L := L) f₁ hy']

lemma chainMaps_inj (L : Language.{u}) :
    ∀ x y (h : x ≤ y), Lhom.is_injective (chainMaps L x y h)
  | x, 0, h => by
      have hx : x = 0 := Nat.eq_zero_of_le_zero h
      subst hx
      refine ⟨?_, ?_⟩ <;> intro n a b hab <;> simpa [chainMaps] using hab
  | x, y + 1, h => by
      by_cases hxy : x = y + 1
      · subst hxy
        refine ⟨?_, ?_⟩ <;> intro n a b hab <;> simpa [chainMaps] using hab
      · have hxy' : x ≤ y := Nat.lt_succ_iff.mp (lt_of_le_of_ne h hxy)
        have ih := chainMaps_inj L x y hxy'
        refine ⟨?_, ?_⟩
        · intro n a b hab
          have hinc :
              inclusion.on_function ((chainMaps L x y hxy').on_function a) =
                inclusion.on_function ((chainMaps L x y hxy').on_function b) := by
            simpa [chainMaps, hxy, Lhom.comp] using hab
          have hmid :
              (chainMaps L x y hxy').on_function a = (chainMaps L x y hxy').on_function b :=
            (inclusion_inj (L := chainObjects L y)).on_function hinc
          exact ih.on_function hmid
        · intro n a b hab
          have hinc :
              inclusion.on_relation ((chainMaps L x y hxy').on_relation a) =
                inclusion.on_relation ((chainMaps L x y hxy').on_relation b) := by
            simpa [chainMaps, hxy, Lhom.comp] using hab
          have hmid :
              (chainMaps L x y hxy').on_relation a = (chainMaps L x y hxy').on_relation b :=
            (inclusion_inj (L := chainObjects L y)).on_relation hinc
          exact ih.on_relation hmid

def languageChain {L : Language.{u}} : directed_diagram_language ℕ' :=
  { obj := chainObjects L
    mor := fun h => chainMaps L _ _ h
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      exact chainMaps_comp (L := L) f₁ f₂ }

def LInfty (L : Language.{u}) : Language.{u} :=
  colimit_language (languageChain (L := L))

def canonicalMap {L : Language.{u}} (m : Nat) : chainObjects L m →ᴸ LInfty L :=
  canonical_map_language (F := languageChain (L := L)) m

lemma canonicalMap_inj {L : Language.{u}} (m : Nat) : Lhom.is_injective (@canonicalMap L m) := by
  refine ⟨?_, ?_⟩
  · intro n
    simpa [canonicalMap, canonical_map_language] using
      (canonical_map_inj_of_transition_maps_inj
        (D := ℕ') (F := diagram_functions (F := languageChain (L := L)) n) m
        (by
          intro i j h
          exact (chainMaps_inj L i j h).on_function))
  · intro n
    simpa [canonicalMap, canonical_map_language] using
      (canonical_map_inj_of_transition_maps_inj
        (D := ℕ') (F := diagram_relations (F := languageChain (L := L)) n) m
        (by
          intro i j h
          exact (chainMaps_inj L i j h).on_relation))

def termChain {L : Language.{u}} (l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => preterm (chainObjects L k) l
    mor := fun h => Lhom.on_term (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext t
      simp [chainMaps_comp (L := L) f₁ f₂] }

def formulaChain {L : Language.{u}} (l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => preformula (chainObjects L k) l
    mor := fun h => Lhom.on_formula (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext f
      simp [chainMaps_comp (L := L) f₁ f₂] }

def boundedTermChain {L : Language.{u}} (n l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => bounded_preterm (chainObjects L k) n l
    mor := fun h => Lhom.on_bounded_term (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext t
      simp [chainMaps_comp (L := L) f₁ f₂] }

@[reducible] def boundedTermChain' {L : Language.{u}} : directed_diagram ℕ' :=
  boundedTermChain (L := L) 1 0

def boundedFormulaChain {L : Language.{u}} (n l : Nat) : directed_diagram ℕ' :=
  { obj := fun k => bounded_preformula (chainObjects L k) n l
    mor := fun h => Lhom.on_bounded_formula (chainMaps L _ _ h)
    h_mor := by
      intro x y z f₁ f₂ f₃
      have hf₃ : f₃ = Nat.le_trans f₁ f₂ := Subsingleton.elim _ _
      subst hf₃
      funext f
      simp [chainMaps_comp (L := L) f₁ f₂] }

@[reducible] def boundedFormulaChain' {L : Language.{u}} : directed_diagram ℕ' :=
  boundedFormulaChain (L := L) 1 0

def coconeOfLInfty {L : Language.{u}} : cocone_language (languageChain (L := L)) :=
  cocone_of_colimit_language (languageChain (L := L))

def coconeOfTermLInfty {L : Language.{u}} (l : Nat) : cocone (termChain (L := L) l) := by
  refine ⟨preterm (LInfty L) l, fun i => Lhom.on_term (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext t
  have hmap := congrArg (fun ϕ => @Lhom.on_term _ _ ϕ l t) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_term (canonicalMap (L := L) i) t =
      Lhom.on_term (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) t := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_term (canonicalMap (L := L) j) (Lhom.on_term (chainMaps L i j h) t) := by
        simp

def coconeOfFormulaLInfty {L : Language.{u}} (l : Nat) : cocone (formulaChain (L := L) l) := by
  refine ⟨preformula (LInfty L) l, fun i => Lhom.on_formula (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext f
  have hmap := congrArg (fun ϕ => @Lhom.on_formula _ _ ϕ l f) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_formula (canonicalMap (L := L) i) f =
      Lhom.on_formula (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) f := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_formula (canonicalMap (L := L) j) (Lhom.on_formula (chainMaps L i j h) f) := by
        simp

def coconeOfBoundedTermLInfty {L : Language.{u}} (n l : Nat) :
    cocone (boundedTermChain (L := L) n l) := by
  refine ⟨bounded_preterm (LInfty L) n l, fun i => Lhom.on_bounded_term (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext t
  have hmap := congrArg (fun ϕ => @Lhom.on_bounded_term _ _ ϕ n l t) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_bounded_term (canonicalMap (L := L) i) t =
      Lhom.on_bounded_term (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) t := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_bounded_term (canonicalMap (L := L) j) (Lhom.on_bounded_term (chainMaps L i j h) t) := by
        simp

def coconeOfBoundedFormulaLInfty {L : Language.{u}} (n l : Nat) :
    cocone (boundedFormulaChain (L := L) n l) := by
  refine ⟨bounded_preformula (LInfty L) n l, fun i => Lhom.on_bounded_formula (canonicalMap (L := L) i), ?_⟩
  intro i j h
  funext f
  have hmap := congrArg (fun ϕ => @Lhom.on_bounded_formula _ _ ϕ n l f) ((coconeOfLInfty (L := L)).h_compat h)
  calc
    Lhom.on_bounded_formula (canonicalMap (L := L) i) f =
      Lhom.on_bounded_formula (canonicalMap (L := L) j ∘ᴸ chainMaps L i j h) f := by
        simpa [coconeOfLInfty, canonicalMap, languageChain] using hmap
    _ = Lhom.on_bounded_formula (canonicalMap (L := L) j) (Lhom.on_bounded_formula (chainMaps L i j h) f) := by
        simp

def coconeOfBoundedFormulaPrimeLInfty {L : Language.{u}} :
    cocone (boundedFormulaChain' (L := L)) := by
  simpa [boundedFormulaChain'] using coconeOfBoundedFormulaLInfty (L := L) 1 0

def termComparison {L : Language.{u}} (l : Nat) :
    colimit (termChain (L := L) l) → preterm (LInfty L) l :=
  universal_map (F := termChain (L := L) l) (V := coconeOfTermLInfty (L := L) l)

def formulaComparison {L : Language.{u}} (l : Nat) :
    colimit (formulaChain (L := L) l) → preformula (LInfty L) l :=
  universal_map (F := formulaChain (L := L) l) (V := coconeOfFormulaLInfty (L := L) l)

def boundedTermComparison {L : Language.{u}} (n l : Nat) :
    colimit (boundedTermChain (L := L) n l) → bounded_preterm (LInfty L) n l :=
  universal_map (F := boundedTermChain (L := L) n l) (V := coconeOfBoundedTermLInfty (L := L) n l)

@[reducible] def boundedTermComparison' {L : Language.{u}} :
    colimit (boundedTermChain' (L := L)) → bounded_term (LInfty L) 1 :=
  boundedTermComparison (L := L) 1 0

def boundedFormulaComparison {L : Language.{u}} (n l : Nat) :
    colimit (boundedFormulaChain (L := L) n l) → bounded_preformula (LInfty L) n l :=
  universal_map (F := boundedFormulaChain (L := L) n l) (V := coconeOfBoundedFormulaLInfty (L := L) n l)

@[reducible] def boundedFormulaComparison' {L : Language.{u}} :
    colimit (boundedFormulaChain' (L := L)) → bounded_formula (LInfty L) 1 :=
  boundedFormulaComparison (L := L) 1 0

private theorem termComparison_surjective {L : Language.{u}} :
    {l : Nat} → (t : preterm (LInfty L) l) →
      ∃ x : colimit (termChain (L := L) l), termComparison l x = t
  | _, .var k => by
      refine ⟨canonical_map (F := termChain (L := L) 0) 0 (&k), ?_⟩
      simp [termComparison, coconeOfTermLInfty]
  | l, .func f => by
      rcases germ_rep f with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).functions l at x
      refine ⟨canonical_map (F := termChain (L := L) l) i (preterm.func x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_function x = f := by
        simpa [canonicalMap, canonical_map_language] using hx
      simp [termComparison, coconeOfTermLInfty, hx']
  | l, .app t₁ t₂ => by
      rcases termComparison_surjective t₁ with ⟨u₁, hu₁⟩
      rcases termComparison_surjective t₂ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := termChain (L := L) l) (i + j)
        (preterm.app (push_to_sum_r (F := termChain (L := L) (l + 1)) x j)
          (push_to_sum_l (F := termChain (L := L) 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := termChain (L := L) (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := termChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          termComparison (L := L) (l + 1)
            (canonical_map (F := termChain (L := L) (l + 1)) (i + j)
              (push_to_sum_r (F := termChain (L := L) (l + 1)) x j)) = t₁ := by
        calc
          termComparison (L := L) (l + 1)
              (canonical_map (F := termChain (L := L) (l + 1)) (i + j)
                (push_to_sum_r (F := termChain (L := L) (l + 1)) x j)) =
            termComparison (L := L) (l + 1)
              (canonical_map (F := termChain (L := L) (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := termChain (L := L) (l + 1)) x j]
          _ = termComparison (L := L) (l + 1) u₁ := by rw [hx']
          _ = t₁ := hu₁
      have hty :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_l (F := termChain (L := L) 0) y i)) = t₂ := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_l (F := termChain (L := L) 0) y i)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := termChain (L := L) 0) y i]
          _ = termComparison (L := L) 0 u₂ := by rw [hy']
          _ = t₂ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := termChain (L := L) (l + 1)) x j) = t₁ := by
        simpa [termComparison, coconeOfTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := termChain (L := L) 0) y i) = t₂ := by
        simpa [termComparison, coconeOfTermLInfty] using hty
      simpa [termComparison, coconeOfTermLInfty, htx', hty']

theorem termComparison_bijective {L : Language.{u}} (l : Nat) :
    Function.Bijective (@termComparison L l) := by
  refine ⟨?_, ?_⟩
  · unfold termComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfTermLInfty]
    exact Lhom.on_term_inj (canonicalMap_inj (L := L) i)
  · intro t
    exact termComparison_surjective t

private theorem formulaComparison_surjective {L : Language.{u}} :
    {l : Nat} → (f : preformula (LInfty L) l) →
      ∃ x : colimit (formulaChain (L := L) l), formulaComparison l x = f
  | _, .falsum => by
      refine ⟨canonical_map (F := formulaChain (L := L) 0) 0 (preformula.falsum), ?_⟩
      change (⊥ : formula (LInfty L)) = preformula.falsum
      rfl
  | _, .equal t₁ t₂ => by
      rcases termComparison_surjective t₁ with ⟨u₁, hu₁⟩
      rcases termComparison_surjective t₂ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := formulaChain (L := L) 0) (i + j)
        (push_to_sum_r (F := termChain (L := L) 0) x j ≃
          push_to_sum_l (F := termChain (L := L) 0) y i), ?_⟩
      have hx' :
          canonical_map (F := termChain (L := L) 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := termChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_r (F := termChain (L := L) 0) x j)) = t₁ := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_r (F := termChain (L := L) 0) x j)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := termChain (L := L) 0) x j]
          _ = termComparison (L := L) 0 u₁ := by rw [hx']
          _ = t₁ := hu₁
      have hty :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_l (F := termChain (L := L) 0) y i)) = t₂ := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_l (F := termChain (L := L) 0) y i)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := termChain (L := L) 0) y i]
          _ = termComparison (L := L) 0 u₂ := by rw [hy']
          _ = t₂ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := termChain (L := L) 0) x j) = t₁ := by
        simpa [termComparison, coconeOfTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := termChain (L := L) 0) y i) = t₂ := by
        simpa [termComparison, coconeOfTermLInfty] using hty
      simpa [formulaComparison, coconeOfFormulaLInfty, htx', hty']
  | l, .rel R => by
      rcases germ_rep R with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).relations l at x
      refine ⟨canonical_map (F := formulaChain (L := L) l) i (preformula.rel x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_relation x = R := by
        simpa [canonicalMap, canonical_map_language] using hx
      simp [formulaComparison, coconeOfFormulaLInfty, hx']
  | l, .apprel f t => by
      rcases formulaComparison_surjective f with ⟨u₁, hu₁⟩
      rcases termComparison_surjective t with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := formulaChain (L := L) l) (i + j)
        (preformula.apprel
          (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j)
          (push_to_sum_l (F := termChain (L := L) 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := formulaChain (L := L) (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := termChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          formulaComparison (L := L) (l + 1)
            (canonical_map (F := formulaChain (L := L) (l + 1)) (i + j)
              (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j)) = f := by
        calc
          formulaComparison (L := L) (l + 1)
              (canonical_map (F := formulaChain (L := L) (l + 1)) (i + j)
                (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j)) =
            formulaComparison (L := L) (l + 1)
              (canonical_map (F := formulaChain (L := L) (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := formulaChain (L := L) (l + 1)) x j]
          _ = formulaComparison (L := L) (l + 1) u₁ := by rw [hx']
          _ = f := hu₁
      have hty :
          termComparison (L := L) 0
            (canonical_map (F := termChain (L := L) 0) (i + j)
              (push_to_sum_l (F := termChain (L := L) 0) y i)) = t := by
        calc
          termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) (i + j)
                (push_to_sum_l (F := termChain (L := L) 0) y i)) =
            termComparison (L := L) 0
              (canonical_map (F := termChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := termChain (L := L) 0) y i]
          _ = termComparison (L := L) 0 u₂ := by rw [hy']
          _ = t := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := formulaChain (L := L) (l + 1)) x j) = f := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hfx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := termChain (L := L) 0) y i) = t := by
        simpa [termComparison, coconeOfTermLInfty] using hty
      simpa [formulaComparison, coconeOfFormulaLInfty, hfx', hty']
  | _, .imp f₁ f₂ => by
      rcases formulaComparison_surjective f₁ with ⟨u₁, hu₁⟩
      rcases formulaComparison_surjective f₂ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := formulaChain (L := L) 0) (i + j)
        (push_to_sum_r (F := formulaChain (L := L) 0) x j ⟹
          push_to_sum_l (F := formulaChain (L := L) 0) y i), ?_⟩
      have hx' :
          canonical_map (F := formulaChain (L := L) 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := formulaChain (L := L) 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          formulaComparison (L := L) 0
            (canonical_map (F := formulaChain (L := L) 0) (i + j)
              (push_to_sum_r (F := formulaChain (L := L) 0) x j)) = f₁ := by
        calc
          formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) (i + j)
                (push_to_sum_r (F := formulaChain (L := L) 0) x j)) =
            formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := formulaChain (L := L) 0) x j]
          _ = formulaComparison (L := L) 0 u₁ := by rw [hx']
          _ = f₁ := hu₁
      have hgy :
          formulaComparison (L := L) 0
            (canonical_map (F := formulaChain (L := L) 0) (i + j)
              (push_to_sum_l (F := formulaChain (L := L) 0) y i)) = f₂ := by
        calc
          formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) (i + j)
                (push_to_sum_l (F := formulaChain (L := L) 0) y i)) =
            formulaComparison (L := L) 0
              (canonical_map (F := formulaChain (L := L) 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := formulaChain (L := L) 0) y i]
          _ = formulaComparison (L := L) 0 u₂ := by rw [hy']
          _ = f₂ := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := formulaChain (L := L) 0) x j) = f₁ := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hfx
      have hgy' :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_l (F := formulaChain (L := L) 0) y i) = f₂ := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hgy
      simpa [formulaComparison, coconeOfFormulaLInfty, hfx', hgy']
  | _, .all f => by
      rcases formulaComparison_surjective f with ⟨u, hu⟩
      rcases germ_rep u with ⟨⟨i, x⟩, hx⟩
      refine ⟨canonical_map (F := formulaChain (L := L) 0) i (∀' x), ?_⟩
      have hx' : canonical_map (F := formulaChain (L := L) 0) i x = u := by
        simpa [canonical_map] using hx
      have hfx : formulaComparison (L := L) 0
          (canonical_map (F := formulaChain (L := L) 0) i x) = f := by
        rw [hx']
        exact hu
      have hfx' : (canonicalMap (L := L) i).on_formula x = f := by
        simpa [formulaComparison, coconeOfFormulaLInfty] using hfx
      simpa [formulaComparison, coconeOfFormulaLInfty, hfx']

theorem formulaComparison_bijective {L : Language.{u}} (l : Nat) :
    Function.Bijective (@formulaComparison L l) := by
  refine ⟨?_, ?_⟩
  · unfold formulaComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfFormulaLInfty]
    exact Lhom.on_formula_inj (canonicalMap_inj (L := L) i)
  · intro f
    exact formulaComparison_surjective f

private theorem boundedTermComparison_surjective {L : Language.{u}} :
    {n l : Nat} → (t : bounded_preterm (LInfty L) n l) →
      ∃ x : colimit (boundedTermChain (L := L) n l), boundedTermComparison n l x = t
  | n, _, ⟨.var k, hk⟩ => by
      refine ⟨canonical_map (F := boundedTermChain (L := L) n 0) 0 (bd_var ⟨k, hk⟩), ?_⟩
      simp [boundedTermComparison, coconeOfBoundedTermLInfty, bd_var]
  | n, l, ⟨.func f, _⟩ => by
      rcases germ_rep f with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).functions l at x
      refine ⟨canonical_map (F := boundedTermChain (L := L) n l) i (bd_func x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_function x = f := by
        simpa [canonicalMap, canonical_map_language] using hx
      apply Subtype.ext
      simp [boundedTermComparison, coconeOfBoundedTermLInfty, bd_func, hx']
  | n, l, ⟨.app t s, hts⟩ => by
      rcases boundedTermComparison_surjective ⟨t, hts.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedTermComparison_surjective ⟨s, hts.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedTermChain (L := L) n l) (i + j)
        (bd_app (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)
          (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedTermChain (L := L) n (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedTermChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          boundedTermComparison (L := L) n (l + 1)
            (canonical_map (F := boundedTermChain (L := L) n (l + 1)) (i + j)
              (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)) = ⟨t, hts.1⟩ := by
        calc
          boundedTermComparison (L := L) n (l + 1)
              (canonical_map (F := boundedTermChain (L := L) n (l + 1)) (i + j)
                (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)) =
            boundedTermComparison (L := L) n (l + 1)
              (canonical_map (F := boundedTermChain (L := L) n (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedTermChain (L := L) n (l + 1)) x j]
          _ = boundedTermComparison (L := L) n (l + 1) u₁ := by rw [hx']
          _ = ⟨t, hts.1⟩ := hu₁
      have hty :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) = ⟨s, hts.2⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedTermChain (L := L) n 0) y i]
          _ = boundedTermComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨s, hts.2⟩ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j) = ⟨t, hts.1⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i) = ⟨s, hts.2⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using hty
      have htxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j)).1 = t := by
        simpa using congrArg Subtype.val htx'
      have htyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)).1 = s := by
        simpa using congrArg Subtype.val hty'
      have htxt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := boundedTermChain (L := L) n (l + 1)) x j).1 = t := by
        simpa using htxv
      have htys :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i).1 = s := by
        simpa using htyv
      apply Subtype.ext
      simpa [boundedTermComparison, coconeOfBoundedTermLInfty, bd_app] using And.intro htxt htys
termination_by
  n l t => sizeOf t.1
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boundedTermComparison_bijective {L : Language.{u}} (n l : Nat) :
    Function.Bijective (@boundedTermComparison L n l) := by
  refine ⟨?_, ?_⟩
  · unfold boundedTermComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfBoundedTermLInfty]
    exact Lhom.on_bounded_term_inj (canonicalMap_inj (L := L) i)
  · intro t
    exact boundedTermComparison_surjective t

private theorem boundedFormulaComparison_surjective {L : Language.{u}} :
    {n l : Nat} → (f : bounded_preformula (LInfty L) n l) →
      ∃ x : colimit (boundedFormulaChain (L := L) n l), boundedFormulaComparison n l x = f
  | n, _, ⟨.falsum, _⟩ => by
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) 0 (bd_falsum), ?_⟩
      apply Subtype.ext
      rfl
  | n, _, ⟨.equal t₁ t₂, hts⟩ => by
      rcases boundedTermComparison_surjective ⟨t₁, hts.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedTermComparison_surjective ⟨t₂, hts.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
        (bd_equal (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)
          (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedTermChain (L := L) n 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedTermChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have htx :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)) = ⟨t₁, hts.1⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedTermChain (L := L) n 0) x j]
          _ = boundedTermComparison (L := L) n 0 u₁ := by rw [hx']
          _ = ⟨t₁, hts.1⟩ := hu₁
      have hty :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) = ⟨t₂, hts.2⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedTermChain (L := L) n 0) y i]
          _ = boundedTermComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨t₂, hts.2⟩ := hu₂
      have htx' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j) = ⟨t₁, hts.1⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using htx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i) = ⟨t₂, hts.2⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using hty
      have htxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j)).1 = t₁ := by
        simpa using congrArg Subtype.val htx'
      have htyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)).1 = t₂ := by
        simpa using congrArg Subtype.val hty'
      have htxt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_r (F := boundedTermChain (L := L) n 0) x j).1 = t₁ := by
        simpa using htxv
      have htyt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i).1 = t₂ := by
        simpa using htyv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_equal] using
        And.intro htxt htyt
  | n, l, ⟨.rel R, _⟩ => by
      rcases germ_rep R with ⟨⟨i, x⟩, hx⟩
      change (chainObjects L i).relations l at x
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n l) i (bd_rel x), ?_⟩
      have hx' : (canonicalMap (L := L) i).on_relation x = R := by
        simpa [canonicalMap, canonical_map_language] using hx
      apply Subtype.ext
      simp [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_rel, hx']
  | n, l, ⟨.apprel f t, hft⟩ => by
      rcases boundedFormulaComparison_surjective ⟨f, hft.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedTermComparison_surjective ⟨t, hft.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n l) (i + j)
        (bd_apprel (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)
          (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedTermChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          boundedFormulaComparison (L := L) n (l + 1)
            (canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) (i + j)
              (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)) = ⟨f, hft.1⟩ := by
        calc
          boundedFormulaComparison (L := L) n (l + 1)
              (canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) (i + j)
                (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)) =
            boundedFormulaComparison (L := L) n (l + 1)
              (canonical_map (F := boundedFormulaChain (L := L) n (l + 1)) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedFormulaChain (L := L) n (l + 1)) x j]
          _ = boundedFormulaComparison (L := L) n (l + 1) u₁ := by rw [hx']
          _ = ⟨f, hft.1⟩ := hu₁
      have hty :
          boundedTermComparison (L := L) n 0
            (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) = ⟨t, hft.2⟩ := by
        calc
          boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)) =
            boundedTermComparison (L := L) n 0
              (canonical_map (F := boundedTermChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedTermChain (L := L) n 0) y i]
          _ = boundedTermComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨t, hft.2⟩ := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j) = ⟨f, hft.1⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hfx
      have hty' :
          (canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i) = ⟨t, hft.2⟩ := by
        simpa [boundedTermComparison, coconeOfBoundedTermLInfty] using hty
      have hfxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j)).1 = f := by
        simpa using congrArg Subtype.val hfx'
      have htyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i)).1 = t := by
        simpa using congrArg Subtype.val hty'
      have hfxf :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n (l + 1)) x j).1 = f := by
        simpa using hfxv
      have htyt :
          (canonicalMap (L := L) (i + j)).on_term
            (push_to_sum_l (F := boundedTermChain (L := L) n 0) y i).1 = t := by
        simpa using htyv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_apprel] using
        And.intro hfxf htyt
  | n, _, ⟨.imp f₁ f₂, hff⟩ => by
      rcases boundedFormulaComparison_surjective ⟨f₁, hff.1⟩ with ⟨u₁, hu₁⟩
      rcases boundedFormulaComparison_surjective ⟨f₂, hff.2⟩ with ⟨u₂, hu₂⟩
      rcases germ_rep u₁ with ⟨⟨i, x⟩, hx⟩
      rcases germ_rep u₂ with ⟨⟨j, y⟩, hy⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
        (bd_imp (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)
          (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)), ?_⟩
      have hx' :
          canonical_map (F := boundedFormulaChain (L := L) n 0) i x = u₁ := by
        simpa [canonical_map] using hx
      have hy' :
          canonical_map (F := boundedFormulaChain (L := L) n 0) j y = u₂ := by
        simpa [canonical_map] using hy
      have hfx :
          boundedFormulaComparison (L := L) n 0
            (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
              (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)) = ⟨f₁, hff.1⟩ := by
        calc
          boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
                (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)) =
            boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) i x) := by
                rw [← same_fiber_as_push_to_r (F := boundedFormulaChain (L := L) n 0) x j]
          _ = boundedFormulaComparison (L := L) n 0 u₁ := by rw [hx']
          _ = ⟨f₁, hff.1⟩ := hu₁
      have hgy :
          boundedFormulaComparison (L := L) n 0
            (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
              (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)) = ⟨f₂, hff.2⟩ := by
        calc
          boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) (i + j)
                (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)) =
            boundedFormulaComparison (L := L) n 0
              (canonical_map (F := boundedFormulaChain (L := L) n 0) j y) := by
                rw [← same_fiber_as_push_to_l (F := boundedFormulaChain (L := L) n 0) y i]
          _ = boundedFormulaComparison (L := L) n 0 u₂ := by rw [hy']
          _ = ⟨f₂, hff.2⟩ := hu₂
      have hfx' :
          (canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j) = ⟨f₁, hff.1⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hfx
      have hgy' :
          (canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i) = ⟨f₂, hff.2⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hgy
      have hfxv :
          ((canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j)).1 = f₁ := by
        simpa using congrArg Subtype.val hfx'
      have hgyv :
          ((canonicalMap (L := L) (i + j)).on_bounded_formula
            (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i)).1 = f₂ := by
        simpa using congrArg Subtype.val hgy'
      have hfxf :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_r (F := boundedFormulaChain (L := L) n 0) x j).1 = f₁ := by
        simpa using hfxv
      have hgyg :
          (canonicalMap (L := L) (i + j)).on_formula
            (push_to_sum_l (F := boundedFormulaChain (L := L) n 0) y i).1 = f₂ := by
        simpa using hgyv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_imp] using
        And.intro hfxf hgyg
  | n, _, ⟨.all f, hf⟩ => by
      rcases boundedFormulaComparison_surjective ⟨f, hf⟩ with ⟨u, hu⟩
      rcases germ_rep u with ⟨⟨i, x⟩, hx⟩
      refine ⟨canonical_map (F := boundedFormulaChain (L := L) n 0) i (bd_all x), ?_⟩
      have hx' : canonical_map (F := boundedFormulaChain (L := L) (n + 1) 0) i x = u := by
        simpa [canonical_map] using hx
      have hfx :
          boundedFormulaComparison (L := L) (n + 1) 0
            (canonical_map (F := boundedFormulaChain (L := L) (n + 1) 0) i x) = ⟨f, hf⟩ := by
        rw [hx']
        exact hu
      have hfx' : (canonicalMap (L := L) i).on_bounded_formula x = ⟨f, hf⟩ := by
        simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty] using hfx
      have hfxv : ((canonicalMap (L := L) i).on_bounded_formula x).1 = f := by
        simpa using congrArg Subtype.val hfx'
      have hfxf : (canonicalMap (L := L) i).on_formula x.1 = f := by
        simpa using hfxv
      apply Subtype.ext
      simpa [boundedFormulaComparison, coconeOfBoundedFormulaLInfty, bd_all] using hfxf
termination_by
  n l f => sizeOf f.1
decreasing_by
  all_goals
    try simp_wf
    try omega

theorem boundedFormulaComparison_bijective {L : Language.{u}} (n l : Nat) :
    Function.Bijective (@boundedFormulaComparison L n l) := by
  refine ⟨?_, ?_⟩
  · unfold boundedFormulaComparison
    apply universal_map_inj_of_components_inj
    intro i
    dsimp [coconeOfBoundedFormulaLInfty]
    exact Lhom.on_bounded_formula_inj (canonicalMap_inj (L := L) i)
  · intro f
    exact boundedFormulaComparison_surjective f

theorem boundedFormulaComparison'_bijective {L : Language.{u}} :
    Function.Bijective (@boundedFormulaComparison' L) := by
  simpa [boundedFormulaComparison'] using
    (boundedFormulaComparison_bijective (L := L) 1 0)

noncomputable def equivBoundedFormulaComparison {L : Language.{u}} :
    colimit (boundedFormulaChain' (L := L)) ≃ bounded_formula (LInfty L) 1 :=
  Equiv.ofBijective (boundedFormulaComparison' (L := L))
    boundedFormulaComparison'_bijective

@[reducible] def witProperty {L : Language.{u}} (f : bounded_formula L 1) (c : L.constants) :
    sentence L :=
  ⟨(bd_ex f).fst ⟹ subst_formula f.fst (bd_const c).fst 0,
    by
      simpa [bounded_formula_at] using
        (And.intro (bd_ex f).2
          (bounded_formula_at_subst_closed (f := f.fst) (n := 0)
            (s := (bd_const (L := L) (n := 0) c).fst) f.2 (bd_const (L := L) (n := 0) c).2))⟩

def has_enough_constants {L : Language.{u}} (T : Theory L) : Prop :=
  ∃ C : bounded_formula L 1 → L.constants, ∀ f : bounded_formula L 1, T ⊢' witProperty f (C f)

lemma has_enough_constants.intro {L : Language.{u}} (T : Theory L)
    (H : ∀ f : bounded_formula L 1, ∃ c : L.constants, T ⊢' witProperty f c) :
    has_enough_constants T := by
  classical
  choose C hC using H
  exact ⟨C, hC⟩

def henkinTheoryStep {L : Language.{u}} (T : Theory L) : Theory (languageStep L) :=
  Lhom.Theory_induced (inclusion (L := L)) T ∪
    ((fun f : bounded_formula L 1 =>
        witProperty
          (L := languageStep L)
          (Lhom.on_bounded_formula (inclusion (L := L)) f)
          (wit' f)) '' (Set.univ : Set (bounded_formula L 1)))

def henkinTheoryChain {L : Language.{u}} (T : Theory L) :
    (n : Nat) → Theory (chainObjects L n)
  | 0 => T
  | n + 1 => henkinTheoryStep (henkinTheoryChain T n)

/-- The standard existential premise used to show a Henkin witness step is admissible. -/
noncomputable def provable_henkinWitnessBody {L : Language.{u}} {T : Theory L}
    (f : bounded_formula L 1) : T ⊢ bd_ex (bd_imp (bounded_preformula.cast1 (bd_ex f)) f) := by
  change Theory.fst T ⊢ ((bd_ex (bd_imp (bounded_preformula.cast1 (bd_ex f)) f) : sentence L) : formula L)
  apply prf.falsumE
  apply prf.impE (bd_ex f : formula L)
  · apply prf.impI
    apply prf.impE _ axm2
    apply exE axm1
    apply exI (&0 : term L)
    rw [lift_subst_formula_cancel]
    apply prf.impI
    exact axm2
  · apply prf.falsumE
    apply prf.impE _ axm2
    apply exI (&0 : term L)
    apply prf.impI
    apply exfalso
    apply prf.impE _ axm2
    let Γ' : Set (formula L) :=
      insert (((bd_ex f : sentence L) : formula L) ⟹ (⊥ : formula L))
        (insert ((((bd_ex (bd_imp (bounded_preformula.cast1 (bd_ex f)) f) : sentence L) : formula L) ⟹
            (⊥ : formula L))) T.fst)
    have hax :
        insert (subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0) Γ' ⊢
          subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0 := by
      exact prf.axm (by simp [Γ'])
    have hEq :
        subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0 = (bd_ex f : formula L) := by
      simpa [bounded_preformula.cast1_fst] using subst_sentence_irrel (bd_ex f) (&0 : term L)
    exact cast
      (congrArg
        (fun A : formula L =>
          insert (subst_formula (bounded_preformula.cast1 (bd_ex f)).fst (&0 : term L) 0) Γ' ⊢ A)
        hEq)
      hax

lemma wit_not_mem_range_inclusion {L : Language.{u}} (f : bounded_formula L 1) :
    wit' f ∉ Set.range (@Lhom.on_function _ _ (inclusion (L := L)) 0) := by
  rintro ⟨c, hc⟩
  cases hc

lemma wit_not_mem_symbols_witnessBody {L : Language.{u}} (ψ ψ' : bounded_formula L 1) :
    (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∉
      symbols_in_formula (Lhom.on_bounded_formula (inclusion (L := L)) ψ').fst := by
  exact Lhom.not_mem_function_in_formula_on_formula
    (ϕ := inclusion (L := L)) (wit_not_mem_range_inclusion (L := L) ψ) (ψ' : formula L)

lemma wit_not_mem_symbols_witProperty_of_ne {L : Language.{u}} {ψ ψ' : bounded_formula L 1}
    (hneq : ψ' ≠ ψ) :
    (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∉
      symbols_in_formula
        ((witProperty
          (L := languageStep L)
          (Lhom.on_bounded_formula (inclusion (L := L)) ψ')
          (wit' ψ') : sentence (languageStep L)) : formula (languageStep L)) := by
  intro hs
  dsimp [witProperty] at hs
  rcases hs with hs | hs
  · exact Lhom.not_mem_function_in_formula_on_formula
      (ϕ := inclusion (L := L)) (wit_not_mem_range_inclusion (L := L) ψ)
      ((bd_ex ψ' : sentence L) : formula L) hs
  · rcases symbols_in_formula_subst
      (f := (Lhom.on_bounded_formula (inclusion (L := L)) ψ').fst)
      (s := (bd_const (wit' ψ')).fst) (n := 0) hs with hsForm | hsTerm
    · exact wit_not_mem_symbols_witnessBody (L := L) ψ ψ' hsForm
    · have hsym :
          (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) =
            Sum.inl ⟨0, wit' ψ'⟩ := by
        have hsTerm' :
            (Sum.inl ⟨0, wit' ψ⟩ : (languageStep L).symbols) ∈
              ({Sum.inl ⟨0, wit' ψ'⟩} : Set (languageStep L).symbols) := by
          simpa [bd_const, bd_func] using hsTerm
        exact Set.mem_singleton_iff.mp hsTerm'
      have hwit : wit' ψ = wit' ψ' := by
        have hpairs :
            ((⟨0, wit' ψ⟩ : Σ n, (languageStep L).functions n)) =
              ⟨0, wit' ψ'⟩ := Sum.inl.inj hsym
        cases hpairs
        rfl
      exact hneq (languageFunctions.wit.inj hwit).symm

def iota {L : Language.{u}} {T : Theory L} (m : Nat) : Theory (LInfty L) :=
  Lhom.Theory_induced (canonicalMap (L := L) m) (henkinTheoryChain T m)

def TInfty {L : Language.{u}} (T : Theory L) : Theory (LInfty L) :=
  ⟨⋃ n : Nat, (iota (T := T) n).carrier⟩

@[reducible] def henkinLanguage {L : Language.{u}} (T : Theory L) : Language.{u} :=
  let _ := T
  LInfty L

def henkinLanguageOver {L : Language.{u}} {T : Theory L} :
    L →ᴸ henkinLanguage (L := L) T := by
  change chainObjects L 0 →ᴸ LInfty L
  exact canonicalMap (L := L) 0

lemma henkinLanguageOver_injective {L : Language.{u}} {T : Theory L} :
    Lhom.is_injective (henkinLanguageOver (L := L) (T := T)) := by
  simpa [henkinLanguageOver] using canonicalMap_inj (L := L) 0

def completeHenkinTheoryOver {L : Language.{u}} (T : Theory L) (hT : is_consistent T) : Type (u + 1) :=
  Σ' T' : Theory_over T hT, has_enough_constants T'.1 ∧ is_complete T'.1

@[reducible] def henkinization {L : Language.{u}} {T : Theory L} (hT : is_consistent T) :
    Theory (henkinLanguage (L := L) T) :=
  let _ := hT
  TInfty T

noncomputable def witInfty {L : Language.{u}} (f : bounded_formula (LInfty L) 1) :
    Σ c : (LInfty L).constants,
      Σ f' : Σ' x : colimit (boundedFormulaChain' (L := L)),
        equivBoundedFormulaComparison (L := L) x = f,
        Σ' f'' : coproduct_of_directed_diagram (boundedFormulaChain' (L := L)),
          (Quotient.mk'' f'' : colimit (boundedFormulaChain' (L := L))) = f'.1 ∧
            c = (canonicalMap (L := L) (f''.1 + 1)).on_function (wit' f''.2) := by
  let f' : Σ' x : colimit (boundedFormulaChain' (L := L)),
      equivBoundedFormulaComparison (L := L) x = f :=
    ⟨(equivBoundedFormulaComparison (L := L)).symm f,
      (equivBoundedFormulaComparison (L := L)).apply_symm_apply f⟩
  let f'' := germ_rep f'.1
  refine ⟨(canonicalMap (L := L) (f''.1.1 + 1)).on_function (wit' f''.1.2), f', f''.1, ?_, rfl⟩
  simpa using f''.2

lemma inIotaOfInStep {L : Language.{u}} {T : Theory L} (i : Nat)
    (f : sentence (chainObjects L (i + 1))) (hf : f ∈ henkinTheoryChain T (i + 1)) :
    Lhom.on_sentence (canonicalMap (L := L) (i + 1)) f ∈ iota (T := T) (i + 1) :=
  Set.mem_image_of_mem _ hf

@[simp] lemma henkinizationIsHenkin {L : Language.{u}} {T : Theory L} (hT : is_consistent T) :
    has_enough_constants (henkinization (L := L) (T := T) hT) := by
  apply has_enough_constants.intro
  intro f
  rcases witInfty (L := L) f with ⟨c, ⟨⟨f', hf'⟩, ⟨⟨i, f''⟩, hrep, hc⟩⟩⟩
  refine ⟨c, ?_⟩
  refine ⟨saxm ?_⟩
  unfold henkinization TInfty
  refine Set.mem_iUnion.mpr ⟨i + 1, ?_⟩
  have hstep :
      witProperty
        (L := chainObjects L (i + 1))
        (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')
        (wit' f'') ∈ henkinTheoryChain T (i + 1) := by
    dsimp [henkinTheoryChain, henkinTheoryStep]
    exact Or.inr (Set.mem_image_of_mem _ (by simp))
  have hstage :
      Lhom.on_bounded_formula (canonicalMap (L := L) i) f'' = f := by
    have hq :
        canonical_map (F := boundedFormulaChain' (L := L)) i f'' =
          (Quotient.mk'' (⟨i, f''⟩ : coproduct_of_directed_diagram (boundedFormulaChain' (L := L))) :
            colimit (boundedFormulaChain' (L := L))) := by
      simpa using
        (canonical_map_quotient (F := boundedFormulaChain' (L := L))
          (⟨i, f''⟩ : coproduct_of_directed_diagram (boundedFormulaChain' (L := L))))
    have hcmp :
        boundedFormulaComparison' (L := L)
          (canonical_map (F := boundedFormulaChain' (L := L)) i f'') = f := by
      rw [hq]
      rw [hrep]
      exact hf'
    simpa [boundedFormulaComparison', boundedFormulaComparison, coconeOfBoundedFormulaPrimeLInfty] using hcmp
  have hsucc : chainMaps L i (i + 1) (by simp) = inclusion (L := chainObjects L i) := by
    have hself : chainMaps L i i (Nat.le_refl i) = Lhom.id (chainObjects L i) := by
      induction i with
      | zero =>
          simp [chainMaps]
      | succ i ih =>
          simp [chainMaps]
    calc
      chainMaps L i (i + 1) (Nat.le_succ i) =
        inclusion (L := chainObjects L i) ∘ᴸ chainMaps L i i (Nat.le_refl i) := by
          have hneq : i ≠ i + 1 := Nat.ne_of_lt (Nat.lt_succ_self i)
          simp [chainMaps, hneq, Lhom.comp]
      _ = inclusion (L := chainObjects L i) := by
          rw [hself]
          simp
  have hstageSucc :
      Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
        (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'') = f := by
    have hcompat :
        Lhom.on_bounded_formula
            ((canonicalMap (L := L) (i + 1)) ∘ᴸ (chainMaps L i (i + 1) (Nat.le_succ i))) f'' =
          Lhom.on_bounded_formula (canonicalMap (L := L) i) f'' := by
      simpa [canonicalMap, coconeOfLInfty, languageChain, Lhom.comp] using
        congrArg
          (fun ϕ => @Lhom.on_bounded_formula _ _ ϕ 1 0 f'')
          ((coconeOfLInfty (L := L)).h_compat (Nat.le_succ i)).symm
    calc
      Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
          (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'') =
        Lhom.on_bounded_formula
          ((canonicalMap (L := L) (i + 1)) ∘ᴸ (inclusion (L := chainObjects L i))) f'' := by
            simp [Lhom.comp]
      _ = Lhom.on_bounded_formula
          ((canonicalMap (L := L) (i + 1)) ∘ᴸ (chainMaps L i (i + 1) (by simp))) f'' := by
            rw [hsucc]
      _ = Lhom.on_bounded_formula (canonicalMap (L := L) i) f'' := by
            exact hcompat
      _ = f := hstage
  have hex :
      (bd_ex
        (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
          (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f''))).fst =
        (bd_ex f).fst := by
    simpa using congrArg (fun g => (bd_ex g).fst) hstageSucc
  have hsub :
      subst_formula
          (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')).fst
          (bd_const (L := LInfty L) (n := 0)
            ((canonicalMap (L := L) (i + 1)).on_function (wit' f''))).fst 0 =
        subst_formula f.fst (bd_const (L := LInfty L) (n := 0) c).fst 0 := by
    calc
      subst_formula
          (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')).fst
          (bd_const (L := LInfty L) (n := 0)
            ((canonicalMap (L := L) (i + 1)).on_function (wit' f''))).fst 0 =
        subst_formula
          (Lhom.on_bounded_formula (canonicalMap (L := L) (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')).fst
          (bd_const (L := LInfty L) (n := 0) c).fst 0 := by
            simp [hc]
      _ = subst_formula f.fst (bd_const (L := LInfty L) (n := 0) c).fst 0 := by
            simpa using congrArg
              (fun g => subst_formula g.fst (bd_const (L := LInfty L) (n := 0) c).fst 0)
              hstageSucc
  have himage :
      Lhom.on_sentence (canonicalMap (L := L) (i + 1))
          (witProperty
            (L := chainObjects L (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')
            (wit' f'')) =
        witProperty (L := LInfty L) f c := by
    apply Subtype.ext
    simpa [witProperty] using And.intro hex hsub
  have hiota :
      Lhom.on_sentence (canonicalMap (L := L) (i + 1))
          (witProperty
            (L := chainObjects L (i + 1))
            (Lhom.on_bounded_formula (inclusion (L := chainObjects L i)) f'')
            (wit' f'')) ∈ (iota (T := T) (i + 1)).carrier := by
    exact inIotaOfInStep (L := L) (T := T) i _ hstep
  rw [himage] at hiota
  exact hiota

lemma henkinTheoryChainInclusionStep {L : Language.{u}} {T : Theory L} {i : Nat}
    {f : sentence (chainObjects L i)} (hf : f ∈ henkinTheoryChain T i) :
    Lhom.on_sentence (inclusion (L := chainObjects L i)) f ∈ henkinTheoryChain T (i + 1) := by
  dsimp [henkinTheoryChain, henkinTheoryStep]
  exact Or.inl (Set.mem_image_of_mem _ hf)

lemma henkinTheoryChainInclusion {L : Language.{u}} {T : Theory L} :
    ∀ {i j : Nat} (h : i ≤ j) {f : sentence (chainObjects L i)},
      f ∈ henkinTheoryChain T i →
        Lhom.on_sentence (chainMaps L i j h) f ∈ henkinTheoryChain T j
  | i, 0, h, f, hf => by
      have hi : i = 0 := Nat.eq_zero_of_le_zero h
      subst hi
      simpa [henkinTheoryChain, chainMaps] using hf
  | i, j + 1, h, f, hf => by
      by_cases hij : i = j + 1
      · subst hij
        simpa [henkinTheoryChain, chainMaps] using hf
      · have hij' : i ≤ j := Nat.lt_succ_iff.mp (lt_of_le_of_ne h hij)
        have ih := henkinTheoryChainInclusion (j := j) hij' hf
        have hmap :
            Lhom.on_sentence (chainMaps L i (j + 1) h) f =
              Lhom.on_sentence (inclusion (L := chainObjects L j))
                (Lhom.on_sentence (chainMaps L i j hij') f) := by
          apply Subtype.ext
          simp [chainMaps, hij, Lhom.comp]
        rw [hmap]
        exact henkinTheoryChainInclusionStep ih

lemma iotaInclusionOfLe {L : Language.{u}} {T : Theory L} :
    ∀ {i j : Nat} (h : i ≤ j), Theory.Subset (iota (T := T) i) (iota (T := T) j)
  | i, j, h => by
      intro ψ hψ
      change ψ ∈
        (Lhom.on_sentence (canonicalMap (L := L) i) ''
          (henkinTheoryChain T i).carrier) at hψ
      rcases hψ with ⟨f, hf, rfl⟩
      refine ⟨Lhom.on_sentence (chainMaps L i j h) f, ?_, ?_⟩
      · exact henkinTheoryChainInclusion (T := T) h hf
      · apply Subtype.ext
        calc
          (Lhom.on_sentence (canonicalMap (L := L) j)
              (Lhom.on_sentence (chainMaps L i j h) f) : sentence (LInfty L)).1 =
              (((canonicalMap (L := L) j) ∘ᴸ (chainMaps L i j h)).on_formula
                (f : formula (chainObjects L i))) := by
                  simp [Lhom.on_sentence_fst, Lhom.on_formula_comp, Lhom.comp]
          _ = (canonicalMap (L := L) i).on_formula (f : formula (chainObjects L i)) := by
                simpa [coconeOfLInfty, canonicalMap, languageChain] using
                  congrArg
                    (fun ϕ => @Lhom.on_formula _ _ ϕ 0 (f : formula (chainObjects L i)))
                    ((coconeOfLInfty (L := L)).h_compat h).symm

end henkin

end Flypitch
