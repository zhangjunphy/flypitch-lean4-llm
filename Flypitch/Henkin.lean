import Flypitch.Colimit
import Flypitch.Completion
import Flypitch.LanguageExtension

universe u v

namespace Flypitch

open fol

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
  ⟨fun {n} f => languageFunctions.inc f, fun {n} R => R⟩

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

end henkin

end Flypitch
