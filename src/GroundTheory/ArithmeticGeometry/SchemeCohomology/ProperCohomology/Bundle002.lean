module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.ReesAlgebra
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

lemma isIso_opens_ι_restrict {Z : Scheme.{u}} (O : Z.Opens) : IsIso (O.ι ∣_ O) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply le_antisymm le_top
  intro x _
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change O.ι x ∈ O
    exact x.2
  · apply Subtype.ext
    exact morphismRestrict_base_coe O.ι O ⟨x, _⟩

theorem exists_irreducible_isIso_restrict (Z : Scheme.{u}) [IsNoetherian Z] [Nonempty Z] :
    ∃ (Z₁ : Scheme.{u}) (c : Z₁ ⟶ Z) (O : Z.Opens), IsClosedImmersion c ∧ IrreducibleSpace Z₁ ∧
      (O : Set Z).Nonempty ∧ IsIso (c ∣_ O) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hC := irreducibleComponent_mem_irreducibleComponents z
  set C := irreducibleComponent z
  set O := Z.irreducibleComponentOpen C
  refine ⟨Z.irreducibleComponent C hC, Z.irreducibleComponentι C hC, O, inferInstance,
    inferInstance, ?_, ?_⟩
  · obtain ⟨o, ho, hne, hoC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC

    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents C hC
    have : (O : Set Z) = (⋃₀ (irreducibleComponents Z \ {C}))ᶜ := rfl
    rw [this, Set.compl_empty_iff] at h
    rw [h, Set.compl_univ, closure_empty] at hcl
    exact hC.1.nonempty.ne_empty hcl.symm
  · have hI := Z.irreducibleComponentIdeal_def C hC
    have : IsIso (O.ι ∣_ O) := isIso_opens_ι_restrict O
    have key := SchemeImage.imageRestrictLift_fac O.ι O
    change IsIso ((Z.irreducibleComponentIdeal C hC).subschemeι ∣_ O)
    rw [hI]
    change IsIso (O.ι.imageι ∣_ O)
    rw [← key]
    infer_instance

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

section Schemes

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]

abbrev reesStructure : Spec (.of (reesAlgebra I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (reesAlgebra I)))

abbrev reesPolyStructure : Spec (.of (Polynomial A)) ⟶ Spec (.of (reesAlgebra I)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)))

def reesScheme : Scheme.{u} := pullback (X ↘ Spec (.of A)) (reesStructure I)

def reesPr : reesScheme I X ⟶ X := pullback.fst _ _

def reesSnd : reesScheme I X ⟶ Spec (.of (reesAlgebra I)) := pullback.snd _ _

lemma isPullback_rees :
    IsPullback (reesPr I X) (reesSnd I X) (X ↘ Spec (.of A)) (reesStructure I) :=
  IsPullback.of_hasPullback _ _

instance : (reesScheme I X).Over (Spec (.of (reesAlgebra I))) := ⟨reesSnd I X⟩

instance : IsAffineHom (reesPr I X) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance

instance [IsProper (X ↘ Spec (.of A))] :
    IsProper (reesScheme I X ↘ Spec (.of (reesAlgebra I))) := by
  change IsProper (pullback.snd (X ↘ Spec (.of A)) (reesStructure I))
  infer_instance

def reesPolyScheme : Scheme.{u} := pullback (reesSnd I X) (reesPolyStructure I)

def reesPolyMap : reesPolyScheme I X ⟶ reesScheme I X := pullback.fst _ _

def reesPolySnd : reesPolyScheme I X ⟶ Spec (.of (Polynomial A)) := pullback.snd _ _

lemma isPullback_reesPoly :
    IsPullback (reesPolyMap I X) (reesPolySnd I X) (reesSnd I X) (reesPolyStructure I) :=
  IsPullback.of_hasPullback _ _

instance : IsAffineHom (reesPolyMap I X) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance

end Schemes

section Rings

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]


variable (X) in
def algV (V : X.Opens) : A →+* Γ(X, V) :=
  ((X ↘ Spec (.of A)).appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

variable (I) in
def reesInr (V : X.Opens) : CommRingCat.of (reesAlgebra I) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) :=
  (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv ≫ (reesSnd I X).appLE ⊤ _ le_top


variable (I) in
def polyInr (V : X.Opens) : CommRingCat.of (Polynomial A) ⟶
    Γ(reesPolyScheme I X, reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) :=
  (Scheme.ΓSpecIso (.of (Polynomial A))).inv ≫ (reesPolySnd I X).appLE ⊤ _ le_top


theorem isPushout_rees {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (CommRingCat.ofHom (algV X V)) (CommRingCat.ofHom (algebraMap A (reesAlgebra I)))
      ((reesPr I X).app V) (reesInr I V) := by
  refine (isPushout_app_of_isPullback (isPullback_rees I X) hV).of_iso
    (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of (reesAlgebra I))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [algV]
  · exact Scheme.ΓSpecIso_naturality _
  · simp
  · simp [reesInr]


theorem isPushout_reesPoly {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (CommRingCat.ofHom (algV X V)) (CommRingCat.ofHom (Polynomial.C))
      ((reesPr I X).app V ≫ (reesPolyMap I X).app _) (polyInr I V) := by
  have h1 := (isPushout_app_of_isPullback (isPullback_rees I X) hV).flip
  have h2 := (isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).flip
  have h := (h1.paste_horiz h2).flip
  refine h.of_iso (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of (Polynomial A)))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [algV]
  · rw [Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.ΓSpecIso_naturality,
      Category.assoc]
    rfl
  · simp
  · simp [polyInr]

end Rings

end

end GroundTheory.Arith.SchemeCoh
end
