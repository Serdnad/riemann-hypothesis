module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.adicCompletion_ringHom_ext_padicAlgClosure : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (p : ℕ) [Fact p.Prime] (f g : AdicCompletion (maximalIdeal O) O →+* OO p), IsLocalHom (f.comp (algebraMap O _)) → (∀ a, f (algebraMap O _ a) = g (algebraMap O _ a)) → f = g := by
  first | exact @GlobalTheory.AdicExt.completion_ringHom_ext | exact GlobalTheory.AdicExt.completion_ringHom_ext | (intros; apply GlobalTheory.AdicExt.completion_ringHom_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.stalk_noetherian_padicImage_finiteExtension : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ x ∈ U, Algebra.FiniteType ℤ Γ(X, U) → ∀ (p : ℕ) [Fact p.Prime] (φ : X.presheaf.stalk x →+* OO p), IsNoetherianRing (X.presheaf.stalk x) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ a, ((φ a : OO p) : PadicAlgCl p) ∈ K := by
  first | exact @GlobalTheory.stalk_noetherian_and_finite_image | exact GlobalTheory.stalk_noetherian_and_finite_image | (intros; apply GlobalTheory.stalk_noetherian_and_finite_image <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  first | exact @GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | exact GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | (intros; apply GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_unique_stalkHom_padicAlgClosure_valuation : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  first | exact @GlobalTheory.ValPt.exists_unique_stalk_hom | exact GlobalTheory.ValPt.exists_unique_stalk_hom | (intros; apply GlobalTheory.ValPt.exists_unique_stalk_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.modelValue_at_point_of_open_via_spec_subalgebra : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (Rs : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp Rs), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap Rs.val.toRingHom) → ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : Rs →+* K), spMap f = q ≫ u₀ → ∀ a : Rs, M.val (q ≫ U₀.ι) (a : Ω) = f a := by
  first | exact @GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap | exact GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap | (intros; apply GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg

theorem affineFromSpec_comp_eq_specMap_cst {R : Type} [CommRing R] {W : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    V.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (cst f V.1)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) V.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem comap_idealSheaf_pow_eq {X Y : Scheme.{0}} (g : Y ⟶ X) (K : X.IdealSheafData) (k : ℕ) :
    (K ^ k).comap g = (K.comap g) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Scheme.IdealSheafData.comap_top g
  | succ n ih =>
    rw [pow_succ, pow_succ, GlobalTheory.Principalise.comap_mul_idealSheaf, ih]

theorem isIso_pullbackSnd_restrict_preimage {X Y S : Scheme.{0}} (π : X ⟶ S) (g : Y ⟶ S) (U : S.Opens)
    (h : IsIso (π ∣_ U)) : IsIso (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) := by
  have hEq : pullback.fst π g ⁻¹ᵁ π ⁻¹ᵁ U = pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U := by
    show (pullback.fst π g ≫ π) ⁻¹ᵁ U = (pullback.snd π g ≫ g) ⁻¹ᵁ U
    rw [pullback.condition]
  have L : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U).ι (π ⁻¹ᵁ U).ι (pullback.fst π g) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by simpa only [Scheme.Opens.opensRange_ι] using hEq)
  have s := L.paste_vert (IsPullback.of_hasPullback π g)
  have key : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) (π ∣_ U) (g ∣_ U) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict g U)
    · rw [morphismRestrict_ι, morphismRestrict_ι]
      exact s
    · rw [← cancel_mono U.ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
        Scheme.Hom.resLE_comp_ι_assoc, pullback.condition]
  exact key.isIso_snd_of_isIso h

theorem ideal_eq_of_reduces_affine : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t →
    ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) →
    ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  intro R _ I W W' _ f π U hπ hU K hK t ht V
  obtain ⟨hbc, hbs, -⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support
  obtain ⟨hbC, hloc⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus
  haveI : IsNoetherianRing Γ(W, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨C, _, φ, hCn, hφ, hC, hfaith⟩ := GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete Γ(W, V.1) (I.map (cst f V.1))
  haveI := hCn
  haveI := hπ
  have hJjac : (I.map (cst f V.1)).map φ ≤ Ideal.jacobson ⊥ := by
    haveI := hC
    exact IsAdicComplete.le_jacobson_bot _
  haveI hφF : Flat (Spec.map (CommRingCat.ofHom φ)) := AlgebraicGeometry.Flat.SpecMap_iff.mpr hφ
  have hOF : Flat V.2.fromSpec :=
    @HasRingHomProperty.of_isOpenImmersion @Flat RingHom.Flat _ _ _ _ RingHom.Flat.containsIdentities
      V.2.isOpenImmersion_fromSpec
  have hgF : Flat (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) :=
    MorphismProperty.comp_mem @Flat _ _ hφF hOF
  have F1 : ∀ X : W.IdealSheafData, X.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((X.ideal V).map φ) := fun X => hloc W V C φ X
  have F2 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).ideal V = (I.map (cst f V.1)) ^ (e + 1) := by
    intro e
    rw [baseIdeal_ideal, Ideal.map_pow]
  have F4 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, F2, Ideal.map_pow]
  have F5 : ∀ e : ℕ, ((t e).ideal V).map φ = ((t (e + 1)).ideal V).map φ ⊔ ((I.map (cst f V.1)).map φ) ^ (e + 1) := by
    intro e
    conv_lhs => rw [ht e]
    rw [← Ideal.map_pow, ← F2 e, ← Ideal.map_sup]
    rfl
  have F6 := GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals C ((I.map (cst f V.1)).map φ) hC (fun e => ((t e).ideal V).map φ) F5
  have F7 : ∀ e : ℕ, (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, ← (hbC C).2, F6 e]
  have F8 : ∀ e : ℕ, (baseIdeal (π ≫ f) (I ^ (e + 1))).comap
      (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) =
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    have hgf : (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ≫ f =
        Spec.map (CommRingCat.ofHom (φ.comp (cst f V.1))) := by
      rw [Category.assoc, affineFromSpec_comp_eq_specMap_cst, ← Spec.map_comp]
      rfl
    rw [hbc, ← Category.assoc, pullback.condition, Category.assoc, hgf, hbs, ← Ideal.map_map,
      Ideal.map_pow, Ideal.map_pow]
  have hKC : ∀ x, x ∉ (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)).support →
      x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U := by
    intro x hx
    refine hK _ (fun h => hx ?_)
    rw [Scheme.IdealSheafData.support_comap]
    exact h
  have hπC : IsProper (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := inferInstance
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction C ((I.map (cst f V.1)).map φ) hJjac _
    (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) _ hπC
    (isIso_pullbackSnd_restrict_preimage π _ U hU) _
    (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ)) hKC
  refine ⟨k₀, fun k hk T' T'' hT' hT'' e => ?_⟩
  have h1 : ∀ e : ℕ, T'.comap (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ⊔
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1))).comap
        (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := by
    intro e
    have hT'e : T' ⊔ baseIdeal (π ≫ f) (I ^ (e + 1)) = (t e).comap π := hT' e
    rw [← F8 e, ← Scheme.IdealSheafData.comap_sup, hT'e, ← F7 e,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, pullback.condition]
  have h2 : ∀ e : ℕ, T''.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⊔
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) ⊔
        (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ^ k := by
    intro e
    have hT''e : T'' ⊔ baseIdeal f (I ^ (e + 1)) = t e ⊔ K ^ k := hT'' e
    rw [← F4 e, ← Scheme.IdealSheafData.comap_sup, hT''e, Scheme.IdealSheafData.comap_sup, F7 e,
      comap_idealSheaf_pow_eq, F4 e]
  have hmain := hk₀ k hk _ _ h1 h2
  have hX : ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).comap
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) := by
    rw [Scheme.IdealSheafData.comap_sup, GlobalTheory.T.idealSheafData_comap_inf_of_flat _ _ _ hgF,
      GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' _ _ π _ (pullback.fst π _) (pullback.snd π _) (IsPullback.of_hasPullback π _) hgF
        inferInstance, hmain, F4 e, F7 e]
  rw [F1, F1] at hX
  have hX' := (hbC C).1.1 hX
  have hle1 : (I.map (cst f V.1)) ^ (e + 1) ≤ ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp le_sup_right V
  have hle2 : (I.map (cst f V.1)) ^ (e + 1) ≤ (t e).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp (ht.baseIdeal_le e) V
  calc ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V
      = ((((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V).map φ).comap φ := (hfaith _ _ hle1).symm
    _ = ((((t e).ideal V)).map φ).comap φ := by rw [hX']
    _ = (t e).ideal V := hfaith _ _ hle2

end GlobalTheory.FormalAlg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem genLam_pull_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hExt W _ _ _ φ GW _ _ βW βW₂ DW AW UW hW hφ hφl hβ hsqW hPP
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => by
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  let κW : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst _ _ ≫ βW) (pullback.snd _ _ ≫ spMap ga) (by
      rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κW ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := pullback.lift_fst _ _ _
  have w : κW ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GW).hom ≫ spMap ga :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GW) ((Over.pullback (jK R)).obj G) (spMap ga) κW :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GW (jK W)).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK W)).obj GW) := Functor.isCommMonObj_obj
  have : IsMonHom UW.gen.hom := UW.gen_hom
  have : IsMonHom gen.hom := hgen
  have : IsMonHom UW.gen.symm.hom := show IsMonHom UW.gen.inv by infer_instance
  have hu : IsGrpPullback AW.A ((Over.pullback (jK W)).obj GW) (𝟙 _) UW.gen.inv.left :=
    isGrpPullback_of_iso UW.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G) A.A (𝟙 _) gen.hom.left := isGrpPullback_of_iso gen
  have hα : IsGrpPullback AW.A A.A (spMap ga) (UW.gen.inv.left ≫ κW ≫ gen.hom.left) :=
    (hu.comp (hκ.comp hg)).congr (by simp) rfl
  obtain ⟨u₂, squ, Hu⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hu
  obtain ⟨κ₂, sqκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hκ
  obtain ⟨g₂, sqg, Hg⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hg
  obtain ⟨fW₂, sqfW, HfW⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback GW (jK W))
  obtain ⟨fR₂, sqfR, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback G (jK R))
  have hLA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLG : (UW.LG.L.pull (pullback.fst GW.hom (jK W))).IsLB := pull_isLB UW.LG.isLB _
  have hAg : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _

  have Z : LBIso (abelian₂ ((Over.pullback (jK R)).obj G) (A.L.pull gen.hom.left)) ((abelian₂ A.A A.L).pull g₂) := by
    have h := Hg A.L (A.L.pull gen.hom.left) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hAg hLA
      (PolBaseChange.lbIso_refl hAg)
      (LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hLA))
    rwa [Category.comp_id] at h
  have Y : LBIso (PP.pull fR₂) ((abelian₂ A.A A.L).pull g₂) :=
    LBIso.trans (pull_isLB hExt.1 _) (DVR.linComb_isLB _ hAg _ _) (pull_isLB hLA _) (hExt.2 fR₂ sqfR).symm Z
  have e : fW₂ ≫ βW₂ = κ₂ ≫ fR₂ := by
    apply pullback.hom_ext
    · show (fW₂ ≫ βW₂) ≫ (fst G G).left = (κ₂ ≫ fR₂) ≫ (fst G G).left
      simp only [Category.assoc, hsqW.1, sqfR.1]
      rw [← Category.assoc fW₂, sqfW.1, reassoc_of% sqκ.1, hκf, Category.assoc]
    · show (fW₂ ≫ βW₂) ≫ (snd G G).left = (κ₂ ≫ fR₂) ≫ (snd G G).left
      simp only [Category.assoc, hsqW.2, sqfR.2]
      rw [← Category.assoc fW₂, sqfW.2, reassoc_of% sqκ.2, hκf, Category.assoc]
  have B1 : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      (PP.pull (κ₂ ≫ fR₂)) := by
    have h := HfW UW.LG.L (UW.LG.L.pull (pullback.fst GW.hom (jK W))) _ PP βW₂ UW.LG.isLB hLG hExt.1
      (PolBaseChange.lbIso_refl hLG) hPP
    rwa [e] at h
  have B3 : LBIso (PP.pull (κ₂ ≫ fR₂)) ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.chartPull (chartPullSame PP _ (fun _ => fR₂) _ κ₂ fun _ => rfl)
      (chartPullSame (abelian₂ A.A A.L) _ (fun _ => g₂) _ κ₂ fun _ => rfl) Y
  have hLamW : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.trans (DVR.linComb_isLB _ hLG _ _) (pull_isLB hExt.1 _) (pull_isLB hLA _) B1 B3

  have hN : LBIso AW.L ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) := by
    have hext : LBIso (AW.L.pull UW.gen.hom.left) (UW.LG.L.pull (pullback.fst GW.hom (jK W))) := UW.ext
    have h1 : LBIso (AW.L.pull (𝟙 _)) ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) :=
      LBIso.chartPull (chartPullSame AW.L _ (fun _ => UW.gen.hom.left) _ UW.gen.inv.left fun _ => by
          rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left])
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) hext
    have h0 : LBIso AW.L (AW.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl AW.isLB)
    exact LBIso.trans AW.isLB (pull_isLB AW.isLB _) (pull_isLB hLG _) h0 h1
  refine ⟨ga, UW.gen.inv.left ≫ κW ≫ gen.hom.left, u₂ ≫ κ₂ ≫ g₂, hga, hα, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Category.assoc, sqg.1, reassoc_of% sqκ.1, reassoc_of% squ.1]
  · simp only [Category.assoc, sqg.2, reassoc_of% sqκ.2, reassoc_of% squ.2]
  · exact Hu _ AW.L _ (abelian₂ A.A A.L) (κ₂ ≫ g₂) hLG AW.isLB hLA hN hLamW
  · rw [Category.assoc, Category.assoc, ← Category.assoc gen.hom.left, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp, hκf]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Mum.KeepsIota

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_v (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (k : D.X → D.X) (hk : ∀ χ, D.c (k χ) = D.c χ ≫ f)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f := fun T => by
    rw [cP, hk, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k' := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k'
  refine (val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact
  subst hEa hEh
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hs := (endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd
  obtain ⟨ha, ha', -, hc, hc', -⟩ := hd
  obtain ⟨-, -, hr', -, -, hbal'⟩ := hs
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'
  obtain ⟨gb, gv⟩ := (isIota_iff _ _).1 hg
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [hact.1, gb, cP, cP, hc, ← Category.assoc]
  · obtain ⟨v, hv, vv⟩ := exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ
    have k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J := by
      have := vv _ g.b _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at this
      exact (GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this
    rw [hact.2 χ z J hJ, gv _ z J hJ, k1, gb]
    let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)
    have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
        val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J := by
      rw [val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
    rw [← e']
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
      (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

end GlobalTheory.Mum.KeepsIota

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) [IsLocallyNoetherian T.left] (lv : D.La → (T ⟶ o.A)), (∀ x y, lv (x + y) = lv x * lv y) → (∀ x, lv (N' • x) = 1) → (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) → ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ T.left) (x' : Sp k' ⟶ T.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ((∃ I : TateIsoO D k (Over.mk (x ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y) ↔ (∃ I : TateIsoO D k' (Over.mk (x' ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x' rfl : Over.mk (x' ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y)) := by
  first | exact @GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes | exact GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes | (intros; apply GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes; all_goals assumption)
end
