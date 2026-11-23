module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle218
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

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

namespace GlobalTheory

theorem stalk_noetherian_and_finite_image :
    ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ x ∈ U, Algebra.FiniteType ℤ Γ(X, U) → ∀ (p : ℕ) [Fact p.Prime] (φ : X.presheaf.stalk x →+* OO p), IsNoetherianRing (X.presheaf.stalk x) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ a, ((φ a : OO p) : PadicAlgCl p) ∈ K := by
  intro X U hU x hx hft p _ φ
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hU.isLocalization_stalk ⟨x, hx⟩
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℤ Γ(X, U)
  refine ⟨IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ this, ?_⟩
  let ψ : X.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ
  let f : Γ(X, U) →+* PadicAlgCl p := ψ.comp (algebraMap Γ(X, U) (X.presheaf.stalk x))
  obtain ⟨s, hs⟩ := hft.out
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    IntermediateField.adjoin ℚ_[p] ((s.image f : Finset (PadicAlgCl p)) : Set (PadicAlgCl p))
  refine ⟨K, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin (fun y _ => Algebra.IsIntegral.isIntegral y)
  · have hgen : ∀ r : Γ(X, U), f r ∈ K := by
      intro r
      have hr : r ∈ Algebra.adjoin ℤ (s : Set Γ(X, U)) := by rw [hs]; trivial
      induction hr using Algebra.adjoin_induction with
      | mem y hy =>
        apply IntermediateField.subset_adjoin
        simp only [Finset.coe_image]
        exact Set.mem_image_of_mem f hy
      | algebraMap n =>
        have : f (algebraMap ℤ Γ(X, U) n) = (n : PadicAlgCl p) := by simp
        rw [this]; exact K.intCast_mem n
      | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
    intro a
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl a
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk x) r t
    have hunit : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) t) := IsLocalization.map_units _ t
    have hne : f t ≠ 0 := (hunit.map ψ).ne_zero
    have heq : ψ (IsLocalization.mk' (X.presheaf.stalk x) r t) =
        f r * (f t)⁻¹ := by
      have h2 := congrArg ψ hspec
      rw [map_mul] at h2
      change ψ _ * f t = f r at h2
      rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hne, _root_.mul_one]
    change ψ _ ∈ K
    rw [heq]
    exact K.mul_mem (hgen r) (K.inv_mem (hgen t))

end GlobalTheory
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

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_eq_of_spMap : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (Rs : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp Rs), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap Rs.val.toRingHom) → ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : Rs →+* K), spMap f = q ≫ u₀ → ∀ a : Rs, M.val (q ≫ U₀.ι) (a : Ω) = f a := by
  intro o Ω _ _ _ M U₀ Rs u₀ hne hpt K _ q f hf a
  set s : Γ(U₀.toScheme, ⊤) :=
    (u₀.appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) with hs
  set t : Γ(M.Z, U₀.ι ''ᵁ ⊤) := (U₀.ι.appIso ⊤).inv.hom s with ht
  have key : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      valF (y ≫ U₀.ι) (U₀.ι ''ᵁ ⊤) t = valR (y ≫ u₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) := by
    intro C _ y
    rw [GlobalTheory.Points.valF_eq_valR, ← GlobalTheory.Points.valR_appLE y U₀.ι (U₀.ι.preimage_image_eq ⊤).ge
      (GlobalTheory.Points.le_preimage_top y), ← Scheme.Hom.appIso_hom', ht, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply, hs]
    exact GlobalTheory.Points.valR_appLE y u₀ _ (GlobalTheory.Points.le_preimage_top y) _
  have hW : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      Set.range (y ≫ U₀.ι) ⊆ ((U₀.ι ''ᵁ ⊤ : M.Z.Opens) : Set M.Z) := by
    intro C _ y
    rw [Scheme.Opens.ι_image_top, ← Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ⟨y w, rfl⟩
  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact M.top_le_preimage_pt hne (x := w) trivial
  have hx : IsOpenImmersion.lift U₀.ι M.pt hrange ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have h1 := hpt _ hx
  have e1 : valF M.pt (U₀.ι ''ᵁ ⊤) t = (a : Ω) := by
    rw [← hx, key, h1, GlobalTheory.Points.valR_specMap]
    rfl
  rw [RatModel.val_eq (hW q) e1, key, ← hf, GlobalTheory.Points.valR_specMap]
  rfl

end GlobalTheory.Poinc.TestAtPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjModelSurj

theorem surjective_of_isProjOver (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z)
    (hf : X.IsHom M (AlgHom.id o Ω) f) (hM : IsProjOver M.s) : Function.Surjective f := by
  obtain ⟨N, i, hi, hs⟩ := hM
  haveI : IsProper (PSpace.str o N) := isProper_str o N
  haveI : IsProper M.s := hs ▸ inferInstance
  haveI : IsSeparated X.s := X.sep
  haveI : IsProper (f ≫ X.s) := by rw [hf.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsProper f := IsProper.of_comp f X.s
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hgen : genericPoint X.Z ∈ Set.range f := by
    have w : Sp Ω := IsLocalRing.closedPoint Ω
    refine ⟨M.pt w, ?_⟩
    have h : (M.pt ≫ f) w = (spMap (AlgHom.id o Ω).toRingHom ≫ X.pt) w := by rw [hf]
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact X.pt_apply _
  intro x
  obtain ⟨y, hy⟩ := (genericPoint_specializes x).mem_closed hcl hgen
  exact ⟨y, hy⟩

end GlobalTheory.ProjModelSurj
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

theorem GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro p _ V _ _ _ i hloc hi x
  have hV : ValuationRing V := inferInstance
  constructor
  · intro hx
    by_contra hnot
    have hx0 : x ≠ 0 := fun h => hnot ⟨0, by simp [h]⟩
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨a, ha⟩ | ⟨w, hw⟩
    · exact hnot ⟨a, ha⟩
    · have hwu : ¬ IsUnit w := by
        intro hu
        apply hnot
        refine ⟨(hu.unit⁻¹ : Vˣ), ?_⟩
        have h1 : algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ) * algebraMap V (FractionRing V) w = 1 := by
          rw [← map_mul]; simp
        rw [hw] at h1
        exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv x)
      have hiw : ¬ IsUnit (i w) := fun h => hwu (IsLocalHom.map_nonunit w h)
      have hlt : ‖((i w : OO p) : PadicAlgCl p)‖ < 1 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 hiw
      have hlw : IsFractionRing.lift (K := FractionRing V) hi x⁻¹ = ((i w : OO p) : PadicAlgCl p) := by
        rw [← hw, IsFractionRing.lift_algebraMap]; rfl
      have hprod : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖IsFractionRing.lift (K := FractionRing V) hi x⁻¹‖ = 1 := by
        rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
      rw [hlw] at hprod
      have : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖((i w : OO p) : PadicAlgCl p)‖ < 1 :=
        calc _ ≤ 1 * ‖((i w : OO p) : PadicAlgCl p)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [_root_.one_mul]; exact hlt
      linarith
  · rintro ⟨v, rfl⟩
    rw [IsFractionRing.lift_algebraMap]
    exact (GlobalTheory.ZH.mem_OO_iff _).1 (i v).2
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

namespace GlobalTheory.ValPt

theorem exists_unique_stalk_hom : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  intro X x p _ y hy
  subst hy
  refine ⟨(Scheme.stalkClosedPointTo y).hom, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y, ?_⟩
  intro g hg
  have hpt : (X.fromSpecStalk (y (cPt p))) ((spMap g) (cPt p)) =
      (X.fromSpecStalk (y (cPt p))) (closedPoint (X.presheaf.stalk (y (cPt p)))) := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact congrArg (fun f : Sp (OO p) ⟶ X => f (cPt p)) hg
  have hinj : Function.Injective (X.fromSpecStalk (y (cPt p))) :=
    (X.fromSpecStalk (y (cPt p))).isEmbedding.injective
  have hloc : IsLocalHom g := by
    rw [isLocalHom_iff_comap_closedPoint]
    exact hinj hpt
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of (OO p))).symm.injective
    (a₁ := ⟨y (cPt p), CommRingCat.ofHom g, hloc⟩)
    (a₂ := ⟨y (cPt p), Scheme.stalkClosedPointTo y, inferInstance⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
        exact hg.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at e3
  exact congrArg CommRingCat.Hom.hom e3

end GlobalTheory.ValPt
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

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_gPt_of_stalk : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsLocalHom j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ c : M.O x, ((ev (j ((M.stalkEquiv x).symm c)) : OO p) : PadicAlgCl p) = M.val (gPt p ≫ y) (c : Ω) := by
  intro o Ω _ _ _ M x R _ _ j _ p _ y ev hy c
  have hsp : ∀ w, (spMap j ≫ M.Z.fromSpecStalk x) w ⤳ x := fun w => by
    have : M.Z.fromSpecStalk x (spMap j w) ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  obtain ⟨U, hx, f, hf⟩ := M.Z.presheaf.germ_exist ((M.stalkEquiv x).symm c)
  have hc : c = ⟨valF M.pt U f, RatModel.valF_mem_O hx f⟩ := by
    rw [← RatModel.stalkEquiv_germ hx, hf, RingEquiv.apply_symm_apply]
  have hU : ⊤ ≤ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ U := fun w _ => (hsp w).mem_open U.isOpen hx
  have hU0 : ⊤ ≤ M.Z.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : M.Z.fromSpecStalk x w ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hx
  have hg : gPt p ≫ y = spMap ((OO p).subtype.comp ev) ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [← hy, ← Category.assoc]
    congr 1
    change spMap (OO p).subtype ≫ spMap ev = spMap ((OO p).subtype.comp ev)
    rw [spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hU' : ⊤ ≤ (gPt p ≫ y) ⁻¹ᵁ U := by
    rw [hg]; exact fun w _ => hU (x := spMap ((OO p).subtype.comp ev) w) trivial
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hU') (f := f) (hc ▸ rfl), GlobalTheory.Points.valF_eq_valR, hg,
    GlobalTheory.Points.valR_spMap_comp _ _ U hU]
  have e1 : valR (spMap j ≫ M.Z.fromSpecStalk x) U f = j (valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f) :=
    GlobalTheory.Points.valR_spMap_comp (C := M.Z.presheaf.stalk x) j (M.Z.fromSpecStalk x) U hU0 f
  have e2 : valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f = M.Z.presheaf.germ U x hx f := by
    have eA : (M.Z.fromSpecStalk x).appLE U ⊤ hU0 =
        M.Z.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (M.Z.presheaf.stalk x)).inv := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
      simp only [Category.assoc, ← Functor.map_comp]
      have e : ((homOfLE le_top).op ≫ (homOfLE hU0).op :
          Opposite.op (⊤ : (Spec (M.Z.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
      rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
    unfold valR
    erw [dite_eq_left hU0, eA]
    simp only [CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
    rfl
  rw [e1]
  exact (congrArg (fun t => ((OO p).subtype.comp ev) (j t)) (e2.trans hf)).symm

end GlobalTheory.Poinc.TestAtPt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo


theorem _root_.GlobalTheory.T.frame_conjugate_embedding_eq_conj_mul_unitary : ∀ (K : Type) [Field K] (N : ℕ) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.ChowHt.ConjCompat A → (∀ σ, (A σ).det ≠ 0) →
    ∀ σ : K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U := by
  first | exact @GlobalTheory.ConjUnitary.conj_frame_unitary | exact GlobalTheory.ConjUnitary.conj_frame_unitary | (intros; apply GlobalTheory.ConjUnitary.conj_frame_unitary <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq : ∀ (R : Type) [CommRing R] (J : Ideal R) (W T Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : T ⟶ W) (j : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsClosedImmersion i → IsClosedImmersion j → j ≫ f = q ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ((∃ b : Y ⟶ T, b ≫ i = j ∧ IsPullback b q (i ≫ f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) ↔ i.ker ⊔ baseIdeal f J = j.ker) := by
  first | exact @GlobalTheory.FormalAlg.reduces_iff_ker_eq | exact GlobalTheory.FormalAlg.reduces_iff_ker_eq | (intros; apply GlobalTheory.FormalAlg.reduces_iff_ker_eq <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  first | exact @GlobalTheory.FormalAlg.map_inf_eq_of_reductions | exact GlobalTheory.FormalAlg.map_inf_eq_of_reductions | (intros; apply GlobalTheory.FormalAlg.map_inf_eq_of_reductions <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.isClosedImmersion_of_proper_closedImmersion_mod_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  first | exact @GlobalTheory.ClosedLev.isClosedImmersion_of_mod | exact GlobalTheory.ClosedLev.isClosedImmersion_of_mod | (intros; apply GlobalTheory.ClosedLev.isClosedImmersion_of_mod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.rosati_condition_descends_galois_cover : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  first | exact @GlobalTheory.RosatiDescent.lbIso_act_descent | exact GlobalTheory.RosatiDescent.lbIso_act_descent | (intros; apply GlobalTheory.RosatiDescent.lbIso_act_descent; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.Mum.PosMult

theorem eventually_relAmple : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (a : P.A ⟶ P.A), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]) := by
  intro R _ P a
  have := P.isAb.proper
  have hL := P.isLB
  have hA : IsAmpleLB P.L := isAmpleLB_of_relAmple_of_isAffine P.A hL P.ample
  have hNb : (LB.LinComb P.L (K := Fin 1) ![a.left] ![-1]).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hA.eventually_isAmpleLB_tens_lbPow_succ hNb)
  refine ⟨n₀ + 1, fun N hN => ?_⟩
  have key := hn₀ (N - 1) (by omega)
  have hN1 : N - 1 + 1 = N := by omega
  rw [hN1] at key
  have hM := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM]
  refine key.of_lbIso hM ((cls_eq_iff hM (isLB_tens hNb (isLB_lbPow hL N))).1 ?_)
  rw [cls_tens hNb (isLB_lbPow hL N), cls_lbPow hL, cls_linComb hL, cls_linComb hL]
  simp [Fin.sum_univ_two, pull_id]
  abel

theorem exists_pos_mult : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ RelAmple D.toPre.P.A (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) ∧ ∀ (κ : D.toPre.X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR D a a' h h' _
  obtain ⟨N₀, hN₀⟩ := eventually_relAmple R D.toPre.P a
  obtain ⟨C, hC⟩ := GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound D.toPre.X h h'
  refine ⟨max N₀ (C + 1), le_trans (by omega) (le_max_right _ _), hN₀ _ (le_max_left _ _), ?_⟩
  exact GlobalTheory.T.exists_pow_eq_mul_of_quadraticBound_normalLocal R hR D.toPre.X h h' C hC _ (le_max_right _ _)

end GlobalTheory.Mum.PosMult
end
