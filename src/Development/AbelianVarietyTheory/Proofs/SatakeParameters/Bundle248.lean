module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle026
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle394
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped GlobalTheory.ProjSpace
namespace GlobalTheory.PD.XCover.Integ
attribute [local instance] MvPolynomial.gradedAlgebra
variable {d : ℕ}

theorem ratioSec_eq_ratio (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  rw [ratioSec, GlobalTheory.ProjFrac.awayToSection_mk]
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem basicOpen_ratioSec (a i : Fin (d + 1)) :
    (PSpace ℂ d).basicOpen (ratioSec d a i) = chart d a ⊓ chart d i := by
  rw [ratioSec_eq_ratio]
  exact GlobalTheory.ProjSpace.basicOpen_ratioOn

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem basicOpen_prod (φ : Z ⟶ PSpace ℂ d) (a : Fin (d + 1)) (T : Finset (Fin (d + 1))) :
    Z.basicOpen (φ.app (chart d a) (∏ i ∈ T, ratioSec d a i)) =
      φ ⁻¹ᵁ chart d a ⊓ T.inf fun i => φ ⁻¹ᵁ chart d i := by
  rw [← Scheme.preimage_basicOpen]
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one, Finset.inf_empty, inf_top_eq]
  | insert j T hj ih =>
    rw [Finset.prod_insert hj, Scheme.basicOpen_mul, Scheme.Hom.preimage_inf, ih, basicOpen_ratioSec,
      Scheme.Hom.preimage_inf, Finset.inf_insert, inf_inf_inf_comm, inf_idem]

theorem rat_eq (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1)) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (ratioSec d a j)) := by
  rw [rat, dite_eq_left ha]

theorem germ_const (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (c : ℂ) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (algebraMap ℂ Γ(PSpace ℂ d, chart d a) c)) =
      algebraMap ℂ Z.functionField c := by
  subst hinst hφ
  rw [GlobalTheory.ProjSpace.algebraMap_sections_eq]
  simp only [Scheme.Hom.appLE, ffAlg, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Hom.comp_appTop]
  generalize (CommRingCat.Hom.hom (Scheme.Hom.app (PSpace.str ℂ d) ⊤))
    ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv) c) = w
  have e := ConcreteCategory.congr_hom (φ.naturality (homOfLE (le_top : chart d a ≤ ⊤)).op) w
  simp only [ConcreteCategory.comp_apply] at e
  erw [e, TopCat.Presheaf.germ_res_apply]
  rfl

theorem germ_mem_adjoin (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (t : Γ(PSpace ℂ d, chart d a)) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) t) ∈
      Algebra.adjoin ℂ (Set.range (rat φ a)) := by
  obtain ⟨q, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d a t
  induction q using MvPolynomial.induction_on with
  | C c => rw [aeval_C, germ_const p hinst φ hφ a ha c]; exact Subalgebra.algebraMap_mem _ c
  | add q r hq hr => rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact add_mem hq hr
  | mul_X q j hq =>
    rw [map_mul, map_mul, map_mul, aeval_X, ← ratioSec_eq_ratio, ← rat_eq φ a j ha]
    exact mul_mem hq (Algebra.subset_adjoin ⟨j, rfl⟩)

theorem rat_eq_crd [Algebra ℂ Z.functionField] (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1))
    (h0 : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = algebraMap (fld φ) Z.functionField (crd φ j / crd φ a) := by
  rw [map_div₀]
  exact (rat_overlap d Z φ 0 a j h0 ha).2

end GlobalTheory.PD.XCover.Integ


open GlobalTheory.PD.XCover.Integ in
theorem GlobalTheory.PD.XCover.germ_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  intro d Z _ p _ inst hinst φ _ hφ hgen I hI h f
  obtain ⟨a, ha⟩ := hI
  have hV : IsAffineOpen (chart d a) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d a
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d a) := hV.preimage φ
  have hsub : Algebra.adjoin ℂ (Set.range (rat φ a)) ≤
      (rA ℂ (crd φ) I).map (IsScalarTower.toAlgHom ℂ (fld φ) Z.functionField) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨crd φ j / crd φ a, Algebra.subset_adjoin ⟨a, ha, j, rfl⟩, (rat_eq_crd φ a j (hgen 0) (hgen a)).symm⟩
  have hint : ∀ y : Γ(Z, φ ⁻¹ᵁ chart d a),
      IsIntegral (rA ℂ (crd φ) I) ((Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y) := by
    intro y
    obtain ⟨P, hPm, hP⟩ := IsIntegralHom.isIntegral_app φ _ hV y
    set G := (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom
    have hlift : P.map (G.comp (φ.app (chart d a)).hom) ∈
        Polynomial.lifts (algebraMap (rA ℂ (crd φ) I) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨x, hx, hxy⟩ := hsub (germ_mem_adjoin p hinst φ hφ a (hgen a) (P.coeff n))
      exact ⟨⟨x, hx⟩, hxy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hPm.map _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, hP, map_zero]
  set s := φ.app (chart d a) (∏ i ∈ I, ratioSec d a i) with hs
  have hbo : Z.basicOpen s = I.inf fun i => φ ⁻¹ᵁ chart d i := by
    rw [hs, basicOpen_prod]
    exact inf_eq_right.2 (Finset.inf_le (f := fun i => φ ⁻¹ᵁ chart d i) ha)
  have hgs : (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom s = ∏ i ∈ I, rat φ a i := by
    rw [hs, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => (rat_eq φ a i (hgen a)).symm
  have hinv : (∏ i ∈ I, rat φ a i)⁻¹ = algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i) := by
    rw [map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [rat_eq_crd φ a i (hgen 0) (hgen a), ← map_inv₀, inv_div]
  have hne : (∏ i ∈ I, rat φ a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (rat_overlap d Z φ a i i (hgen a) (hgen i)).1
  suffices H : ∀ (W : Z.Opens) (hW : W = Z.basicOpen s) (h : genericPoint Z ∈ W) (f : Γ(Z, W)),
      (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I from H _ hbo.symm h f
  rintro W rfl h f
  haveI := hU.isLocalization_basicOpen s
  obtain ⟨⟨y, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) f
  dsimp only at e
  have hres : ∀ z : Γ(Z, φ ⁻¹ᵁ chart d a), (Z.presheaf.germ _ (genericPoint Z) h).hom
      (algebraMap Γ(Z, φ ⁻¹ᵁ chart d a) Γ(Z, Z.basicOpen s) z) = (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom z :=
    fun z => Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le s)) _ h z
  have e' := congrArg (Z.presheaf.germ _ (genericPoint Z) h).hom e
  rw [map_mul, hres, hres, map_pow, hgs] at e'
  have hf : (Z.presheaf.germ _ (genericPoint Z) h).hom f =
      (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y * ((∏ i ∈ I, rat φ a i)⁻¹) ^ n := by
    rw [inv_pow, ← e', mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), mul_one]
  have hr : (∏ i ∈ I, crd φ a / crd φ i) ∈ rA ℂ (crd φ) I :=
    prod_mem fun i hi => Algebra.subset_adjoin ⟨i, hi, a, rfl⟩
  have hA : IsIntegral (rA ℂ (crd φ) I)
      (algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i)) :=
    isIntegral_algebraMap (R := rA ℂ (crd φ) I) (A := Z.functionField) (x := ⟨_, hr⟩)
  rw [hf, hinv]
  exact (Subalgebra.mem_restrictScalars ℂ).2 ((hint y).mul (hA.pow n))
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

theorem injective_mvPolynomial_of_finite_of_ringKrullDim {k B : Type} [Field k] [CommRing B] {d : ℕ}
    (ψ : MvPolynomial (Fin d) k →+* B) (hψ : ψ.Finite) (hB : ringKrullDim B = d) :
    Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  letI : Algebra (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := (RingHom.kerLift ψ).toAlgebra
  have hfin : (RingHom.kerLift ψ).Finite := by
    have e : ψ = (RingHom.kerLift ψ).comp (Ideal.Quotient.mk _) := by
      ext x <;> rfl
    exact RingHom.Finite.of_comp_finite (e ▸ hψ)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := ⟨hfin.to_isIntegral⟩
  have e1 : ringKrullDim B = ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) :=
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (RingHom.kerLift_injective ψ)
  have e2 : ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) ≤
      ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective _
      (Ideal.Quotient.factor_surjective (by rw [Ideal.span_singleton_le_iff_mem]; exact hr))
  have e3 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at e3
  have e4 : (d : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    (hB.symm.trans e1).le.trans e2
  have h := (add_le_add e4 (le_refl (1 : WithBot ℕ∞))).trans e3
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, zero_add] at h
  norm_cast at h
  omega

theorem ratioSec_eq_projSpace_ratio (d : ℕ) (i j : Fin (d + 1)) (h : j ≠ i) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  have e := GlobalTheory.ProjSpace.chartAlgEquiv_X ℂ d i ⟨j, h⟩
  rw [GlobalTheory.ProjSpace.chartAlgEquiv_apply, GlobalTheory.ProjSpace.polyToAway, MvPolynomial.eval₂Hom_X'] at e
  exact e

theorem algebraicIndependent_rat : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ)
    [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p →
    ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) →
      AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  intro d Z _ p _ inst hinst φ _ hφ hgen
  subst hφ
  obtain ⟨hU, hψ₀⟩ := (GlobalTheory.ProjSpace.isFinite_iff_pullRatio φ (U := fun i => φ ⁻¹ᵁ chart d i)
    (fun _ => rfl)).1 inferInstance 0
  set c := (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str ℂ d) (φ ⁻¹ᵁ chart d 0)).hom with hc
  set y := GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl with hy
  let ψ : MvPolynomial (Fin d) ℂ →+* Γ(Z, φ ⁻¹ᵁ chart d 0) := MvPolynomial.eval₂Hom c (fun j => y j.succ)
  let σ : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin d) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)
  have hcomp : ψ.comp σ = MvPolynomial.eval₂Hom c y := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp [ψ, σ]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [ψ, σ, y]
      · simp [ψ, σ]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (hcomp ▸ hψ₀)
  have hdim : ringKrullDim Γ(Z, φ ⁻¹ᵁ chart d 0) = d :=
    GlobalTheory.SmoothDim.ringKrullDim_affineOpen ℂ Z (φ ≫ PSpace.str ℂ d) d inferInstance _ hU ⟨_, hgen 0⟩
  have hinj : Function.Injective ψ := injective_mvPolynomial_of_finite_of_ringKrullDim ψ hψ hdim
  have hgerm : Function.Injective (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom :=
    germ_injective_of_isIntegral Z _ (hgen 0)
  have key : (MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)).toRingHom =
      (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_C]
      subst hinst
      have e : (φ ≫ PSpace.str ℂ d).appLE ⊤ (φ ⁻¹ᵁ chart d 0) le_top =
          (φ ≫ PSpace.str ℂ d).appTop ≫ Z.presheaf.map (homOfLE le_top).op := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_map _ _ _).symm
      rw [hc, GlobalTheory.QCoh.Qcqs.baseRingHom, CommRingCat.hom_comp, RingHom.comp_apply, e,
        CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]
      rfl
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_X']
      rw [rat, dite_eq_left (hgen 0), hy, GlobalTheory.ProjSpace.pullRatio, ← ratioSec_eq_projSpace_ratio d 0 j.succ (Fin.succ_ne_zero j),
        Scheme.Hom.app_eq_appLE]
  rw [algebraicIndependent_iff_injective_aeval]
  have : ⇑(MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)) =
      ⇑((Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ) :=
    congrArg DFunLike.coe key
  rw [this]
  exact hgerm.comp hinj

end GlobalTheory.PD.XCover
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

noncomputable section

namespace GlobalTheory.PD.XCover

theorem finiteDimensional_of_finite {A B F K : Type} [CommRing A] [CommRing B] [Field F] [Field K] [Algebra F K]
    (ψ : B →+* A) (hψ : ψ.Finite) (g : A →+* K) (hB : ∀ b, g (ψ b) ∈ Set.range (algebraMap F K))
    (hfr : ∀ x : K, ∃ a b : A, g b ≠ 0 ∧ x * g b = g a) : FiniteDimensional F K := by
  letI := ψ.toAlgebra
  haveI : Module.Finite B A := hψ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := A)
  let M : Submodule F K := Submodule.span F (g '' (s : Set A))
  have hMfg : M.FG := Submodule.fg_span (s.finite_toSet.image g)
  have hM : ∀ a : A, g a ∈ M := by
    intro a
    have ha : a ∈ Submodule.span B (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact M.add_mem hx hy
    | smul b x _ hx =>
      obtain ⟨c, hc⟩ := hB b
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hc, ← Algebra.smul_def]
      exact M.smul_mem c hx
  let R := Algebra.adjoin F (Set.range g)
  have hRM : Subalgebra.toSubmodule R ≤ M := by
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ g.range.toSubmonoid := (Submonoid.closure_le.2 (fun y hy => hy)) hx
    obtain ⟨a, rfl⟩ := hx'
    exact hM a
  have hRfg : (Subalgebra.toSubmodule R).FG := by
    haveI : FiniteDimensional F M := Module.Finite.iff_fg.2 hMfg
    exact isNoetherian_submodule.1 inferInstance _ hRM
  have htop : ∀ z : K, z ∈ M := by
    intro z
    obtain ⟨a, b, hb, e⟩ := hfr z
    have hbR : g b ∈ R := Algebra.subset_adjoin ⟨b, rfl⟩
    have hint : IsIntegral F (g b) := IsIntegral.of_mem_of_fg R hRfg _ hbR
    have hinv : (g b)⁻¹ ∈ R := Subalgebra.inv_mem_of_algebraic R (x := ⟨g b, hbR⟩) hint.isAlgebraic
    have hz : z = g a * (g b)⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [hz]
    exact hRM (R.mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) hinv)
  have : M = ⊤ := eq_top_iff.2 fun z _ => htop z
  exact ⟨this ▸ hMfg⟩

variable {d : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ratioSec_eq (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  refine (GlobalTheory.ProjFrac.awayToSection_mk (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 _).trans ?_
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem exists_frac_germ (Z : Scheme.{0}) [IsIntegral Z] (U : Z.Opens) (hU : IsAffineOpen U) (h : genericPoint Z ∈ U)
    (x : Z.functionField) : ∃ a b : Γ(Z, U), (Z.presheaf.germ U _ h).hom b ≠ 0 ∧
      x * (Z.presheaf.germ U _ h).hom b = (Z.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Z, U)) x
  have hb' : algebraMap Γ(Z, U) Z.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem germ_app_mem (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) (φ : Z ⟶ PSpace ℂ d)
    (hp : φ ≫ PSpace.str ℂ d = p) (h : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (b : Γ(PSpace ℂ d, chart d 0)) :
    letI := ffAlg p
    (Z.presheaf.germ _ _ h).hom ((φ.app (chart d 0)).hom b) ∈ fld φ := by
  letI := ffAlg p
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d 0 b
  have e := congrArg (fun t => t P) (GlobalTheory.ProjSpace.appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ chart d 0) (i := 0) (hi := le_rfl))
  simp only [RingHom.comp_apply, RingHom.coe_coe] at e
  rw [← Scheme.Hom.appLE_eq_app, e, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine MvPolynomial.eval₂_mem (fun _ _ => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, hp]
    have hc : ∀ c : ℂ, (Z.presheaf.germ _ _ h).hom ((GlobalTheory.QCoh.Qcqs.baseRingHom p (φ ⁻¹ᵁ chart d 0)).hom c) =
        algebraMap ℂ Z.functionField c := by
      intro c
      rw [← GlobalTheory.QCoh.Qcqs.baseRingHom_res p (le_top : φ ⁻¹ᵁ chart d 0 ≤ ⊤), Z.presheaf.germ_res_apply,
        GlobalTheory.QCoh.Qcqs.baseRingHom_top]
      rfl
    rw [hc]
    exact IntermediateField.algebraMap_mem _ _
  · have hr : (Z.presheaf.germ _ _ h).hom (GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl j) = rat φ 0 j := by
      rw [rat, dite_eq_left h, ratioSec_eq, ← Scheme.Hom.appLE_eq_app]
      rfl
    simp only [Function.comp_apply]
    rw [hr]
    exact IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩

theorem finiteDimensional_fld : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p →
    (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  intro d Z _ p _ inst hinst φ _ hp hgen
  subst hinst
  have hC : IsAffineOpen (chart d 0) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d 0
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d 0) := hC.preimage φ
  exact finiteDimensional_of_finite (φ.app (chart d 0)).hom (φ.finite_app _ hC) (Z.presheaf.germ _ _ (hgen 0)).hom
    (fun b => ⟨⟨_, germ_app_mem Z p φ hp (hgen 0) b⟩, rfl⟩) (exists_frac_germ Z _ hU (hgen 0))

end GlobalTheory.PD.XCover
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.HeckeToGal

theorem exists_galChar_of_finite_order : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (η : HChar K) (n : ℕ), 0 < n → η ^ n = 1 → ∃ χ : _root_.Formalism.ConjugateSelfDual.G K Ω →* ℂˣ,
      IsOpen (χ.ker : Set (_root_.Formalism.ConjugateSelfDual.G K Ω)) ∧ (χ = 1 → η = 1) ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : _root_.Formalism.ConjugateSelfDual.G K Ω),
        _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v := by
  intro Ω _ K _ _ _ _ η n hn hη
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have hηn : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar K => ξ.1 x) hη
  have hopen : IsOpen (η.1.ker : Set (Ideles K)) := isOpen_ker_of_pow η.1 η.2.1 hn hηn
  have hinf : infConn K ≤ η.1.ker := by
    rintro _ ⟨y, hy, rfl⟩
    let φ : (InfiniteAdeleRing K)ˣ →* ℂˣ :=
      η.1.comp (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))
    have hc : Continuous fun z : InfiniteAdeleRing K => (z, (1 : FiniteAdeleRing (𝓞 K) K)) :=
      continuous_id.prodMk continuous_const
    have hφ : Continuous φ := η.2.1.comp (Continuous.units_map _ hc)
    have hop : IsOpen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := isOpen_ker_of_pow φ hφ hn (fun x => hηn _)
    have hcl : IsClopen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
    exact hcl.connectedComponent_subset (one_mem φ.ker) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (Subgroup.isClosed_of_isOpen _ hopen)
    rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (η.2.2 k)
  have hs : Function.Surjective art := ha.quot.surjective
  let ηb : Gab K Ω →* ℂˣ :=
    art.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩
  have hηb : ∀ x, ηb (art x) = η.1 x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply art (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩ x
  have hηbc : Continuous ηb := by
    refine ha.quot.isQuotientMap.continuous_iff.mpr ?_
    have e : (ηb ∘ art) = η.1 := funext hηb
    rw [e]
    exact η.2.1
  let χ : _root_.Formalism.ConjugateSelfDual.G K Ω →* ℂˣ := (ηb.comp (toAb K Ω))⁻¹
  have hχ : ∀ σ, χ σ = (ηb (toAb K Ω σ))⁻¹ := fun σ => rfl
  have hχc : Continuous χ := by
    have ht : Continuous (toAb K Ω) := (QuotientGroup.isQuotientMap_mk _).continuous
    exact (hηbc.comp ht).inv
  have hχn : ∀ σ, χ σ ^ n = 1 := fun σ => by
    obtain ⟨x, hx⟩ := hs (toAb K Ω σ)
    rw [hχ, ← hx, hηb, inv_pow, hηn, inv_one]
  refine ⟨χ, isOpen_ker_of_pow χ hχc hn hχn, fun h1 => ?_, ?_⟩
  · apply Subtype.ext
    refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
    have e := DFunLike.congr_fun h1 σ
    rw [hχ, hσ, hηb, MonoidHom.one_apply, inv_eq_one] at e
    exact e
  · filter_upwards [(GlobalTheory.Mem.UnrAe.unr_ae_and_level K η).1.compl_mem_cofinite] with v hv
    have hv : η.UnrAt v := by simpa using hv
    intro A σ hA hσ
    obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
    rw [hχ, ← map_inv, ← map_inv, ← e, hηb, ← η.val_eq hv x hx]
    rfl

end GlobalTheory.HeckeToGal

end
end
