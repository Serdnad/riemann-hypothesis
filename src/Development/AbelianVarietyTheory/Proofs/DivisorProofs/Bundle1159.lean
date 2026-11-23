module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_generating_secs_tens_lbPow_O1 : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (n : ℕ) (u : Fin n → (CechPic.tens L (lbPow ((ProjSpace.O1 ℂ Y.N).pull Y.ι) m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro Y L hL
  obtain ⟨s, hs⟩ := exists_veryAmpleBy_O1 Y
  have hH : ((ProjSpace.O1 ℂ Y.N).pull Y.ι).IsLB := pull_isLB (ProjSpace.O1_isLB ℂ Y.N) _
  generalize (ProjSpace.O1 ℂ Y.N).pull Y.ι = H at s hs hH
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated ℂ Y.X Y.str H _ s hH hs L hL
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

end GlobalTheory.ProjVar
end

section

noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FrameCoord {K : Type} [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K)
    {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)} (m1 : SABMap t₀ Xo.univ.t y.x)
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ)
    (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K) : Prop :=
  ∀ i, ∃ (u : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A),
    u ≫ m1.φ = y.u ρ i ∧ u ≫ m2.φ = w.left ≫ F.φ ∧ IsLieComb (v i) F.v w

def LocBasis {K : Type} [Field K] [NumberField K] {n : ℕ} (𝔓 : HeightOneSpectrum (𝓞 K))
    (L : Submodule (𝓞 K) (Fin n → K)) {m : ℕ} (b : Fin m → Fin n → K) : Prop :=
  (∀ i, b i ∈ L) ∧ LinearIndependent K b ∧
    ∀ x ∈ L, ∃ d : 𝓞 K, d ∉ 𝔓.asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b)

end GlobalTheory.PtDeg
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LieSpan

theorem exists_isLieBasis_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib B.pol) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (n : SABMap G.t B.t (spMap ρV)), ∃ vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G), IsLieBasis vV ∧ ∀ k, ∃ (M : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A), IsLieComb M F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ ∧ (fun l => iK (M l)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) l => iK (v l)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  intro E _ _ _ H K _ _ B F 𝔓 T iK hiK ρV hρV G n
  obtain ⟨N, r, M, hr, hM, -, hloc⟩ := GlobalTheory.T.lie_lattice_local_basis_description K B.pol F
  obtain ⟨i, hi⟩ : ∃ i, r i ∉ 𝔓.asIdeal := by
    by_contra h
    push_neg at h
    refine 𝔓.isPrime.ne_top ?_
    rw [eq_top_iff, ← hr]
    exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h j)
  have hv1 : ∀ m : ℕ, 𝔓.valuation K (algebraMap (𝓞 K) K (r i ^ m)) = 1 := fun m => by
    rw [HeightOneSpectrum.valuation_of_algebraMap, map_pow]
    rw [le_antisymm (𝔓.intValuation_le_one _) (not_lt.1 fun h => hi ((𝔓.intValuation_lt_one_iff_mem _).1 h)),
      one_pow]
  let R := Localization.subalgebra.ofField K (Submonoid.powers (r i))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (hM i).1)
  have e₁ : (algebraMap R K).comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hval : ∀ z : R, iK (algebraMap R K z) ∈ Set.range (algebraMap T.V T.Fr) := fun z => by
    refine (hiK _).2 ?_
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r i)) z
    have hz := congrArg (algebraMap R K) (IsLocalization.mk'_spec R x s)
    rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, e₁] at hz
    obtain ⟨m, hm⟩ := s.2
    have hs : 𝔓.valuation K (algebraMap (𝓞 K) K s) = 1 := by rw [← hm]; exact hv1 m
    have := congrArg (𝔓.valuation K) hz
    rw [map_mul, hs, _root_.mul_one] at this
    rw [this]
    exact 𝔓.valuation_le_one x
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.LamT.exists_restrict_ringHom (algebraMap R K) (algebraMap T.V T.Fr) hinj iK hval
  have hρ : ρV = ψ'.comp (algebraMap (𝓞 K) R) := by
    refine RingHom.ext fun x => hinj ?_
    have h₁ := RingHom.congr_fun hρV x
    have h₂ := RingHom.congr_fun hψ' (algebraMap (𝓞 K) R x)
    have h₃ := RingHom.congr_fun e₁ x
    simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  let GR := (Over.pullback (spMap (algebraMap (𝓞 K) R))).obj B.t.G
  have hp : IsGrpPullback GR B.t.G (spMap (algebraMap (𝓞 K) R)) (pullback.fst _ _) := isGrpPullback_pullback _ _
  have es₁ : spMap (algebraMap (𝓞 K) K) = spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [← spMap_comp, e₁]
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have w₁ : F.φ ≫ B.t.G.hom = (F.P₀.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hF.1.w, es₁, Category.assoc]
  have hψ : IsGrpPullback F.P₀.A GR (spMap (algebraMap R K)) (hp.1.lift _ _ w₁) :=
    IsGrpPullback.cancel hp (hF.congr es₁ (hp.1.lift_fst _ _ w₁).symm) (hp.1.lift_snd _ _ w₁)
  obtain ⟨e, he, hx⟩ := hloc i R GR (pullback.fst _ _) (hp.1.lift _ _ w₁)
    (IsLocalization.map_units R (⟨r i, Submonoid.mem_powers _⟩ : Submonoid.powers (r i))) hp hψ
    (hp.1.lift_fst _ _ w₁)
  choose e₀ he₀ hM₀ using hx
  have hin := (GlobalTheory.T.lieLattice_localization_modelLieAlgebra K B.pol F R (Submonoid.powers (r i)) GR (pullback.fst _ _) (hp.1.lift _ _ w₁) e e₀ (M i)
    hp hψ (hp.1.lift_fst _ _ w₁) he fun k => ⟨he₀ k, hM₀ k⟩).1
  have es₂ : spMap ρV = spMap ψ' ≫ spMap (algebraMap (𝓞 K) R) := by rw [hρ]; exact spMap_comp _ _
  have hn : IsGrpPullback G.t.G B.t.G (spMap ρV) n.φ := n.cart
  have w₂ : n.φ ≫ B.t.G.hom = (G.t.G.hom ≫ spMap ψ') ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [hn.1.w, es₂, Category.assoc]
  have hq : IsGrpPullback G.t.G GR (spMap ψ') (hp.1.lift _ _ w₂) :=
    IsGrpPullback.cancel hp (hn.congr es₂ (hp.1.lift_fst _ _ w₂).symm) (hp.1.lift_snd _ _ w₂)
  have hsm : Smooth GR.hom := by
    haveI := B.dim
    haveI : Smooth B.t.G.hom := SmoothOfRelativeDimension.smooth B.g _
    exact MorphismProperty.of_isPullback (P := @Smooth) hp.1 inferInstance
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ' GR G.t.G _ hq hsm _ e he
  refine ⟨v', hb, fun k => ⟨M i k, e₀ k, hM₀ k, ?_, ?_⟩⟩
  · have ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        (Formalism.L2.Pj.dualMap iK).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      refine RingHom.ext fun x => ?_
      have h₁ := RingHom.congr_fun hψ' x.fst
      have h₂ := RingHom.congr_fun hψ' x.snd
      simp only [RingHom.comp_apply] at h₁ h₂
      refine TrivSqZeroExt.ext ?_ ?_
      · simpa [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR] using h₁
      · simp only [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
          zero_add]
        exact h₂
    have es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') =
        spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) := by
      rw [← spMap_comp, ← spMap_comp, ed]
    have eL : (v' k).left ≫ n.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ') ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₂, ← Category.assoc, hv' k, Category.assoc]
    have eR : (e₀ k).left ≫ F.φ =
        spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) ≫ (e k).left ≫ pullback.fst _ _ := by
      rw [← hp.1.lift_fst _ _ w₁, ← Category.assoc, he₀ k, Category.assoc]
    rw [eL, eR, ← Category.assoc, es, Category.assoc]
  · obtain ⟨_, ⟨m, rfl⟩, hs⟩ := hin k
    have hs0 : algebraMap (𝓞 K) K (r i ^ m) ≠ 0 := by
      intro h0
      have := hv1 m
      rw [h0, map_zero] at this
      exact zero_ne_one this
    obtain ⟨u, hu⟩ := (hiK (algebraMap (𝓞 K) K (r i ^ m))⁻¹).2 (by rw [map_inv₀, hv1 m, inv_one])
    have eq : (fun l => iK (M i k l)) = u • fun l => iK ((r i ^ m • M i k) l) := by
      funext l
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hu, map_inv₀]
      rw [← _root_.mul_assoc, inv_mul_cancel₀ ((map_ne_zero iK).2 hs0), _root_.one_mul]
    rw [eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hs, rfl⟩)

end GlobalTheory.LieSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow

theorem hypS_of_isPolFibre : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (P : PolAV (Sp K)) (P' : PolAV (Sp K')) (ψ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' ψ → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  intro K K' _ _ f P P' ψ h hS
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ P.A P'.A (spMap f) ψ P.L P'.L P.isLB P'.isLB h.2.1 h.2.2.symm hS
end GlobalTheory.MBLow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_form_of_discrete_norms : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) (t : C), N.Int q → t ≠ 0 → ‖t‖ < 1 → (∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖t‖ ^ n) → ∀ m : ℕ, 1 ≤ m → ∃ (β : N.Form (m ^ 2)) (π : C), π ≠ 0 ∧ ‖π‖ < 1 ∧ (∀ n : ℕ, {α | (β.be α α / (2 * m ^ 2)).toNat = n}.Finite) ∧ ∀ α, Real.exp (-(q α / (m : ℝ) ^ 2)) = ‖π‖ ^ (β.be α α / (2 * m ^ 2)).toNat := by
  intro C _ _ N q t hI ht0 ht1 hψ m hm
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  set L : ℝ := -Real.log ‖t‖ with hL
  have hLpos : 0 < L := by
    have := Real.log_neg htpos ht1
    linarith
  clear_value L
  choose Q hQ using hψ
  have hq : ∀ χ, q χ = (Q χ : ℝ) * L := by
    intro χ
    have h1 := hI.ψ χ
    rw [hQ χ] at h1
    have h2 : Real.log (‖t‖ ^ Q χ) = -q χ := by rw [h1, Real.log_exp]
    rw [Real.log_zpow] at h2
    rw [hL]; linarith
  set Bf : N.X → N.X → ℤ := fun x y => Q (x + y) - Q x - Q y with hBf
  have hB : ∀ x y, (Bf x y : ℝ) = QuadraticMap.polar q x y / L := by
    intro x y
    rw [eq_div_iff hLpos.ne']
    simp only [hBf, QuadraticMap.polar, hq]
    push_cast; ring
  have inj : ∀ a b : ℤ, (a : ℝ) = b → a = b := fun a b h => Int.cast_inj.1 h
  let Bm : LinearMap.BilinForm ℤ N.X := LinearMap.mk₂ ℤ Bf
    (fun x x' y => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_left, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_left, zsmul_eq_mul, mul_div_assoc]))
    (fun x y y' => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_right, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_right, zsmul_eq_mul, mul_div_assoc]))
  have hBm : ∀ x y, Bm x y = Bf x y := fun x y => rfl
  have hdiag : ∀ x, Bf x x = 2 * Q x := by
    intro x
    apply inj
    rw [hB, QuadraticMap.polar_self, hq, nsmul_eq_mul]
    push_cast
    field_simp
    try ring
  have hsymm : ∀ x y, Bf x y = Bf y x := by
    intro x y; simp only [hBf, add_comm x y]; ring
  have hpos : ∀ y, y ≠ 0 → 0 < q y := by
    intro y hy
    by_contra hn
    push_neg at hn
    have hfin : {α | ¬ (0 < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop 0))
    have hinf : (Set.range fun c : ℤ => c • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℤ hy)
    refine hinf (hfin.subset ?_)
    rintro _ ⟨c, rfl⟩
    simp only [Set.mem_setOf_eq, not_lt]
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    nlinarith [mul_self_nonneg (c : ℝ)]
  have hQnn : ∀ y, 0 ≤ Q y := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have : (Q 0 : ℝ) * L = 0 := by rw [← hq, QuadraticMap.map_zero]
      have : (Q 0 : ℝ) = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hLpos.ne'
      exact_mod_cast this.ge
    · have := hpos y hy
      rw [hq] at this
      have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
      exact_mod_cast this.le
  have hQpos : ∀ y, y ≠ 0 → 0 < Q y := by
    intro y hy
    have := hpos y hy
    rw [hq] at this
    have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
    exact_mod_cast this
  have hm0 : (2 * (m : ℤ) ^ 2) ≠ 0 := by positivity
  let β : N.Form (m ^ 2) :=
    { be := (2 * (m : ℤ) ^ 2) • Bm
      symm := fun y z => by
        simp only [LinearMap.smul_apply, hBm, hsymm y z]
      pos := fun y hy => by
        simp only [LinearMap.smul_apply, hBm, hdiag, smul_eq_mul]
        have := hQpos y hy
        positivity
      dvd := fun y z => ⟨Bf y z, by simp [LinearMap.smul_apply, hBm, smul_eq_mul]⟩ }
  have hβ : ∀ α, β.be α α / (2 * m ^ 2) = 2 * Q α := by
    intro α
    show ((2 * (m : ℤ) ^ 2) • Bm) α α / (2 * m ^ 2) = 2 * Q α
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hBm, hdiag, Int.mul_ediv_cancel_left _ hm0]
  have hn : 0 < 2 * m ^ 2 := by positivity
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq t hn
  have hπ0 : π ≠ 0 := by rintro rfl; exact ht0 (by rw [← hπ, zero_pow hn.ne'])
  have hπn : ‖π‖ ^ (2 * m ^ 2) = ‖t‖ := by rw [← norm_pow, hπ]
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hπ1 : ‖π‖ < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := 2 * m ^ 2) h
    rw [hπn] at this
    linarith
  have hlp : Real.log ‖π‖ * (2 * (m : ℝ) ^ 2) = -L := by
    rw [hL, ← hπn, Real.log_pow]; push_cast; ring
  refine ⟨β, π, hπ0, hπ1, fun n => ?_, fun α => ?_⟩
  · have hfin : {α | ¬ ((n : ℝ) * L < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop _))
    refine hfin.subset fun α hα => ?_
    simp only [Set.mem_setOf_eq, hβ] at hα ⊢
    rw [not_lt, hq]
    have h1 : (2 * Q α) = (n : ℤ) := by
      rw [← hα, Int.toNat_of_nonneg (by linarith [hQnn α])]
    have h2 : (Q α : ℝ) ≤ n := by
      have : Q α ≤ (n : ℤ) := by linarith [hQnn α]
      exact_mod_cast this
    nlinarith
  · have hc : ((2 * Q α).toNat : ℝ) = 2 * (Q α : ℝ) := by
      have := Int.toNat_of_nonneg (show 0 ≤ 2 * Q α by linarith [hQnn α])
      exact_mod_cast this
    rw [hβ, ← Real.exp_log hπpos, ← Real.exp_nat_mul, hc, hq]
    congr 1
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    have e : Real.log ‖π‖ = -L / (2 * (m : ℝ) ^ 2) := by
      rw [eq_div_iff (by positivity)]; exact hlp
    rw [e]
    field_simp

end GlobalTheory.MBLow
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem cxPts_var_compact_manifold : ∀ Y : Var ℂ, CompactSpace (CxPts Y.str (RingHom.id ℂ)) ∧ T2Space (CxPts Y.str (RingHom.id ℂ)) ∧ SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) ∧ ∃ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A := fun Y =>
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  ⟨this, t2Space_cxPts_of_isProjOver _ Y.isProjOver, secondCountableTopology_of_isProjOver _ Y.isProjOver,
    (AnRead.all Y.str (RingHom.id ℂ) Y.dim).finAtlas, AnRead.isAlgAtlas_finAtlas _⟩

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess bas wd wdb)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ENNReal

namespace GlobalTheory.ChernMA

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B : LB Y} {φ : Weight p σ B} {A : FinHolAtlas D (CxPts p σ)}

variable [SecondCountableTopology (CxPts p σ)]

theorem restrict_chernPart (h : φ.IsCInf) (ε : ℤˣ) (c : AlgChart p σ D) :
    (φ.chernPart D ε).restrict c.finChart.source = ((volume.restrict c.finChart.target).withDensity
      fun z => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.finChart.symm z))).map c.finChart.symm := by
  ext T hT
  have ht := c.finChart.open_target.measurableSet
  have hs : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable ht
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin D))
  rw [Measure.restrict_apply hT, Weight.chernPart_apply h ε c
      (hT.inter c.finChart.open_source.measurableSet) inter_subset_right,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', Measure.restrict_restrict' ht, inter_comm, AlgChart.finChart_source,
    c.e.image_source_inter_eq', ← hp.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), inter_comm]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]


end GlobalTheory.ChernMA
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s), ∃ o' : Obj b N (f ≫ s), Nonempty (ObjMap o' o f) := by
  first | exact @GlobalTheory.HTPull.exists_objMap_pull | exact GlobalTheory.HTPull.exists_objMap_pull | (intros; apply GlobalTheory.HTPull.exists_objMap_pull <;> assumption)
end
