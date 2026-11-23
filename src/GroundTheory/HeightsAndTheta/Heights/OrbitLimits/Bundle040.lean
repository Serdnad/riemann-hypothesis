module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle023
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
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Smooth.Flat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime)
open GroundTheory.Heights₂.Heights (segreChartComponents mem_segreChartComponents)

theorem ChartConeComponent.proof : ChartConeComponent.Statement := by
  intro K _ _ ι _ W m σ i hW W' hW'
  have hmin := mem_segreChartComponents.1 hW'
  have : W'.IsPrime := hmin.1.1
  let φ : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ := chartSubst σ i
  have : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
  have hle : W.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W'.comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show φ (MvPolynomial.map (Int.castRingHom ℂ) f) ∈ W'
    have h := ChartDivisorComponents.chartSection_mem hW.2.1 σ i hf
    rw [chartSection_eq_chartSubst] at h
    exact hmin.1.2 h
  obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨W'', hW'', Ideal.map_le_iff_le_comap.2 hW''le⟩

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

namespace CurveSectionQuotientFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero (y : (Σ k, ι k) → Ω) (hP : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have e : (C (n : ℤ) : MRing ι) = (n : MRing ι) := by simp
    rw [e, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [hP, Ideal.mem_bot] at h
  exact_mod_cast h

theorem aeval_ne_zero (y : (Σ k, ι k) → Ω) {s : MRing ι} {d : K → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d)
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  apply hsP
  change s ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
  rw [h0, map_zero, zero_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_ratioField [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {b : Ω}
    (hb : b ∈ chartRingZ y c) : b ∈ _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ hx
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem isAlgebraic_of_mem [CharZero Ω] (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c) : IsAlgebraic ℚ x := by
  have htr := LowerBoundFree.FnFieldTrdeg.full K ι (_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c) (ratioPtL y c) 0 (birational y c hc)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hP)
  have halg : Algebra.IsAlgebraic ℤ (_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c) := trdeg_eq_zero_iff.mp htr
  have h1 : IsAlgebraic ℚ (⟨x, hx⟩ : _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c) :=
    (halg.isAlgebraic _).extendScalars (algebraMap ℤ ℚ).injective_int
  exact IntermediateField.isAlgebraic_iff.mp h1

theorem exists_nat_mul_mem_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {q : Ω} (hq : q ∈ _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * q ∈ chartRingZ y c := by
  have hq' : q ∈ Algebra.adjoin ℚ (coneRatios y c) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x hx => isAlgebraic_of_mem y hP c hc (IntermediateField.subset_adjoin _ _ hx))]
    exact hq
  exact CurveAffineCharts.exists_nat_mul_mem_adjoin hq'


omit [∀ k, Fintype (ι k)] in
theorem div_mem_ratioField [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m x : Ω} (hm : m ∈ chartLat y a 1) (hx : x ∈ chartLat y a 1) :
    m / x ∈ _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c := by
  have key : ∀ p : Ω, p ≠ 0 → m * p ∈ _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c → x * p ∈ _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c → m / x ∈ _root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c :=
    fun p hp h1 h2 => by rw [← mul_div_mul_right m x hp]; exact div_mem h1 h2
  exact key _ (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
    (mem_ratioField y c (hm c hc)) (mem_ratioField y c (hx c hc))

theorem exists_nat_mul_mem_span (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1) {a : K → ℤ}
    {m x : Ω} (hm : m ∈ chartLat y a 1) (hx : x ∈ chartLat y a 1) (hx0 : x ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * m ∈ Submodule.span (curveRing y) {x} := by
  classical
  have := charZero y hP.2.2.1
  have key : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → (n : Ω) * (m / x) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_chartRingZ y hP c hc (div_mem_ratioField y a c hc hm hx)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => (hc h).elim⟩
  choose N hN0 hN using key
  have hb : ((∏ c, N c : ℕ) : Ω) * (m / x) ∈ curveRing y := by
    rw [mem_curveRing]
    intro c hc
    have e : ((∏ c', N c' : ℕ) : Ω) * (m / x) =
        ((∏ c' ∈ Finset.univ.erase c, N c' : ℕ) : Ω) * ((N c : Ω) * (m / x)) := by
      rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ c)]
      push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ _) (hN c hc)
  refine ⟨∏ c, N c, Finset.prod_ne_zero_iff.mpr fun c _ => hN0 c,
    Submodule.mem_span_singleton.mpr ⟨⟨_, hb⟩, ?_⟩⟩
  rw [Subring.smul_def, smul_eq_mul]
  field_simp

theorem finite_curveSectionMod (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1) (a : K → ℤ) :
    Module.Finite ℤ (curveSectionMod y a) := by
  obtain ⟨c, -, hc⟩ := exists_chart hP
  have hfg : (chartLat y a 1).FG :=
    HilbertSamuel.SectionLatticeFinite.proof HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond K ι Ω y a 1
      (fun k => ⟨c k, hc k⟩)
  have : Module.Finite ℤ (chartLat y a 1) :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg _).mpr hfg)
  let f : curveSectionMod y a →+ chartLat y a 1 :=
    { toFun := fun m => ⟨m, m.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact Module.Finite.of_injective f.toIntLinearMap fun u v h =>
    Subtype.ext (congrArg (fun z : chartLat y a 1 => (z : Ω)) h)

end CurveSectionQuotientFinite


open CurveSectionQuotientFinite in
theorem CurveSectionQuotFinite.proof : CurveSectionQuotFinite.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  have hxM : aeval y s ∈ chartLat y (fun k => (d k : ℤ)) 1 := HilbertSamuel.LiftBirationalAmple.chartLat_form hs
  have hx0 := aeval_ne_zero y hs hsP
  have hfM := finite_curveSectionMod y hP (fun k => (d k : ℤ))
  have hfg : AddGroup.FG (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _)
      (hG := Module.Finite.iff_addGroup_fg.mp hfM)
  let _ : Module ℤ (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := AddCommGroup.toIntModule _
  have hfin : Module.Finite ℤ (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) :=
    Module.Finite.iff_addGroup_fg.mpr hfg
  refine Module.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, hnm⟩ := exists_nat_mul_mem_span y hP m.2 hxM hx0
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩
  change ((n : ℤ)) • (Submodule.Quotient.mk m : curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) = 0
  rw [natCast_zsmul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply]
  simpa [nsmul_eq_mul] using hnm

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveVerticalPointMultiplicity

variable {K : Type} {ι : K → Type}

theorem aeval_mul_of_homog [Fintype K] [∀ k, Fintype (ι k)] {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {f : MRing ι}
    {d : K → ℕ} (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    aeval (fun p => r p * t p.1) f = aeval r f * ∏ k, t k ^ d k := by
  classical

  rw [f.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  dsimp only
  rw [Finset.prod_pow_eq_pow_sum, hf m hm k]

theorem map_aeval_int {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (r : (Σ k, ι k) → S)
    (f : MRing ι) : φ (aeval r f) = aeval (fun p => φ (r p)) f := by
  induction f using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end CurveVerticalPointMultiplicity


open CurveVerticalPointMultiplicity GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart in
theorem CurveVertPointMultChart.proof (hCh : CurveVertPointChart.Statement)
    (hN : CurveVertPointNagata.Statement) : CurveVertPointMultChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP W hW c hc a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN K ι Ω y s d hP hs hsP W hW c hc a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let e : Localization.AtPrime (curvePtIdeal y W) →+* Ω := IsLocalization.lift hunit
  have hinj : Function.Injective e := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl)
      (Localization.AtPrime (curvePtIdeal y W)) (le_nonZeroDivisors_of_noZeroDivisors fun h =>
        h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  let r : (Σ k, ι k) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p) (⟨b' p, hb' p⟩ : (curvePtIdeal y W).primeCompl)
  have her : ∀ p, e (r p) = y p / y ⟨p.1, c p.1⟩ := fun p =>
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' p).symm
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [map_aeval_int, funext her]
    have key : aeval y s = aeval (fun p => y p / y ⟨p.1, c p.1⟩) s * ∏ k, y ⟨k, c k⟩ ^ d k := by
      rw [← aeval_mul_of_homog _ (fun k => y ⟨k, c k⟩) hs]
      exact congrArg (fun v => aeval v s) (funext fun p => (div_mul_cancel₀ _ (hyc p.1)).symm)
    have hpc : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : Ω) = (b : Ω) * _
    apply mul_right_cancel₀ hpc
    rw [mul_assoc, ← key, hab]

  have hXk : ∀ k, (X k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl := fun k h => by
    have h1 := MvPolynomial.mem_map_C_iff.mp h (Finsupp.single k 1)
    rw [MvPolynomial.coeff_X, if_pos rfl] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hprod : (∏ k, X k ^ d k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl :=
    Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hXk k) _
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) :=
    isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) := by
    rw [hΦ s, aeval_mul_of_homog (fun p => MvPolynomial.C (r p)) X hs, ← map_aeval_int MvPolynomial.C, hsr,
      IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_mul, map_mul, ← mul_assoc,
      IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), MvPolynomial.algebraMap_eq]
  have hv : IsUnit (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) :=
    ((hbu.map MvPolynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hprod⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), ← Ideal.map_map,
      MvPolynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dite_eq_left hWp, locLen, dite_eq_left hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights.Targets
end
