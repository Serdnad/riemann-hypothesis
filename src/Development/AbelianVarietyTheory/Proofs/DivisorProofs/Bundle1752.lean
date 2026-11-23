module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle578
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle164
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle130
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle044
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology Set GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK expG inG)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem shapeM_mono {n : ℕ} (ε : Fin n → Bool) {d d' : ℕ} (h : d ≤ d') : ShapeM ε d ≤ ShapeM ε d' :=
  Submodule.span_mono fun _ ⟨H, P, hH, hP, e⟩ => ⟨H, P, hH, hP.trans h, e⟩

theorem hasTrace_add' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {S T : U →L[ℂ] U} {a b : ℂ} (hS : HasTrace S a) (hT : HasTrace T b) : HasTrace (S + T) (a + b) :=
  ⟨hS.1.add hT.1, by rw [trace_add hS.1 hT.1, hS.2, hT.2]⟩

theorem hasTrace_smul' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {T : U →L[ℂ] U} {a : ℂ} (c : ℂ) (hT : HasTrace T a) : HasTrace (c • T) (c * a) :=
  ⟨hT.1.smul c, by rw [trace_smul, hT.2]⟩

theorem toM_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

theorem trace_adBas (hSh : StShape) (hBD : StBasDeriv) (hUF : UFin) (hRS : RangeShape) (hTS : TraceSum)
    (hCD : ConjDeriv) {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type)
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U))
    (hπ : IsUnitaryRep π) (hirr : IsTopIrreducible π) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n)
    (hZ : LieU ε Z) (hH : IsCutFn H) :
    HasTrace (repOp π μ fun g => adBas ε Z H P (toM g)) 0 := by
  have := GlobalTheory.CompanionTheory.HaarUJ.haar_rinv_UJ n ε μ
  have hZG : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
  obtain ⟨hxc, hxinv⟩ := GlobalTheory.CompanionTheory.ExpOneParam.continuous_expG_and_toM_inv n ε Z hZG
  obtain ⟨hadS, hder⟩ := hBD n ε Z H P hZ hH
  have hbS : bas ε H P ∈ ShapeM ε (P.totalDegree + 2) := Submodule.subset_span ⟨H, P, hH, by omega, rfl⟩
  obtain ⟨-, -, hac, hacs⟩ := hSh n ε _ _ hadS
  obtain ⟨-, -, hbc, hbcs⟩ := hSh n ε _ _ hbS
  obtain ⟨L, hLf, hLmem, hLd⟩ := hUF n ε U π hπ hirr (P.totalDegree + 2)
  have := hLf
  obtain ⟨-, hTr⟩ := hRS n ε μ U π hπ _ _ hadS
  obtain ⟨-, hAr⟩ := hRS n ε μ U π hπ _ _ hbS
  set fad : UJ ε → ℂ := fun g => adBas ε Z H P (toM g) with hfad
  set fb : UJ ε → ℂ := fun g => bas ε H P (toM g) with hfb
  set T := repOp π μ fad with hT
  set A := repOp π μ fb with hA
  set e := stdOrthonormalBasis ℂ L with he
  set x : ℝ → UJ ε := fun t => expG ε Z t with hx
  have hx0 : x 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have := Formalism.REAL.toM_expG ε Z 0 hZG
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at this
    exact this
  have hconj : ∀ (s : ℝ) (g : UJ ε), toM ((x s)⁻¹ * g * x s) =
      NormedSpace.exp (-((s : ℂ) • Z)) * toM g * NormedSpace.exp ((s : ℂ) • Z) := fun s g => by
    rw [toM_mul', toM_mul', hxinv s, Formalism.REAL.toM_expG ε Z s hZG]
  have key : ∀ (y : UJ ε) (v u : U), ⟪v, π y u⟫_ℂ = ⟪π y⁻¹ v, u⟫_ℂ := fun y v u => by
    rw [hπ.inner_apply_left, inv_inv]
  set w : UJ ε → ℂ := fun g => ∑ j, ⟪(e j : U), π g (e j : U)⟫_ℂ with hw
  have hwc : Continuous w := continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)

  have hsum : ∑ j, ⟪(e j : U), T (e j : U)⟫_ℂ = ∫ g, fad g * w g ∂μ := by
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fad g * ⟪(e j : U), π g (e j : U)⟫_ℂ) μ := fun j _ =>
      (hac.mul (continuous_const.inner (hπ.continuous_apply _))).integrable_of_hasCompactSupport hacs.mul_right
    simp only [hT, hπ.inner_repOp hac hacs, hw, Finset.mul_sum]
    rw [integral_finsetSum _ hint]

  have hid : ∀ t : ℝ, ∑ j, ⟪(e j : U), π (x t) (A (π (x t)⁻¹ (e j : U)))⟫_ℂ =
      ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ := by
    intro t
    set y := x t
    have h1 : ∀ j, ⟪(e j : U), π y (A (π y⁻¹ (e j : U)))⟫_ℂ =
        ∫ g, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ ∂μ := by
      intro j
      rw [key y, hA, hπ.inner_repOp hbc hbcs]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      congr 1
      rw [map_mul, map_mul]
      show _ = ⟪(e j : U), π y (π g (π y⁻¹ (e j : U)))⟫_ℂ
      rw [key y]
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) μ :=
      fun j _ => (hbc.mul (continuous_const.inner ((hπ.continuous_apply _).comp (by fun_prop)))).integrable_of_hasCompactSupport
        hbcs.mul_right
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← integral_finsetSum _ hint]
    have e2 : (fun g => ∑ j, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) =
        fun g => fb g * w (y * g * y⁻¹) := funext fun g => by simp only [hw, Finset.mul_sum]
    rw [e2]
    have e3 := integral_mul_right_eq_self (μ := μ) (fun g => fb (y⁻¹ * g) * w (y * (y⁻¹ * g) * y⁻¹)) y
    have e4 := integral_mul_left_eq_self (μ := μ) (fun g => fb g * w (y * g * y⁻¹)) y⁻¹
    rw [← e4, ← e3]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    congr 2
    · group
    · group

  have h0 : π (x 0) = 1 := by rw [hx0, map_one]
  have hCD' := hCD U L (fun t => π (x t)) (fun t => π (x t)⁻¹) A h0
    (fun t v u => by
      rw [hπ.inner_apply_left, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply])
    (fun t v u => (hπ.inner_apply_left _ v u).symm) (fun v hv => hLd v hv Z hZG)
    (fun u => hLmem _ (hAr u).1) (fun u => hLmem _ (hAr u).2)
  have hfun : (fun t => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π (x t) (A (π (x t)⁻¹
      (stdOrthonormalBasis ℂ L j : U)))⟫_ℂ) = fun t => ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ :=
    funext hid
  rw [hfun] at hCD'

  have hC : IsCompact ((fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad)) :=
    (isCompact_Icc.prod hacs.isCompact).image (by fun_prop)
  obtain ⟨χ, h1, -, hcs, -⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty (disjoint_empty _)
  obtain ⟨M, hM⟩ := hacs.exists_bound_of_continuous hac
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have keyb : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ g, ‖fad ((x u)⁻¹ * g * x u) * w g‖ ≤ M * ‖(χ g : ℂ)‖ * ‖w g‖ := by
    intro u hu g
    rw [norm_mul]
    by_cases h : fad ((x u)⁻¹ * g * x u) = 0
    · rw [h, norm_zero, zero_mul]
      positivity
    · have hg : g ∈ (fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad) :=
        ⟨(u, (x u)⁻¹ * g * x u), ⟨hu, subset_tsupport fad h⟩, by simp only; group⟩
      have h2 : (χ g : ℂ) = 1 := by simp [h1 hg]
      rw [h2, norm_one, mul_one]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hχc : Continuous fun g => (χ g : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hbint : Integrable (fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖) μ := by
    refine (((hχc.norm.const_mul M).mul hwc.norm)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_right ?_
    refine HasCompactSupport.mul_left ?_
    exact (hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).norm
  have hcontF : ∀ (f : UJ ε → ℂ), Continuous f → ∀ u, Continuous fun g => f ((x u)⁻¹ * g * x u) * w g :=
    fun f hf u => (hf.comp (by fun_prop)).mul hwc
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun u g => fb ((x u)⁻¹ * g * x u) * w g) (F' := fun u g => fad ((x u)⁻¹ * g * x u) * w g)
    (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1) (bound := fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun u => (hcontF fb hbc u).aestronglyMeasurable)
    (by
      simp only [hx0, inv_one, one_mul, mul_one]
      exact (hbc.mul hwc).integrable_of_hasCompactSupport hbcs.mul_right)
    (hcontF fad hac 0).aestronglyMeasurable
    (.of_forall fun g u hu => keyb u (Ioo_subset_Icc_self hu) g) hbint
    (.of_forall fun g u _ => by
      have e5 : (fun v : ℝ => fb ((x v)⁻¹ * g * x v) * w g) =
          fun v : ℝ => bas ε H P (NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z)) * w g :=
        funext fun v => by simp only [hfb, hconj]
      rw [e5]
      have e6 : fad ((x u)⁻¹ * g * x u) =
          adBas ε Z H P (NormedSpace.exp (-((u : ℂ) • Z)) * toM g * NormedSpace.exp ((u : ℂ) • Z)) := by
        simp only [hfad, hconj]
      rw [e6]
      exact (hder (toM g) u).mul_const (w g))
  have hzero : ∫ g, fad ((x 0)⁻¹ * g * x 0) * w g ∂μ = 0 := hint.2.unique hCD'
  simp only [hx0, inv_one, one_mul, mul_one] at hzero
  have hTL : ∀ u, T u ∈ L := fun u => hLmem _ (hTr u).1
  have := hTS U L T hTL
  rwa [hsum, hzero] at this

theorem stTrAd_of : StShape → StBasDeriv → UFin → RangeShape → TraceSum → ConjDeriv → StTrAd := by
  intro hSh hBD hUF hRS hTS hCD n ε μ _ U _ _ _ π hπ hirr φ hφ
  suffices h : (∃ d, φ ∈ ShapeM ε d) ∧ HasTrace (repOp π μ fun g => φ (toM g)) 0 from h.2
  induction hφ using Submodule.span_induction with
  | mem φ hmem =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hmem
    exact ⟨⟨_, (hBD n ε Z H P hZ hH).1⟩, trace_adBas hSh hBD hUF hRS hTS hCD ε μ U π hπ hirr Z H P hZ hH⟩
  | zero =>
    refine ⟨⟨0, zero_mem _⟩, ?_⟩
    have h0 : IsRepOp π μ (fun g => (0 : Mat n → ℂ) (toM g)) 0 := fun v => by
      simp only [Pi.zero_apply, zero_smul, integral_zero, ContinuousLinearMap.zero_apply]
      exact ⟨integrable_zero _ _ _, trivial⟩
    rw [h0.repOp_eq]
    exact ⟨isTraceClass_zero, trace_zero⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨⟨d₁, hd₁⟩, ht₁⟩ := h₁
    obtain ⟨⟨d₂, hd₂⟩, ht₂⟩ := h₂
    refine ⟨⟨max d₁ d₂, add_mem (shapeM_mono ε (le_max_left _ _) hd₁) (shapeM_mono ε (le_max_right _ _) hd₂)⟩, ?_⟩
    have o₁ := (hRS n ε μ U π hπ d₁ φ₁ hd₁).1
    have o₂ := (hRS n ε μ U π hπ d₂ φ₂ hd₂).1
    have hs : IsRepOp π μ (fun g => (φ₁ + φ₂) (toM g))
        (repOp π μ (fun g => φ₁ (toM g)) + repOp π μ (fun g => φ₂ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o₁ v).1.add (o₂ v).1).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.add_apply, add_smul]
      · rw [ContinuousLinearMap.add_apply, (o₁ v).2, (o₂ v).2, ← integral_add (o₁ v).1 (o₂ v).1]
        simp only [Pi.add_apply, add_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_add' ht₁ ht₂
  | smul c φ _ h =>
    obtain ⟨⟨d, hd⟩, ht⟩ := h
    refine ⟨⟨d, Submodule.smul_mem _ c hd⟩, ?_⟩
    have o := (hRS n ε μ U π hπ d φ hd).1
    have hs : IsRepOp π μ (fun g => (c • φ) (toM g)) (c • repOp π μ (fun g => φ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o v).1.smul c).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      · rw [ContinuousLinearMap.smul_apply, (o v).2, ← integral_smul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_smul' c ht

end GlobalTheory.PsCo.Pc3
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.ConjAtPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_of_lt_one {w : HeightOneSpectrum (𝓞 E)} (x : w.adicCompletion E) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (nhds 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_of_lt_one z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  rw [map_pow] at hN
  exact absurd hN (not_lt.2 (one_le_pow₀ hc))

theorem conjSrc_eq_of_cont (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s)
    (he : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hmem : ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ Valued.v (algebraMap E (w.adicCompletion E) (a : E)) < 1 := by
    intro a
    rw [hval, HeightOneSpectrum.valuation_lt_one_iff_mem]
  have hdir : ∀ x y : 𝓞 E, (y : E) = IsCMField.complexConj E (x : E) → x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    rw [hmem] at hx ⊢
    rw [hxy, ← he]
    exact lt_one_of_continuous s hs hx
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.SplitPts.conjE E) w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    refine ⟨hdir x y hxy, hdir y x ?_⟩
    rw [show (GlobalTheory.SplitPts.conjE E) (x : E) = IsCMField.complexConj E (x : E) from rfl] at hxy
    rw [hxy, IsCMField.complexConj_apply_apply]
  exact (eq_conjSrc hc).symm

theorem conjSrc_eq_iff (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w ↔ ¬ IsSplitAt w := by
  refine ⟨fun h hs => (GlobalTheory.SplitPts.over_split hs).1 h, fun h => ?_⟩
  by_contra hne
  apply h
  exact ⟨conjSrc (GlobalTheory.SplitPts.conjE E) w, hne,
    (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))⟩

theorem ext_of_cont {v w : HeightOneSpectrum (𝓞 E)} (s t : v.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) (ht : Continuous t)
    (hse : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hte : ∀ x : E, t (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) : s = t :=
  RingHom.ext fun y => congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hs ht
    (funext fun k => (hse k).trans (hte k).symm)) y

theorem cont_of_val {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s :=
  GlobalTheory.Mem.Chr.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective E w) s hv

theorem cj_spec (w : Pl E)
    (h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    Continuous (cj w) ∧ ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  unfold cj
  rw [dite_eq_left h]
  exact h.choose_spec

theorem cj_of_not (w : Pl E)
    (h : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    cj w = RingHom.id _ := by
  unfold cj
  rw [dite_eq_right h]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  intro E _ _ _ hU w
  by_cases hsp : IsSplitAt w
  · have hno : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
      rintro ⟨s, hs, he⟩
      exact (GlobalTheory.SplitPts.over_split hsp).1 (conjSrc_eq_of_cont w s hs he)
    have hid := cj_of_not w hno
    refine ⟨by rw [hid]; exact continuous_id, fun x => by rw [hid]; rfl, fun x => by rw [hid]; rfl,
      fun h => absurd hsp h, fun s hv he _ => hno ⟨s, cont_of_val s hv, he⟩⟩
  · obtain ⟨s0, ϖ, q, he0, hU0⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hU w) hsp
    have hc0 : Continuous s0 := cont_of_val s0 hU0.2.1
    obtain ⟨hcj, hecj⟩ := cj_spec w ⟨s0, hc0, he0⟩
    have heq : cj w = s0 := ext_of_cont _ _ hcj hc0 hecj he0
    have hsrc : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := (conjSrc_eq_iff w).2 hsp
    refine ⟨hcj, fun x => by rw [heq]; exact hU0.1 x, fun x => by rw [heq]; exact hU0.2.1 x,
      fun _ => ⟨hecj, ⟨ϖ, q, by rw [heq]; exact hU0, ?_⟩, fun x => ?_,
        fun s hv he => ext_of_cont _ _ (cont_of_val s hv) hcj he hecj⟩, fun _ _ _ => hsp⟩
    · exact (Formalism.UG.P.tjcosets_card_residue w).symm.trans hU0.2.2.2.2.2.2
    · rw [pLoc_conjFin]
      have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
          Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
          f (pLoc E v x) = cj w (pLoc E w x) := by
        rintro v rfl f hf hfe
        rw [ext_of_cont f (cj v) hf hcj hfe hecj]
      exact key _ hsrc _ (conjLoc_spec _ w).1 (conjLoc_spec _ w).2.1

end GlobalTheory.ConjAtPlace
end
end

section

namespace GlobalTheory.AnUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem exp_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f =>
    ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

theorem fr_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ Φ' : AnFr A L x0 g) (he : ∀ z, Φ'.e z = Φ.e z) (hH : ∀ z w, hermForm Φ'.Hm z w = hermForm Φ.Hm z w)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) : Φ.fr j z = Φ'.fr j z := by
  choose c hc using Φ.exists_chart_e
  have ne' : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → Φ'.fr j z ≠ 0 := fun j z h => Φ'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => Φ.fr (c z) z / Φ'.fr (c z) z
  have key : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → q z = Φ.fr j z / Φ'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U (c z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := Φ.fr_g j (c z) z hz
    have h2 := Φ'.fr_g j (c z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ Φ.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := (Φ.hol (L.L.U (c z0)) 0).1
    have h' : DifferentiableOn ℂ (Φ'.fr (c z0)) {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := by
      simpa only [he] using Φ'.fr_hol (c z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} :=
      ((Φ.fr_hol (c z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  have hper : ∀ z (a : Φ.lat), ‖q (z + Φ.lat.subtype a)‖ = ‖q z‖ := fun z a => by
    have ha' : (a : Fin g → ℂ) ∈ Φ'.lat := (Φ'.e_ker _).1 ((he _).trans ((Φ.e_ker _).2 a.2))
    have h : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U (c z) := by rw [Φ.e_add_lat a.2]; exact hc z
    have h1 := Φ.fr_per a a.2 (c z) z (hc z)
    have h2 := Φ'.fr_per a ha' (c z) z (by rw [he]; exact hc z)
    rw [hH, hH] at h2
    change ‖q (z + a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      Φ.χ_norm _ a.2, Φ'.χ_norm _ ha',
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := norm_periodic_const_range Φ.lat.subtype
    (by rw [AddSubgroup.coe_subtype, Subtype.range_coe]; exact Φ.span) q hq hper z 0
  have h0 : q 0 = 1 := by
    have := Φ'.fr_0 (c 0) (by rw [he]; exact hc 0)
    rw [← Φ.fr_0 (c 0) (hc 0)] at this
    change Φ.fr (c 0) 0 / Φ'.fr (c 0) 0 = 1
    rw [this, div_self (Φ.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact (div_eq_one_iff_eq (ne' j z hj)).1 hc0

end GlobalTheory.AnUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AnUniq.anFib_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A A' : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → A.ex = A'.ex ∧ ∀ ϑ, A.Reads 1 y.s ϑ ↔ A'.Reads 1 y.s ϑ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A A' hs hx hL
  have hex : A.ex = A'.ex := AnUniq.exp_eq A.ex_add A'.ex_add A.hol A'.hol (fun i => y.u (e i).1 (e i).2)
    (fun i => by simpa only [Equiv.symm_apply_apply] using A.der (e i))
    (fun i => by simpa only [Equiv.symm_apply_apply] using A'.der (e i))
  obtain ⟨Φ, k₁, f₁, -, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, f₂, -, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A' hs hx hL
  have hfr := AnUniq.fr_eq Φ.toAnFr Φ'.toAnFr (fun z => by rw [k₁, k₂, hex]) (fun z w => by rw [m₁, m₂])
  simp only [k₁, f₁, f₂] at hfr
  refine ⟨hex, fun ϑ => ⟨fun h j z pt h1 h2 hj => ?_, fun h j z pt h1 h2 hj => ?_⟩⟩
  · rw [← hex] at h1 hj
    rw [← hfr j z hj]
    exact h j z pt h1 h2 hj
  · rw [hfr j z hj]
    rw [hex] at h1 hj
    exact h j z pt h1 h2 hj
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.conj_torsion_translate_vacuum_entire_gaussian_growth : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ F : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → ∀ y, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl))) := by
  first | exact @GlobalTheory.ConjTranslate.conj_translate | exact GlobalTheory.ConjTranslate.conj_translate | (intros; apply GlobalTheory.ConjTranslate.conj_translate <;> assumption)
end
