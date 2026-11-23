module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle153
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTest
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConjScale

open Topology Filter

theorem integral_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) :
    ∫ t, φ (L *ᵥ t) = |L.det|⁻¹ * ∫ t, φ t := by
  have hc : Continuous (Matrix.toLin' L) := LinearMap.continuous_of_finiteDimensional _
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have h2 : ∫ t, φ t ∂(Measure.map (Matrix.toLin' L) volume) = ∫ t, φ (Matrix.toLin' L t) :=
    integral_map hc.measurable.aemeasurable hφ.aestronglyMeasurable
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul] at h2
  simpa using h2.symm

theorem hasCompactSupport_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : HasCompactSupport φ) : HasCompactSupport (fun t => φ (L *ᵥ t)) := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (Matrix.toLinearEquiv' L (Matrix.invertibleOfIsUnitDet L hu)).toContinuousLinearEquiv
  exact hφ.comp_homeomorph e.toHomeomorph

theorem scalar_eq_inv_det {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X → X) (hT : Measurable T)
    (h : X → ℝ) (hh : Measurable h) {d : ℕ} (t : X → Fin d → ℝ) (ht : Measurable t)
    (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0) (c : NNReal) (hc : μ.map T = (c : ENNReal) • μ)
    (hTt : ∀ᵐ g ∂μ, t (T g) = L *ᵥ t g) (C : ℝ) (hC : 1 ≤ C) (h1 : ∀ g, h (T g) ≤ C * h g)
    (h2 : ∀ g, h g ≤ C * h (T g)) (ρ : ℝ) (hρ : 0 < ρ) (hfin : μ {g | h g < ρ} ≠ ⊤)
    (hlim : ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ ρ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | h g < r₁}, φ (fun i => t g i / r) ∂μ)
        (𝓝[>] 0) (𝓝 (∫ x, φ x))) :
    (c : ℝ) = |L.det|⁻¹ := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  let b : ContDiffBump (0 : Fin d → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : (Fin d → ℝ) → ℝ := b
  have hφc : Continuous φ := b.continuous
  have hφs : HasCompactSupport φ := b.hasCompactSupport
  have hφp : 0 < ∫ x, φ x := b.integral_pos
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => b.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => b.le_one
  let ψ : (Fin d → ℝ) → ℝ := fun x => φ (L *ᵥ x)
  have hψc : Continuous ψ := hφc.comp (continuous_const.matrix_mulVec continuous_id)
  have hψs : HasCompactSupport ψ := hasCompactSupport_comp_mulVec L hL φ hφs
  have hψi : ∫ x, ψ x = |L.det|⁻¹ * ∫ x, φ x := integral_comp_mulVec L hL φ hφc
  have hr1 : 0 < ρ / C := div_pos hρ hC0
  have hr1' : ρ / C ≤ ρ := div_le_self hρ.le hC
  have hr2 : 0 < ρ / C / C := div_pos hr1 hC0
  have hr2' : ρ / C / C ≤ ρ := (div_le_self hr1.le hC).trans hr1'
  have hB1 : MeasurableSet {g | h g < ρ / C} := measurableSet_lt hh measurable_const
  have hs1 : {g | h g < ρ / C / C} ⊆ T ⁻¹' {g | h g < ρ / C} := by
    intro g hg
    have hg : h g < ρ / C / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h1 g
    show h (T g) < ρ / C
    linarith
  have hs2 : T ⁻¹' {g | h g < ρ / C} ⊆ {g | h g < ρ} := by
    intro g hg
    have hg : h (T g) < ρ / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h2 g
    show h g < ρ
    linarith
  have hm : ∀ r : ℝ, Measurable (fun g => (fun i => t g i / r : Fin d → ℝ)) := fun r =>
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp ht).div_const r
  have hint : ∀ r : ℝ, IntegrableOn (fun g => ψ (fun i => t g i / r)) {g | h g < ρ} μ := by
    intro r
    refine Measure.integrableOn_of_bounded (M := 1) hfin (hψc.measurable.comp (hm r)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun g => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  have key : ∀ r : ℝ, (c : ℝ) * ∫ g in {g | h g < ρ / C}, φ (fun i => t g i / r) ∂μ
      = ∫ g in T ⁻¹' {g | h g < ρ / C}, ψ (fun i => t g i / r) ∂μ := by
    intro r
    have e1 := setIntegral_map (μ := μ) (g := T) (f := fun g => φ (fun i => t g i / r)) hB1
      (hφc.measurable.comp (hm r)).aestronglyMeasurable hT.aemeasurable
    rw [hc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul] at e1
    rw [e1]
    refine integral_congr_ae (ae_restrict_of_ae (hTt.mono fun g hg => ?_))
    have e2 : ∀ y : Fin d → ℝ, (fun i => y i / r) = r⁻¹ • y := fun y => by
      ext i; simp [div_eq_inv_mul]
    show φ (fun i => t (T g) i / r) = φ (L *ᵥ fun i => t g i / r)
    rw [e2, e2, hg, Matrix.mulVec_smul]
  have l1 := (hlim _ hr1 hr1' φ hφc hφs).const_mul (c : ℝ)
  have l2 := hlim _ hr2 hr2' ψ hψc hψs
  have l3 := hlim _ hρ le_rfl ψ hψc hψs
  have a1 : ∫ x, ψ x ≤ c * ∫ x, φ x := by
    refine le_of_tendsto_of_tendsto l2 l1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set ((hint r).mono_set hs2) (Eventually.of_forall fun g => hφ0 _) (Filter.Eventually.of_forall hs1)
  have a2 : c * ∫ x, φ x ≤ ∫ x, ψ x := by
    refine le_of_tendsto_of_tendsto l1 l3 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set (hint r) (Eventually.of_forall fun g => hφ0 _) (Filter.Eventually.of_forall hs2)
  exact mul_right_cancel₀ hφp.ne' ((le_antisymm a2 a1).trans hψi)

theorem hs_conj_le {n : ℕ} {ε : Fin n → Bool} (m g : Formalism.REAL.UJ ε) :
    Formalism.REAL.hs (uMat (m * g * m⁻¹) - 1) ≤
      Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) * Formalism.REAL.hs (uMat g - 1) := by
  have a : uMat (m * g * m⁻¹) = uMat m * uMat g * uMat m⁻¹ := rfl
  have b : uMat m * uMat m⁻¹ = 1 := by
    have : uMat m * uMat m⁻¹ = uMat (m * m⁻¹) := rfl
    rw [this, mul_inv_cancel]; rfl
  have e : uMat (m * g * m⁻¹) - 1 = uMat m * (uMat g - 1) * uMat m⁻¹ := by
    rw [a, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, b]
  rw [e]
  refine (Formalism.REAL.frobenius_mul_le _ _).trans ?_
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (Formalism.REAL.frobenius_mul_le _ _) (Formalism.REAL.frobenius_nonneg _)

theorem map_conj_eq_inv_det_smul (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (hS : ∀ g, g ∈ S ↔ uMat g - 1 ∈ A) (hcl : IsClosed (S : Set (Formalism.REAL.UJ ε)))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ)
    (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S)
    (hmL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) (hL : L.det ≠ 0) :
    μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  have hSe : (S : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := Set.ext hS
  obtain ⟨-, hK, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hsp μ (hSe ▸ hμ)
  obtain ⟨h1, h2, h3⟩ := hμ
  have hp : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := Metric.measure_ball_pos _ _ one_pos
  have hf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤ := measure_ball_lt_top
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ :=
    (((h3.eventually (lt_mem_nhds hp)).and (h3.eventually (gt_mem_nhds hf))).and self_mem_nhdsWithin).exists
  have hr : 0 < r := hr
  have hcu : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((hcu.sub continuous_const).matrix_elem i j).norm).pow 2
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at hr1
  have hfin : μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
    exact lt_irrefl _ hr2
  obtain ⟨c, hcμ⟩ := GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing n ε S μ hcl h1 h2 hK hne m hm
  have hC0 : 0 ≤ Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) :=
    mul_nonneg (Formalism.REAL.frobenius_nonneg _) (Formalism.REAL.frobenius_nonneg _)
  have hT : Continuous (fun u : Formalism.REAL.UJ ε => m * u * m⁻¹) := by fun_prop
  have ht : Continuous (fun (g : Formalism.REAL.UJ ε) (i : Fin d) => (((uMat g - 1) * (E i)ᴴ).trace).re) :=
    continuous_pi fun i => Complex.continuous_re.comp
      (((hcu.sub continuous_const).matrix_mul continuous_const).matrix_trace)
  have key := scalar_eq_inv_det μ (fun u => m * u * m⁻¹) hT.measurable _ hc.measurable _ ht.measurable L hL c hcμ
    ?_ (Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) + 1) (by linarith) ?_ ?_ (min r₀ (r ^ 2))
    (lt_min hr₀ (by positivity)) ?_ (fun r₁ a b => hlim r₁ a (b.trans (min_le_left _ _)))
  · rw [hcμ, ← key, ENNReal.ofReal_coe_nnreal]
  · have : ∀ᵐ g ∂μ, g ∈ (S : Set (Formalism.REAL.UJ ε)) := h1
    filter_upwards [this] with g hg
    exact GlobalTheory.T.unitaryJ_lieCoords_conj_linear n ε A d E hE hsp g m L ((hS g).1 hg) ((hS _).1 (S.inv_mem hg)) hmL
  · intro g
    have := hs_conj_le m g
    have := Formalism.REAL.frobenius_nonneg (uMat g - 1)
    linarith
  · intro g
    have h4 := hs_conj_le m⁻¹ (m * g * m⁻¹)
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rw [e, inv_inv] at h4
    have := Formalism.REAL.frobenius_nonneg (uMat (m * g * m⁻¹) - 1)
    linarith
  · refine ne_top_of_le_ne_top hfin (measure_mono fun g hg => ?_)
    have hg : Formalism.REAL.hs (uMat g - 1) < min r₀ (r ^ 2) := hg
    exact Real.sqrt_le_iff.2 ⟨hr.le, (hg.trans_le (min_le_right _ _)).le⟩

end GlobalTheory.GaugeConjScale
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.StabQuot

theorem sigmaFinite_quot {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨f, hf0, hfm, hfi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hm : Measurable fun x => (f x : ℝ≥0∞) := hfm.coe_nnreal_ennreal
  have hact : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 :=
    (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  have hm2 : Measurable fun p : Mt k r × Mt k r => (f (lmulM (Matrix.of p.2) p.1) : ℝ≥0∞) :=
    hm.comp (hact.comp measurable_swap)
  set F : Mt k r → ℝ≥0∞ := fun x => ∫⁻ s, (f (lmulM (Matrix.of s) x) : ℝ≥0∞) ∂μS with hF
  have hFm : Measurable F := hm2.lintegral_prod_right'
  have hFi : ∫⁻ x, F x ∂ν < 1 := (hq _ hm).symm.trans_lt hfi
  have hFpos : ∀ x, 0 < F x := fun x => by
    have hx : Measurable fun s => (f (lmulM (Matrix.of s) x) : ℝ≥0∞) :=
      hm.comp (continuous_rmulM (k := k) (r := r) (Matrix.of x)).measurable
    rw [hF, lintegral_pos_iff_support hx]
    have : Function.support (fun s => (f (lmulM (Matrix.of s) x) : ℝ≥0∞)) = Set.univ := by
      ext s; simp [(hf0 _).ne']
    rw [this]
    exact Measure.measure_univ_pos.mpr hS
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞))⁻¹ ≤ F x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e : {x | (((0 : ℕ) : ℝ≥0∞))⁻¹ ≤ F x} = {x | F x = ∞} := by ext x; simp
      show ν {x | (((0 : ℕ) : ℝ≥0∞))⁻¹ ≤ F x} < ∞
      rw [e, measure_eq_top_of_lintegral_ne_top hFm.aemeasurable (hFi.trans ENNReal.one_lt_top).ne]
      simp
    · exact (meas_ge_le_lintegral_div hFm.aemeasurable (by simp) (by simpa using hn.ne')).trans_lt
        (ENNReal.div_lt_top (hFi.trans ENNReal.one_lt_top).ne (by simp))
  · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hFpos x).ne'
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

theorem exists_sigmaFinite_quot : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (μG μ : Measure (Mt k r)), IsHaarOn (UH (Hpk k r)) μG → IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ 1 μ → γ ∈ UH (Hpk k r) → SigmaFinite μ ∧ IsHaarOn (Rset k r γ⁻¹) μ ∧ IsNormalFormStabilizerMeasure k r hj z z' γ 1 (μ.map (conjM γ⁻¹)) ∧ ∃ ν : Measure (Mt k r), SigmaFinite ν ∧ ν {x | Matrix.of x ∉ UH (Hpk k r)} = 0 ∧ IsQuotMeas μG (μ.map (conjM γ⁻¹)) ν := by
  intro k r j hj z z' γ μG μ hG hN hγ
  obtain ⟨-, -, a3, -, a5, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z' z γ⁻¹ 1 μ one_pos hN
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG hγ)] at a5
  obtain ⟨-, b2, b3, b4, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' γ 1 _ one_pos a5
  obtain ⟨ν, hν⟩ := GlobalTheory.SgQuot.exists_isQuotMeas k r _ μG _ b2 hG b3 b4
  haveI := hG.1
  haveI := b3.1
  exact ⟨a3.1, a3, a5, ν, sigmaFinite_quot b3.2.1 hν,
    (GlobalTheory.Amp.CutQuot.cut_quotient k r _ μG _ ν b2 hG b3 b4 hν).1, hν⟩

end GlobalTheory.DegVol.StabQuot
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PerpPos

theorem re_pos {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {k r : ℕ}
    (hA : GlobalTheory.SA.Amb S k r) {T : ℕ} (hT : 0 < T) (F : FlagG S r (T : E)) {x : S.V}
    (hx : x ∈ orth S F.Xplus) (hxX : x ∉ F.X) (τ : E →+* ℂ) : 0 < (τ (S.hT x x)).re := by
  have hsym : ∀ a b : S.V, S.hT a b = 0 → S.hT b a = 0 := fun a b h => by
    rw [← S.herm.eq a b, h, map_zero]
  have hx' : ∀ y ∈ F.Xplus, S.hT y x = 0 := fun y hy => by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx y hy
  have hzP : F.z ∈ F.Xplus := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hXP : ∀ y ∈ F.X, y ∈ F.Xplus := fun y hy => Submodule.mem_sup_left hy
  have hspan : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ y ∈ F.X, S.hT y w = 0 := by
    intro w hw y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hw a
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
  have hXz : ∀ y ∈ F.X, S.hT y F.z = 0 := hspan _ F.z_orth
  have hXX : ∀ y ∈ F.X, ∀ y' ∈ F.X, S.hT y y' = 0 := fun y hy y' hy' =>
    hspan y' (fun a => hsym _ _ (hspan _ (fun b => F.e_iso b a) y' hy')) y hy
  have hTne : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hzX : F.z ∉ F.X := fun h => by
    have := hXz _ h
    rw [F.z_norm, neg_eq_zero] at this
    exact hTne this
  have hxP : x ∉ F.Xplus := fun h => by
    obtain ⟨ξ, hξ, w, hw, hsum⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 := hx' _ hzP
    rw [← hsum, map_add (f := _), map_smul, hsym _ _ (hXz _ hξ), F.z_norm, zero_add, smul_eq_mul, mul_eq_zero,
      neg_eq_zero] at h1
    rcases h1 with h1 | h1
    · apply hxX
      rw [← hsum, h1, zero_smul, add_zero]
      exact hξ
    · exact hTne h1
  have hdX : finrank E F.X = r := by
    have := finrank_span_eq_card F.e_indep
    rwa [Fintype.card_fin] at this
  have hdP : finrank E F.Xplus = r + 1 := by
    have := Submodule.finrank_sup_span_singleton hzX
    rwa [hdX] at this
  have hdU : finrank E (F.Xplus ⊔ Submodule.span E {x} : Submodule E S.V) = r + 2 := by
    have := Submodule.finrank_sup_span_singleton hxP
    rwa [hdP] at this
  by_contra hle
  rw [not_lt] at hle
  have := hA.neg τ (F.Xplus ⊔ Submodule.span E {x}) (by
    intro y hy
    obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨ξ, hξ, w, hw, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have e : S.hT (ξ + a • F.z + c • x) (ξ + a • F.z + c • x) =
        (star a * a) * (-(T : E)) + (star c * c) * S.hT x x := by
      simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
        smul_eq_mul, hXX _ hξ _ hξ, hXz _ hξ, hsym _ _ (hXz _ hξ), hx' _ (hXP _ hξ),
        hsym _ _ (hx' _ (hXP _ hξ)), hx' _ hzP, hsym _ _ (hx' _ hzP), F.z_norm,
        starRingEnd_apply]
      ring
    have n : ∀ b : E, τ (star b * b) = (Complex.normSq (τ b) : ℂ) := fun b => by
      rw [map_mul, hA.cm, Complex.normSq_eq_conj_mul_self]
    rw [e, map_add (f := _), map_mul τ (star a * a), map_mul τ (star c * c), n, n, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, map_neg, map_natCast, Complex.neg_re, Complex.natCast_re]
    have h1 := Complex.normSq_nonneg (τ a)
    have h2 := Complex.normSq_nonneg (τ c)
    have h3 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    nlinarith [mul_nonneg h1 h3, mul_nonneg h2 (neg_nonneg.2 hle)])
  omega

theorem trace_pos {K : Type} [Field K] [NumberField K] (y : K) (hp : ∀ τ : K →+* ℂ, 0 < (τ y).re) :
    0 < Algebra.trace ℚ K y := by
  have e := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := y)
  have e2 : ((Algebra.trace ℚ K y : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ y).re := by
    rw [← Complex.re_sum, ← e]
    simp
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have : (0 : ℝ) < ((Algebra.trace ℚ K y : ℚ) : ℝ) := by
    rw [e2]
    exact Finset.sum_pos (fun σ _ => hp (σ : K →+* ℂ)) Finset.univ_nonempty
  exact_mod_cast this

theorem trace_pos_perp : ∀ (D : D7) (T' : ℕ) (F' : Fg D ((T' : ℕ) : D.host.E)), 0 < T' →
    ∀ x ∈ orth (hS D) (Xplus F'), x ∉ Xsp F' → 0 < Algebra.trace ℚ D.host.E ((hS D).hT x x) := by
  intro D T' F' hT x hx hxX
  have hA : GlobalTheory.SA.Amb (hS D) D.R.k D.R.rS :=
    GlobalTheory.SA.AmbSig.amb_of_sig _ _ _ _ D.sp.cm.cmUnram.2.1 (D.sp.Y_sig 0) D.sp.baseSpace_signature_eq
  exact trace_pos _ (re_pos hA hT F'.fl hx hxX)

end GlobalTheory.LoopC.PerpPos
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ClassMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem M_eq_Mof (S : Frames L r k) {C : Set S.FrP} {p : S.FrP} (hp : p ∈ C) {d : S.Datum}
    {Λ : Submodule L.O S.V} (hC : S.Fr d Λ = C) : S.M d Λ = S.Mof p.1 p.2 := by
  subst hC
  exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1 p hp).2.symm

theorem class_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, (∀ Q : ℕ → Prop, (S.sumData fun d => S.nT d C fun Λ => Q (S.be d Λ)) ≤ ∑' Mh : {Mh : Submodule L.O S.V // S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) ∧ Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup)}, S.massSig Mh) ∧ (S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ) = S.massSig (S.Mof p.1 p.2) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp
  have hM : ∀ d Λ, S.Fr d Λ = C → S.M d Λ = S.Mof p.1 p.2 := fun d Λ hF => M_eq_Mof S hp hF
  constructor
  · intro Q
    refine (GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass L r k S C (fun d Λ => Q (S.be d Λ)) ?_).trans_le ?_
    · intro h hh d Λ hT hQ
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show Q (S.be (h • d) (h • Λ))
      unfold Frames.be
      rw [hM', hsat']
      exact hQ
    · unfold Frames.massSig
      rw [ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum fun o => ?_
      split_ifs with hcond
      · obtain ⟨d, hT, hQ, hF⟩ := hcond
        have hbasic := GlobalTheory.HL.TermBasic.term_basic L r k S d o.out hT
        have hSD : IsSD L S.Hm o.out := hbasic.1
        have hle : S.M d o.out ≤ S.sat o.out := hbasic.2.2.1
        rw [hM d o.out hF] at hle
        have hQ' : Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex (S.sat o.out).toAddSubgroup) := by
          have h := hQ
          unfold Frames.be at h
          rw [hM d o.out hF] at h
          exact h
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ⟨S.sat o.out, hle,
          fun x hx => (Submodule.mem_inf.mp hx).2,
          fun x hx y hy => (hSD.2 y).mpr (Submodule.mem_inf.mp hy).1 x (Submodule.mem_inf.mp hx).1, hQ'⟩)
        rw [if_pos ⟨hSD, rfl⟩]
      · exact zero_le
  · have hb : ∀ Λ : Submodule L.O S.V, (∃ d, S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C) ↔
        (IsSD L S.Hm Λ ∧ S.sat Λ = S.Mof p.1 p.2) := by
      intro Λ
      constructor
      · rintro ⟨d, hT, hB, hF⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1,
          (show S.M d Λ = S.sat Λ from hB).symm.trans (hM d Λ hF)⟩
      · rintro ⟨hSD, hsat⟩
        obtain ⟨d, hT, hF, hB⟩ := GlobalTheory.HL.PrimTerm.term_of_primitive L r k S Λ hSD C hC p hp hsat
        exact ⟨d, hT, hB, hF⟩
    refine (GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass L r k S C (fun d Λ => S.BBzero d Λ) ?_).trans ?_
    · intro h hh d Λ hT hB
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show S.M (h • d) (h • Λ) = S.sat (h • Λ)
      rw [hM', hsat']
      exact hB
    · unfold Frames.massSig
      exact tsum_congr fun o => if_congr (hb o.out) rfl rfl

end GlobalTheory.HL.ClassMass
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.discreteSeriesKernel_summable_with_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  first | exact @GlobalTheory.Dec.kernel_abs_bound | exact GlobalTheory.Dec.kernel_abs_bound | (intros; apply GlobalTheory.Dec.kernel_abs_bound <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.continuous_automorphicKernel_discreteSeriesTest : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) := by
  first | exact @GlobalTheory.Dec.continuous_kern_phe | exact GlobalTheory.Dec.continuous_kern_phe | (intros; apply GlobalTheory.Dec.continuous_kern_phe <;> assumption)
end
