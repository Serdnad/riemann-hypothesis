module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle116
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle119
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def absTy (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i

def ThetaC {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : A :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))

def GTCCurvPoly : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel → 2 ≤ P.k →
    d.L.TT = (P.TT : ℂ) →
    MAx3.G.PolyIn (fun u => d.QQ u 0 0 - u ^ (P.k + 1) • (1 : A) - u ^ P.k • ThetaC d) (P.k - 1) ∧
    MAx3.G.PolyIn (fun u => d.QQ u 1 0) P.k

def GTCCurvRTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (f g : ℂ → A) (Θ : A), 1 ≤ n →
    (∀ u v : ℂ, (u - v) • (f u * g v - g v * f u) = g u * f v - g v * f u) →
    MAx3.G.PolyIn (fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ) (n - 1) →
    MAx3.G.PolyIn g n → ∀ v, Θ * g v - g v * Θ = - g v

def GTCCurvBlock : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel →
    (∀ v : ℂ, ThetaC d * d.QQ v 1 0 - d.QQ v 1 0 * ThetaC d = - d.QQ v 1 0) →
    ∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
      algebraMap ℂ A ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvIdOfCut : Prop := GTCCurvPoly → GTCCurvRTT → GTCCurvBlock → GTCCurvId

theorem gTCCurvId_of_cut : GTCCurvIdOfCut := by
  intro hPo hR hB Wp Wq _ _ _ _ _ _ P Bs X d hyp ρ
  obtain ⟨hPl, hk, -, hAL, -, hRel, hQQ⟩ := hyp
  have hS : Wd.IsStart d.QQ (M.qC P) := by
    have h0 := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X).1
    rwa [show X.QQ = d.QQ from funext hQQ] at h0
  have hTT : d.L.TT = (P.TT : ℂ) := by
    rw [hAL.2.2.2.2.2.2.2.2.2.2.2.2, Formalism.FourierDecayAlt.P.NFx4.TT_eq hPl]
  obtain ⟨h1, h2⟩ := hPo P _ d hRel hk hTT
  have hc := hR _ P.k (fun u => d.QQ u 0 0) (fun u => d.QQ u 1 0) (ThetaC d) (by omega)
    (fun u v => Formalism.FourierDecayAlt.P.NFx4.SX.rtt_ent d hS u v 0 0 1 0) h1 h2
  exact hB P _ d hRel hc ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section fam

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def UX (X : Type) [TopologicalSpace X] : Set (X × ℂ) := Set.univ ×ˢ {τ : ℂ | τ ≠ 0}

theorem isOpen_UX : IsOpen (UX X) := isOpen_univ.prod isOpen_ne_zero_complex

def Good (Φ : X → V1 E) : Prop :=
  ContDiffOn ℝ ∞ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (UX X) ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ {τ | τ ≠ 0} →
      ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, (Φ v : ℂ → E) τ = 0

def IsInt (μ : Measure X) (ℓ : X → E →L[ℂ] E) (Φ : X → V1 E) (f : V1 E) : Prop :=
  ∀ τ : ℂ, τ ≠ 0 → (f : ℂ → E) τ = ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ

theorem good_cont_at {Φ : X → V1 E} (h : Good Φ) {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous (fun v => (Φ v : ℂ → E) τ) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩

theorem partial_fderiv {Φ : X → V1 E} (h : Good Φ) (v : X) {τ : ℂ} (hτ : τ ≠ 0) :
    fderiv ℝ (Φ v : ℂ → E) τ =
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ)).comp (ContinuousLinearMap.inr ℝ X ℂ) := by
  have hd : DifferentiableAt ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ) :=
    (h.1.differentiableOn (by simp)).differentiableAt (isOpen_UX.mem_nhds ⟨Set.mem_univ _, hτ⟩)
  have hi : HasFDerivAt (fun t : ℂ => (v, t)) (ContinuousLinearMap.inr ℝ X ℂ) τ := hasFDerivAt_prodMk_right v τ
  exact (hd.hasFDerivAt.comp τ hi).fderiv

theorem fd_contOn {Φ : X → V1 E} (h : Good Φ) :
    ContinuousOn (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2) (UX X) := by
  have h1 : ContinuousOn (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q).comp (ContinuousLinearMap.inr ℝ X ℂ)) (UX X) :=
    (h.1.continuousOn_fderiv_of_isOpen isOpen_UX (by simp)).clm_comp continuousOn_const
  exact h1.congr fun q hq => partial_fderiv h q.1 hq.2

theorem cd_partial {Φ : X → V1 E} (h : Good Φ) (w : ℂ) :
    ContDiffOn ℝ ∞ (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2 w) (UX X) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q) (ContinuousLinearMap.inr ℝ X ℂ w)) (UX X) :=
    (h.1.fderiv_of_isOpen isOpen_UX (by simp)).clm_apply contDiffOn_const
  refine h1.congr fun q hq => ?_
  rw [partial_fderiv h q.1 hq.2]
  rfl

theorem fderiv_zero_of {Φ : X → V1 E} (h : Good Φ) {K : Set ℂ} (hK : IsCompact K) (hK0 : K ⊆ {τ | τ ≠ 0}) :
    ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, fderiv ℝ (Φ v : ℂ → E) τ = 0 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK isOpen_ne_zero_complex hK0
  obtain ⟨C, hC, hz⟩ := h.2 L hL hLU
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  have hev : (Φ v : ℂ → E) =ᶠ[𝓝 τ] fun _ => (0 : E) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds (hKL hτ)) fun t ht => hz v hv t (interior_subset ht)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

section int

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

theorem good_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) :
    Integrable (fun v => ℓ v ((Φ v : ℂ → E) τ)) μ := by
  obtain ⟨C, hC, hz⟩ := h.2 {τ} isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (good_cont_at h hτ)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl, map_zero]

theorem fd_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) (w : ℂ) :
    Integrable (fun v => ℓ v (fderiv ℝ (Φ v : ℂ → E) τ w)) μ := by
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  have hc : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (hc.clm_apply continuous_const)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl]; simp

theorem rs_cont (hℓ : Continuous ℓ) : Continuous (fun v => (ℓ v).restrictScalars ℝ) :=
  (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).continuous.comp hℓ

theorem hasFDerivAt_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ0 : ℂ} (hτ0 : τ0 ≠ 0) :
    HasFDerivAt (fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ)
      (∫ v, ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0) ∂μ) τ0 := by
  have hn : 0 < ‖τ0‖ := norm_pos_iff.2 hτ0
  set r := ‖τ0‖ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hK : IsCompact (Metric.closedBall τ0 r) := isCompact_closedBall _ _
  have hK0 : Metric.closedBall τ0 r ⊆ {τ | τ ≠ 0} := by
    intro τ hτ
    show τ ≠ 0
    rintro rfl
    rw [Metric.mem_closedBall, dist_zero_left] at hτ
    linarith
  have hB : ∀ τ ∈ Metric.ball τ0 r, τ ≠ 0 := fun τ hτ => hK0 (Metric.ball_subset_closedBall hτ)
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  obtain ⟨Mf, hMf⟩ := (hC.prod hK).exists_bound_of_continuousOn
    ((fd_contOn h).mono fun q hq => ⟨Set.mem_univ _, hK0 hq.2⟩)
  obtain ⟨Ml, hMl⟩ := hC.exists_bound_of_continuousOn hℓ.continuousOn
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
    (F := fun τ v => ℓ v ((Φ v : ℂ → E) τ))
    (F' := fun τ v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ))
    (bound := Set.indicator C fun _ => Ml * Mf) (Metric.ball_mem_nhds τ0 hr0) ?_ (good_int μ ℓ h hℓ hτ0) ?_ ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds τ0 hr0] with τ hτ
    exact (hℓ.clm_apply (good_cont_at h (hB τ hτ))).aestronglyMeasurable
  · exact ((rs_cont ℓ hℓ).clm_comp hc0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    by_cases hv : v ∈ C
    · rw [Set.indicator_of_mem hv]
      have h1 := hMl v hv
      have h2 := hMf (v, τ) ⟨hv, Metric.ball_subset_closedBall hτ⟩
      calc ‖((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ)‖
          ≤ ‖(ℓ v).restrictScalars ℝ‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖ℓ v‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := by rw [ContinuousLinearMap.norm_restrictScalars]
        _ ≤ Ml * Mf := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    · rw [Set.indicator_of_notMem hv, hz v hv τ (Metric.ball_subset_closedBall hτ),
        ContinuousLinearMap.comp_zero, norm_zero]
  · exact (continuousOn_const.integrableOn_compact hC).integrable_indicator hC.measurableSet
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    exact ((ℓ v).restrictScalars ℝ).hasFDerivAt.comp τ (differentiableAt_of_punctured_smooth (Φ v).2 (hB τ hτ)).hasFDerivAt

theorem fderiv_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) (w : ℂ) :
    fderiv ℝ (f : ℂ → E) τ0 w = ∫ v, ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 w) ∂μ := by
  have hev : (f : ℂ → E) =ᶠ[𝓝 τ0] fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ :=
    Filter.eventually_of_mem (isOpen_ne_zero_complex.mem_nhds hτ0) fun τ hτ => hf τ hτ
  rw [hev.fderiv_eq, (hasFDerivAt_int μ ℓ h hℓ hτ0).fderiv]
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ0)
  have hI : Integrable (fun v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0)) μ := by
    refine Continuous.integrable_of_hasCompactSupport ((rs_cont ℓ hℓ).clm_comp hc0) ?_
    refine HasCompactSupport.intro hC fun v hv => ?_
    rw [hz v hv τ0 rfl, ContinuousLinearMap.comp_zero]
  rw [ContinuousLinearMap.integral_apply hI]
  rfl

theorem dz_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dz (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dz (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dz
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_sub
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_sub, map_smul]

theorem dzb_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dzb (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dzb (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dzb
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_add
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_add (f := _), map_smul]

end int

end fam

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section pts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem annZ_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    AnnZ P Bs = {ζ : ℂ | P.TT < Complex.normSq ζ} := by
  ext ζ
  simp only [Set.mem_setOf_eq]
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (X.fn j Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.2) •
        NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
  exact X.fn_apply j Φ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq)

theorem fnVal_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 0 (NF.muZ P.k P.r Bs.μsec ζ) = ζ := by
  show Q.zetaL _ _ _ _ _ _ = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem fnVal_two (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 2 (NF.muZ P.k P.r Bs.μsec ζ) = starRingEnd ℂ ζ := by
  show star (Q.zetaL _ _ _ _ _ _) = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]
  rfl

theorem fnVal_five (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 5 (NF.muZ P.k P.r Bs.μsec ζ) =
      (((Complex.normSq ζ - Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' : ℝ)) : ℂ)⁻¹ := by
  show (((Q.GGl _ _ _ _ _ : ℝ)) : ℂ)⁻¹ = _
  unfold Q.GGl
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem ggi_smooth (c : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)⁻¹)
      {ζ : ℂ | c < Complex.normSq ζ} := by
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ - c) := by
      simp only [Complex.normSq_apply]
      exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)).sub contDiff_const
    exact Complex.ofRealCLM.contDiff.comp this
  refine hn.contDiffOn.inv fun ζ hζ h0 => ?_
  have h : c < Complex.normSq ζ := hζ
  have : Complex.normSq ζ - c = 0 := by exact_mod_cast h0
  linarith

theorem conj_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => starRingEnd ℂ ζ) :=
  Complex.conjCLE.contDiff

theorem radDZ_fn_left (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 5)
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs (X.fn j * T) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ζ => Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec ζ)) (AnnZ P Bs) := by
    rcases hj with rfl | rfl | rfl
    · exact (contDiffOn_id (s := AnnZ P Bs)).congr fun ζ hζ => fnVal_zero P Bs hpl hζ
    · exact conj_smooth'.contDiffOn.congr fun ζ hζ => fnVal_two P Bs hpl hζ
    · exact (ggi_smooth _).congr fun ζ hζ => fnVal_five P Bs hpl hζ
  refine radDZ_fun_left hT _ hs fun Φ q hq => ?_
  rw [Module.End.mul_apply, radR_fn P Bs hpl X j _ q hq]

def Lp [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.Lin (B.hsVec (e ρ ζ)))).smulRight (e ρ ζ)).restrictScalars ℝ

theorem Lp_apply [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ)
    (Xv : Wq →L[ℂ] Wp) : Lp e ρ ζ Xv = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Xv) • e ρ ζ := rfl

theorem Lp_smooth [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P Bs e) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Lp e ρ) (AnnZ P Bs) := by
  rw [contDiffOn_clm_apply]
  intro y
  rw [annZ_eq P Bs hpl]
  exact (((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (he.1 ρ)).inner ℂ contDiffOn_const).smul (he.1 ρ)).congr
    fun ζ _ => rfl

theorem radR_fib (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q ∈
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' q.2 := by
  intro p hp
  unfold NF.radR
  rw [Set.indicator_of_mem hq]
  have hx := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq
  have h := Θ.2.2.2 _ hx p.1 hp.1 p.2 hp.2.1
  simp only at h
  rw [hp.2.2] at h
  exact h.symm

theorem radR_kap [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      ∑ ρ, f ρ • (inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) • e ρ q.2) := by
  obtain ⟨hpl, hk2, -, -, -, -, -⟩ := hH
  have hζ : P.TT < Complex.normSq q.2 := by
    have h := hq.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1] at h
    exact h
  let q' : MA.Qp P.r P.TT := ⟨q, hq.1, hζ⟩
  have hw : ((wR P.k P.TT q.2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
    exact Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)
  have hcoef : ∀ ρ, inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) =
      f ρ * inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) := by
    intro ρ
    have hK := congrFun (hk f Φ) ρ
    rw [actA_kap] at hK
    have s1 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he ((d.κ f).1 Φ) ρ
    have s2 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he Φ ρ
    unfold trR at hK
    rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s1, Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s2] at hK
    have h3 := congrFun (congrArg Subtype.val hK) q'
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, rawR] at h3
    unfold NF.radR
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    have h4 : ((wR P.k P.TT q.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.2))
        (B.hsVec (((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2))) =
        ((wR P.k P.TT q.2 : ℝ) : ℂ) * (f ρ * inner ℂ (B.hsVec (e ρ q.2))
          (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2)))) := by
      rw [h3]; ring
    exact mul_left_cancel₀ hw h4
  rw [(he.2 q.2 hζ).2.2 _ (radR_fib P Bs hpl _ q hq)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [hcoef ρ, mul_smul]

def dl {P : M.Par} (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ' => if ρ' = ρ then 1 else 0

theorem radR_kap_dl [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ (dl ρ)).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Lp e ρ q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) := by
  rw [radR_kap P Bs X d hH e he hk _ Φ q hq, Finset.sum_eq_single ρ]
  · simp [dl, Lp_apply]
  · intro b _ hb; simp [dl, hb]
  · intro h; exact absurd (Finset.mem_univ ρ) h

theorem radDZ_kap_left [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs ((d.κ (dl ρ)).1 * T) :=
  radDZ_comp_left hT (Lp e ρ) (Lp_smooth P Bs hH.1 he ρ) fun Φ q hq => by
    rw [Module.End.mul_apply, radR_kap_dl P Bs X d hH e he hk ρ _ q hq]

end pts

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

section

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_coefficient_commutation : RcComm := by
  intro k r E _ _ D f _ hf Z₁ Z₂ h₁ h₂ g hg
  exact Qx5.RZ_comm hf hg h₁ h₂

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end
