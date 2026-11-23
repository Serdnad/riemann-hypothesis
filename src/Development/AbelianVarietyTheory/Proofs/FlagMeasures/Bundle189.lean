module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle172
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle173
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.Count.Majorant

theorem decE_le_exp (q : ℕ) (hq : 1 ≤ q) (h d : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d) :
    decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * d)) := by
  have hs : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  have hm : d / Real.sqrt q - 1 ≤ min (2 * d ^ 2) (d / Real.sqrt q) := by
    have h1 : d / Real.sqrt q ≤ d := div_le_self hd hs
    exact le_min (by nlinarith [sq_nonneg (d - 1 / 4)]) (by linarith)
  have key : h / (8 * Real.sqrt q) * d = h / 8 * (d / Real.sqrt q) := by
    rw [div_mul_eq_mul_div, div_mul_div_comm]
  have hmul := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ h / 8)
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add, Real.exp_le_exp, key]
  nlinarith [hmul]

theorem dOp_eq_zero {n : ℕ} (ε : Fin n → Bool) (h0 : rkR ε = 0) (g : UJ ε) : dOp (uMat g) = 0 := by
  have hall : (∀ a, ε a = false) ∨ (∀ a, ε a = true) := by
    unfold GlobalTheory.Count.rkR at h0
    rcases Nat.min_eq_zero_iff.mp h0 with h1 | h1
    · left
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = true) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
    · right
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = false) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
  have hJ : Jm ε = 1 ∨ Jm ε = -1 := by
    rcases hall with hf | ht
    · right
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, hf, hij]
    · left
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, ht, hij]
  have hg : inUJ ε (uMat g) := g.2
  have hu : uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold inUJ at hg
    rcases hJ with hJ | hJ <;> rw [hJ] at hg <;> simpa using hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold GlobalTheory.Count.dOp
    have hle : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (uMat g))‖ ≤ 0 :=
      ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => by simp [EuclideanSpace.norm_eq]
    rw [le_antisymm hle (norm_nonneg _), Real.log_zero]
  · have hP0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inP, inG]
    obtain ⟨hb0, hb1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hu hP0
    rw [NormedSpace.exp_zero, mul_one] at hb0 hb1
    have hs0 : hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hs]
    rw [hs0, Real.sqrt_zero] at hb1
    nlinarith [Real.sqrt_pos.mpr (two_pos : (0 : ℝ) < 2)]

theorem majorant_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (h s : ℝ), 0 ≤ h → (rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) → Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  intro n ε h s hh hcase
  obtain ⟨C, -, hC⟩ := GlobalTheory.T.haar_ball_growth_unitaryJ n ε
  have hcont : Continuous (fun g : UJ ε => dOp (uMat g)) :=
    (GlobalTheory.Count.Cartan.cartan_distances n ε).2.2.2.2
  have hmeas : Measurable (fun g : UJ ε => dOp (uMat g)) := hcont.measurable
  have hdec : Continuous (decE (rkR ε) h) := by
    unfold GlobalTheory.Count.decE
    fun_prop
  have hint_meas : AEStronglyMeasurable
      (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) :=
    ((hdec.comp hcont).mul (Real.continuous_exp.comp (continuous_const.mul hcont))).aestronglyMeasurable
  by_cases hq : rkR ε = 0
  · have hz : ∀ g : UJ ε, dOp (uMat g) = 0 := fun g => dOp_eq_zero ε hq g
    have hI := GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (4 * n * rkR ε + 1) C hmeas (fun g => by simp [hz g]) hC (by linarith)
    refine hI.congr (ae_of_all _ fun g => ?_)
    simp [hz g, GlobalTheory.Count.decE]
  · have hq1 : 1 ≤ rkR ε := Nat.one_le_iff_ne_zero.mpr hq
    have hlt : 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h := hcase.resolve_left hq
    have hrk : rkR ε ≤ n := by
      unfold GlobalTheory.Count.rkR
      exact (min_le_left _ _).trans ((Finset.card_le_univ _).trans (Fintype.card_fin n).le)
    have hn : 1 ≤ n := hq1.trans hrk
    have hpos : ∀ g : UJ ε, 0 ≤ dOp (uMat g) := fun g =>
      ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    have hsq : 0 < Real.sqrt (rkR ε) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hq)
    have hab : (4 * n * rkR ε : ℝ) < h / (8 * Real.sqrt (rkR ε)) - s := by
      have : s + 4 * n * rkR ε < h / (8 * Real.sqrt (rkR ε)) :=
        (lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * Real.sqrt (rkR ε))).mpr (by linarith)
      linarith
    have hI := (GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (h / (8 * Real.sqrt (rkR ε)) - s) C hmeas hpos hC hab).const_mul (Real.exp (h / 8))
    refine hI.mono' hint_meas (ae_of_all _ fun g => ?_)
    have hd := hpos g
    have hE := decE_le_exp (rkR ε) hq1 h (dOp (uMat g)) hh hd
    have hnn : 0 ≤ decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      unfold GlobalTheory.Count.decE
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))
        ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt (rkR ε)) * dOp (uMat g))) *
            Real.exp (s * dOp (uMat g)) := mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
      _ = Real.exp (h / 8) * Real.exp (-((h / (8 * Real.sqrt (rkR ε)) - s) * dOp (uMat g))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

end GlobalTheory.Count.Majorant
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.LocEmb

variable {k r : ℕ}

theorem det_ne_zero_of_mem {g : Mat k r} (hg : g ∈ GG k r) : g.det ≠ 0 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH : (Hpk k r).det ≠ 0 := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact hH this.symm

theorem isClosed_GG : IsClosed (GG k r) := by
  show IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem continuousOn_inv : ContinuousOn (fun b : Mat k r => b⁻¹) {b | b.det ≠ 0} := by
  have : (fun b : Mat k r => b⁻¹) = fun b => (b.det)⁻¹ • b.adjugate := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ContinuousOn.smul ((continuous_id.matrix_det).continuousOn.inv₀ fun b hb => hb)
    continuous_id.matrix_adjugate.continuousOn

end GlobalTheory.SgInf.LocEmb

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LocEmb
variable {k r : ℕ}

def quotSet (K : Set (Mt k r)) : Set (Mt k r) :=
  (fun p : Mt k r × Mt k r => ((Matrix.of p.1 : Mat k r) * (Matrix.of p.2 : Mat k r)⁻¹ : Mat k r)) '' (K ×ˢ K)

theorem isCompact_quotSet {K : Set (Mt k r)} (hK : IsCompact K)
    (hd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0) : IsCompact (quotSet K) := by
  refine (hK.prod hK).image_of_continuousOn ?_
  have hc1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have hc2' : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  have hc2 : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹) (K ×ˢ K) :=
    continuousOn_inv.comp hc2'.continuousOn fun p hp => hd p.2 hp.2
  exact hc1.continuousOn.mul hc2

end GlobalTheory.SgInf.LocEmb

theorem GlobalTheory.SgInf.lint_compact_le_quot : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r))
    (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS →
    IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F →
    (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  intro k r S μG μS ν K₀ hS hG hSH hU hQ hK₀
  set K : Set (Mt k r) := K₀ ∩ {x | (Matrix.of x : Mat k r) ∈ GG k r} with hKdef
  have hGc : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := LocEmb.isClosed_GG
  have hK : IsCompact K := hK₀.inter_right hGc
  have hKd : ∀ x ∈ K, (Matrix.of x : Mat k r).det ≠ 0 := fun x hx => LocEmb.det_ne_zero_of_mem hx.2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨μS (LocEmb.quotSet K), (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r S μS hS hSH).1 _ (LocEmb.isCompact_quotSet hK hKd), ?_⟩
  intro F hF hinv

  have hfib : ∀ x : Mt k r, ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
      μS (LocEmb.quotSet K) * F x := by
    intro x
    set A : Set (Mt k r) := {s | (Matrix.of s : Mat k r) ∈ S ∧
      (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K} with hA
    have h1 : ∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤
        ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := by
      refine lintegral_mono_ae ?_
      have hnull : μS {x | Matrix.of x ∉ S} = 0 := hSH.2.2.1
      filter_upwards [(ae_iff (p := fun s : Mt k r => (Matrix.of s : Mat k r) ∈ S)).2 hnull] with s hs'
      by_cases hsK : (fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r) ∈ K
      · rw [Set.indicator_of_mem hsK, Set.indicator_of_mem (show s ∈ A from ⟨hs', hsK⟩)]
        exact le_of_eq (hinv _ hs' x)
      · rw [Set.indicator_of_notMem hsK]; simp
    have h2 : μS A ≤ μS (LocEmb.quotSet K) := by
      rcases A.eq_empty_or_nonempty with hAe | ⟨s₀, hs₀S, hs₀K⟩
      · rw [hAe, measure_empty]; simp
      set t : Mat k r := Matrix.of s₀ with ht
      have htS : t⁻¹ ∈ S := hS.2.2.2.2 _ hs₀S
      have hdx : (Matrix.of x : Mat k r).det ≠ 0 := by
        have := hKd _ hs₀K
        have h' : (Matrix.of (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r) : Mat k r) =
          (Matrix.of s₀ : Mat k r) * Matrix.of x := rfl
        rw [h', Matrix.det_mul] at this
        exact right_ne_zero_of_mul this
      have hsub : A ⊆ rmulM t⁻¹ ⁻¹' LocEmb.quotSet K := by
        intro s ⟨_, hsK⟩
        refine ⟨((fun i j => ((Matrix.of s : Mat k r) * Matrix.of x) i j : Mt k r),
          (fun i j => ((Matrix.of s₀ : Mat k r) * Matrix.of x) i j : Mt k r)), ⟨hsK, hs₀K⟩, ?_⟩
        show (Matrix.of s : Mat k r) * Matrix.of x * ((Matrix.of s₀ : Mat k r) * Matrix.of x)⁻¹ =
          (Matrix.of s : Mat k r) * t⁻¹
        rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of s : Mat k r),
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdx), Matrix.mul_one]
      calc μS A ≤ μS (rmulM t⁻¹ ⁻¹' LocEmb.quotSet K) := measure_mono hsub
        _ ≤ (μS.map (rmulM t⁻¹)) (LocEmb.quotSet K) :=
          Measure.le_map_apply (continuous_rmulM _).measurable.aemeasurable _
        _ = μS (LocEmb.quotSet K) := by rw [hU.1 _ htS]
    calc _ ≤ ∫⁻ s, A.indicator (fun _ => F x) s ∂μS := h1
      _ ≤ F x * μS A := lintegral_indicator_const_le _ _
      _ ≤ F x * μS (LocEmb.quotSet K) := by gcongr
      _ = μS (LocEmb.quotSet K) * F x := mul_comm _ _
  have hnullG : μG {x | Matrix.of x ∉ GG k r} = 0 := hG.2.2.1
  calc ∫⁻ x in K₀, F x ∂μG = ∫⁻ x, K₀.indicator F x ∂μG :=
        (lintegral_indicator hK₀.isClosed.measurableSet F).symm
    _ ≤ ∫⁻ x, K.indicator F x ∂μG := by
        refine lintegral_mono_ae ?_
        filter_upwards [(ae_iff (p := fun x : Mt k r => (Matrix.of x : Mat k r) ∈ GG k r)).2 hnullG] with x hx'
        by_cases h0 : x ∈ K₀
        · rw [Set.indicator_of_mem h0, Set.indicator_of_mem (show x ∈ K from ⟨h0, hx'⟩)]
        · rw [Set.indicator_of_notMem h0]; simp
    _ = ∫⁻ x, (∫⁻ s, K.indicator F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν :=
        hQ _ (hF.indicator hKm)
    _ ≤ ∫⁻ x, μS (LocEmb.quotSet K) * F x ∂ν := lintegral_mono hfib
    _ = μS (LocEmb.quotSet K) * ∫⁻ x, F x ∂ν := lintegral_const_mul _ hF
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.siegel_region_norm_bound : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ b : Fin (r + 1), eucl (s *ᵥ fvec k r z b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) ∧ eucl (s' *ᵥ fvec k r z' b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) := by
  first | exact @GlobalTheory.SgInf.frame_image_bound | exact GlobalTheory.SgInf.frame_image_bound | (intros; apply GlobalTheory.SgInf.frame_image_bound <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.continuousOn_majorantFlagLengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  first | exact @GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | exact GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | (intros; apply GlobalTheory.Amp.LenCont.lA_Sg_continuousOn <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.twoFlagsGramNumber_mul_topMinorNorm_le_two_pow : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Yv k r z z' γ x * Yv k r z' z γ⁻¹ (γ * x) * Dr k r z z' γ ≤ 2 ^ r := by
  first | exact @GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le | exact GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le | (intros; apply GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.CovMul

open GlobalTheory.HomCovolume GlobalTheory.SnMass.FrameDual

theorem hasDom_ideLat {E : Type} [Field E] [NumberField E] (hE : IsTotallyComplex E)
    (a : FractionalIdeal (𝓞 E)⁰ E) (ha : a ≠ 0) {c : ℝ} (hc : 0 < c) :
    HasDom volume (ideLat a c : Set (InfinitePlace E → ℂ))
      (ENNReal.ofReal ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E *
        c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  obtain ⟨L₀, hL₀, hcov⟩ := exists_idealLat E hE a ha
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z, f z = c⁻¹ • z := fun _ => rfl
  have hrank : Module.finrank ℝ (InfinitePlace E → ℂ) = 2 * Fintype.card (InfinitePlace E) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hdet : LinearMap.det f = (c ^ (2 * Fintype.card (InfinitePlace E)))⁻¹ := by
    change LinearMap.det (c⁻¹ • LinearMap.id) = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hrank, inv_pow]
  have hpos : 0 < c ^ (2 * Fintype.card (InfinitePlace E)) := pow_pos hc _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ ideLat a c := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · have h1 := h w
      rw [hf, Pi.smul_apply, Complex.real_smul] at h1
      rw [← h1, Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast hc.ne')]
    · rw [hf, Pi.smul_apply, Complex.real_smul, h w, Complex.ofReal_inv,
        inv_mul_cancel_left₀ (by exact_mod_cast hc.ne')]
  refine ⟨GlobalTheory.latticeDomain L, GlobalTheory.measurableSet_latticeDomain L, fun v => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := GlobalTheory.existsUnique_add_mem_latticeDomain L v
    refine ⟨z, ⟨(hL _).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hlD⟩
    exact congrArg Subtype.val (hu ⟨l, (hL l).2 hl⟩ hlD)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (GlobalTheory.isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet,
      abs_of_pos (inv_pos.2 hpos), div_inv_eq_mul] at h
    have hfin : volume (GlobalTheory.latticeDomain L) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]

theorem value_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] (t t' : ℕ) :
    ((FractionalIdeal.absNorm (dInv E t * dInv E t') : ℚ) : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E =
      (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) *
        |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) := by
  have hD : 0 < |(NumberField.discr F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hdisc : |(discr E : ℝ)| = |(NumberField.discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℝ) (natAbs_discr_sq (F := F) (E := E) h2)
    simpa [Nat.cast_natAbs] using h1
  have hcard : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hexp : |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) =
      ((|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t * (|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t') *
        |(NumberField.discr F : ℝ)| := by
    have e1 : (2 * (t : ℝ)) = ((2 * t : ℕ) : ℝ) := by push_cast; ring
    have e2 : (2 * (t' : ℝ)) = ((2 * t' : ℕ) : ℝ) := by push_cast; ring
    rw [Real.rpow_sub hD, Real.rpow_sub hD, Real.rpow_one, e1, e2, Real.rpow_natCast,
      Real.rpow_natCast, pow_mul, pow_mul, inv_pow, inv_pow]
    field_simp
  rw [map_mul, Rat.cast_mul, absNorm_dInv, absNorm_dInv, vInv_pow E hE, hdisc,
    Real.sqrt_sq hD.le, hcard, hexp]
  ring

theorem hasDom_ideLat_dInv_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hU t t' c hc
  have h := hasDom_ideLat hσ.2.1 (dInv E t * dInv E t')
    (mul_ne_zero (dInv_ne_zero t) (dInv_ne_zero t')) hc
  rwa [value_eq hσ.2.1 hσ.2.2.1 t t'] at h

end GlobalTheory.SnMass.VolN.CovMul
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  first | exact @GlobalTheory.LeviIso.spansFlag_flagAt | exact GlobalTheory.LeviIso.spansFlag_flagAt | (intros; apply GlobalTheory.LeviIso.spansFlag_flagAt <;> assumption)
end

section

open Formalism.HermitianLatticeCounting.S6

theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) → ∀ v : V, GlobalTheory.RowStab.gen H J e ρ c (GlobalTheory.RowStab.gen H J e (-ρ) c' v) = v := by
  first | exact @GlobalTheory.RowStab.gen_comp_gen_neg | exact GlobalTheory.RowStab.gen_comp_gen_neg | (intros; apply GlobalTheory.RowStab.gen_comp_gen_neg <;> assumption)
end

section

open Formalism.HermitianLatticeCounting.S6

theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) → ∀ u v : V, H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  first | exact @GlobalTheory.RowStab.gen_isometry | exact GlobalTheory.RowStab.gen_isometry | (intros; apply GlobalTheory.RowStab.gen_isometry <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.unitaryRealTraceBump_peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧ (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧ ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1, ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  first | exact @GlobalTheory.KFinAvg.peak_properties | exact GlobalTheory.KFinAvg.peak_properties | (intros; apply GlobalTheory.KFinAvg.peak_properties <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian : ∀ k r : ℕ, ∃ μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), GlobalTheory.KFinAvg.IsHaarKH k r μ := by
  first | exact @GlobalTheory.KFinAvg.exists_isHaarKH | exact GlobalTheory.KFinAvg.exists_isHaarKH | (intros; apply GlobalTheory.KFinAvg.exists_isHaarKH <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ), (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  first | exact @GlobalTheory.KFinAvg.peak_pow_polynomial | exact GlobalTheory.KFinAvg.peak_pow_polynomial | (intros; apply GlobalTheory.KFinAvg.peak_pow_polynomial <;> assumption)
end
