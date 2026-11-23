module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.Cancel

open ValuativeRel
open scoped Topology NNReal

theorem compact_subset_cball {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {K : Set F} (hK : IsCompact K) :
    ∃ s : Fˣ, K ⊆ GlobalTheory.SplitWeil.cball s := by
  refine hK.elim_directed_cover (fun s : Fˣ => GlobalTheory.SplitWeil.cball s) GlobalTheory.SplitWeil.isOpen_cball ?_ ?_
  · intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [GlobalTheory.SplitWeil.cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩
  · intro a b
    rcases le_total (valuation F (a : F)) (valuation F (b : F)) with h | h
    · exact ⟨b, fun x hx => le_trans (show valuation F x ≤ _ from hx) h, fun x hx => hx⟩
    · exact ⟨a, fun x hx => hx, fun x hx => le_trans (show valuation F x ≤ _ from hx) h⟩

theorem punctured_neBot (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : (𝓝[≠] (0 : F)).NeBot := by
  by_contra h
  rw [Filter.not_neBot, ← isOpen_singleton_iff_punctured_nhds] at h
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (h.mem_nhds rfl)
  exact s.ne_zero (hs (by simp [GlobalTheory.SplitWeil.cball]))

theorem mul_mem_cball_iff {F : Type} [Field F] [ValuativeRel F] (a s : Fˣ) (x : F) :
    valuation F ((a : F) * x) ≤ valuation F (s : F) ↔ valuation F x ≤ valuation F ((a⁻¹ * s : Fˣ) : F) := by
  rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    le_inv_mul_iff₀ (by simp [zero_lt_iff])]

theorem gauss_cancel : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → (∫ z in {z : E | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ (Algebra.norm F z) ∂μ) + (nabs F t : ℂ) * ∫ z in {z : E | (t : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _ t ht
  borelize F
  obtain ⟨hfd, hring, -, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := GlobalTheory.SplitWeil.t2Space F
  haveI := punctured_neBot F
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  haveI : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot F E 0
  haveI : LocallyCompactSpace E := by
    obtain ⟨L, -, h1, h2⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1
    exact h1.locallyCompactSpace_of_mem_nhds_of_addGroup (h2.mem_nhds L.zero_mem)
  have hμ0 : μ {0} = 0 := measure_singleton 0
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.SplitWeil.exists_isUnitVol F
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.exists_integral_closedBall_addChar_eq_zero F lam ψ hψ hψ1 hψ0
  have hm : ∀ a : F, Measurable fun z : E => a * Algebra.norm F z := fun a =>
    (continuous_const.mul hN).measurable
  let m : Fˣ → Measure F := fun a => μ.map fun z : E => (a : F) * Algebra.norm F z
  let n : Fˣ → Measure F := fun a => distribHaarChar F a • m a
  have hmc : ∀ a, IsFiniteMeasureOnCompacts (m a) := fun a => ⟨fun K hK => by
    obtain ⟨s, hs⟩ := compact_subset_cball hK
    obtain ⟨L, hL, h1, -⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (a⁻¹ * s)
    rw [Measure.map_apply (hm a) hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (h1.measure_lt_top (μ := μ))
    intro z hz
    rw [hL]
    exact (mul_mem_cball_iff a s _).mp (hs hz)⟩
  have hnc : ∀ a, IsFiniteMeasureOnCompacts (n a) := fun a => by
    haveI := hmc a
    exact IsFiniteMeasureOnCompacts.smul_nnreal (m a) _
  have hn0 : ∀ a, n a {0} = 0 := fun a => by
    have : (fun z : E => (a : F) * Algebra.norm F z) ⁻¹' {0} = {0} := by
      ext z; simp [Algebra.norm_eq_zero_iff]
    simp only [n, m, Measure.smul_apply]
    rw [Measure.map_apply (hm a) (measurableSet_singleton 0), this, hμ0, smul_zero]
  have hn1 : ∀ (a : Fˣ) (b : Fˣ), b ∈ (Units.map (Algebra.norm F : E →* F)).range → n (b * a) = n a := by
    rintro a _ ⟨w, rfl⟩
    have h1 := GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul F E c δ hE μ w
    have h2 : m (Units.map (Algebra.norm F : E →* F) w * a) =
        (μ.map fun x => (w : E) * x).map fun z : E => (a : F) * Algebra.norm F z := by
      rw [Measure.map_map (hm a) (measurable_const_mul _)]
      simp only [m]
      congr 1
      funext z
      simp [map_mul, mul_comm, mul_left_comm, mul_assoc]
    simp only [n]
    rw [h2, h1, Measure.map_smul _ (hm a).aemeasurable, smul_smul, map_mul, mul_right_comm,
      mul_inv_cancel₀ (distribHaarChar_pos).ne', one_mul]
  have hn2 : ∀ a u : Fˣ, (n a).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n (u * a) := by
    intro a u
    simp only [n, m]
    rw [Measure.map_smul _ (measurable_const_mul _).aemeasurable,
      Measure.map_map (measurable_const_mul _) (hm a), smul_smul, map_mul,
      inv_mul_cancel_left₀ (distribHaarChar_pos).ne']
    congr 2
    funext z
    simp [mul_assoc]
  have hhom : ∀ u : Fˣ, (n 1 + n t).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • (n 1 + n t) := by
    intro u
    rw [Measure.map_add _ _ (measurable_const_mul _), hn2, hn2, ← smul_add]
    congr 1
    by_cases hu : u ∈ (Units.map (Algebra.norm F : E →* F)).range
    · rw [hn1 _ _ hu, hn1 _ _ hu]
    · have h1 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE u t hu ht
      have h2 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE t t ht ht
      have h3 := hn1 1 _ h1
      have h4 := hn1 t _ (mul_mem h1 (inv_mem h2))
      rw [mul_one] at h3
      have h5 : u * t * (t * t)⁻¹ * t = u * 1 := by group
      rw [h5] at h4
      rw [h3, h4, add_comm]
  haveI := hnc 1
  haveI := hnc t
  haveI : IsFiniteMeasureOnCompacts (n 1 + n t) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  obtain ⟨r, hr⟩ := GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField F lam (n 1 + n t) (by rw [Measure.add_apply, hn0, hn0, add_zero]) hhom
  refine ⟨s₀, fun s hs => ?_⟩
  have hB := GlobalTheory.SplitWeil.isCompact_cball s
  have hint : ∀ a : Fˣ, ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n a) = (nabs F a : ℂ) *
      ∫ z in {z : E | (a : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((a : F) * Algebra.norm F z) ∂μ := by
    intro a
    simp only [n, m]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      setIntegral_map hB.measurableSet hψ.aestronglyMeasurable (hm a).aemeasurable]
    rfl
  have h1 : ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n 1 + n t) = 0 := by
    rw [hr, Measure.restrict_smul, integral_smul_nnreal_measure, hs₀ s hs, smul_zero]
  rw [Measure.restrict_add, integral_add_measure (hψ.continuousOn.integrableOn_compact hB)
    (hψ.continuousOn.integrableOn_compact hB), hint, hint] at h1
  simpa [GlobalTheory.SplitWeil.nabs_one] using h1

end GlobalTheory.KSp.Cancel
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

noncomputable section
namespace GlobalTheory.IntShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow' (u : kˣ) (m : ℕ) : nabs k (u ^ m) = nabs k u ^ m := by
  simp [nabs, map_pow]

theorem exists_unit_nabs_lt_one : ∃ u : kˣ, nabs k u < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  refine ⟨Units.mk0 _ h0, ?_⟩
  rw [nabs_uniformiser hϖ rfl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)

theorem cball_one : cball (1 : kˣ) = (𝒪[k] : Set k) := by
  ext y; simp [cball, Valuation.mem_integer_iff]

theorem nabs_le_of_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∈ cball u) :
    nabs k (Units.mk0 y hy) ≤ nabs k u := by
  rw [nabs_le_iff]; exact h

theorem nabs_ge_of_not_mem_cball {u : kˣ} {y : k} (hy : y ≠ 0) (h : y ∉ cball u) :
    nabs k u ≤ nabs k (Units.mk0 y hy) := by
  rw [nabs_le_iff]; exact (not_le.mp h).le

theorem exists_shell {u : kˣ} (hu : nabs k u < 1) {y : k} (hy : y ≠ 0) (hO : y ∈ 𝒪[k]) :
    ∃ m : ℕ, y ∈ cball (u ^ m) ∧ y ∉ cball (u ^ (m + 1)) := by
  have hP : ∃ n : ℕ, y ∉ cball (u ^ n) := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (nabs_pos k (Units.mk0 y hy)) hu
    refine ⟨n, fun h => ?_⟩
    have := nabs_le_of_mem_cball hy h
    rw [nabs_pow'] at this
    linarith
  have h0 : Nat.find hP ≠ 0 := by
    intro h
    have := Nat.find_spec hP
    rw [h, pow_zero, cball_one] at this
    exact this hO
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  refine ⟨m, ?_, ?_⟩
  · have := Nat.find_min hP (show m < Nat.find hP by omega)
    simpa using this
  · have := Nat.find_spec hP
    rwa [hm] at this

section Meas
variable [MeasurableSpace k] [BorelSpace k]

theorem measure_zero_singleton (μ : Measure k) [μ.IsAddHaarMeasure] : μ {0} = 0 := by
  obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
  have hle : ∀ m : ℕ, μ {0} ≤ ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k) := by
    intro m
    have h1 : ({0} : Set k) ⊆ cball (u ^ m) := by
      intro y hy; rw [Set.mem_singleton_iff.mp hy]; simp [cball]
    refine (measure_mono h1).trans (le_of_eq ?_)
    rw [measure_cball, map_pow]
    congr 1
    simp [nabs, ENNReal.ofReal_coe_nnreal]
  have ht : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (nabs k u) ^ m * μ (𝒪[k] : Set k)) Filter.atTop
      (nhds (0 * μ (𝒪[k] : Set k))) :=
    ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by rw [ENNReal.ofReal_lt_one]; exact hu)) (Or.inr (isCompact_int k).measure_lt_top.ne)
  rw [zero_mul] at ht
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

end Meas

section Main
variable [MeasurableSpace k] [BorelSpace k]

theorem lintegral_int_nabs_rpow_lt_top (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ) (hs : -1 < s) :
    ∫⁻ x, (𝒪[k] : Set k).indicator
      (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ < ⊤ := by
  have hO : μ (𝒪[k] : Set k) < ⊤ := (isCompact_int k).measure_lt_top
  rcases le_or_gt 0 s with hs0 | hs0
  · calc _ ≤ ∫⁻ x, (𝒪[k] : Set k).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
            refine ENNReal.rpow_le_one ?_ hs0
            rw [ENNReal.ofReal_le_one]
            split_ifs with h
            · exact zero_le_one
            · exact Model.nabs_le_one _ hx
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      _ = μ (𝒪[k] : Set k) := by rw [lintegral_indicator_const (isOpen_int k).measurableSet, one_mul]
      _ < ⊤ := hO
  ·
    obtain ⟨u, hu⟩ := exists_unit_nabs_lt_one (k := k)
    set R := ENNReal.ofReal (nabs k u) with hRdef
    have hR0 : R ≠ 0 := by rw [hRdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact nabs_pos k u
    have hRt : R ≠ ⊤ := ENNReal.ofReal_ne_top
    have hR1 : R ^ s * R < 1 := by
      have e : R ^ s * R = R ^ (s + 1) := by rw [ENNReal.rpow_add _ _ hR0 hRt, ENNReal.rpow_one]
      rw [e]
      exact ENNReal.rpow_lt_one (by rw [hRdef, ENNReal.ofReal_lt_one]; exact hu) (by linarith)
    have hRs : R ^ s < ⊤ := by
      rw [lt_top_iff_ne_top, ne_eq, ENNReal.rpow_eq_top_iff]
      rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hR0 h
      · exact hRt h
    have hanti : ∀ a b : ℝ≥0∞, a ≤ b → b ^ s ≤ a ^ s := by
      intro a b h
      have hb : b ^ s = (b ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      have ha : a ^ s = (a ^ (-s))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
      rw [ha, hb]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow h (show (0:ℝ) ≤ -s by linarith))
    have hae : ∀ᵐ y ∂μ, y ∉ ({0} : Set k) := measure_eq_zero_iff_ae_notMem.mp (measure_zero_singleton μ)
    calc _ ≤ ∫⁻ y, ∑' m : ℕ, (cball (u ^ m)).indicator
            (fun _ => ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s) y ∂μ := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          have hy0 : y ≠ 0 := hy
          by_cases hx : y ∈ (𝒪[k] : Set k)
          · rw [Set.indicator_of_mem hx, dite_eq_right hy0]
            obtain ⟨m, hm1, hm2⟩ := exists_shell hu hy0 hx
            refine le_trans ?_ (ENNReal.le_tsum m)
            rw [Set.indicator_of_mem hm1]
            refine hanti _ _ (ENNReal.ofReal_le_ofReal ?_)
            have := nabs_ge_of_not_mem_cball hy0 hm2
            rwa [nabs_pow'] at this
          · rw [Set.indicator_of_notMem hx]; exact bot_le
      _ = ∑' m : ℕ, ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s * μ (cball (u ^ m)) := by
          rw [lintegral_tsum fun m => (measurable_const.indicator (isOpen_cball _).measurableSet).aemeasurable]
          congr 1; funext m
          rw [lintegral_indicator_const (isOpen_cball _).measurableSet]
      _ = ∑' m : ℕ, R ^ s * μ (𝒪[k] : Set k) * (R ^ s * R) ^ m := by
          congr 1; funext m
          have hc : ((distribHaarChar k (u ^ m) : NNReal) : ℝ≥0∞) = R ^ m := by
            rw [map_pow, ENNReal.coe_pow, hRdef]
            congr 1
            simp [nabs, ENNReal.ofReal_coe_nnreal]
          have h2 : ENNReal.ofReal (nabs k u ^ (m + 1)) ^ s = (R ^ s) ^ m * R ^ s := by
            rw [ENNReal.ofReal_pow (nabs_pos k u).le, ← hRdef, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
              mul_comm (((m + 1 : ℕ)) : ℝ) s, ENNReal.rpow_mul, ENNReal.rpow_natCast, pow_succ]
          rw [h2, measure_cball, hc, mul_pow]
          ring
      _ = R ^ s * μ (𝒪[k] : Set k) * (1 - R ^ s * R)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hRs hO) ?_
          rw [ENNReal.inv_lt_top]
          exact tsub_pos_of_lt hR1

end Main

end GlobalTheory.IntShell
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_eval_regular_at_fieldPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z),
      ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k,
        (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧
        ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u →
          ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  intro F _ Y Z _ k _ w
  set z := w (IsLocalRing.closedPoint k) with hz
  let ι := algebraMap (Z.presheaf.stalk z) Z.functionField
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  let e : Z.presheaf.stalk z ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), fun u => by
      obtain ⟨a, ha⟩ := u.2
      exact ⟨a, Subtype.ext ha⟩⟩
  let s : Z.presheaf.stalk z →+* k := (Scheme.stalkClosedPointTo (R := .of k) w).hom
  haveI : IsLocalHom s := Scheme.isLocalHom_stalkClosedPointTo' w
  have he : ∀ a, e.symm ⟨ι a, ⟨a, rfl⟩⟩ = a := fun a => e.symm_apply_eq.2 rfl
  refine ⟨s.comp e.symm.toRingHom, ?_, ?_⟩
  · rintro ⟨_, a, rfl⟩
    change s (e.symm ⟨ι a, ⟨a, rfl⟩⟩) ≠ 0 ↔ _
    rw [he]
    constructor
    · intro h0
      exact ⟨a, isUnit_of_map_unit s a (isUnit_iff_ne_zero.2 h0), rfl⟩
    · rintro ⟨b, hb, hba⟩
      rw [← hι hba]
      exact (hb.map s).ne_zero
  · intro q _ u ⟨a, ha⟩
    subst ha
    have hm := functionFieldMap_algebraMap q z a
    refine ⟨⟨_, hm.symm⟩, ?_⟩
    have h1 : (⟨functionFieldMap q (algebraMap _ Y.X.functionField a), ⟨_, hm.symm⟩⟩ : ι.range) =
        ⟨ι ((q.stalkMap z).hom a), ⟨_, rfl⟩⟩ := Subtype.ext hm
    change s (e.symm _) = _
    rw [h1, he]
    have hw : w ≫ q = spMap (s.comp (q.stalkMap z).hom) ≫ Y.X.fromSpecStalk (q z) := by
      conv_lhs => rw [← spMap_stalkClosedPointTo w]
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
      congr 1
      rw [spMap, spMap, ← Spec.map_comp]
      rfl
    have hv := val_ratOf (Y := Y) (s.comp (q.stalkMap z).hom) a
    exact hv.symm.trans (congrArg (fun p => (ratOf Y).val p (algebraMap _ Y.X.functionField a)) hw.symm)

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem val_spMap_pt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (σ : Ω →+* K) (x : Ω) : M.val (spMap σ ≫ M.pt) x = σ x := by
  have hx : x ∈ M.O (genericPoint M.Z) := by rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have := M.val_spMap_comp σ M.pt (M.pt_specializes _ _) ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val, RatModel.val_pt] at this
  exact this

theorem flag_conv : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hR B hB A hA K _ ψ₁ ψ₂ U hpt hBe
  have hom : (ratOf Y).pt ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hR.hom
  have key : ∀ σ : Y.Fn →+* K, spMap σ ≫ (ratOf Y).pt ≫ f = spMap (σ.comp φ.toRingHom) ≫ (ratOf X).pt := by
    intro σ
    rw [hom]
    show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map (CommRingCat.ofHom (σ.comp φ.toRingHom)) ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).symm
  have h1 : ∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u) := by
    intro u
    have e1 := val_spMap_pt (ratOf X) (ψ₁.comp φ.toRingHom) u
    have e2 := val_spMap_pt (ratOf X) (ψ₂.comp φ.toRingHom) u
    rw [← key, hpt, key] at e1
    exact e1.symm.trans e2
  refine ⟨h1, ?_⟩
  obtain ⟨A', hA', hP⟩ := hBe
  have hgen : (spMap ψ₂ ≫ (ratOf Y).pt) (IsLocalRing.closedPoint K) = genericPoint Y.X :=
    (ratOf Y).pt_apply _
  rw [hgen] at hA'
  have hval : (ratOf Y).val (spMap ψ₂ ≫ (ratOf Y).pt) = ψ₂ := funext (val_spMap_pt (ratOf Y) ψ₂)
  rw [hval] at hP
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hBd : ∀ τ, (B τ).det ≠ 0 := Fr.det_ne hB
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  set C : Mat m Y.Fn := A.map φ with hC
  have hCd : ∀ τ, (C τ).det ≠ 0 := fun τ => by
    rw [hC]; exact fun h0 => (map_ne_zero φ.toRingHom).2 (hAd τ) ((Mat.det_map A φ.toRingHom τ).symm.trans h0)
  have hCψ : C.map ψ₁ = C.map ψ₂ := by
    funext τ; ext i j; exact h1 (A τ i j)
  have hC2d : ∀ τ, (C.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hCd τ)
  have hA'2d : ∀ τ, (A'.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA'd τ)
  have e : U * (B * C⁻¹).map ψ₁ * ((A' * C⁻¹).map ψ₂)⁻¹ = U * B.map ψ₁ * (A'.map ψ₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hCψ, Mat.mul_inv_rev, Mat.inv_inv hC2d]
    rw [mul_assoc U, mul_assoc (B.map ψ₁), ← mul_assoc (C.map ψ₂)⁻¹, Mat.inv_mul hC2d, one_mul, ← mul_assoc]
  rw [e] at hP
  have hQ : Par m (⊤ : Subring K) ((A' * B⁻¹).map ψ₂) := by
    have := (Fr.mem_iff hB).1 hA'
    exact this.map ψ₂ (fun _ _ => trivial)
  have := hP.mul hQ
  rw [Mat.map_mul, Mat.map_inv] at this
  have e2 : U * B.map ψ₁ * (A'.map ψ₂)⁻¹ * (A'.map ψ₂ * (B.map ψ₂)⁻¹) = U * (B.map ψ₁ * (B.map ψ₂)⁻¹) := by
    rw [mul_assoc (U * B.map ψ₁), ← mul_assoc (A'.map ψ₂)⁻¹, Mat.inv_mul hA'2d, one_mul, mul_assoc]
  rwa [e2] at this

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem lcAt_iff_of_isLogEqn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 → 0 < m → IsLogEqn p Γ η x m g → (LcAt p n Γ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g) := by
  intro X _ _ _ p n hp hn Γ η x m g hη hm h
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  exact ⟨fun ⟨_, _, _, h₁, h₂, h₃, h₄⟩ E hE => discrep_eq hn h₁ hη h₂ hm h₃ h hE ▸ h₄ E hE,
    fun h' => ⟨η, m, g, hη, hm, h, h'⟩⟩

end GlobalTheory.PairStep
end
