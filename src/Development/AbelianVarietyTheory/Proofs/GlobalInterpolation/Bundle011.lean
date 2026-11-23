module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInterpolationExteriorSmallCoeffs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle003
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.QuadFibre

theorem IsSqrtOn.div_mem_of_mem_smul {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {t₀ t y : K} (h0 : t₀ ≠ 0) (ht : t ∈ t₀ • U) (hy : y ∈ t₀ • U) :
    y ≠ 0 ∧ t / y ∈ U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht hy
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨b, hb, rfl⟩ := hy
  have hb0 : b ≠ 0 := by
    intro hb0
    have := hnorm b hb
    rw [hb0, norm_zero] at this
    exact zero_ne_one this
  refine ⟨smul_ne_zero h0 hb0, ?_⟩
  simp only [smul_eq_mul]
  rw [mul_div_mul_left a b h0, div_eq_mul_inv]
  exact hmul a ha _ (hinv b hb)

theorem IsSqrtOn.smul_eq_of_mem_smul {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {t₀ t : K} (ht : t ∈ t₀ • U) : t • U = t₀ • U := by
  obtain ⟨-, -, -, hmul, hinv, hnorm, -, -⟩ := h
  rw [Set.mem_smul_set] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  have ha0 : a ≠ 0 := by
    intro ha0
    have := hnorm a ha
    rw [ha0, norm_zero] at this
    exact zero_ne_one this
  have haU : a • U = U := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hmul a ha b hb
    · intro hx
      refine ⟨a⁻¹ * x, hmul _ (hinv a ha) x hx, ?_⟩
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  rw [smul_eq_mul, mul_smul, haU]

theorem IsSqrtOn.norm_sqrt {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {a : K} (ha : a ∈ U) : ‖s a‖ = 1 := by
  obtain ⟨-, -, -, -, -, hnorm, -, hsq⟩ := h
  have h2 : ‖s a‖ ^ 2 = 1 := by rw [← norm_pow, hsq a ha, hnorm a ha]
  have h0 := norm_nonneg (s a)
  nlinarith [sq_nonneg (‖s a‖ - 1)]

theorem exists_integrable_bound_unit_smul {K V : Type} [NormedField K] [ProperSpace K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [ContinuousSMul K V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ g : V → ℝ, Integrable g μ ∧ ∀ (a : K) (x : V), ‖a‖ = 1 → ‖φ (a • x)‖ ≤ g x := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set T : Set V := Metric.sphere (0 : K) 1 • tsupport φ with hTdef
  have hT : IsCompact T := by
    have := ((isCompact_sphere (0 : K) 1).prod hc).image (f := fun p : K × V => p.1 • p.2) continuous_smul
    rwa [Set.image_smul_prod] at this
  refine ⟨T.indicator (fun _ => C), ?_, ?_⟩
  · exact (integrable_indicator_iff hT.isClosed.measurableSet).mpr
      (integrableOn_const hT.measure_lt_top.ne)
  · intro a x ha
    by_cases hx : φ (a • x) = 0
    · rw [hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hC0) x
    · have ha0 : a ≠ 0 := by
        rintro rfl
        rw [norm_zero] at ha
        exact zero_ne_one ha
      have hmem : x ∈ T := by
        refine Set.mem_smul.mpr ⟨a⁻¹, ?_, a • x, subset_tsupport _ (Function.mem_support.mpr hx),
          inv_smul_smul₀ ha0 x⟩
        rw [mem_sphere_zero_iff_norm, norm_inv, ha, inv_one]
      rw [Set.indicator_of_mem hmem]
      exact hC _

theorem integrable_and_continuousOn_fibOf (K V : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V]
    [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure]
    (q : V → K) (hq : Continuous q) (_hh : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (h : IsSqrtOn U s) (φ : V → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    (∀ t : K, t ≠ 0 → Integrable φ (fibOf μ ν q U s t)) ∧
      ContinuousOn (fun t => ∫ x, φ x ∂(fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  have h' := h
  obtain ⟨hUo, -, h1, -, -, -, hs, -⟩ := h'
  have hmf : ∀ t' : K, Measurable (fun x : V => s (t' / q x) • x) := by
    intro t'
    have hd : Measurable (fun x : V => t' / q x) := by
      simp_rw [div_eq_mul_inv]
      exact (hq.measurable.inv).const_mul t'
    exact (hs.measurable.comp hd).smul measurable_id
  obtain ⟨g, hg, hgb⟩ := exists_integrable_bound_unit_smul (K := K) μ hφ hc
  have hset : ∀ t : K, t ≠ 0 → MeasurableSet (q ⁻¹' (t • U)) := fun t ht =>
    (hUo.smul₀ ht).measurableSet.preimage hq.measurable
  have hself : ∀ t : K, t ∈ t • U := fun t => by
    simpa using Set.smul_mem_smul_set (a := t) h1
  have hν : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0 := fun t ht =>
    ((hUo.smul₀ ht).measure_pos ν ⟨t, hself t⟩).ne'
  have hbd : ∀ t t' : K, t ≠ 0 → t' ∈ t • U → ∀ x ∈ q ⁻¹' (t • U), ‖φ (s (t' / q x) • x)‖ ≤ g x :=
    fun t t' ht ht' x hx => hgb _ x (h.norm_sqrt (h.div_mem_of_mem_smul ht ht' hx).2)
  have hint : ∀ t : K, t ≠ 0 →
      Integrable (fun x => φ (s (t / q x) • x)) (μ.restrict (q ⁻¹' (t • U))) := by
    intro t ht
    refine Integrable.mono' hg.restrict (hφ.measurable.comp (hmf t)).aestronglyMeasurable ?_
    exact (ae_restrict_iff' (hset t ht)).mpr
      (Filter.Eventually.of_forall (fun x hx => hbd t t ht (hself t) x hx))
  have heq : ∀ t : K, t ≠ 0 → ∀ t' ∈ t • U, ∫ x, φ x ∂(fibOf μ ν q U s t') =
      (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ := by
    intro t ht t' ht'
    have ht'0 : t' ≠ 0 := (h.div_mem_of_mem_smul ht ht' ht').1
    rw [fibOf_ne μ ν q U s ht'0, h.smul_eq_of_mem_smul ht', integral_smul_measure,
      integral_map (hmf t').aemeasurable hφ.aestronglyMeasurable]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [fibOf_ne μ ν q U s ht]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (hν t ht))
    exact (integrable_map_measure hφ.aestronglyMeasurable (hmf t).aemeasurable).mpr (hint t ht)
  · have ht0 : t ≠ 0 := ht
    apply ContinuousAt.continuousWithinAt
    have hnhds : t • U ∈ 𝓝 t := (hUo.smul₀ ht0).mem_nhds (hself t)
    have hev : (fun t' => (ν (t • U))⁻¹.toReal • ∫ x in q ⁻¹' (t • U), φ (s (t' / q x) • x) ∂μ)
        =ᶠ[𝓝 t] (fun t' => ∫ x, φ x ∂(fibOf μ ν q U s t')) :=
      Filter.eventually_of_mem hnhds (fun t' ht' => (heq t ht0 t' ht').symm)
    refine ContinuousAt.congr (ContinuousAt.const_smul (continuousAt_of_dominated
      (F := fun t' x => φ (s (t' / q x) • x)) (bound := g) ?_ ?_ hg.restrict ?_)
      ((ν (t • U))⁻¹.toReal)) hev
    · exact Filter.Eventually.of_forall
        (fun t' => (hφ.measurable.comp (hmf t')).aestronglyMeasurable)
    · exact Filter.eventually_of_mem hnhds (fun t' ht' => (ae_restrict_iff' (hset t ht0)).mpr
        (Filter.Eventually.of_forall (fun x hx => hbd t t' ht0 ht' x hx)))
    · exact Filter.Eventually.of_forall (fun x =>
        (hφ.comp ((hs.comp (continuous_id.div_const _)).smul continuous_const)).continuousAt)

end GlobalTheory.QuadFibre
end

section

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

def qPoch (t : ℂ) (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1 - t ^ (i + 1))

def qPochInf (t : ℂ) : ℂ := ∏' i : ℕ, (1 - t ^ (i + 1))

def qBinom (t : ℂ) (m k : ℕ) : ℂ := qPoch t m / (qPoch t k * qPoch t (m - k))

def finCoeff (t : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  if j.natAbs ≤ n then qBinom t (2 * n) ((n : ℤ) + j).toNat else 0

theorem qPoch_tendsto (t : ℂ) (ht : ‖t‖ < 1) :
    Filter.Tendsto (qPoch t) Filter.atTop (nhds (qPochInf t)) ∧ qPochInf t ≠ 0 ∧
      ∀ m, qPoch t m ≠ 0 := by
  have hg : Summable (fun i : ℕ => ‖t‖ * ‖t‖ ^ i) :=
    (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left ‖t‖
  have hsum : Summable (fun i : ℕ => ‖-(t ^ (i + 1))‖) :=
    hg.congr (fun i => by rw [norm_neg, norm_pow, pow_succ, mul_comm])
  have hne : ∀ i : ℕ, 1 + -(t ^ (i + 1)) ≠ 0 := by
    intro i h
    have h1 : t ^ (i + 1) = 1 := by linear_combination -h
    have h2 : ‖t‖ ^ (i + 1) < 1 := pow_lt_one₀ (norm_nonneg t) ht (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hm := multipliable_one_add_of_summable hsum
  have h0 := tprod_one_add_ne_zero_of_summable hne hsum
  simp only [← sub_eq_add_neg] at hm h0 hne
  refine ⟨hm.hasProd.tendsto_prod_nat, h0, fun m => Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)⟩

theorem tpFactor_eq (τ : ℍ) (z : ℂ) (k : ℕ) :
    GlobalTheory.ThetaWeberRoad.tpFactor τ z k = (1 - (cexp (π * I * (τ : ℂ)) ^ 2) ^ (k + 1)) *
      ((1 + cexp (2 * π * I * z) * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1)) *
        (1 + (cexp (2 * π * I * z))⁻¹ * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1))) := by
  unfold GlobalTheory.ThetaWeberRoad.tpFactor
  rw [← pow_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_neg, ← exp_add, ← exp_add]
  rw [mul_assoc]
  congr 3 <;> push_cast <;> ring_nf

theorem jacobiTheta₂_term_eq_zpow (τ z : ℂ) (j : ℤ) :
    jacobiTheta₂_term j z τ = cexp (2 * π * I * z) ^ j * cexp (π * I * τ) ^ (j ^ 2) := by
  unfold jacobiTheta₂_term
  rw [← exp_int_mul, ← exp_int_mul, ← exp_add]
  congr 1
  push_cast
  ring

theorem norm_exp_pi_I_lt_one (τ : ℂ) (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  have : (π * I * τ).re = -(π * τ.im) := by simp
  rw [this]
  have := Real.pi_pos
  nlinarith

theorem multipliable_tpFactor (τ : ℍ) (z : ℂ) :
    Multipliable (GlobalTheory.ThetaWeberRoad.tpFactor τ z) := by
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) τ.2
  have g : Summable (fun k : ℕ => (‖s‖ ^ 2) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg s])
  have h1 : Multipliable (fun k : ℕ => 1 + -((s ^ 2) ^ (k + 1))) :=
    multipliable_one_add_of_summable ((g.mul_left (‖s‖ ^ 2)).congr (fun k => by
      rw [norm_neg, norm_pow, norm_pow, pow_succ]; ring))
  have h2 : Multipliable (fun k : ℕ => 1 + x * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  have h3 : Multipliable (fun k : ℕ => 1 + x⁻¹ * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x⁻¹‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  convert h1.mul (h2.mul h3) using 1
  funext k
  rw [tpFactor_eq]
  ring

end GlobalTheory.JacobiTriple
end
end

section

open Complex

open UpperHalfPlane hiding I
open scoped Real
open Filter Topology

noncomputable section

namespace GlobalTheory.ThetaWeberRoad.OddDeriv

def tailProd (τ : ℍ) (v : ℂ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ) * v)

lemma hasProd_tailProd (τ : ℍ) (v : ℂ) :
    HasProd (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ) * v) (tailProd τ v) := by
  have hs : Summable fun n : ℕ => ‖-(ModularForm.eta_q n (τ : ℂ) * v)‖ := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg, norm_mul] at h ⊢
    exact h.mul_right _
  have hm : Multipliable fun n : ℕ => 1 + -(ModularForm.eta_q n (τ : ℂ) * v) :=
    multipliable_one_add_of_summable hs
  simp only [← sub_eq_add_neg] at hm
  exact hm.hasProd

lemma continuousAt_tailProd (τ : ℍ) (v₀ : ℂ) : ContinuousAt (tailProd τ) v₀ := by
  have hK : IsCompact (Metric.closedBall v₀ 1) := isCompact_closedBall v₀ 1
  have hu : Summable fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖ * (‖v₀‖ + 1) := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg] at h
    exact h.mul_right _
  have H := Summable.hasProdUniformlyOn_nat_one_add
    (f := fun n v => -(ModularForm.eta_q n (τ : ℂ) * v)) hK hu
    (Filter.Eventually.of_forall fun n v hv => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_of_mem_closedBall hv) (norm_nonneg _))
    (fun n => by fun_prop)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at H
  have hc := H.continuousOn (Frequently.of_forall fun s =>
    (continuous_finsetProd s fun i _ => by fun_prop).continuousOn)
  have : ContinuousOn (tailProd τ) (Metric.closedBall v₀ 1) := by
    refine hc.congr fun v _ => ?_
    simp [tailProd, sub_eq_add_neg]
  exact this.continuousAt (Metric.closedBall_mem_nhds v₀ one_pos)

lemma tpFactor_shift (τ : ℍ) (z : ℂ) (n : ℕ) :
    tpFactor τ (z + ((τ : ℂ) + 1) / 2) n =
      (1 - ModularForm.eta_q n (τ : ℂ) * 1) *
        (1 - ModularForm.eta_q n (τ : ℂ) * cexp (2 * π * I * z)) *
        (1 - cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
  have hm : cexp (-(π * I)) = -1 := by rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hp : cexp (π * I) = -1 := Complex.exp_pi_mul_I
  have h1 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) := by
    rw [show -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) =
      cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z) * cexp (π * I) by
        rw [hp]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  have h2 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
    rw [show -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z)) * cexp (-(π * I)) by
        rw [hm]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  unfold tpFactor
  rw [ModularForm.eta_q_eq_cexp, h1, h2]
  ring

lemma jacobiTheta₂_shift (hT : TripleProduct) (τ : ℍ) (z : ℂ) :
    jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ =
      tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
        ((1 - cexp (-(2 * π * I * z))) * tailProd τ (cexp (-(2 * π * I * z)))) := by
  have hA := hasProd_tailProd τ 1
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have h0 := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have h1 : HasProd (fun n : ℕ => 1 - cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (τ : ℂ)) *
      cexp (-(2 * π * I * z))) (tailProd τ (cexp (-(2 * π * I * z)))) := by
    convert h0 using 2 with n
    rw [ModularForm.eta_q_eq_cexp]; push_cast; ring_nf
  have hC := HasProd.zero_mul
    (f := fun n : ℕ => 1 - cexp (2 * π * I * (n : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) h1
  have e0 : (1 - cexp (2 * π * I * ((0 : ℕ) : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      1 - cexp (-(2 * π * I * z)) := by simp
  rw [e0] at hC
  have hAll := (hA.mul hB).mul hC
  refine (hT τ (z + ((τ : ℂ) + 1) / 2)).unique ?_
  convert hAll using 1
  funext n
  rw [tpFactor_shift]

end GlobalTheory.ThetaWeberRoad.OddDeriv

namespace GlobalTheory.ThetaWeberRoad.OddDeriv

theorem hasDerivAt_mul_of_eq_zero {F R : ℂ → ℂ} {F' : ℂ} (hF : HasDerivAt F F' 0) (hF0 : F 0 = 0)
    (hR : ContinuousAt R 0) : HasDerivAt (fun z => F z * R z) (F' * R 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hF ⊢
  have hR' : Tendsto R (𝓝[≠] (0 : ℂ)) (𝓝 (R 0)) := hR.tendsto.mono_left nhdsWithin_le_nhds
  refine (hF.mul hR').congr' ?_
  filter_upwards with z
  simp only [slope_def_field, hF0, sub_zero, zero_mul]
  ring

theorem hasDerivAt_oddTheta_zero :
    TripleProduct → ∀ τ : UpperHalfPlane,
      HasDerivAt (oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  intro hT τ
  set F : ℂ → ℂ := fun z => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) *
    (1 - cexp (-(2 * π * I * z))) with hFdef
  set R : ℂ → ℂ := fun z => tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
    tailProd τ (cexp (-(2 * π * I * z))) with hRdef
  have hfun : oddTheta τ = fun z => F z * R z := by
    funext z
    simp only [oddTheta, F, R]
    rw [jacobiTheta₂_shift hT]
    ring
  have hF0 : F 0 = 0 := by simp [F]
  have h1 : HasDerivAt (fun z : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)))
      (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1)) 0 :=
    ((((hasDerivAt_id (0 : ℂ)).add_const (1 / 2)).const_mul (π * I)).const_add _).cexp
  have h2 : HasDerivAt (fun z : ℂ => 1 - cexp (-(2 * π * I * z)))
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).neg.cexp).const_sub 1
  have hF : HasDerivAt F (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1) *
      (1 - cexp (-(2 * π * I * 0))) + cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) *
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1)))) 0 := h1.mul h2
  have hR : ContinuousAt R 0 := by
    have hu : Continuous fun z : ℂ => cexp (2 * π * I * z) := by fun_prop
    have hv : Continuous fun z : ℂ => cexp (-(2 * π * I * z)) := by fun_prop
    exact (continuousAt_const.mul ((continuousAt_tailProd τ _).comp hu.continuousAt)).mul
      ((continuousAt_tailProd τ _).comp hv.continuousAt)
  rw [hfun]
  have key := hasDerivAt_mul_of_eq_zero hF hF0 hR
  convert key using 1
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have hq : (Function.Periodic.qParam 24 (τ : ℂ)) ^ 3 = cexp (π * I * (τ : ℂ) / 4) := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hI : cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) = cexp (π * I * (τ : ℂ) / 4) * I := by
    rw [Complex.exp_add]
    congr 1
    rw [show π * I * (0 + 1 / 2) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  simp only [R, mul_zero, neg_zero, Complex.exp_zero, hT1, hI]
  unfold ModularForm.eta
  rw [mul_pow, hq]
  ring_nf
  rw [Complex.I_sq]
  ring

end GlobalTheory.ThetaWeberRoad.OddDeriv
end
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_interpolation_exterior_small_coeffs : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by
  first | exact @GlobalTheory.ExteriorInterpolation.interpolation | exact GlobalTheory.ExteriorInterpolation.interpolation | (intros; apply GlobalTheory.ExteriorInterpolation.interpolation <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.fourier_inversion_haar_symm_form_alt : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ x y, B x y = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∃ c : ℝ, 0 < c ∧ ∀ Φ : V → ℂ, Continuous Φ → Integrable Φ μ → Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ → ∀ z, ∫ y, (∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) * Complex.exp (2 * Real.pi * Complex.I * ((B y z : ℝ) : ℂ)) ∂μ = (c : ℂ) * Φ (-z)) ∧ ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ := by
  first | exact @GlobalTheory.fourier_inversion_haar_symm_form | exact GlobalTheory.fourier_inversion_haar_symm_form | (intros; apply GlobalTheory.fourier_inversion_haar_symm_form <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CharConductor

theorem eq_one_of_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterationConvergence.main
  | exact _root_.GlobalTheory.IterationConvergence.main
  | (apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)

theorem exists_exponent_of_valued {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | (apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)

theorem exists_conductor_exponent : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion

end GlobalTheory.CharConductor
end
