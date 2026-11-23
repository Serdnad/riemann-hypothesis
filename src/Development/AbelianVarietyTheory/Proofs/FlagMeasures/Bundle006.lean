module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_isometricRep_inv {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (g : G) (u v : H) : ⟪u, σ g⁻¹ v⟫_ℂ = ⟪σ g u, v⟫_ℂ := by
  have hv : σ g (σ g⁻¹ v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  have hf : ∀ x, f x = σ g x := fun _ => rfl
  calc ⟪u, σ g⁻¹ v⟫_ℂ = ⟪f u, f (σ g⁻¹ v)⟫_ℂ := (f.inner_map_map _ _).symm
    _ = ⟪σ g u, v⟫_ℂ := by rw [hf, hf, hv]

theorem matrixCoeff_idempotent_of_orthogonality : ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), 0 < d → (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ v w v' w' : H, ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) → ∀ w : H, ‖w‖ = 1 → (∀ g : G, star ((d : ℂ) * star ⟪w, σ g⁻¹ w⟫_ℂ) = (d : ℂ) * star ⟪w, σ g w⟫_ℂ) ∧ (∀ x y : G, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ)) ∧ (∀ u u' : H, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) ∧ ∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0 := by
  intro G _ _ μ H _ _ _ σ d hd hσ hS w hw
  have adj : ∀ (g : G) (a b : H), ⟪a, σ g⁻¹ b⟫_ℂ = ⟪σ g a, b⟫_ℂ :=
    fun g a b => inner_isometricRep_inv σ hσ g a b
  have hc : ∀ a b : H, star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := fun a b => by
    rw [← starRingEnd_apply, inner_conj_symm]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdc : star (d : ℂ) = d := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    rw [star_mul', star_star, hdc, adj, hc]
  · intro x y
    have key : ∀ g : G, star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ y w, σ g (σ x w)⟫_ℂ := by
      intro g
      rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
        adj, adj, hc]
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ
        = ∫ g, ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; rw [key]; ring
      _ = ((d : ℂ) * d) * (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ / d) := by
          rw [integral_const_mul, hS]
      _ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ) := by
          rw [hc]; field_simp
  · intro u u'
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ
        = ∫ g, (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; ring
      _ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ := by
          rw [integral_const_mul, hS]; field_simp
  · intro y hy
    have h0 := hS w y w y
    simp only [hy, zero_mul, integral_zero] at h0
    have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    rw [hww, one_mul] at h0
    have hyy : ⟪y, y⟫_ℂ = 0 := (div_eq_zero_iff.mp h0.symm).resolve_right hd0
    exact inner_self_eq_zero.mp hyy

end GlobalTheory
end

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem absOpInt_integrable {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => π g x) (φ : G → ℂ) (hφ : Integrable φ μ) (y : Hp) :
    Integrable (fun g => φ g • π g y) μ := by
  refine Integrable.mono' (hφ.norm.mul_const ‖y‖) ?_ (ae_of_all _ fun g => ?_)
  · exact hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable
  · rw [norm_smul, hn]

theorem absOpInt : ∀ (G : Type) [Group G] [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ φ : G → ℂ, Integrable φ μ → ∃ P : Hp →L[ℂ] Hp, (∀ y, P y = ∫ g, φ g • π g y ∂μ) ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ := by
  intro G _ _ _ _ _ μ Hp _ _ _ π hn hc φ hφ
  let L : Hp →ₗ[ℂ] Hp :=
    { toFun := fun y => ∫ g, φ g • π g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (absOpInt_integrable μ π hn hc φ hφ y)
          (absOpInt_integrable μ π hn hc φ hφ z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (φ _) c]
        exact integral_smul c _ }
  refine ⟨L.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun y => rfl, fun x y => ?_⟩
  · calc ‖L y‖ = ‖∫ g, φ g • π g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • π g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by simp_rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · change ⟪x, ∫ g, φ g • π g y ∂μ⟫_ℂ = _
    rw [← integral_inner (absOpInt_integrable μ π hn hc φ hφ y)]
    simp_rw [inner_smul_right]

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq {N : ℕ} (m₁ m₂ : Measure (Fin N → ℝ))
    (h : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U) (hb : Bornology.IsBounded U) : m₁ U = m₂ U := by

  obtain ⟨f, hfs, hfd, hfr⟩ := hU.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfr ⟨x, rfl⟩).1
  have hfU : ∀ x, x ∉ U → f x = 0 := fun x hx => by
    rw [← hfs] at hx; simpa using hx
  have hfpos : ∀ x, x ∈ U → 0 < f x := fun x hx => by
    rw [← hfs] at hx; exact lt_of_le_of_ne (hf0 x) (Ne.symm hx)

  set φ : ℕ → (Fin N → ℝ) → ℝ := fun n x => Real.smoothTransition ((n : ℝ) * f x) with hφdef
  have hφd : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    Real.smoothTransition.contDiff.comp (contDiff_const.mul hfd)
  have hφU : ∀ n x, x ∉ U → φ n x = 0 := fun n x hx => by
    simp [hφdef, hfU x hx]
  have hK : IsCompact (closure U) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    HasCompactSupport.intro hK fun x hx => hφU n x fun hxU => hx (subset_closure hxU)
  have hφn : ∀ n x, 0 ≤ φ n x := fun n x => Real.smoothTransition.nonneg _
  have key : ∀ m : Measure (Fin N → ℝ),
      Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (φ n x) ∂m) Filter.atTop (nhds (m U)) := by
    intro m
    rw [← lintegral_indicator_one hU.measurableSet]
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hφd n).continuous.measurable.ennreal_ofReal.aemeasurable)
      (Filter.Eventually.of_forall fun x i j hij => ?_) (Filter.Eventually.of_forall fun x => ?_)
    · exact ENNReal.ofReal_le_ofReal (Real.smoothTransition.monotone
        (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) (hf0 x)))
    · by_cases hx : x ∈ U
      · have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) * f x) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop.atTop_mul_const (hfpos x hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [ht.eventually_ge_atTop 1] with n hn
        simp [hφdef, Real.smoothTransition.one_of_one_le hn, hx]
      · simp [hφU _ x hx, hx]
  exact tendsto_nhds_unique (key m₁)
    ((key m₂).congr fun n => (h (φ n) (hφd n) (hφc n) (hφn n)).symm)

theorem measure_eq_of_lintegral_smooth_eq :
    ∀ (N : ℕ) (m₁ m₂ : Measure (Fin N → ℝ)) [IsFiniteMeasureOnCompacts m₂],
      (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂) →
      m₁ = m₂ := by
  intro N m₁ m₂ _ h

  let C : Set (Set (Fin N → ℝ)) := {s | IsOpen s ∧ Bornology.IsBounded s}
  have hgen : (inferInstance : MeasurableSpace (Fin N → ℝ)) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := Fin N → ℝ)]
      refine MeasurableSpace.generateFrom_le fun s hs => ?_
      have hs' : s = ⋃ n : ℕ, s ∩ Metric.ball 0 ((n : ℝ) + 1) := by
        rw [← Set.inter_iUnion, Metric.iUnion_ball_nat_succ, Set.inter_univ]
      rw [hs']
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨by exact IsOpen.inter hs Metric.isOpen_ball, Metric.isBounded_ball.subset Set.inter_subset_right⟩
    · exact MeasurableSpace.generateFrom_le fun s hs => hs.1.measurableSet
  have hpi : IsPiSystem C := fun s hs t ht _ =>
    ⟨hs.1.inter ht.1, hs.2.subset Set.inter_subset_left⟩
  refine (Measure.ext_of_generateFrom_of_iUnion C (fun n : ℕ => Metric.ball (0 : Fin N → ℝ) ((n : ℝ) + 1))
    hgen hpi (Metric.iUnion_ball_nat_succ _) (fun n => ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩)
    (fun n => measure_ball_lt_top.ne) fun s hs => ?_).symm
  exact (measure_eq_of_isOpen_isBounded_of_lintegral_smooth_eq m₁ m₂ h s hs.1 hs.2).symm

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem sq_intervalIntegral_le_mul_intervalIntegral_sq (g : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hg : ContinuousOn g (Set.Icc 0 s)) :
    (∫ t in (0 : ℝ)..s, g t) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, g t ^ 2 := by
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hg1 : IntervalIntegrable g volume 0 s := (hg.mono hIcc.subset).intervalIntegrable
  have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 s :=
    ((hg.pow 2).mono hIcc.subset).intervalIntegrable
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t in (0 : ℝ)..s, g t) / s := ⟨_, rfl⟩
  have hcs : c * s = ∫ t in (0 : ℝ)..s, g t := by rw [hc]; exact div_mul_cancel₀ _ hs.ne'
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..s, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hs.le (fun t _ => sq_nonneg _)
  have hexp : (fun t => (g t - c) ^ 2) = fun t => (g t ^ 2 - (2 * c) * g t) + c ^ 2 := by
    funext t; ring
  rw [hexp, intervalIntegral.integral_add (hg2.sub (hg1.const_mul (2 * c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hg2 (hg1.const_mul (2 * c)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [sub_zero, smul_eq_mul] at h0
  have hsq : s * c ^ 2 = c * ∫ t in (0 : ℝ)..s, g t := by rw [← hcs]; ring
  have h1 : c * (∫ t in (0 : ℝ)..s, g t) ≤ ∫ t in (0 : ℝ)..s, g t ^ 2 := by linarith
  have h2 : (∫ t in (0 : ℝ)..s, g t) ^ 2 = s * (c * ∫ t in (0 : ℝ)..s, g t) := by
    rw [← hcs]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 hs.le

theorem sobolev_endpoint_one_variable : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ φ' : ℝ → H) (s : ℝ), 0 < s → (∀ t ∈ Set.Icc 0 s, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc 0 s) → ‖φ 0‖ ^ 2 ≤ 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
  intro H _ _ _ φ φ' s hs hd hc
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hφc : ContinuousOn φ (Set.Icc 0 s) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hn' : ContinuousOn (fun t => ‖φ' t‖) (Set.Icc 0 s) := hc.norm
  have hn'i : IntervalIntegrable (fun t => ‖φ' t‖) volume 0 s :=
    (hn'.mono hIcc.subset).intervalIntegrable
  have hA : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume 0 s :=
    ((hφc.norm.pow 2).mono hIcc.subset).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ‖φ 0‖ ^ 2 ≤ 2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 := by
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 s := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hint : IntervalIntegrable φ' volume 0 t := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..t, φ' y = φ t - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx)) hint
    have h1 : ‖φ 0‖ ≤ ‖φ t‖ + ‖∫ y in (0 : ℝ)..t, φ' y‖ := by
      rw [hftc]
      have := norm_sub_le (φ t) (φ t - φ 0)
      rwa [sub_sub_cancel] at this
    have h2 : ‖∫ y in (0 : ℝ)..t, φ' y‖ ≤ ∫ y in (0 : ℝ)..t, ‖φ' y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have h3 : ∫ y in (0 : ℝ)..t, ‖φ' y‖ ≤ ∫ y in (0 : ℝ)..s, ‖φ' y‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun y => norm_nonneg _) hn'i
    have h4 : ‖φ 0‖ ≤ ‖φ t‖ + ∫ y in (0 : ℝ)..s, ‖φ' y‖ := by linarith
    nlinarith [norm_nonneg (φ 0), mul_nonneg (norm_nonneg (φ 0)) (sub_nonneg.2 h4),
      sq_nonneg (‖φ t‖ - ∫ y in (0 : ℝ)..s, ‖φ' y‖),
      sq_nonneg (‖φ t‖ + (∫ y in (0 : ℝ)..s, ‖φ' y‖) - ‖φ 0‖)]
  have hmono : ∫ _ in (0 : ℝ)..s, ‖φ 0‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..s, (2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2) :=
    intervalIntegral.integral_mono_on hs.le intervalIntegrable_const
      ((hA.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hA.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  have hCS : (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 :=
    sq_intervalIntegral_le_mul_intervalIntegral_sq (fun t => ‖φ' t‖) s hs hn'
  have key : ‖φ 0‖ ^ 2 * s ≤
      2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hCS hs.le]
  calc ‖φ 0‖ ^ 2 = ‖φ 0‖ ^ 2 * s / s := by field_simp
    _ ≤ (2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2) / s := by
      gcongr
    _ = 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
      field_simp

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem ae_eq_of_dense_of_local_sq_bound : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  intro X _ μ K _hK hcov H _ _ E _ _ D hD P Q hP hQ hPb hQb hPQ u
  have key : ∀ n, ∀ᵐ x ∂μ.restrict (K n), P u x = Q u x := by
    intro n
    obtain ⟨CP, hCP⟩ := hPb n
    obtain ⟨CQ, hCQ⟩ := hQb n
    have hmeas : AEMeasurable (fun x => ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2) (μ.restrict (K n)) :=
      (((hCP u).1.sub (hCQ u).1).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2
    set M : ℝ := 2 * (|CP| + |CQ|) with hM
    have hbound : ∀ δ : ℝ, 0 < δ →
        ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) ≤ ENNReal.ofReal (M * δ ^ 2) := by
      intro δ hδ
      obtain ⟨u', hu'D, hdist⟩ := hD.exists_dist_lt u hδ
      have hwδ : ‖u - u'‖ ^ 2 ≤ δ ^ 2 := by
        have : ‖u - u'‖ < δ := by rw [← dist_eq_norm]; exact hdist
        exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
      have hae : ∀ᵐ x ∂(μ.restrict (K n)), ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ≤
          2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 := by
        have h1 := ae_restrict_of_ae (s := K n) (hP u u')
        have h2 := ae_restrict_of_ae (s := K n) (hQ u u')
        have h3 := ae_restrict_of_ae (s := K n) (hPQ u' hu'D)
        filter_upwards [h1, h2, h3] with x e1 e2 e3
        have e1' : P u x - P u' x = P (u - u') x := e1
        have e2' : Q u x - Q u' x = Q (u - u') x := e2
        have e3' : P u' x = Q u' x := e3
        have e : P u x - Q u x = P (u - u') x - Q (u - u') x := by
          have : P u x - Q u x = (P u x - P u' x) - (Q u x - Q u' x) + (P u' x - Q u' x) := by abel
          rw [this, e1', e2', e3', sub_self, add_zero]
        rw [e]
        have hn : ‖P (u - u') x - Q (u - u') x‖₊ ≤ ‖P (u - u') x‖₊ + ‖Q (u - u') x‖₊ := nnnorm_sub_le _ _
        have hsq : ‖P (u - u') x - Q (u - u') x‖₊ ^ 2 ≤
            2 * ‖P (u - u') x‖₊ ^ 2 + 2 * ‖Q (u - u') x‖₊ ^ 2 := by
          have hn' : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ≤
              ((‖P (u - u') x‖₊ : NNReal) : ℝ) + ((‖Q (u - u') x‖₊ : NNReal) : ℝ) := by exact_mod_cast hn
          have h0 : (0:ℝ) ≤ ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) := NNReal.coe_nonneg _
          have hreal : ((‖P (u - u') x - Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 ≤
              2 * ((‖P (u - u') x‖₊ : NNReal) : ℝ) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : NNReal) : ℝ) ^ 2 := by
            nlinarith [sq_nonneg (((‖P (u - u') x‖₊ : NNReal) : ℝ) - ((‖Q (u - u') x‖₊ : NNReal) : ℝ))]
          exact_mod_cast hreal
        have := ENNReal.coe_le_coe.mpr hsq
        push_cast at this
        exact this
      calc ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n))
          ≤ ∫⁻ x, (2 * ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 + 2 * ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2)
              ∂(μ.restrict (K n)) := lintegral_mono_ae hae
        _ = 2 * ∫⁻ x, ((‖P (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) +
              2 * ∫⁻ x, ((‖Q (u - u') x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) := by
            rw [lintegral_add_left'
              (((hCP (u - u')).1.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2).const_mul 2),
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * ENNReal.ofReal (CP * ‖u - u'‖ ^ 2) + 2 * ENNReal.ofReal (CQ * ‖u - u'‖ ^ 2) := by
            gcongr
            · exact (hCP (u - u')).2
            · exact (hCQ (u - u')).2
        _ ≤ 2 * ENNReal.ofReal (|CP| * δ ^ 2) + 2 * ENNReal.ofReal (|CQ| * δ ^ 2) := by
            gcongr <;> first | exact le_abs_self _ | exact hwδ
        _ = ENNReal.ofReal (M * δ ^ 2) := by
            have : M * δ ^ 2 = 2 * (|CP| * δ ^ 2) + 2 * (|CQ| * δ ^ 2) := by rw [hM]; ring
            rw [this, ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    have hzero : ∫⁻ x, ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 ∂(μ.restrict (K n)) = 0 := by
      have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (M * δ ^ 2)) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (ENNReal.ofReal (M * 0 ^ 2))) := by
        apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
        exact (ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 2))).tendsto 0
      have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun δ hδ => hbound δ hδ))
      simpa using this
    have hae0 := (lintegral_eq_zero_iff' hmeas).mp hzero
    filter_upwards [hae0] with x hx
    have hx' : ((‖P u x - Q u x‖₊ : ENNReal)) ^ 2 = 0 := hx
    simpa [sub_eq_zero] using hx'
  have hall : ∀ᵐ x ∂μ.restrict (⋃ n, K n), P u x = Q u x :=
    (ae_restrict_iUnion_iff K (fun x => P u x = Q u x)).mpr key
  rw [hcov, Measure.restrict_univ] at hall
  exact hall

end GlobalTheory
end

section

open Matrix Finset Real

namespace GlobalTheory

theorem exp_neg_mul_two_pow_le_geometric (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    Real.exp (-T * 2 ^ i) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
  have hb : (1 : ℝ) + i ≤ 2 ^ i := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) i
    norm_num at h
    linarith
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) two_pos]
    linarith
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hexp : -T * 2 ^ i ≤ -T + (i : ℝ) * (-1) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ T by linarith) (sub_nonneg.mpr hb),
      mul_nonneg (sub_nonneg.mpr hT) hi]
  calc Real.exp (-T * 2 ^ i) ≤ Real.exp (-T + (i : ℝ) * (-1)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-T) * Real.exp (-1) ^ i := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le he i) (Real.exp_pos _).le

theorem shell_sum_elementary_inequalities :
    (∀ (s ep c : ℝ), 0 < ep → ep ≤ s → 0 < c → ep ≤ 1 / c → ep * s ≤ min (s ^ 2) (s / c)) ∧ (∀ T : ℝ, 1 ≤ T → Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) ∧ ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ 2 * Real.exp (-T)) ∧ ∀ (al be : ℝ) (f : ℕ), 0 ≤ al → al ≤ 2 → 0 ≤ be → be ≤ 1 → (al + be) ^ f - al ^ f ≤ f * be * 3 ^ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro s ep c hep hs hc hc'
    have hs0 : 0 ≤ s := le_trans hep.le hs
    refine le_min ?_ ?_
    · rw [sq]
      exact mul_le_mul_of_nonneg_right hs hs0
    · calc ep * s ≤ (1 / c) * s := mul_le_mul_of_nonneg_right hc' hs0
        _ = s / c := by ring
  · intro T hT
    have hg : Summable (fun i : ℕ => Real.exp (-T) * (1 / 2 : ℝ) ^ i) :=
      summable_geometric_two.mul_left _
    have hs : Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) :=
      Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
        (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hg
    refine ⟨hs, ?_⟩
    calc ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ ∑' i : ℕ, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
          Summable.tsum_le_tsum (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hs hg
      _ = 2 * Real.exp (-T) := by rw [tsum_mul_left, tsum_geometric_two, mul_comm]
  · intro al be f h0 h2 hb0 hb1
    induction f with
    | zero => simp
    | succ n ih =>
      have hX : 0 ≤ (al + be) ^ n - al ^ n :=
        sub_nonneg.mpr (pow_le_pow_left₀ h0 (by linarith) n)
      have ha : al ^ n ≤ 3 ^ n := pow_le_pow_left₀ h0 (by linarith) n
      have h1 : (al + be) * ((al + be) ^ n - al ^ n) ≤ 3 * ((n : ℝ) * be * 3 ^ n) :=
        mul_le_mul (by linarith) ih hX (by norm_num)
      have h3 : be * al ^ n ≤ be * 3 ^ n := mul_le_mul_of_nonneg_left ha hb0
      have h4 : 0 ≤ be * 3 ^ n := mul_nonneg hb0 (pow_nonneg (by norm_num) n)
      calc (al + be) ^ (n + 1) - al ^ (n + 1)
          = (al + be) * ((al + be) ^ n - al ^ n) + be * al ^ n := by ring
        _ ≤ 3 * ((n : ℝ) * be * 3 ^ n) + be * 3 ^ n := by linarith
        _ ≤ ((n + 1 : ℕ) : ℝ) * be * 3 ^ (n + 1) := by
          push_cast
          rw [pow_succ]
          nlinarith

end GlobalTheory
end
