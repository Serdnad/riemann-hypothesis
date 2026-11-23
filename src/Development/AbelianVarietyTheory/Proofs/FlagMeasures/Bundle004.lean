module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

@[expose] public section

section

open Finset

namespace GlobalTheory

theorem exists_real_submodule_block_finrank_le :
    ∀ (n : ℕ) (E E' : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ 2 * Module.finrank ℂ E' * Module.finrank ℂ E ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        E'.starProjection ∘L T ∘L E.starProjection ∈ U := by
  intro n E E'
  let f : (E →L[ℂ] E') →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E'.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun M N => by ext; simp
      map_smul' := fun c M => by ext; simp }
  refine ⟨LinearMap.range f, ?_, fun T => ⟨E'.orthogonalProjection ∘L T ∘L E.subtypeL, rfl⟩⟩
  refine (LinearMap.finrank_range_le f).trans (le_of_eq ?_)
  have h1 : Module.finrank ℂ (E →L[ℂ] E') = Module.finrank ℂ E * Module.finrank ℂ E' := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := E')).finrank_eq,
      Module.finrank_linearMap]
  rw [← Module.finrank_mul_finrank ℝ ℂ (E →L[ℂ] E'), Complex.finrank_real_complex, h1]
  ring

end GlobalTheory
end

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem sigmaFinite_and_isInvInvariant_of_continuous_integrable :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
      [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : G → ℂ),
      Continuous f → f 1 ≠ 0 → Integrable f μ → SigmaFinite μ ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ μ _ _ f hfc hf1 hfi

  have hf1' : ‖f 1‖ₑ ≠ 0 := enorm_ne_zero.2 hf1
  have hc0 : ‖f 1‖ₑ / 2 ≠ 0 := by simp [hf1']
  have hcT : ‖f 1‖ₑ / 2 ≠ ⊤ := (ENNReal.div_lt_top enorm_ne_top two_ne_zero).ne

  have hUo : IsOpen {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} := isOpen_lt continuous_const hfc.enorm
  have h1U : (1 : G) ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} :=
    ENNReal.half_lt_self hf1' enorm_ne_top

  have hUfin : μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} < ⊤ := by
    calc μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ≤ μ {x : G | ‖f 1‖ₑ / 2 ≤ ‖f x‖ₑ} :=
          measure_mono (Set.setOf_subset_setOf.2 fun _ hx => hx.le)
      _ ≤ (∫⁻ x, ‖f x‖ₑ ∂μ) / (‖f 1‖ₑ / 2) :=
          meas_ge_le_lintegral_div hfi.aestronglyMeasurable.enorm hc0 hcT
      _ < ⊤ := ENNReal.div_lt_top hfi.2.ne hc0

  have hσ : SigmaFinite μ := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ})
      (fun g => hUo.preimage (continuous_const.mul continuous_id))
    refine Measure.sigmaFinite_of_countable
      (hTc.image fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}) ?_ ?_
    · rintro _ ⟨g, -, rfl⟩
      rw [measure_preimage_mul]
      exact hUfin
    · rw [Set.sUnion_image, hT]
      refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, ?_⟩
      show x⁻¹ * x ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}
      rw [inv_mul_cancel]
      exact h1U

  have key : μ.inv = μ := by
    open Pointwise in
    have hVo : IsOpen ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := hUo.inter hUo.inv
    open Pointwise in
    have hV0 : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ 0 :=
      (hVo.measure_pos μ ⟨1, h1U, by simpa using h1U⟩).ne'
    open Pointwise in
    have hVT : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_left).trans_lt hUfin).ne
    open Pointwise in
    have hVinv : μ.inv ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) = μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := by
      rw [Measure.inv_apply, Set.inter_inv, inv_inv, Set.inter_comm]
    rw [measure_eq_div_smul μ.inv μ hV0 hVT, hVinv, ENNReal.div_self hV0 hVT, one_smul]
  exact ⟨hσ, ⟨key⟩⟩

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.PosDefFT

theorem integral_prod_nonneg (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) := by
  set I := ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) with hI
  have key : ∀ k : ℕ, 0 ≤ (k : ℂ) * (ψ 0 - I + k * I) := by
    intro k
    let P : Measure (Fin k → ℝ) := Measure.pi (fun _ => μ)
    have hint : ∀ i j : Fin k, Integrable (fun t : Fin k → ℝ => ψ (t j - t i)) P := by
      intro i j
      refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
      exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have hval : ∀ i j : Fin k, ∫ t, ψ (t j - t i) ∂P = (if i = j then ψ 0 - I else 0) + I := by
      intro i j
      by_cases h : i = j
      · subst h
        simp
      · have hind : ProbabilityTheory.iIndepFun (fun (i : Fin k) (t : Fin k → ℝ) => t i) P :=
          ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
        have h2 := hind.indepFun h
        rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable] at h2
        have e : ∀ l : Fin k, P.map (fun t => t l) = μ := fun l =>
          (measurePreserving_eval (fun _ : Fin k => μ) l).map_eq
        rw [e, e] at h2
        rw [if_neg h, zero_add, hI, ← h2, integral_map (by fun_prop)]
        exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have h0 : 0 ≤ ∫ t, ∑ i, ∑ j, ψ (t j - t i) ∂P := integral_nonneg (fun t => hp k t)
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))] at h0
    simp_rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint _ j), hval] at h0
    simpa [Finset.sum_add_distrib, mul_add] using h0
  have key2 : ∀ k : ℕ, 0 ≤ (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I := by
    intro k
    have h1 := key (k + 1)
    have h2 : (0 : ℝ) ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by positivity
    have h3 := smul_nonneg h2 h1
    convert h3 using 1
    have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [Complex.real_smul]
    push_cast
    field_simp
  have hlim : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I) atTop
      (𝓝 ((0 : ℝ) • (ψ 0 - I) + I)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _).add_const _
  simpa using ge_of_tendsto' hlim key2

theorem integral_nonneg_of_sums (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hi : Integrable ψ)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i)) :
    0 ≤ ∫ s, ψ s := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let G : ℕ → ℝ → ℂ := fun n x => ∫ s in (-((n : ℝ) * x))..((n : ℝ) * (1 - x)), ψ s
  have hG : ∀ n x, G n x = (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := by
    intro n x
    have h := intervalIntegral.smul_integral_comp_mul_sub (f := ψ) (a := 0) (b := 1) (n : ℝ)
      ((n : ℝ) * x)
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
    simp only [G, μ, mul_sub]
    rw [h]
    simp
  have hint : ∀ n : ℕ, Integrable (fun p : ℝ × ℝ => ψ ((n : ℝ) * (p.2 - p.1))) (μ.prod μ) := by
    intro n
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  have hnn : ∀ n, 0 ≤ ∫ x, G n x ∂μ := by
    intro n
    have h := integral_prod_nonneg (fun s => ψ ((n : ℝ) * s)) (hc.comp (by fun_prop)) C
      (fun s => hb _) (fun k t => by simpa [mul_sub] using hp k (fun i => (n : ℝ) * t i)) μ
    rw [integral_prod _ (hint n)] at h
    simp_rw [hG, integral_smul]
    exact smul_nonneg (Nat.cast_nonneg n) h
  have hlim : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ _x, (∫ s, ψ s) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ s, ‖ψ s‖) ?_
      (integrable_const _) ?_ ?_
    · intro n
      have : G n = fun x => (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := funext (hG n)
      rw [this]
      exact ((hint n).integral_prod_left.smul (n : ℝ)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
      exact setIntegral_le_integral hi.norm (Eventually.of_forall fun _ => norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      refine intervalIntegral_tendsto_integral hi ?_ ?_
      · exact tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hx.1)
      · exact tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hx.2)
  simpa using ge_of_tendsto' hlim hnn

theorem fourier_nonneg : ∀ φ : ℝ → ℂ, Continuous φ →
    (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
    (∀ (k : ℕ) (t : Fin k → ℝ) (z : Fin k → ℂ),
      0 ≤ ∑ i, ∑ j, star (z i) * z j * φ (t j - t i)) →
    ∀ ξ : ℝ, 0 ≤ ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s := by
  rintro φ hc ⟨A, e, he, hb⟩ hp ξ
  have hn : ∀ s : ℝ, ‖Complex.exp (-(Complex.I * ξ * s)) * φ s‖ = ‖φ s‖ := by
    intro s
    rw [norm_mul, Complex.norm_exp]
    simp
  have hc' : Continuous fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s := by fun_prop
  have hA : 0 ≤ A := by simpa using (norm_nonneg _).trans (hb 0)
  refine integral_nonneg_of_sums _ hc' A (fun s => ?_) ?_ (fun k t => ?_)
  · rw [hn]
    refine (hb s).trans (mul_le_of_le_one_right hA ?_)
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  · have h1 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Ioi 0) := by
      refine (exp_neg_integrableOn_Ioi 0 he).congr_fun (fun s hs => ?_) measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.1 hs)]
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Iic 0) := by
      refine (integrableOn_exp_mul_Iic he 0).congr_fun (fun s hs => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.1 hs)]
    have h3 : Integrable (fun s : ℝ => Real.exp (-(e * |s|))) := by
      have := h2.union h1
      rwa [Set.Iic_union_Ioi, integrableOn_univ] at this
    refine (h3.const_mul A).mono' hc'.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [hn]
    exact hb s
  · convert hp k t (fun j => Complex.exp (-(Complex.I * ξ * t j))) using 4 with i _ j _
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp
    ring

end GlobalTheory.PosDefFT
end

section

namespace GlobalTheory.DecayOfMemSpan

theorem decay_of_mem_span {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {u : H}
    (h : ∀ v ∈ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))) :
    ∀ v ∈ Submodule.span ℂ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, fun g => ?_⟩
    rw [inner_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA g) (hB g))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖a‖ * A, fun g => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA g) (norm_nonneg a)

end GlobalTheory.DecayOfMemSpan
end

section

namespace GlobalTheory.SpanDecay

theorem span_decay : (let d1 : {G H : Type} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → (G → H →L[ℂ] H) → (G → ℝ) → ℝ → H → H → Prop := @(fun {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : G → H →L[ℂ] H) (D : G → ℝ) (c : ℝ) (v u : H) ↦ ∃ (C : ℝ), ∀ (g : G), ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))); ∀ {G H : Type} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {v : H}, (∀ u ∈ S, d1 ρ D c v u) → ∀ u ∈ Submodule.span ℂ S, d1 ρ D c v u) := by
  dsimp only
  intro G H _ _ ρ D c S v hS u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1⟩ := hx
    obtain ⟨C2, h2⟩ := hy
    refine ⟨C1 + C2, fun g => ?_⟩
    rw [map_add (f := _), inner_add_right, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 g) (h2 g))
  | smul a x _ hx =>
    obtain ⟨C, h⟩ := hx
    refine ⟨‖a‖ * C, fun g => ?_⟩
    rw [map_smul, inner_smul_right, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h g) (norm_nonneg _)

end GlobalTheory.SpanDecay
end

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_translate_translate_of_norm {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (w : H)
    (g h : G) : ⟪σ g w, σ h w⟫_ℂ = ⟪w, σ (g⁻¹ * h) w⟫_ℂ := by
  have hmul : σ h w = σ g (σ (g⁻¹ * h) w) := by
    show σ h w = (σ g * σ (g⁻¹ * h)) w
    rw [← map_mul, mul_inv_cancel_left]
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  rw [hmul]
  exact T.inner_map_map w (σ (g⁻¹ * h) w)

theorem exists_isometric_intertwiner_of_matrixCoeff_eq :
    ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (Hp : Type) [NormedAddCommGroup Hp]
      [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)),
      (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (w : H) (v : Hp),
      (∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0) → (∀ g, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) →
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
  intro G _ H _ _ _ σ Hp _ _ _ π hσ hπ w v hcyc hvw

  obtain ⟨A, hA⟩ : ∃ A : (G →₀ ℂ) →ₗ[ℂ] H, A = Finsupp.linearCombination ℂ (fun g => σ g w) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (G →₀ ℂ) →ₗ[ℂ] Hp, B = Finsupp.linearCombination ℂ (fun g => π g v) :=
    ⟨_, rfl⟩

  have hkey : ∀ g h : G, ⟪π g v, π h v⟫_ℂ = ⟪σ g w, σ h w⟫_ℂ := by
    intro g h
    rw [inner_translate_translate_of_norm π hπ, inner_translate_translate_of_norm σ hσ, hvw]
  have hinner : ∀ c d, ⟪B c, B d⟫_ℂ = ⟪A c, A d⟫_ℂ := by
    intro c d
    rw [hA, hB]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hkey]
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A c), hinner]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]

  obtain ⟨F, hF⟩ : ∃ F : LinearMap.range A →ₗ[ℂ] Hp,
      ∀ c, F ⟨A c, LinearMap.mem_range_self A c⟩ = B c :=
    ⟨(LinearMap.ker A).liftQ B hker ∘ₗ A.quotKerEquivRange.symm.toLinearMap, fun c => by simp⟩
  have hFn : ∀ y, ‖F y‖ = ‖y‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hF, hnorm]
    rfl
  let F' : LinearMap.range A →ₗᵢ[ℂ] Hp := { toLinearMap := F, norm_map' := hFn }

  have hclos : (LinearMap.range A).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    refine hcyc y fun g => inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hy _ ?_)
    exact ⟨Finsupp.single g 1, by simp [hA]⟩
  have hdense : DenseRange (LinearMap.range A).subtypeL :=
    denseRange_subtype_val.mpr (Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos)
  have huni : IsUniformInducing (LinearMap.range A).subtypeL :=
    (LinearMap.range A).subtypeₗᵢ.isometry.isUniformInducing

  obtain ⟨X, hXdef⟩ : ∃ X : H →L[ℂ] Hp, X = F'.toContinuousLinearMap.extend (LinearMap.range A).subtypeL :=
    ⟨_, rfl⟩
  have hX : ∀ c, X (A c) = B c := fun c => by
    rw [hXdef]
    exact (ContinuousLinearMap.extend_eq F'.toContinuousLinearMap hdense huni
      ⟨A c, LinearMap.mem_range_self A c⟩).trans (hF c)
  have hXn : ∀ u, ‖X u‖ = ‖u‖ := by
    intro u
    refine hdense.induction_on (p := fun u => ‖X u‖ = ‖u‖) u
      (isClosed_eq (continuous_norm.comp X.continuous) continuous_norm) ?_
    rintro ⟨_, c, rfl⟩
    show ‖X (A c)‖ = ‖A c‖
    rw [hX, hnorm]

  have hshA : ∀ g c, σ g (A c) = A (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hA, Finsupp.linearCombination_mapDomain]
    change (σ g : H →ₗ[ℂ] H) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hshB : ∀ g c, π g (B c) = B (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hB, Finsupp.linearCombination_mapDomain]
    change (π g : Hp →ₗ[ℂ] Hp) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hXi : ∀ g u, X (σ g u) = π g (X u) := by
    intro g u
    refine hdense.induction_on (p := fun u => X (σ g u) = π g (X u)) u
      (isClosed_eq (X.continuous.comp (σ g).continuous) ((π g).continuous.comp X.continuous)) ?_
    rintro ⟨_, c, rfl⟩
    show X (σ g (A c)) = π g (X (A c))
    rw [hshA, hX, hX, hshB]
  have hw : A (Finsupp.single 1 1) = w := by simp [hA]
  have hv : B (Finsupp.single 1 1) = v := by simp [hB]
  refine ⟨{ toLinearMap := (X : H →ₗ[ℂ] Hp), norm_map' := hXn }, ?_, fun g u => hXi g u⟩
  show X w = v
  rw [← hw, hX, hv]

end GlobalTheory
end

section

namespace GlobalTheory.InnerSumZeroSpan

theorem main : (let d1 : ℕ → Type := @(fun (n : ℕ) ↦ EuclideanSpace ℂ (Fin n)); ∀ {n : ℕ} (L M : d1 n →L[ℂ] d1 n) (s t : Set (d1 n)), (∀ u ∈ s, ∀ z ∈ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) → ∀ u ∈ Submodule.span ℂ s, ∀ z ∈ Submodule.span ℂ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) := by
  intro d1 n L M s t h u hu z hz
  induction hz using Submodule.span_induction with
  | mem z hz' =>
    induction hu using Submodule.span_induction with
    | mem u hu' => exact h u hu' z hz'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), inner_add_left, inner_add_left, add_add_add_comm, hx, hy, add_zero]
    | smul c x _ hx =>
      rw [map_smul, inner_smul_left, inner_smul_left, ← mul_add, hx, mul_zero]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), inner_add_right, inner_add_right, add_add_add_comm, hx, hy, add_zero]
  | smul c x _ hx =>
    rw [map_smul, inner_smul_right, inner_smul_right, ← mul_add, hx, mul_zero]

end GlobalTheory.InnerSumZeroSpan
end
