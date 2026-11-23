module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory InnerProductSpace
open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_rankOne_self : Continuous fun w : H => rankOne ℂ w w := by
  have h : (fun w : H => rankOne ℂ w w) =
      fun w => StrongDual.smulRightL ℂ H H (innerSL ℂ w) w := by
    funext w
    ext z
    simp [rankOne_apply]
  rw [h]
  exact (StrongDual.smulRightL ℂ H H).continuous₂.comp
    ((innerSL ℂ).continuous.prodMk continuous_id)

theorem isCompactOperator_rankOne_self (w : H) : IsCompactOperator (rankOne ℂ w w) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ w)).comp_clm (innerSL ℂ w)

theorem convex_compactOperators : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := by
  exact ((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex

variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}

theorem isCompactOperator_integral [IsProbabilityMeasure μ] {F : X → H →L[ℂ] H}
    (hFi : Integrable F μ) (hF : ∀ k, IsCompactOperator (F k)) :
    IsCompactOperator (∫ k, F k ∂μ : H →L[ℂ] H) := by
  have hs : IsClosed {f : H →L[ℂ] H | IsCompactOperator f} := isClosed_setOfPred_isCompactOperator
  have hc : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := convex_compactOperators
  have hae : ∀ᵐ k ∂μ, F k ∈ {f : H →L[ℂ] H | IsCompactOperator f} := Filter.Eventually.of_forall hF
  have hm := hc.integral_mem hs hae hFi
  exact hm

theorem inner_integral_rankOne {w : X → H} (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ)
    (x y : H) : ⟪y, (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) x⟫_ℂ =
      ∫ k, ⟪w k, x⟫_ℂ * ⟪y, w k⟫_ℂ ∂μ := by
  have hix : Integrable (fun k => rankOne ℂ (w k) (w k) x) μ :=
    (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
  rw [ContinuousLinearMap.integral_apply hFi x, ← integral_inner hix y]
  simp only [rankOne_apply, inner_smul_right]

theorem isSymmetric_integral_rankOne {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_integral_rankOne hFi x y, inner_integral_rankOne hFi y x,
    ← integral_conj]
  congr 1
  funext k
  rw [map_mul, inner_conj_symm, inner_conj_symm, mul_comm]

theorem integral_rankOne_ne_zero {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) (v : H)
    (hpos : 0 < ∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) ≠ 0 := by
  intro h0
  have h := inner_integral_rankOne hFi v v
  rw [h0, zero_apply, inner_zero_right] at h
  have h3 : ∫ k, ⟪w k, v⟫_ℂ * ⟪v, w k⟫_ℂ ∂μ = ((∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext k
    rw [← inner_conj_symm (w k) v, Complex.conj_mul']
    push_cast
    rfl
  rw [h3] at h
  exact hpos.ne' (by exact_mod_cast h.symm)

end

theorem exists_finiteDimensional_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
      [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] (π : K →* (H →L[ℂ] H)), (∀ k x, ‖π k x‖ = ‖x‖) →
      (∀ x, Continuous fun k => π k x) →
      ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ ∀ k, ∀ x ∈ S, π k x ∈ S := by
  intro K _ _ _ _ _ _ H _ _ _ _ π hnorm hcont
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ : ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant ∧
      μ.IsOpenPosMeasure := by
    refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance, inferInstance⟩
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hw : Continuous fun k => π k v := hcont v
  have hFc : Continuous fun k => rankOne ℂ (π k v) (π k v) := continuous_rankOne_self.comp hw
  have hFi : Integrable (fun k => rankOne ℂ (π k v) (π k v)) μ :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTc : IsCompactOperator (∫ k, rankOne ℂ (π k v) (π k v) ∂μ : H →L[ℂ] H) :=
    isCompactOperator_integral hFi (fun k => isCompactOperator_rankOne_self _)
  have hTs := isSymmetric_integral_rankOne hFi
  have hpos : 0 < ∫ k, ‖⟪v, π k v⟫_ℂ‖ ^ 2 ∂μ := by
    have hc : Continuous fun k => ‖⟪v, π k v⟫_ℂ‖ ^ 2 :=
      ((continuous_const.inner hw).norm).pow 2
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (x := 1) ?_
    simp [hv]
  have hT0 := integral_rankOne_ne_zero hFi v hpos
  set T : H →L[ℂ] H := ∫ k, rankOne ℂ (π k v) (π k v) ∂μ with hT
  obtain ⟨c, hc, hc0⟩ : ∃ c, Module.End.HasEigenvalue (T : Module.End ℂ H) c ∧ c ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hT0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp hno)
  have hinner : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map ⟨(π g).toLinearMap, hnorm g⟩ x y
  have hcomm : ∀ g x, T (π g x) = π g (T x) := by
    intro g x
    have hix : Integrable (fun k => rankOne ℂ (π k v) (π k v) x) μ :=
      (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
    have hsh := integral_mul_left_eq_self (μ := μ)
      (fun k => rankOne ℂ (π k v) (π k v) (π g x)) g
    rw [hT, ContinuousLinearMap.integral_apply hFi, ContinuousLinearMap.integral_apply hFi,
      ← ContinuousLinearMap.integral_comp_comm (π g) hix, ← hsh]
    congr 1
    funext k
    have hm : ∀ a b : K, ∀ y, π (a * b) y = π a (π b y) := fun a b y => by rw [map_mul]; rfl
    simp only [rankOne_apply, hm, hinner, map_smul]
  refine ⟨Module.End.eigenspace (T : Module.End ℂ H) c, Module.End.hasEigenvalue_iff.mp hc,
    ContinuousLinearMap.finite_dimensional_eigenspace hTc c hc0, ?_⟩
  intro k x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change T (π k x) = c • π k x
  change T x = c • x at hx
  rw [hcomm, hx, map_smul]

end GlobalTheory.CompactRep
end

section

namespace GlobalTheory.EigenvalueNormBound

theorem pow_mulVec_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (μ : ℂ)
    (h : Matrix.mulVec M v = μ • v) (k : ℕ) : Matrix.mulVec (M ^ k) v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem norm_eigenvalue_le_one : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (C : ℝ),
    (∀ (k : ℕ) (i j : Fin n), ‖(M ^ k) i j‖ ≤ C) → ∀ (v : Fin n → ℂ), v ≠ (0 : Fin n → ℂ) →
    ∀ (μ : ℂ), Matrix.mulVec M v = μ • v → ‖μ‖ ≤ (1 : ℝ) := by
  intro n M C hC v hv μ hμ
  by_contra hlt
  rw [not_le] at hlt

  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi

  have bound : ∀ k : ℕ, ‖μ‖ ^ k * ‖v i‖ ≤ C * ∑ j, ‖v j‖ := by
    intro k
    have e := congrFun (pow_mulVec_eq M v μ hμ k) i
    have hk : ‖μ‖ ^ k * ‖v i‖ = ‖∑ j, (M ^ k) i j * v j‖ := by
      have : (M ^ k).mulVec v i = ∑ j, (M ^ k) i j * v j := by simp [Matrix.mulVec, dotProduct]
      rw [← this, e, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    rw [hk]
    calc ‖∑ j, (M ^ k) i j * v j‖ ≤ ∑ j, ‖(M ^ k) i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖(M ^ k) i j‖ * ‖v j‖ := by simp only [norm_mul]
      _ ≤ ∑ j, C * ‖v j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC k i j) (norm_nonneg _)
      _ = C * ∑ j, ‖v j‖ := by rw [Finset.mul_sum]

  have htend : Filter.Tendsto (fun k : ℕ => ‖μ‖ ^ k * ‖v i‖) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hvi (tendsto_pow_atTop_atTop_of_one_lt hlt)
  obtain ⟨k, hk⟩ := (htend.eventually_gt_atTop (C * ∑ j, ‖v j‖)).exists
  exact absurd (bound k) (not_le.mpr hk)

end GlobalTheory.EigenvalueNormBound
end

section

open MeasureTheory Classical

namespace GlobalTheory.BlockFubini

theorem integral_block_indicator (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (hR : ∀ i, R i ↔ P i ∧ ¬ Q i) (hQ : ∀ i, Q i → P i) (s : Set k) (hs : MeasurableSet s) (_hν : ν s ≠ ⊤) (G : (I → k) → ℂ) (hG : ∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) : ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  let σ : {i // Q i} ⊕ {i // R i} ≃ {i // P i} :=
    { toFun := Sum.elim (fun a => ⟨a.1, hQ _ a.2⟩) (fun a => ⟨a.1, ((hR _).1 a.2).1⟩)
      invFun := fun a => if h : Q a.1 then Sum.inl ⟨a.1, h⟩ else Sum.inr ⟨a.1, (hR _).2 ⟨a.2, h⟩⟩
      left_inv := by
        rintro (a | a)
        · simp [a.2]
        · simp [((hR _).1 a.2).2]
      right_inv := by
        intro a
        by_cases h : Q a.1 <;> simp [h] }
  have h1 := measurePreserving_piCongrLeft (α := fun _ : {i // P i} => k) (fun _ => ν) σ
  have h2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // Q i} ⊕ {i // R i} => k) (fun _ => ν)
  have h3 := h1.comp h2
  rw [← h3.integral_comp ((MeasurableEquiv.measurableEmbedding _).comp (MeasurableEquiv.measurableEmbedding _))]
  have key : ∀ z : ({i // Q i} → k) × ({i // R i} → k),
      G (fun i => if h : P i then ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z ⟨i, h⟩ else 0)
      = (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) z.1 * G (fun i => if h : R i then z.2 ⟨i, h⟩ else 0) := by
    intro z
    set E := ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z with hE
    have e0 : ∀ a, E (σ a) = Sum.elim z.1 z.2 a := by
      intro a
      rw [hE]
      simp only [Function.comp_apply]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      cases a <;> rfl
    have e1 : ∀ i (h : Q i), E ⟨i, hQ i h⟩ = z.1 ⟨i, h⟩ := fun i h => e0 (Sum.inl ⟨i, h⟩)
    have e2 : ∀ i (h : R i), E ⟨i, ((hR i).1 h).1⟩ = z.2 ⟨i, h⟩ := fun i h => e0 (Sum.inr ⟨i, h⟩)
    rw [hG]
    congr 1
    · rw [Set.indicator_apply]
      congr 1
      apply propext
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h a
        have := h a.1 a.2
        rwa [dif_pos (hQ _ a.2), e1 _ a.2] at this
      · intro h i hi
        rw [dif_pos (hQ _ hi), e1 _ hi]
        exact h _
    · congr 1
      funext i
      by_cases hq : Q i
      · have : ¬ R i := fun h => ((hR i).1 h).2 hq
        simp [hq, this]
      · by_cases hp : P i
        · have : R i := (hR i).2 ⟨hp, hq⟩
          simp only [hq, if_false, dif_pos hp, dif_pos this]
          exact e2 i this
        · have : ¬ R i := fun h => hp ((hR i).1 h).1
          simp [hq, hp, this]
  simp_rw [key]
  rw [integral_prod_mul (fun x => (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) x) (fun y : {i // R i} → k => G (fun i => if h : R i then y ⟨i, h⟩ else 0))]
  congr 1
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hs)]
  simp [Measure.real, Measure.pi_pi]

end GlobalTheory.BlockFubini
end

section

noncomputable section

namespace GlobalTheory.Honda.TwistedDivision

variable {K : Type} [NormedField K]

theorem norm_sub_le_max_of_ultrametric_field [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_eq (by rw [norm_neg])

theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hτ]

noncomputable def step (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : ℕ → K
  | 0 => 1
  | m + 1 => (π * t (m + 2) - ∑ i : Fin (m + 1), step τ π c t i * (τ ^ (i : ℕ)) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0)
termination_by m => m
decreasing_by exact i.isLt

theorem step_zero (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : step τ π c t 0 = 1 := by
  rw [step]

theorem step_succ (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) (m : ℕ) :
    step τ π c t (m + 1) = (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0) := by
  rw [step, Fin.sum_univ_eq_sum_range (fun i => step τ π c t i * (τ ^ i) (c (m + 1 - i)))]

variable (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1)
include hτ hc0

include hc in
theorem step_bound [IsUltrametricDist K] (hπ : ‖π‖ ≤ 1) (t : ℕ → K) (ht : ∀ j, ‖t j‖ ≤ 1) (m : ℕ) : ‖step τ π c t m‖ ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [step_zero]
    | succ m =>
      rw [step_succ, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_one₀ hπ (norm_nonneg _) (ht _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        exact mul_le_one₀ (ih i (Finset.mem_range.1 hi)) (norm_nonneg _) (hc _)

include hc in
theorem step_diff [IsUltrametricDist K] (t t' : ℕ → K) (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ j, ‖t j - t' j‖ ≤ ε) (m : ℕ) :
    ‖step τ π c t m - step τ π c t' m‖ ≤ ‖π‖ * ε := by
  have hπε : 0 ≤ ‖π‖ * ε := mul_nonneg (norm_nonneg _) hε
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simpa [step_zero] using hπε
    | succ m =>
      rw [step_succ, step_succ, ← sub_div, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      have key : (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) -
          (π * t' (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t' i * (τ ^ i) (c (m + 1 - i))) =
          π * (t (m + 2) - t' (m + 2)) -
            ∑ i ∈ Finset.range (m + 1), (step τ π c t i - step τ π c t' i) * (τ ^ i) (c (m + 1 - i)) := by
        simp only [sub_mul, Finset.sum_sub_distrib]; ring
      rw [key]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hπε fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        have hi' : i < m + 1 := Finset.mem_range.1 hi
        calc ‖step τ π c t i - step τ π c t' i‖ * ‖c (m + 1 - i)‖ ≤ (‖π‖ * ε) * 1 :=
              mul_le_mul (ih i hi') (hc _) (norm_nonneg _) hπε
          _ = ‖π‖ * ε := mul_one _

theorem step_eq (t : ℕ → K) (m : ℕ) :
    π * t (m + 2) = ∑ i ∈ Finset.range (m + 2), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) := by
  have hu : (τ ^ (m + 1)) (c 0) ≠ 0 := by
    intro h0; have := norm_pow_apply τ hτ (m + 1) (c 0); rw [h0, norm_zero, hc0] at this; exact zero_ne_one this
  rw [Finset.sum_range_succ, step_succ]
  have h1 : m + 2 - 1 - (m + 1) = 0 := by omega
  rw [h1, div_mul_cancel₀ _ hu]
  have h2 : ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) =
      ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : m + 2 - 1 - i = m + 1 - i := by omega
    rw [this]
  rw [h2]; ring

end GlobalTheory.Honda.TwistedDivision

namespace GlobalTheory.Honda

open PowerSeries Filter Topology

theorem exists_twisted_division : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (τ : K →+* K),
    (∀ x, ‖τ x‖ = ‖x‖) → ∀ π : K, ‖π‖ < 1 → ∀ c : ℕ → K, ‖c 0‖ = 1 → (∀ i, ‖c i‖ ≤ 1) →
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  intro K _ _ _ τ hτ π hπ c hc0 hc
  let T : ℕ → ℕ → K := fun k => (TwistedDivision.step τ π c)^[k] (fun _ => 1)
  have hTs : ∀ k, T (k + 1) = TwistedDivision.step τ π c (T k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hπ1 : ‖π‖ ≤ 1 := hπ.le
  have hB : ∀ k j, ‖T k j‖ ≤ 1 := by
    intro k
    induction k with
    | zero => intro j; simp [T]
    | succ k ih => intro j; rw [hTs]; exact TwistedDivision.step_bound τ hτ π c hc0 hc hπ1 _ ih j
  have hD : ∀ k j, ‖T (k + 1) j - T k j‖ ≤ ‖π‖ ^ k := by
    intro k
    induction k with
    | zero => intro j; simpa using (TwistedDivision.norm_sub_le_max_of_ultrametric_field _ _).trans (max_le (hB 1 j) (hB 0 j))
    | succ k ih =>
      intro j
      have := TwistedDivision.step_diff τ hτ π c hc0 hc (T (k + 1)) (T k) _ (pow_nonneg (norm_nonneg _) _) ih j
      rw [← hTs (k + 1), ← hTs k, ← pow_succ'] at this
      exact this
  have hC : ∀ j, ∃ x, Tendsto (fun k => T k j) atTop (𝓝 x) := fun j =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ‖π‖ 1 hπ fun k => by
      rw [dist_eq_norm, norm_sub_rev, one_mul]; exact hD k j)
  choose t ht using hC
  refine ⟨t, ?_, ?_, ?_⟩
  · have h0 : ∀ k, T k 0 = 1 := by
      intro k; cases k with
      | zero => rfl
      | succ k => rw [hTs]; exact TwistedDivision.step_zero _ _ _ _
    have : Tendsto (fun k => T k 0) atTop (𝓝 1) := by simp only [h0]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (ht 0) this
  · intro j
    exact le_of_tendsto' (ht j).norm fun k => hB k j
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hL : Tendsto (fun k => π * T k (m + 2)) atTop (𝓝 (π * t (m + 2))) := (ht _).const_mul π
    have hR : Tendsto (fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i))) atTop
        (𝓝 (∑ i ∈ Finset.range (m + 2), t i * (τ ^ i) (c (m + 2 - 1 - i)))) :=
      tendsto_finsetSum _ fun i _ => (((ht i).comp (tendsto_add_atTop_nat 1)).mul_const _)
    have hEq : (fun k => π * T k (m + 2)) =
        fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i)) := by
      funext k; rw [hTs]; exact TwistedDivision.step_eq τ hτ π c hc0 _ m
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR

end GlobalTheory.Honda
end
end

section

namespace GlobalTheory.CardValuationLt

theorem card_val_lt : ∀ (N n : ℕ), n ≤ N → Finset.card {i : Fin N | (↑i : ℕ) < n} = n := by
  intro N n h
  have hmap : ({i : Fin N | (↑i : ℕ) < n} : Finset (Fin N)).map Fin.valEmbedding = Finset.range n := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hm
      exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]

end GlobalTheory.CardValuationLt
end
