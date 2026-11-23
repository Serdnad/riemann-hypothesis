module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle134
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSumma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviUnip

variable {n n₀ a : ℕ} {j : Fin a → ℕ}

theorem umul {ε : Fin n → Bool} (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uone {ε : Fin n → Bool} : uMat (1 : UJ ε) = 1 := rfl

theorem umul_inv {ε : Fin n → Bool} (g : UJ ε) : uMat g * uMat g⁻¹ = 1 := by rw [← umul, mul_inv_cancel, uone]

theorem uinv_mul {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by rw [← umul, inv_mul_cancel, uone]

theorem col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {i : Fin a} (hi : i.castSucc < k) (u : Fin (j i) → ℂ) :
    B i *ᵥ u ∈ W k := by
  classical
  refine (hB k _).2 ⟨Pi.single i u, fun i' hi' => ?_, ?_⟩
  · have hne : i' ≠ i := by rintro rfl; exact hi' hi
    exact Pi.single_eq_of_ne hne _
  · rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, Matrix.mulVec_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

theorem map_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} (F : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ))
    (h : ∀ i : Fin a, i.castSucc < k → ∀ u, (F * B i) *ᵥ u ∈ U) {y : Fin n → ℂ} (hy : y ∈ W k) :
    F *ᵥ y ∈ U := by
  obtain ⟨u, hu, rfl⟩ := (hB k y).1 hy
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.castSucc < k
  · rw [Matrix.mulVec_mulVec]
    exact h i hi (u i)
  · rw [hu i hi, Matrix.mulVec_zero, Matrix.mulVec_zero]
    exact U.zero_mem

theorem sum_col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {r : ℕ} (q : ∀ i, Matrix (Fin (j i)) (Fin r) ℂ)
    (hq : ∀ i : Fin a, ¬ i.castSucc < k → q i = 0) (u : Fin r → ℂ) : (∑ i, B i * q i) *ᵥ u ∈ W k := by
  rw [Matrix.sum_mulVec]
  refine (hB k _).2 ⟨fun i => q i *ᵥ u, fun i hi => by
    show q i *ᵥ u = 0
    rw [hq i hi, Matrix.zero_mulVec], ?_⟩
  exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_mulVec _ _ _).symm

theorem mul_inv_mem_flagN (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (hF : IsFrame ε ε₀ B B₀)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ)
    (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ) (s h : Formalism.REAL.UJ ε₀)
    (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g m : Formalism.REAL.UJ ε)
    (hA : SpansFlag A W) (hB : SpansFlag B W) (hp : ∀ k i, i < k → p k i = 0) (hpd : ∀ i, (p i i).det ≠ 0)
    (hAB : ∀ i, A i = ∑ k, B k * p k i) (hA₀ : A₀ = B₀ * uMat s + ∑ k, B k * d k)
    (hy : ∀ i, (y i).det ≠ 0) (hg : ∀ i, uMat g * A i = A i * y i) (hg₀ : uMat g * A₀ = A₀ * uMat h)
    (hm : uMat m = lev ε B B₀ (fun i => p i i * y i * (p i i)⁻¹) (uMat (s * h * s⁻¹))) :
    g * m⁻¹ ∈ flagN ε W := by
  classical
  have hpu : ∀ i, IsUnit (p i i).det := fun i => isUnit_iff_ne_zero.2 (hpd i)
  have hyu : ∀ i, IsUnit (y i).det := fun i => isUnit_iff_ne_zero.2 (hy i)
  set x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ := fun i => p i i * y i * (p i i)⁻¹ with hx
  have hxu : ∀ i, IsUnit (x i).det := by
    intro i
    rw [isUnit_iff_ne_zero]
    simp [hx, Matrix.det_mul, Matrix.det_nonsing_inv, hpd i, hy i]

  have hMB : ∀ i, uMat m⁻¹ * B i = B i * (x i)⁻¹ := by
    intro i
    have h1 : uMat m * B i = B i * x i := by
      rw [hm]
      exact GlobalTheory.LeviIso.IsFrame.lev_mul_B _ _ hF i
    calc uMat m⁻¹ * B i = uMat m⁻¹ * (B i * (x i * (x i)⁻¹)) := by
          rw [Matrix.mul_nonsing_inv _ (hxu i), Matrix.mul_one]
      _ = (uMat m⁻¹ * uMat m) * B i * (x i)⁻¹ := by
          rw [← Matrix.mul_assoc (B i), ← h1]
          simp only [Matrix.mul_assoc]
      _ = B i * (x i)⁻¹ := by rw [uinv_mul, Matrix.one_mul]

  have hG : ∀ k (v : Fin n → ℂ), v ∈ W k → uMat g *ᵥ v ∈ W k := fun k v hv =>
    map_mem hA (uMat g) (W k) (fun i hi u => by
      rw [hg i, ← Matrix.mulVec_mulVec]
      exact col_mem hA hi _) hv
  have hsub : ∀ v : Fin n → ℂ, uMat (g * m⁻¹) *ᵥ v - v = (uMat g * uMat m⁻¹ - 1) *ᵥ v := by
    intro v
    rw [umul, Matrix.sub_mulVec, Matrix.one_mulVec]

  have hNA : ∀ l, (uMat g * uMat m⁻¹ - 1) * A l =
      uMat g * ∑ k, B k * ((x k)⁻¹ * p k l - p k l * (y l)⁻¹) := by
    intro l
    have e1 : uMat m⁻¹ * A l = ∑ k, B k * ((x k)⁻¹ * p k l) := by
      rw [hAB l, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.mul_assoc, hMB k, Matrix.mul_assoc]
    have e2 : uMat g * A l * (y l)⁻¹ = A l := by
      rw [hg l, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hyu l), Matrix.mul_one]
    calc (uMat g * uMat m⁻¹ - 1) * A l = uMat g * (uMat m⁻¹ * A l) - A l := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * ∑ k, B k * ((x k)⁻¹ * p k l) - uMat g * A l * (y l)⁻¹ := by rw [e1, e2]
      _ = _ := by
          rw [hAB l]
          simp only [Matrix.mul_sub, Finset.sum_sub_distrib, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_assoc]

  have hq0 : ∀ l k, l ≤ k → (x k)⁻¹ * p k l - p k l * (y l)⁻¹ = 0 := by
    intro l k hlk
    rcases hlk.lt_or_eq with h | rfl
    · rw [hp k l h, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    · have : (x l)⁻¹ * p l l = p l l * (y l)⁻¹ := by
        rw [hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hpu l),
          Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hpu l), Matrix.mul_one]
      rw [this, sub_self]

  have hNB₀ : (uMat g * uMat m⁻¹ - 1) * B₀ =
      (∑ k, B k * d k) * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) := by
    have hinv : (s * h * s⁻¹)⁻¹ = s * h⁻¹ * s⁻¹ := by group
    have e1 : uMat m⁻¹ * B₀ = B₀ * (uMat s * uMat h⁻¹ * uMat s⁻¹) := by
      have h1 : uMat m * B₀ = B₀ * uMat (s * h * s⁻¹) := by
        rw [hm]
        exact GlobalTheory.LeviIso.IsFrame.lev_mul_B₀ _ _ hF
      calc uMat m⁻¹ * B₀ = uMat m⁻¹ * (B₀ * (uMat (s * h * s⁻¹) * uMat (s * h * s⁻¹)⁻¹)) := by
            rw [umul_inv, Matrix.mul_one]
        _ = (uMat m⁻¹ * uMat m) * B₀ * uMat (s * h * s⁻¹)⁻¹ := by
            rw [← Matrix.mul_assoc B₀, ← h1]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [uinv_mul, Matrix.one_mul, hinv, umul, umul]
    have e2 : B₀ * uMat s = A₀ - ∑ k, B k * d k := by
      rw [hA₀]
      abel
    calc (uMat g * uMat m⁻¹ - 1) * B₀ = uMat g * (uMat m⁻¹ * B₀) - B₀ := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * (B₀ * uMat s) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e1]
          simp only [Matrix.mul_assoc]
      _ = (A₀ * uMat h - uMat g * ∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e2, Matrix.mul_sub, hg₀]
      _ = A₀ * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [Matrix.sub_mul, Matrix.mul_assoc A₀, ← Matrix.mul_assoc (uMat h), umul_inv h,
            Matrix.one_mul]
      _ = (B₀ * uMat s + ∑ k, B k * d k) * uMat s⁻¹
            - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by rw [← hA₀]
      _ = _ := by
          rw [Matrix.add_mul, Matrix.mul_assoc B₀, umul_inv s, Matrix.mul_one]
          abel
  have hlast : ∀ i : Fin a, i.castSucc < Fin.last a := fun i => Fin.castSucc_lt_last i
  have hD : ∀ z, (∑ k, B k * d k) *ᵥ z ∈ W (Fin.last a) := fun z =>
    sum_col_mem hB d (fun i hi => absurd (hlast i) hi) z
  simp only [flagN, Set.mem_ofPred_eq]
  refine ⟨fun i v hv => ?_, fun v hv => ?_⟩
  · rw [hsub]
    refine map_mem hA _ (W i.castSucc) (fun l hl u => ?_) hv
    rw [hNA l, ← Matrix.mulVec_mulVec]
    refine hG _ _ (sum_col_mem hB (fun k => (x k)⁻¹ * p k l - p k l * (y l)⁻¹) (fun k hk => hq0 l k ?_) u)
    rw [Fin.castSucc_lt_castSucc_iff, not_lt] at hk
    rw [Fin.castSucc_lt_succ_iff] at hl
    exact hl.trans hk
  · rw [hsub]

    have hBJ : ∀ i, (B i)ᴴ *ᵥ (Jm ε *ᵥ v) = 0 := by
      intro i
      funext c
      have hc := hv _ (col_mem hB (hlast i) (Pi.single c 1))
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at hc
      simpa using hc
    have hdec : v = (∑ i, B i *ᵥ ((B i)ᴴ *ᵥ v)) + B₀ *ᵥ (B₀ᴴ *ᵥ v) := by
      have hF' := hF
      unfold IsFrame at hF'
      obtain ⟨-, -, -, -, -, -, hsum⟩ := hF'
      have := congrArg (· *ᵥ v) hsum
      simp only [Matrix.one_mulVec, Matrix.add_mulVec, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hBJ,
        Matrix.mulVec_zero, Finset.sum_const_zero, add_zero] at this
      exact this.symm
    rw [hdec, Matrix.mulVec_add]
    refine add_mem ?_ ?_
    · refine map_mem hB _ (W (Fin.last a)) (fun i _ u => ?_)
        ((hB _ _).2 ⟨_, fun i hi => absurd (hlast i) hi, rfl⟩)
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hMB i, Matrix.sub_mulVec]
      refine sub_mem ?_ (col_mem hB (hlast i) u)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hG _ _ (col_mem hB (hlast i) _)
    · rw [Matrix.mulVec_mulVec, hNB₀, Matrix.sub_mulVec]
      refine sub_mem ?_ ?_
      · rw [← Matrix.mulVec_mulVec]
        exact hD _
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact hG _ _ (hD _)

end GlobalTheory.LeviUnip
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarPi

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hrw : ∀ z : E × (Fin n → E),
        ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm z i) =
          f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := by
      intro z
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp_rw [hrw]
    rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → E => ∏ i : Fin n, f i.succ (y i))
      (hf 0).aemeasurable, ih (fun i => f i.succ) (fun i => hf i.succ),
      Fin.prod_univ_succ]
    · exact (Finset.measurable_prod _ fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i)).aemeasurable

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hrw : ∀ y : Fin (Fintype.card ι) → E,
      ∏ i, f i (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e y i) = ∏ k, f (e k) (y k) := by
    intro y
    rw [← e.prod_comp]
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hrw]
  rw [lintegral_pi_fin _ μ (fun k => f (e k)) (fun k => hf (e k))]
  exact e.prod_comp (fun i => ∫⁻ t, f i t ∂μ)

theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq (μ := fun _ : ι => μ.withDensity f) fun s hs => ?_
  have hind : ∀ x : ι → E, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x =
      ∏ i, (s i).indicator f (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (Set.mem_univ_pi.1 hx i) f).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  rw [lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

theorem haarGL_eq_pi : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  intro E _ _ j
  set F : (Fin j → Fin j → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)
  have hF : Measurable F := by
    have hc : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := continuous_id.matrix_det
    exact ENNReal.measurable_ofReal.comp
      (((hc.norm.pow 2).measurable.inv).pow_const j)
  have : SigmaFinite ((volume : Measure (Fin j → Fin j → ℂ)).withDensity F) :=
    inferInstanceAs (SigmaFinite (haarLoc j))
  have hloc : haarLoc j = (volume : Measure (Fin j → Fin j → ℂ)).withDensity F := rfl
  simp only [hloc]
  rw [pi_withDensity (ι := InfinitePlace E) volume F hF, ← volume_pi, haarGL]
  congr 1
  funext x
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => by positivity]
  congr 1
  unfold MatInf at x
  unfold GlobalTheory.FlagMeas.detNorm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]

end GlobalTheory.HaarPi
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm hs Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviIso

theorem trace_compress {n m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin m) ℂ) (hC : Cᴴ * C = 1) (hD : D * C = C * y) :
    (Dᴴ * D * (C * Cᴴ)).trace = (yᴴ * y).trace := by
  have hcore : Cᴴ * (Dᴴ * D * C) = yᴴ * y :=
    calc Cᴴ * (Dᴴ * D * C) = (D * C)ᴴ * (D * C) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C * y)ᴴ * (C * y) := by rw [hD]
      _ = yᴴ * (Cᴴ * C) * y := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = yᴴ * y := by rw [hC, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, hcore]

private theorem hs_eq_re_trace_conjTranspose_mul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hs X = (trace (Xᴴ * X)).re := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem hs_lev_sub_one : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ →
    ∀ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Matrix (Fin n₀) (Fin n₀) ℂ),
    Formalism.REAL.hs (lev ε B B₀ x g - 1) =
      ∑ i, (Formalism.REAL.hs (x i - 1) + Formalism.REAL.hs ((x i)⁻¹ - 1)) + Formalism.REAL.hs (g - 1) := by
  intro n n₀ a j ε ε₀ B B₀ h x g
  have hJ : ∀ i, (Jm ε * B i)ᴴ * (Jm ε * B i) = 1 := fun i => by
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε),
      Jm_mul_self, Matrix.one_mul, h.1 i]
  have hsplit : (1 : Matrix (Fin n) (Fin n) ℂ) =
      ∑ i, B i * (B i)ᴴ + ∑ i, (Jm ε * B i) * (Jm ε * B i)ᴴ + B₀ * B₀ᴴ := by
    rw [← h.2.2.2.2.2.2]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hsub : ∀ {m : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) (y : Matrix (Fin m) (Fin m) ℂ),
      lev ε B B₀ x g * C = C * y → (lev ε B B₀ x g - 1) * C = C * (y - 1) := by
    intro m C y hy
    rw [Matrix.sub_mul, hy, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hconj : ∀ {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ), hs Yᴴ = hs Y := by
    intro m Y
    rw [hs_eq_re_trace_conjTranspose_mul, hs_eq_re_trace_conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  set M := lev ε B B₀ x g - 1 with hM
  have eB : ∀ i, (Mᴴ * M * (B i * (B i)ᴴ)).trace = ((x i - 1)ᴴ * (x i - 1)).trace := fun i =>
    trace_compress M (B i) _ (h.1 i) (hsub _ _ (h.lev_mul_B x g i))
  have eJ : ∀ i, (Mᴴ * M * ((Jm ε * B i) * (Jm ε * B i)ᴴ)).trace =
      (((x i)⁻¹ᴴ - 1)ᴴ * ((x i)⁻¹ᴴ - 1)).trace := fun i =>
    trace_compress M (Jm ε * B i) _ (hJ i) (hsub _ _ (h.lev_mul_JB x g i))
  have e0 : (Mᴴ * M * (B₀ * B₀ᴴ)).trace = ((g - 1)ᴴ * (g - 1)).trace :=
    trace_compress M B₀ _ h.2.2.2.2.1 (hsub _ _ (h.lev_mul_B₀ x g))
  rw [hs_eq_re_trace_conjTranspose_mul, ← Matrix.mul_one (Mᴴ * M), hsplit]
  simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.trace_add, Matrix.trace_sum, Complex.add_re,
    Complex.re_sum, eB, eJ, e0, Finset.sum_add_distrib]
  have hinv : ∀ i, (x i)⁻¹ᴴ - 1 = ((x i)⁻¹ - 1)ᴴ := fun i => by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  simp only [hinv, ← hs_eq_re_trace_conjTranspose_mul, hconj]

end GlobalTheory.LeviIso
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.HaarMul

theorem measurePreserving_withDensity {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → X}
    (hf : Measurable f) {ρ : X → ENNReal} (hρ : Measurable ρ) {c d : ENNReal} (hcd : d * c = 1)
    (hμ : μ.map f = c • μ) (hρf : ∀ x, ρ x = d * ρ (f x)) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]

  have h1 : ∫⁻ x in f ⁻¹' s, ρ x ∂μ = ∫⁻ x, d * s.indicator ρ (f x) ∂μ := by
    rw [← lintegral_indicator (hf hs)]
    congr 1
    funext x
    by_cases hx : f x ∈ s
    · simp [Set.indicator_apply, hx, ← hρf x]
    · simp [Set.indicator_apply, hx]
  rw [h1, lintegral_const_mul d (f := fun x => s.indicator ρ (f x)) ((hρ.indicator hs).comp hf),
    ← lintegral_map (hρ.indicator hs) hf, hμ,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hcd, one_mul, lintegral_indicator hs]

theorem measurePreserving_mul_mul : ∀ (j : ℕ) (a b : Matrix (Fin j) (Fin j) ℂ), a.det ≠ 0 → b.det ≠ 0 →
    MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => (a * Matrix.of x * b) r s)
      (haarLoc j) (haarLoc j) := by
  intro j a b ha hb

  let L : (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) :=
    { toFun := fun x r s => (a * Matrix.of x * b) r s
      map_add' := fun x y => by
        have h : a * Matrix.of (x + y) * b = a * Matrix.of x * b + a * Matrix.of y * b := by
          rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add, Matrix.add_mul]
        funext r s
        exact congrFun (congrFun h r) s
      map_smul' := fun c x => by
        have h : a * Matrix.of (c • x) * b = c • (a * Matrix.of x * b) := by
          rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul, Matrix.smul_mul]
        funext r s
        exact congrFun (congrFun h r) s }
  have hdet : LinearMap.det L = ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    GlobalTheory.TwoSidedJac.real_jacobians.1 j j a b L (fun T => rfl)
  have hA : ‖a.det‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hB : ‖b.det‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have hD : 0 < ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    mul_pos (pow_pos (norm_pos_iff.2 ha) _) (pow_pos (norm_pos_iff.2 hb) _)
  have hcont : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_id.matrix_det : Continuous fun A : Matrix (Fin j) (Fin j) ℂ => A.det)
  have hρ : Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) :=
    ENNReal.measurable_ofReal.comp (((hcont.measurable.norm.pow_const 2).inv).pow_const j)

  haveI : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure ℂ))
  haveI : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure (Fin j → ℂ)))
  have hμ : (volume : Measure (Fin j → Fin j → ℂ)).map L =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hD.ne')
  have hcd : ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) * ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    rw [hdet, abs_of_pos (inv_pos.2 hD), ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne', ENNReal.ofReal_one]

  have hρf : ∀ x : Fin j → Fin j → ℂ, ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) =
      ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) *
        ENNReal.ofReal ((‖(Matrix.of (L x)).det‖ ^ 2)⁻¹ ^ j) := by
    intro x
    rw [← ENNReal.ofReal_mul hD.le]
    congr 1
    rw [show Matrix.of (L x) = a * Matrix.of x * b from rfl, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
    have hP : (‖a.det‖ ^ 2) ^ j * ((‖a.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hA))
    have hQ : (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hB))
    rw [mul_pow, mul_pow, mul_inv, mul_inv, mul_pow, mul_pow, inv_pow (‖a.det‖ ^ 2), inv_pow (‖b.det‖ ^ 2),
      pow_mul, pow_mul]
    linear_combination (-((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹)) * hP
      - (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * hQ
  unfold haarLoc
  exact measurePreserving_withDensity volume L.continuous_of_finiteDimensional.measurable hρ hcd hμ hρf

end GlobalTheory.HaarMul
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary : ∀ (k r : ℕ), chart k r 0 = 1 ∧ ContinuousOn (chart k r) (Metric.ball 0 1) ∧ ∀ i j, ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧ ∀ v, D v = dchart k r v i j := by
  first | exact @GlobalTheory.CellDens.Deriv.chart_strict | exact GlobalTheory.CellDens.Deriv.chart_strict | (intros; apply GlobalTheory.CellDens.Deriv.chart_strict <;> assumption)
end
