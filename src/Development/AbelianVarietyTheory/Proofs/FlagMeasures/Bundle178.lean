module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle156
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Order.Sigma
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.BlockGS

theorem exists_coeff_of_mem_span {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (g : ι → V) (s : Set ι) (v : V) (hv : v ∈ Submodule.span ℂ (g '' s)) :
    ∃ c : ι → ℂ, (∀ y, y ∉ s → c y = 0) ∧ v = ∑ y, c y • g y := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hv
  refine ⟨l, fun y hy => ?_, ?_⟩
  · by_contra h
    exact hy (hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp

theorem exists_orthonormal_triangular {ι V : Type} [Fintype ι] [LinearOrder ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : ι → V) (hf : LinearIndependent ℂ f) :
    ∃ (g : ι → V) (P Q : ι → ι → ℂ), Orthonormal ℂ g ∧ (∀ y x, x < y → P y x = 0 ∧ Q y x = 0) ∧
      (∀ x, f x = ∑ y, P y x • g y) ∧ ∀ x, g x = ∑ y, Q y x • f y := by
  classical
  let _ : LocallyFiniteOrderBot ι := LocallyFiniteOrderBot.ofIic ι (fun x => Finset.univ.filter (· ≤ x)) (by simp)
  have : WellFoundedLT ι := Finite.to_wellFoundedLT
  have hs : ∀ x, Submodule.span ℂ (InnerProductSpace.gramSchmidtNormed ℂ f '' Set.Iic x)
      = Submodule.span ℂ (f '' Set.Iic x) := fun x => by
    rw [InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic]
  have h1 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      f x = ∑ y, c y • InnerProductSpace.gramSchmidtNormed ℂ f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  have h2 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      InnerProductSpace.gramSchmidtNormed ℂ f x = ∑ y, c y • f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [← hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  choose P hP hP' using h1
  choose Q hQ hQ' using h2
  exact ⟨_, fun y x => P x y, fun y x => Q x y, InnerProductSpace.gramSchmidtNormed_orthonormal hf,
    fun y x h => ⟨hP x y (not_le.2 h), hQ x y (not_le.2 h)⟩, hP', hQ'⟩

theorem linearIndependent_columns (n a : ℕ) (j : Fin a → ℕ)
    (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ)
    (h1 : ∀ i, C i * A i = 1) (h0 : ∀ i k, i ≠ k → C i * A k = 0) :
    LinearIndependent ℂ (fun x : (Σ i, Fin (j i)) =>
      (WithLp.toLp 2 (fun r => A x.1 r x.2) : EuclideanSpace ℂ (Fin n))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨i, u⟩
  have hr : ∀ r, ∑ x : (Σ i, Fin (j i)), c x * A x.1 r x.2 = 0 := fun r => by
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) hc
    simpa using this
  have h : ∑ x : (Σ i, Fin (j i)), c x * (C i * A x.1) u x.2 = 0 := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    have := congrArg (fun z => C i u r * z) (hr r)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Fintype.sum_sigma, Finset.sum_eq_single i] at h
  · simpa [h1, Matrix.one_apply] using h
  · intro k _ hk
    simp [h0 i k hk.symm]
  · simp

theorem block_gramSchmidt : ∀ (n a : ℕ) (j : Fin a → ℕ) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ), (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → ∃ (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ), (∀ i, (B i)ᴴ * B i = 1) ∧ (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) ∧ (∀ k i, i < k → p k i = 0 ∧ q k i = 0) ∧ (∀ i, A i = ∑ k, B k * p k i) ∧ (∀ i, B i = ∑ k, A k * q k i) ∧ ∀ i, p i i * q i i = 1 := by
  classical
  intro n a j A C h1 h0
  let _ : LinearOrder (Σ i, Fin (j i)) := inferInstanceAs (LinearOrder (Σₗ i, Fin (j i)))
  obtain ⟨g, P, Q, hg, htri, hf, hg'⟩ :=
    exists_orthonormal_triangular _ (linearIndependent_columns n a j A C h1 h0)
  let B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ := fun i => Matrix.of fun r u => g ⟨i, u⟩ r
  let p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => P ⟨k, v⟩ ⟨i, u⟩
  let q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => Q ⟨k, v⟩ ⟨i, u⟩
  have hBB : ∀ i k u v, ((B i)ᴴ * B k) u v = inner ℂ (g ⟨i, u⟩) (g ⟨k, v⟩) := by
    intro i k u v
    simp [B, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have e1 : ∀ i, (B i)ᴴ * B i = 1 := by
    intro i
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg, Matrix.one_apply]
    simp
  have e2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0 := by
    intro i k h
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg]
    simp [h]
  have e3 : ∀ k i, i < k → p k i = 0 ∧ q k i = 0 := by
    intro k i h
    constructor <;> ext v u
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).1
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).2
  have e4 : ∀ i, A i = ∑ k, B k * p k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hf ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, p, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  have e5 : ∀ i, B i = ∑ k, A k * q k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hg' ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, q, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  refine ⟨B, p, q, e1, e2, e3, e4, e5, fun i => ?_⟩
  have hp : ∀ k, (B i)ᴴ * A k = p i k := by
    intro k
    rw [e4 k, Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
    · intro l _ hl
      rw [← Matrix.mul_assoc, e2 i l hl.symm, Matrix.zero_mul]
    · simp
  have h : (B i)ᴴ * (∑ k, A k * q k i) = 1 := by rw [← e5, e1]
  rw [Matrix.mul_sum, Finset.sum_eq_single i] at h
  · rw [← h, ← Matrix.mul_assoc, hp]
  · intro l _ hl
    rw [← Matrix.mul_assoc, hp]
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [(e3 i l hl).1, Matrix.zero_mul]
    · rw [(e3 l i hl).2, Matrix.mul_zero]
  · simp

end GlobalTheory.LeviIso.BlockGS
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem smallBall_pi_fin (n : ℕ) : ∀ (X : Fin n → Type) [∀ i, MeasurableSpace (X i)]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : Fin n → ℕ)
    (C : Fin n → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < C i) →
    (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (C i) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) →
    Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, ρ i (x i)) ≤ r} /
        ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (∏ i, C i) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  induction n with
  | zero =>
    intro X _ ν _ ρ d C _ _ _ _
    have hball : ∀ m : ℕ, m = 0 →
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) = 1 := by
      rintro m rfl
      rw [volume_euclideanSpace_eq_dirac]
      exact Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)
    rw [hball _ (Fin.sum_univ_zero d), Fin.prod_univ_zero, ENNReal.ofReal_one, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    have hset : {x : ∀ i : Fin 0, X i | Real.sqrt (∑ i, ρ i (x i)) ≤ r} = Set.univ := by
      ext x
      simp [hr']
    rw [hset, Measure.pi_univ]
    simp
  | succ n ih =>
    intro X _ ν _ ρ d C hρm hρ0 hC h
    have hmp := measurePreserving_piFinSuccAbove ν 0
    have h2 := ih (fun j => X (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
      (fun j => ρ (Fin.succAbove 0 j)) (fun j => d (Fin.succAbove 0 j))
      (fun j => C (Fin.succAbove 0 j)) (fun j => hρm _) (fun j => hρ0 _) (fun j => hC _)
      (fun j => h _)
    have hmeas2 : Measurable fun y : (∀ j : Fin n, X (Fin.succAbove 0 j)) =>
        ∑ j, ρ (Fin.succAbove 0 j) (y j) :=
      Finset.measurable_sum _ fun j _ => (hρm _).comp (measurable_pi_apply j)
    have key := GlobalTheory.T.tendsto_prod_smallBall_asymptotics (X 0) (∀ j : Fin n, X (Fin.succAbove 0 j)) (ν 0)
      (Measure.pi fun j => ν (Fin.succAbove 0 j)) (ρ 0)
      (fun y => ∑ j, ρ (Fin.succAbove 0 j) (y j)) (d 0) (∑ j, d (Fin.succAbove 0 j))
      (C 0) (∏ j, C (Fin.succAbove 0 j)) (hρm 0) hmeas2 (hρ0 0)
      (fun y => Finset.sum_nonneg fun j _ => hρ0 _ _) (hC 0)
      (Finset.prod_pos fun j _ => hC _) (h 0) h2
    have hsumd : d 0 + ∑ j, d (Fin.succAbove 0 j) = ∑ i, d i :=
      (Fin.sum_univ_succAbove d 0).symm
    have hprodC : C 0 * ∏ j, C (Fin.succAbove 0 j) = ∏ i, C i :=
      (Fin.prod_univ_succAbove C 0).symm
    rw [hsumd, hprodC] at key
    refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
    congr 1
    rw [← hmp.measure_preimage_equiv]
    congr 1
    ext x
    change Real.sqrt (ρ 0 (x 0) + ∑ j, ρ (Fin.succAbove 0 j) (x (Fin.succAbove 0 j))) ≤ r ↔
      Real.sqrt (∑ i, ρ i (x i)) ≤ r
    rw [Fin.sum_univ_succAbove (fun i => ρ i (x i)) 0]

theorem smallBall_weight {X : Type} [MeasurableSpace X] (ν : Measure X) (ρ : X → ℝ) (d : ℕ)
    (w : ℝ) (hw : 0 < w) (V : ENNReal)
    (h : Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds V)) :
    Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (w * ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (w ^ (-((d : ℝ) / 2))) * V)) := by
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hmap : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhds 0)
          (nhds (0 / Real.sqrt w)) := (continuous_id.div_const _).tendsto 0
      rw [zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hs
  have key := ENNReal.Tendsto.mul_const (h.comp hmap)
    (b := ENNReal.ofReal (w ^ (-((d : ℝ) / 2)))) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_comm]
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hrs : 0 < r / Real.sqrt w := div_pos hr' hs
  have hset : {x | Real.sqrt (w * ρ x) ≤ r} = {x | Real.sqrt (ρ x) ≤ r / Real.sqrt w} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.sqrt_mul hw.le, le_div_iff₀' hs]
  have hc : w ^ (-((d : ℝ) / 2)) = (Real.sqrt w ^ d)⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    congr 2
    ring
  have hrd : r ^ d = (r / Real.sqrt w) ^ d * Real.sqrt w ^ d := by
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ hs.ne'
  have ha0 : ENNReal.ofReal ((r / Real.sqrt w) ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hrs d
  simp only [Function.comp_apply]
  rw [hset, hc, hrd, ENNReal.ofReal_mul (pow_nonneg hrs.le d),
    ENNReal.ofReal_inv_of_pos (pow_pos hs d)]
  simp only [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top)]
  ring

theorem smallBall_pi_weight : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : ι → ℕ) (w : ι → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < w i) → (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) → Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, w i * ρ i (x i)) ≤ r} / ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (∏ i, w i ^ (-((d i : ℝ) / 2))) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  intro ι _ X _ ν _ ρ d w hρm hρ0 hw h
  have hw' : ∀ i, Filter.Tendsto
      (fun r : ℝ => ν i {x | Real.sqrt (w i * ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (w i ^ (-((d i : ℝ) / 2))) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1))) :=
    fun i => smallBall_weight (ν i) (ρ i) (d i) (w i) (hw i) _ (h i)
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have key := smallBall_pi_fin (Fintype.card ι) (fun j => X (f j)) (fun j => ν (f j))
    (fun j x => w (f j) * ρ (f j) x) (fun j => d (f j))
    (fun j => w (f j) ^ (-((d (f j) : ℝ) / 2))) (fun j => (hρm _).const_mul _)
    (fun j x => mul_nonneg (hw _).le (hρ0 _ x)) (fun j => Real.rpow_pos_of_pos (hw _) _)
    (fun j => hw' _)
  have hS : ∑ j, d (f j) = ∑ i, d i := Equiv.sum_comp f d
  have hP : ∏ j, w (f j) ^ (-((d (f j) : ℝ) / 2)) = ∏ i, w i ^ (-((d i : ℝ) / 2)) :=
    Equiv.prod_comp f (fun i => w i ^ (-((d i : ℝ) / 2)))
  rw [hS, hP] at key
  have hmp := measurePreserving_piCongrLeft ν f
  refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
  congr 1
  rw [← hmp.measure_preimage_equiv]
  congr 1
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hsum : ∑ i, w i * ρ i (MeasurableEquiv.piCongrLeft X f g i) =
      ∑ j, w (f j) * ρ (f j) (g j) := by
    rw [← Equiv.sum_comp f (fun i => w i * ρ i (MeasurableEquiv.piCongrLeft X f g i))]
    simp only [MeasurableEquiv.piCongrLeft_apply_apply]
  rw [hsum]

end GlobalTheory
end
