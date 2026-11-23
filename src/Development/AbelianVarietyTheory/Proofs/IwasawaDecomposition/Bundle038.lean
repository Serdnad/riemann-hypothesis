module

public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle010
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvr
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataCD
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

@[expose] public section

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaLebExists

theorem J_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

end GlobalTheory.OmegaLebExists
end
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem finiteDimensional_eigenspace_sum_sq_invariantFields : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  intro K _ _ _ _ _ L _ _ _ S hS e he he0 hU d hadd hsmul hder ι _ X hX lam
  classical
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  set μ : Measure K := haarProb K with hμ
  have hc : ∀ f : S, Continuous f.1 := fun f => hS f.1 f.2
  have hint : ∀ {F : Type} [NormedAddCommGroup F] {g : K → F}, Continuous g → Integrable g μ :=
    fun hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : ∀ f g : S, Integrable (fun x => (starRingEnd ℂ) (f.1 x) * g.1 x) μ :=
    fun f g => hint ((Complex.continuous_conj.comp (hc f)).mul (hc g))

  have hskew : ∀ (Y : L) (f : S), ((∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ) +
      ∫ x, (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x ∂μ = 0 := by
    intro Y f
    have c1 : Continuous fun x => (starRingEnd ℂ) (f.1 x) :=
      Complex.continuous_conj.comp (hc f)
    have c2 : Continuous fun x => (starRingEnd ℂ) ((d Y f).1 x) :=
      Complex.continuous_conj.comp (hc _)
    have h := (GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
      (fun x => (starRingEnd ℂ) (f.1 x) * (d Y f).1 x)
      (fun x => (starRingEnd ℂ) ((d Y f).1 x) * (d Y f).1 x
        + (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x)
      (c1.mul (hc _)) ((c2.mul (hc _)).add (c1.mul (hc _)))
      (fun x t => (hder Y f x t).star.mul (hder Y (d Y f) x t))).2
    rw [integral_add (hi2 _ _) (hi2 _ _)] at h
    rw [← h, ← integral_complex_ofReal]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  have hsum : ∀ f : S, f ∈ Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam →
      ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ ≤ ‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by
    intro f hf
    rw [Module.End.mem_eigenspace_iff] at hf
    have h1 : ∑ i, ∫ x, (starRingEnd ℂ) (f.1 x) * (d (X i) (d (X i) f)).1 x ∂μ
        = lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_finsetSum _ (fun i _ => hi2 _ _), ← integral_complex_ofReal,
        ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have h2 := congrArg (fun g : S => g.1 x) hf
      simp only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h2
      simp only
      rw [← Finset.mul_sum, h2, mul_left_comm, Complex.conj_mul']
      simp
    have h3 : ((∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ)
        = - (lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ)) := by
      rw [← h1, Complex.ofReal_sum, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => hskew _ _
    have h4 := congrArg norm h3
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (a := ∫ x, ‖f.1 x‖ ^ 2 ∂μ)
        (integral_nonneg fun x => by positivity)] at h4
    rw [← h4]
    exact le_abs_self _
  obtain ⟨a, ha⟩ := (Fintype.linearCombination ℝ X).exists_rightInverse_of_surjective
    (by rw [Fintype.range_linearCombination, hX])
  have hac : Continuous a := a.continuous_of_finiteDimensional
  have hd0 : d 0 = 0 := by
    have := hsmul 0 0
    simpa using this
  have hdY : ∀ Y, d Y = ∑ i, ((a Y i : ℝ) : ℂ) • d (X i) := by
    intro Y
    have h1 : Y = ∑ i, a Y i • X i := by
      have := LinearMap.congr_fun ha Y
      simpa [Fintype.linearCombination_apply] using this.symm
    let D : L →+ Module.End ℂ S := ⟨⟨d, hd0⟩, hadd⟩
    calc d Y = D (∑ i, a Y i • X i) := congrArg d h1
      _ = ∑ i, D (a Y i • X i) := map_sum D _ _
      _ = _ := Finset.sum_congr rfl fun i _ => hsmul _ _
  have hbound : ∀ (Y : L) (f : S), ∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ ≤
      (∑ i, (a Y i) ^ 2) * ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ := by
    intro Y f
    have ci : ∀ g : S, Continuous fun x => ‖g.1 x‖ ^ 2 := fun g => (hc g).norm.pow 2
    rw [← integral_finsetSum _ (fun i _ => hint (ci _)), ← integral_const_mul]
    refine integral_mono (hint (ci _))
      (hint (continuous_const.mul (continuous_finsetSum _ fun i _ => ci _))) fun x => ?_
    have h1 : ‖(d Y f).1 x‖ ≤ ∑ i, |a Y i| * ‖(d (X i) f).1 x‖ := by
      rw [hdY Y]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a Y i|)
      (fun i => ‖(d (X i) f).1 x‖)
    simp only [sq_abs] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hcont : Continuous fun Y : L => (∑ i, (a Y i) ^ 2) * ‖lam‖ := by fun_prop
  have hev : ∀ᶠ Y in 𝓝 (0 : L), (∑ i, (a Y i) ^ 2) * ‖lam‖ < 1 / 4 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hfin := GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt K μ
    ((Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam).map S.subtype)
    (by rintro _ ⟨f, -, rfl⟩; exact hc f) _ (hU r hr) (by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨Y, hY, rfl⟩
      have h := (GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
        f.1 (d Y f).1 (hc _) (hc _) (hder Y f)).1
      simp only [one_smul] at h
      have hn : 0 ≤ ∫ x, ‖f.1 x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
      have hs : 0 ≤ ∑ i, (a Y i) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
      calc _ ≤ _ := h
        _ ≤ _ := hbound Y f
        _ ≤ (∑ i, (a Y i) ^ 2) * (‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left (hsum f hf) hs
        _ = ((∑ i, (a Y i) ^ 2) * ‖lam‖) * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hball Y hY).le hn)
  exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective _).symm.finiteDimensional

end GlobalTheory
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.ExpBallSandwich

section Matrices
variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def sumAbs (M : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

omit [DecidableEq n] in
theorem sumAbs_nonneg (M : Matrix n n ℂ) : 0 ≤ sumAbs M := by
  unfold sumAbs; positivity

omit [DecidableEq n] in
theorem sumAbs_add_le (A B : Matrix n n ℂ) : sumAbs (A + B) ≤ sumAbs A + sumAbs B := by
  unfold sumAbs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

omit [DecidableEq n] in
theorem sumAbs_neg (A : Matrix n n ℂ) : sumAbs (-A) = sumAbs A := by
  simp [sumAbs]

omit [DecidableEq n] in
theorem sumAbs_mul_le (A B : Matrix n n ℂ) : sumAbs (A * B) ≤ sumAbs A * sumAbs B := by
  first
  | exact @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | (apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le ..)

section Op
open scoped Matrix.Norms.Operator

theorem row_le_op (M : Matrix n n ℂ) (i : n) : ∑ j, ‖M i j‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have := Finset.le_sup (f := fun i : n => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ _ := NNReal.coe_le_coe.2 this
  simpa using h2

theorem op_le_sumAbs (M : Matrix n n ℂ) : ‖M‖ ≤ sumAbs M := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : n => ∑ j, ‖M i j‖₊) ≤ ∑ i, ∑ j, ‖M i j‖₊ :=
    Finset.sup_le fun i _ => Finset.single_le_sum (f := fun l => ∑ j, ‖M l j‖₊)
          (fun l _ => by positivity) (Finset.mem_univ i)
  have h2 := NNReal.coe_le_coe.2 this
  simpa [sumAbs] using h2

theorem sumAbs_le_op (M : Matrix n n ℂ) : sumAbs M ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  unfold sumAbs
  calc _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum fun i _ => row_le_op M i
    _ = _ := by simp

theorem exp_strict (η : ℝ) (hη : 0 < η) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ A B : Matrix n n ℂ,
    sumAbs A < ρ → sumAbs B < ρ →
    sumAbs (NormedSpace.exp A - NormedSpace.exp B - (A - B)) ≤ η * sumAbs (A - B) := by
  have h := (hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)).isLittleO
  have hc : 0 < η / ((Fintype.card n : ℝ) + 1) := by positivity
  have h2 := h.def hc
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ρ, hρ, h3⟩ := h2
  refine ⟨ρ, hρ, fun A B hA hB => ?_⟩
  have h4 := @h3 (A, B) (by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt ((op_le_sumAbs A).trans_lt hA) ((op_le_sumAbs B).trans_lt hB))
  simp only [ContinuousLinearMap.one_apply] at h4
  have h5 := op_le_sumAbs (A - B)
  have h6 := sumAbs_nonneg (A - B)
  calc _ ≤ _ := sumAbs_le_op _
    _ ≤ (Fintype.card n : ℝ) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        refine mul_le_mul_of_nonneg_left (h4.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h5 hc.le
    _ ≤ ((Fintype.card n : ℝ) + 1) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        gcongr; linarith
    _ = _ := by field_simp

end Op

theorem defect_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ X Y Z : Matrix n n ℂ,
    sumAbs X < ρ → sumAbs Y < ρ → sumAbs Z < ρ →
    NormedSpace.exp Y = NormedSpace.exp X * NormedSpace.exp Z →
    sumAbs (Y - X - Z) ≤ η * sumAbs (Y - X) + 3 * η * sumAbs Z := by
  obtain ⟨ρ, hρ, h⟩ := exp_strict (n := n) η hη
  refine ⟨min ρ (η / 2), by positivity, fun X Y Z hX hY hZ he => ?_⟩
  rw [lt_min_iff] at hX hY hZ
  have h0 : sumAbs (0 : Matrix n n ℂ) < ρ := by simpa [sumAbs] using hρ
  have key : ∀ W : Matrix n n ℂ, sumAbs W < ρ →
      sumAbs (NormedSpace.exp W - 1 - W) ≤ η * sumAbs W ∧
      sumAbs (NormedSpace.exp W - 1) ≤ 2 * sumAbs W := by
    intro W hW
    have h1 := h W 0 hW h0
    rw [NormedSpace.exp_zero, sub_zero] at h1
    refine ⟨h1, ?_⟩
    have h2 := sumAbs_add_le (NormedSpace.exp W - 1 - W) W
    rw [sub_add_cancel] at h2
    have := sumAbs_nonneg W
    nlinarith
  have e : Y - X - Z = -(NormedSpace.exp Y - NormedSpace.exp X - (Y - X)) +
      ((NormedSpace.exp Z - 1 - Z) + (NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) := by
    rw [he]; noncomm_ring
  have a1 := h Y X hY.1 hX.1
  have a2 := (key Z hZ.1).1
  have a3 := (key Z hZ.1).2
  have a4 : sumAbs (NormedSpace.exp X - 1) ≤ η := by linarith [(key X hX.1).2, hX.2]
  have a5 : sumAbs ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) ≤ η * (2 * sumAbs Z) :=
    (sumAbs_mul_le _ _).trans (mul_le_mul a4 a3 (sumAbs_nonneg _) hη.le)
  rw [e]
  refine (sumAbs_add_le _ _).trans ?_
  rw [sumAbs_neg]
  have a6 := sumAbs_add_le (NormedSpace.exp Z - 1 - Z)
    ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1))
  linarith

end Matrices

end GlobalTheory.ExpBallSandwich
end

section

open Metric Filter Topology Set

noncomputable section

namespace GlobalTheory

def updCLM (n : ℕ) (k : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = k then ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ
    else (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)

theorem updCLM_apply (n : ℕ) (k : Fin n) (p : (Fin n → ℂ) × ℂ) :
    updCLM n k p = Function.update p.1 k p.2 := by
  funext i
  simp only [updCLM, ContinuousLinearMap.pi_apply, Function.update_apply]
  split_ifs <;> simp

theorem cauchyCoord_differentiableAt :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ),
      0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U →
      DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} →
      DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  intro n U k f z₀ r hr hz₀ hU hball hf
  set V : Set (Fin n → ℂ) := {z | z ∈ U ∧ z k ≠ 0} with hVdef
  have hV : IsOpen V := hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  have hfa : AnalyticOnNhd ℂ f V := ReciprocityTheory.AnForm.Osgood.osgood n V f hV hf
  set Φ : (Fin n → ℂ) × ℂ → ℂ := fun p => (p.2 - p.1 k)⁻¹ • f (Function.update p.1 k p.2) with hΦdef
  set Wd : Set ((Fin n → ℂ) × ℂ) := {p | Function.update p.1 k p.2 ∈ V ∧ p.2 - p.1 k ≠ 0} with hWdef
  have hupd : Continuous fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2 :=
    continuous_fst.update k continuous_snd
  have hWo : IsOpen Wd :=
    (hV.preimage hupd).inter (isOpen_ne_fun (continuous_snd.sub ((continuous_apply k).comp continuous_fst))
      continuous_const)
  have hΦa : AnalyticOnNhd ℂ Φ Wd := by
    intro p hp
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) p := by
      have he : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) = updCLM n k :=
        funext fun p => (updCLM_apply n k p).symm
      rw [he]; exact (updCLM n k).analyticAt p
    have h2 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => f (Function.update p.1 k p.2)) p :=
      AnalyticAt.comp (g := f) (f := fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) (hfa _ hp.1) h1
    have h3 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 k) p :=
      analyticAt_snd.sub (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt _).comp
        analyticAt_fst)
    exact (h3.inv hp.2).smul h2
  have hΦc : ContinuousOn Φ Wd := hΦa.continuousOn
  have hD : ContinuousOn (fun p => fderiv ℂ Φ p) Wd :=
    (hΦa.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hWo le_rfl

  set K : Set ((Fin n → ℂ) × ℂ) := closedBall z₀ (r / 2) ×ˢ sphere (0 : ℂ) r
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKW : K ⊆ Wd := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [mem_closedBall, mem_sphere_iff_norm, sub_zero] at hz ht
    have hzk : ‖z k‖ ≤ r / 2 := by
      have := dist_le_pi_dist z z₀ k
      rw [hz₀, dist_zero_right] at this
      linarith [this]
    refine ⟨⟨hball ?_, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_pi_le_iff hr.le]
      intro i
      by_cases hi : i = k
      · subst hi; simp [hz₀, ht]
      · rw [Function.update_of_ne hi]
        exact (dist_le_pi_dist z z₀ i).trans (by linarith)
    · simp only [Function.update_self]
      intro h; rw [h, norm_zero] at ht; linarith
    · intro h
      have : t = z k := sub_eq_zero.mp h
      rw [this] at ht; linarith
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hD.mono hKW)
  have hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ => circleMap_mem_sphere 0 hr.le θ
  have hmemW : ∀ z ∈ closedBall z₀ (r / 2), ∀ θ : ℝ, (z, circleMap 0 r θ) ∈ Wd := fun z hz θ =>
    hKW ⟨hz, hcirc θ⟩
  have hderc : Continuous fun θ => deriv (circleMap 0 r) θ := by
    have : (fun θ => deriv (circleMap 0 r) θ) = fun θ => circleMap 0 r θ * Complex.I :=
      funext fun θ => deriv_circleMap 0 r θ
    rw [this]; exact (continuous_circleMap 0 r).mul continuous_const
  have hpath : ∀ z : Fin n → ℂ, Continuous fun θ : ℝ => (z, circleMap 0 r θ) := fun z =>
    continuous_const.prodMk (continuous_circleMap 0 r)
  have hr2 : 0 < r / 2 := half_pos hr
  set F : (Fin n → ℂ) → ℝ → ℂ := fun z θ => deriv (circleMap 0 r) θ • Φ (z, circleMap 0 r θ)
  set F' : (Fin n → ℂ) → ℝ → (Fin n → ℂ) →L[ℂ] ℂ := fun z θ =>
    deriv (circleMap 0 r) θ • (fderiv ℂ Φ (z, circleMap 0 r θ)).comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ)
  have hFc : ∀ z ∈ closedBall z₀ (r / 2), Continuous (F z) := fun z hz =>
    hderc.smul (hΦc.comp_continuous (hpath z) (hmemW z hz))
  have hF'c : Continuous (F' z₀) :=
    hderc.smul ((hD.comp_continuous (hpath z₀) (hmemW z₀ (mem_closedBall_self hr2.le))).clm_comp
      continuous_const)
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (a := 0) (b := 2 * Real.pi) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun _ => r * (B * ‖ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ‖)) (ball_mem_nhds z₀ hr2)
    (eventually_of_mem (ball_mem_nhds z₀ hr2) fun z hz =>
      (hFc z (ball_subset_closedBall hz)).aestronglyMeasurable)
    ((hFc z₀ (mem_closedBall_self hr2.le)).intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      simp only [F', norm_smul]
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hB _ ⟨ball_subset_closedBall hz, hcirc θ⟩) (norm_nonneg _))) hr.le)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      have hd : DifferentiableAt ℂ Φ (z, circleMap 0 r θ) :=
        (hΦa _ (hmemW z (ball_subset_closedBall hz) θ)).differentiableAt
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℂ) z (circleMap 0 r θ))).const_smul
        (deriv (circleMap 0 r) θ))
  exact key.differentiableAt

end GlobalTheory
end
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.associated_prime_localization_dvr : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 → (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) → ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  first | exact @GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | exact GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient | (intros; apply GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.regular_local_ring_normal_domain : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | exact GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing <;> assumption)
end
