module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.HsLe

theorem hs_toMK_sub_one_le {n : ℕ} (ε : Fin n → Bool) (k : KG ε) :
    Formalism.REAL.hs (toMK k - 1) ≤ 4 * (n : ℝ) := by
  have hu : toMK k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := k.2.1
  have hcol : ∀ j : Fin n, ∑ i, ‖toMK k i j‖ ^ 2 = 1 := by
    intro j
    have hm : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
    have h1 : (star (toMK k) * toMK k) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by rw [hm]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ((∑ i, ‖toMK k i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.star_apply, ← Complex.conj_mul']
      rfl
    exact_mod_cast h2
  have hsum : ∑ i, ∑ j, ‖toMK k i j‖ ^ 2 = (n : ℝ) := by
    rw [Finset.sum_comm]
    simp [hcol]
  have hone : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = (n : ℝ) := by
    have : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have key : ∀ a b : ℂ, ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have h := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  unfold Formalism.REAL.hs
  calc ∑ i, ∑ j, ‖(toMK k - 1) i j‖ ^ 2
      ≤ ∑ i, ∑ j, (2 * ‖toMK k i j‖ ^ 2 + 2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.sub_apply]
        exact key _ _
    _ = 2 * ∑ i, ∑ j, ‖toMK k i j‖ ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 4 * (n : ℝ) := by rw [hsum, hone]; ring

end GlobalTheory.HsLe
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory

theorem hs_toMK_sub_one {n : ℕ} (ε : Fin n → Bool) (k : KG ε) :
    Formalism.REAL.hs (toMK k - 1) = 2 * (n : ℝ) - 2 * (Matrix.trace (toMK k)).re := by
  have hu : star (toMK k) * toMK k = 1 := Unitary.star_mul_self_of_mem k.2.1
  have hcol : ∀ j, ∑ i, ‖toMK k i j‖ ^ 2 = (1 : ℝ) := by
    intro j
    have h := congrArg Complex.re (congrFun (congrFun hu j) j)
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Complex.re_sum, Complex.one_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  have hentry : ∀ i j, ‖(toMK k - 1) i j‖ ^ 2 =
      ‖toMK k i j‖ ^ 2 + (if i = j then 1 - 2 * (toMK k i j).re else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.sub_apply, Matrix.one_apply_eq, if_pos rfl, Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_sub]
      simp
      ring
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, if_neg hij, sub_zero, add_zero]
  unfold Formalism.REAL.hs
  simp_rw [hentry]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib, hcol]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Matrix.trace, Complex.re_sum]
  simp [Matrix.diag]
  ring

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section
namespace GlobalTheory.KFourier

theorem pairing_convolution_swap {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ)
    (he : Continuous e) (hq : Continuous q) (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : (muK ε).IsInvInvariant := ⟨(compact_haar_holds n ε).2.2.2⟩
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))

  have h1 : ∀ k' : KG ε, ∫ k, e k * g (k' * k) ∂(muK ε) = ∫ y, e (k'⁻¹ * y) * g y ∂(muK ε) := by
    intro k'
    have := integral_mul_left_eq_self (μ := muK ε) (fun y => e (k'⁻¹ * y) * g y) k'
    rw [← this]; simp [← mul_assoc]

  have h2 : ∀ y : KG ε, ∫ k', star (q k') * e (k'⁻¹ * y) ∂(muK ε) =
      ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) := by
    intro y
    have a := integral_inv_eq_self (fun x => star (q (y * x)) * e ((y * x)⁻¹ * y)) (muK ε)
    have b := integral_mul_left_eq_self (μ := muK ε) (fun k' => star (q k') * e (k'⁻¹ * y)) y
    rw [← b, ← a]
    congr 1; funext x
    rw [mul_comm]; congr 2; group
  have hcont : Continuous (fun p : KG ε × KG ε => star (q p.1) * e (p.1⁻¹ * p.2) * g p.2) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (k' y : KG ε) => star (q k') * e (k'⁻¹ * y) * g y)
      ((muK ε).prod (muK ε)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε)
      = ∫ k', ∫ y, star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) := by
        congr 1; funext k'
        rw [h1, ← integral_const_mul]
        congr 1; funext y; ring
    _ = ∫ y, ∫ k', star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) :=
        integral_integral_swap hint
    _ = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
        congr 1; funext y
        rw [← h2, ← integral_const_mul]
        congr 1; funext k'; ring

end GlobalTheory.KFourier
end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.hilbertSchmidt_compactUnitary_sub_one_eq_trace : ∀ {n : ℕ} (ε : Fin n → Bool) (k : KG ε), Formalism.REAL.hs (toMK k - 1) = 2 * (n : ℝ) - 2 * (Matrix.trace (toMK k)).re := by
  first | exact @GlobalTheory.hs_toMK_sub_one | exact GlobalTheory.hs_toMK_sub_one | (intros; apply GlobalTheory.hs_toMK_sub_one <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.hilbertSchmidt_compactUnitary_sub_one_le_four_mul : ∀ {n : ℕ} (ε : Fin n → Bool) (k : KG ε), Formalism.REAL.hs (toMK k - 1) ≤ 4 * (n : ℝ) := by
  first | exact @GlobalTheory.HsLe.hs_toMK_sub_one_le | exact GlobalTheory.HsLe.hs_toMK_sub_one_le | (intros; apply GlobalTheory.HsLe.hs_toMK_sub_one_le <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier


theorem _root_.GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap : ∀ {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ), Continuous e → Continuous q → Continuous g → ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.pairing_convolution_swap | exact GlobalTheory.KFourier.pairing_convolution_swap | (intros; apply GlobalTheory.KFourier.pairing_convolution_swap <;> assumption)

end
end
