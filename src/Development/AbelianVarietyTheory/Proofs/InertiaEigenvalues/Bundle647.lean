module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem linIndep_of_mutual_span_of_indep :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)),
      (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W),
        (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) →
        (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) →
        (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) →
        ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro R W _ _ act hmul hone ι _ _ b f hb hf hbf d hd
  letI : Module R W :=
    { smul := fun r w => act r w
      one_smul := hone
      mul_smul := fun r s w => hmul r s w
      smul_zero := fun r => map_zero (act r)
      smul_add := fun r x y => map_add (act r) x y
      add_smul := fun r s w => by
        show act (r + s) w = act r w + act s w
        rw [map_add (f := _), AddMonoidHom.add_apply]
      zero_smul := fun w => by
        show act 0 w = 0
        rw [map_zero, AddMonoidHom.zero_apply] }
  have hs : ∀ (r : R) (w : W), act r w = r • w := fun _ _ => rfl
  simp only [hs] at hb hf hbf hd
  choose P hP using hf
  choose Q hQ using hbf
  have expand : ∀ c : ι → R,
      ∑ i, c i • f i = ∑ k, (Matrix.vecMul c (Matrix.of P)) k • b k := by
    intro c
    simp only [hP, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Matrix.of_apply,
      Finset.sum_smul]
    rw [Finset.sum_comm]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext k k'
    have h0 : ∑ k'', ((Matrix.vecMul (Q k) (Matrix.of P)) k'' - (1 : Matrix ι ι R) k k'') • b k''
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← expand, ← hQ, Matrix.one_apply,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    have := hb _ h0 k'
    rw [sub_eq_zero] at this
    rw [← this, Matrix.mul_apply]
    simp [Matrix.vecMul, dotProduct]
  have hPQ : Matrix.of P * Matrix.of Q = 1 := mul_eq_one_comm.mp hQP
  have he : Matrix.vecMul d (Matrix.of P) = 0 := by
    rw [expand] at hd
    funext k
    exact hb _ hd k
  have : d = 0 := by
    rw [← Matrix.vecMul_one d, ← hPQ, ← Matrix.vecMul_vecMul, he, Matrix.zero_vecMul]
  intro i
  rw [this]
  rfl

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem powerSeries_inv_coeff_norm_le_one :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) →
      ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1 := by
  intro K _ _ f hf hc
  have hc0 : constantCoeff f ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  refine ⟨f⁻¹, ?_, PowerSeries.mul_inv_cancel f hc0⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · rw [norm_inv, hc, inv_one]
    · rw [norm_mul, norm_neg, norm_inv, hc, inv_one, one_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x hx => ?_
      split_ifs with hlt
      · rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hlt)
      · rw [norm_zero]; exact zero_le_one

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.divided_difference_ideal_power_mem : ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u → q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B), (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  first | exact @GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | exact GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | (intros; apply GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow <;> assumption)
end
