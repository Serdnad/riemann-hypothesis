module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle022
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Mathlib.Algebra.MvPolynomial.Eval
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle014
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombination
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle023
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

@[expose] public section

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.LowerAny

theorem sum_sub_succ (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc, Fin.castSucc_zero] at h ⊢
    rw [h, Fin.succ_last]
    simp

theorem sum_weight_lower {n : ℕ} (a d : Fin n → ℝ) (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hd : ∀ i, d i ≤ M) :
    -((∑ i, a i) * M) ≤ ∑ i, a i * (-d i) := by
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [mul_le_mul_of_nonneg_left (hd i) (ha i)]

theorem step_le {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {r : ℕ} (A : SatFlag E r)
    (μ : ℝ) (N : ℝ) (hμ : 0 ≤ μ) (hE : E.slopeMax ≤ (μ : EReal)) (hN : (r : ℝ) ≤ N) (i : Fin (r + 1)) :
    E.normDegree (A.F i) ≤ N * μ := by
  have h := GlobalTheory.T.normalized_degree_le_rank_mul_slope K E μ hE (A.F i)
  rw [A.rank i] at h
  have hi : ((i : ℕ) : ℝ) ≤ N := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) hN
  exact h.trans (mul_le_mul_of_nonneg_right hi hμ)

theorem term_lower {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ]
    (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ)
    (τ : Ψ) (hanti : Antitone (lam τ)) (hΛ : ∀ i, |lam τ i| ≤ Λ) (hμ : 0 ≤ μ)
    (hE : E.slopeMax ≤ (μ : EReal)) (hC : |A.flatDeg τ| ≤ C) :
    -(2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C) ≤
      (∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) *
          (-E.normDegree ((A.W τ).F i.succ.castSucc))) +
        (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) *
          (-E.normDegree (A.W τ).top) +
        (∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) *
          (-E.normDegree ((A.S τ).F i.rev.succ.castSucc))) -
        lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set N : ℝ := (j : ℝ) + 1 + ((k : ℝ) + 1) with hNdef
  have hNW : (((j + 1 : ℕ)) : ℝ) ≤ N := by push_cast; linarith
  have hNS : (((k + 1 : ℕ)) : ℝ) ≤ N := by push_cast; linarith
  have hN0 : 0 ≤ N := by linarith
  have hM : 0 ≤ N * μ := mul_nonneg hN0 hμ
  have hg : ∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) =
      lam τ (Fin.castAdd (k + 1) 0) - lam τ (Fin.castAdd (k + 1) (Fin.last j)) :=
    sum_sub_succ j (fun i => lam τ (Fin.castAdd (k + 1) i))
  have hh : ∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) =
      lam τ (Fin.natAdd (j + 1) 0) - lam τ (Fin.natAdd (j + 1) (Fin.last k)) :=
    sum_sub_succ k (fun i => lam τ (Fin.natAdd (j + 1) i))
  have h1 := sum_weight_lower
    (fun i : Fin j => lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ))
    (fun i : Fin j => E.normDegree ((A.W τ).F i.succ.castSucc)) (N * μ)
    (fun i => sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp)))
    (fun i => step_le (A.W τ) μ N hμ hE hNW _)
  have h3 := sum_weight_lower
    (fun i : Fin k => lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ))
    (fun i : Fin k => E.normDegree ((A.S τ).F i.rev.succ.castSucc)) (N * μ)
    (fun i => sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp)))
    (fun i => step_le (A.S τ) μ N hμ hE hNS _)
  rw [hg] at h1
  rw [hh] at h3
  have hb : 0 ≤ lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0) :=
    sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp))
  have htop : E.normDegree (A.W τ).top ≤ N * μ := step_le (A.W τ) μ N hμ hE hNW (Fin.last _)
  have h2 : -((lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) * (N * μ)) ≤
      (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) *
        (-E.normDegree (A.W τ).top) := by
    nlinarith [mul_le_mul_of_nonneg_left htop hb]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ (Fin.natAdd (j + 1) 0))
  have h4 : lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ ≤ Λ * C := by
    calc lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ
        ≤ |lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ| := le_abs_self _
      _ = |lam τ (Fin.natAdd (j + 1) 0)| * |A.flatDeg τ| := abs_mul _ _
      _ ≤ Λ * C := mul_le_mul (hΛ _) hC (abs_nonneg _) hΛ0
  have hfirst : lam τ (Fin.castAdd (k + 1) 0) ≤ Λ := (le_abs_self _).trans (hΛ _)
  have hlast : -Λ ≤ lam τ (Fin.natAdd (j + 1) (Fin.last k)) := (abs_le.mp (hΛ _)).1
  have h5 : (lam τ (Fin.castAdd (k + 1) 0) - lam τ (Fin.natAdd (j + 1) (Fin.last k))) * (N * μ) ≤
      (2 * Λ) * (N * μ) := mul_le_mul_of_nonneg_right (by linarith) hM
  have h6 : 2 * Λ * N * μ = (2 * Λ) * (N * μ) := by ring
  rw [h6]
  nlinarith [h1, h2, h3, h4, h5]

theorem lamDeg_lower : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ), (∀ τ, Antitone (lam τ)) → (∀ τ i, |lam τ i| ≤ Λ) → 0 ≤ μ → E.slopeMax ≤ (μ : EReal) → (∀ τ, |A.flatDeg τ| ≤ C) → -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C)) ≤ A.lamDeg lam := by
  intro K _ _ E Ψ _ j k A lam Λ μ C hanti hΛ hμ hE hC
  rw [GlobalTheory.CompanionTheory.Ar.Decomp.lamDeg_eq]
  calc -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C))
      = ∑ _τ : Ψ, -(2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_neg]
    _ ≤ _ := Finset.sum_le_sum fun τ _ =>
        term_lower E Ψ j k A lam Λ μ C τ (hanti τ) (hΛ τ) hμ hE (hC τ)

end GlobalTheory.CompanionTheory.Ar.LowerAny
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem pderiv_fin_prod {σ : Type*} (k : σ) : ∀ (d : ℕ) (f : Fin (d + 1) → MvPolynomial σ ℝ),
    pderiv k (∏ r, f r) = ∑ r, pderiv k (f r) * ∏ s, f (r.succAbove s) := by
  intro d
  induction d with
  | zero => intro f; simp
  | succ d ih =>
    intro f
    rw [Fin.prod_univ_succ, Derivation.leibniz, ih (fun i => f i.succ),
      Fin.sum_univ_succ (fun r => pderiv k (f r) * ∏ s, f (r.succAbove s))]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · simp only [Fin.succAbove_zero]
      ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [Fin.prod_univ_succ (fun s => f (r.succ.succAbove s))]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      ring

theorem pderiv_row_weight (c v : ℝ) : pderiv (some 0 : Option (Fin 2)) (rowW ![c, 0] v) = C c := by
  simp [rowW, pderiv_X, Pi.single_apply]

theorem eval_row_weight (n : Fin 3 → ℝ) (c v : ℝ) :
    evalW n n (rowW ![c, 0] v) = lin4 (fun i => c * n i) + C v * X none := by
  have h : lin4 (fun i => c * n i) = C c * lin4 n := by

    simp only [lin4, lin3, map_sum, map_mul, rename_C, rename_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  simp [rowW, evalW, aeval_def, algebraMap_eq]

theorem extract_one : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  intro d T H L hL c v n e
  have h1 := ((GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun r => (c r : ℂ) * e)
    (fun r => (∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))
  refine h1.trans ?_

  rw [pderiv_fin_prod, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h3 := hL (fun s i => c (r.succAbove s) * n i) (fun s => v (r.succAbove s))
  rw [h3, pderiv_row_weight, map_mul (evalW n n), map_prod (evalW n n)]
  simp only [eval_row_weight]
  have h4 : evalW n n (C (c r)) = C (c r) := by simp [evalW, aeval_def, algebraMap_eq]
  rw [h4, C_mul', map_smul, Complex.real_smul]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.complex_hessian_two_point_combination : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p₀ p₁ e₀ e₁ : ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) (s t v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p₀ y) → ContDiffAt ℝ 2 f (Fin.cons p₁ y) → ContDiffAt ℝ 2 α y →
    hessC f (Fin.cons p₀ y) = blk e₀ B₀ → hessC f (Fin.cons p₁ y) = blk e₁ B₁ →
    hessC (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z)))
      (Fin.cons p₀ (Fin.cons p₁ y)) =
    blk ((s : ℂ) * e₀) (blk ((t : ℂ) * e₁) ((s : ℂ) • B₀ + (t : ℂ) • B₁ + (v : ℂ) • hessC α y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square <;> assumption)
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.integral_normSq_mobD_mul_comp_mob' : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ → ℝ, ∫ a : ℂ, Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g a) = ∫ b : ℂ, f b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob <;> assumption)
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.analyticAt_mobius_det_jacobian_eq : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ), (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ), GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 → AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧ (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det = GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem oldPart_mem_mcPts {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨fun k => hu.1 (some k), fun f hf => ?_⟩
  have hg : glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
    funext ⟨o, i⟩
    cases o <;> rfl
  have h1 := hu.2 (inc f) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
  have h2 := eval_inc (basePart₂ u) (fun j => u ⟨none, j⟩) f
  rw [hg] at h2
  rw [← h2]
  exact h1

theorem exists_segre_eq_embL [Nonempty K] {p : ℕ} {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    {u : (Σ o, Tb ι o) → ℂ} (hu : u ∈ mcPts (twist p Q)) {v : Fin 2 → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hv : ∀ j : Fin 2, u ⟨none, j⟩ = c * v j) :
    ∃ z ∈ mcPts Q, segre u = embL v (segre z) := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, mcPts_smul hQ (fun k => if k = k0 then c else 1)
    (fun k => by by_cases h : k = k0 <;> simp [h, hc]) (oldPart_mem_mcPts hu), ?_⟩
  funext J
  show ∏ o, u ⟨o, J o⟩ =
    (∏ k, (if k = k0 then c else 1) * basePart₂ u ⟨k, J (some k)⟩) * v (J none)
  rw [Fintype.prod_option, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k0]
  have h1 : u ⟨none, J none⟩ = c * v (J none) := hv (J none)
  rw [h1]
  simp only [Finset.mem_univ, if_true]
  have h2 : ∀ k, basePart₂ u ⟨k, J (some k)⟩ = u ⟨some k, J (some k)⟩ := fun _ => rfl
  simp only [h2]
  ring

theorem new_coords {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ j : Fin 2, u ⟨none, j⟩ = c * vPlus p j) ∨
      (∀ j : Fin 2, u ⟨none, j⟩ = c * vMinus p j)) := by
  have hq : u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
    rw [← eval_quad]
    exact hu.2 _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hy : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    intro h0
    rw [h0] at hq
    have hx : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using hq
    obtain ⟨i, hi⟩ := hu.1 none
    have hall : ∀ j : Fin 2, u ⟨none, j⟩ = 0 := by
      intro j
      fin_cases j
      · exact hx
      · exact h0
    exact hi (hall i)
  refine ⟨u ⟨none, (1 : Fin 2)⟩, hy, ?_⟩
  have hf : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) = 0 := by
    have : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) =
        u ⟨none, (0 : Fin 2)⟩ ^ 2 - u ⟨none, (1 : Fin 2)⟩ ^ 2 * cRoot p ^ 2 := by ring
    rw [this, cRoot_sq, ← hq]
    ring
  rcases mul_eq_zero.mp hf with h | h
  · left
    intro j
    fin_cases j
    · simpa [vPlus] using sub_eq_zero.mp h
    · simp [vPlus]
  · right
    intro j
    fin_cases j
    · simpa [vMinus] using eq_neg_of_add_eq_zero_left h
    · simp [vMinus]

theorem embL_image_subset {e : ℕ} {p : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) :
    embL v '' fibre Q (pj v Ψ) y ⊆ fibre (twist p Q) Ψ y := by
  rintro _ ⟨w, ⟨z, hz, rfl, hΨ⟩, rfl⟩
  exact ⟨glue z v, glue_mem_mcPts hz hv hv1, segre_glue z v, hΨ⟩

theorem fibre_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (Q : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ),
    p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q →
    fibre (twist p Q) Ψ y =
      embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪
        embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  intro K _ ι _ p Q e Ψ y _ hK hQ
  refine Set.Subset.antisymm ?_ (Set.union_subset
    (embL_image_subset (vPlus_root p) (by simp [vPlus]))
    (embL_image_subset (vMinus_root p) (by simp [vMinus])))
  rintro w ⟨u, hu, rfl, hΨ⟩
  obtain ⟨c, hc, h | h⟩ := new_coords hu
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inl ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vPlus p) (segre z)) = _
    rw [← hs]
    exact hΨ
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inr ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vMinus p) (segre z)) = _
    rw [← hs]
    exact hΨ

end GlobalTheory.CompanionTheory.Ar.Tw.Fib
end
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Kext

theorem exists_algHom_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω) (E : Type) [CommRing E] [Algebra ℚ E] (u : σ → E),
      aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → aeval u G = 0) → IsUnit (aeval u F) →
      ∃ φ : S →ₐ[ℚ] E, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval τ G →
        φ s = aeval u G :=
  _root_.UpperTheory.Reformulated.B.Yde9.main

end GlobalTheory.CompanionTheory.Ar.Cmp.Kext
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.local_unitary_normal_frame_2x2 : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧ IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧ (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧ (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near <;> assumption)
end

section

open Complex Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_unit_extension_of_log_growth :
    ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ →
      DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} →
      (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → φ z ≠ 0 ∧
        ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N ∧
        ‖(φ z)⁻¹‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) →
      ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧
        (∀ z ∈ ball (0 : Fin n → ℂ) ρ, ψ z ≠ 0) ∧
        ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  intro n S φ ρ C N hρ hφ hb
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.T.removable_log_growth_singularity n S φ ρ C N hρ hφ (fun z hz hS => (hb z hz hS).2.1)
  obtain ⟨χ, hχ, hχe⟩ := GlobalTheory.T.removable_log_growth_singularity n S (fun z => (φ z)⁻¹) ρ C N hρ
    (hφ.inv fun z hz => (hb z hz.1 hz.2).1) (fun z hz hS => (hb z hz hS).2.2)
  refine ⟨ψ, hψ, fun z hz => ?_, hψe⟩
  have hF : ContinuousAt (fun w => ψ w * χ w) z :=
    ((hψ.mul hχ).differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ → (Fin n → ℂ),
      w = fun (ε : ℝ) i => if z i = 0 then (ε : ℂ) else z i := ⟨_, rfl⟩
  have hwc : Continuous w := by
    rw [hw_def]
    refine continuous_pi fun i => ?_
    by_cases h : z i = 0
    · simp only [h, if_true]
      exact continuous_ofReal
    · simp only [h, if_false]
      exact continuous_const
  have hw0 : w 0 = z := funext fun i => by by_cases h : z i = 0 <;> simp [hw_def, h]
  have hlim : Filter.Tendsto w (nhdsWithin 0 {0}ᶜ) (nhds z) := by
    rw [← hw0]
    exact hwc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ, ψ (w ε) * χ (w ε) = 1 := by
    have h1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ, w ε ∈ ball (0 : Fin n → ℂ) ρ :=
      hlim (isOpen_ball.mem_nhds hz)
    filter_upwards [h1, self_mem_nhdsWithin] with ε hε hε0
    have hS : ∀ i ∈ S, w ε i ≠ 0 := by
      intro i _
      by_cases h : z i = 0
      · simp only [hw_def, h, if_true]
        exact Complex.ofReal_ne_zero.2 hε0
      · simp only [hw_def, h, if_false]
        exact h
    rw [hψe _ hε hS, hχe _ hε hS]
    exact mul_inv_cancel₀ (hb _ hε hS).1
  have h2 : Filter.Tendsto (fun ε => ψ (w ε) * χ (w ε)) (nhdsWithin 0 {0}ᶜ) (nhds (ψ z * χ z)) :=
    hF.tendsto.comp hlim
  have h3 : ψ z * χ z = 1 :=
    tendsto_nhds_unique h2 (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  exact left_ne_zero_of_mul_eq_one h3

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gram_det_log_size : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m :=
  PositivityTheory.Xgp.t_gram_size

end GlobalTheory.CompanionTheory.Ar.PB
end
