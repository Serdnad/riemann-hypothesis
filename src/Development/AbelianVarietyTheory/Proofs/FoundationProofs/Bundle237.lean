module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle223
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle136
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle228
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory


open Formalism.MainNotions.GL3Theta in
theorem mulBy_integral_isClosed : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsClosed {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} := by
  intro p _ g
  set L : MvPowerSeries Unit ℂ_[p] := g.lg (GL3Theta.Xv ()) with hLdef
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by
    rw [hLdef, GL3Theta.G1.lg]
    exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _
      (GlobalTheory.GenusOneDatum.constantCoeff_flog _ _)
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have key : ∀ e : Unit →₀ ℕ, ∃ S : Finset ℕ, ∀ c : ℂ_[p],
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
        ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
    intro e
    have hfin := PowerSeries.coeff_subst_finite hL (PowerSeries.mk fun _ => (1 : ℂ_[p])) e
    have hfin' : (Function.support fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.mk fun _ => (1 : ℂ_[p])) • MvPowerSeries.coeff e (L ^ d)).Finite := hfin
    refine ⟨hfin'.toFinset, fun c => ?_⟩
    have ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * L) = 0 := by
      simp [hL0]
    have ha : PowerSeries.HasSubst (MvPowerSeries.C c * L) :=
      PowerSeries.HasSubst.of_constantCoeff_zero ha0
    show MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.C c * L) g.ex) = _
    rw [PowerSeries.coeff_subst ha]
    have hterm : ∀ d : ℕ, PowerSeries.coeff d g.ex • MvPowerSeries.coeff e ((MvPowerSeries.C c * L) ^ d) =
        PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
      intro d
      rw [mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, smul_eq_mul]
    simp_rw [hterm]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hd
    simp only [PowerSeries.coeff_mk, one_smul] at h0
    rw [h0, mul_zero, mul_zero]
  have hset : {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} =
      ⋂ e : Unit →₀ ℕ, {c : ℂ_[p] |
        ‖MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])‖ ≤ 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [hset]
  refine isClosed_iInter fun e => ?_
  obtain ⟨S, hS⟩ := key e
  have hfun : (fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])) =
      fun c => ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) :=
    funext hS
  have hcont : Continuous fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    rw [hfun]
    fun_prop
  exact isClosed_le (continuous_norm.comp hcont) continuous_const

end GlobalTheory
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_determinantIdeal_hermitianLattice_basis : ∀ (D : D7) (N N' r : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ x ∈ Y, ∀ y ∈ Y, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → (∀ i, ∃ s : ℕ, 0 < s ∧ (s : D.host.E) • b₀ i ∈ Y) → ∃ I : Submodule (𝓞 D.host.K) D.host.K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : D.host.K) * x ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧ ∀ (p : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p Y b → (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det ∈ I) ∧ ∀ x ∈ I, ∃ (s : ℕ) (c : 𝓞 D.host.K), Nat.Coprime s p ∧ (s : D.host.K) * x = (c : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det := by
  first | exact @GlobalTheory.NormSum.exists_detIdeal | exact GlobalTheory.NormSum.exists_detIdeal | (intros; apply GlobalTheory.NormSum.exists_detIdeal <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaFunction_selfDual_exists_eq_smul : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), 0 < area T.abelian₂ → DiscreteTopology A → (∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → ∀ F ∈ ThSp D T A, ∀ G ∈ ThSp D T A, G ≠ 0 → ∃ c : ℂ, F = c • G := by
  first | exact @GlobalTheory.ThetaCoordLine.exists_eq_smul | exact GlobalTheory.ThetaCoordLine.exists_eq_smul | (intros; apply GlobalTheory.ThetaCoordLine.exists_eq_smul <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.latticeCovolume_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  first | exact @GlobalTheory.PlaneLattice.area_pos_and_selfDual | exact GlobalTheory.PlaneLattice.area_pos_and_selfDual | (intros; apply GlobalTheory.PlaneLattice.area_pos_and_selfDual <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaPar

theorem padicComplex_norm_le_max_norm_add_norm {p : ℕ} [Fact p.Prime] {a b : ℂ_[p]} :
    ‖a‖ ≤ max ‖a + b‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max (a + b) (-b)
  simpa using this

theorem unit_of_double_integral_sub {p : ℕ} [Fact p.Prime] (a b : ℂ_[p]) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  simpa [sub_eq_add_neg] using this

theorem unit_of_double_integral {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x y m : ℂ_[p])
    (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1)
    (hΔ : ‖W.Δ‖ = 1) (he : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1)
    (_hη : 2 * y + W.a₁ * x + W.a₃ ≠ 0)
    (hm : m * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hm2 : ‖m ^ 2 + W.a₁ * m - W.a₂ - 2 * x‖ ≤ 1) :
    ‖2 * y + W.a₁ * x + W.a₃‖ = 1 := by
  have he' := he
  rw [WeierstrassCurve.Affine.equation_iff] at he'
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2

  have hy : ‖y‖ ≤ 1 := by
    by_contra hy
    push_neg at hy
    have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
      refine it_add (it_add (it_add ?_ (it_mul h2 ?_)) (it_mul h4 hx)) h6
      · rw [show x ^ 3 = x * x * x by ring]; exact it_mul (it_mul hx hx) hx
      · rw [sq]; exact it_mul hx hx
    have hS : ‖(W.a₁ * x + W.a₃) * y‖ ≤ ‖y‖ := by
      rw [norm_mul]
      calc ‖W.a₁ * x + W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ :=
            mul_le_mul_of_nonneg_right (it_add (it_mul h1 hx) h3) (norm_nonneg _)
        _ = ‖y‖ := one_mul _
    have hyy : ‖y‖ < ‖y ^ 2‖ := by
      rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := y ^ 2) (b := (W.a₁ * x + W.a₃) * y)
    have hsum : y ^ 2 + (W.a₁ * x + W.a₃) * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
      linear_combination he'
    rw [hsum] at key
    have : ‖y ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hR
      · exact absurd (h.trans hS) (not_le.mpr hyy)
    linarith
  have hηle : ‖2 * y + W.a₁ * x + W.a₃‖ ≤ 1 :=
    it_add (it_add (it_mul n2 hy) (it_mul h1 hx)) h3
  refine le_antisymm hηle (not_lt.mp fun hlt => ?_)

  have hmi : ‖m‖ ≤ 1 := by
    by_contra hmg
    push_neg at hmg
    have hT : ‖W.a₁ * m - W.a₂ - 2 * x‖ ≤ ‖m‖ := by
      have hm1 : (1 : ℝ) ≤ ‖m‖ := hmg.le
      refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ ?_)
      · refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ (h2.trans hm1))
        rw [norm_mul]
        calc ‖W.a₁‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = ‖m‖ := one_mul _
      · exact (it_mul n2 hx).trans hm1
    have hmm : ‖m‖ < ‖m ^ 2‖ := by rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := m ^ 2) (b := W.a₁ * m - W.a₂ - 2 * x)
    rw [show m ^ 2 + (W.a₁ * m - W.a₂ - 2 * x) = m ^ 2 + W.a₁ * m - W.a₂ - 2 * x by ring] at key
    have : ‖m ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hm2
      · exact absurd (h.trans hT) (not_le.mpr hmm)
    nlinarith [norm_nonneg m, show ‖m ^ 2‖ = ‖m‖ * ‖m‖ by rw [norm_pow, sq]]
  have hsmall : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1 := by
    rw [← hm]; exact sm_mul hmi hlt
  have := disc_small W x y h1 h2 hx he hlt hsmall
  linarith

end GlobalTheory.ThetaPar
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

variable {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_quad {a c m : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (h : ‖m ^ 2 + a * m - c‖ ≤ 1) : ‖m‖ ≤ 1 := by
  by_contra hm
  push_neg at hm
  have e : m ^ 2 = (m ^ 2 + a * m - c) + (-(a * m) + c) := by ring
  have hb : ‖m ^ 2‖ ≤ ‖m‖ := by
    rw [e]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (h.trans hm.le) ?_)
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (hc.trans hm.le))
    rw [norm_neg, norm_mul]
    calc ‖a‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ = ‖m‖ := one_mul _
  rw [norm_pow, sq] at hb
  have : 1 * ‖m‖ < ‖m‖ * ‖m‖ := mul_lt_mul_of_pos_right hm (by linarith)
  linarith

theorem norm_sub_x_eq_one : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x₁ y₁ x₂ y₂ m m' : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ → ‖x₁‖ ≤ 1 → ‖x₂‖ ≤ 1 → x₁ ≠ x₂ → m * (x₁ - x₂) = y₁ - y₂ → m' * (x₁ - x₂) = y₁ - W.toAffine.negY x₂ y₂ → ‖m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖x₁ - x₂‖ = 1 := by
  intro p _ W x₁ y₁ x₂ y₂ m m' h1 h2 hΔ he1 he2 hx1 hx2 hne hm hm' hq hq'
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hle : ‖x₁ - x₂‖ ≤ 1 := by
    rw [sub_eq_add_neg]; exact it_add hx1 (by rwa [norm_neg])
  refine le_antisymm hle (not_lt.mp fun hs => ?_)
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have c12 : ‖W.a₂ + x₁ + x₂‖ ≤ 1 := it_add (it_add h2 hx1) hx2
  have mb : ‖m‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m ^ 2 + W.a₁ * m - (W.a₂ + x₁ + x₂) = m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂ by ring])
  have mb' : ‖m'‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m' ^ 2 + W.a₁ * m' - (W.a₂ + x₁ + x₂) = m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂ by ring])
  have s1 : ‖y₁ - y₂‖ < 1 := by rw [← hm, mul_comm]; exact sm_mul' hs mb
  have s2 : ‖y₁ + y₂ + W.a₁ * x₂ + W.a₃‖ < 1 := by
    have e : y₁ + y₂ + W.a₁ * x₂ + W.a₃ = m' * (x₁ - x₂) := by
      rw [hm']; simp only [WeierstrassCurve.Affine.negY]; ring
    rw [e, mul_comm]; exact sm_mul' hs mb'
  have s3 : ‖W.a₁ * (x₁ - x₂)‖ < 1 := sm_mul h1 hs
  have hy : ‖2 * y₁ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show 2 * y₁ + W.a₁ * x₁ + W.a₃ =
      (y₁ - y₂) + (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add (sm_add s1 s2) s3
  have s4 : ‖y₁ + y₂ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show y₁ + y₂ + W.a₁ * x₁ + W.a₃ = (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add s2 s3
  have e1 := he1
  have e2 := he2
  rw [WeierstrassCurve.Affine.equation_iff] at e1 e2
  have hN : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂ =
      m * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) := by
    apply mul_right_cancel₀ hd
    have hsub : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) = (x₁ - x₂) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) := by
      linear_combination e1 - e2
    linear_combination -hsub - (y₁ + y₂ + W.a₁ * x₁ + W.a₃) * hm
  have hN' : ‖x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂‖ < 1 := by
    rw [hN]; exact sm_mul mb s4
  have hx' : ‖3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁‖ < 1 := by
    rw [show 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ =
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) -
        ((x₂ - x₁) * (x₂ + 2 * x₁ + W.a₂) + W.a₁ * (y₁ - y₂)) by ring]
    refine sm_sub hN' (sm_add ?_ (sm_mul h1 s1))
    exact sm_mul' (by rw [← norm_neg, neg_sub]; exact hs) (it_add (it_add hx2 (it_mul n2 hx1)) h2)
  have hc := disc_small W x₁ y₁ h1 h2 hx1 he1 hy hx'
  rw [hΔ] at hc
  exact lt_irrefl _ hc

end GlobalTheory.ThetaPar
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  first | exact @GlobalTheory.EisM.lseries_ne_zero_edge | exact GlobalTheory.EisM.lseries_ne_zero_edge | (intros; apply GlobalTheory.EisM.lseries_ne_zero_edge <;> assumption)
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.setIntegral_tsum_translate_eq_integral : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  first | exact @GlobalTheory.integral_unfold_fundamentalDomain | exact GlobalTheory.integral_unfold_fundamentalDomain | (intros; apply GlobalTheory.integral_unfold_fundamentalDomain <;> assumption)
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.integral_cexp_complex_gaussian_linear : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | exact GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | (intros; apply GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane <;> assumption)
end

section

open Polynomial

namespace GlobalTheory

theorem classGroup_mk0_mul_mul_pow_eq_one_of_span_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (N : ℕ) (P D C : Ideal A) (f : A) (hP : P ∈ nonZeroDivisors (Ideal A))
    (hD : D ∈ nonZeroDivisors (Ideal A)) (hC : C ∈ nonZeroDivisors (Ideal A))
    (h : Ideal.span {f} = P * D * C ^ N) :
    ClassGroup.mk0 ⟨P, hP⟩ * ClassGroup.mk0 ⟨D, hD⟩ * ClassGroup.mk0 ⟨C, hC⟩ ^ N = 1 := by
  rw [← map_pow, ← map_mul, ← map_mul]
  have hm : P * D * C ^ N ∈ nonZeroDivisors (Ideal A) :=
    mul_mem (mul_mem hP hD) (pow_mem hC N)
  have e : (⟨P, hP⟩ * ⟨D, hD⟩ * ⟨C, hC⟩ ^ N : nonZeroDivisors (Ideal A)) = ⟨P * D * C ^ N, hm⟩ :=
    Subtype.ext (by simp)
  rw [e, ClassGroup.mk0_eq_one_iff, ← h]
  exact ⟨⟨f, rfl⟩⟩

theorem prod_maximal_mem_nonZeroDivisors {A : Type} [CommRing A] [IsDedekindDomain A]
    {I : Type} [Fintype I] (Q : I → Ideal A) (hQ : ∀ i, (Q i).IsMaximal)
    (P₀ : Ideal A) (hP₀ : P₀.IsMaximal) (h₀ : P₀ ≠ ⊥) :
    (∏ i, Q i) ∈ nonZeroDivisors (Ideal A) := by
  refine prod_mem fun i _ => mem_nonZeroDivisors_of_ne_zero ?_
  intro hi
  have hb : (⊥ : Ideal A).IsMaximal := by
    have := hQ i
    rwa [hi] at this
  exact h₀ (hb.eq_of_le hP₀.ne_top bot_le).symm

theorem exists_class_group_mk0_eq_mul_pow :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (N : ℕ), 2 ≤ N → ∀ P₀ : Ideal A, P₀.IsMaximal →
      ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal →
        a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A,
          ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  intro k A _ _ _ _ _ _ _ _ _ _ N hN P₀ hP₀ h₀
  haveI : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨r, V, D, Q, f₀, hset, hdeg⟩ := GlobalTheory.T.exists_linear_system_maximalDegree_factorization k A N P₀ (by omega) hP₀
  have hform := GlobalTheory.T.exists_formal_deformation_powerSeries_solution k A N (Fin r) V D P₀ Q f₀ hN hP₀ hset
  obtain ⟨a, ha, hall⟩ := GlobalTheory.T.specialise_generic_solution_almost_all_points k A (PowerSeries k) N (Fin r) V D hN hform
  obtain ⟨-, hVD, hQ, -, -, -, -, -, hf₀, hspan₀, -⟩ := hset
  refine ⟨a, ha, fun P hP haP h => ?_⟩
  obtain ⟨Q', f, hQ', hinj, hne, hDQ', hDP, hfV, hf, hfP, hfQ'⟩ := hall P hP haP
  have hspan := GlobalTheory.T.degree_count_maximalIdeal_generates_product k A N (Fin r) D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hne hDQ' hDP
    hf₀ hf hspan₀ (hVD f hfV) hfP hfQ' (hdeg f hfV hf)
  have hP₀ne : P₀ ≠ ⊥ := nonZeroDivisors.ne_zero h₀
  have hD : D ∈ nonZeroDivisors (Ideal A) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hD0
    apply hDP
    rw [hD0]
    exact bot_le
  have hC := prod_maximal_mem_nonZeroDivisors Q hQ P₀ hP₀ hP₀ne
  have hC' := prod_maximal_mem_nonZeroDivisors Q' hQ' P₀ hP₀ hP₀ne
  rw [Finset.prod_pow] at hspan hspan₀
  have e := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P D _ f h hD hC' hspan
  have e₀ := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P₀ D _ f₀ h₀ hD hC hspan₀
  refine ⟨ClassGroup.mk0 ⟨_, hC⟩ / ClassGroup.mk0 ⟨_, hC'⟩, ?_⟩
  generalize ClassGroup.mk0 ⟨P, h⟩ = p at e ⊢
  generalize ClassGroup.mk0 ⟨P₀, h₀⟩ = p₀ at e₀ ⊢
  generalize ClassGroup.mk0 ⟨D, hD⟩ = d at e e₀
  generalize ClassGroup.mk0 ⟨_, hC⟩ = c at e₀ ⊢
  generalize ClassGroup.mk0 ⟨_, hC'⟩ = c' at e ⊢
  have e' : p * c' ^ N = p₀ * c ^ N := by
    apply mul_right_cancel (b := d)
    rw [mul_right_comm p, mul_right_comm p₀, e, e₀]
  rw [div_pow, ← mul_div_assoc, ← e', mul_div_cancel_right]

end GlobalTheory
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

theorem _root_.GlobalTheory.T.hermite_right_factor_of_prime_dvd_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  first | exact @GlobalTheory.hermite_right_factor_prime_det | exact GlobalTheory.hermite_right_factor_prime_det | (intros; apply GlobalTheory.hermite_right_factor_prime_det <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

theorem _root_.GlobalTheory.T.exists_sl2_mul_eq_of_coprime_det_factorization : ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ), y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' → ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  first | exact @GlobalTheory.sl2_right_factor_of_coprime_factorizations | exact GlobalTheory.sl2_right_factor_of_coprime_factorizations | (intros; apply GlobalTheory.sl2_right_factor_of_coprime_factorizations <;> assumption)
end
