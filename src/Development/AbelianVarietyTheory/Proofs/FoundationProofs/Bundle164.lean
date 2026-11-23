module

public import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant
public import GroundTheory.GlobalFields.ComplexMultiplication.JInvariantHomothety
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Formalism.DirichletDensity.DirichletDensityProofs.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.JOrbit

open GroundTheory.Global.Elliptic

theorem exists_smul_of_homothetic (τ σ : ℍ) {c : ℂ} (hc : c ≠ 0)
    (h : ((latticeOfTau τ).lattice : Set ℂ) = (c * ·) '' (latticeOfTau σ).lattice) :
    ∃ γ : SL(2, ℤ), τ = γ • σ := by
  have m1 : (τ : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₁_mem_lattice
  have m2 : (1 : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₂_mem_lattice
  have m3 : c * σ ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨σ, (latticeOfTau σ).ω₁_mem_lattice, rfl⟩
  have m4 : c * 1 ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨1, (latticeOfTau σ).ω₂_mem_lattice, rfl⟩
  obtain ⟨z, hz, h1⟩ := m1
  obtain ⟨w, hw, h2⟩ := m2
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  obtain ⟨e, f, rfl⟩ := PeriodPair.mem_lattice.1 hw
  obtain ⟨p, q, h3⟩ := PeriodPair.mem_lattice.1 m3
  obtain ⟨r, s, h4⟩ := PeriodPair.mem_lattice.1 m4
  simp only [latticeOfTau_ω₁, latticeOfTau_ω₂, mul_one] at h1 h2 h3 h4
  have k1 : (σ : ℂ) = p * (a * σ + b) + q * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h3 - p * h1 - q * h2
  have k2 : (1 : ℂ) = r * (a * σ + b) + s * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h4 - r * h1 - s * h2
  have k3 : (τ : ℂ) * (e * σ + f) = a * σ + b := by
    apply mul_left_cancel₀ hc
    linear_combination (τ : ℂ) * h2 - h1
  have hy : 0 < σ.im := σ.im_pos
  have hv : 0 < τ.im := τ.im_pos
  have k1i := congrArg Complex.im k1
  have k1r := congrArg Complex.re k1
  have k2i := congrArg Complex.im k2
  have k2r := congrArg Complex.re k2
  have k3i := congrArg Complex.im k3
  have k3r := congrArg Complex.re k3
  simp at k1i k1r k2i k2r k3i k3r
  have e1 : ((p * a + q * e : ℤ) : ℝ) = (1 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k1i
  have e3 : ((r * a + s * e : ℤ) : ℝ) = (0 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k2i
  have e2 : ((p * b + q * f : ℤ) : ℝ) = (0 : ℤ) := by
    push_cast at e1 ⊢; linear_combination -k1r - σ.re * e1
  have e4 : ((r * b + s * f : ℤ) : ℝ) = (1 : ℤ) := by
    push_cast at e3 ⊢; linear_combination -k2r - σ.re * e3
  have e1' : p * a + q * e = 1 := by exact_mod_cast e1
  have e2' : p * b + q * f = 0 := by exact_mod_cast e2
  have e3' : r * a + s * e = 0 := by exact_mod_cast e3
  have e4' : r * b + s * f = 1 := by exact_mod_cast e4
  have hdet : (a * f - b * e) * (p * s - q * r) = 1 := by
    linear_combination (r * b + s * f) * e1' + e4' - (r * a + s * e) * e2'
  have him : τ.im * ((e * σ.re + f) ^ 2 + (e * σ.im) ^ 2) = σ.im * ((a * f - b * e : ℤ) : ℝ) := by
    push_cast
    linear_combination (e * σ.re + f) * k3i - (e * σ.im) * k3r
  have hnn : (0 : ℝ) ≤ ((a * f - b * e : ℤ) : ℝ) := by
    have : 0 ≤ σ.im * ((a * f - b * e : ℤ) : ℝ) := by rw [← him]; positivity
    exact (mul_nonneg_iff_of_pos_left hy).1 this
  have hnn' : 0 ≤ a * f - b * e := by exact_mod_cast hnn
  have hD : a * f - b * e = 1 := Int.eq_one_of_mul_eq_one_right hnn' hdet
  have hne : (e : ℂ) * σ + f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  let γ : SL(2, ℤ) := ⟨!![a, b; e, f], by rw [Matrix.det_fin_two_of]; exact hD⟩
  refine ⟨γ, ?_⟩
  ext
  rw [coe_specialLinearGroup_apply γ σ]
  simp [γ]
  rw [eq_div_iff hne, k3]

theorem exists_smul_of_E₄_E₆ :
    ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  intro τ σ h
  have hj : modularJ σ = modularJ τ := by
    have h1 := ModularForm.discriminant_ne_zero τ
    have h2 := ModularForm.discriminant_ne_zero σ
    rw [modularJ, modularJ, div_eq_div_iff h2 h1,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq σ]
    linear_combination h / 1728
  obtain ⟨c, hc, hl⟩ := (modularJ_eq_iff σ τ).1 hj
  exact exists_smul_of_homothetic τ σ hc hl

end GlobalTheory.JOrbit
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_inv_add_int_sub_inv_add_int_le (z : ℂ) (L : ℝ) (d m : ℤ)
    (hm : |(m : ℝ) - d| ≤ L) (hd : 2 * (‖z‖ + L) + 1 ≤ |(d : ℝ)|) :
    ‖(z + d)⁻¹ - (z + m)⁻¹‖ ≤ 4 * L * (1 / (d : ℝ) ^ 2) := by
  have hL : 0 ≤ L := (abs_nonneg _).trans hm
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have key : ∀ x : ℤ, |(x : ℝ)| - ‖z‖ ≤ ‖z + x‖ := by
    intro x
    have h1 : ‖(x : ℂ)‖ ≤ ‖z + x‖ + ‖z‖ := by
      have := norm_sub_le (z + x) z
      simpa using this
    have h2 : ‖(x : ℂ)‖ = |(x : ℝ)| := Complex.norm_intCast x
    linarith
  have hdm : |(d : ℝ)| - L ≤ |(m : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (d : ℝ) m
    rw [abs_sub_comm] at this
    linarith
  have hD : 0 < |(d : ℝ)| / 2 := by linarith
  have h1 : |(d : ℝ)| / 2 ≤ ‖z + d‖ := by have := key d; linarith
  have h2 : |(d : ℝ)| / 2 ≤ ‖z + m‖ := by have := key m; linarith
  have n1 : z + d ≠ 0 := norm_pos_iff.1 (hD.trans_le h1)
  have n2 : z + m ≠ 0 := norm_pos_iff.1 (hD.trans_le h2)
  have e : (z + d)⁻¹ - (z + m)⁻¹ = ((m - d : ℤ) : ℂ) / ((z + d) * (z + m)) := by
    push_cast
    field_simp
    ring
  rw [e, norm_div, norm_mul, Complex.norm_intCast]
  push_cast
  calc |(m : ℝ) - d| / (‖z + d‖ * ‖z + m‖)
      ≤ L / (|(d : ℝ)| / 2 * (|(d : ℝ)| / 2)) := by
        gcongr
    _ = 4 * L * (1 / (d : ℝ) ^ 2) := by
        have : |(d : ℝ)| ≠ 0 := (by linarith : 0 < |(d : ℝ)|).ne'
        rw [← sq_abs (d : ℝ)]
        field_simp
        ring

theorem summable_periodic_mul_inv_sub_inv_floor :
    ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im →
      Summable (fun d : ℤ => φ d * ((z + d)⁻¹ - (z + (L * (d / L) : ℤ))⁻¹)) := by
  intro L φ z hL _
  haveI : NeZero L := ⟨hL.ne'⟩
  set M : ℝ := ∑ y, ‖φ y‖ with hM
  have hφ : ∀ y, ‖φ y‖ ≤ M := fun y =>
    Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hφ 0)
  have hs : Summable (fun d : ℤ => M * (4 * (L : ℝ) * (1 / (d : ℝ) ^ 2))) :=
    ((Real.summable_one_div_int_pow.2 one_lt_two).mul_left _).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (‖z‖ + L) + 1)
  have hfin : (Set.Icc (-(N : ℤ)) N).Finite := Set.finite_Icc _ _
  refine Filter.mem_of_superset hfin.compl_mem_cofinite ?_
  intro d hd
  have hd' : (N : ℤ) ≤ |d| := by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hd
    rcases hd with h | h
    · exact le_abs.2 (Or.inr (by omega))
    · exact le_abs.2 (Or.inl h.le)
  have hd'' : (N : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast hd'
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hm : |(L : ℤ) * (d / L) - d| ≤ L := by
    have a := Int.emod_nonneg d hL'.ne'
    have b := Int.emod_lt_of_pos d hL'
    have c := Int.emod_def d L
    rw [abs_le]
    constructor <;> linarith
  have hm' : |(((L : ℤ) * (d / L) : ℤ) : ℝ) - d| ≤ (L : ℝ) := by exact_mod_cast hm
  have := norm_inv_add_int_sub_inv_add_int_le z L d _ hm' (hN.trans hd'')
  show ‖_‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hφ _) this (norm_nonneg _) hM0

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocSer

theorem step (x y : ℂ) (c : ℕ → ℂ) (h1 : c 1 = x + y) (h0 : c 0 = 1)
    (hr : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) :
    ∀ r, c (r + 1) = y * c r + x ^ (r + 1) := by
  intro r
  induction r with
  | zero => rw [h1, h0]; ring
  | succ n ih => rw [hr n, ih]; ring

theorem bound (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    ∀ r : ℕ, ‖c r * z ^ r‖ ≤ ((r : ℝ) + 1) * (max ‖x * z‖ ‖y * z‖) ^ r := by
  intro r
  induction r with
  | zero => simp [h0]
  | succ n ih =>
    have e : c (n + 1) * z ^ (n + 1) = (y * z) * (c n * z ^ n) + (x * z) ^ (n + 1) := by
      rw [hs n]; ring
    rw [e]
    set ρ := max ‖x * z‖ ‖y * z‖
    have hx : ‖x * z‖ ≤ ρ := le_max_left _ _
    have hy : ‖y * z‖ ≤ ρ := le_max_right _ _
    have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hx
    calc ‖(y * z) * (c n * z ^ n) + (x * z) ^ (n + 1)‖
        ≤ ‖y * z‖ * ‖c n * z ^ n‖ + ‖x * z‖ ^ (n + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ ρ * (((n : ℝ) + 1) * ρ ^ n) + ρ ^ (n + 1) := by
          gcongr
      _ = (((n + 1 : ℕ) : ℝ) + 1) * ρ ^ (n + 1) := by push_cast; ring

theorem summ1 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact (a.add b).congr (fun r => by ring)

theorem summ2 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) ^ 2 * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have a1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact ((a.add (a1.mul_left 2)).add b).congr (fun r => by ring)

theorem part1 (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1))
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    Summable (fun r => c r * z ^ r) ∧ (∑' r, c r * z ^ r) * ((1 - x * z) * (1 - y * z)) = 1 := by
  set ρ := max ‖x * z‖ ‖y * z‖
  have hρ1 : ρ < 1 := max_lt hx hy
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hS : Summable (fun r => c r * z ^ r) :=
    Summable.of_norm_bounded (summ1 ρ hρ0 hρ1) (bound x y z c h0 hs)
  refine ⟨hS, ?_⟩
  have hG := tsum_geometric_of_norm_lt_one hx
  have hGs := summable_geometric_of_norm_lt_one hx
  have hne : (1 : ℂ) - x * z ≠ 0 := by
    intro h
    have : x * z = 1 := by linear_combination -h
    rw [this, norm_one] at hx; exact lt_irrefl _ hx
  have hG' : (∑' n : ℕ, (x * z) ^ n) * (1 - x * z) = 1 := by
    rw [hG]; exact inv_mul_cancel₀ hne
  have e1 := hS.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * z ^ (r + 1) = (y * z) * (c r * z ^ r) + (x * z) * (x * z) ^ r := by
    intro r; rw [hs r]; ring
  simp_rw [e2] at e1
  rw [Summable.tsum_add (hS.mul_left _) (hGs.mul_left _), tsum_mul_left, tsum_mul_left, h0] at e1
  simp only [pow_zero, mul_one] at e1
  linear_combination (1 - x * z) * e1 + (x * z) * hG'

theorem part2 (x y : ℂ) (c : ℕ → ℂ) (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T < 1) (hx : ‖x‖ ^ 2 * T < 1)
    (hy : ‖y‖ ^ 2 * T < 1) (h0 : c 0 = 1) (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)
      = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  have hnx : 0 ≤ ‖x‖ := norm_nonneg _
  have hny : 0 ≤ ‖y‖ := norm_nonneg _
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hxy : ‖y‖ * (‖x‖ * T) < 1 := by
    have hp := mul_lt_mul'' hx hy (by positivity) (by positivity)
    have e : (‖y‖ * (‖x‖ * T)) ^ 2 = (‖x‖ ^ 2 * T) * (‖y‖ ^ 2 * T) := by ring
    have : (‖y‖ * (‖x‖ * T)) ^ 2 < 1 := by rw [e]; linarith
    nlinarith [mul_nonneg hny (mul_nonneg hnx hT0)]

  set m := max ‖x‖ ‖y‖ with hm
  have hσ : m ^ 2 * T < 1 := by
    rcases max_choice ‖x‖ ‖y‖ with h | h <;> rw [hm, h] <;> assumption
  have hb : ∀ r : ℕ, ‖c r‖ ≤ ((r : ℝ) + 1) * m ^ r := by
    intro r; have := bound x y 1 c h0 hs r; simpa using this
  have hU : Summable (fun r : ℕ => ‖c r‖ ^ 2 * T ^ r) := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
      (summ2 (m ^ 2 * T) (by positivity) hσ)
    calc ‖c r‖ ^ 2 * T ^ r ≤ (((r : ℝ) + 1) * m ^ r) ^ 2 * T ^ r := by
          gcongr; exact hb r
      _ = ((r : ℝ) + 1) ^ 2 * (m ^ 2 * T) ^ r := by ring
  have hf : ∀ r : ℕ, c r * conj (c r) * (T : ℂ) ^ r = ((‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) := by
    intro r; push_cast; rw [Complex.mul_conj']
  have hVs : Summable (fun r : ℕ => c r * conj (c r) * (T : ℂ) ^ r) := by
    have := (Complex.summable_ofReal).mpr hU
    exact this.congr (fun r => (hf r).symm)
  have hVdef : ((∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) = ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r := by
    rw [Complex.ofReal_tsum]; congr 1; funext r; exact (hf r).symm

  have hW : Summable (fun r => c r * (conj x * T) ^ r) ∧
      (∑' r, c r * (conj x * T) ^ r) * ((1 - x * (conj x * T)) * (1 - y * (conj x * T))) = 1 := by
    refine part1 x y (conj x * T) c h0 hs ?_ ?_
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; exact hxy
  have hW' : Summable (fun r => conj (c r) * (x * T) ^ r) ∧
      (∑' r, conj (c r) * (x * T) ^ r) * ((1 - conj x * (x * T)) * (1 - conj y * (x * T))) = 1 := by
    refine part1 (conj x) (conj y) (x * T) (fun r => conj (c r)) (by simp [h0]) ?_ ?_ ?_
    · intro r
      show conj (c (r + 1)) = conj y * conj (c r) + conj x ^ (r + 1)
      rw [hs r]; simp only [map_add (f := _), map_mul, map_pow]
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; linarith [hxy]
  have hGn : ‖x * conj x * (T : ℂ)‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
  have hGs := summable_geometric_of_norm_lt_one hGn
  have hG : (∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n) * (1 - x * conj x * T) = 1 := by
    rw [tsum_geometric_of_norm_lt_one hGn]
    refine inv_mul_cancel₀ ?_
    intro h
    have : x * conj x * (T : ℂ) = 1 := by linear_combination -h
    rw [this, norm_one] at hGn; exact lt_irrefl _ hGn
  have e1 := hVs.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * conj (c (r + 1)) * (T : ℂ) ^ (r + 1) =
      (T : ℂ) * (y * conj y * (c r * conj (c r) * (T : ℂ) ^ r) + y * conj x * (c r * (conj x * T) ^ r)
        + x * conj y * (conj (c r) * (x * T) ^ r) + x * conj x * (x * conj x * T) ^ r) := by
    intro r; rw [hs r]; simp only [map_add (f := _), map_mul, map_pow]; ring
  simp_rw [e2] at e1
  rw [tsum_mul_left, Summable.tsum_add (((hVs.mul_left _).add (hW.1.mul_left _)).add (hW'.1.mul_left _))
    (hGs.mul_left _), Summable.tsum_add ((hVs.mul_left _).add (hW.1.mul_left _)) (hW'.1.mul_left _),
    Summable.tsum_add (hVs.mul_left _) (hW.1.mul_left _)] at e1
  simp only [tsum_mul_left, h0, map_one, pow_zero, mul_one] at e1
  have hW2 := hW.2
  have hW'2 := hW'.2
  set V := ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r
  set W := ∑' r, c r * (conj x * T) ^ r
  set W' := ∑' r, conj (c r) * (x * T) ^ r
  set G := ∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n
  have key : V * ((1 - x * conj x * T) * (1 - y * conj y * T) * ((1 - x * conj y * T) * (1 - conj x * y * T)))
      = 1 - x * conj x * (y * conj y) * T ^ 2 := by
    linear_combination ((1 - x * conj x * T) * (1 - x * conj y * T) * (1 - conj x * y * T)) * e1
      + (T * y * conj x * (1 - x * conj y * T)) * hW2 + (T * x * conj y * (1 - conj x * y * T)) * hW'2
      + (x * conj x * T * (1 - x * conj y * T) * (1 - conj x * y * T)) * hG
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, hVdef]
  push_cast
  have hx2 : ((‖x‖ : ℂ)) ^ 2 = x * conj x := (Complex.mul_conj' x).symm
  have hy2 : ((‖y‖ : ℂ)) ^ 2 = y * conj y := (Complex.mul_conj' y).symm
  have hxy2 : ((‖x * y‖ : ℂ)) ^ 2 = x * y * conj (x * y) := (Complex.mul_conj' _).symm
  have hn2 : ((‖1 - x * conj y * T‖ : ℂ)) ^ 2 = (1 - x * conj y * T) * conj (1 - x * conj y * T) :=
    (Complex.mul_conj' _).symm
  rw [hx2, hy2, hxy2, hn2]
  simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination key

theorem twoStep_eulerFactors : ∀ (x y : ℂ) (c : ℕ → ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∑' r : ℕ, c r * (T : ℂ) ^ r) * ((1 - x * T) * (1 - y * T)) = 1 ∧ (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2) = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  intro x y c T hT0 hT1 hx hy h0 h1 hr
  have hs := step x y c h1 h0 hr
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hsq : ∀ u : ℂ, ‖u‖ ^ 2 * T < 1 → ‖u * (T : ℂ)‖ < 1 := by
    intro u hu
    rw [norm_mul, hnT]
    have hn : 0 ≤ ‖u‖ * T := mul_nonneg (norm_nonneg _) hT0
    have : (‖u‖ * T) ^ 2 ≤ ‖u‖ ^ 2 * T := by
      have : (‖u‖ * T) ^ 2 = (‖u‖ ^ 2 * T) * T := by ring
      rw [this]
      exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hT0) hT1.le
    nlinarith
  exact ⟨(part1 x y T c h0 hs (hsq x hx) (hsq y hy)).2, part2 x y c T hT0 hT1 hx hy h0 hs⟩

end GlobalTheory.LocSer
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem sub_one_mul_log_div_rpow_le (n : ℕ) (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    (x - 1) * (Real.log n / (n : ℝ) ^ x) ≤ 1 / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have e : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [Real.rpow_sub_one hp.ne' x]; field_simp
  have hq : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hp _
  have hl : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
    rw [Real.rpow_def_of_pos hp]
    have := Real.add_one_le_exp (Real.log n * (x - 1))
    nlinarith [this]
  have hrw : (x - 1) * (Real.log n / (n : ℝ) ^ x) =
      ((x - 1) * Real.log n / (n : ℝ) ^ (x - 1)) * (1 / n) := by
    rw [e]; field_simp
  rw [hrw]
  refine mul_le_of_le_one_left (by positivity) ((div_le_one hq).2 hl)

theorem not_summable_one_div_primes_eq_neg_one :
    ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ =>
      if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  intro M hM hs
  haveI : NeZero M := ⟨hM.ne'⟩
  have hD := Formalism.HF.apLogDensity M (-1 : ZMod M) isUnit_one.neg
  unfold Formalism.HF.LogDensity at hD
  set S := {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod M) = -1}} with hS
  have h0 : Tendsto (fun x : ℝ => ∑' n : ℕ,
      (x - 1) * S.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) (𝓝[>] 1)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
    · by_cases hn : n ∈ S
      · simp only [Set.indicator_of_mem hn]
        have hp : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
        have hc : Continuous fun x : ℝ => (x - 1) * (Real.log n / (n : ℝ) ^ x) := by
          refine (continuous_id.sub continuous_const).mul (continuous_const.div ?_ ?_)
          · exact continuous_const.rpow continuous_id (fun _ => Or.inl hp.ne')
          · intro x; exact (Real.rpow_pos_of_pos hp x).ne'
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · simp only [Set.indicator_of_notMem hn, mul_zero]
        exact tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx n
      have hx : (1 : ℝ) < x := hx
      by_cases hn : n ∈ S
      · have hc : n.Prime ∧ (n : ZMod M) = -1 := hn
        simp only [Set.indicator_of_mem hn, if_pos hc]
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hc.1.one_lt.le)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
          (div_nonneg hlog (Real.rpow_nonneg n.cast_nonneg _)))]
        exact sub_one_mul_log_div_rpow_le n hc.1.one_lt hx
      · have hc : ¬ (n.Prime ∧ (n : ZMod M) = -1) := hn
        simp only [Set.indicator_of_notMem hn, if_neg hc, mul_zero, norm_zero, le_refl]
  simp only [tsum_zero, tsum_mul_left] at h0
  have hu := tendsto_nhds_unique hD h0
  have ht : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 hM
  rw [one_div] at hu
  exact (inv_pos.2 ht).ne' hu

end GlobalTheory
end
