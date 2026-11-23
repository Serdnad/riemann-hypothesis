module

public import Formalism.HermitianCurvature.StatementJ
public import Formalism.HermitianCurvature.StatementLE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle012
public import Formalism.HermitianCurvature.StatementWd
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt

def FrameThresholdBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι),
    0 < G.g → 0 < G.lenI → 28 * Real.exp 1 ≤ C →
    (∀ one, 0 ≤ J.supA G de de' T T' l one w) →
    (∀ (b s : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1) + s) →
      (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w ≤
        J.thrS G C de de' T T' l b (s + 1) w) ∧
    (∀ (b : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1)) →
      √((2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) ≤
        J.thrP G C de de' T T' l b w)

theorem pow_bound (C x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hC : 28 * Real.exp 1 ≤ C) :
    Real.exp 1 * (28 * x) ^ n ≤ C * (C * x) ^ n := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have heC : Real.exp 1 ≤ C := by nlinarith
  have hpow : (28 * x) ^ n ≤ (C * x) ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
  exact mul_le_mul heC hpow (by positivity) (by linarith)

theorem frame_threshold_bound : FrameThresholdBound := by
  intro ι _ G C de de' T T' l w hg hI hC hA
  have hN : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have hkg : 0 < 2 * Real.pi / G.g := by positivity
  have key : ∀ (n : ℕ) (Q cg : ℝ), 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg → cg ≤ (28 * G.N / G.lenI) ^ n →
      Q * cg ≤ C * (C * (G.N / G.lenI)) ^ n := by
    intro n Q cg h0 h1 h2 h3
    have hx : 0 ≤ G.N / G.lenI := div_nonneg hN hI.le
    rw [mul_div_assoc] at h3
    calc Q * cg ≤ Real.exp 1 * (28 * (G.N / G.lenI)) ^ n := mul_le_mul h1 h3 h2 (by positivity)
      _ ≤ C * (C * (G.N / G.lenI)) ^ n := pow_bound C _ n hx hC
  refine ⟨fun b s Q cg hb h0 h1 h2 h3 => ?_, fun b Q cg hb h0 h1 h2 h3 => ?_⟩
  · have hA' := hA (decide (b = 1 ∧ s + 1 = 1))
    have hk := key (2 * (b - 1) + s) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) =
        (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    have hn : 2 * (b - 1) + (s + 1) - 1 = 2 * (b - 1) + s := by omega
    unfold J.thrS Sz.lamThreshold Sz.Glob.m
    rw [hn, hz, show C * (2 * Real.pi / G.g) * G.N / G.lenI = (C * (G.N / G.lenI)) * (2 * Real.pi / G.g) by ring,
      mul_pow]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w := mul_nonneg (by positivity) hA'
    calc (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w
        = ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1) + s)) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) *
          ((C * (G.N / G.lenI)) ^ (2 * (b - 1) + s) * (2 * Real.pi / G.g) ^ (2 * (b - 1) + s)) := by ring
  · have hA' := hA false
    have hk := key (2 * (b - 1)) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
        (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    unfold J.thrP Sz.lamPrimeSq Sz.Glob.m
    apply Real.sqrt_le_sqrt
    rw [hz, show C * G.N / G.lenI = C * (G.N / G.lenI) by ring]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l false w * (√(T * T'))⁻¹ := mul_nonneg (mul_nonneg (by positivity) hA') (by positivity)
    calc (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹
        = ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1))) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l false w) *
          (2 * Real.pi / G.g) ^ (2 * b - 1) * (√(T * T'))⁻¹ * (C * (G.N / G.lenI)) ^ (2 * (b - 1)) := by ring

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.frame_threshold_bound_holds : Formalism.FourierDecayAlt.P.PBD.FrameThresholdBound := Formalism.FourierDecayAlt.P.PBD.frame_threshold_bound
end

section

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P

namespace Jx4

theorem rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  have h : (0 : ℝ) < ((|NumberField.discr E| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  unfold S6.rd
  first
    | exact Real.rpow_pos_of_pos h _
    | exact Real.rpow_pos h _

end Jx4

theorem poisson_level_joint : Formalism.FourierDecayAlt.J.PoissonStepJoint := by
  intro hF hJ E W _ D V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hFr hW
  intro ε hε i hi1 hi2 w Y hY κ hκ t₀ B hB S hS
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW ε hε i hi1 hi2 w Y hY κ hκ
  obtain ⟨hinj, hmem, hd0, hdual⟩ := hFr i hi1 hi2
  have key := hJ hF V ι π hπ (Λ i) E (emb i) (dmap i) (D.La i 1) (D.Lad i) φ Cφ
    (D.Nhat ε i w Y κ) hinj hmem hd0 hdual hc hb hnn hhat t₀ B hB S (fun t ht => (hS t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hS t ht).1

theorem lattice_x_eq_lambda_one : Formalism.FourierDecayAlt.J.XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * (i - 1) + 1 - 1 = 2 * i - 2 := by omega
  refine ⟨?_, ?_⟩
  · unfold Sz.xThreshold Sz.lamThreshold
    rw [h]
  · unfold Sz.xHat Sz.lamHat
    rw [h]

theorem frame_product_identities : Formalism.FourierDecayAlt.J.FrameProducts := by
  intro r i s C rd g N I A TT hi hs hrd hg
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hg0 : g ≠ 0 := hg.ne'
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  constructor
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((t + 1 : ℕ) : ℤ) + 1) =
        rd ^ (2 * r + 1) / rd ^ (2 * n + t) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have e2 : 2 * (n + 1 - 1) + (t + 1) - 1 = 2 * n + t := by omega
    unfold Sz.lamThreshold Sz.lamHat
    rw [hz, e1, e2]
    have b1 : C * (2 * Real.pi / g) * N / I = (2 * Real.pi / g) * (C * N / I) := by ring
    have b2 : C * (2 * Real.pi / rd) * N / (g * I) = (2 * Real.pi / (rd * g)) * (C * N / I) := by ring
    rw [b1, b2, mul_pow, mul_pow]
    generalize C * N / I = X
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    ring
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((r : ℤ) + 2 - ((n + 1 : ℕ) : ℤ))) =
        rd ^ r / rd ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have key : ∀ P a : ℝ, 0 ≤ a → √P * a = √(P * a ^ 2) := fun P a ha => by
      rw [Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha]
    rw [hz, key _ _ (mul_nonneg hg.le (div_nonneg (pow_nonneg hrd.le _) (pow_nonneg hrd.le _)))]
    unfold Sz.lamPrimeHat Sz.lamPrimeSq
    congr 1
    have e3 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have e4 : 2 * (n + 1 - 1) = 2 * n := by omega
    have e5 : 2 * (n + 1) - 2 = 2 * n := by omega
    rw [e1, e3, e4, e5]
    have b3 : C * (2 * Real.pi / rd) * N / I = (2 * Real.pi / rd) * (C * N / I) := by ring
    rw [b3, mul_pow]
    generalize C * N / I = X
    generalize (Real.sqrt TT)⁻¹ = Y
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    have hg1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0
    have hr1 : rd * rd⁻¹ = 1 := mul_inv_cancel₀ hrd0
    linear_combination
      (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hg1 -
        (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hr1

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem cutTheta : CutTheta := by
  intro hC c σ ε h4 hε p
  choose Cc hCc using fun i => cutBound c 1 i le_rfl
  have hexp : ∀ ε₂ x : ℝ, ld p (fun y => c.sc ε₂ 1 y * th ε σ y) x =
      ∑ i ∈ range (p + 1), (p.choose i : ℝ) * ld i (c.sc ε₂ 1) x * ld (p - i) (th ε σ) x := by
    intro ε₂ x
    unfold ld
    have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => c.sc ε₂ 1 (Real.exp u)) := smoothLog_sc c ε₂ 1
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => th ε σ (Real.exp u)) := thetaSmooth ε σ hε
    exact iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by exact_mod_cast le_top))
      (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  refine ⟨∑ i ∈ range (p + 1), (p.choose i : ℝ) * Cc i *
      (Real.exp 1 * (p - i).factorial * (4 * σ) ^ (p - i)), fun ε₂ x h2 hx => ⟨?_, ?_⟩⟩
  · rw [hexp, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have a := (hCc i ε₂ x h2 hx).1
    have b := thetaBound hC σ ε h4 hε (p - i) x hx
    calc (p.choose i : ℝ) * |ld i (c.sc ε₂ 1) x| * |ld (p - i) (th ε σ) x|
        ≤ ((p.choose i : ℝ) * Cc i) * (Real.exp 1 * (p - i).factorial * (4 * σ) ^ (p - i) * th ε σ x) :=
          mul_le_mul (mul_le_mul_of_nonneg_left a (Nat.cast_nonneg _)) b (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans a))
      _ = _ := by ring
  · intro hlt
    rw [hexp, Finset.sum_eq_single 0]
    · rw [(hCc 0 ε₂ x h2 hx).2.2 hlt]; simp
    · intro i _ hi
      rw [(hCc i ε₂ x h2 hx).2.2 hlt, if_neg hi]; simp
    · simp

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

end Formalism.FourierDecayAlt.P.LEx1
end

section

namespace Formalism.FourierDecayAlt.P.Wd2

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Units

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

end Units

section Entries

variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]

end Entries

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

end Slots

section Start

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem io_smul (c : K) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem liftMatrix_eq_map_scalar (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A)) = M.map (Matrix.scalar (Ix S)) := rfl

theorem firstEmbed_liftMatrix (M : M2 A) :
    E1 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E1 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E1, lift0, io, Matrix.of_apply, Matrix.map_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem secondEmbed_liftMatrix (M : M2 A) :
    E2 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E2 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E2, lift0, io, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem core_map (c : K) :
    c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A) =
      (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext p q : 1
  simp only [Pf, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply]
  split_ifs <;> simp [map_sub, map_neg, hsc]

theorem J_map : YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) = (YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem smulJ_map (c : K) :
    algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) =
      (algebraMap K A c • YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J, Algebra.algebraMap_eq_smul_one, hsc] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem rtt_lift0 (M N : M2 A) (c : K)
    (H : (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M * E2 N =
      E2 N * E1 M * (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) :
    (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) *
        E1 (lift0 M) * E2 (lift0 N) =
      E2 (lift0 N) * E1 (lift0 M) *
        (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) := by
  rw [core_map, firstEmbed_liftMatrix, secondEmbed_liftMatrix, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0 (M M' : M2 A) (c : K) (H : M'ᵀ * YangianSpanCharacter.T.J A * M = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M' : M2 (SlopeTestRemainingChoices S A))ᵀ * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * lift0 M = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0' (M M' : M2 A) (c : K) (H : M * YangianSpanCharacter.T.J A * M'ᵀ = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (lift0 M')ᵀ = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem liftMatrix_conjTranspose [StarRing A] (M : M2 A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A))ᴴ = lift0 Mᴴ := by
  ext i j x y
  simp [lift0, io, Matrix.conjTranspose_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.star_apply]
  split_ifs <;> simp_all [@eq_comm _ y x]

theorem d0_one : (d0 (1 : SlopeTestRemainingChoices S A)) = 1 := by
  unfold d0
  exact Matrix.diagonal_one

end Start

end Formalism.FourierDecayAlt.P.Wd2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

theorem initial_module_structure : Formalism.FourierDecayAlt.Wd.StartModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q hS
  refine ⟨star_one _, fun Y _ hY => ?_, fun Y _ Y' _ => ?_, fun Y _ _ => ?_, hS.q_real⟩
  · rw [Formalism.FourierDecayAlt.P.Wd2.d0_one, one_mul, Formalism.FourierDecayAlt.P.Wd2.liftMatrix_conjTranspose, hS.herm Y hY]
  · exact Formalism.FourierDecayAlt.P.Wd2.rtt_lift0 (QQ Y') (QQ Y) (Y' - Y) (hS.rtt Y Y')
  · exact ⟨Formalism.FourierDecayAlt.P.Wd2.det_lift0 (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).1,
      Formalism.FourierDecayAlt.P.Wd2.det_lift0' (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).2⟩

end Formalism.FourierDecayAlt.P
end
