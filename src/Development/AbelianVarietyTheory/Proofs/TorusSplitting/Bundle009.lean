module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormProdSumThetaLeExp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.EtaAn.archimedeanBoundTotalConstant_size : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q m Nc : ℕ) (L : ℝ), 2 ≤ L → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E → 1 ≤ r → 1 ≤ m → m ≤ r → 1 ≤ q → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E) ≤ 2 * L → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E) ≤ 2 * L → Real.log r ≤ L → Real.log q ≤ 70 * L → Real.log Nc ≤ 41 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 → 0 ≤ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ∧ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ≤ 200000 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 := by
  intro E _ _ _ r q m Nc L hL hf hr hm hmr hq hrd hlrd hlf hlr hlq hlN
  unfold _root_.GlobalTheory.EtaAn.p16 _root_.GlobalTheory.EtaAn.p3 _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar _root_.ReciprocityTheory.ChartRestriction.G.I2.RR
  push_cast
  set f := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E with hfdef
  set D := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E with hDdef
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMR : (m : ℝ) ≤ r := by exact_mod_cast hmr
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlM : Real.log m ≤ L := (Real.log_le_log (by positivity) hMR).trans hlr
  have hlFnn : 0 ≤ Real.log f := Real.log_nonneg hF
  have hlMnn : 0 ≤ Real.log m := Real.log_nonneg hM
  have heOne := Real.exp_one_gt_d9
  have heTwo : (7.3 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
  have hlTwo : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlFive : Real.log 5 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSix : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSeven : Real.log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlTenThousand : Real.log 10000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (10 : ℝ) = 2 * 5 by norm_num, Real.exp_mul]
    have : (7.3 : ℝ) ^ 5 ≤ Real.exp 2 ^ 5 := pow_le_pow_left₀ (by norm_num) heTwo 5
    rw [← Real.rpow_natCast] at this
    norm_num at this ⊢
    linarith

  have hy : (1 : ℝ) ≤ f * r * q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hR) hQ
  have hsqrt : 1 ≤ √((f : ℝ) * r * q) := Real.one_le_sqrt.mpr hy
  have hlogSqrt : Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ 2 + 37 * L := by
    calc Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ Real.log (7 * √((f : ℝ) * r * q)) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 7 + (Real.log f + Real.log r + Real.log q) / 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      _ ≤ 2 + 37 * L := by linarith
  have hlogSqrtNonneg : 0 ≤ Real.log (1 + 6 * √((f : ℝ) * r * q)) :=
    Real.log_nonneg (by have := Real.sqrt_nonneg ((f : ℝ) * r * q); linarith)

  have hg : Real.log (3 * (2 * (f : ℝ) * m)) = Real.log 6 + Real.log f + Real.log m := by
    rw [show 3 * (2 * (f : ℝ) * m) = 6 * f * m by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlogFact : Real.log (2 * (3 * (2 * (f : ℝ) * m)) ^ (2 * f * m)) =
      Real.log 2 + 2 * f * m * Real.log (3 * (2 * (f : ℝ) * m)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hgUpper : Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 + 3 * L := by rw [hg]; linarith
  have hgNonneg : 0 ≤ Real.log (3 * (2 * (f : ℝ) * m)) := by rw [hg]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 6 by norm_num)]

  have hmaxOne : (1 : ℝ) ≤ max 1 (Nc : ℝ) := le_max_left _ _
  have hlogBig : Real.log (max 1 (Nc : ℝ) * 5 ^ (8 * f * r ^ 2)) =
      Real.log (max 1 (Nc : ℝ)) + 8 * f * r ^ 2 * Real.log 5 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hXnn : 0 ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by positivity
  have hlogMax : Real.log (max 1 (Nc : ℝ)) ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by
    rcases le_total (Nc : ℝ) 1 with h | h
    · rw [max_eq_left h, Real.log_one]; exact hXnn
    · rw [max_eq_right h]; exact hlN
  have hlogMaxNonneg : 0 ≤ Real.log (max 1 (Nc : ℝ)) := Real.log_nonneg hmaxOne

  have hlogLast : Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
      ≤ 10 + 24 * L := by
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith
  have hlogLastNonneg : 0 ≤ Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    apply Real.log_nonneg
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hR)
        (one_le_pow₀ hF)) (one_le_pow₀ hM)) (one_le_pow₀ hrd)
  rw [hlogFact, hlogBig]

  have hFL : 2 ≤ (f : ℝ) * L := le_trans hL (le_mul_of_one_le_left (by linarith) hF)
  have hFRsq : 4 * ((f : ℝ) * r ^ 2) ≤ ((f : ℝ) * r * L) ^ 2 := by
    have hFLsq : 4 ≤ (f : ℝ) * L ^ 2 := by
      calc (4 : ℝ) = 1 * (2 * 2) := by ring
        _ ≤ f * (L * L) := mul_le_mul hF (mul_le_mul hL hL (by norm_num) (by linarith))
            (by norm_num) (by positivity)
        _ = f * L ^ 2 := by ring
    calc 4 * ((f : ℝ) * r ^ 2) ≤ (f * L ^ 2) * ((f : ℝ) * r ^ 2) :=
          mul_le_mul_of_nonneg_right hFLsq (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hFRsqL : 2 * ((f : ℝ) * r ^ 2 * L) ≤ ((f : ℝ) * r * L) ^ 2 := by
    calc 2 * ((f : ℝ) * r ^ 2 * L) ≤ (f * L) * ((f : ℝ) * r ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hFL (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hRle : (r : ℝ) ≤ f * r ^ 2 := by
    calc (r : ℝ) = 1 * 1 * r := by ring
      _ ≤ f * r * r := mul_le_mul (mul_le_mul hF hR zero_le_one (by positivity)) le_rfl
          (by positivity) (by positivity)
      _ = f * r ^ 2 := by ring
  have hprodSqrt : (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) ≤
      r * (f * r * (2 + 37 * L)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogSqrt (by positivity)) (by positivity)
  have hprodFact : (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) ≤ r * (2 * f * r * (2 + 3 * L)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc 2 * (f : ℝ) * m * Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 * f * m * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_left hgUpper (by positivity)
      _ ≤ 2 * f * r * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMR (by positivity)) (by linarith)
  have hprodRFM : (r : ℝ) * (2 * f * m) ≤ 2 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hMR (by positivity : (0 : ℝ) ≤ 2 * f * r)
    linarith
  have hprodLast : (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) ≤
      625 * (f * r ^ 2) * (10 + 24 * L) := by
    calc (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
          Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
        ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_left hlogLast (by positivity)
      _ ≤ 625 * (f * r ^ 2) * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_right (by linarith [hprodRFM]) (by linarith)
  have hprodFiveA : 8 * (f : ℝ) * r ^ 2 * Real.log 5 ≤ 16 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlFive (by positivity : (0 : ℝ) ≤ f * r ^ 2)
    linarith
  have hnnSqrt : 0 ≤ (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) := by positivity
  have hnnFact : 0 ≤ (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) := by positivity
  have hnnLast : 0 ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    positivity
  have hnnFive : 0 ≤ (f : ℝ) * r ^ 2 * Real.log 5 := by positivity
  have hnnTwo : 0 ≤ (r : ℝ) * Real.log 2 := by positivity
  have hRlogTwo : (r : ℝ) * Real.log 2 ≤ r := mul_le_of_le_one_right (by positivity) hlTwo
  have hrfm_nonneg : 0 ≤ (r : ℝ) * (2 * f * m) := by positivity
  constructor
  · linarith
  · linarith

end GlobalTheory.EtaAn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RunParametersBound

theorem real_bounds (f r m ρ w q : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmf : m ≤ f)
    (hf2 : f ^ 2 ≤ ρ) (hρ : 16 ≤ ρ) (hw0 : 0 ≤ w) (hw : w ≤ f ^ 2)
    (hq : 135 * (f * r) * (ρ ^ 7) ^ 4 * (r + 1) ≤ q) :
    (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (135 * (f * r)) * (ρ ^ 7) ^ 3) < q ∧
    2 ≤ q / (135 * (f * r) * (ρ ^ 7) ^ 4) ∧
    90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ q / 2 ∧
    4 * (7 + Real.log q) + 2 * f * m + 1 ≤ q * 2 ∧
    f * r * Real.log 2 + 2 * (2 * f * m) + 3 + (1 + 1) * (r * Real.log r + 3 * r + 3) ≤ q := by
  have hρ1 : (1 : ℝ) ≤ ρ := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hN : r ≤ f * r := by nlinarith
  have hN1 : 1 ≤ f * r := by linarith
  have hfρ : f ≤ ρ := by nlinarith
  have hfm : f * m ≤ ρ := by nlinarith
  have hm2 : m ^ 2 ≤ ρ := by nlinarith
  have hd0 : 0 ≤ 2 * f * m := by positivity
  have hd : 2 * f * m ≤ 2 * ρ := by linarith
  have hd2 : (2 * f * m) ^ 2 ≤ (2 * ρ) ^ 2 := by gcongr
  have hB : 0 < 135 * (f * r) * (ρ ^ 7) ^ 4 := by positivity
  have h2B : 135 * (f * r) * (ρ ^ 7) ^ 4 * 2 ≤ q :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hB.le) hq
  have hT : ρ ^ 5 ≤ (ρ ^ 7) ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hρ1 (by norm_num)
  have hT4 : 16 * ρ ^ 4 ≤ ρ ^ 5 := by
    rw [pow_succ' ρ 4]; gcongr
  have hT1 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have hqT : 270 * (ρ ^ 7) ^ 4 ≤ q := by
    have : 135 * 1 * (ρ ^ 7) ^ 4 * 2 ≤ 135 * (f * r) * (ρ ^ 7) ^ 4 * 2 := by gcongr
    linarith
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (135 * (f * r)) * (ρ ^ 7) ^ 3) ≤
        (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * (135 * (f * r)) * (ρ ^ 7) ^ 3) := by
      have hwρ : w ≤ ρ := hw.trans hf2
      gcongr
    have h2 : (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * (135 * (f * r)) * (ρ ^ 7) ^ 3) =
        8 * (135 * (f * r) * ρ ^ 26) := by ring
    have h3 : 135 * (f * r) * (ρ ^ 7) ^ 4 = ρ ^ 2 * (135 * (f * r) * ρ ^ 26) := by ring
    have h4 : 0 < 135 * (f * r) * ρ ^ 26 := by positivity
    have h5 : 8 * (135 * (f * r) * ρ ^ 26) ≤ ρ ^ 2 * (135 * (f * r) * ρ ^ 26) :=
      mul_le_mul_of_nonneg_right (by nlinarith) h4.le
    linarith
  · rw [le_div_iff₀ hB]; linarith
  · have h1 : 90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ 90 * ρ * (2 * ρ) ^ 2 * ρ := by gcongr
    have h2 : 90 * ρ * (2 * ρ) ^ 2 * ρ = 360 * ρ ^ 4 := by ring
    linarith
  · have h1 : Real.log q = Real.log (q / 4) + Real.log 4 := by
      rw [Real.log_div hq0.ne' (by norm_num)]; ring
    have h2 : Real.log (q / 4) ≤ q / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  · have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h2 : Real.log r ≤ r := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by linarith); linarith
    have h3 : f * r * Real.log 2 ≤ f * r * 1 := by gcongr
    have h2' : 0 ≤ Real.log r := Real.log_nonneg hr
    have h4 : r * Real.log r ≤ (f * r) * r := by gcongr
    have h5 : 135 * (f * r) * ρ * (r + 1) ≤ 135 * (f * r) * (ρ ^ 7) ^ 4 * (r + 1) := by
      have : ρ ≤ (ρ ^ 7) ^ 4 := by linarith
      gcongr
    have h6 : (f * r) * 1 * r ≤ (f * r) * ρ * r := by gcongr
    have h7 : 1 * ρ ≤ (f * r) * ρ := by gcongr
    have h8 : (f * r) * 16 ≤ (f * r) * ρ := by gcongr
    have h9 : 0 ≤ (f * r) * r := by positivity
    nlinarith

theorem exists_run_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ), 2 ≤ I2.PT.f E * r → 1 ≤ m → m ^ 4 ≤ I2.PT.f E → (I2.PT.f E : ℝ) ^ 2 ≤ I2.PT.rd E → 16 ≤ I2.PT.rd E → ∃ (q : ℕ) (R0 : ℝ), 1 ≤ q ∧ Real.log q ≤ 28 * Real.log (I2.PT.rd E) + 2 * Real.log (I2.PT.f E * r) + 7 ∧ RunOK E r 1 q R0 m := by
  intro E _ _ _ r m hfr hm1 hmf hf2 hrd
  have hf : 1 ≤ I2.PT.f E := by
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hfr; omega
    · exact h
  have hmf' : m ≤ I2.PT.f E := (Nat.le_self_pow (by norm_num) m).trans hmf
  have hfR : (1 : ℝ) ≤ I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmfR : (m : ℝ) ≤ I2.PT.f E := by exact_mod_cast hmf'
  have hfrR : (2 : ℝ) ≤ I2.PT.f E * r := by exact_mod_cast hfr
  have hfrd : (I2.PT.f E : ℝ) ≤ I2.PT.rd E := by nlinarith
  have hw : (I2.PT.f E : ℝ) ^ ((3 : ℝ) / 2) ≤ (I2.PT.f E : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hfR (by norm_num)
  have hρ0 : 0 < I2.PT.rd E := by linarith
  set S : ℝ := 135 * ((I2.PT.f E : ℝ) * r) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  set B : ℝ := S * (I2.PT.rd E ^ 7) ^ 4 with hB
  have hB1 : 1 ≤ B := by
    have h1 : (1 : ℝ) ≤ (I2.PT.rd E ^ 7) ^ 4 := one_le_pow₀ (one_le_pow₀ (by linarith))
    have h2 : (1 : ℝ) ≤ S := by linarith
    exact one_le_mul_of_one_le_of_one_le h2 h1
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈B⌉₊ * (r + 1) := ⟨_, rfl⟩
  have hqR : (q : ℝ) = (⌈B⌉₊ : ℝ) * (r + 1) := by rw [hq]; push_cast; ring
  have hlo : B * (r + 1) ≤ q := by
    rw [hqR]; gcongr; exact Nat.le_ceil B
  have hqR1 : (1 : ℝ) ≤ q := by nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hqR1
  have hq0 : (0 : ℝ) < q := by linarith
  have hhi : (q : ℝ) ≤ I2.PT.rd E ^ 28 * ((I2.PT.f E : ℝ) * r) ^ 2 * 540 := by
    have h1 : (⌈B⌉₊ : ℝ) ≤ 2 * B := by
      have := Nat.ceil_lt_add_one (show 0 ≤ B by linarith); linarith
    have h2 : (r : ℝ) + 1 ≤ 2 * ((I2.PT.f E : ℝ) * r) := by nlinarith
    calc (q : ℝ) = (⌈B⌉₊ : ℝ) * (r + 1) := hqR
      _ ≤ (2 * B) * (2 * ((I2.PT.f E : ℝ) * r)) := by gcongr
      _ = _ := by rw [hB, hS]; ring
  obtain ⟨c1, c2, c3, c5, c6⟩ := real_bounds (I2.PT.f E) r m (I2.PT.rd E) _ q hfR hrR hmR hmfR hf2 hrd
    (by positivity) hw hlo
  have hb0 : 2 ≤ I2.b0 (E := E) q (Real.sqrt S) := by
    unfold I2.b0 I2.RR; rw [hsq]; exact c2
  have ht0 : (q : ℝ) * 2 ≤ I2.t0 (E := E) q (Real.sqrt S) := by
    unfold I2.t0; gcongr
  have hd : (I2.dstar (E := E) m : ℝ) = 2 * I2.PT.f E * m := by unfold I2.dstar; push_cast; ring
  refine ⟨q, Real.sqrt S, hq1, ?_, ?_⟩
  · have h7 : Real.log 540 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have h3 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by gcongr
      rw [h1]; exact le_trans (by norm_num) h3
    have h1 := Real.log_le_log hq0 hhi
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  · intro X hX hdim
    subst hX
    refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, by linarith, ?_,
      hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
    · rw [hsq, hS]
      unfold I2.PT.gA
      push_cast
      constructor <;> linarith
    · unfold I2.th I2.omStar I2.RR
      rw [Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hq0, hsq, hd]
      exact c1
    · unfold I2.M1
      rw [hd]; exact c3
    · rw [Nat.cast_one, _root_.mul_one, _root_.mul_one, hd]
      linarith
    · unfold I2.PT.gA
      rw [Nat.cast_one, hd]
      push_cast
      linarith

end GlobalTheory.RunParametersBound
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem isHolTo_snd_slice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {e : W → (Sp ℂ ⟶ X)}
    (he : IsHolTo ((Set.univ : Set V) ×ˢ (Set.univ : Set W)) (fun bz => e bz.2)) : IsHolTo Set.univ e := by
  intro U f
  have h := he U f
  have hd : Differentiable ℂ (fun z : W => ((0 : V), z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have hs : {b ∈ (Set.univ : Set W) | ⊤ ≤ e b ⁻¹ᵁ U} = (fun z : W => ((0 : V), z)) ⁻¹'
        {b ∈ (Set.univ : Set V) ×ˢ (Set.univ : Set W) | ⊤ ≤ e b.2 ⁻¹ᵁ U} :=
      Set.ext fun z => ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
    rw [hs]
    exact h.1.preimage hd.continuous
  · exact h.2.comp (f := fun z : W => ((0 : V), z)) hd.differentiableOn
      (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

theorem isHolTo_ex_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty Pm) :
    IsHolTo Set.univ (fun z => (Fu.ex i Pm z).left) := by
  exact isHolTo_snd_slice (e := fun z => (Fu.ex i Pm z).left)
    (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2

theorem isFnOf_entire_factor :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ (s : LB.Sec (PPx (Fu.u i Pm))) (θ : (Fin g → ℂ) → ℂ), IsFnOf Fu i Pm fr (Fu.u i Pm) s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Pm a) = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) + Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * θ z := by
  intro E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF s θ hθ
  obtain ⟨-, -, -, hdf, hne, -, -, hfac⟩ := hF
  let pt : (Fin g → ℂ) → (Sp ℂ ⟶ Gx (Fu.u i Pm)) := fun z =>
    (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left
  have h1 : ∀ z, pt z ≫ gxFst (Fu.u i Pm) = (Fu.ex i Pm z).left := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ snd _ _).left = (Fu.ex i Pm z).left := by
      rw [Out.ptSecT, lift_snd]
    exact this
  have h2 : ∀ z, pt z ≫ gxSnd (Fu.u i Pm) = 𝟙 (Sp ℂ) := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ fst _ _).left = 𝟙 (Sp ℂ) := by
      rw [Out.ptSecT, lift_fst]; rfl
    exact this
  have hex := isHolTo_ex_of_isPeriod Fu i Pm hP
  have hpt : IsHolTo Set.univ pt := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback (p := gxSnd (Fu.u i Pm)) (q := gxFst (Fu.u i Pm))
      (IsPullback.of_hasPullback (Fu.u i Pm) Xo.univ.t.G.hom) ?_ ?_
    · simp only [h2]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
    · simp only [h1]
      exact hex
  have hch : ∀ z, ∃ j, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    have hm : (Fu.ex i Pm z).left (default : PrimeSpectrum ℂ) ∈ ⨆ j, Xo.univ.t.PP.L.U j := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  have hU : ∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ pt z ⁻¹ᵁ (PPx (Fu.u i Pm)).U (fun _ => j) := fun j z h y hy => by
    have h3 := h hy
    rw [← h1] at h3
    exact Set.mem_iInter.2 fun _ => h3
  refine ⟨fun z₀ => ?_, fun a z => ?_⟩
  · obtain ⟨j, hj⟩ := hch z₀
    have ho : IsOpen {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h0 := (hex (Xo.univ.t.PP.L.U j) 0).1
      simp only [Set.mem_univ, true_and] at h0
      exact h0
    have hv : DifferentiableOn ℂ (fun z => valAt' (pt z) ((PPx (Fu.u i Pm)).U fun _ => j) (s.f fun _ => j))
        {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} :=
      (hpt _ (s.f (fun _ => j))).2.mono (fun z hz => ⟨trivial, hU j z hz⟩)
    have hq : DifferentiableOn ℂ θ {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      refine (hv.mul ((hdf j).inv (fun z hz => hne j z hz))).congr fun z hz => ?_
      rw [Pi.mul_apply, Pi.inv_apply, hθ j z (pt z) (h1 z) (h2 z) hz, mul_inv_cancel_right₀ (hne j z hz)]
    exact hq.differentiableAt (ho.mem_nhds hj)
  · obtain ⟨j, hj⟩ := hch z
    have he : Fu.ex i Pm (z + Pm a) = Fu.ex i Pm z := by
      rw [Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP (Pm a)).2 ⟨a, rfl⟩, _root_.mul_one]
    have e1 := hθ j z (pt z) (h1 z) (h2 z) hj
    have e2 := hθ j (z + Pm a) (pt z) (by rw [he]; exact h1 z) (h2 z) (by rw [he]; exact hj)
    have e3 := (hfac a j z).2 hj
    have n2 := hne j (z + Pm a) (by rw [he]; exact hj)
    apply mul_right_cancel₀ n2
    rw [← e2, e1, e3]
    ring

end GlobalTheory.EtaAn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem norm_prod_sum_theta_le_exp_of_card :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (T : I2.PT E) (DF : ℕ) (P : I2.Par T DF) (R i N : ℕ), 2 ≤ R → 1 ≤ N → ∀ s ∈ T.Sec 1 1, T.l2 1 s = 1 → ∀ (G J : Type) [Fintype G] [Fintype J], Fintype.card G = 2 * R ^ 4 * i → Fintype.card J ≤ R ^ (2 * I2.PT.f E * T.r ^ 2) → ∀ (cf : J → ℤ) (w : G → J → Fin T.r → ℂ) (a : G → J → Fin T.r → I2.Vsp T.dim), (∀ j, |cf j| ≤ N) → (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) → (∀ g j, ∀ x ∈ T.L, ∃ c : Fin T.r → 𝓞 E, ∃ y ∈ T.L, x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) → (∀ g j b, ‖w g j b‖ = Real.sqrt (T.ptN2 1 s fun _ => a g j b)) → ‖∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b‖ ≤ Real.exp (-(i : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E T.r P.q P.m R N)) := by
  intro E _ _ _ T DF P R i N hR hN s hs hl G J _ _ hG hJ cf w a hcf ha hsp hw
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [I2.PT.l2, I2.PT.ptN2] at hl
  let eG : Fin (2 * R ^ 4 * i) ≃ G := (Fintype.equivFinOfCardEq hG).symm
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have key := GlobalTheory.norm_prod_sum_theta_le_exp I2.T_holds E T DF P R hR s hs hs0 i N
    (Fintype.card J) hN hJ (fun _ t => (cf (eJ t) : ℂ)) (fun k t => ∏ b, w (eG k) (eJ t) b)
    (fun k t => a (eG k) (eJ t))
    (fun _ t => by
      rw [Complex.norm_intCast]
      exact_mod_cast hcf (eJ t))
    (fun k t => ⟨ha _ _, hsp _ _⟩)
    (fun k t => by
      rw [norm_prod]
      simp [hw, hl])
  have h1 : ∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b =
      ∏ k, ∑ t, (cf (eJ t) : ℂ) * ∏ b, w (eG k) (eJ t) b := by
    rw [← eG.prod_comp]
    exact Finset.prod_congr rfl fun k _ => (eJ.sum_comp _).symm
  rw [h1, neg_mul]
  exact key

end GlobalTheory
end
