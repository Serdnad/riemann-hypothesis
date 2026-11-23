module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

@[expose] public section

section

open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace GlobalTheory.AbsFubini

variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]

lemma lintegral_mul_le_sqrt (ν : Measure Y) {a₁ a₂ : Y → ℝ≥0∞} (h₁ : Measurable a₁) (h₂ : Measurable a₂) :
    ∫⁻ y, a₁ y * a₂ y ∂ν ≤
      (∫⁻ y, a₁ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) * (∫⁻ y, a₂ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two h₁.aemeasurable
    h₂.aemeasurable
  simpa only [Pi.mul_apply] using h

lemma sqrt_le_of_sq_le {I N : ℝ≥0∞} (h : I ≤ N ^ 2) : I ^ (1 / (2:ℝ)) ≤ N := by
  calc I ^ (1 / (2:ℝ)) ≤ (N ^ 2) ^ (1 / (2:ℝ)) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = N := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

lemma lintegral_prod_split {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂)) (y : Y) :
    (∫⁻ x₁, a₁ x₁ y ∂μ₁) * (∫⁻ x₂, a₂ x₂ y ∂μ₂) = ∫⁻ p : X₁ × X₂, a₁ p.1 y * a₂ p.2 y ∂μ₁.prod μ₂ := by
  have m₁ : Measurable fun x => a₁ x y := ha₁.comp (measurable_id.prodMk measurable_const)
  have m₂ : Measurable fun x => a₂ x y := ha₂.comp (measurable_id.prodMk measurable_const)
  exact (lintegral_prod_mul (f := fun x => a₁ x y) (g := fun x => a₂ x y) m₁.aemeasurable
    m₂.aemeasurable).symm

lemma core {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞} {b₁ : X₁ → ℝ≥0∞} {b₂ : X₂ → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂))
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) {N₁ : X₁ → ℝ≥0∞} {N₂ : X₂ → ℝ≥0∞}
    (hN₁ : ∀ x, ∫⁻ y, a₁ x y ^ 2 ∂ν ≤ N₁ x ^ 2) (hN₂ : ∀ x, ∫⁻ y, a₂ x y ^ 2 ∂ν ≤ N₂ x ^ 2) :
    ∫⁻ y, (∫⁻ x₁, a₁ x₁ y * b₁ x₁ ∂μ₁) * (∫⁻ x₂, a₂ x₂ y * b₂ x₂ ∂μ₂) ∂ν ≤
      (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) := by
  have hA₁ : Measurable (Function.uncurry fun x y => a₁ x y * b₁ x) :=
    ha₁.mul (hb₁.comp measurable_fst)
  have hA₂ : Measurable (Function.uncurry fun x y => a₂ x y * b₂ x) :=
    ha₂.mul (hb₂.comp measurable_fst)

  set n₁ : X₁ → ℝ≥0∞ := fun x => (∫⁻ y, a₁ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₁
  set n₂ : X₂ → ℝ≥0∞ := fun x => (∫⁻ y, a₂ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₂
  have mn₁ : Measurable n₁ :=
    ((ha₁.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have mn₂ : Measurable n₂ :=
    ((ha₂.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have nN₁ : ∀ x, n₁ x ≤ N₁ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₁ x)
  have nN₂ : ∀ x, n₂ x ≤ N₂ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₂ x)
  have hsplit := lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁ hA₂
  simp only [hsplit]
  have hG : Measurable (Function.uncurry fun (y : Y) (p : X₁ × X₂) =>
      a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2)) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => a₁ z.2.1 z.1 * b₁ z.2.1 :=
      hA₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => a₂ z.2.2 z.1 * b₂ z.2.2 :=
      hA₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    exact e₁.mul e₂
  rw [lintegral_lintegral_swap hG.aemeasurable]
  calc ∫⁻ p : X₁ × X₂, ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν ∂μ₁.prod μ₂
      ≤ ∫⁻ p : X₁ × X₂, (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) ∂μ₁.prod μ₂ := by
        refine lintegral_mono fun p => ?_
        have m₁ : Measurable fun y => a₁ p.1 y := ha₁.comp (measurable_const.prodMk measurable_id)
        have m₂ : Measurable fun y => a₂ p.2 y := ha₂.comp (measurable_const.prodMk measurable_id)
        calc ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν
            = ∫⁻ y, (b₁ p.1 * b₂ p.2) * (a₁ p.1 y * a₂ p.2 y) ∂ν := by
              congr 1; funext y; ring
          _ = (b₁ p.1 * b₂ p.2) * ∫⁻ y, a₁ p.1 y * a₂ p.2 y ∂ν := lintegral_const_mul _ (m₁.mul m₂)
          _ ≤ (b₁ p.1 * b₂ p.2) * (n₁ p.1 * n₂ p.2) :=
              by gcongr; exact lintegral_mul_le_sqrt ν m₁ m₂
          _ = (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) := by ring
    _ = (∫⁻ x, n₁ x * b₁ x ∂μ₁) * (∫⁻ x, n₂ x * b₂ x ∂μ₂) :=
        lintegral_prod_mul (f := fun x => n₁ x * b₁ x) (g := fun x => n₂ x * b₂ x)
          (mn₁.mul hb₁).aemeasurable (mn₂.mul hb₂).aemeasurable
    _ ≤ (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) :=
        by
          gcongr with x x
          · exact nN₁ x
          · exact nN₂ x

lemma memLp_lift {k : X₁ → Y → ℂ} {u : X₁ → ℂ} (hk : Measurable (Function.uncurry k))
    (hu : Measurable u) {N : X₁ → ℝ≥0∞} (hN : ∀ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂ν ≤ N x ^ 2)
    (hfin : ∫⁻ x, N x * ‖u x‖ₑ ∂μ₁ ≠ ⊤) :
    MemLp (fun y => ∫ x, k x y * u x ∂μ₁) 2 ν := by
  have hF : Measurable fun q : Y × X₁ => k q.2 q.1 * u q.2 :=
    (hk.comp (measurable_snd.prodMk measurable_fst)).mul (hu.comp measurable_snd)
  have hsm : StronglyMeasurable fun y => ∫ x, k x y * u x ∂μ₁ :=
    hF.stronglyMeasurable.integral_prod_right'
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
    hsm.aestronglyMeasurable]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hA : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.enorm
  have hb : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₁) (ν := ν) hA hA hb hb hN hN
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hfin hfin) (le_trans ?_ hc)
  refine lintegral_mono fun y => ?_
  have h1 : ‖∫ x, k x y * u x ∂μ₁‖ₑ ≤ ∫⁻ x, ‖k x y‖ₑ * ‖u x‖ₑ ∂μ₁ := by
    simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (μ := μ₁) (fun x => k x y * u x)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, pow_two]
  exact mul_le_mul' h1 h1

theorem abstract_fubini_two_lifts : ∀ {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (ν : Measure Y) [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
    (k₁ : X₁ → Y → ℂ) (k₂ : X₂ → Y → ℂ) (u₁ : X₁ → ℂ) (u₂ : X₂ → ℂ),
    Measurable (Function.uncurry k₁) → Measurable (Function.uncurry k₂) → Measurable u₁ → Measurable u₂ →
    ∀ (N₁ : X₁ → ENNReal) (N₂ : X₂ → ENNReal),
    (∀ x, ∫⁻ y, ‖k₁ x y‖ₑ ^ 2 ∂ν ≤ N₁ x ^ 2) → (∀ x, ∫⁻ y, ‖k₂ x y‖ₑ ^ 2 ∂ν ≤ N₂ x ^ 2) →
    ∫⁻ x, N₁ x * ‖u₁ x‖ₑ ∂μ₁ ≠ ⊤ → ∫⁻ x, N₂ x * ‖u₂ x‖ₑ ∂μ₂ ≠ ⊤ →
    (∀ y, Integrable (fun x => k₁ x y * u₁ x) μ₁) → (∀ y, Integrable (fun x => k₂ x y * u₂ x) μ₂) →
    MemLp (fun y => ∫ x, k₁ x y * u₁ x ∂μ₁) 2 ν ∧ MemLp (fun y => ∫ x, k₂ x y * u₂ x ∂μ₂) 2 ν ∧
    ∫ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) ∂ν =
      ∫ p : X₁ × X₂, (∫ y, k₁ p.1 y * conj (k₂ p.2 y) ∂ν) * u₁ p.1 * conj (u₂ p.2) ∂μ₁.prod μ₂ := by
  intro X₁ X₂ Y _ _ _ μ₁ μ₂ ν _ _ _ k₁ k₂ u₁ u₂ hk₁ hk₂ hu₁ hu₂ N₁ N₂ hN₁ hN₂ hf₁ hf₂ _ _
  refine ⟨memLp_lift hk₁ hu₁ hN₁ hf₁, memLp_lift hk₂ hu₂ hN₂ hf₂, ?_⟩
  set F : Y → X₁ × X₂ → ℂ := fun y p => k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => k₁ z.2.1 z.1 * u₁ z.2.1 :=
      (hk₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₁.comp (measurable_fst.comp measurable_snd))
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => k₂ z.2.2 z.1 * u₂ z.2.2 :=
      (hk₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₂.comp (measurable_snd.comp measurable_snd))
    exact e₁.mul (Complex.continuous_conj.measurable.comp e₂)
  have hA₁ : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ) := hk₁.enorm
  have hA₂ : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ) := hk₂.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₂) (ν := ν) hA₁ hA₂ hu₁.enorm hu₂.enorm hN₁ hN₂
  have hFi : Integrable (Function.uncurry F) (ν.prod (μ₁.prod μ₂)) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.enorm.aemeasurable]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hc
      (ENNReal.mul_lt_top hf₁.lt_top hf₂.lt_top))
    refine lintegral_congr fun y => ?_
    have hA₁' : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ * ‖u₁ x‖ₑ) :=
      hA₁.mul (hu₁.enorm.comp measurable_fst)
    have hA₂' : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ * ‖u₂ x‖ₑ) :=
      hA₂.mul (hu₂.enorm.comp measurable_fst)
    rw [lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁' hA₂' y]
    refine lintegral_congr fun p => ?_
    simp only [Function.uncurry_apply_pair, hFdef, enorm_mul, RCLike.enorm_conj]
  have hpt : ∀ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) =
      ∫ p, F y p ∂μ₁.prod μ₂ := by
    intro y
    rw [← integral_conj]
    exact (integral_prod_mul (fun x => k₁ x y * u₁ x) (fun x => conj (k₂ x y * u₂ x))).symm
  simp_rw [hpt]
  rw [integral_integral_swap hFi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hFdef]
  have : ∀ y, k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) =
      k₁ p.1 y * conj (k₂ p.2 y) * (u₁ p.1 * conj (u₂ p.2)) := by
    intro y; simp only [map_mul]; ring
  simp_rw [this]
  rw [integral_mul_const]
  ring

end GlobalTheory.AbsFubini
end

section

open MeasureTheory

namespace GlobalTheory.FoldIntegral

theorem integral_integral_eq_pos_sub_neg {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (h : Y × Z → ℝ) (hh : Measurable h)
    (hfin : ∫⁻ y, ∫⁻ s, ‖h (y, s)‖ₑ ∂m ∂ν < ⊤) :
    ∫ y, ∫ s, h (y, s) ∂m ∂ν =
      (∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν).toReal -
        (∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν).toReal := by
  have hN : Measurable fun y => ∫⁻ s, ‖h (y, s)‖ₑ ∂m := hh.enorm.lintegral_prod_right'
  have hp : Measurable fun y => ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m :=
    hh.ennreal_ofReal.lintegral_prod_right'
  have hn : Measurable fun y => ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m :=
    hh.neg.ennreal_ofReal.lintegral_prod_right'
  have bp : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => Real.ofReal_le_enorm _) hfin
  have bn : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s =>
      (Real.ofReal_le_enorm _).trans (enorm_neg _).le) hfin
  rw [← integral_toReal hp.aemeasurable (ae_lt_top hp bp.ne),
    ← integral_toReal hn.aemeasurable (ae_lt_top hn bn.ne),
    ← integral_sub (integrable_toReal_of_lintegral_ne_top hp.aemeasurable bp.ne)
      (integrable_toReal_of_lintegral_ne_top hn.aemeasurable bn.ne)]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    ⟨(hh.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩

theorem clm_integral_integral {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (H : Y × Z → ℂ) (hH : Measurable H)
    (hfin : ∫⁻ y, ∫⁻ s, ‖H (y, s)‖ₑ ∂m ∂ν < ⊤) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, ∫ s, H (y, s) ∂m ∂ν) = ∫ y, ∫ s, L (H (y, s)) ∂m ∂ν := by
  have hN : Measurable fun y => ∫⁻ s, ‖H (y, s)‖ₑ ∂m := hH.enorm.lintegral_prod_right'
  have hI : Integrable (fun y => ∫ s, H (y, s) ∂m) ν :=
    ⟨hH.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
      lt_of_le_of_lt (lintegral_mono fun y => enorm_integral_le_lintegral_enorm _) hfin⟩
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact (L.integral_comp_comm
    ⟨(hH.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩).symm

theorem fold : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  intro α Y Z _ _ _ μ Fs ν m S hS Φ hΦ c hc P hQ G hG hP hfin
  haveI : IsFiniteMeasure (m.restrict S) := ⟨by simpa using hS⟩
  have hint : IntegrableOn G Fs μ := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hQ _ hG.enorm (hP (fun z => ‖z‖ₑ) (by simp))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨hint, ?_⟩
  have hH : Measurable fun p : Y × Z => G (Φ p.1 p.2) := hG.comp hΦ
  have key : ∀ L : ℂ →L[ℝ] ℝ, (∀ z, ‖L z‖ ≤ ‖z‖) →
      L (∫ x in Fs, G x ∂μ) = c * L (∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν) := by
    intro L hL
    have hLm : Measurable L := L.continuous.measurable
    have h1 := clm_integral_integral ν (m.restrict S) _ hH hfin L
    have h2 := integral_integral_eq_pos_sub_neg ν (m.restrict S)
      (fun p : Y × Z => L (G (Φ p.1 p.2))) (hLm.comp hH)
      (lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hL _)) hfin)
    have h3 := hQ (fun x => ENNReal.ofReal (L (G x))) (hLm.comp hG).ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (L z)) (by simp))
    have h4 := hQ (fun x => ENNReal.ofReal (-L (G x))) (hLm.comp hG).neg.ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (-L z)) (by simp))
    simp only at h1 h2
    rw [h1, h2, ← L.integral_comp_comm hint,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp hint), h3, h4,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, mul_sub]
  apply Complex.ext
  · have := key Complex.reCLM (fun z => by simpa using Complex.abs_re_le_norm z)
    simpa using this
  · have := key Complex.imCLM (fun z => by simpa using Complex.abs_im_le_norm z)
    simpa using this

end GlobalTheory.FoldIntegral
end

section

open Matrix Filter Topology

namespace GlobalTheory.UnitaryLog

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma linftyOp_norm_le_mul_of_entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ δ) : ‖A‖ ≤ n * δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : A = 0 := Subsingleton.elim _ _
    simp [this]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (h ⟨0, hn⟩ ⟨0, hn⟩)
  lift δ to NNReal using hδ
  rw [linfty_opNorm_def]
  have key : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ n • δ := by
    refine Finset.sup_le fun i _ => ?_
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => ‖A i j‖₊) δ
      (fun j _ => by exact_mod_cast h i j)
    simpa using this
  have := (NNReal.coe_le_coe.2 key)
  simpa [nsmul_eq_mul] using this

open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma norm_entry_le_linftyOp_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  rw [linfty_opNorm_def]
  calc ‖A i j‖ = ((‖A i j‖₊ : NNReal) : ℝ) := rfl
    _ ≤ ((∑ k, ‖A i k‖₊ : NNReal) : ℝ) := by
      exact_mod_cast Finset.single_le_sum (f := fun k => ‖A i k‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := by
      exact_mod_cast Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)


open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem _root_.GlobalTheory.UnitaryLog.exists_log_unitary (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ →
      (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧
        NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  set L := hf.localInverse _ _ _ with hL
  set φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => G⁻¹ * Xᴴ * G with hφ
  have hφc : Continuous φ :=
    (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  have hφ0 : Tendsto φ (𝓝 0) (𝓝 0) := by
    simpa [φ] using hφc.tendsto 0
  have hleft : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X :=
    hf.eventually_left_inverse
  have hP : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X ∧
      L (NormedSpace.exp (φ X)) = φ X ∧ L (NormedSpace.exp (-X)) = -X :=
    hleft.and ((hφ0.eventually hleft).and
      ((continuous_neg.tendsto' (0 : Matrix (Fin n) (Fin n) ℂ) 0 neg_zero).eventually hleft))
  obtain ⟨K, s, hs, hK⟩ := hf.to_localInverse.exists_lipschitzOnWith
  have hQ := hf.eventually_right_inverse.and ((hf.localInverse_tendsto.eventually hP).and hs)
  have hL1 : L (NormedSpace.exp 0) = 0 := hf.localInverse_apply_image
  have hs1 : NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) ∈ s := mem_of_mem_nhds hs
  rw [NormedSpace.exp_zero] at hQ hL1 hs1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hQ
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  refine ⟨ε / (2 * ((n : ℝ) + 1)), K * n, by positivity, ?_⟩
  intro u δ hu hδ hentry
  have hnorm : ‖u - 1‖ ≤ n * δ := linftyOp_norm_le_mul_of_entry_le _ δ hentry
  have hsmall : (n : ℝ) * (ε / (2 * ((n : ℝ) + 1))) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith
  have hdist : dist u 1 < ε := by
    rw [dist_eq_norm]
    calc ‖u - 1‖ ≤ n * δ := hnorm
      _ ≤ n * (ε / (2 * ((n : ℝ) + 1))) := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg n)
      _ < ε := hsmall
  obtain ⟨hexp, ⟨hX, hXφ, hXneg⟩, hus⟩ := hball hdist
  refine ⟨L u, ?_, hexp, ?_⟩
  · have hGu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hG
    have hinv : u⁻¹ = G⁻¹ * uᴴ * G := by
      apply Matrix.inv_eq_left_inv
      have hu' := hu
      simp only [Matrix.mul_assoc] at hu' ⊢
      rw [hu', Matrix.nonsing_inv_mul G hG]
    have hexpφ : NormedSpace.exp (φ (L u)) = NormedSpace.exp (-L u) := by
      rw [Matrix.exp_neg, hexp, hinv]
      simp only [φ]
      rw [Matrix.exp_conj' G _ hGu, Matrix.exp_conjTranspose, hexp]
    have heq : φ (L u) = -L u := by
      rw [← hXφ, ← hXneg, hexpφ]
    calc (L u)ᴴ * G + G * L u = G * φ (L u) + G * L u := by
          simp only [φ]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
            Matrix.one_mul]
      _ = 0 := by rw [heq, Matrix.mul_neg, neg_add_cancel]
  · intro i j
    calc ‖L u i j‖ ≤ ‖L u‖ := norm_entry_le_linftyOp_norm _ i j
      _ = dist (L u) (L 1) := by rw [hL1, dist_zero_right]
      _ ≤ K * dist u 1 := hK.dist_le_mul u hus 1 hs1
      _ ≤ K * (n * δ) := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
      _ = K * n * δ := by ring

end GlobalTheory.UnitaryLog
end

section

namespace GlobalTheory.ExpPow

theorem int_eq_zero_of_exp_I_mul (m : ℤ) (h : Complex.exp (Complex.I * m) = 1) : m = 0 := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h1 : (m : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  by_contra hm
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact hm (by exact_mod_cast h1)
  apply irrational_pi
  refine ⟨(m : ℚ) / (2 * n), ?_⟩
  push_cast
  rw [h1]
  field_simp

theorem exp_I_pow_injective (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul] at h
  have h2 : Complex.exp (Complex.I * (((a : ℤ) - b : ℤ) : ℂ)) = 1 := by
    have : Complex.I * (((a : ℤ) - b : ℤ) : ℂ) = a * Complex.I - b * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  have := int_eq_zero_of_exp_I_mul _ h2
  omega

theorem pow_exp_I_or_inv_injective :
    ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) →
      w ^ a = w ^ b → a = b := by
  rintro a b w (rfl | rfl) h
  · exact exp_I_pow_injective a b h
  · rw [inv_pow, inv_pow, inv_inj] at h
    exact exp_I_pow_injective a b h

end GlobalTheory.ExpPow
end

section

-- Interpret the original scalar argument as the identity ring homomorphism.
local notation:max "MultilinearMap" R:max M:max N:max =>
  _root_.MultilinearMap (RingHom.id R) M N


theorem _root_.GlobalTheory.T.finiteDimensional_span_multilinear_values' : ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F) (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) → FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  letI : ∀ i, FiniteDimensional ℂ (W i) := hW
  let restricted : (∀ i, W i) →ₘₗ[ℂ] F := T.compLinearMap (fun i => (W i).subtype)
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (PiTensorProduct.lift restricted))
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ (fun i => ⟨v i, hv i⟩), ?_⟩
  rw [PiTensorProduct.lift.tprod]
  rfl
end

section

namespace GlobalTheory

def chainEdge (k : ℕ) {r : ℕ} (i j : Fin r) : Prop := j.val = i.val + 1 ∧ i.val + 1 ≠ k

instance (k : ℕ) {r : ℕ} : DecidableRel (chainEdge k (r := r)) := fun i j =>
  inferInstanceAs (Decidable (j.val = i.val + 1 ∧ i.val + 1 ≠ k))

end GlobalTheory
end
