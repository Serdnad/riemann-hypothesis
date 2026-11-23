module

public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSum
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZLocLower
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle006
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem sqn_pos_of_ne (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {y : Y} (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  have h0 : 0 < A.nsq la (w k) y := by
    unfold nsq
    have := norm_pos_iff.2 hk
    positivity
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq la (w j) y)
    (fun j _ => A.nsq_nonneg la (w j) y) (Finset.mem_univ k))

theorem sqn_pos_of_notMem (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {s : Fin N → ι → Y → ℂ}
    {y : Y} (h : y ∉ A.zeroSet s) : 0 < A.sqn la s y := by
  apply A.sqn_pos_of_ne
  simpa [zeroSet] using h

theorem setLIntegral_biUnion_le {α κ : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : Finset κ) (U : κ → Set α) (G : α → ℝ≥0∞) :
    ∫⁻ y in ⋃ P ∈ F, U P, G y ∂μ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂μ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem start_int (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu < ⊤)
    (hvan : ∀ P ∈ A.zeroSet s, A.VanishOrd f P (T - n)) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  classical
  set G : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) with hG
  have hloc : ∀ P ∈ A.zeroSet s, ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧ ∫⁻ y in U, G y ∂A.mu < ⊤ :=
    fun P hP => A.local_int hMVI hn hD hf hT hP (hvan P hP)
  choose! U hUo hPU hUint using hloc
  set F := hD.finite_S.toFinset
  set V := ⋃ P ∈ F, U P with hV
  have hVo : IsOpen V := isOpen_biUnion (fun P hP => hUo P ((Set.Finite.mem_toFinset _).1 hP))
  have hSV : A.zeroSet s ⊆ V := fun P hP =>
    Set.mem_biUnion ((Set.Finite.mem_toFinset _).2 hP) (hPU P hP)
  obtain ⟨C, hC⟩ := hD.family_le_coords V hVo hSV
  set a : ℝ := (T : ℝ) - 1 / 2 with ha
  have hpt : ∀ y ∈ Vᶜ, G y ≤ ENNReal.ofReal (C ^ a) *
      ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
    intro y hy
    have hyS : y ∉ A.zeroSet s := fun h => hy (hSV h)
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y hy
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have h1 : A.sqn L s y ^ (-a) ≤ (A.sqn L w y / C) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [div_le_iff₀ hCpos]; linarith)
        (by have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
            linarith)
    have h2 : (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) =
        C ^ a * A.sqn L w y ^ (-(T : ℝ)) := by
      rw [Real.div_rpow hw.le hCpos.le, Real.rpow_neg hCpos.le, div_inv_eq_mul, mul_comm _ (C ^ a),
        mul_assoc, ← Real.rpow_add hw]
      congr 2
      ring
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la f y
    calc A.nsq la f y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))
        ≤ A.nsq la f y * (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) := by
          have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
          gcongr
      _ = C ^ a * (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
          rw [mul_assoc, h2]; ring
  calc ∫⁻ y, G y ∂A.mu = ∫⁻ y in V ∪ Vᶜ, G y ∂A.mu := by
        rw [Set.union_compl_self, Measure.restrict_univ]
    _ ≤ ∫⁻ y in V, G y ∂A.mu + ∫⁻ y in Vᶜ, G y ∂A.mu := lintegral_union_le _ _ _
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y in Vᶜ, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add (setLIntegral_biUnion_le _ _ _ _) (setLIntegral_mono' hVo.measurableSet.compl hpt)
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add le_rfl (setLIntegral_le_lintegral _ _)
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 (fun P hP => hUint P
          ((Set.Finite.mem_toFinset _).1 hP)), ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint⟩

theorem end_int (A : WeightedAtlas n Y ι La) (hn : 1 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {h : ι → Y → ℂ}
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-((n : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu < ⊤ := by
  have : NullSingletonClass A.mu := ⟨fun x => A.mu_singleton hn x⟩
  have hS0 : A.mu (A.zeroSet s) = 0 := hD.finite_S.measure_zero A.mu
  obtain ⟨C, hC⟩ := hD.s_le_w
  set a : ℝ := (n : ℝ) - 1 / 2 with ha
  have hae : ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ≤
      ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with y hyS
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have hna : 0 ≤ a := by
      have : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : (C * A.sqn L w y) ^ (-a) ≤ A.sqn L s y ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hs hCy (by linarith)
    have h2 : A.sqn L w y ^ (-(n : ℝ)) =
        C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
      rw [Real.mul_rpow hCpos.le hw.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hCpos,
        mul_assoc, ← Real.rpow_add hw]
      have e1 : a + -a = 0 := by ring
      have e2 : -a + -(1 / 2 : ℝ) = -(n : ℝ) := by rw [ha]; ring
      rw [e1, e2, Real.rpow_zero, one_mul]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la h y
    have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
    have := Real.rpow_nonneg hCpos.le a
    rw [h2]
    calc A.nsq la h y * (C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))))
        = C ^ a * (A.nsq la h y * (C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          ring
      _ ≤ C ^ a * (A.nsq la h y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          gcongr
  calc ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu
      ≤ ∫⁻ y, ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu := lintegral_mono_ae hae
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

theorem sum_int (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (hh : ∀ q ∈ F, A.IsSec la (h q)) (Wt : Y → ℝ) (hWt : Measurable Wt)
    (hW0 : ∀ y, 0 ≤ Wt y)
    (hint : ∀ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ∂A.mu < ⊤ := by
  have hpt : ∀ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ≤
      ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) := by
    intro y
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (A.nsq_nonneg _ _ _) (hW0 y)),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.nsq_sum_le la F h y) (hW0 y)
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (F.card : ℝ) *
        ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := lintegral_mono hpt
    _ = ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro q hq
        exact (ENNReal.measurable_ofReal.comp
          ((A.continuous_nsq (hh q hq)).measurable.mul hWt)).aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 hint)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

def FOURMulStatement' (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω, ∀ ν : Fin f → ℤ,
      HasSum (fun ν' : Fin f → ℤ => fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν'))
        (fourCoeff (h1 * h2) b ν)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fmLine {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) : (Fin f → ℝ) → ℂ :=
  fun x => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I)

theorem fm_coeff_star {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (i : Fin f → ℤ) :
    conj (UnitAddTorus.mFourierCoeff (⇑(star F)) i) = UnitAddTorus.mFourierCoeff (⇑F) (-i) := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.star_apply, smul_eq_mul, neg_neg]
  rw [← integral_conj]
  congr 1
  funext t
  simp [UnitAddTorus.mFourier_neg]

theorem fm_coeff_shift {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (ν i : Fin f → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(UnitAddTorus.mFourier (-ν) * F)) i =
      UnitAddTorus.mFourierCoeff (⇑F) (i + ν) := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.mul_apply, smul_eq_mul]
  congr 1
  funext t
  rw [neg_add, UnitAddTorus.mFourier_add]
  ring

theorem fm_conv {f : ℕ} (F1 F2 : C(UnitAddTorus (Fin f), ℂ)) (ν : Fin f → ℤ) :
    HasSum (fun ν' => UnitAddTorus.mFourierCoeff (⇑F1) ν' * UnitAddTorus.mFourierCoeff (⇑F2) (ν - ν'))
      (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
  have H := UnitAddTorus.hasSum_prod_mFourierCoeff ((star F1).toLp 2 volume ℂ)
    ((UnitAddTorus.mFourier (-ν) * F2).toLp 2 volume ℂ)
  have H2 : HasSum (fun i => UnitAddTorus.mFourierCoeff (⇑F1) (-i) *
      UnitAddTorus.mFourierCoeff (⇑F2) (i + ν)) (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
    convert (preTransparency := .reducible) H using 1
    · funext i
      rw [UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp, fm_coeff_star,
        fm_coeff_shift]
    · rw [UnitAddTorus.mFourierCoeff]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (star F1),
        ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
          (UnitAddTorus.mFourier (-ν) * F2)] with t h1 h2
      rw [h1, h2]
      simp
      ring
  rw [← (Equiv.neg (Fin f → ℤ)).hasSum_iff]
  convert H2 using 1
  funext i
  simp [sub_neg_eq_add, add_comm]

theorem fm_fourCoeff {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ)
    (hper : ∀ x (n : Fin f → ℤ), fmLine h b (x + fun i => (n i : ℝ)) = fmLine h b x)
    (ν : Fin f → ℤ) :
    fourCoeff h b ν = Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) *
      UnitAddTorus.mFourierCoeff (fsFun (fmLine h b)) ν := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
  have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
      : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [hset, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
  beta_reduce
  rw [h1, fsFun_proj _ hper, smul_eq_mul, fs_mFourier_proj]
  simp only [fmLine]
  rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (-2 * (Real.pi : ℂ) * (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq

theorem four_mul' (f : ℕ) : FOURMulStatement' f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν
  have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
  have hmem : ∀ x : Fin f → ℝ, (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) ∈ tube f Ω := by
    intro x
    show (fun k => ((x k : ℂ) + (b k : ℂ) * Complex.I).im) ∈ Ω
    convert hb using 1
    ext k
    simp [Complex.add_im]
  have hc : ∀ hh : (Fin f → ℂ) → ℂ, DifferentiableOn ℂ hh (tube f Ω) →
      Continuous (fmLine hh b) := by
    intro hh hd
    have hcc : Continuous (fun y : Fin f → ℝ => (fun k => (y k : ℂ) + (b k : ℂ) * Complex.I)) := by
      fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ((hd _ (hmem y)).differentiableAt (hopen.mem_nhds (hmem y))).continuousAt.comp
      hcc.continuousAt
  have hper : ∀ hh : (Fin f → ℂ) → ℂ,
      (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, hh (s + fun k => (m k : ℂ)) = hh s) →
      ∀ x (n : Fin f → ℤ), fmLine hh b (x + fun i => (n i : ℝ)) = fmLine hh b x := by
    intro hh hp x n
    have := hp _ (hmem x) n
    simp only [fmLine]
    convert this using 2
    ext k
    simp only [Pi.add_apply, Complex.ofReal_add]
    have hn : ((n k : ℝ) : ℂ) = (n k : ℂ) := by norm_cast
    rw [hn]
    ring
  have hper12 : ∀ x (n : Fin f → ℤ),
      fmLine (h1 * h2) b (x + fun i => (n i : ℝ)) = fmLine (h1 * h2) b x := by
    intro x n
    show fmLine h1 b _ * fmLine h2 b _ = fmLine h1 b x * fmLine h2 b x
    rw [hper h1 hp1, hper h2 hp2]
  let F1 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h1 b), fsFun_continuous _ (hc h1 hd1) (hper h1 hp1)⟩
  let F2 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h2 b), fsFun_continuous _ (hc h2 hd2) (hper h2 hp2)⟩
  have e12 : fsFun (fmLine (h1 * h2) b) = ⇑F1 * ⇑F2 := rfl
  rw [fm_fourCoeff (h1 * h2) b hper12, e12]
  have H := (fm_conv F1 F2 ν).mul_left (Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)))
  refine H.congr_fun fun ν' => ?_
  rw [fm_fourCoeff h1 b (hper h1 hp1), fm_fourCoeff h2 b (hper h2 hp2)]
  have hE : Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) =
      Complex.exp (2 * Real.pi * ∑ k, (ν' k : ℂ) * (b k : ℂ)) *
        Complex.exp (2 * Real.pi * ∑ k, ((ν - ν') k : ℂ) * (b k : ℂ)) := by
    rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 3
    ext k
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [hE]
  simp only [F1, F2, ContinuousMap.coe_mk]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

section
variable (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La]

end

theorem four_sign_holds (f : ℕ) : FOURSignStatement f :=
  four_sign f (four_indep f) (four_bound f)

end ReciprocityTheory.L2DbarEstimates.Y
end
