module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle248
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem exists_least_argmax_of_tendsto_zero (b : ℕ → ℝ) (h0 : ∀ i, 0 ≤ b i)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0)) :
    ∃ i₀, (∀ i, b i ≤ b i₀) ∧ ∀ i < i₀, b i < b i₀ := by
  have hex : ∃ i, ∀ j, b j ≤ b i := by
    by_cases hpos : ∃ k, 0 < b k
    · obtain ⟨k, hk⟩ := hpos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hb.eventually (gt_mem_nhds hk))
      obtain ⟨i, hi, hmax⟩ := (Finset.range (max N (k + 1))).exists_max_image b
        ⟨k, Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))⟩
      refine ⟨i, fun j => ?_⟩
      by_cases hj : j < max N (k + 1)
      · exact hmax j (Finset.mem_range.2 hj)
      · have hjN : N ≤ j := le_trans (le_max_left _ _) (not_lt.1 hj)
        have hkmem : k ∈ Finset.range (max N (k + 1)) :=
          Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))
        exact (hN j hjN).le.trans (hmax k hkmem)
    · push Not at hpos
      exact ⟨0, fun j => (hpos j).trans (h0 0)⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩
  have hle : b i ≤ b (Nat.find hex) := Nat.find_spec hex i
  refine lt_of_le_of_ne hle fun heq => Nat.find_min hex hi ?_
  intro j
  rw [heq]
  exact Nat.find_spec hex j

theorem BddSer.tendsto_weighted {K : Type*} [NormedField K] {f : PowerSeries K} (hf : BddSer f)
    {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    Filter.Tendsto (fun i => ‖PowerSeries.coeff i f‖ * ρ ^ i) Filter.atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := hf
  have hlim : Filter.Tendsto (fun i : ℕ => B * ρ ^ i) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul B
  exact squeeze_zero (fun i => by positivity)
    (fun i => mul_le_mul_of_nonneg_right (hB i) (pow_nonneg h0.le i)) hlim

private lemma norm_finset_sum_lt_of_ultrametric {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}
    (s : Finset ι) (x : ι → K) {D : ℝ} (hD : 0 < D) (hx : ∀ p ∈ s, ‖x p‖ < D) :
    ‖∑ p ∈ s, x p‖ < D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hD
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact hx a (Finset.mem_insert_self a s)
    · exact ih fun p hp => hx p (Finset.mem_insert_of_mem hp)

theorem norm_coeff_mul_weighted_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (i j : ℕ) :
    (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
  set A : ℕ → ℝ := fun k => ‖PowerSeries.coeff k f‖ * ρ ^ k with hAdef
  set B : ℕ → ℝ := fun k => ‖PowerSeries.coeff k g‖ * ρ ^ k with hBdef
  have hA0 : ∀ k, 0 ≤ A k := fun k => by positivity
  have hB0 : ∀ k, 0 ≤ B k := fun k => by positivity
  obtain ⟨i₀, hAi, hAlt⟩ := exists_least_argmax_of_tendsto_zero A hA0 (hf.tendsto_weighted h0 h1)
  obtain ⟨j₀, hBj, hBlt⟩ := exists_least_argmax_of_tendsto_zero B hB0 (hg.tendsto_weighted h0 h1)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hstep : A i * B j ≤ A i₀ * B j₀ := mul_le_mul (hAi i) (hBj j) (hB0 j) (hA0 i₀)
  change A i * B j ≤ c
  refine hstep.trans ?_
  rcases (mul_nonneg (hA0 i₀) (hB0 j₀)).eq_or_lt with hz | hpos
  · rw [← hz]; exact hc0
  have hApos : 0 < A i₀ := lt_of_le_of_ne (hA0 i₀) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl 0 hpos
  have hBpos : 0 < B j₀ := lt_of_le_of_ne (hB0 j₀) fun h => by rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos
  set n := i₀ + j₀ with hn
  have hρn : 0 < ρ ^ n := pow_pos h0 n
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      A p.1 * B p.2 = ‖PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ * ρ ^ n := by
    intro p hp
    rw [← hp, norm_mul, pow_add]
    simp only [hAdef, hBdef]
    ring
  set D := PowerSeries.coeff i₀ f * PowerSeries.coeff j₀ g with hDdef
  have hDA : A i₀ * B j₀ = ‖D‖ * ρ ^ n := hterm (i₀, j₀) rfl
  have hDpos : 0 < ‖D‖ := by
    have : 0 < ‖D‖ * ρ ^ n := hDA ▸ hpos
    exact pos_of_mul_pos_left this hρn.le
  have hmem : (i₀, j₀) ∈ Finset.HasAntidiagonal.antidiagonal n := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
  have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
      PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ < ‖D‖ := by
    refine norm_finset_sum_lt_of_ultrametric _ _ hDpos fun p hp => ?_
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have hlt : A p.1 * B p.2 < A i₀ * B j₀ := by
      rcases lt_trichotomy p.1 i₀ with h | h | h
      · calc A p.1 * B p.2 ≤ A p.1 * B j₀ := mul_le_mul_of_nonneg_left (hBj _) (hA0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_right (hAlt _ h) hBpos
      · exfalso
        apply hne
        ext
        · exact h
        · simp only; omega
      · have h2 : p.2 < j₀ := by omega
        calc A p.1 * B p.2 ≤ A i₀ * B p.2 := mul_le_mul_of_nonneg_right (hAi _) (hB0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_left (hBlt _ h2) hApos
    rw [hterm p hsum, hDA] at hlt
    exact lt_of_mul_lt_mul_right hlt hρn.le
  have hcoeff : PowerSeries.coeff n (f * g) =
      D + ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g := by
    rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem]
  have hDle : ‖D‖ ≤ ‖PowerSeries.coeff n (f * g)‖ := by
    by_contra hcon
    push Not at hcon
    have hD : D = PowerSeries.coeff n (f * g) + -(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) := by
      rw [hcoeff]; ring
    have := IsUltrametricDist.norm_add_le_max (PowerSeries.coeff n (f * g))
      (-(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))
    rw [← hD, norm_neg] at this
    exact lt_irrefl _ (lt_of_le_of_lt this (max_lt hcon hrest))
  rw [hDA]
  calc ‖D‖ * ρ ^ n ≤ c * ρ ^ n := mul_le_mul_of_nonneg_right (hDle.trans (hc n)) hρn.le
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0.le h1.le) hc0
    _ = c := mul_one c

theorem norm_coeff_mul_norm_coeff_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) (i j : ℕ) :
    ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  have ht : Filter.Tendsto
      (fun ρ : ℝ => (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((‖PowerSeries.coeff i f‖ * 1 ^ i) * (‖PowerSeries.coeff j g‖ * 1 ^ j))) :=
    ((Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ ρ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact norm_coeff_mul_weighted_le f g c hf hg hc hρ.1 hρ.2 i j
  simpa using le_of_tendsto ht hev

theorem sup_norm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ),
    BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) →
      ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  intro p _ f g c hf hg hc i j
  exact norm_coeff_mul_norm_coeff_le f g c hf hg hc i j

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.SerTransport

open PowerSeries

theorem taylorCoeff_add_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z + G z) n = coef1 F n + coef1 G n := by
  simp only [coef1]
  rw [iteratedDeriv_fun_add hF.contDiff.contDiffAt hG.contDiff.contDiffAt, add_div]

theorem taylorCoeff_mul_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z * G z) n =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, coef1 F q.1 * coef1 G q.2 := by
  simp only [coef1]
  rw [iteratedDeriv_fun_mul hF.contDiff.contDiffAt hG.contDiff.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : ((n.choose i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← e]
  field_simp

theorem taylorCoeff_const_function (c : ℂ) (n : ℕ) : coef1 (fun _ => c) n = if n = 0 then c else 0 := by
  simp only [coef1, iteratedDeriv_const]
  split_ifs with h
  · simp [h]
  · simp

theorem taylorCoeff_zero_eq_value (F : ℂ → ℂ) : coef1 F 0 = F 0 := by simp [coef1]

theorem taylorCoeff_scale_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (β : ℂ) (n : ℕ) :
    coef1 (fun z => F (β * z)) n = β ^ n * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_comp_const_mul hF.contDiff]
  simp [mul_div_assoc]

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem coeff_padicTransportSeries (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (n : ℕ) :
    coeff n (GL3Theta.ser1 lam F) = lamC lam (coef1 F n) := by
  simp [GL3Theta.ser1, coef1]

theorem exists_coef {F : ℂ → ℂ} (hF : AlgEnt F) : ∃ a : ℕ → Qbar, ∀ n, coef1 F n = a n :=
  ⟨fun n => ⟨_, hF.2 n⟩, fun _ => rfl⟩

theorem padicTransportSeries_add (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z + G z) ∧
      GL3Theta.ser1 lam (fun z => F z + G z) = GL3Theta.ser1 lam F + GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z + G z) n = ((a n + b n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_add_entire hF.1 hG.1, ha, hb]; rfl
  refine ⟨⟨hF.1.add hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [map_add (f := _), coeff_padicTransportSeries, e, ha, hb, lamC_coe]

theorem padicTransportSeries_mul (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z * G z) ∧
      GL3Theta.ser1 lam (fun z => F z * G z) = GL3Theta.ser1 lam F * GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z * G z) n =
      ((∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, a q.1 * b q.2 : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_mul_entire hF.1 hG.1]
    simp [ha, hb]
  refine ⟨⟨hF.1.mul hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n

  simp only [coeff_mul, coeff_padicTransportSeries, e, ha, hb, lamC_coe, map_sum, map_mul]

theorem padicTransportSeries_const (lam : Qbar →+* ℂ_[p]) {c : ℂ} (hc : c ∈ Qbar) :
    AlgEnt (fun _ => c) ∧ GL3Theta.ser1 lam (fun _ => c) = C (lamC lam c) := by
  refine ⟨⟨differentiable_const c, fun n => ?_⟩, ?_⟩
  · rw [taylorCoeff_const_function]
    split_ifs
    exacts [hc, zero_mem _]
  · ext n
    rw [coeff_padicTransportSeries, taylorCoeff_const_function, coeff_C]
    split_ifs
    · rfl
    · exact (lamC_coe lam 0).trans (map_zero lam)

theorem taylorSeriesInParameter_rescale_of_algebraic (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) {β : ℂ} (hβ : β ∈ Qbar) :
    AlgEnt (fun z => F (β * z)) ∧
      GL3Theta.ser1 lam (fun z => F (β * z)) = rescale (lamC lam β) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, rfl⟩ : ∃ b : Qbar, (b : ℂ) = β := ⟨⟨β, hβ⟩, rfl⟩
  have e : ∀ n, coef1 (fun z => F (b * z)) n = ((b ^ n * a n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_scale_entire hF.1, ha]
    simp
  refine ⟨⟨hF.1.comp (by fun_prop), fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [coeff_rescale, coeff_padicTransportSeries, e, ha, lamC_coe, map_pow, map_mul]

theorem const_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    constantCoeff (f.subst a : PowerSeries ℂ_[p]) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

theorem one_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    coeff 1 (f.subst a : PowerSeries ℂ_[p]) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, const_subst ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

variable (g : GL3Theta.G1 p)

theorem const_l : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem const_Cl (c : ℂ_[p]) : constantCoeff (C c * g.l) = 0 := by
  rw [map_mul, const_l, mul_zero]

theorem atU_eq (F : ℂ → ℂ) : g.atU F =
    subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l : PowerSeries ℂ_[p]) (GL3Theta.ser1 g.lam F) := rfl

theorem mulBy_X (c : ℂ_[p]) : (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
    subst (C c * g.l : PowerSeries ℂ_[p]) g.ex := by
  have : g.lg (GL3Theta.Xv ()) = g.l := X_subst g.l
  rw [GL3Theta.G1.mulBy, this]
  rfl

theorem transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), (∀ F G : ℂ → ℂ, AlgEnt F → AlgEnt G → (AlgEnt (fun z => F z * G z) ∧ g.atU (fun z => F z * G z) = g.atU F * g.atU G) ∧ (AlgEnt (fun z => F z + G z) ∧ g.atU (fun z => F z + G z) = g.atU F + g.atU G)) ∧ (∀ c ∈ Qbar, AlgEnt (fun _ => c) ∧ g.atU (fun _ => c) = PowerSeries.C (lamC g.lam c)) ∧ (∀ F : ℂ → ℂ, AlgEnt F → F 0 ∈ Qbar ∧ PowerSeries.constantCoeff (g.atU F) = lamC g.lam (F 0)) ∧ (g.Ok → ∀ β ∈ Qbar, ∃ h : PowerSeries ℂ_[p], h = (g.mulBy (lamC g.lam β) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧ PowerSeries.constantCoeff h = 0 ∧ PowerSeries.coeff 1 h = lamC g.lam β ∧ ∀ F : ℂ → ℂ, AlgEnt F → AlgEnt (fun z => F (β * z)) ∧ g.atU (fun z => F (β * z)) = PowerSeries.subst h (g.atU F)) := by
  intro p _ g
  have hs := HasSubst.of_constantCoeff_zero' (const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  refine ⟨fun F G hF hG => ⟨⟨(padicTransportSeries_mul g.lam hF hG).1, ?_⟩, (padicTransportSeries_add g.lam hF hG).1, ?_⟩,
    fun c hc => ⟨(padicTransportSeries_const g.lam hc).1, ?_⟩, fun F hF => ⟨taylorCoeff_zero_eq_value F ▸ hF.2 0, ?_⟩, fun hg β hβ => ?_⟩
  · simp only [atU_eq, (padicTransportSeries_mul g.lam hF hG).2, subst_mul hs]
  · simp only [atU_eq, (padicTransportSeries_add g.lam hF hG).2, subst_add hs]
  · rw [atU_eq, (padicTransportSeries_const g.lam hc).2, subst_C]; rfl
  · rw [atU_eq, const_subst (const_Cl g _), ← coeff_zero_eq_constantCoeff_apply, coeff_padicTransportSeries, taylorCoeff_zero_eq_value]
  · set b := lamC g.lam β with hb
    have hbl := HasSubst.of_constantCoeff_zero' (const_Cl g b)
    have he := HasSubst.of_constantCoeff_zero' hg.2.2.1
    have h0 : constantCoeff (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) = 0 := by
      rw [const_subst (const_Cl g b), hg.2.2.1]
    have hh := HasSubst.of_constantCoeff_zero' h0
    refine ⟨subst (C b * g.l : PowerSeries ℂ_[p]) g.ex, (mulBy_X g b).symm, h0, ?_, fun F hF =>
      ⟨(taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).1, ?_⟩⟩
    · have e := congrArg (coeff 1) hg.2.2.2
      rw [one_subst hg.2.2.1, coeff_one_X] at e
      rw [one_subst (const_Cl g b), coeff_C_mul]
      linear_combination b * e
    · have e : subst (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) g.l = C b * g.l := by
        rw [← subst_comp_subst_apply he hbl, hg.2.2.2, subst_X hbl]
      rw [atU_eq, atU_eq, (taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).2, rescale_eq_subst,
        subst_comp_subst_apply (HasSubst.smul_X' _) hs, subst_comp_subst_apply hs hh,
        subst_smul hs, subst_X hs, subst_mul hh, e, subst_C]
      congr 1
      rw [smul_eq_C_mul]
      exact mul_left_comm _ _ _

end GlobalTheory.SerTransport
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_two_Cp_eq_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ((2 : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := (map_natCast _ 2).symm
  have h2 : (2 : ℂ_[p]) = ((2 : ℕ) : ℂ_[p]) := by norm_num
  rw [h2, h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp

theorem intSer_of_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (H : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff H = 1) (hH : IntSer (H ^ 2)) : IntSer H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, h0]
    set f : ℕ × ℕ → ℂ_[p] := fun q => PowerSeries.coeff q.1 H * PowerSeries.coeff q.2 H with hf
    have hsq : PowerSeries.coeff n (H ^ 2) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q := by
      rw [pow_two, PowerSeries.coeff_mul]
    have m1 : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    have m2 : (n, (0 : ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n) := by
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, add_zero, and_true, ne_eq, Prod.mk.injEq]
      omega
    have c0 : PowerSeries.coeff 0 H = 1 := by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0
    set S := ∑ q ∈ ((Finset.HasAntidiagonal.antidiagonal n).erase (0, n)).erase (n, 0), f q with hS
    have hdec : PowerSeries.coeff n (H ^ 2) = 2 * PowerSeries.coeff n H + S := by
      rw [hsq, ← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2]
      simp only [hf, c0, one_mul, mul_one]
      ring
    have hSle : ‖S‖ ≤ 1 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro q hq
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a, b⟩ := q
      simp only [Prod.mk.injEq, Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2 hq3
      have ha : a < n := by omega
      have hb : b < n := by omega
      simp only [hf, norm_mul]
      exact mul_le_one₀ (ih a ha) (norm_nonneg _) (ih b hb)
    have h2 : ‖2 * PowerSeries.coeff n H‖ = ‖PowerSeries.coeff n H‖ := by
      rw [norm_mul, norm_two_Cp_eq_one p hp, one_mul]
    have e : 2 * PowerSeries.coeff n H = PowerSeries.coeff n (H ^ 2) - S := by rw [hdec]; ring
    rw [← h2, e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hH n) ?_)
    rw [norm_neg]; exact hSle

theorem intSer_of_sq_main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p],
    PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H :=
  fun p _ hp H h0 hH => intSer_of_sq p hp H h0 hH

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem GlobalTheory.torsion_parallelogram_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  intro Λ _ N hN M h0 _ hlaw t ht
  by_cases hQ : t ∈ Λ
  · exact h0 t hQ
  have key : ∀ k : ℕ, M ((k:ℂ) * t) = (k:ℝ)^2 * M t ∧
      M (((k:ℂ)+1) * t) = ((k:ℝ)+1)^2 * M t := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [h0 0 (zero_mem Λ)]
      · simp
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have hmem : (N:ℂ) * (((k:ℂ)+1) * t) ∈ Λ := by
        have e : (N:ℂ) * (((k:ℂ)+1) * t) = (k+1 : ℕ) • ((N:ℂ) * t) := by
          rw [nsmul_eq_mul]; push_cast; ring
        rw [e]; exact AddSubgroup.nsmul_mem Λ ht _
      have h := hlaw (((k:ℂ)+1) * t) t hmem ht hQ
      have e1 : ((k:ℂ)+1) * t + t = ((k:ℂ)+1+1) * t := by ring
      have e2 : ((k:ℂ)+1) * t - t = (k:ℂ) * t := by ring
      rw [e1, e2, ih.1, ih.2] at h
      push_cast
      linear_combination h
  have h1 := (key N).1
  rw [h0 _ ht] at h1
  have hN' : (N:ℝ)^2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h1.symm).resolve_left hN'
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

def sqThD (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (GlobalTheory.EvenTheta.sqTh Λ v) z - 2 * deriv (sgStar Λ) z * GlobalTheory.EvenTheta.sqTh Λ v z

end GlobalTheory.ThetaTransl
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_generator_cmDifferentIdealScaled : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ t₀ ∈ Iid D cc, (∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) ∧ ∀ θ : D.host.E, ¬ IntE D θ → (∀ p ∈ P, IntE D (p • θ)) → ∀ a : 𝓞 D.host.E, a • (t₀ * θ) ∈ Iid D cc → a ∈ P := by
  first | exact @GlobalTheory.IdealGenerator.exists_generator_Iid | exact GlobalTheory.IdealGenerator.exists_generator_Iid | (intros; apply GlobalTheory.IdealGenerator.exists_generator_Iid <;> assumption)
end
