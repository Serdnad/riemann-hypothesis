module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.FactorNonneg
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Formalism.PeriodIntegrals.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsWtOnIffOfTorus
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle011
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PowerSeries.Inverse
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle001
import Formalism.RealPlaceAnalysis.Bundle001

@[expose] public section

section

open Finset

noncomputable section

namespace GlobalTheory.WigSh

theorem prod_other_neighbour_raise {n : ℕ} (d : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (hd : ∀ i, 0 < d i) (hl : d l = 1) :
    (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) * (d 0 * d (Fin.last n))
      = ∏ j : Fin n, d (l.succAbove j) := by
  have hP : ∏ i, d i = ∏ j : Fin n, d (l.succAbove j) := by
    rw [Fin.prod_univ_succAbove d l, hl, one_mul]
  have h1 := Fin.prod_univ_succ d
  have h2 := Fin.prod_univ_castSucc d
  have h3 : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j) = (∏ j : Fin n, d j.succ) * ∏ j : Fin n, d j.castSucc := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold Fin.succAbove
    split_ifs
    · rfl
    · exact mul_comm _ _
  have hpos : 0 < ∏ j : Fin n, d (l.succAbove j) := Finset.prod_pos fun j _ => hd _
  apply mul_right_cancel₀ hpos.ne'
  calc _ = ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j)) * (d 0 * d (Fin.last n)) := by ring
    _ = (d 0 * ∏ j : Fin n, d j.succ) * ((∏ j : Fin n, d j.castSucc) * d (Fin.last n)) := by
      rw [h3]; ring
    _ = _ := by rw [← h1, ← h2, hP]

theorem inv_sq_le_wP (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hL : StrictAnti L) (hM : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l + 1) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hn : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ wP L M l := by
  set e : Fin (n + 1) → ℤ := fun i => max |L i - L l| 1 with he
  set d : Fin (n + 1) → ℝ := fun i => (e i : ℝ) with hd
  have hdpos : ∀ i, 0 < d i := fun i => by
    have : 0 < e i := lt_of_lt_of_le one_pos (le_max_right _ _)
    simp only [hd]; exact_mod_cast this
  have hdl : d l = 1 := by simp [hd, he]
  have key := prod_other_neighbour_raise d l hdpos hdl
  have hd0 : d 0 ≤ D := by
    have a : L l ≤ L 0 := hL.antitone (Fin.zero_le _)
    have a' : (L l : ℝ) ≤ L 0 := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonneg (by linarith)]; exact h0) hD
  have hdn : d (Fin.last n) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hL.antitone (Fin.le_last _)
    have a' : (L (Fin.last n) : ℝ) ≤ L l := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonpos (by linarith)]; linarith) hD
  have hden : ∏ j : Fin n, |(L (l.succAbove j) : ℝ) - L l| = ∏ j : Fin n, d (l.succAbove j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    have a : L (l.succAbove j) ≠ L l := fun h => Fin.succAbove_ne l j (hL.injective h)
    have b : 1 ≤ |L (l.succAbove j) - L l| := Int.one_le_abs (sub_ne_zero.2 a)
    simp only [hd, he, max_eq_left b]
    push_cast
    rfl
  have hnum : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      ≤ ∏ j : Fin n, |(M j : ℝ) - 1 - L l| := by
    refine Finset.prod_le_prod₀ (fun j _ => (hdpos _).le) fun j _ => ?_
    obtain ⟨h1, h2⟩ := hM j
    have h3 := hne j
    have : e (if j.castSucc < l then j.succ else j.castSucc) ≤ |M j - 1 - L l| := by
      split_ifs with hl
      · have a2 : L l ≤ L j.succ := hL.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
        simp only [he]
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
        omega
      · have a2 : L j.castSucc ≤ L l := hL.antitone (not_lt.1 hl)
        simp only [he]
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
        omega
    simp only [hd]
    exact_mod_cast this
  rw [← abs_of_nonneg (Model.placeWeight_nonneg hM l)]
  unfold wP
  rw [Model.prod_erase_eq, abs_div, Finset.abs_prod, Finset.abs_prod, hden, ← key]
  have hQ : 0 < ∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc) :=
    Finset.prod_pos fun j _ => hdpos _
  have hm : d 0 * d (Fin.last n) ≤ D ^ 2 := by
    rw [sq]; exact mul_le_mul hd0 hdn (hdpos _).le (by linarith)
  have hmpos : 0 < d 0 * d (Fin.last n) := mul_pos (hdpos _) (hdpos _)
  calc (D ^ 2)⁻¹ ≤ (d 0 * d (Fin.last n))⁻¹ := inv_anti₀ hmpos hm
    _ = (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) /
        ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
          * (d 0 * d (Fin.last n))) := by
      rw [div_mul_eq_div_div, div_self hQ.ne', one_div]
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hQ hmpos).le

end GlobalTheory.WigSh
end
end

section


theorem _root_.GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wM | exact GlobalTheory.WigSh.inv_sq_le_wM | (intros; apply GlobalTheory.WigSh.inv_sq_le_wM <;> assumption)
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  first | exact @GlobalTheory.ConvSer.Bridge.csub_bridge | exact GlobalTheory.ConvSer.Bridge.csub_bridge | (intros; apply GlobalTheory.ConvSer.Bridge.csub_bridge <;> assumption)
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.formalGroupNatMulSeries_properties : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (nMul F n) = 0 ∧ PowerSeries.coeff 1 (nMul F n) = (n : R)) ∧ nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = nMul F (i + j)) ∧ (∀ i j, (nMul F i).subst (nMul F j) = nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (nMul F n) = nMul (F.map φ) n) := by
  first | exact @GlobalTheory.ConvSer.nMul_props | exact GlobalTheory.ConvSer.nMul_props | (intros; apply GlobalTheory.ConvSer.nMul_props <;> assumption)
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_integral_coeff_interpolation_bivariate_series : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (S : Finset K) (H : MvPowerSeries (Fin 2) K), (∀ x ∈ S, ‖x‖ < 1) → Intg H → ∃ c : Fin S.card → Fin S.card → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ x ∈ S, ∀ y ∈ S, ev H ![x, y] = ∑ a, ∑ b, c a b * x ^ (a : ℕ) * y ^ (b : ℕ) := by
  first | exact @GlobalTheory.ConvSer.exists_integral_interpolation_two | exact GlobalTheory.ConvSer.exists_integral_interpolation_two | (intros; apply GlobalTheory.ConvSer.exists_integral_interpolation_two <;> assumption)
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K), Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ ev1 h x = 0) → (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card, ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  first | exact @GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | exact GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | (intros; apply GlobalTheory.ConvSer.norm_coeff_le_prod_zeros <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem dvd_aeval_sub_aeval_two {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a u w u' w' : A) (hu : a ∣ u - u') (hw : a ∣ w - w') (P : MvPolynomial (Fin 2) K) :
    a ∣ MvPolynomial.aeval ![u, w] P - MvPolynomial.aeval ![u', w'] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr =>
    have := dvd_add hp hr
    simp only [map_add (f := _)]
    convert this using 1
    ring
  | mul_X p i hp =>
    have hi : a ∣ (![u, w] i) - (![u', w'] i) := by
      fin_cases i
      · simpa using hu
      · simpa using hw
    have := dvd_add (hp.mul_right (![u, w] i)) (hi.mul_left (MvPolynomial.aeval ![u', w'] p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem X_pow_succ_dvd_of_DT {q : ℕ} [Fact q.Prime] (f : ℂ_[q]⟦X⟧) (n : ℕ)
    (h0 : constantCoeff f = 0) (hD : (X : ℂ_[q]⟦X⟧) ^ n ∣ DT f) :
    (X : ℂ_[q]⟦X⟧) ^ (n + 1) ∣ f := by
  have hu : IsUnit (1 + X : ℂ_[q]⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  unfold DT at hD
  rw [hu.dvd_mul_left, X_pow_dvd_iff] at hD
  rw [X_pow_dvd_iff]
  intro m hm
  cases m with
  | zero => simpa using h0
  | succ k =>
    have := hD k (by omega)
    rw [coeff_derivative] at this
    have hk : ((k : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp this).resolve_right hk

theorem ode_unique : ∀ (q : ℕ) [Fact q.Prime] (P₁ P₂ : MvPolynomial (Fin 2) ℂ_[q]) (u w u' w' : ℂ_[q]⟦X⟧), DT u = MvPolynomial.aeval ![u, w] P₁ → DT w = MvPolynomial.aeval ![u, w] P₂ → DT u' = MvPolynomial.aeval ![u', w'] P₁ → DT w' = MvPolynomial.aeval ![u', w'] P₂ → constantCoeff u = constantCoeff u' → constantCoeff w = constantCoeff w' → u = u' ∧ w = w' := by
  intro q _ P₁ P₂ u w u' w' h1 h2 h3 h4 hu hw
  have hsub : ∀ f g : ℂ_[q]⟦X⟧, DT (f - g) = DT f - DT g := by
    intro f g
    unfold DT
    rw [map_sub, mul_sub]
  have key : ∀ n : ℕ, (X : ℂ_[q]⟦X⟧) ^ n ∣ u - u' ∧ (X : ℂ_[q]⟦X⟧) ^ n ∣ w - w' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      constructor
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hu, sub_self]
        · rw [hsub, h1, h3]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hw, sub_self]
        · rw [hsub, h2, h4]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
  constructor
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).1 n (by omega)
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).2 n (by omega)

end GlobalTheory.MomOne
end

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.MulSeries

variable {q : ℕ} [Fact q.Prime]

def zcHom : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq (a : ℤ_[q]) : zc a = zcHom a := rfl

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.norm_def]

theorem coeff_DT (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (DT f) = coeff (n + 1) f * (n + 1) + coeff n f * n := by
  rw [DT, add_mul, one_mul, map_add (f := _), coeff_derivative]
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp

theorem coeff_one_add_mulS (a : ℤ_[q]) (n : ℕ) :
    coeff n (1 + mulS a : ℂ_[q]⟦X⟧) = zcHom (Ring.choose a n) := by
  cases n with
  | zero => simp [mulS]
  | succ n => simp [mulS, coeff_one, zc_eq]

theorem constantCoeff_mulS (a : ℤ_[q]) : constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 := by
  simp [mulS]

theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_mulS a)

theorem choose_step (c : ℤ_[q]) (n : ℕ) :
    Ring.choose c (n + 1) * (n + 1) + Ring.choose c n * n = c * Ring.choose c n := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose c (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Ring.descPochhammer_eq_factorial_smul_choose] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one, pow_zero,
    nsmul_eq_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  have h0 : (n.factorial : ℤ_[q]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ h0
  linear_combination -h1

theorem DT_one_add_mulS (a : ℤ_[q]) :
    DT (1 + mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  ext n
  rw [coeff_DT, coeff_C_mul, coeff_one_add_mulS, coeff_one_add_mulS, zc_eq]
  have := congrArg zcHom (choose_step a n)
  simpa using this

theorem DT_mulS (a : ℤ_[q]) : DT (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  rw [← DT_one_add_mulS]; simp [DT]

theorem ode_unique (c : ℂ_[q]) (h : ℂ_[q]⟦X⟧) {f g : ℂ_[q]⟦X⟧} (hf : DT f = C c * f + h)
    (hg : DT g = C c * g + h) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := congrArg (coeff n) hf
    have h2 := congrArg (coeff n) hg
    rw [coeff_DT, map_add (f := _), coeff_C_mul] at h1 h2
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    apply mul_right_cancel₀ h3
    rw [ih] at h1
    linear_combination h1 - h2

theorem DT_logS : DT (logS : ℂ_[q]⟦X⟧) = 1 := by
  ext n
  rw [coeff_DT]
  cases n with
  | zero => simp [logS]
  | succ n =>
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have h4 : ((n : ℂ_[q]) + 1 + 1) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    simp only [logS, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false]
    push_cast
    field_simp
    ring

theorem DT_subst_mulS (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (f.subst (mulS a : ℂ_[q]⟦X⟧)) = C (zc a) * (DT f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  have hs := hasSubst_mulS a
  have h2 := DT_mulS a
  have h1 : (DT f).subst (mulS a : ℂ_[q]⟦X⟧) =
      (1 + mulS a) * (derivative f).subst (mulS a : ℂ_[q]⟦X⟧) := by
    rw [DT, ← coe_substAlgHom hs, map_mul, map_add (f := _), map_one, substAlgHom_X]
  rw [h1]
  unfold DT at h2 ⊢
  rw [derivative_subst hs]
  linear_combination ((derivative f).subst (mulS a : ℂ_[q]⟦X⟧)) * h2

theorem constantCoeff_subst_mulS (a : ℤ_[q]) {f : ℂ_[q]⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff (f.subst (mulS a : ℂ_[q]⟦X⟧)) = 0 := by
  have hs := hasSubst_mulS a
  obtain ⟨b, rfl⟩ : (X : ℂ_[q]⟦X⟧) ∣ f := X_dvd_iff.2 hf
  rw [← coe_substAlgHom hs, map_mul, substAlgHom_X, map_mul, constantCoeff_mulS, zero_mul]

theorem logS_subst (a : ℤ_[q]) :
    (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS := by
  have hs := hasSubst_mulS a
  have h0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by simp [logS]
  refine ode_unique 0 (C (zc a)) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_logS, ← coe_substAlgHom hs]; simp
  · have := DT_logS (q := q)
    unfold DT at this ⊢
    rw [Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero, map_zero, zero_mul, zero_add]
    linear_combination (C (zc a)) * this
  · rw [constantCoeff_subst_mulS a h0, map_mul, h0, mul_zero]

theorem mulS_subst (a b : ℤ_[q]) :
    (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b) := by
  have hs := hasSubst_mulS b
  have hz : zc (a * b) = zc a * zc b := by simp [zc_eq]
  refine ode_unique (zc (a * b)) (C (zc (a * b))) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_mulS, ← coe_substAlgHom hs, map_mul, map_add (f := _), map_one, hz, map_mul]
    have : (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧) (C (zc a)) = C (zc a) :=
      (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧).commutes (zc a)
    rw [this]
    ring
  · rw [DT_mulS]; ring
  · rw [constantCoeff_subst_mulS b (constantCoeff_mulS a), constantCoeff_mulS]

theorem mulS_one : (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X := by
  refine ode_unique 1 1 ?_ ?_ ?_
  · rw [DT_mulS]; simp [zc_eq, add_comm]
  · simp [DT, add_comm]
  · simp [constantCoeff_mulS]

theorem bd_mulS (a : ℤ_[q]) : Bd 1 (mulS a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [mulS, coeff_mk]
  split_ifs
  · simp
  · rw [norm_zc]; exact PadicInt.norm_le_one _

theorem bd_one_pow {h : ℂ_[q]⟦X⟧} (hh : Bd 1 h) (d : ℕ) : Bd 1 (h ^ d) := by
  induction d with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ d ih =>
    intro n
    rw [pow_succ, coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hh _)

theorem bd_subst {f h : ℂ_[q]⟦X⟧} {A : ℝ} (hf : Bd A f) (hh : Bd 1 h) (h0 : constantCoeff h = 0) :
    Bd A (f.subst h) := by
  classical
  intro n
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' h0
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  rw [coeff_subst' hs, finsum_def]
  split_ifs
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hA fun d _ => ?_
    rw [smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (bd_one_pow hh d n)).trans (hf d)
  · simpa using hA

theorem bd_subst_mulS_iff (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ) (ha : ‖a‖ = 1) :
    Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f := by
  refine ⟨fun h => ?_, fun h => bd_subst h (bd_mulS a) (constantCoeff_mulS a)⟩
  obtain ⟨b, hb⟩ := (PadicInt.isUnit_iff.2 ha).exists_right_inv
  have h1 := bd_subst h (bd_mulS b) (constantCoeff_mulS b)
  rwa [subst_comp_subst_apply (hasSubst_mulS a) (hasSubst_mulS b), mulS_subst, hb, mulS_one,
    X_subst] at h1

theorem mulS_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ a : ℤ_[q], Bd 1 (mulS a : ℂ_[q]⟦X⟧) ∧ constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 ∧ coeff 1 (mulS a : ℂ_[q]⟦X⟧) = zc a ∧ (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS) ∧ (∀ a b : ℤ_[q], (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b)) ∧ (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X ∧ (∀ (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ), ‖a‖ = 1 → (Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f)) ∧ DT (logS : ℂ_[q]⟦X⟧) = 1 ∧ (∀ a : ℤ_[q], ‖zc a‖ = ‖a‖) :=
  fun _ _ => ⟨fun a => ⟨bd_mulS a, constantCoeff_mulS a, by simp [mulS], logS_subst a⟩, mulS_subst,
    mulS_one, bd_subst_mulS_iff, DT_logS, norm_zc⟩

end GlobalTheory.MomOne.MulSeries
end
end

section

open Matrix

noncomputable section

namespace GlobalTheory.BesselMapCompare

open PI.UpqRep GlobalTheory.IndefiniteRowSideFullHecke

section Maps

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem isHCParam_of_isHCTypeW {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V)}
    (h : IsHCTypeW k r z u π) : PI.UpqRep.IsHCParam u := by
  obtain ⟨g, -, hg⟩ := h
  exact (KTypeCompare.isHCParam_iff u).2 ((KTypeCompare.isHCTypeU_iff u _).1 hg).param

end Maps

end GlobalTheory.BesselMapCompare

end
end

section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  first | exact @GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | exact GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | (intros; apply GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity <;> assumption)
end
