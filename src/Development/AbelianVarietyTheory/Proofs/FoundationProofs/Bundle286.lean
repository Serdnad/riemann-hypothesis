module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle276
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle266
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle280
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Isog

theorem coeff_lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) (n : ℕ) :
    PowerSeries.coeff n (lineSer e x) = PowerSeries.coeff n e - if n = 2 then x else 0 := by
  simp [lineSer, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

theorem constantCoeff_lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) :
    PowerSeries.constantCoeff (lineSer e x) = PowerSeries.constantCoeff e := by
  simp [lineSer]

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_le_max' (a b : ℂ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_coeff_lineSer_le {e : PowerSeries ℂ_[p]} (he : IntSer e) (x : ℂ_[p]) (n : ℕ) :
    ‖PowerSeries.coeff n (lineSer e x)‖ ≤ max 1 ‖x‖ := by
  rw [coeff_lineSer]
  refine (norm_sub_le_max' _ _).trans (max_le_max (he n) ?_)
  split_ifs <;> simp

theorem exists_norm_coeff_lineSer {e : PowerSeries ℂ_[p]} (he : IntSer e)
    (he0 : PowerSeries.constantCoeff e = 1) (x : ℂ_[p]) :
    ∃ n, max 1 ‖x‖ ≤ ‖PowerSeries.coeff n (lineSer e x)‖ := by
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · refine ⟨0, ?_⟩
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lineSer, he0, norm_one]
    exact max_le le_rfl hx
  · refine ⟨2, ?_⟩
    rw [max_eq_right hx.le]
    have h1 := norm_sub_le_max' (PowerSeries.coeff 2 e) (PowerSeries.coeff 2 (lineSer e x))
    have h2 : PowerSeries.coeff 2 e - PowerSeries.coeff 2 (lineSer e x) = x := by
      rw [coeff_lineSer]; simp
    rw [h2] at h1
    rcases le_max_iff.1 h1 with h | h
    · exact absurd (h.trans (he 2)) (not_le.2 hx)
    · exact h

theorem IntSer.bdd {f : PowerSeries ℂ_[p]} (hf : IntSer f) : BddSer f := ⟨1, hf⟩

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs <;> simp

theorem bdd_prod {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℂ_[p]) (hg : ∀ i, BddSer (g i)) :
    BddSer (∏ i ∈ s, g i) :=
  Finset.prod_induction g BddSer (fun a b ha hb => ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 a b ha hb).2.2)
    (IntSer.bdd intSer_one) (fun i _ => hg i)

theorem int_pow {g : PowerSeries ℂ_[p]} (hg : IntSer g) (k : ℕ) : IntSer (g ^ k) := by
  induction k with
  | zero => simpa using intSer_one
  | succ k ih => rw [pow_succ]; exact ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).1 _ _ ih hg).2.2

theorem subst_lineSer_sub {e h : PowerSeries ℂ_[p]} (h0 : PowerSeries.constantCoeff h = 0)
    (x₀ x₁ : ℂ_[p]) :
    (PowerSeries.subst h (lineSer e x₀) : PowerSeries ℂ_[p]) - PowerSeries.subst h (lineSer e x₁) =
      PowerSeries.C (x₁ - x₀) * h ^ 2 := by
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have e1 : lineSer e x₀ = lineSer e x₁ + (x₁ - x₀) • PowerSeries.X ^ 2 := by
    rw [PowerSeries.smul_eq_C_mul]
    simp only [lineSer, map_sub]; ring
  rw [e1, PowerSeries.subst_add hs, PowerSeries.subst_smul hs, PowerSeries.subst_pow hs,
    PowerSeries.subst_X hs, PowerSeries.smul_eq_C_mul]
  ring

theorem bdd_of_mul_sq {Ψ h : PowerSeries ℂ_[p]} {c : ℂ_[p]} (hc : c ≠ 0) (hh : IntSer h)
    (h0 : PowerSeries.constantCoeff h = 0) (h1 : ‖PowerSeries.coeff 1 h‖ = 1)
    (hb : BddSer (Ψ * (PowerSeries.C c * h ^ 2))) : BddSer Ψ := by
  obtain ⟨h', rfl⟩ := PowerSeries.X_dvd_iff.2 h0
  have hi : IntSer h' := fun n => by simpa using hh (n + 1)
  have hc0 : ‖PowerSeries.constantCoeff h'‖ = 1 := by
    have := PowerSeries.coeff_succ_X_mul 0 h'
    simp only [zero_add] at this
    rw [this] at h1
    simpa using h1
  have hne : PowerSeries.constantCoeff h' ≠ 0 := by
    intro h; rw [h] at hc0; simp at hc0
  have hinv := (GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.2.2.1 h' hi hc0
  have hb2 := ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ hb (((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.1 _ _ ((GlobalTheory.T.padicComplex_integral_bounded_series_laws p).2.2.1 c⁻¹).1
    (IntSer.bdd (int_pow hinv 2))).2.2)).2.2
  have hm := PowerSeries.mul_inv_cancel h' hne
  have hcc : (PowerSeries.C c : PowerSeries ℂ_[p]) * PowerSeries.C c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have e : Ψ * (PowerSeries.C c * (PowerSeries.X * h') ^ 2) * (PowerSeries.C c⁻¹ * h'⁻¹ ^ 2) =
      Ψ * PowerSeries.X ^ 2 := by
    calc _ = Ψ * PowerSeries.X ^ 2 * (PowerSeries.C c * PowerSeries.C c⁻¹) * (h' * h'⁻¹) ^ 2 := by ring
      _ = _ := by rw [hm, hcc]; ring
  rw [e] at hb2
  obtain ⟨B, hB⟩ := hb2
  exact ⟨B, fun n => by simpa [PowerSeries.coeff_mul_X_pow] using hB (n + 2)⟩

end GlobalTheory.EvenTheta.Isog

namespace GlobalTheory.EvenTheta
open Isog

theorem intSer_of_isogeny_identities : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (e h S f : PowerSeries ℂ_[p]) (x₀ x₁ : ℂ_[p]) (y : Fin k → ℂ_[p]) (y' : Fin (2 * k) → ℂ_[p]), IntSer e → PowerSeries.constantCoeff e = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖((2 * k : ℕ) : ℂ_[p])‖ < 1 → PowerSeries.constantCoeff S = 1 → PowerSeries.constantCoeff f = 1 → f ^ 2 = S * lineSer e x₀ → (PowerSeries.subst h f : PowerSeries ℂ_[p]) = S ^ k * ∏ i, lineSer e (y i) → (PowerSeries.subst h (S * lineSer e x₁) : PowerSeries ℂ_[p]) = S ^ (2 * k) * ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → (∃ j, y' j = x₀) → (∃ j, y' j = x₁) → x₀ ≠ x₁ → IntSer f ∧ ‖x₀‖ ≤ 1 := by
  intro p _ k e h S f x₀ x₁ y y' he he0 hh h0 h1 hk hS0 hf0 hf2 hf hS hy ⟨j₀, hj₀⟩ ⟨j₁, hj₁⟩ hx
  obtain ⟨rI, rB, rC, -, -, rS, rM⟩ := GlobalTheory.T.padicComplex_integral_bounded_series_laws p
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hG : ∀ x, BddSer (lineSer e x) := fun x => ⟨_, norm_coeff_lineSer_le he x⟩
  have hG0 : ∀ x, PowerSeries.constantCoeff (lineSer e x) = 1 := fun x => by
    rw [constantCoeff_lineSer, he0]
  have hGs : ∀ x n, ‖PowerSeries.coeff n (PowerSeries.subst h (lineSer e x) : PowerSeries ℂ_[p])‖ ≤
      max 1 ‖x‖ := fun x => rS _ h _ (norm_coeff_lineSer_le he x) hh h0
  set P := ∏ i, lineSer e (y i) with hP
  set P' := ∏ j, lineSer e (y' j) with hP'
  have hPb : BddSer P := bdd_prod _ _ fun i => hG _
  have hP'b : BddSer P' := bdd_prod _ _ fun i => hG _
  have hP0 : PowerSeries.constantCoeff P = 1 := by simp [hP, map_prod, hG0]
  have hP'0 : PowerSeries.constantCoeff P' = 1 := by simp [hP', map_prod, hG0]
  have hinv := PowerSeries.mul_inv_cancel (S ^ (2 * k)) (by simp [hS0])
  set Ψ : PowerSeries ℂ_[p] := PowerSeries.subst h S * (S ^ (2 * k))⁻¹ with hΨ
  set A : PowerSeries ℂ_[p] := PowerSeries.subst h (lineSer e x₀) with hA
  set B : PowerSeries ℂ_[p] := PowerSeries.subst h (lineSer e x₁) with hB
  have eA : Ψ * A = P ^ 2 := by
    have h2 : (PowerSeries.subst h S : PowerSeries ℂ_[p]) * A = S ^ (2 * k) * P ^ 2 := by
      rw [hA, ← PowerSeries.subst_mul hs, ← hf2, PowerSeries.subst_pow hs, hf]; ring
    rw [hΨ]
    linear_combination (S ^ (2 * k))⁻¹ * h2 + P ^ 2 * hinv
  have eB : Ψ * B = P' := by
    rw [PowerSeries.subst_mul hs] at hS
    rw [hΨ]
    linear_combination (S ^ (2 * k))⁻¹ * hS + P' * hinv
  have eAB : A - B = PowerSeries.C (x₁ - x₀) * h ^ 2 := subst_lineSer_sub h0 x₀ x₁
  have hB0 : PowerSeries.constantCoeff B = 1 := by
    have e1 : lineSer e x₁ = 1 + PowerSeries.X * PowerSeries.mk fun n =>
        PowerSeries.coeff (n + 1) (lineSer e x₁) := by
      conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (lineSer e x₁)]
      rw [hG0, map_one, add_comm]
    have e2 : (PowerSeries.subst h (1 : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p]) = 1 := by
      rw [← PowerSeries.coe_substAlgHom hs, map_one]
    rw [hB, e1, PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, e2]
    simp [h0]
  have hΨ0 : PowerSeries.constantCoeff Ψ = 1 := by
    have := congrArg PowerSeries.constantCoeff eB
    rwa [map_mul, hB0, hP'0, mul_one] at this
  have hΨb : BddSer Ψ := by
    refine bdd_of_mul_sq (sub_ne_zero.2 hx.symm) hh h0 h1 ?_
    rw [← eAB, mul_sub, eA, eB, sq]
    exact (rB _ _ (rB _ _ hPb hPb).2.2 hP'b).2.1
  have hΨi : IntSer Ψ :=
    GlobalTheory.T.integral_series_of_common_divisor_line_products p k (2 * k) e Ψ A B y y' (IntSer.bdd he) hΨb ⟨_, hGs x₀⟩ ⟨_, hGs x₁⟩ hΨ0 eA eB hy
  have hP'm : ∀ n, ‖PowerSeries.coeff n P'‖ ≤ max 1 ‖x₁‖ := fun n => by
    have := rM Ψ B _ _ hΨi (hGs x₁) n
    rwa [eB, one_mul] at this
  have hj : j₀ ≠ j₁ := by
    rintro rfl
    exact hx (hj₀.symm.trans hj₁)
  set R := ∏ j ∈ (Finset.univ.erase j₁).erase j₀, lineSer e (y' j) with hR
  have hRb : BddSer R := bdd_prod _ _ fun i => hG _
  have hR0 : PowerSeries.constantCoeff R = 1 := by simp [hR, map_prod, hG0]
  have eP' : P' = lineSer e x₁ * (lineSer e x₀ * R) := by
    rw [hP', hR, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₁),
      ← Finset.mul_prod_erase (Finset.univ.erase j₁) _ (a := j₀) (by simp [hj]), hj₀, hj₁]
  have hGR : IntSer (lineSer e x₀ * R) := fun n => by
    obtain ⟨i, hi⟩ := exists_norm_coeff_lineSer he he0 x₁
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ (hG x₁) (rB _ _ (hG x₀) hRb).2.2 (eP' ▸ hP'm) i n
    have hpos : (0 : ℝ) < max 1 ‖x₁‖ := lt_max_of_lt_left one_pos
    have h4 := mul_le_mul_of_nonneg_right hi
      (norm_nonneg (PowerSeries.coeff n (lineSer e x₀ * R)))
    exact le_of_mul_le_mul_left (by rw [mul_one]; exact h4.trans h3) hpos
  have hGi : IntSer (lineSer e x₀) := fun n => by
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ (hG x₀) hRb hGR n 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0, norm_one, mul_one] at h3
  have hx0 : ‖x₀‖ ≤ 1 := by
    obtain ⟨i, hi⟩ := exists_norm_coeff_lineSer he he0 x₀
    exact (le_max_right _ _).trans (hi.trans (hGi i))
  have hPi : IntSer P := fun n => by
    have hAi : IntSer A := rS _ h _ hGi hh h0
    have h2 : IntSer (P * P) := by
      rw [← sq, ← eA]; exact (rI _ _ hΨi hAi).2.2
    have h3 := GlobalTheory.T.powerSeries_supNorm_mul_padicComplex p _ _ _ hPb hPb h2 n 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply, hP0, norm_one, mul_one] at h3
  refine ⟨GlobalTheory.T.powerSeriesCoeffNormLeOne_functional_equation_padic p f h (lineSer e x₀ ^ k) P (2 * k) hf0 hh h0 h1 hk (int_pow hGi k)
    (by simp [hG0]) hPi hP0 ?_, hx0⟩
  rw [hf, pow_mul, hf2]; ring

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.FrobStick

open PowerSeries

theorem omegaW_mul_inv {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (hwq : IsWq W wq) :
    omegaW W wq * (wq⁻¹ * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) =
      X * derivative (R := ℂ_[p]) wq⁻¹ - 2 * wq⁻¹ ∧ omegaW W wq ≠ 0 := by
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative (R := ℂ_[p]) wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * derivative (R := ℂ_[p]) wq) * (wq * N)⁻¹ := by
      have hd : dX wq = derivative (R := ℂ_[p]) wq := by
        ext n
        simp [dX, coeff_derivative, mul_comm]
      unfold omegaW
      rw [hd]
      rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * derivative (R := ℂ_[p]) e + e * derivative (R := ℂ_[p]) wq = 0 := by
    have := congrArg (derivative (R := ℂ_[p])) he
    rw [Derivation.leibniz] at this
    simpa using this
  have key : omegaW W wq * (e * N) = X * derivative (R := ℂ_[p]) e - 2 * e := by
    linear_combination e ^ 2 * hω - X * e * hde -
      (omegaW W wq * N * e + 2 * e - X * derivative (R := ℂ_[p]) e) * he
  refine ⟨key, fun h => ?_⟩
  rw [h, zero_mul] at key
  have := congrArg constantCoeff key
  simp [he1, h2] at this

theorem atU_sgStar_eq {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (X * ePhi1 g.lam g.abelian₂ g.C g.wq) := by
  have h0 : constantCoeff (GL3Theta.ser1 g.lam (sgStar g.abelian₂)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.taylorCoeff_zero_eq_value,
      (hL.sg_eq_zero 0).2 (zero_mem _)]
    exact (GlobalTheory.SerTransport.lamC_coe g.lam 0).trans (map_zero g.lam)
  obtain ⟨S, hS⟩ := X_dvd_iff.2 h0
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g S hS, GlobalTheory.SerTransport.atU_eq, hS, subst_mul hs, subst_X hs,
    mul_assoc]

theorem colC_atU : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  intro hD p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hQ, eQ⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hσ', dσ⟩ := hD p g _ hσ
  obtain ⟨hQ', dQ⟩ := hD p g _ hQ
  obtain ⟨hT, hc, -⟩ := GlobalTheory.SerTransport.transport p g
  have hm : (-2 : ℂ) ∈ Qbar := neg_mem (ofNat_mem _ 2)
  obtain ⟨c1, c2⟩ := hc _ hm
  have c3 : lamC g.lam (-2) = -2 := by
    have : (-2 : ℂ) = ((-2 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  obtain ⟨a1, a2⟩ := (hT _ _ hσ hQ').1
  obtain ⟨b1, b2⟩ := (hT _ _ c1 hσ').1
  obtain ⟨d1, d2⟩ := (hT _ _ b1 hQ).1
  obtain ⟨f1, f2⟩ := (hT _ _ a1 d1).2
  have e : colC g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (-2 * deriv (sgStar g.abelian₂) z) * sqTh g.abelian₂ v z := by
    funext z
    rw [colC]; ring
  rw [e]
  refine ⟨f1, ?_⟩
  rw [f2, a2, d2, b2, c2, c3, map_neg, map_ofNat]
  obtain ⟨hω, hω0⟩ := omegaW_mul_inv g.W g.wq hq
  have eS := atU_sgStar_eq g hL
  have hε : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    rw [constantCoeff_C, map_zero] at this
    exact Units.ne_zero _ this
  apply mul_left_cancel₀ (mul_ne_zero hε hω0)
  rw [eQ, lineSer] at dQ
  rw [eS] at dσ
  rw [eQ, eS, lineSer]
  generalize ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ε at *
  generalize ePhi1 g.lam g.abelian₂ g.C g.wq = E at *
  generalize g.wq⁻¹ = q at *
  generalize xAt g v = x at *
  have k1 : derivative (R := ℂ_[p]) (C ε * (X * E)) = C ε * (E + X * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, Derivation.leibniz]; simp [add_comm]
  have k2 : derivative (R := ℂ_[p]) (E ^ 2 * (q - C x * X ^ 2)) =
      E ^ 2 * (derivative (R := ℂ_[p]) q - C x * (2 * X)) + (q - C x * X ^ 2) * (2 * E * derivative (R := ℂ_[p]) E) := by
    rw [Derivation.leibniz, map_sub, Derivation.leibniz (a := C x), Derivation.leibniz_pow, Derivation.leibniz_pow]
    simp only [derivative_C, derivative_X, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [k1] at dσ
  rw [k2] at dQ
  linear_combination -(C ε * (X * E)) * dQ + 2 * (E ^ 2 * (q - C x * X ^ 2)) * dσ - C ε * E ^ 3 * hω

end GlobalTheory.FrobStick
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_atU {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) (hσ : AlgEnt (sgStar g.abelian₂)) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  have h0 : coef1 (sgStar g.abelian₂) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar g.abelian₂)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar g.abelian₂) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  have hS' : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * PowerSeries.map g.lam S := by
    rw [GlobalTheory.EvenTheta.Param.theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X]
  have hE := GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g _ hS'
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, hS', subst_mul hs, subst_X hs, mul_assoc, mul_assoc, hE]

theorem colAB_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hT, hC, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨aT, eT⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have e1 := sgStar_atU g hL hσ
  obtain ⟨⟨a2, e2⟩, -⟩ := hT _ _ hσ hσ
  obtain ⟨⟨a3, e3⟩, -⟩ := hT _ _ a2 hσ
  obtain ⟨aw, ew⟩ := hC _ hw
  obtain ⟨⟨a4, e4⟩, -⟩ := hT _ _ aw a2
  obtain ⟨-, a5, e5⟩ := hT _ _ aT a4
  obtain ⟨⟨a6, e6⟩, -⟩ := hT _ _ hσ a5
  have hA : colA g.abelian₂ = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z * sgStar g.abelian₂ z := by
    funext z; rw [colA]; ring
  have hB : colB g.abelian₂ v = fun z => sgStar g.abelian₂ z *
      (sqTh g.abelian₂ v z + wpF g.abelian₂ v * (sgStar g.abelian₂ z * sgStar g.abelian₂ z)) := by
    funext z; rw [colB]; ring
  rw [hA, hB]
  refine ⟨a3, a6, e1, ?_, ?_⟩
  · rw [e3, e2, e1, map_pow]; ring
  · rw [e6, e5, e4, e2, ew, eT, e1, lineSer, xAt]
    simp only [map_mul, map_pow, map_sub]
    ring

end GlobalTheory.FrobStick
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_nat_common_denom {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (c : ι → K) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∃ a : 𝓞 K, (a : K) = (k : K) * c i := by
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨(m * m).natAbs, Int.natAbs_pos.2 (mul_ne_zero hm0 hm0), fun i => ?_⟩
  have h := hm (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨(m : 𝓞 K) * ⟨m • c i, h⟩, ?_⟩
  have h2 : (((m * m).natAbs : ℕ) : K) = (m : K) * m := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]; push_cast; rfl
  rw [h2]
  change ((m : 𝓞 K) : K) * (m • c i) = _
  simp [mul_assoc]

theorem smul_mem_YYl (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : 𝓞 D.host.K)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L L') : (a : D.host.K) • y ∈ YYl D L L' := by
  have h := (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a) hy
  exact h

theorem exists_comm_YYl (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hb : OnB D b) (hL : SD D L) (hL' : SD D L') :
    ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  have hc : ∀ i, ∃ c : Fin r → D.host.K, ∑ j, c j • b j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hb.2]; trivial)
  choose c hc using hc
  obtain ⟨k, hk, hden⟩ := exists_nat_common_denom (K := D.host.K) (ι := (Fin s × Fin r) ⊕ (Fin s × Fin r))
    (Sum.elim (fun p => c p.1 p.2) (fun p => hYY D (b p.2) (y' p.1)))
  choose a ha using hden
  refine ⟨k, hk, fun x hx => ?_, fun j => ?_⟩
  · have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine ⟨fun j => ∑ i, t i * a (Sum.inl (i, j)), ?_⟩
    conv_lhs => rw [hexp x]
    rw [← Nat.cast_smul_eq_nsmul D.host.K]
    simp only [← hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1

    rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ha, ht]
    simp only [Sum.elim_inl]
    ring
  · apply AddSubgroup.subset_closure
    rw [hexp (b j), ← Nat.cast_smul_eq_nsmul D.host.K, Finset.smul_sum]
    refine (YYl D L L').sum_mem fun i _ => ?_
    rw [smul_smul]
    have := ha (Sum.inr (i, j))
    simp only [Sum.elim_inr] at this
    rw [← this]
    exact smul_mem_YYl D L L' _ (hy i)

end GlobalTheory.ThetaConj
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  first | exact @GlobalTheory.EisM.zm_fun_mf | exact GlobalTheory.EisM.zm_fun_mf | (intros; apply GlobalTheory.EisM.zm_fun_mf <;> assumption)
end
