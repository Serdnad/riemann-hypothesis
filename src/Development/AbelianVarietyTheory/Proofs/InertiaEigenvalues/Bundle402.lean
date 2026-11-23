module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalRingPolyDividesVarPow
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle309
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle310
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem exists_pow_mul_pow_mul_pow_dvd_prod_pow {B : Type} [CommRing B] {ι : Type} (t x y : B)
    (ξ : ι → B) (hξ : ∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) (u : ι → ℕ) (s : Finset ι) :
    ∃ a b c : ℕ, a + b + c = ∑ q ∈ s, u q ∧ t ^ a * x ^ b * y ^ c ∣ ∏ q ∈ s, ξ q ^ u q := by
  classical
  induction s using Finset.induction_on
  case empty => exact ⟨0, 0, 0, by simp, by simp⟩
  case insert q s hq ih =>
    obtain ⟨a, b, c, habc, hd⟩ := ih
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    rcases hξ q with ⟨r, hr⟩ | hx | hy
    · refine ⟨u q + a, b, c, by omega, ?_⟩
      have h := mul_dvd_mul (dvd_mul_right (t ^ u q) (r ^ u q)) hd
      rw [hr, mul_pow]
      convert h using 1
      ring
    · refine ⟨a, u q + b, c, by omega, ?_⟩
      have h := mul_dvd_mul_left (x ^ u q) hd
      rw [hx]
      convert h using 1
      ring
    · refine ⟨a, b, u q + c, by omega, ?_⟩
      have h := mul_dvd_mul_left (y ^ u q) hd
      rw [hy]
      convert h using 1
      ring

theorem aeval_eq_zero_of_low_coeff_of_three_nilpotent :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ)
      (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 →
      (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) →
      (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t x y K m ξ F ht hx hy hξ hF
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [F.as_sum, map_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hu : u.degree < K + m
  · rw [hF u hu, zero_mul]
  · obtain ⟨a, b, c, habc, hd⟩ := exists_pow_mul_pow_mul_pow_dvd_prod_pow t x y ξ hξ u u.support
    have hdeg : u.degree = ∑ q ∈ u.support, u q := rfl
    have hzero : t ^ a * x ^ b * y ^ c = 0 := by
      by_cases hc : m ≤ c
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
        rw [pow_add, hy]
        simp
      · by_cases hb : 2 ≤ b
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
          rw [pow_add, pow_two, hx]
          simp
        · have hK : K ≤ a := by omega
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
          rw [pow_add, ht]
          simp
    rw [hzero, zero_dvd_iff] at hd
    rw [Finsupp.prod]
    simp only [hd, mul_zero]

end GlobalTheory.NewPrime
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_finiteLocalRing_poly_divides_var_pow : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (l : O) (e w : ℕ) (ι : Type) [Fintype ι] (K : Set ι) (F : MvPolynomial ι O), IsDiscreteValuationRing.addVal O l = e → (∃ m : ι →₀ ℕ, m.degree < w + 1 ∧ (∀ q ∈ K, m q = 0) ∧ IsUnit (F.coeff m)) → ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : Finite A) (_ : Algebra O A) (t : A) (a : ι → A), (∀ x ∈ Ideal.span {l} * IsLocalRing.maximalIdeal O, algebraMap O A x = 0) ∧ t ^ (2 * (e + 1) * w + 2) = 0 ∧ algebraMap O A l * t ^ (2 * (e + 1) * w + 1) ≠ 0 ∧ (∀ q ∈ K, a q = 0) ∧ (∀ q ∉ K, IsUnit (a q)) ∧ MvPolynomial.aeval (fun q => a q * t) F ∣ t ^ ((e + 1) * w) := by
  first | exact @GlobalTheory.NewPrime.LocalRing.exists_finite_local_ring | exact GlobalTheory.NewPrime.LocalRing.exists_finite_local_ring | (intros; apply GlobalTheory.NewPrime.LocalRing.exists_finite_local_ring <;> assumption)
end

section

open Matrix

namespace GlobalTheory.UnitDiscAlg

theorem unit_split {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] {n : ℕ} {N : Matrix (Fin n) (Fin n) E} {ϖ : E}
    (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hB : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1) (hϖ : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖)
    (hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x)
    (y : Matrix (Fin n) (Fin n) E) (hyN : y * N = N * y) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧
      e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a := by
  obtain ⟨x, z, a₁, a₂, a₃, ⟨hxN, hzN, h1N, h2N, h3N⟩, hint, hx, hyx, hyz⟩ :=
    GlobalTheory.T.commuting_integral_matrix_decompose E n N ϖ hN hB h0 h1 hϖ y hyN hy
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  obtain ⟨e, a', heN, ha'N, he, heI, ha'I, hea⟩ :=
    GlobalTheory.T.exists_integral_idempotent_lift_newton E n N x a₁ ϖ h1 hxN (fun i j => (hint i j).1) (fun i j => (hint i j).2.2.1) hx
  have hzI : ∀ i j, ‖z i j‖ ≤ 1 := fun i j => (hint i j).2.1
  have ha₂I : ∀ i j, ‖a₂ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.1
  have ha₃I : ∀ i j, ‖a₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2
  refine ⟨e, a₂ - y * a', heN, ?_, fun i j => ⟨heI i j, integ_sub ha₂I (integ_mul hy ha'I) i j⟩,
    he, ?_, ?_⟩
  · rw [sub_mul, mul_sub, h2N, Matrix.mul_assoc, ha'N, ← Matrix.mul_assoc, hyN, Matrix.mul_assoc]
  ·
    have hye : y * e = e * y := hcomm y e hyN heN
    have hze : z * e = e * z := hcomm z e hzN heN
    have hyz' : y * z = z * y := hcomm y z hyN hzN
    have hprod : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + ϖ • (a₃ + y * z * a' - a') := by
      have e1 : e = x + ϖ • a' := by rw [← hea]; abel
      have e2 : y * z * x = x + ϖ • a₃ := by rw [← hyz]; abel
      have key : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + y * z * e - e := by
        have : (y * e + (1 - e)) * (z * e + (1 - e)) =
            y * (e * z) * e + y * e * (1 - e) + (1 - e) * z * e + (1 - e) * (1 - e) := by
          noncomm_ring
        rw [this, ← hze]
        have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have hee' : (1 - e) * z * e = 0 := by
          rw [Matrix.mul_assoc, hze, ← Matrix.mul_assoc, sub_mul, one_mul, he, sub_self,
            Matrix.zero_mul]
        have hee'' : (1 - e) * (1 - e) = 1 - e := by
          rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
        rw [Matrix.mul_assoc y e (1 - e), hee, Matrix.mul_zero, hee', hee'',
          ← Matrix.mul_assoc, Matrix.mul_assoc (y * z) e e, he]
        abel
      rw [key]
      conv_lhs => rw [e1]
      rw [Matrix.mul_add, e2, Matrix.mul_smul]
      simp only [smul_add, smul_sub]
      abel
    have hwI : ∀ i j, ‖(y * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hy heI) (integ_sub integ_one heI)
    have hw'I : ∀ i j, ‖(z * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hzI heI) (integ_sub integ_one heI)
    have hd := congrArg (fun m => ‖m.det‖) hprod
    simp only [Matrix.det_mul, norm_mul] at hd
    rw [GlobalTheory.T.ultrametric_norm_det_one_add_smul E n _ ϖ h1 (integ_sub (integ_add ha₃I (integ_mul (integ_mul hy hzI) ha'I)) ha'I)]
      at hd
    have ha := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hwI
    have hb := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hw'I
    nlinarith [norm_nonneg (y * e + (1 - e)).det, norm_nonneg (z * e + (1 - e)).det]
  · have : y * (1 - e) = y * (1 - x) - y * (e - x) := by noncomm_ring
    rw [this, hyx, hea, Matrix.mul_smul, ← smul_sub]

theorem units_quotient : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N c b : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ _ n N c b ϖ hN hB h0 h1 hϖ hc hcN hbN hb hbd
  have hB' : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1 := by
    obtain ⟨u, v, -, -, h⟩ := hB
    exact ⟨u, v, h⟩
  have hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x :=
    fun x y hx hy => comm_of_bezout hB' hx hy
  obtain ⟨e₁, e₂, e₃, u, a₂, a₃, hN6, hI6, hu, h11, h22, h33, h12, h13, h23, hs, hc1, hc2, hc3⟩ :=
    GlobalTheory.T.matrix_commutant_valuation_decomposition E n N ϖ h0 h1 hcomm (unit_split hN hB h0 h1 hϖ hcomm) c hc hcN
  exact GlobalTheory.T.quotient_integral_unit_alt E n N c b e₁ e₂ e₃ u a₂ a₃ ϖ h0 h1 hcomm hc hcN hbN hb hbd hN6 hI6 hu h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3

end GlobalTheory.UnitDiscAlg
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith


open NumberField IsDedekindDomain Module in
theorem _root_.GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul :
    ∀ (l N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ N → 1 ≤ L →
      ((5 + Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1)) +
        N * (4 + 2 * Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1))) : ℕ) : ℝ) ≤ 25 * N * L := by
  intro l N L hl hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have he : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
  have hm : ((2 * (⌊2 * Real.exp L⌋₊ + 1) : ℕ) : ℝ) ≤ 2 ^ 3 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1)) : ℝ)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hNL : (1 : ℝ) ≤ N * L := one_le_mul_of_one_le_of_one_le hN' hL
  have hL1 : L ≤ N * L := by nlinarith
  have hN1 : (N : ℝ) ≤ N * L := by nlinarith
  have hA : (N : ℝ) * K ≤ N * (3 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
end
