module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.FourierTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

open Set Filter Topology

theorem norm_pow_mul_cexp_neg (n : ℕ) (r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ n * Complex.exp (-(r * t))‖ = t ^ (n : ℝ) * Real.exp (-r.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Real.rpow_natCast, Real.rpow_one]
  congr 2
  simp

theorem integrableOn_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hr
  refine h.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_pow_mul_cexp_neg n r ht]

theorem tendsto_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_pow_mul_cexp_neg n r ht, Real.rpow_one]

theorem integral_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [← neg_mul]
    rw [h]; simp [hr0]
  | succ n ih =>
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
    have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-(r * t)) / (-r))
        (Complex.exp (-(r * t))) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-r) t := by
        simpa using ((h1 t).const_mul (-r))
      have hv' := h2.cexp.div_const (-r)
      rwa [mul_div_assoc, div_self (neg_ne_zero.mpr hr0), mul_one] at hv'
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      intro t _
      convert (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal using 1
      simp
    have hint := integrableOn_pow_mul_cexp_neg n hr
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv
      (integrableOn_pow_mul_cexp_neg (n + 1) hr)
      (by
        refine IntegrableOn.congr_fun (hint.const_mul (-((n : ℂ) + 1) / r)) (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; field_simp)
      (by
        have hc : Continuous (fun t : ℝ => (t : ℂ) ^ (n + 1) * (Complex.exp (-(r * t)) / (-r))) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        convert this using 2 <;> simp)
      (by
        have := (tendsto_pow_mul_cexp_neg (n + 1) hr).const_mul (-1 / r)
        rw [mul_zero] at this
        refine this.congr (fun t => ?_)
        simp only [Pi.mul_apply]; field_simp)
    rw [hibp]
    have e : (fun t : ℝ => ((n : ℂ) + 1) * (t : ℂ) ^ n * (Complex.exp (-(r * t)) / (-r))) =
        fun t : ℝ => (-((n : ℂ) + 1) / r) * ((t : ℂ) ^ n * Complex.exp (-(r * t))) := by
      funext t; field_simp
    rw [e, integral_const_mul, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem fourier_phi1_eq_factorial_mul_zpow : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ),
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  intro k hk hke w hw x
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hwx : w - (x : ℂ) ≠ 0 := by
    intro h
    apply hw
    have := congrArg Complex.im h
    simpa using this
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [Nat.add_sub_cancel]
  rw [Real.fourier_real_eq_integral_exp_smul]
  rcases hw.lt_or_gt with hneg | hpos
  · set r : ℂ := 2 * Real.pi * Complex.I * (w - x) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * (-v) * x) * Complex.I) • phi1 (m + 1) w (-v)) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_neg hneg, SignType.coe_neg,
        SignType.coe_one, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos (by linarith), if_pos hv, abs_neg, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg (by linarith), if_neg hv, mul_zero]
    rw [← integral_neg_eq_self, e, integral_indicator measurableSet_Ioi,
      integral_pow_mul_cexp_neg m hr, hrdef, mul_pow, zpow_neg, zpow_natCast]
    field_simp
  · set r : ℂ := -(2 * Real.pi * Complex.I * (w - x)) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • phi1 (m + 1) w v) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_pos hpos,
        SignType.coe_one, one_mul, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos hv, if_pos hv, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [e, integral_indicator measurableSet_Ioi, integral_pow_mul_cexp_neg m hr, hrdef,
      hke.neg_pow, mul_pow, zpow_neg, zpow_natCast]
    field_simp

end GlobalTheory.LipschitzTR
end
end

section

open GlobalTheory.EtC Polynomial

namespace GlobalTheory.EtC

theorem exists_excisionNbhd_adjoin_root : ∀ (A : Type) [CommRing A] (h : A) (q : ℕ), IsUnit (q : A) →
    ∀ ε r : A, IsUnit ε → ε - r ^ q ∈ Ideal.span {h} → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      IsExcisionNbhd A A' h ∧ ∃ x : A', algebraMap A A' ε = x ^ q := by
  intro A _ h q hq ε r hε hr
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    have : Subsingleton A := by
      simp only [Nat.cast_zero, isUnit_zero_iff] at hq
      exact subsingleton_of_zero_eq_one hq
    exact ⟨A, inferInstance, inferInstance, isExcisionNbhd_self A h, 1, Subsingleton.elim _ _⟩
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  set qi : A := ↑hq.unit⁻¹
  set ei : A := ↑hε.unit⁻¹
  have hq1 : ((m + 1 : ℕ) : A) * qi = 1 := hq.mul_val_inv
  have he1 : ε * ei = 1 := hε.mul_val_inv
  let g : A[X] := ∑ i ∈ Finset.range (m + 1), X ^ i * C r ^ (m + 1 - 1 - i)
  let P : StandardEtalePair A :=
    { f := X ^ (m + 1) - C ε
      monic_f := monic_X_pow_sub_C ε (by omega)
      g := g
      cond := ⟨C (qi * ei) * X, - C ei, 0, by
        have a1 : C ((m + 1 : ℕ) : A) * C qi = 1 := by rw [← C_mul, hq1, C_1]
        have a2 : C ε * C ei = 1 := by rw [← C_mul, he1, C_1]
        simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero, C_mul,
          Nat.add_sub_cancel]
        linear_combination (X ^ (m + 1) * C ei) * a1 + a2⟩ }
  let I : Ideal A := Ideal.span {h}
  have hmap : P.HasMap (Ideal.Quotient.mk I r) := by
    constructor
    · show aeval _ (X ^ (m + 1) - C ε) = 0
      rw [map_sub, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      simpa using I.neg_mem hr
    · show IsUnit (aeval _ g)

      simp only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq]
      rw [geom_sum₂_self]
      refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
      · simpa using hq.map (Ideal.Quotient.mk I)
      · rw [← isUnit_pow_iff (n := m + 1) (by omega), ← map_pow]
        have : Ideal.Quotient.mk I (r ^ (m + 1)) = Ideal.Quotient.mk I ε := by
          rw [Ideal.Quotient.eq]; simpa using I.neg_mem hr
        rw [this]; exact hε.map _
  let φ : P.Ring →ₐ[A] A ⧸ I := P.lift _ hmap
  let J : Ideal P.Ring := Ideal.span {algebraMap A P.Ring h}
  have hgu : IsUnit (aeval P.X g) := P.hasMap_X.2
  have e2 : P.X ^ (m + 1) = algebraMap A P.Ring ε := by
    have : aeval P.X (X ^ (m + 1) - C ε) = 0 := P.hasMap_X.1
    simpa [sub_eq_zero] using this
  have hX : P.X - algebraMap A P.Ring r ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
    have key : (P.X - algebraMap A P.Ring r) * aeval P.X g =
        algebraMap A P.Ring c * algebraMap A P.Ring h := by
      have e1 : aeval P.X g * (P.X - algebraMap A P.Ring r) =
          P.X ^ (m + 1) - (algebraMap A P.Ring r) ^ (m + 1) := by

        simp only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C]
        exact geom_sum₂_mul _ _ _
      rw [mul_comm, e1, e2, ← map_pow, ← map_sub, ← hc, map_mul]
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap A P.Ring c * ↑hgu.unit⁻¹, ?_⟩
    calc _ = (P.X - algebraMap A P.Ring r) * aeval P.X g * ↑hgu.unit⁻¹ := by rw [key]; ring
      _ = _ := by rw [mul_assoc, hgu.mul_val_inv, mul_one]
  let ψ : A ⧸ I →ₐ[A] P.Ring ⧸ J := Ideal.Quotient.liftₐ I (Algebra.ofId A (P.Ring ⧸ J)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact J.mul_mem_left _ (Ideal.mem_span_singleton_self _))
  have hψ : ∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap A P.Ring a) := by
    intro a
    first
      | rfl
      | simp [ψ, Ideal.Quotient.liftₐ_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J)]
  have hcomp : ψ.comp φ = Ideal.Quotient.mkₐ A J := by
    apply P.hom_ext
    simp only [AlgHom.comp_apply, φ, StandardEtalePair.lift_X, Ideal.Quotient.mkₐ_eq_mk]
    show ψ (Ideal.Quotient.mk I r) = _
    rw [hψ, Ideal.Quotient.eq]
    first
      | exact hX
      | (have := J.neg_mem hX; rwa [neg_sub] at this)
  refine ⟨P.Ring, inferInstance, inferInstance, ⟨inferInstance, ?_, ?_⟩, P.X, e2.symm⟩
  · intro a'
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ a')
    refine ⟨a, ?_⟩
    have h1 := congrArg (fun F => F a') hcomp
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← ha] at h1
    rw [hψ] at h1
    exact Ideal.Quotient.eq.mp h1.symm
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp ha
    have h1 := congrArg φ hy
    have hh0 : Ideal.Quotient.mk I h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [map_mul, AlgHom.commutes, Ideal.Quotient.algebraMap_eq] at h1
    rw [hh0, mul_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

end GlobalTheory.EtC
end

section

open IsLocalRing

noncomputable section
namespace GlobalTheory.DenseSec

open KaehlerDifferential
open scoped TensorProduct

theorem formallyEtale_of_bijective_kaehler_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem exists_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A),
      (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  intro R _ _ A _ _ _ ε
  classical
  let p : Ideal A := (maximalIdeal R).comap ε
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let t : κ → A := fun i => a i - algebraMap R A (ε (a i))
  have hDt : ∀ i, D R A (t i) = D R A (a i) := by intro i; simp [t]
  have hεt : ∀ i, ε (t i) = 0 := by intro i; simp [t]
  let e : (κ →₀ A) →ₗ[A] Ω[A⁄R] :=
    Finsupp.linearCombination A fun i : κ ↦ D R A (t i)
  let l₁ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime p))
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[Localization.AtPrime p⁄R] := map R R A (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, hDt]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A _)
  let l₂ₜ : Ω[A⁄R] →ₗ[A] Ω[Localization.Away g⁄R] :=
    map R R A (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  let bB : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hbB : ∀ i, bB i = D R _ (algebraMap A (Localization.Away g) (t i)) := by
    intro i
    have h1 : bB i = eₜ' (Finsupp.single i 1) := by
      rfl
    rw [h1]
    trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e <| l₁ₜ <| Finsupp.single i 1
    · simp [eₜ', -IsLocalizedModule.map_apply, l₁ₜ]
    · simp [l₂ₜ, e]
  let eκ : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  refine ⟨Nat.card κ, t ∘ eκ.symm, g, fun i => hεt _, ?_, ?_⟩
  · have hg' : ε g ∉ maximalIdeal R := hg
    exact (IsLocalRing.notMem_maximalIdeal.mp hg')
  · unfold EtChart
    letI inst : Algebra (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      ((algebraMap A (Localization.Away g)).comp (MvPolynomial.aeval (t ∘ eκ.symm)).toRingHom).toAlgebra
    show Algebra.Etale (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g)
    have hsc : IsScalarTower R (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R (Localization.Away g) r =
          algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
    have hX : ∀ i, algebraMap (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) (MvPolynomial.X i) =
        algebraMap A (Localization.Away g) (t (eκ.symm i)) := by
      intro i
      change algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X]; rfl
    haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
    haveI : Algebra.FormallySmooth R (Localization.Away g) := Algebra.FormallySmooth.comp R A (Localization.Away g)
    let P := MvPolynomial (Fin (Nat.card κ)) R
    let bP : Module.Basis (Fin (Nat.card κ)) (Localization.Away g) ((Localization.Away g) ⊗[P] Ω[P⁄R]) :=
      (mvPolynomialBasis R (Fin (Nat.card κ))).baseChange (Localization.Away g)
    let bB' := bB.reindex eκ
    have hbij : Function.Bijective (mapBaseChange R P (Localization.Away g)) := by
      have : mapBaseChange R P (Localization.Away g) = (bP.equiv bB' (Equiv.refl _)).toLinearMap := by
        refine bP.ext fun i => ?_
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        simp [bP, bB', hbB, ← hX, P]
      rw [this]
      exact (bP.equiv bB' (Equiv.refl _)).bijective
    haveI : Algebra.FormallyEtale P (Localization.Away g) :=
      formallyEtale_of_bijective_kaehler_mapBaseChange R P (Localization.Away g) hbij
    haveI : Algebra.FinitePresentation R (Localization.Away g) :=
      Algebra.FinitePresentation.trans R A (Localization.Away g)
    haveI : Algebra.FinitePresentation P (Localization.Away g) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P (Localization.Away g)
    exact ⟨inferInstance, inferInstance⟩
end GlobalTheory.DenseSec
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.TorsorTrace

theorem injective_trace_galoisData : ∀ (F D : Type) [CommRing F] [CommRing D] [Algebra F D] (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[F] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor F D q act →
    Function.Injective (algebraMap F D) ∧
    (∃ τ : D →ₗ[F] F, ∀ d : D, algebraMap F D (τ d) = ∑ g, act g d) ∧
    ∃ (n : ℕ) (x y : Fin n → D), ∀ g, ∑ i, x i * act g (y i) = if g = 1 then 1 else 0 := by
  intro F D _ _ _ q _ act h
  obtain ⟨_, _, hff, hbij⟩ := h
  have hinj : Function.Injective (algebraMap F D) := FaithfulSMul.algebraMap_injective F D
  refine ⟨hinj, ?_, ?_⟩
  · have hex : ∀ d : D, ∃ c : F, algebraMap F D c = ∑ g, act g d := by
      intro d
      have hfix : ∀ k, act k (∑ g, act g d) = ∑ g, act g d := by
        intro k

        rw [map_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
        intro g
        simp [map_mul]
      have h1 : (∑ g, act g d) ⊗ₜ[F] (1 : D) = (1 : D) ⊗ₜ[F] (∑ g, act g d) := by
        apply hbij.1
        rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
          map_one, map_one, mul_one, one_mul]
        funext k
        exact (hfix k).symm
      have := (Algebra.IsEffective.of_faithfullyFlat F D (∑ g, act g d)).1 (by
        rw [Algebra.TensorProduct.includeLeftSubRight_apply, h1, sub_self])
      obtain ⟨c, hc⟩ := this
      exact ⟨c, hc⟩
    choose t ht using hex
    refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
    · intro a b
      apply hinj
      simp [ht, Finset.sum_add_distrib]
    · intro a b
      apply hinj
      rw [RingHom.id_apply, smul_eq_mul, map_mul, ht, ht, ← Algebra.smul_def, Finset.smul_sum]
      simp
  · obtain ⟨z, hz⟩ := hbij.2 (fun g => if g = 1 then 1 else 0)
    obtain ⟨n, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    refine ⟨n, x, y, fun g => ?_⟩
    have := congrFun hz g

    rw [map_sum, Finset.sum_apply] at this
    exact this

end GlobalTheory.TorsorTrace
end
