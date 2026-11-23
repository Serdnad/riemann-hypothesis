module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Mathlib.NumberTheory.NumberField.CMField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoSum

theorem norm_cpow_eq_mul_conj_cpow (u s : ℂ) :
    ((‖u‖ : ℝ) : ℂ) ^ (-2 * s) = (u * starRingEnd ℂ u) ^ (-s) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [sq, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  rw [show -2 * s = ((2:ℕ):ℂ) * (-s) by push_cast; ring, Complex.cpow_nat_mul, sq]

theorem hasFDerivAt_factor_norm_cpow {I : Type} [Fintype I] (j : I) (a c K σ : ℂ) (n : ℕ) (z : I → ℂ)
    (hu : a + z j * c ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => K * (a + w j * c)⁻¹ ^ n * ((‖a + w j * c‖ : ℝ) : ℂ) ^ (-2 * σ))
      ((K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) * (-((n : ℂ) + σ) * c / (a + z j * c))) • dz j +
       (K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) *
         (-σ * starRingEnd ℂ c / starRingEnd ℂ (a + z j * c))) • dzbar j) z := by
  simp_rw [norm_cpow_eq_mul_conj_cpow]
  set u := a + z j * c with hu_def
  have hU : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => a + w j * c) (c • dz j) z :=
    ((dz j).hasFDerivAt.mul_const c).const_add a
  have hC : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => starRingEnd ℂ (a + w j * c))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (c • dz j)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hU
  have hP := hU.mul hC
  have hcu : starRingEnd ℂ u ≠ 0 := (map_ne_zero _).2 hu
  have hne : u * starRingEnd ℂ u ≠ 0 := mul_ne_zero hu hcu
  have hslit : u * starRingEnd ℂ u ∈ Complex.slitPlane := by
    rw [Complex.mul_conj]
    exact Complex.ofReal_mem_slitPlane.2 (Complex.normSq_pos.2 hu)
  have hpow := ((hasDerivAt_id (u * starRingEnd ℂ u)).cpow_const (c := -σ) hslit).comp_hasFDerivAt z hP
  have hinv := (((hasDerivAt_id u).inv hu).pow n).comp_hasFDerivAt z hU
  have h := (hinv.const_mul K).mul hpow
  refine h.congr_fderiv ?_
  ext v
  clear h hinv hpow hP hC hU hslit
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    dz_apply, dzbar_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    Function.comp_apply, id, Pi.inv_apply, Pi.pow_apply, Pi.mul_apply, ← hu_def]
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  rcases n with _ | n
  · simp
    field_simp
    ring
  · simp only [Nat.add_sub_cancel, inv_pow]
    field_simp
    push_cast
    ring

theorem hasFDerivAt_eTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x)
      (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j +
        (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by
  intro E _ _ I _ _ φ m σ x hx z hz
  let C : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * ∏ j ∈ Finset.range n, (2 + σ + j)
  let c : I → ℂ := fun i => starRingEnd ℂ (φ i x)
  let F : I → (I → ℂ) → ℂ := fun i w => C (m i) * c i ^ m i * (φ i x + w i * c i)⁻¹ ^ (2 + m i) *
    ((‖φ i x + w i * c i‖ : ℝ) : ℂ) ^ (-2 * σ)
  let α : I → ℂ := fun i => -(((2 + m i : ℕ) : ℂ) + σ) * c i / (φ i x + z i * c i)
  let β : I → ℂ := fun i => -σ * starRingEnd ℂ (c i) / starRingEnd ℂ (φ i x + z i * c i)
  have hF : ∀ i, HasFDerivAt (𝕜 := ℝ) (F i) ((F i z * α i) • dz i + (F i z * β i) • dzbar i) z := fun i =>
    hasFDerivAt_factor_norm_cpow i (φ i x) (c i) (C (m i) * c i ^ m i) σ (2 + m i) z
      (GlobalTheory.DeformedSum.defCoord_ne_zero φ z hz x hx i)
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (g := F) (x := z) (fun i _ => hF i)
  have hfun : (fun w : I → ℂ => eTerm φ m σ w x) = fun w => ∏ i ∈ Finset.univ, F i w := rfl
  have hval : eTerm φ m σ z x = ∏ i ∈ Finset.univ, F i z := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : ∀ (f g : I → ℂ), (∀ i, i ≠ j → g i = f i) →
      ∏ i, g i = (∏ i ∈ Finset.univ.erase j, f i) * g j := by
    intro f g h
    rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ j)]
    congr 1
    exact Finset.prod_congr rfl fun i hi => h i (Finset.ne_of_mem_erase hi)
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  · congr 1
    unfold eTerm
    rw [key (fun i => F i z) _ ?_]
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same, F, α, C, c, defCoord, Finset.prod_range_succ, pow_succ]
      push_cast
      ring
    · intro i hij
      simp only [Pi.add_apply, Pi.single_eq_of_ne hij, add_zero]
      rfl
  · congr 1
    rw [hval, ← Finset.prod_erase_mul Finset.univ (fun i => F i z) (Finset.mem_univ j)]
    simp only [β, c, defCoord, Complex.conj_conj]
    ring

end GlobalTheory.WeightTwoSum
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

theorem _root_.GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x) (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  first | exact @GlobalTheory.DeformedSum.hasFDerivAt_dTerm | exact GlobalTheory.DeformedSum.hasFDerivAt_dTerm | (intros; apply GlobalTheory.DeformedSum.hasFDerivAt_dTerm <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoSum.Bound

theorem eTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) →
      ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by
  intro E _ _ _ I _ φ hφ m σ r hσ hr
  have hr' : 0 < 1 - r := by linarith
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹) ^ (2 + m i) *
    (1 - r) ^ (-2 * σ.re)), fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) = ∏ i, (‖φ i x‖ ^ 2) ^ (-(1 + σ.re)) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  rw [hN, ← Finset.prod_mul_distrib, eTerm, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  have hp : 0 < ‖φ i x‖ := norm_pos_iff.2 ((map_ne_zero (φ i)).2 hx)
  have hl := GlobalTheory.DeformedSum.Bound.defCoord_lower φ z x i (hz i)
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hd]
  set a := ‖φ i x‖ with ha
  set d := ‖defCoord φ z x i‖ with hdd
  have h1 : a ^ m i * d⁻¹ ^ (2 + m i) ≤ (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by
    have hinv : d⁻¹ ≤ (1 - r)⁻¹ * a⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
    calc a ^ m i * d⁻¹ ^ (2 + m i) ≤ a ^ m i * ((1 - r)⁻¹ * a⁻¹) ^ (2 + m i) := by gcongr
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 * (a ^ m i * a⁻¹ ^ m i) := by rw [mul_pow, pow_add a⁻¹]; ring
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow, mul_one]
  have h2 : d ^ ((-2 * σ).re) ≤ (1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re) := by
    rw [show (-2 * σ).re = -2 * σ.re by simp, ← Real.mul_rpow hr'.le hp.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hr' hp) hl (by linarith)
  have h3 : (a ^ 2) ^ (-(1 + σ.re)) = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by
    calc (a ^ 2) ^ (-(1 + σ.re)) = a ^ ((2 : ℝ) * (-(1 + σ.re))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
      _ = a ^ (-(2 : ℝ)) * a ^ (-2 * σ.re) := by rw [← Real.rpow_add hp]; ring_nf
      _ = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by rw [Real.rpow_neg hp.le, inv_pow]; norm_num
  rw [h3]
  calc ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * a ^ m i * d⁻¹ ^ (2 + m i) * d ^ ((-2 * σ).re)
      = ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * (a ^ m i * d⁻¹ ^ (2 + m i)) * d ^ ((-2 * σ).re) := by
        ring
    _ ≤ ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2) *
        ((1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (by positivity) (by positivity)
    _ = _ := by ring

end GlobalTheory.WeightTwoSum.Bound
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

theorem _root_.GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  first | exact @GlobalTheory.DeformedSum.Bound.dTerm_bound | exact GlobalTheory.DeformedSum.Bound.dTerm_bound | (intros; apply GlobalTheory.DeformedSum.Bound.dTerm_bound <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPair

variable {E : Type} [Field E] [NumberField E]

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m) (h' : ¬ x ≤ WithZero.exp (m - 1)) :
    x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem exists_int_cong (P : HeightOneSpectrum (𝓞 E)) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ b : 𝓞 E, Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E P).mem_nhds (OrderUnits.ball_mem_nhds P 1 z)
  have hk' : Valued.v (algebraMap E (P.adicCompletion E) k - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hk
  have hval : ∀ x : E, Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x
  have h1 : P.valuation E k ≤ 1 := by
    have h2 : WithZero.exp (-((1 : ℕ) : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have := Valuation.map_add_le _ (hk'.trans h2) hz
    rwa [sub_add_cancel, hval] at this
  obtain ⟨b, hb⟩ := P.exists_valuation_sub_lt_of_integer h1 (Units.mk0 (WithZero.exp (-((1 : ℕ) : ℤ))) WithZero.exp_ne_zero)
  refine ⟨b, ?_⟩
  rw [← hval, map_sub] at hb
  have := Valuation.map_add_le _ hb.le hk'
  rw [sub_add_sub_cancel] at this
  exact this

def unitF (a : OF E) (ha : a ≠ 0) : (maximalRealSubfield E)ˣ :=
  Units.mk0 (a : maximalRealSubfield E) (fun h => ha (RingOfIntegers.ext h))

def locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (P.adicCompletion E)ˣ :=
  Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) (unitF a ha))

theorem coe_locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (locF P a ha : P.adicCompletion E) = iota a P := rfl

theorem loc_mul_loc {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (h2 : ∀ R, Over R v → R = P ∨ R = P') (a : OF E) (ha : a ≠ 0) :
    χ.loc P (locF P a ha) * χ.loc P' (locF P' a ha) = 1 := by
  classical
  have hS : Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v = {P, P'} := by
    ext R
    rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨h2 R, ?_⟩
    rintro (rfl | rfl)
    · exact hP
    · exact hP'
  have h := hF.1 v (unitF a ha)
  unfold Formalism.L2.Host.HChar.resFin at h
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h
  exact h

theorem unrAt_and_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E))
    (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P →
    UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  intro E _ _ _ χ v P P' hF hs hP hP' hne hlev hun
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  have hval : ∀ R, Over R v → ∀ (n : ℕ) (a : OF E), a ∈ v.asIdeal ^ n → a ∉ v.asIdeal ^ (n + 1) →
      Valued.v (iota a R) = WithZero.exp (-(n : ℤ)) := fun R hR n a h h' => by
    refine eq_exp_of_le (val_iota_le_of_mem hR n h) fun h3 => h' ?_
    rw [← (hef R hR).2.1, ← val_iota_le_iff]
    convert h3 using 2
    push_cast; ring
  have hun' : UnrAt χ P' := by
    intro u hu
    have hu1 : Valued.v (u : P'.adicCompletion E) = 1 := hu
    obtain ⟨b, hb⟩ := exists_int_cong P' u hu1.le
    obtain ⟨a, ha⟩ := (hef P' hP').2.2 b
    have h3 := OrderUnits.val_int_le P' 1 _ (by simpa using ha)
    have h4 : Valued.v (iota a P' - u) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
      have := Valuation.map_sub_le _ hb h3
      rw [sub_sub_sub_cancel_left] at this
      exact this
    have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h5 : Valued.v (iota a P') = 1 := by
      rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ h4.trans_lt hlt), hu1]
    have hav : a ∉ v.asIdeal ^ (0 + 1) := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt
    have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
    have h6 : χ.loc P (locF P a ha0) = 1 := hun _ (by
      show Valued.v (iota a P) = 1
      simpa using hval P hP 0 a (by simp) hav)
    have h7 := hmul a ha0
    rw [h6, one_mul] at h7
    have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
        rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu1, div_one]
      · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, coe_locF]
        exact h4
    rw [map_div, div_eq_one, h7] at h8
    exact h8.symm
  refine ⟨hun', ?_⟩
  obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have ha0 : a ≠ 0 := fun h => ha' (h ▸ zero_mem _)
  have h7 := hmul a ha0
  have hunif : ∀ R, Over R v → Formalism.L2.Host.IsUnifAt R (locF R a ha0) := fun R hR => by
    show Valued.v (iota a R) = WithZero.exp (-1 : ℤ)
    simpa using hval R hR 1 a ha ha'
  rw [χ.val_eq hun _ (hunif P hP), χ.val_eq hun' _ (hunif P' hP')] at h7
  exact eq_inv_of_mul_eq_one_right h7

end GlobalTheory.CMVal.Euler.SplitPair
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.Resid

variable {E : Type} [Field E] [NumberField E]

theorem le_exp_iff (x : WithZero (Multiplicative ℤ)) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) ↔ x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_lt_exp]
    omega

theorem val_iota_lt_iff {P : HeightOneSpectrum (𝓞 E)} {q : HeightOneSpectrum (OF E)} (h : Over P q) (a : OF E) :
    Valued.v (iota a P) < 1 ↔ a ∈ q.asIdeal := by
  rw [← le_exp_iff, val_iota_le_iff, pow_one, ← Ideal.mem_comap, h]

theorem val_iota_eq_one {P : HeightOneSpectrum (𝓞 E)} {q : HeightOneSpectrum (OF E)} (h : Over P q) {a : OF E}
    (ha : a ∉ q.asIdeal) : Valued.v (iota a P) = 1 :=
  le_antisymm (val_iota_le_one P a) (not_lt.1 fun h' => ha ((val_iota_lt_iff h a).1 h'))

theorem exists_iota_approx {P : HeightOneSpectrum (𝓞 E)}
    (h : ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal) (x : P.adicCompletion E)
    (hx : Valued.v x ≤ 1) : ∃ a : OF E, Valued.v (x - iota a P) < 1 := by
  obtain ⟨b, hb⟩ := ReciprocityTheory.Aut.adic_exists_approx (R := 𝓞 E) (K := E) P x hx
  obtain ⟨a, ha⟩ := h b
  refine ⟨a, ?_⟩
  rw [ReciprocityTheory.Aut.adic_algebraMap_R] at hb
  have h1 : iota a P = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a)) := rfl
  have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (b - algebraMap (OF E) (𝓞 E) a))) < 1 := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 ha
  have := Valuation.map_add_lt _ hb h2
  rwa [map_sub, map_sub, sub_add_sub_cancel, ← h1] at this

theorem locIn_iff {q : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P q) (hP' : Over P' q)
    (hne : P' ≠ P) (hall : ∀ R, Over R q → R = P ∨ R = P') (y : (Af E)ˣ) {a b t : OF E}
    (ha : Valued.v ((y : Af E) P' - iota a P') < 1) (hb : Valued.v ((y : Af E) P - iota b P) < 1)
    (ht : t ∉ q.asIdeal) (r : (P.adicCompletion E)ˣ) (hr : (r : P.adicCompletion E) = iota t P) :
    LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) ↔ b - t * a ∈ q.asIdeal := by
  have e1 : (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) P = (iota t P)⁻¹ * (y : Af E) P := by
    rw [Units.val_mul, mul_coord, inv_coord, single_self, hr]
  have e2 : (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) P' = (y : Af E) P' := by
    rw [Units.val_mul, mul_coord, inv_coord, suppAt_single P r P' hne, inv_one, one_mul]
  have hv := val_iota_eq_one hP ht
  have h0 : iota t P ≠ 0 := hr ▸ r.ne_zero
  constructor
  · rintro ⟨d, hd⟩
    have h1 := (le_exp_iff _).1 (hd P hP)
    have h2 := (le_exp_iff _).1 (hd P' hP')
    rw [e1] at h1
    rw [e2] at h2
    have h3 : d - a ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP', iota_sub, sub_coord]
      have := Valuation.map_sub_lt _ ha h2
      rwa [sub_sub_sub_cancel_left] at this
    have h4 : b - t * d ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP, iota_sub, iota_mul, sub_coord, mul_coord]
      have : iota b P - iota t P * iota d P =
          iota t P * ((iota t P)⁻¹ * (y : Af E) P - iota d P) - ((y : Af E) P - iota b P) := by
        rw [mul_sub, mul_inv_cancel_left₀ h0]; ring
      rw [this]
      refine Valuation.map_sub_lt _ ?_ hb
      rwa [map_mul, hv, one_mul]
    have := add_mem h4 (q.asIdeal.mul_mem_left t h3)
    convert this using 1
    ring
  · intro h
    refine ⟨a, fun R hR => (le_exp_iff _).2 ?_⟩
    rcases hall R hR with rfl | rfl
    · rw [← val_iota_lt_iff hP, iota_sub, iota_mul, sub_coord, mul_coord] at h
      have : (iota t R)⁻¹ * (y : Af E) R - iota a R =
          (iota t R)⁻¹ * (((y : Af E) R - iota b R) + (iota b R - iota t R * iota a R)) := by
        rw [sub_add_sub_cancel, mul_sub, inv_mul_cancel_left₀ h0]
      rw [e1, this, map_mul, map_inv₀, hv, inv_one, one_mul]
      exact Valuation.map_add_lt _ hb h
    · rwa [e2]

theorem notMem_of_approx {q : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)} (hP : Over P q)
    {x : P.adicCompletion E} (hx : Valued.v x = 1) {a : OF E} (ha : Valued.v (x - iota a P) < 1) : a ∉ q.asIdeal := by
  intro h
  have := Valuation.map_add_lt _ ha ((val_iota_lt_iff hP a).2 h)
  rw [sub_add_cancel, hx] at this
  exact lt_irrefl _ this

theorem exists_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : HeightOneSpectrum (OF E))
    (P : HeightOneSpectrum (𝓞 E)), Splits q → Over P q → ∃ R : Finset (P.adicCompletion E)ˣ,
      R.card + 1 = Ideal.absNorm q.asIdeal ∧ (∀ r ∈ R, Valued.v (r : P.adicCompletion E) = 1) ∧
      ∀ y : (Af E)ˣ, (∀ P', Over P' q → Valued.v ((y : Af E) P') = 1) →
        ∃! r, r ∈ R ∧ LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) := by
  intro E _ _ _ q P hs hP
  classical
  obtain ⟨htwo, hf⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E q hs
  obtain ⟨P', hne, hP'⟩ : ∃ P', P' ≠ P ∧ Over P' q := by
    obtain ⟨P₁, P₂, h, h1, h2⟩ := hs
    by_cases h' : P₁ = P
    · exact ⟨P₂, fun e => h (h'.trans e.symm), h2⟩
    · exact ⟨P₁, h', h1⟩
  have hall := htwo P P' hP hP' hne.symm
  haveI := q.isMaximal
  letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot
  letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _
  choose t ht using fun c : (OF E ⧸ q.asIdeal)ˣ => Ideal.Quotient.mk_surjective (c : OF E ⧸ q.asIdeal)
  have htq : ∀ c, t c ∉ q.asIdeal := fun c h => c.ne_zero (by rw [← ht c]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
  have h0 : ∀ c, iota (t c) P ≠ 0 := fun c h => by
    have := val_iota_eq_one hP (htq c)
    rw [h, map_zero] at this
    exact zero_ne_one this
  let u : (OF E ⧸ q.asIdeal)ˣ → (P.adicCompletion E)ˣ := fun c => Units.mk0 _ (h0 c)
  have hu : ∀ c, (u c : P.adicCompletion E) = iota (t c) P := fun c => rfl
  have hinj : Function.Injective u := fun c c' h => by
    have h1 : iota (t c) P = iota (t c') P := by rw [← hu, ← hu, h]
    have h2 : t c - t c' ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP, iota_sub, sub_coord, h1, sub_self, map_zero]
      exact zero_lt_one
    apply Units.ext
    rw [← ht c, ← ht c']
    exact Ideal.Quotient.eq.2 h2
  refine ⟨Finset.univ.image u, ?_, ?_, fun y hy => ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_units, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact Nat.sub_add_cancel Fintype.card_pos
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact val_iota_eq_one hP (htq c)
  · obtain ⟨a, ha⟩ := exists_iota_approx (hf P' hP').2.2 _ (hy P' hP').le
    obtain ⟨b, hb⟩ := exists_iota_approx (hf P hP).2.2 _ (hy P hP).le
    have ha0 : Ideal.Quotient.mk q.asIdeal a ≠ 0 := fun h =>
      notMem_of_approx hP' (hy P' hP') ha (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have hb0 : Ideal.Quotient.mk q.asIdeal b ≠ 0 := fun h =>
      notMem_of_approx hP (hy P hP) hb (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have key : ∀ c, LocIn 1 q (((single P (u c))⁻¹ * y : (Af E)ˣ) : Af E) ↔
        c = Units.mk0 _ hb0 * (Units.mk0 _ ha0)⁻¹ := fun c => by
      rw [locIn_iff hP hP' hne hall y ha hb (htq c) (u c) (hu c), ← Ideal.Quotient.eq, map_mul, ht, eq_mul_inv_iff_mul_eq,
        Units.ext_iff, Units.val_mul, Units.val_mk0, Units.val_mk0, eq_comm]
    refine ⟨u _, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key c).1 h]

end GlobalTheory.CMVal.Euler.Resid
end
end
