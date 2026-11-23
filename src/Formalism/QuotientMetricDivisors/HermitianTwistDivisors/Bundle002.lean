module

public import Formalism.QuotientMetricDivisors.Bundle004
public import Formalism.QuotientMetricDivisors.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Matrix.Order
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
public import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

theorem log_abs_norm_eq_two_sum (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (a : K) (ha : a ≠ 0) :
    Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      2 * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ := by
  have h := NumberField.InfinitePlace.prod_eq_abs_norm a
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := fun w => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w))]
  have hpos : ∀ w : InfinitePlace K, w a ≠ 0 := fun w => by
    rw [← InfinitePlace.norm_embedding_eq]
    simpa using ha
  rw [← Rat.cast_abs, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (hpos w)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hm, Real.log_pow, InfinitePlace.norm_embedding_eq]
  push_cast
  ring

theorem prod_formula' : ProdFormula := by
  intro K _ _ _ _ a ha
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := FractionalIdeal.spanSingleton _ a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have hfin : {w : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  have hvw : ∀ w : HeightOneSpectrum (𝓞 K), vw w a = FractionalIdeal.count K w I := fun w => rfl
  have hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)) ⊆
      (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    simp only [Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
    intro h0
    apply hw
    simp [hvw, h0]
  refine ⟨hfin.subset (by simpa using hsupp), ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpos : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := fun w => by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hN : (|Algebra.norm ℚ a| : ℚ) = ∏ w ∈ hfin.toFinset,
      ((Ideal.absNorm w.asIdeal : ℚ)) ^ FractionalIdeal.count K w I := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), ← hIdef]
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) ?_, map_prod]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    · intro w hw
      simp only [Function.mem_mulSupport, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
      intro h0
      apply hw
      rw [h0, zpow_zero]
  have hlog : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ w ∈ hfin.toFinset,
      (FractionalIdeal.count K w I : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    have h1 : |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w ∈ hfin.toFinset,
        ((Ideal.absNorm w.asIdeal : ℝ)) ^ FractionalIdeal.count K w I := by
      rw [← Rat.cast_abs, hN]
      push_cast
      rfl
    rw [h1, Real.log_prod (fun w _ => zpow_ne_zero _ (hpos w))]
    exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _
  have hB := log_abs_norm_eq_two_sum K a ha
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  calc (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖
      = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / finrank ℚ K := by
        rw [hB]
        field_simp
    _ = ∑ w ∈ hfin.toFinset, lw w * (vw w a : ℝ) := by
        rw [hlog, Finset.sum_div]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hvw, lw]
        ring

end Formalism.DivisionValues
end
end

section

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Formalism.DivisionValues

lemma one_le_det_one_add {m : Type*} [Fintype m] [DecidableEq m] {Z : Matrix m m ℂ}
    (hZ : Z.PosSemidef) : (1 : ℂ) ≤ (1 + Z).det := by
  have hspec := hZ.1.spectral_theorem
  have hUU : (hZ.1.eigenvectorUnitary : Matrix m m ℂ) * star (hZ.1.eigenvectorUnitary : Matrix m m ℂ) = 1 := by
    simp
  have hdet : ∀ x : Matrix m m ℂ, ((hZ.1.eigenvectorUnitary : Matrix m m ℂ) * x *
      star (hZ.1.eigenvectorUnitary : Matrix m m ℂ)).det = x.det := by
    intro x
    rw [det_mul, det_mul, mul_comm (det (hZ.1.eigenvectorUnitary : Matrix m m ℂ)), mul_assoc, ← det_mul, hUU,
      det_one, mul_one]
  have key : 1 + Z = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hZ.1.eigenvectorUnitary)
      (1 + diagonal (RCLike.ofReal ∘ hZ.1.eigenvalues)) := by
    rw [map_add (f := _), map_one, ← hspec]
  rw [key, Unitary.conjStarAlgAut_apply, hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have hev := hZ.eigenvalues_nonneg
  have hprod : ∏ i, ((1 : ℂ) + (RCLike.ofReal ∘ hZ.1.eigenvalues) i) =
      ((∏ i, (1 + hZ.1.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, ← Complex.ofReal_one, Complex.real_le_real]
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => by linarith [hev i])

lemma det_le_det_add {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix m m ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : X.det ≤ (X + Y).det := by
  by_cases hXu : IsUnit X
  · have hX0 : (0 : Matrix m m ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
    have hSS : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX0
    have hS0 : (0 : Matrix m m ℂ) ≤ CFC.sqrt X := CFC.sqrt_nonneg X
    set S := CFC.sqrt X with hSdef
    have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS0
    have hSh : Sᴴ = S := hSpsd.1
    have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS ▸ hXu)
    have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
    have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
    have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
    have hTh : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSh]
    have hZ : ((S⁻¹)ᴴ * Y * S⁻¹).PosSemidef := hY.conjTranspose_mul_mul_same _
    have hmid : S * (S⁻¹ * Y * S⁻¹) * S = Y := by
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, mul_assoc, h2, mul_one]
    have hsum : X + Y = S * (1 + (S⁻¹)ᴴ * Y * S⁻¹) * S := by
      rw [hTh, mul_add, add_mul, mul_one, hSS, hmid]
    have hdX : X.det = S.det * S.det := by rw [← hSS, det_mul]
    rw [hsum, det_mul, det_mul]
    have e : S.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det * S.det = X.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det := by
      rw [hdX]; ring
    rw [e]
    have hone := one_le_det_one_add hZ
    have hXd : 0 ≤ X.det := hX.det_nonneg
    have := mul_le_mul_of_nonneg_left hone hXd
    simpa using this
  · have hd : X.det = 0 := by
      by_contra h
      exact hXu ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr h))
    rw [hd]
    exact (hX.add hY).det_nonneg

theorem determinant_cauchy_schwarz : DetCS := by
  intro n D Hc hHc A B
  have hHh : Hcᴴ = Hc := hHc.1
  have hPpsd : (A * Hc * Aᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same A
  set P := A * Hc * Aᴴ with hP
  set Q := A * Hc * Bᴴ with hQ
  set R := B * Hc * Bᴴ with hR
  by_cases hPu : IsUnit P
  · have hPpd : P.PosDef := (hPpsd.posDef_iff_isUnit).mpr hPu
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
    have hPinv : (P⁻¹).PosSemidef := hPpd.inv.posSemidef
    have hPih : (P⁻¹)ᴴ = P⁻¹ := hPinv.1
    have hQh : Qᴴ = B * Hc * Aᴴ := by
      rw [hQ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
    set K := B - Qᴴ * P⁻¹ * A with hK
    have hKpsd : (K * Hc * Kᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same K
    have hXpsd : (Qᴴ * P⁻¹ * Q).PosSemidef := hPinv.conjTranspose_mul_mul_same Q
    have hKh : Kᴴ = Bᴴ - Aᴴ * P⁻¹ * Q := by
      rw [hK, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPih]
      simp only [Matrix.mul_assoc]
    have r1 : B * (Hc * Bᴴ) = R := by rw [hR, Matrix.mul_assoc]
    have r2 : ∀ X : Matrix (Fin D) (Fin D) ℂ, B * (Hc * (Aᴴ * X)) = Qᴴ * X := by
      intro X; rw [hQh]; simp only [Matrix.mul_assoc]
    have r3 : A * (Hc * Bᴴ) = Q := by rw [hQ, Matrix.mul_assoc]
    have r4 : ∀ X : Matrix (Fin D) (Fin D) ℂ, A * (Hc * (Aᴴ * X)) = P * X := by
      intro X; rw [hP]; simp only [Matrix.mul_assoc]
    have r5 : ∀ X : Matrix (Fin D) (Fin D) ℂ, P⁻¹ * (P * X) = X := by
      intro X; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet, one_mul]
    have hKK : K * Hc * Kᴴ = R - Qᴴ * P⁻¹ * Q := by
      rw [hKh, hK]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      rw [r2, r3, r4, r5, r1]
      abel
    have hsplit : R = Qᴴ * P⁻¹ * Q + K * Hc * Kᴴ := by rw [hKK]; abel
    have hle := det_le_det_add hXpsd hKpsd
    rw [← hsplit, det_mul, det_mul, det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hle
    obtain ⟨hpre, hpim⟩ := Complex.lt_def.mp hPpd.det_pos
    have key : ∀ pr : ℝ, star Q.det * (pr : ℂ)⁻¹ * Q.det = ((‖Q.det‖ ^ 2 / pr : ℝ) : ℂ) := by
      intro pr
      rw [mul_right_comm, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    have hpeq : P.det = ((P.det.re : ℝ) : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; simpa using hpim.symm)
    rw [hpeq, key] at hle
    have h2 := (Complex.le_def.mp hle).1
    rw [Complex.ofReal_re] at h2
    have hpre' : 0 < P.det.re := by simpa using hpre
    rw [div_le_iff₀ hpre'] at h2
    rw [mul_comm]
    exact h2
  · have hd : P.det = 0 := by
      by_contra h
      exact hPu ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr h))
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have hw : v ᵥ* A = 0 := by
      by_contra hw
      have hsw : star (v ᵥ* A) ≠ 0 := star_ne_zero.mpr hw
      have hpos := hHc.dotProduct_mulVec_pos hsw
      have h0 : star (star (v ᵥ* A)) ⬝ᵥ (Hc *ᵥ star (v ᵥ* A)) = 0 := by
        rw [star_star]
        have h00 : (v ᵥ* P) ⬝ᵥ star v = 0 := by rw [hv, zero_dotProduct]
        rw [hP, ← vecMul_vecMul, ← vecMul_vecMul, ← dotProduct_mulVec, mulVec_conjTranspose, star_star,
          ← dotProduct_mulVec] at h00
        exact h00
      rw [h0] at hpos
      exact lt_irrefl _ hpos
    have hq : Q.det = 0 := by
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hv0, ?_⟩
      rw [hQ, ← vecMul_vecMul, ← vecMul_vecMul, hw, zero_vecMul, zero_vecMul]
    rw [hq, hd]
    simp

end Formalism.DivisionValues
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationZeroReduction

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_eq_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {s} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hs0
  classical
  have hnd : ¬ w.asIdeal ∣ Ideal.span {s} := by
    rw [Ideal.dvd_span_singleton]; exact hs
  have hirr : Irreducible w.asIdeal := (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible
  have hc := mt (Associates.count_ne_zero_iff_dvd hJ hirr).mp hnd
  push_neg at hc
  unfold vw
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ, Nat.cast_eq_zero]
  convert hc

end ValuationZeroReduction

theorem reduction_first_step : StepA := by
  intro K _ _ _ w n D M π ι B P ζ σ hζ hvζ hP hM x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ w.asIdeal := hs
  obtain ⟨y, hy, hyx⟩ := hsx
  obtain ⟨F, hF, hFy⟩ := hy
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hFy hyx
  have hs0 : s ≠ 0 := fun h => hs' (h ▸ w.asIdeal.zero_mem)
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h; apply hs0; apply IsFractionRing.injective (𝓞 K) K; rw [map_zero]; exact h
  have hPF : P F = ζ * (algebraMap (𝓞 K) K s * B x) := by
    rw [hP F, hFy, hyx, ← algebraMap_smul K s x, map_smul, smul_eq_mul]
  have hvmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b := by
    intro a b ha hb
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w
      (fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))
      (fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))]
  have hv0 : vw w (algebraMap (𝓞 K) K s) = 0 := ValuationZeroReduction.vw_eq_zero_of_not_mem w s hs'
  by_cases hBx : B x = 0
  · exact Or.inl hBx
  · right
    have hPF0 : P F ≠ 0 := by rw [hPF]; exact mul_ne_zero hζ (mul_ne_zero hsK hBx)
    rcases hM F hF with h0 | hσ
    · exact absurd h0 hPF0
    · rw [hPF, hvmul _ _ hζ (mul_ne_zero hsK hBx), hvmul _ _ hsK hBx, hvζ, hv0] at hσ
      simpa using hσ

end Formalism.DivisionValues
end
end

section

open Finset

noncomputable section

namespace Formalism.DivisionValues

theorem divisor_bounds_sum : BoundsSum := by
  intro Pl J _ S D hD lcvR logκ LG E3 lcvM L E1 E2 l ell vG g I Ic jT F err Jx η hl h0 hvG hLG hL
    hI hjT hE1 hE2 hE3
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : ∑ j, lcvM j ≤ (D : ℝ) * ∑ j, L j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have := (div_le_iff₀ hDr).1 (hL j)
      linarith
  have h2 : ∑ w ∈ S, l w * vG w ≤ (D : ℝ) * LG := by
    calc ∑ w ∈ S, l w * vG w ≤ ∑ w ∈ S, (D : ℝ) * (l w * g w) :=
          Finset.sum_le_sum fun w hw => by
            have := mul_le_mul_of_nonneg_left (hvG w hw) (hl w)
            linarith
      _ = (D : ℝ) * ∑ w ∈ S, l w * g w := by rw [Finset.mul_sum]
      _ ≤ (D : ℝ) * LG := mul_le_mul_of_nonneg_left hLG hDr.le
  have f1 : ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) =
      ∑ w ∈ S, l w * vG w + ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) +
        ∑ w ∈ S, l w * ∑ j, jT w j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_add_distrib]
    ring
  have f4 : ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) ≤
      (D : ℝ) * 2 * ∑ w ∈ S, l w * ∑ j, F w j + (D : ℝ) * ∑ w ∈ S, l w * ∑ j, err w j +
        (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h := mul_le_mul_of_nonneg_left (hI w hw) (hl w)
    have e : ∑ j, (2 * F w j + err w j) = 2 * ∑ j, F w j + ∑ j, err w j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [e] at h
    linarith
  have f6 : ∑ w ∈ S, l w * ∑ j, jT w j ≤
      (D : ℝ) * ∑ w ∈ S, l w * ∑ j, Jx w j + ∑ w ∈ S, l w * ∑ j, η w j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h : ∑ j, jT w j ≤ (D : ℝ) * ∑ j, Jx w j + ∑ j, η w j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by have := hjT w hw j; linarith
    have := mul_le_mul_of_nonneg_left h (hl w)
    linarith
  have eswap : ∀ f : Pl → J → ℝ, ∑ j, ∑ w ∈ S, l w * f w j = ∑ w ∈ S, l w * ∑ j, f w j := by
    intro f
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have f8 : ∑ w ∈ S, l w * ∑ j, err w j + ∑ w ∈ S, l w * ∑ j, Jx w j ≤ ∑ j, E1 j := by
    rw [← eswap, ← eswap, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by
      refine le_trans (le_of_eq ?_) (hE1 j)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
  have f9 : ∑ w ∈ S, l w * ∑ j, η w j ≤ (D : ℝ) * ∑ j, E2 j := by
    rw [← eswap, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have h := hE2 j
      rw [← Finset.sum_div] at h
      have := (div_le_iff₀ hDr).1 h
      linarith
  have f10 : (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ (D : ℝ) * E3 :=
    mul_le_mul_of_nonneg_left hE3 hDr.le
  have f11 : ∑ j, (E1 j + E2 j) = ∑ j, E1 j + ∑ j, E2 j := Finset.sum_add_distrib
  have eF := eswap F
  rw [div_le_iff₀ hDr]
  have hD0 : (0 : ℝ) ≤ D := hDr.le
  nlinarith [h0, h1, h2, f1, f4, f6, f8, f9, f10, f11, eF, mul_le_mul_of_nonneg_left f8 hD0]

end Formalism.DivisionValues
end
end
