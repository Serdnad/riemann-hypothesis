module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle001
public import Formalism.GL3MeanSquares.Bundle003
public import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Th1.B

open PowerSeries

section Rules

variable {K : Type} [Field K] [CharZero K]

theorem dz_ofNat (n : ℕ) [n.AtLeastTwo] : dz (OfNat.ofNat n : PowerSeries K) = 0 := by
  rw [show (OfNat.ofNat n : PowerSeries K) = C (OfNat.ofNat n : K) from (map_ofNat C n).symm]
  exact PowerSeries.derivative_C

theorem dz_one : dz (1 : PowerSeries K) = 0 := by
  exact Derivation.map_one_eq_zero _

theorem dz_C (a : K) : dz (C a : PowerSeries K) = 0 := PowerSeries.derivative_C

theorem dz_X : dz (X : PowerSeries K) = 1 := PowerSeries.derivative_X

theorem dz_add (f g : PowerSeries K) : dz (f + g) = dz f + dz g := map_add _ f g

theorem dz_sub (f g : PowerSeries K) : dz (f - g) = dz f - dz g := map_sub _ f g

theorem dz_neg (f : PowerSeries K) : dz (-f) = -dz f := map_neg _ f

theorem dz_mul (f g : PowerSeries K) : dz (f * g) = f * dz g + g * dz f := by
  simp only [dz, Derivation.leibniz, smul_eq_mul]

theorem dz_two : dz (2 : PowerSeries K) = 0 := dz_ofNat 2

theorem dz_four : dz (4 : PowerSeries K) = 0 := dz_ofNat 4

theorem two_ne : (2 : PowerSeries K) ≠ 0 := by
  intro h
  have h2 := congrArg (constantCoeff (R := K)) h
  rw [map_ofNat, map_zero] at h2
  exact two_ne_zero h2

theorem dz_sq (f : PowerSeries K) : dz (f ^ 2) = 2 * f * dz f := by
  rw [pow_two, dz_mul]
  ring

theorem dz_cube (f : PowerSeries K) : dz (f ^ 3) = 3 * f ^ 2 * dz f := by
  rw [pow_succ, dz_mul, dz_sq]
  ring

theorem dz_X_pow (n : ℕ) : dz ((X : PowerSeries K) ^ (n + 1)) = ((n : PowerSeries K) + 1) * X ^ n := by
  induction n with
  | zero => simp [dz_X]
  | succ n ih =>
    rw [pow_succ, dz_mul, ih, dz_X]
    push_cast
    ring

theorem X_ne : (X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero

theorem ne_zero_of_constantCoeff {f : PowerSeries K} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (map_zero _)

end Rules

theorem weierstrassReducedEquations : WpReduced := by
  intro K _ _ g2 g3 P hP
  obtain ⟨_, _, hE⟩ := hP
  have E1 : X ^ 4 * dz P ^ 2 - 4 * X * dz P =
      12 * P + 12 * X ^ 2 * P ^ 2 + 4 * X ^ 4 * P ^ 3 - C g2 * X ^ 2 * (1 + X ^ 2 * P) -
        C g3 * X ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne (K := K)))
    linear_combination hE
  refine ⟨E1, ?_⟩
  have hg : (C g2 : PowerSeries K) = 2 * C (g2 / 2) := by
    rw [← map_ofNat C 2, ← map_mul]
    congr 1
    field_simp
  rw [hg] at E1
  have d4 : dz ((X : PowerSeries K) ^ 4) = 4 * X ^ 3 := by
    rw [show (X : PowerSeries K) ^ 4 = (X ^ 2) ^ 2 by ring, dz_sq, dz_sq, dz_X]
    ring
  have hdiff : 4 * X ^ 3 * dz P ^ 2 + 2 * X ^ 4 * dz P * dz (dz P) - 4 * dz P - 4 * X * dz (dz P) =
      12 * dz P + 24 * X * P ^ 2 + 24 * X ^ 2 * P * dz P + 16 * X ^ 3 * P ^ 3 +
        12 * X ^ 4 * P ^ 2 * dz P - 2 * C (g2 / 2) * (2 * X + 4 * X ^ 3 * P + X ^ 4 * dz P) -
        4 * C g3 * X ^ 3 := by
    have h := congrArg dz E1
    have c12 : dz (12 : PowerSeries K) = 0 := dz_ofNat 12
    simp only [dz_add, dz_sub, dz_mul, dz_sq, dz_cube, dz_C, dz_X, dz_two, dz_four, c12, dz_one, d4] at h
    linear_combination h
  refine mul_left_cancel₀ (?_ : (2 * X * (X ^ 3 * dz P - 2) : PowerSeries K) ≠ 0) ?_
  · refine mul_ne_zero (mul_ne_zero two_ne X_ne) (ne_zero_of_constantCoeff ?_)
    rw [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, map_ofNat]
    norm_num
  · linear_combination X ^ 2 * hdiff - 4 * X * E1

theorem invertedSecondDeriv : WSecond := by
  intro K _ _ A kap w hw
  obtain ⟨h0, h2, hE⟩ := hw
  have e1 : constantCoeff (dz w) = PowerSeries.coeff 1 w := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  have h1 : PowerSeries.coeff 1 w = 0 := by
    have hc := congrArg (constantCoeff (R := K)) hE
    simpa [e1, h0] using hc
  refine ⟨h1, ?_⟩
  have hd : dz w ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) h
    rw [PowerSeries.coeff_derivative, h2] at hc
    norm_num at hc
  have hdiff := congrArg dz hE
  simp only [dz_sq, dz_add, dz_mul, dz_cube, dz_C, dz_four] at hdiff
  refine mul_left_cancel₀ (mul_ne_zero two_ne hd) ?_
  linear_combination hdiff

theorem shiftedReciprocalInverted : WOfWp := by
  intro K _ _ g2 g3 e1 P hP he
  obtain ⟨_, _, hE⟩ := hP
  have hu : constantCoeff (1 + X ^ 2 * P - C e1 * X ^ 2) ≠ 0 := by simp
  have hw : (1 + X ^ 2 * P - C e1 * X ^ 2) * wOf e1 P = X ^ 2 := by
    rw [wOf, mul_left_comm, PowerSeries.mul_inv_cancel _ hu, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [wOf]
    simp
  · rw [wOf, PowerSeries.coeff_X_pow_mul']
    simp [PowerSeries.constantCoeff_inv]
  · have hdu : dz (1 + X ^ 2 * P - C e1 * X ^ 2) = 2 * X * P + X ^ 2 * dz P - 2 * C e1 * X := by
      simp only [dz_add, dz_sub, dz_mul, dz_one, dz_C, dz_X, dz_sq]
      ring
    have hd := congrArg dz hw
    rw [dz_mul, hdu, dz_sq, dz_X] at hd

    have hA : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -X * (X ^ 3 * dz P - 2) := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) * hd - (2 * X * P + X ^ 2 * dz P - 2 * C e1 * X) * hw
    have h1 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P = X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * hw
    have h2 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 2 = X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2) * hw
    have h3 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 3 = X ^ 6 * (1 + X ^ 2 * P - C e1 * X ^ 2) := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P ^ 2 + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * wOf e1 P + X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2)) * hw
    have hg4 : (C g2 : PowerSeries K) = 4 * C (g2 / 4) := by
      rw [← map_ofNat C 4, ← map_mul]
      congr 1
      field_simp
    rw [hg4] at hE
    have he' : 4 * C e1 ^ 3 - 4 * C (g2 / 4) * C e1 - C g3 = (0 : PowerSeries K) := by
      have hc := congrArg (C (R := K)) he
      rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_ofNat, map_zero, hg4] at hc
      linear_combination hc
    rw [show (C (3 * e1) : PowerSeries K) = 3 * C e1 by rw [map_mul, map_ofNat],
      show (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 3 * C e1 ^ 2 - C (g2 / 4) by
        rw [map_sub, map_mul, map_pow, map_ofNat]]
    refine mul_left_cancel₀ (pow_ne_zero 4 (ne_zero_of_constantCoeff hu)) ?_
    linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) - X * (X ^ 3 * dz P - 2)) * hA - 4 * h1 -
      12 * C e1 * h2 - 4 * (3 * C e1 ^ 2 - C (g2 / 4)) * h3 + X ^ 2 * hE + X ^ 8 * he'

end Formalism.L2.Th1.B
end
end

section

noncomputable section

namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)

variable {K ι : Type} [NormedField K] [CharZero K]

theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam (n • f) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul]; exact inLam_nsmul hf m
  · rw [neg_zsmul, natCast_zsmul]; exact inLam_neg (inLam_nsmul hf m)

theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [simeq_iff]
    have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
    rw [e]; exact inLam_add h (inLam_neg h')
  · rw [simeq_iff]
    have e : -f - -g = -(f - g) := by ring
    rw [e]; exact inLam_neg h
  · rw [simeq_iff]
    have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
      rw [zsmul_eq_mul]; ring
    rw [e]; exact inLam_zsmul h n

theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h

end Formalism.L2.Th1.B.Sim
end
end

section

noncomputable section

namespace Formalism.L2.Th1.B.Map

open Formalism.InvariantFactorPaths.G7 (at1 cob)

variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')

theorem map_psubst {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.map j a) (PowerSeries.map j f) := by
  have ha' : MvPowerSeries.constantCoeff (MvPowerSeries.map j a) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, ha, map_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero ha'
  ext e
  rw [MvPowerSeries.coeff_map, PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs',
    map_finsum j (PowerSeries.coeff_subst_finite hs f e)]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, PowerSeries.coeff_map, ← map_pow (MvPowerSeries.map j),
    MvPowerSeries.coeff_map]

theorem map_psubst' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    PowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (PowerSeries.map j a) (PowerSeries.map j f) :=
  map_psubst j (ι := Unit) ha f

theorem map_fExp {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.map j (fExp a) = fExp (MvPowerSeries.map j a) := by
  unfold Formalism.L2.Th1.B.fExp
  rw [map_psubst j ha, PowerSeries.map_exp]

theorem map_fExp' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.map j (fExp a) = fExp (PowerSeries.map j a) :=
  map_fExp j (ι := Unit) ha

theorem map_fLog {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 1) :
    MvPowerSeries.map j (fLog a) = fLog (MvPowerSeries.map j a) := by
  have h' : MvPowerSeries.constantCoeff (a - 1) = 0 := by rw [map_sub, ha, map_one, sub_self]
  unfold Formalism.L2.Th1.B.fLog
  rw [map_psubst j h', map_sub, map_one, PowerSeries.map_log]

theorem map_fLog' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 1) :
    PowerSeries.map j (fLog a) = fLog (PowerSeries.map j a) :=
  map_fLog j (ι := Unit) ha

theorem map_prim (f : PowerSeries K) :
    PowerSeries.map j (prim f) = prim (PowerSeries.map j f) := by
  ext n
  simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_div₀, map_natCast]

theorem map_lU (l : PowerSeries K) :
    PowerSeries.map j (lU l) = lU (PowerSeries.map j l) := by
  ext n
  simp only [Formalism.L2.Th1.B.lU, PowerSeries.coeff_map, PowerSeries.coeff_mk]

private theorem powerSeries_constantCoeff_map' (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.map j f) = j (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map]

theorem map_inv' {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.map j f⁻¹ = (PowerSeries.map j f)⁻¹ := by
  have h' : PowerSeries.constantCoeff (PowerSeries.map j f) ≠ 0 := by
    rw [powerSeries_constantCoeff_map']; exact (map_ne_zero j).mpr hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h', ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]

theorem map_sigS (P : PowerSeries K) :
    PowerSeries.map j (sigS P) = sigS (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, map_prim, map_prim]

theorem cc_sigS (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigmaOneSeries e1 kap w) = sigmaOneSeries (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, map_prim, map_prim, map_add (f := _), map_mul, PowerSeries.map_C,
    PowerSeries.map_C]

theorem cc_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sigma (P : PowerSeries K) :
    PowerSeries.map j (sigma P) = sigma (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigma
  rw [map_mul, PowerSeries.map_X, map_fExp' j (cc_sigS P),
    map_sigS]

theorem map_sgStar (s2 : K) (P : PowerSeries K) :
    PowerSeries.map j (sgStar s2 P) = sgStar (j s2) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0 := by
    simp
  unfold Formalism.L2.Th1.B.sgStar
  rw [map_mul, map_sigma, map_fExp' j hc, map_neg, map_mul, PowerSeries.map_C,
    map_pow, PowerSeries.map_X, map_div₀, map_ofNat]

theorem map_sigma1 (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigma1
  rw [map_fExp' j (cc_sig1S e1 kap w), map_sig1S]

theorem map_wOf (e1 : K) (P : PowerSeries K) :
    PowerSeries.map j (wOf e1 P) = wOf (j e1) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) ≠ 0 := by
    simp
  unfold Formalism.L2.Th1.B.wOf
  rw [map_mul, map_inv' j hc]
  simp only [map_pow, map_sub, map_add (f := _), map_one, map_mul, PowerSeries.map_X, PowerSeries.map_C]

theorem map_phO (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.map j (phO s2 P l) = phO (j s2) (PowerSeries.map j P) (PowerSeries.map j l) := by
  have hd : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.B.lU, PowerSeries.coeff_mk, zero_add, h1]
  unfold Formalism.L2.Th1.B.phO
  rw [map_sub, map_add (f := _), map_neg, map_psubst' j h0, map_sigS, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow, map_fLog' j hd, map_lU]

theorem map_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) :
    PowerSeries.map j (phE s2 e1 kap w l) =
      phE (j s2) (j e1) (j kap) (PowerSeries.map j w) (PowerSeries.map j l) := by
  unfold Formalism.L2.Th1.B.phE
  rw [map_add (f := _), map_neg, map_psubst' j h0, map_sig1S, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow]

theorem map_inVar {ι : Type} (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map j (at1 x f) = at1 x (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.at1
  rw [map_psubst j (MvPowerSeries.constantCoeff_X x), MvPowerSeries.map_X]

theorem map_cob {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.cob
  rw [map_sub, map_sub, map_psubst j hF, map_inVar, map_inVar]

theorem baseChangeCompatible : BaseChange := by
  intro K K' _ _ _ _ j s2 e1 kap P w l F h0 h1 hF
  exact ⟨map_sigma j P, map_sgStar j s2 P, map_sigma1 j e1 kap w,
    map_wOf j e1 P, map_phO j s2 P h0 h1,
    map_phE j s2 e1 kap w h0, fun f => map_cob j hF f⟩

end Formalism.L2.Th1.B.Map
end
end
