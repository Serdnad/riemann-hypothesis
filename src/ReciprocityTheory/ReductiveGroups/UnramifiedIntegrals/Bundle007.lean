module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle004
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem qm_eq_qParam (m : ℕ) (τ : ℍ) : qm m τ = Function.Periodic.qParam (m : ℝ) τ := by
  simp [qm, Function.Periodic.qParam]

theorem qm_norm_lt_one {m : ℕ} (hm : 0 < m) (τ : ℍ) : ‖qm m τ‖ < 1 := by
  rw [qm_eq_qParam]
  exact Function.Periodic.norm_qParam_lt_one (by exact_mod_cast hm) τ.im_pos

theorem qm_surj {m : ℕ} (hm : 0 < m) {x : ℂ} (h0 : 0 < ‖x‖) (h1 : ‖x‖ < 1) : ∃ τ : ℍ, qm m τ = x := by
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg h0 h1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have him : 0 < (Function.Periodic.invQParam (m : ℝ) x).im := by
    rw [Function.Periodic.im_invQParam]
    refine mul_pos_of_neg_of_neg ?_ hlog
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨⟨_, him⟩, ?_⟩
  rw [qm_eq_qParam]
  exact Function.Periodic.qParam_right_inv hmR.ne' (norm_pos_iff.mp h0)

theorem qm_pow {m : ℕ} (hm : 0 < m) (τ : ℍ) : qm m τ ^ m = qm 1 τ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [qm, qm, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem qm_one_eq (τ : ℍ) : qm 1 τ = Function.Periodic.qParam 1 τ := by
  simpa using qm_eq_qParam 1 τ

theorem qm_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    qm 1 (pt a b e τ) = zetaC e ^ b * qm (a * e) τ ^ (a ^ 2) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  rw [qm, qm, zetaC, pt_coe ha he, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem IsMF.hasSum {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) :
    HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) := by
  obtain ⟨g, hg⟩ := hf
  have hgf : (⇑g : ℍ → ℂ) = f := funext hg
  have h := ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ
  rw [hgf, ← qm_one_eq] at h
  exact h

theorem IsMF.conv {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : Conv (qExpansion 1 f) := by
  apply conv_of_hasSum
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    exact (hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable
  · obtain ⟨τ, hτ⟩ := qm_surj one_pos (norm_pos_iff.mpr h0) hx
    rw [← hτ]
    exact (hf.hasSum τ).summable

theorem IsMF.ev_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) : ev (qExpansion 1 f) (qm 1 τ) = f τ := by
  exact (hf.hasSum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem twelve_dvd_five_pow_three_add_seven_pow_five (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have key : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * d ^ 3 + 7 * d ^ 5) 12).mp
    (by push_cast; exact key _)
  exact_mod_cast h

theorem sigma_congr (n : ℕ) :
    (12 : ℤ) ∣ 5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => twelve_dvd_five_pow_three_add_seven_pow_five _

def s3Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 3 n : ℤ)

def s5Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 5 n : ℤ)

def tZ : PowerSeries ℤ := PowerSeries.mk fun n =>
  (5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ)) / 12

theorem eisensteinFourInt_eq : e4Z = 1 + PowerSeries.C (240 : ℤ) * s3Z := by
  ext n
  simp only [e4Z, s3Z, map_add (f := _), PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem eisensteinSixInt_eq : e6Z = 1 - PowerSeries.C (504 : ℤ) * s5Z := by
  ext n
  simp only [e6Z, s5Z, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem tZ_mul : PowerSeries.C (12 : ℤ) * tZ =
    PowerSeries.C (5 : ℤ) * s3Z + PowerSeries.C (7 : ℤ) * s5Z := by
  ext n
  simp only [map_add (f := _), PowerSeries.coeff_C_mul, tZ, s3Z, s5Z, PowerSeries.coeff_mk]
  exact Int.mul_ediv_cancel' (sigma_congr n)

theorem eisenstein_cube_sub_sq_eq : e4Z ^ 3 - e6Z ^ 2 = PowerSeries.C (1728 : ℤ) *
    (tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 + PowerSeries.C (8000 : ℤ) * s3Z ^ 3
      - PowerSeries.C (147 : ℤ) * s5Z ^ 2) := by
  have h := tZ_mul
  rw [eisensteinFourInt_eq, eisensteinSixInt_eq]
  simp only [map_ofNat] at h ⊢
  linear_combination (-144 : PowerSeries ℤ) * h

theorem dZ_mul : PowerSeries.C (1728 : ℤ) * dZ = e4Z ^ 3 - e6Z ^ 2 := by
  ext n
  rw [PowerSeries.coeff_C_mul, dZ, PowerSeries.coeff_mk, eisenstein_cube_sub_sq_eq, PowerSeries.coeff_C_mul]
  exact Int.mul_ediv_cancel' (dvd_mul_right _ _)

private theorem dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq : dZ = tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 +
    PowerSeries.C (8000 : ℤ) * s3Z ^ 3 - PowerSeries.C (147 : ℤ) * s5Z ^ 2 := by
  have h := dZ_mul.trans eisenstein_cube_sub_sq_eq
  refine mul_left_cancel₀ (fun h0 => ?_) h
  have := congrArg PowerSeries.constantCoeff h0
  rw [PowerSeries.constantCoeff_C, map_zero] at this
  norm_num at this

theorem dZ_coeff_zero : PowerSeries.coeff 0 dZ = 0 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add (f := _), PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dZ_coeff_one : PowerSeries.coeff 1 dZ = 1 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add (f := _), PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dC_eq : dC = qExpansion 1 DD := by
  have h4 : qExpansion 1 ⇑((E₄.mul E₄).mul E₄) = qExpansion 1 E₄ ^ 3 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp), ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have h6 : qExpansion 1 ⇑(E₆.mul E₆) = qExpansion 1 E₆ ^ 2 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have hfun : DD = ⇑((1 / 1728 : ℂ) • ((E₄.mul E₄).mul E₄)) - ⇑((1 / 1728 : ℂ) • (E₆.mul E₆)) := by
    funext τ
    simp only [DD, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, Pi.sub_apply,
      ModularForm.coe_smul, ModularForm.coe_mul, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hd := congrArg (PowerSeries.map (Int.castRingHom ℂ)) dZ_mul
  rw [map_mul, map_sub, map_pow, map_pow, PowerSeries.map_C, map_eisensteinFourInt, map_eisensteinSixInt] at hd
  rw [hfun, ModularForm.qExpansion_sub one_pos (by simp), ModularForm.coe_smul, ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos (by simp), ModularForm.qExpansion_smul one_pos (by simp),
    h4, h6, ← smul_sub, ← hd, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  rw [show (1 / 1728 : ℂ) * (Int.castRingHom ℂ) 1728 = 1 by norm_num, map_one, one_mul]
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem rootPoly_monic' {E : Type} [Field E] (xs : Finset E) : (rootPoly xs).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

theorem rootPoly_inter_mul_sdiff {E : Type} [Field E] (xs ys : Finset E) :
    rootPoly (xs ∩ ys) * rootPoly (xs \ ys) = rootPoly xs := by
  unfold rootPoly
  rw [← Finset.prod_union (Finset.disjoint_sdiff_inter xs ys).symm, Finset.union_comm,
    Finset.sdiff_union_inter]

theorem rootPoly_isCoprime_of_disjoint {E : Type} [Field E] (xs ys : Finset E) (h : Disjoint xs ys) :
    IsCoprime (rootPoly xs) (rootPoly ys) := by
  unfold rootPoly
  refine IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy => ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  have hne : x ≠ y := fun e => Finset.disjoint_left.1 h hx (e ▸ hy)
  exact (sub_ne_zero.2 hne).isUnit

theorem exists_poly_map_subfield {E : Type} [Field E] [DecidableEq E] (k : Subfield E) (P : E[X])
    (h : ∀ i, P.coeff i ∈ k) : ∃ p : (k)[X], p.map k.subtype = P := by
  have : P ∈ Polynomial.lifts k.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  exact this

theorem rootPoly_inter_mem {E : Type} [Field E] (k : Subfield E) (xs ys : Finset E)
    (hx : ∀ i, (rootPoly xs).coeff i ∈ k) (hy : ∀ i, (rootPoly ys).coeff i ∈ k) :
    ∀ i, (rootPoly (xs ∩ ys)).coeff i ∈ k := by
  obtain ⟨p, hp⟩ := exists_poly_map_subfield k _ hx
  obtain ⟨q, hq⟩ := exists_poly_map_subfield k _ hy
  set R := rootPoly (xs ∩ ys) with hR
  set g0 := EuclideanDomain.gcd p q with hg0
  set g := g0.map k.subtype with hg
  have hgP : g ∣ rootPoly xs := by
    rw [← hp]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left p q)
  have hgQ : g ∣ rootPoly ys := by
    rw [← hq]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right p q)
  have hA := rootPoly_inter_mul_sdiff xs ys
  have hB := rootPoly_inter_mul_sdiff ys xs
  rw [Finset.inter_comm ys xs] at hB
  have hdisj : Disjoint (xs \ ys) (ys \ xs) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  obtain ⟨u, v, huv⟩ := rootPoly_isCoprime_of_disjoint _ _ hdisj
  have hgR : g ∣ R := by
    have : R = u * rootPoly xs + v * rootPoly ys := by
      rw [← hA, ← hB]
      linear_combination (-R) * huv
    rw [this]
    exact dvd_add (hgP.mul_left _) (hgQ.mul_left _)
  have hRg : R ∣ g := by
    have e : g = EuclideanDomain.gcd (rootPoly xs) (rootPoly ys) := by
      rw [← hp, ← hq, Polynomial.gcd_map]
    rw [e]
    exact EuclideanDomain.dvd_gcd ⟨_, hA.symm⟩ ⟨_, hB.symm⟩
  have hRm : R.Monic := rootPoly_monic' _
  have hg0' : g ≠ 0 := fun e => hRm.ne_zero (by simpa [e] using hgR)
  have hg00 : g0 ≠ 0 := fun e => hg0' (by rw [hg, e, Polynomial.map_zero])
  have hmon : (g0 * C g0.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hg00
  have hmon' : ((g0 * C g0.leadingCoeff⁻¹).map k.subtype).Monic := hmon.map _
  have hassoc : Associated ((g0 * C g0.leadingCoeff⁻¹).map k.subtype) R := by
    have h1 : Associated g R := associated_of_dvd_dvd hgR hRg
    refine Associated.trans ?_ h1
    rw [Polynomial.map_mul, Polynomial.map_C]
    refine (associated_mul_unit_left g _ ?_).symm.symm
    refine Polynomial.isUnit_C.2 (IsUnit.mk0 _ ?_)
    simpa using hg00
  have heq := eq_of_monic_of_associated hmon' hRm hassoc
  intro i
  rw [← heq, Polynomial.coeff_map]
  exact (((g0 * C g0.leadingCoeff⁻¹).coeff i)).2

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1.KE

open Formalism.L2.Th1.CM

theorem norm_le_one_of_integral {K R : Type*} [NormedField K] [IsUltrametricDist K] [CommRing R]
    [Algebra R K] (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (δ : K) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨p, hp, hpe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpe
  have h1 : δ ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hpe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ p.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R K (p.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ p.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ p.natDegree / ‖δ‖ < ‖δ‖ ^ p.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ p.natDegree‖ = ‖δ‖ ^ p.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith

theorem norm_int_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (n : ℤ) :
    ‖algebraMap ℤ K n‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_intCast_le_one K n

theorem norm_le_one_of_integral_int {K : Type*} [NormedField K] [IsUltrametricDist K] (δ : K)
    (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral norm_int_le_one δ h

theorem norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖x ^ i - y ^ i‖ ≤ ‖x - y‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : x ^ (i + 1) - y ^ (i + 1) = x * (x ^ i - y ^ i) + (x - y) * y ^ i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by gcongr
        _ = _ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖x - y‖ * ‖y‖ ^ i ≤ ‖x - y‖ * 1 := by
            gcongr; exact pow_le_one₀ (norm_nonneg _) hy
        _ = _ := mul_one _

theorem norm_eval_sub_eval_le {K : Type*} [NormedField K] [IsUltrametricDist K] (P : Polynomial K)
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖P.coeff i‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by
        gcongr
        · exact hP i
        · exact norm_pow_sub_pow_le hx hy i
    _ = _ := one_mul _

theorem finite_domain_frob (R : Type*) [CommRing R] [IsDomain R] [Finite R] (l : ℕ) (hl : l.Prime)
    (h0 : (l : R) = 0) : ∃ f : ℕ, 0 < f ∧ ∀ x : R, x ^ (l ^ f) = x := by
  classical
  have hch : CharP R l := (CharP.charP_iff_prime_eq_zero hl).mpr h0
  let _ := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R
  obtain ⟨n, -, hq⟩ := FiniteField.card R l
  exact ⟨n, n.pos, fun x => hq ▸ FiniteField.pow_card x⟩

theorem frob_fix_of_integral {K : Type*} [NormedField K] [IsUltrametricDist K] (l : ℕ)
    (hlp : l.Prime) (hl : ‖(l : K)‖ < 1) (δ : K) (hδ : IsIntegral ℤ δ) :
    ∃ f : ℕ, 0 < f ∧ ‖δ ^ (l ^ f) - δ‖ < 1 := by
  let A : Subalgebra ℤ K := Algebra.adjoin ℤ {δ}
  have hA : ∀ x : A, ‖(x : K)‖ ≤ 1 := fun x =>
    norm_le_one_of_integral norm_int_le_one _ (adjoin_le_integralClosure hδ x.2)
  let I : Ideal A :=
    { carrier := {x | ‖(x : K)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖((c * x : A) : K)‖ < 1
        rw [MulMemClass.coe_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hA c) (norm_nonneg _) hx }
  have hImem : ∀ x : A, x ∈ I ↔ ‖(x : K)‖ < 1 := fun x => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
      rw [hImem] at h1
      simp at h1
    · intro x y hxy
      by_contra hcon
      rw [not_or, hImem, hImem, not_lt, not_lt] at hcon
      rw [hImem, MulMemClass.coe_mul, norm_mul] at hxy
      have := one_le_mul_of_one_le_of_one_le hcon.1 hcon.2
      linarith
  have : Module.Finite ℤ A := Algebra.finite_adjoin_simple_of_isIntegral hδ
  have hl0 : ((l : ℕ) : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) l, Ideal.Quotient.eq_zero_iff_mem, hImem]
    have h2 : (((l : ℕ) : A) : K) = (l : K) := map_natCast A.val l
    rw [h2]
    exact hl
  have htors : Module.IsTorsion ℤ (A ⧸ I) := fun {x} =>
    ⟨⟨(l : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hlp.ne_zero)⟩, by
      change (l : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hl0, zero_mul]⟩
  have : Finite (A ⧸ I) := Module.finite_of_fg_torsion _ htors
  obtain ⟨f, hf, h⟩ := finite_domain_frob (A ⧸ I) l hlp hl0
  refine ⟨f, hf, ?_⟩
  let d : A := ⟨δ, Algebra.self_mem_adjoin_singleton ℤ δ⟩
  have h3 := h (Ideal.Quotient.mk I d)
  rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hImem] at h3
  exact h3

variable (l : ℕ) [Fact l.Prime]

theorem rmu_isIntegral_int {x : ℂ_[l]} (hx : x ∈ Rmu l) : IsIntegral ℤ x := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨n, hn, -, h⟩ := hx
    exact IsIntegral.of_pow hn (h ▸ isIntegral_one)
  | zero => exact isIntegral_zero
  | one => exact isIntegral_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

theorem isIntegral_int_of_rmu (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) :
    (Int.castRingHom ℂ_[l]).IsIntegralElem δ := by
  have : Algebra.IsIntegral ℤ (Rmu l) := ⟨fun x => by
    have := rmu_isIntegral_int l x.2
    exact (isIntegral_algebraMap_iff (A := Rmu l) (B := ℂ_[l]) ).mp this⟩
  have h : IsIntegral ℤ δ := isIntegral_trans δ hδ
  exact (Subsingleton.elim (algebraMap ℤ ℂ_[l]) (Int.castRingHom ℂ_[l])) ▸ h

theorem tch_mem_rmu {x : ℂ_[l]} (hx : x ∈ Tch l) : x ∈ Rmu l := by
  rcases hx with rfl | hx
  · exact (Rmu l).zero_mem
  · exact Subring.subset_closure hx

end ReciprocityTheory.ChartRestriction.L1.KE
end
end
