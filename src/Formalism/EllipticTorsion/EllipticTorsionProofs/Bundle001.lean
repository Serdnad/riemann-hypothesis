module

import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
public import Formalism.EllipticTorsion.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

noncomputable section

open PowerSeries

namespace Formalism.ELL.SubstitutionCoefficientCongruence

section Chain

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem coeff_subst_congr_lemma {R : Type*} [CommRing R] {σ : Type*}
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (n : ℕ) :
    ∀ e : σ →₀ ℕ, e.degree < n → MvPowerSeries.coeff e (a ^ n) = 0 := by
  classical
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    intro e he
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h2 : x.2 = 0
    · have h0 : MvPowerSeries.coeff 0 a = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
      rw [h2, h0, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).1 h)
      have hsum : x.1.degree + x.2.degree = e.degree := by rw [← map_add (f := _), hx]
      have h1 : x.1.degree < n := by omega
      rw [ih x.1 h1, zero_mul]

theorem coeff_subst_congr {g h : PowerSeries R} {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (e : σ →₀ ℕ)
    (hgh : ∀ k ≤ e.degree, coeff k g = coeff k h) :
    MvPowerSeries.coeff e (g.subst a) = MvPowerSeries.coeff e (h.subst a) := by
  classical
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k ≤ e.degree
  · rw [hgh k hk]
  · rw [coeff_subst_congr_lemma ha k e (by omega), smul_zero, smul_zero]

theorem pderiv_subst_coe (p : Polynomial R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv (R := R) i ((p : PowerSeries R).subst a) =
      (derivative (p : PowerSeries R)).subst a * MvPowerSeries.pderiv (R := R) i a := by
  apply Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_subst_coe <;> assumption

theorem degree_le_of_mem_antidiagonal [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, map_add (f := _)]
  exact Nat.le_add_right _ _

theorem pderiv_subst (g : PowerSeries R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv (R := R) i (g.subst a) =
      (derivative g).subst a * MvPowerSeries.pderiv (R := R) i a := by
  apply Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.pderiv_subst <;> assumption

end Chain

section Integral

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

theorem mem_unitBall {x : K} : x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem integral_one : Formalism.G.IntegralMv (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_mul {F G : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F)
    (hG : Formalism.G.IntegralMv G) : Formalism.G.IntegralMv (F * G) := by
  classical
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ =>
    Subring.mul_mem _ (mem_unitBall.2 (hF _)) (mem_unitBall.2 (hG _))

theorem integral_pow {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (n : ℕ) :
    Formalism.G.IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hF

theorem integral_pderiv {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (i : σ) :
    Formalism.G.IntegralMv (MvPowerSeries.pderiv (R := K) i F) := by
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_pderiv]
  refine Subring.mul_mem _ (mem_unitBall.2 (hF _)) ?_
  exact Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _)

theorem integral_subst {c : PowerSeries K} (hc : ∀ n, ‖coeff n c‖ ≤ 1)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : Formalism.G.IntegralMv f) : Formalism.G.IntegralMv (c.subst f) := by
  classical
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf0
  intro e
  rw [← mem_unitBall, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1)) ?_]
  · exact Subring.sum_mem _ fun d _ => by
      rw [smul_eq_mul]
      exact Subring.mul_mem _ (mem_unitBall.2 (hc d)) (mem_unitBall.2 (integral_pow hf d e))
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [coeff_subst_congr_lemma hf0 d e (by omega), smul_zero])

end Integral

end Formalism.ELL.SubstitutionCoefficientCongruence

namespace Formalism.ELL

theorem N_partial_derivative : NPderiv := by
  intro K _ _ _ σ G hG i
  obtain ⟨f, hf0, hf, rfl⟩ := hG
  unfold logOnePlus
  rw [SubstitutionCoefficientCongruence.pderiv_subst _ hf0]
  refine SubstitutionCoefficientCongruence.integral_mul ?_ (SubstitutionCoefficientCongruence.integral_pderiv hf i)
  refine SubstitutionCoefficientCongruence.integral_subst ?_ hf0 hf
  intro n
  unfold PowerSeries.log
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n)]
  have hn : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [map_div₀, map_pow, map_neg, map_one, map_natCast, Nat.cast_succ, div_mul_cancel₀ _ hn,
    norm_pow, norm_neg, norm_one, one_pow]

end Formalism.ELL
end
end

section

open PowerSeries IsUltrametricDist

universe u

namespace Formalism.ELL.MultiplicativeWeight

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)

def W (w : ℤ) (f : MvPowerSeries σ K) : Prop :=
  ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e f‖ ≤ c ^ (w - (e.degree : ℤ))

variable {c}

theorem W_one (hc : 0 < c) (_hc1 : c ≤ 1) : W c 0 (1 : MvPowerSeries σ K) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp only [norm_zero]; positivity

theorem W_mul (hc : 0 < c) {w₁ w₂ : ℤ} {f g : MvPowerSeries σ K} (hf : W c w₁ f) (hg : W c w₂ g) :
    W c (w₁ + w₂) (f * g) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖
      ≤ c ^ (w₁ - (p.1.degree : ℤ)) * c ^ (w₂ - (p.2.degree : ℤ)) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = c ^ (w₁ + w₂ - (e.degree : ℤ)) := by
        rw [← zpow_add₀ hc.ne', ← hp, map_add (f := _)]; push_cast; ring_nf

theorem W_pow (hc : 0 < c) (hc1 : c ≤ 1) {w : ℤ} {f : MvPowerSeries σ K} (hf : W c w f) (n : ℕ) :
    W c (n * w) (f ^ n) := by
  induction n with
  | zero => simpa using W_one hc hc1
  | succ n ih => rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact W_mul hc ih hf

theorem W_E (E : PowerSeries K) (hE : constantCoeff E = 0)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) (hc : 0 < c) (i : σ) :
    W c 1 (E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE, norm_zero]; positivity
    · conv_rhs => rw [h, Finsupp.degree_single]
      exact hb _ h0
  · rw [norm_zero]; positivity

theorem W_prod (hc : 0 < c) (hc1 : c ≤ 1) (a : σ → MvPowerSeries σ K) (ha : ∀ i, W c 1 (a i))
    (d : σ →₀ ℕ) : W c (d.degree : ℤ) (d.prod fun s n => a s ^ n) := by
  classical
  unfold Finsupp.prod
  have hdeg : (d.degree : ℤ) = ∑ s ∈ d.support, ((d s : ℕ) : ℤ) := by
    show (((∑ i ∈ d.support, d i : ℕ)) : ℤ) = _
    push_cast; rfl
  rw [hdeg]
  induction d.support using Finset.induction_on with
  | empty => simpa using W_one hc hc1
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    have := W_pow hc hc1 (ha s) (d s)
    rw [mul_one] at this
    exact W_mul hc this ih

theorem comp_exp_coeff_weight_of : CompExpWeight.{u} := by
  intro K _ _ σ _ c hc hc1 E hE hb G hG α
  classical
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := σ) (S := K)
    (a := fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K))
    fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE
  rw [MvPowerSeries.coeff_subst ha]
  have hfin := MvPowerSeries.coeff_subst_finite ha G α
  rw [finsum_eq_sum _ hfin]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d _ => ?_
  rw [smul_eq_mul, norm_mul]
  have h1 := W_prod hc hc1 _ (W_E E hE hb hc) d α
  calc ‖MvPowerSeries.coeff d G‖ * ‖MvPowerSeries.coeff α
          (d.prod fun s e => (E.subst (MvPowerSeries.X s : MvPowerSeries σ K)) ^ e)‖
      ≤ 1 * c ^ ((d.degree : ℤ) - (α.degree : ℤ)) :=
        mul_le_mul (hG d) h1 (norm_nonneg _) zero_le_one
    _ ≤ c ^ (-(α.degree : ℤ)) := by
        rw [one_mul]; exact zpow_le_zpow_right_of_le_one₀ hc hc1 (by omega)

end Formalism.ELL.MultiplicativeWeight

namespace Formalism.ELL

theorem comp_exp_coeff_weight : Formalism.ELL.CompExpWeight := Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of

end Formalism.ELL
end

section

namespace Formalism.ELL

namespace DeuringModel

open Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma norm_add_eq_left {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_nat_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

lemma exists_root_deuring [IsAlgClosed K] (j : K) :
    ∃ a : K, a ^ 3 * (a ^ 3 - 24) ^ 3 = j * (a ^ 3 - 27) := by
  let P : K[X] := X ^ 3 * (X ^ 3 - C 24) ^ 3 - C j * (X ^ 3 - C 27)
  have hdeg : P.degree = 12 := by
    simp only [P]
    compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P (by rw [hdeg]; norm_num)
  refine ⟨a, ?_⟩
  simp only [P, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha
  exact sub_eq_zero.mp ha

end DeuringModel

open DeuringModel in
theorem deuring_model : ModelDeuring := by
  intro K _ _ _ h3 j hj
  obtain ⟨a, ha⟩ := exists_root_deuring j
  have hc4 : (deuring a).c₄ = a * (a ^ 3 - 24) := by
    simp [deuring, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hΔ : (deuring a).Δ = a ^ 3 - 27 := by
    simp [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have h27 : ‖(27 : K)‖ = 1 := by
    have e : (27 : K) = 3 ^ 3 := by norm_num
    rw [e, norm_pow, h3, one_pow]
  have ha1 : ‖a‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hA3 : ‖a ^ 3‖ = ‖a‖ ^ 3 := norm_pow a 3
    have hbig : 1 < ‖a‖ ^ 3 := one_lt_pow₀ hlt (by norm_num)
    have h24 : ‖(24 : K)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one (K := K) 24
    have hn1 : ‖a ^ 3 - 24‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hn2 : ‖a ^ 3 - 27‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = ‖a‖ ^ 12 := by
      rw [norm_mul, hA3, norm_pow, hn1]
      ring
    have hR : ‖j * (a ^ 3 - 27)‖ ≤ ‖a‖ ^ 3 := by
      rw [norm_mul, hn2]
      calc ‖j‖ * ‖a‖ ^ 3 ≤ 1 * ‖a‖ ^ 3 := by gcongr
        _ = ‖a‖ ^ 3 := one_mul _
    rw [ha] at hL
    have hlt2 : ‖a‖ ^ 3 < ‖a‖ ^ 12 := pow_lt_pow_right₀ hlt (by norm_num)
    linarith
  have hA3le : ‖a ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha1
  have hΔle : ‖a ^ 3 - 27‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA3le (by rw [norm_neg, h27]))
  have hΔ1 : ‖a ^ 3 - 27‖ = 1 := by
    by_contra hne
    have hlt : ‖a ^ 3 - 27‖ < 1 := lt_of_le_of_ne hΔle hne
    have e1 : a ^ 3 = 27 + (a ^ 3 - 27) := by ring
    have hA : ‖a ^ 3‖ = 1 := by
      rw [e1, norm_add_eq_left (by rw [h27]; exact hlt), h27]
    have e2 : a ^ 3 - 24 = 3 + (a ^ 3 - 27) := by ring
    have hB : ‖a ^ 3 - 24‖ = 1 := by
      rw [e2, norm_add_eq_left (by rw [h3]; exact hlt), h3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = 1 := by
      rw [norm_mul, hA, norm_pow, hB]
      norm_num
    rw [ha, norm_mul] at hL
    have h4 : ‖j‖ * ‖a ^ 3 - 27‖ < 1 := by
      calc ‖j‖ * ‖a ^ 3 - 27‖ ≤ 1 * ‖a ^ 3 - 27‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hlt
    linarith
  refine ⟨a, ha1, ?_, ?_⟩
  · rw [hc4, hΔ, ← ha]
    ring
  · rw [hΔ, hΔ1]

end Formalism.ELL
end

section

universe u

namespace Formalism.ELL.unitAtAlt

open Formalism.ELL

lemma two_or_three {K : Type u} [NormedField K] [IsUltrametricDist K] :
    ‖(2 : K)‖ = 1 ∨ ‖(3 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h3 : ‖(3 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 3
  have h1 : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
    have : (1 : K) = 3 + -2 := by norm_num
    rw [this]
    simpa [norm_neg] using IsUltrametricDist.norm_add_le_max (3 : K) (-2)
  rw [norm_one] at h1
  by_cases h : ‖(2 : K)‖ = 1
  · exact Or.inl h
  · right
    have hlt : ‖(2 : K)‖ < 1 := lt_of_le_of_ne h2 h
    rcases le_max_iff.mp h1 with h' | h'
    · exact le_antisymm h3 h'
    · exact absurd h' (not_le.mpr hlt)

lemma of_model {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by
  have hne : W.Δ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΔ; exact zero_ne_one hΔ
  have : W.IsElliptic := ⟨hne.isUnit⟩
  refine ⟨W, inferInstance, hI, hΔ, ?_⟩
  rw [WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp

end Formalism.ELL.unitAtAlt

namespace Formalism.ELL

open Formalism.ELL.unitAtAlt

theorem modelUnit_of (hL : Formalism.ELL.ModelLegendre.{u}) (hD : Formalism.ELL.ModelDeuring.{u}) :
    Formalism.ELL.ModelUnit.{u} := by
  intro K _ _ _ j hj
  rcases two_or_three (K := K) with h2 | h3
  · obtain ⟨l, hl, _hl1, hc, hΔ⟩ := hL K h2 j hj
    refine of_model (legendre l) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [legendre]
    · simp
    · rw [norm_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      simp [hl]
    · simp
    · exact hl.le
    · simp
  · obtain ⟨a, ha, hc, hΔ⟩ := hD K h3 j hj
    refine of_model (deuring a) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [deuring]
    · exact ha
    all_goals simp

end Formalism.ELL
end
