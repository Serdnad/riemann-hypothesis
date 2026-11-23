module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle249
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriod

theorem half_comb_not_mem (w₁ w₂ : ℂ) (hind : LinearIndependent ℝ ![w₁, w₂]) (a b : ℤ)
    (hab : ¬ (2 ∣ a ∧ 2 ∣ b)) :
    ((a : ℂ) * w₁ + (b : ℂ) * w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  intro h
  rw [AddSubgroup.mem_closure_pair] at h
  obtain ⟨m, n, hmn⟩ := h
  rw [LinearIndependent.pair_iff] at hind
  have key : ((a - 2 * m : ℤ) : ℝ) • w₁ + ((b - 2 * n : ℤ) : ℝ) • w₂ = 0 := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination (-2 : ℂ) * hmn
  obtain ⟨h1, h2⟩ := hind _ _ key
  have h1' : a - 2 * m = 0 := by exact_mod_cast h1
  have h2' : b - 2 * n = 0 := by exact_mod_cast h2
  exact hab ⟨⟨m, by omega⟩, ⟨n, by omega⟩⟩

theorem exists_other_half_period : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ,
    2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  rintro Λ ⟨w₁, w₂, hind, rfl⟩ P _ _
  have hw₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have hw₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have n₁ : w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 0 (by decide)
    simpa using this
  have n₂ : w₂ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 0 1 (by decide)
    simpa using this
  have n₃ : (w₁ - w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 (-1) (by decide)
    convert this using 2
    push_cast; ring
  by_cases hP : P - w₁ / 2 ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)
  · refine ⟨w₂ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₂, n₂, ?_⟩
    intro h
    apply n₃
    have := AddSubgroup.sub_mem _ h hP
    convert this using 1
    ring
  · exact ⟨w₁ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₁, n₁, hP⟩

end GlobalTheory.HalfPeriod
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

variable {Λ : AddSubgroup ℂ}

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma sgStar_add_lattice_eq_mul_exp (hΛ : _root_.GlobalTheory.EvenTheta.IsLat Λ) {a : ℂ} (ha : a ∈ Λ)
    (z : ℂ) :
    _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ (z + a) = (if a / 2 ∈ Λ then 1 else -1) * _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ z *
      Complex.exp (↑Real.pi * z * (starRingEnd ℂ) a / ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ) +
        ↑Real.pi * a * (starRingEnd ℂ) a / (2 * ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ))) := by
  have h := hΛ.sg_law ha z
  unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h
  rw [← h, mul_assoc, ← Complex.exp_add]
  ring_nf <;> simp

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_exp_eq_one_of_exp_relation {ε s x y w k : ℂ} (hs : s ≠ 0)
    (h : -1 * s * Complex.exp x = ε * (-1 * s * Complex.exp y) * Complex.exp w)
    (hk : y + w = x + k) : ε * Complex.exp k = 1 := by
  have h' : -1 * s * Complex.exp x = ε * (-1 * s * (Complex.exp x * Complex.exp k)) := by
    rw [← Complex.exp_add, ← hk, Complex.exp_add]
    linear_combination h
  have hprod : (s * Complex.exp x) * (ε * Complex.exp k - 1) = 0 := by
    linear_combination h'
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 (mul_ne_zero hs (Complex.exp_ne_zero x))
  · exact sub_eq_zero.1 h0

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_mul_exp_eq_of_mul_exp_eq_one {ε k a s q : ℂ} (h : ε * Complex.exp k = 1) (hs : s = k + q) :
    ε * (a * Complex.exp s) = a * Complex.exp q := by
  rw [hs, Complex.exp_add]
  linear_combination (a * Complex.exp q) * h


open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
theorem _root_.GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties : ∀ Λ : AddSubgroup ℂ, _root_.GlobalTheory.EvenTheta.IsLat Λ →
    ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) ∧ _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ 0 = 1 ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ (-z) = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z ^ 2 = _root_.GlobalTheory.EvenTheta.sqTh Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧
    ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ ω (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) z = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z := by
  intro Λ hΛ t ht h2t
  have hσt : _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ t ≠ 0 := fun h => ht ((hΛ.sg_eq_zero t).1 h)
  have hhalf : ¬ (2 * t / 2 ∈ Λ) := by rwa [mul_div_cancel_left₀ t two_ne_zero]
  have hU0 : _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) 0 ≠ 0 := by
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [zero_add]
    exact mul_ne_zero hσt (Complex.exp_ne_zero _)
  have hopp : ∀ y, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ (-t) (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y = -_root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y := by
    intro y
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [show y + t = y + -t + 2 * t by ring, sgStar_add_lattice_eq_mul_exp hΛ h2t, if_neg hhalf]
    simp only [mul_assoc, ← Complex.exp_add, map_neg, map_mul, map_ofNat]
    ring_nf
  have heven : ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) (-z) = _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) z := by
    intro z
    have h := hopp z
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h ⊢
    rw [show -z + t = -(z + -t) by ring, hΛ.sg_neg]
    simp only [map_neg] at h ⊢
    ring_nf at h ⊢
    linear_combination -h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd := hΛ.differentiable
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    fun_prop
  · unfold _root_.Formalism.MainNotions.GL3Theta.th0
    exact div_self hU0
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [heven]
  · intro z
    have h := hΛ.sqTh_mul ht z
    rw [hopp, hopp] at h
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hU0)]
    linear_combination h
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_eq_zero_iff, or_iff_left hU0]
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), hΛ.sg_eq_zero]
  · intro ω hω hωt z
    have hsum : ¬ ((ω + 2 * t) / 2 ∈ Λ) := by
      rwa [show (ω + 2 * t) / 2 = ω / 2 + t by ring]
    have h1 := sgStar_add_lattice_eq_mul_exp hΛ (add_mem hω h2t) t
    have h2 := sgStar_add_lattice_eq_mul_exp hΛ hω (t + 2 * t)
    have h3 := sgStar_add_lattice_eq_mul_exp hΛ h2t t
    rw [if_neg hsum] at h1
    rw [if_neg hhalf] at h3
    rw [show t + 2 * t + ω = t + (ω + 2 * t) by ring, h1, h3] at h2
    have hε := mul_exp_eq_one_of_exp_relation
      (k := (↑Real.pi * t * (starRingEnd ℂ) ω - ↑Real.pi * ω * (starRingEnd ℂ) t) /
        ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ)) hσt h2 (by simp only [map_add (f := _), map_mul, map_ofNat]; ring)
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    beta_reduce
    rw [show z + ω + t = z + t + ω by ring, sgStar_add_lattice_eq_mul_exp hΛ hω, div_mul_eq_mul_div]
    congr 1
    simp only [mul_assoc, ← Complex.exp_add]
    exact mul_mul_exp_eq_of_mul_exp_eq_one hε (by ring)

end GlobalTheory.EvenTheta
end

section

open scoped BigOperators

noncomputable section
namespace GlobalTheory.RootInt

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (hg : GlobalTheory.EvenTheta.IntSer g) :
    GlobalTheory.EvenTheta.IntSer (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem intSer_pow {f : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (N : ℕ) :
    GlobalTheory.EvenTheta.IntSer (f ^ N) := by
  induction N with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_of_pow {N : ℕ} (hN : ‖(N : K)‖ = 1) {s : PowerSeries K}
    (hs0 : PowerSeries.constantCoeff s = 1) (hsN : GlobalTheory.EvenTheta.IntSer (s ^ N)) :
    GlobalTheory.EvenTheta.IntSer s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, norm_one]
  set a : PowerSeries K := PowerSeries.mk fun k => if k < n then PowerSeries.coeff k s else 0 with ha
  have hca : ∀ k, PowerSeries.coeff k a = if k < n then PowerSeries.coeff k s else 0 := fun k => by
    rw [ha, PowerSeries.coeff_mk]
  have hai : GlobalTheory.EvenTheta.IntSer a := fun k => by
    rw [hca]; split_ifs with h
    · exact ih k h
    · simp
  have hcb : ∀ k, PowerSeries.coeff k (s - a) = if k < n then 0 else PowerSeries.coeff k s := fun k => by
    rw [map_sub, hca]; split_ifs <;> simp
  set G : PowerSeries K := ∑ i ∈ Finset.range N, s ^ i * a ^ (N - 1 - i) with hG
  have hGN : G * (s - a) = s ^ N - a ^ N := geom_sum₂_mul s a N
  have ha0 : PowerSeries.constantCoeff a = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hca, if_pos hn,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0]
  have hG0 : PowerSeries.coeff 0 G = N := by

    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, map_sum]
    simp [hs0, ha0]
  have key : PowerSeries.coeff n (G * (s - a)) = (N : K) * PowerSeries.coeff n s := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hG0, hcb, if_neg (lt_irrefl n)]
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hj : j < n := by
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact absurd (by simp at hij; simp [hij]) hne
        · omega
      simp only
      rw [hcb, if_pos hj, mul_zero]
    · intro h; exact absurd (by simp) h
  have h1 : ‖(N : K) * PowerSeries.coeff n s‖ ≤ 1 := by
    rw [← key, hGN, map_sub]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsN n) ?_)
    rw [norm_neg]; exact intSer_pow hai N n
  rwa [norm_mul, hN, one_mul] at h1

end GlobalTheory.RootInt

theorem GlobalTheory.RootInt.intSer_root : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  intro p _ N _ hcop s hs0 hsN
  refine GlobalTheory.RootInt.intSer_of_pow ?_ hs0 hsN
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact hcop.symm
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.FunEq

open PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : K⟦X⟧} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

omit [IsUltrametricDist K] in
theorem intSer_C {c : K} (hc : ‖c‖ ≤ 1) : IntSer (C c : K⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

theorem intSer_pow {f : K⟦X⟧} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_C (K := K) (c := 1) (by simp)
  | succ n ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_aeval {h : K⟦X⟧} (hh : IntSer h) (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    IntSer (Polynomial.aeval h P) := by
  intro n

  rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)

theorem intSer_of_funEq (f h A B : K⟦X⟧) (N : ℕ) (hf : constantCoeff f = 1) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : ‖coeff 1 h‖ = 1) (hN : ‖(N : K)‖ < 1) (hA : IntSer A)
    (hA0 : constantCoeff A = 1) (hB : IntSer B) (hB0 : constantCoeff B = 1)
    (e : (PowerSeries.subst h f : K⟦X⟧) * A = f ^ N * B) : IntSer f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set P : Polynomial K := trunc n f with hP
  have hPi : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    intro i
    rw [hP, coeff_trunc]
    split_ifs with hi
    · exact ih i hi
    · simp
  have hPs : IntSer (P : K⟦X⟧) := fun i => by rw [Polynomial.coeff_coe]; exact hPi i
  have hP0 : constantCoeff (P : K⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn,
      coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨Q, hQ⟩ : (X : K⟦X⟧) ^ n ∣ f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]
  have hX : ∀ g : K⟦X⟧, coeff n (X ^ n * g) = constantCoeff g := fun g => by
    simpa using coeff_X_pow_mul g n 0
  have hQ0 : constantCoeff Q = coeff n f := by
    rw [← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]
  obtain ⟨h', hh'⟩ : (X : K⟦X⟧) ∣ h := X_dvd_iff.2 hh0
  have h'0 : constantCoeff h' = coeff 1 h := by
    rw [hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hfe : f = (P : K⟦X⟧) + X ^ n * Q := by rw [← hQ]; ring
  have hsQ : constantCoeff (PowerSeries.subst h Q : K⟦X⟧) = constantCoeff Q := by
    obtain ⟨Q', hQ'⟩ : (X : K⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
    have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
    conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
    have hC : (PowerSeries.subst h (C (constantCoeff Q) : K⟦X⟧) : K⟦X⟧) = C (constantCoeff Q) := by
      rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp
    rw [hC]
    simp [hh0]
  have hL : (PowerSeries.subst h f : K⟦X⟧) * A =
      Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A) := by
    conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]
    have : h ^ n = X ^ n * h' ^ n := by rw [hh', mul_pow]
    rw [this]; ring
  have hR : f ^ N * B = (P : K⟦X⟧) ^ N * B +
      X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : K⟦X⟧) ^ (N - 1 - i)) * B) := by
    have := geom_sum₂_mul f (P : K⟦X⟧) N
    rw [hQ] at this
    linear_combination (-B) * this
  have key := congrArg (coeff n) e
  rw [hL, hR, map_add (f := _), map_add (f := _), hX, hX] at key

  simp only [map_mul, map_pow, map_sum, hA0, hB0, hf, hP0, hsQ, hQ0, h'0, one_pow, mul_one,
  Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  have h1 := intSer_mul (intSer_aeval hh P hPi) hA n
  have h2 := intSer_mul (intSer_pow hPs N) hB n
  have k2 : (coeff 1 h ^ n - N) * coeff n f =
      coeff n ((P : K⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A) := by
    linear_combination key
  have hu : ‖coeff 1 h ^ n - (N : K)‖ = 1 := by
    have hp : ‖coeff 1 h ^ n‖ = 1 := by rw [norm_pow, hh1, one_pow]
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]
  have := congrArg norm k2
  rw [norm_mul, hu, one_mul] at this
  rw [this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))

theorem intSer_of_funEq_padic : ∀ (p : ℕ) [Fact p.Prime] (f h A B : PowerSeries ℂ_[p]) (N : ℕ), PowerSeries.constantCoeff f = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖(N : ℂ_[p])‖ < 1 → IntSer A → PowerSeries.constantCoeff A = 1 → IntSer B → PowerSeries.constantCoeff B = 1 → (PowerSeries.subst h f : PowerSeries ℂ_[p]) * A = f ^ N * B → IntSer f :=
  fun _ _ f h A B N => intSer_of_funEq f h A B N

end GlobalTheory.EvenTheta.FunEq
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

def colA (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := sgStar Λ z ^ 3

def colB (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)

def colC (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z

def tay (F : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 F)

def defect {R : Type*} [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) :
    MvPowerSeries (Fin 3) R :=
  Matrix.det (Matrix.of fun i j =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) : MvPowerSeries (Fin 3) R)) -
    2 * PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 1 - MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 2 - MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) s

end GlobalTheory.FrobStick
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_traceOne_integer_conj_diff_prime_to : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  first | exact @GlobalTheory.TraceOne.exists_trace_one | exact GlobalTheory.TraceOne.exists_trace_one | (intros; apply GlobalTheory.TraceOne.exists_trace_one <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTranslate_combination_coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A → ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'), (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  first | exact @GlobalTheory.ThetaTranslateCoef.coef_eq_zero | exact GlobalTheory.ThetaTranslateCoef.coef_eq_zero | (intros; apply GlobalTheory.ThetaTranslateCoef.coef_eq_zero <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.unitaryTransvection_moves_lattice_at_prime : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  first | exact @GlobalTheory.UnitaryTransvection.transvection | exact GlobalTheory.UnitaryTransvection.transvection | (intros; apply GlobalTheory.UnitaryTransvection.transvection <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.self_dual_lattices_neighbour_chain : ∀ (D : D7) (n : ℕ) (L₀ L : Lat D n), SD D L₀ → SD D L → L₀ ≠ L → ∃ (P : Ideal (𝓞 D.host.E)) (q : ℕ) (x : Fin n → D.host.E), P.IsMaximal ∧ q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ x ∈ L₀ ∧ NbD D P L x ∧ lenQ D L₀ (nbr D L x) + 1 = lenQ D L₀ L := by
  first | exact @GlobalTheory.NearerNeighbour.exists_nearer | exact GlobalTheory.NearerNeighbour.exists_nearer | (intros; apply GlobalTheory.NearerNeighbour.exists_nearer <;> assumption)
end
