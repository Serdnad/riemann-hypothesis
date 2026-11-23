module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.ChevalleyWarning
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Algebra.CharP.Defs
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

section

namespace GlobalTheory.RationalValueRealScalar

theorem map_rat_smul_real {U : Type} [AddCommGroup U] [Module ℝ U] {V : Type} [AddCommGroup V]
    [Module ℚ V] (p : V →+ U) (c : ℚ) (x : V) : p (c • x) = (c : ℝ) • p x := by
  have h1 : (c.den : ℤ) • (c • x) = c.num • x := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_natCast, mul_comm, Rat.mul_den_eq_num]
  have h2 : (c.den : ℝ) • p (c • x) = (c.num : ℝ) • p x := by
    rw [← Int.cast_natCast, Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul, ← map_zsmul, h1]
  have hd : (c.den : ℝ) ≠ 0 := by positivity
  calc p (c • x) = ((c.den : ℝ)⁻¹ * c.den) • p (c • x) := by rw [inv_mul_cancel₀ hd, one_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.den : ℝ) • p (c • x)) := by rw [smul_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.num : ℝ) • p x) := by rw [h2]
    _ = (c : ℝ) • p x := by rw [smul_smul, Rat.cast_def, inv_mul_eq_div]

theorem exists_rat_value {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, (q : ℝ) = -(om (p u) (p v)) := by
  obtain ⟨N, hN, hNu⟩ := hL u
  obtain ⟨M, hM, hMv⟩ := hL v
  obtain ⟨k, hk⟩ := hint _ hNu _ hMv
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hk
  refine ⟨-(k / (N * M) : ℚ), ?_⟩
  have hNM : (N : ℝ) * M ≠ 0 := by positivity
  push_cast
  rw [neg_inj, div_eq_iff hNM, ← hk]
  ring

theorem exists_rat_bilinForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v : V, ((B u v : ℚ) : ℝ) = -(om (p u) (p v)) := by
  choose q hq using exists_rat_value om p L hL hint
  refine ⟨LinearMap.mk₂ ℚ q ?_ ?_ ?_ ?_, fun u v => hq u v⟩
  · intro u1 u2 v
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add (f := _), LinearMap.map_add (f := _), LinearMap.add_apply]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro u v1 v2
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add (f := _), LinearMap.map_add (f := _)]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, smul_eq_mul]
    ring

end GlobalTheory.RationalValueRealScalar
end

section

universe u_1

namespace GlobalTheory.BinaryFormUniversal

open Polynomial

theorem binary_form_universal {k : Type u_1} [Field k] [Finite k] {a n : k}
    (hD : a ^ (2 : ℕ) - (4 : k) * n ≠ (0 : k)) (u : k) :
    ∃ (r : k) (s : k), r ^ (2 : ℕ) + a * r * s + n * s ^ (2 : ℕ) = u := by
  classical
  by_cases h2 : ringChar k = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 u
    exact ⟨r, 0, by rw [hr]; ring⟩
  · letI := Fintype.ofFinite k
    have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have h2' : (2 : k) ≠ 0 := Ring.two_ne_zero h2
    have hD' : -(a ^ 2 - 4 * n) ≠ 0 := neg_ne_zero.mpr hD
    have hf : degree (X ^ 2 : k[X]) = 2 := by simp
    have hg : degree (C (-(a ^ 2 - 4 * n)) * X ^ 2 + C 0 * X + C (-(4 * u)) : k[X]) = 2 :=
      degree_quadratic hD'
    obtain ⟨x, s, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
    refine ⟨(x - a * s) / 2, s, ?_⟩
    field_simp
    linear_combination h

end GlobalTheory.BinaryFormUniversal
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_radius_lattice_translate_norm_le (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] : ∃ R : ℝ, 0 < R ∧ ∀ y : V, ∃ l : L, ‖y + l‖ ≤ R := by
  classical
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  refine ⟨∑ i, ‖b i‖ + 1, by positivity, fun y => ?_⟩
  have hmem : (ZSpan.floor b y : V) ∈ L :=
    ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ).le (ZSpan.floor b y).2
  refine ⟨-⟨_, hmem⟩, ?_⟩
  have h := ZSpan.norm_fract_le b y
  rw [ZSpan.fract_apply] at h
  have e : y + ((-⟨_, hmem⟩ : L) : V) = y - (ZSpan.floor b y : V) := by
    rw [Submodule.coe_neg, sub_eq_add_neg]
  rw [e]
  linarith

theorem exists_smooth_compactSupport_hasSum_lattice_translates :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L], ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ ∀ y, HasSum (fun l : L => η (y + l)) 1 := by
  intro V _ _ _ L _ _
  classical
  obtain ⟨R, hR, hcov⟩ := exists_radius_lattice_translate_norm_le V L
  let φ : ContDiffBump (0 : V) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  have hrIn : φ.rIn = R + 1 := rfl
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L :=
    (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
  have hfin : ∀ (x : V) (r : ℝ), {l : L | ‖x + (l : V)‖ < r}.Finite := by
    intro x r
    have hs := ZSpan.setFinite_inter b (Metric.isBounded_ball (x := -x) (r := r))
    rw [hspan] at hs
    refine (hs.preimage Subtype.val_injective.injOn).subset ?_
    intro l hl
    refine ⟨?_, l.2⟩
    show dist (l : V) (-x) < r
    rw [dist_eq_norm, sub_neg_eq_add, add_comm]
    exact hl
  let S : V → ℝ := fun y => ∑' l : L, φ (y + l)
  have hsupp : ∀ y, (Function.support fun l : L => φ (y + l)).Finite := by
    intro y
    refine (hfin y φ.rOut).subset fun l hl => ?_
    have h : y + (l : V) ∈ Metric.ball (0 : V) φ.rOut := by
      rw [← φ.support_eq]
      exact hl
    simpa [mem_ball_zero_iff] using h
  have hsum : ∀ y, HasSum (fun l : L => φ (y + l)) (S y) :=
    fun y => (summable_of_hasFiniteSupport (hsupp y)).hasSum
  have hper : ∀ y (l₀ : L), S (y + l₀) = S y := by
    intro y l₀
    calc S (y + l₀) = ∑' c : L, φ (y + ((l₀ + c : L) : V)) := by
          simp only [S, Submodule.coe_add, add_assoc]
      _ = S y := (Equiv.addLeft l₀).tsum_eq (fun l : L => φ (y + l))
  have hpos : ∀ y, 0 < S y := by
    intro y
    obtain ⟨l, hl⟩ := hcov y
    have h1 : φ (y + l) = 1 :=
      φ.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, hrIn]; linarith)
    have h2 := le_hasSum (hsum y) l (fun _ _ => φ.nonneg)
    linarith
  have hS : ContDiff ℝ ∞ S := by
    rw [contDiff_iff_contDiffAt]
    intro x
    let F := (hfin x (φ.rOut + 1)).toFinset
    have heq : S =ᶠ[nhds x] fun y => ∑ l ∈ F, φ (y + l) := by
      filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
      refine (hsum y).unique (hasSum_sum_of_ne_finset_zero ?_)
      intro l hl
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at hl
      apply φ.zero_of_le_dist
      rw [dist_zero_right]
      have h2 : ‖x + (l : V)‖ ≤ ‖y + (l : V)‖ + ‖x - y‖ := by
        calc ‖x + (l : V)‖ = ‖(y + (l : V)) + (x - y)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖x - y‖ < 1 := by
        rw [← dist_eq_norm, dist_comm]
        exact hy
      linarith
    exact (ContDiff.contDiffAt (ContDiff.sum fun l _ =>
      φ.contDiff.comp (contDiff_id.add contDiff_const))).congr_of_eventuallyEq heq
  refine ⟨fun y => φ y / S y, φ.contDiff.div hS fun y => (hpos y).ne', ?_, ?_⟩
  · refine φ.hasCompactSupport.mono fun y hy => ?_
    simp only [Function.mem_support] at hy ⊢
    intro h
    apply hy
    simp [h]
  · intro y
    show HasSum (fun l : L => φ (y + l) / S (y + l)) 1
    simp_rw [hper y]
    rw [← div_self (hpos y).ne']
    exact (hsum y).div_const _

end GlobalTheory
end

section

universe u_1

namespace GlobalTheory.NonzeroIsotropic

open MvPolynomial

theorem quadForm_totalDegree_le {k : Type u_1} [Field k] (a : Fin 3 → Fin 3 → k) :
    (∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  calc (C (a i j) * X i * X j : MvPolynomial (Fin 3) k).totalDegree
      ≤ (C (a i j) * X i : MvPolynomial (Fin 3) k).totalDegree + (X j : MvPolynomial (Fin 3) k).totalDegree :=
        totalDegree_mul _ _
    _ ≤ ((C (a i j) : MvPolynomial (Fin 3) k).totalDegree + (X i : MvPolynomial (Fin 3) k).totalDegree)
          + (X j : MvPolynomial (Fin 3) k).totalDegree := by gcongr; exact totalDegree_mul _ _
    _ = 2 := by simp [totalDegree_C, totalDegree_X]

theorem exists_nonzero_isotropic :
    ∀ {k : Type u_1} [inst : Field k] [Finite k] (a : Fin (3 : ℕ) → Fin (3 : ℕ) → k),
      ∃ (x : Fin (3 : ℕ) → k), x ≠ (0 : Fin (3 : ℕ) → k) ∧
        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), a i j * x i * x j = (0 : k) := by
  intro k _ _ a
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero k p with h | h
    · exact h
    · subst h
      haveI : CharZero k := CharP.charP_to_charZero k
      exact absurd (Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective) (by
        intro h; exact not_finite ℕ)
  set f : MvPolynomial (Fin 3) k := ∑ i : Fin 3, ∑ j : Fin 3, C (a i j) * X i * X j with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := quadForm_totalDegree_le a
    simp only [Fintype.card_fin]; omega
  have hdvd := char_dvd_card_solutions p hdeg
  have heval : ∀ x : Fin 3 → k, eval x f = ∑ i : Fin 3, ∑ j : Fin 3, a i j * x i * x j := by
    intro x; simp [hf]
  let z : { x : Fin 3 → k // eval x f = 0 } := ⟨0, by rw [heval]; simp⟩
  have hcard : 1 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := by
    have hpos : 0 < Fintype.card { x : Fin 3 → k // eval x f = 0 } := Fintype.card_pos_iff.mpr ⟨z⟩
    have := Nat.le_of_dvd hpos hdvd
    have := hpp.two_le
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard z
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_⟩
  rw [← heval]; exact y.2

end GlobalTheory.NonzeroIsotropic
end

section

open scoped ContDiff

namespace GlobalTheory

theorem charSeries_kill_finset {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (h0 : ∀ a, e i₀ a = 1) (hneg : ∀ i, i ≠ i₀ → ∃ a, e i a = -1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) (s : Finset I) :
    ∃ c' : I → ℂ, c' i₀ = c i₀ ∧ (∀ i ∈ s, i ≠ i₀ → c' i = 0) ∧ (∀ i, ‖c' i‖ ≤ ‖c i‖) ∧
      ∀ a, ∑' i, c' i * e i a = 0 := by
  classical
  refine Finset.induction_on s ⟨c, rfl, by simp, fun i => le_rfl, hF⟩ ?_
  intro j s _ ih
  obtain ⟨c', h1, h2, h3, h4⟩ := ih
  by_cases hji : j = i₀
  · subst hji
    refine ⟨c', h1, ?_, h3, h4⟩
    intro i hi hne
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact absurd rfl hne
    · exact h2 i hi hne
  · obtain ⟨b, hb⟩ := hneg j hji
    refine ⟨fun i => c' i * (1 + e i b) / 2, ?_, ?_, ?_, ?_⟩
    · show c' i₀ * (1 + e i₀ b) / 2 = c i₀
      rw [h0 b, h1]; ring
    · intro i hi hne
      show c' i * (1 + e i b) / 2 = 0
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hb]; ring
      · rw [h2 i hi hne]; ring
    · intro i
      show ‖c' i * (1 + e i b) / 2‖ ≤ ‖c i‖
      have h2b : ‖(1 : ℂ) + e i b‖ ≤ 2 :=
        (norm_add_le _ _).trans (by rw [norm_one]; linarith [hle i b])
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      calc ‖c' i‖ * ‖1 + e i b‖ / 2 ≤ ‖c' i‖ * 2 / 2 := by gcongr
        _ = ‖c' i‖ := by ring
        _ ≤ ‖c i‖ := h3 i
    · intro a
      show ∑' i, c' i * (1 + e i b) / 2 * e i a = 0
      have hsum : ∀ x, Summable (fun i => c' i * e i x) := fun x =>
        Summable.of_norm_bounded hs (fun i => by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (hle i x)).trans (h3 i))
      have key : ∀ i, c' i * (1 + e i b) / 2 * e i a = (c' i * e i a + c' i * e i (b + a)) / 2 := by
        intro i; rw [hmul i b a]; ring
      simp only [key]
      rw [tsum_div_const, (hsum a).tsum_add (hsum (b + a)), h4 a, h4 (b + a)]
      simp

theorem charSeries_exists_ne_zero : ∀ (A I : Type) [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I), (∀ i a b, e i (a + b) = e i a * e i b) → (∀ i a, ‖e i a‖ ≤ 1) → (∀ a, e i₀ a = 1) → (∀ i, i ≠ i₀ → ∃ a, e i a = -1) → Summable (fun i => ‖c i‖) → c i₀ ≠ 0 → ∃ a, ∑' i, c i * e i a ≠ 0 := by
  intro A I _ e c i₀ hmul hle h0 hneg hs hc
  by_contra hcon
  push Not at hcon
  have he0 : ∀ i, e i 0 = 1 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; exact h0 0
    · obtain ⟨a, ha⟩ := hneg i hi
      have h := hmul i a 0
      rw [add_zero, ha] at h
      linear_combination h
  have hpos : 0 < ‖c i₀‖ := norm_pos_iff.2 hc
  obtain ⟨s, hs1, hs2⟩ := (((tendsto_order.1
    (tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖))).2 _ hpos).and
    (Filter.eventually_ge_atTop {i₀})).exists
  have htail : ∑' x : {x // x ∉ s}, ‖c x‖ < ‖c i₀‖ := hs1
  have hi0 : i₀ ∈ s := hs2 (Finset.mem_singleton_self i₀)
  obtain ⟨c', hc'0, hc's, hc'le, hc'F⟩ :=
    charSeries_kill_finset e c i₀ hmul hle h0 hneg hs hcon s
  have hsum' : Summable c' := Summable.of_norm_bounded hs hc'le
  have key := hc'F 0
  simp only [he0, mul_one] at key
  rw [← hsum'.sum_add_tsum_subtype_compl s] at key
  have hfin : ∑ x ∈ s, c' x = c i₀ := by
    rw [Finset.sum_eq_single i₀ (fun b hb hne => hc's b hb hne) (fun h => absurd hi0 h)]
    exact hc'0
  rw [hfin] at key
  have hbound : ‖∑' x : {x // x ∉ s}, c' x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖ :=
    tsum_of_norm_bounded ((hs.subtype _).hasSum) (fun x => hc'le x)
  have hnorm : ‖c i₀‖ = ‖∑' x : {x // x ∉ s}, c' x‖ := by
    rw [eq_neg_of_add_eq_zero_left key, norm_neg]
  linarith

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem real_pos_at_one_of_right (L : ℂ → ℂ) (hc : ContinuousAt L 1) (h1 : L 1 ≠ 0)
    (h : ∀ s : ℂ, 1 < s.re → s.im = 0 → (L s).im = 0 ∧ 0 < (L s).re) :
    (L 1).im = 0 ∧ 0 < (L 1).re := by
  have ht : Tendsto (fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (L 1)) := by
    have h0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using Complex.continuous_ofReal.tendsto 1
    exact (hc.tendsto.comp h0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), (L (t : ℂ)).im = 0 ∧ 0 < (L (t : ℂ)).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h t (by simpa using ht) (by simp)
  have him : (L 1).im = 0 := by
    have h2 := (Complex.continuous_im.tendsto _).comp ht
    have h3 : Tendsto (Complex.im ∘ fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => ht.1.symm)
    exact tendsto_nhds_unique h2 h3
  have hre : 0 ≤ (L 1).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp ht) (hev.mono fun t ht => ht.2.le)
  refine ⟨him, lt_of_le_of_ne hre fun h0 => h1 ?_⟩
  exact Complex.ext h0.symm him

end GlobalTheory
end

section

namespace GlobalTheory.ContinuousHomDifferentiable

open intervalIntegral

theorem exists_integral_ne_zero (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) :
    ∃ δ : ℝ, (∫ x in (0:ℝ)..δ, χ x) ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, χ x) (χ 0) 0 :=
    (hc.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hfun : (fun u => ∫ x in (0:ℝ)..u, χ x) = fun _ => (0:ℂ) := funext h
  rw [hfun] at h1
  have h2 : HasDerivAt (fun _ : ℝ => (0:ℂ)) 0 0 := hasDerivAt_const _ _
  have := h1.unique h2
  rw [h0] at this
  exact one_ne_zero this

theorem continuous_hom_differentiable :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ (0 : ℝ) = (1 : ℂ) →
      (∀ (s t : ℝ), χ (s + t) = χ s * χ t) → Differentiable ℝ χ := by
  intro χ hc h0 hmul
  obtain ⟨δ, hδ⟩ := exists_integral_ne_zero χ hc h0
  set c : ℂ := ∫ x in (0:ℝ)..δ, χ x with hcdef
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, χ x with hF
  have hFd : Differentiable ℝ F := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have key : ∀ s, χ s = c⁻¹ * (F (s + δ) - F s) := by
    intro s
    have e1 : χ s * c = ∫ x in (0:ℝ)..δ, χ (s + x) := by
      rw [hcdef, ← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      rw [hmul]
    have e2 : (∫ x in (0:ℝ)..δ, χ (s + x)) = ∫ x in s..s + δ, χ x := by
      rw [intervalIntegral.integral_comp_add_left (fun x => χ x) s]
      simp
    have e3 : F (s + δ) - F s = ∫ x in s..s + δ, χ x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    rw [e3, ← e2, ← e1]
    field_simp
  have hfun : χ = fun s => c⁻¹ * (F (s + δ) - F s) := funext key
  rw [hfun]
  fun_prop

end GlobalTheory.ContinuousHomDifferentiable
end
