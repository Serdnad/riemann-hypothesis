module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConjAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.MeanValue
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma wtPos_expand (n : ℕ) (l : Fin n → ℤ) :
    ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      2 * (∑ i : Fin n, ((i : ℕ) : ℤ)) * (∑ i, l i) - 2 * n * ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  have h : ∀ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
      ((i : ℕ) : ℤ) * (∑ j, l j) - n * (l i * ((i : ℕ) : ℤ)) - (∑ j : Fin n, l j * ((j : ℕ) : ℤ))
        + (∑ j : Fin n, ((j : ℕ) : ℤ)) * l i := by
    intro i
    have e : ∀ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) =
        ((i : ℕ) : ℤ) * l j - l i * ((i : ℕ) : ℤ) - l j * ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) * l i := by
      intro j; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma wtPos_term {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) (i j : Fin n) :
    0 ≤ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  rcases le_total i j with h | h
  · have h1 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 := hl h
    exact mul_nonneg (by linarith) (by linarith)

private lemma wtPos_term_pos {n : ℕ} {l : Fin n → ℤ} (hl : Antitone l) {i j : Fin n} (hij : l i ≠ l j) :
    0 < (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
  have hne : i ≠ j := fun h => hij (by rw [h])
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l j < l i := lt_of_le_of_ne (hl h.le) (Ne.symm hij)
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h1 : ((j : ℕ) : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : l i < l j := lt_of_le_of_ne (hl h.le) hij
    exact mul_pos (by linarith) (by linarith)

private lemma wtPos_sum (n : ℕ) (l : Fin n → ℤ) (c : ℤ) :
    ∑ i, l i * (c - ((i : ℕ) : ℤ)) = c * (∑ i, l i) - ∑ i : Fin n, l i * ((i : ℕ) : ℤ) := by
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]

theorem UpperTheory.Gal.Gen.wtPos_pf :
    UpperTheory.Gal.Gen.WtPos := by
  intro n l hl hl0
  set S : ℤ := ∑ i, l i with hS
  set T : ℤ := ∑ i : Fin n, l i * ((i : ℕ) : ℤ) with hT
  rcases lt_trichotomy S 0 with h | h | h
  · refine ⟨-(|T| + 1), ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
  ·
    obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hl0 (funext hc)
    obtain ⟨b, hb⟩ : ∃ b, l a ≠ l b := by
      by_contra hc
      push_neg at hc
      have hs : S = n * l a := by
        rw [hS, Finset.sum_congr rfl (fun i _ => (hc i).symm)]
        simp
      rw [h] at hs
      have hn : (n : ℤ) ≠ 0 := by
        have : 0 < n := Fin.pos a
        exact_mod_cast this.ne'
      exact ha ((mul_eq_zero.mp hs.symm).resolve_left hn)
    have hpos : 0 < ∑ i : Fin n, ∑ j : Fin n, (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * (l j - l i) := by
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => wtPos_term hl i j) ⟨a, Finset.mem_univ a, ?_⟩
      exact Finset.sum_pos' (fun j _ => wtPos_term hl a j) ⟨b, Finset.mem_univ b, wtPos_term_pos hl hb⟩
    rw [wtPos_expand, ← hS, ← hT, h] at hpos
    have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have hT0 : T < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg hn hc]
    refine ⟨0, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    linarith
  · refine ⟨|T| + 1, ?_⟩
    rw [wtPos_sum, ← hS, ← hT]
    have h1 : T ≤ |T| := le_abs_self T
    have h2 : 0 ≤ |T| := abs_nonneg T
    nlinarith
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.small_pf :
    UpperTheory.Gal.Gen.SymEx → UpperTheory.Gal.Gen.StarEx → UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.Small := by
  intro hSym hStar hNull hDens n Φ hΦ δ hδ
  obtain ⟨P, hPmem, hPprod, hPpoly⟩ := hSym n Φ
  obtain ⟨Ψ, hΨ, hPΨ⟩ := hPpoly hΦ
  obtain ⟨Q, hQmem, hQ⟩ := hStar n P hPmem
  obtain ⟨-, -, hcont, hnorm⟩ := hDens n 0 le_rfl one_pos
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Fin n → UnitAddCircle))).exists_bound_of_continuousOn
    (hcont P).continuousOn
  set c : ℝ := 1 / (M ^ 2 + 1) with hc
  have hc0 : 0 < c := by positivity
  let g : (Fin n → UnitAddCircle) → ℝ := fun θ => 1 - c * ‖evalAt (pt θ) P‖ ^ 2
  have hg0 : ∀ θ, 0 ≤ g θ := by
    intro θ
    have h1 : ‖evalAt (pt θ) P‖ ≤ M := hM θ (Set.mem_univ _)
    have h2 : ‖evalAt (pt θ) P‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : c * ‖evalAt (pt θ) P‖ ^ 2 ≤ 1 := by
      rw [hc, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    simp only [g]
    linarith
  have hg1 : ∀ θ, g θ ≤ 1 := by
    intro θ
    simp only [g]
    have : 0 ≤ c * ‖evalAt (pt θ) P‖ ^ 2 := by positivity
    linarith
  let pk : ℕ → LaurentRing n := fun k => (1 - (c : ℂ) • (P * Q)) ^ k
  have hpk_mem : ∀ k, pk k ∈ symmetricLaurent (n := n) := by
    intro k
    exact Subalgebra.pow_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hPmem hQmem) _)) k
  have hpk_eval : ∀ k θ, evalAt (pt θ) (pk k) = ((g θ : ℝ) : ℂ) ^ k := by
    intro k θ
    simp only [pk, g, map_pow, map_sub, map_one, map_smul, map_mul, smul_eq_mul]
    rw [hQ (pt θ) (hnorm θ), Complex.mul_conj']
    push_cast
    ring
  have hF : ∀ k θ, ‖evalAt (pt θ) (pk k)‖ ^ 2 = (g θ ^ k) ^ 2 := by
    intro k θ
    rw [hpk_eval, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 θ)]
  have hlim : Filter.Tendsto (fun k => ∫ θ, ‖evalAt (pt θ) (pk k)‖ ^ 2) Filter.atTop
      (nhds (∫ _θ : Fin n → UnitAddCircle, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_) (integrable_const _)
      (fun k => Filter.Eventually.of_forall (fun θ => ?_)) ?_
    · exact ((hcont (pk k)).norm.pow 2).aestronglyMeasurable
    · rw [hF, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (pow_nonneg (hg0 θ) _) (pow_le_one₀ (hg0 θ) (hg1 θ))
    · filter_upwards [hNull n Ψ hΨ] with θ hθ
      have hP0 : evalAt (pt θ) P ≠ 0 := by rw [hPΨ]; exact hθ
      have hlt : g θ < 1 := by
        simp only [g]
        have : 0 < c * ‖evalAt (pt θ) P‖ ^ 2 := by
          have := norm_pos_iff.mpr hP0
          positivity
        linarith
      simp only [hF]
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (hg0 θ) hlt).pow 2
      simpa using h
  rw [MeasureTheory.integral_zero] at hlim
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hlim).2 δ hδ).exists
  refine ⟨pk k, hpk_mem k, fun z hz => ?_, hk.le⟩
  have hP0 : evalAt z P = 0 := by
    rw [hPprod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simpa using hz)
  simp only [pk, map_pow, map_sub, map_one, map_smul, map_mul, hP0, zero_mul, smul_zero, sub_zero, one_pow]
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma circle_mean (g : ℂ → ℂ)
    (hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u) :
    ∫ s : UnitAddCircle, g ((AddCircle.toCircle s : Circle) : ℂ) = g 0 := by
  have hc : ContinuousOn g (Metric.closedBall (0 : ℂ) |1|) := by
    intro u hu
    exact (hd u (by simpa using hu)).continuousAt.continuousWithinAt
  have hmv : Real.circleAverage g 0 1 = g 0 :=
    circleAverage_of_differentiable_on_off_countable (s := ∅) Set.countable_empty hc
      (fun u hu => hd u (by
        have := hu.1
        simp only [abs_one, Metric.mem_ball] at this
        simpa using this.le))
  have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  have e : ∀ a : ℝ, ((AddCircle.toCircle (a : UnitAddCircle) : Circle) : ℂ)
      = circleMap 0 1 (2 * Real.pi * a) := by
    intro a
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp only [zero_add, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  rw [← UnitAddCircle.intervalIntegral_preimage 0, ← hmv, Real.circleAverage_def]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_left (fun θ => g (circleMap 0 1 θ)) hpi]
  simp

private lemma ratio_eq (u : ℂ) (hu : u ≠ 0) (c : ℤ) (i j : ℕ) (hij : i < j) (a b : ℂ) :
    (u ^ (c - (i : ℤ)) * a) / (u ^ (c - (j : ℤ)) * b) = u ^ (j - i) * (a / b) := by
  have h : u ^ (c - (i : ℤ)) / u ^ (c - (j : ℤ)) = u ^ (j - i) := by
    rw [← zpow_sub₀ hu, ← zpow_natCast, Nat.cast_sub hij.le]
    congr 1
    ring
  rw [mul_div_mul_comm, h]

theorem UpperTheory.Gal.Gen.meanVal_pf :
    UpperTheory.Gal.Gen.MeanVal := by
  intro n t ht0 ht1 z hz c m
  set g : ℂ → ℂ := fun u => u ^ m * ∏ p ∈ prs n,
    (1 - u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
      (1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) with hg
  have hden : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, ∀ p : Fin n × Fin n,
      1 - (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) ≠ 0 := by
    intro u hu p h0
    have hu1 : ‖u‖ ≤ 1 := by simpa using hu
    have hx : (t : ℂ) * (u ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) = 1 :=
      (sub_eq_zero.mp h0).symm
    have hn := congrArg norm hx
    rw [norm_mul, norm_mul, norm_div, hz, hz, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0,
      norm_one, div_one, mul_one] at hn
    have : ‖u‖ ^ ((p.2 : ℕ) - (p.1 : ℕ)) ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    nlinarith
  have hd : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, DifferentiableAt ℂ g u := by
    intro u hu
    refine (differentiableAt_id.pow m).mul ?_
    refine DifferentiableAt.fun_finsetProd fun p _ => ?_
    refine DifferentiableAt.div ?_ ?_ (hden u hu p)
    · exact (differentiableAt_const _).sub ((differentiableAt_id.pow _).mul (differentiableAt_const _))
    · exact (differentiableAt_const _).sub
        ((differentiableAt_const _).mul ((differentiableAt_id.pow _).mul (differentiableAt_const _)))
  have h0 : g 0 = if m = 0 then 1 else 0 := by
    have hp : ∏ p ∈ prs n, (1 - (0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ))) /
        (1 - (t : ℂ) * ((0 : ℂ) ^ ((p.2 : ℕ) - (p.1 : ℕ)) * ((z p.1 : ℂ) / (z p.2 : ℂ)))) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
      have hk : (p.2 : ℕ) - (p.1 : ℕ) ≠ 0 := by omega
      simp [zero_pow hk]
    simp only [hg, hp, mul_one]
    split_ifs with hm
    · simp [hm]
    · exact zero_pow hm
  have hs : ∀ s : UnitAddCircle, ((AddCircle.toCircle s : Circle) : ℂ) ^ m *
      half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - (i : ℕ)) * z i)
      = g ((AddCircle.toCircle s : Circle) : ℂ) := by
    intro s
    simp only [hg, half]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hlt : (p.1 : ℕ) < (p.2 : ℕ) := (Finset.mem_filter.mp hp).2
    have hu : ((AddCircle.toCircle s : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have key := ratio_eq _ hu c p.1 p.2 hlt (z p.1 : ℂ) (z p.2 : ℂ)
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Circle.toUnits_apply, Units.val_mk0]
    rw [key]
  simp_rw [hs]
  rw [circle_mean g hd, h0]
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma det_vand_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    (Matrix.vandermonde (v ∘ σ)).det =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

private lemma prod_prs {n : ℕ} (f : Fin n → Fin n → ℂ) :
    ∏ p ∈ prs n, f p.1 p.2 = ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j; simp

private lemma det_rev {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.vandermonde (v ∘ Fin.revPerm)).det = ∏ p ∈ prs n, (v p.1 - v p.2) := by
  rw [Matrix.det_vandermonde, ← prod_prs (fun i j => (v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i)]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p hp
    simpa [Fin.rev_lt_rev] using hp
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

private lemma sign_sq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private lemma prod_comp {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    ∏ p ∈ prs n, (v (σ p.1) - v (σ p.2)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, (v p.1 - v p.2) := by
  have h1 := det_rev (v ∘ σ)
  have h2 := det_rev v
  rw [det_vand_comp] at h1 h2
  have h3 := det_vand_comp v σ
  simp only [Function.comp_apply] at h1
  rw [← h1, ← h2, h3]
  ring

private lemma evalAt_alternant {n : ℕ} (z : Fin n → ℂˣ) :
    evalAt z (alternant (staircase n)) = ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [alternant_eq_det]
    exact (Finset.prod_of_isEmpty _).symm
  · have h := det_rev (fun i => (z i : ℂ))
    rw [det_vand_comp] at h
    rw [alternant_staircase_eq_vdm hn, map_mul, evalAt_vdm_det, ← h, mul_comm]
    simp

theorem UpperTheory.Gal.Gen.rFormula_pf :
    UpperTheory.Gal.Gen.RFormula := by
  intro n t l z hz
  have hD : ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp h => ?_
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact hlt.ne (hz (Units.ext (sub_eq_zero.mp h)))
  have key := congrArg (evalAt z) (alternant_mul_altQuot (monomial l * hlFactor n t))
  rw [map_mul, evalAt_antisymm, evalAt_alternant] at key
  refine mul_left_cancel₀ hD ?_
  have hR : hlR t l = altQuot (monomial l * hlFactor n t) := rfl
  rw [hR, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs := sign_sq_one σ
  have hc : ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p ∈ prs n, ((z p.1 : ℂ) - (z p.2 : ℂ)) :=
    prod_comp (fun i => (z i : ℂ)) σ
  rw [map_mul, monomial, evalAt_single, one_mul, evalAt_hlFactor, Finset.prod_div_distrib, hc]
  simp only [Function.comp_apply]
  have hs0 : ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hs
  field_simp
  linear_combination ((monomialChar l (z ∘ σ)) * ∏ p ∈ prs n, ((z (σ p.1) : ℂ) - t * (z (σ p.2) : ℂ))) * hs
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_shift {n : ℕ} (c : ℤ) (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) :
    pt ((fun i : Fin n => (c - ((i : ℕ) : ℤ)) • s) + θ) =
      fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i := by
  funext i
  simp only [pt, Pi.add_apply, AddCircle.toCircle_add, AddCircle.toCircle_zsmul, map_mul, map_zpow]

private lemma prod_zpow_sum {ι : Type*} (S : Finset ι) (u : ℂˣ) (f : ι → ℤ) :
    ∏ i ∈ S, u ^ f i = u ^ ∑ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private lemma monoChar_shift {n : ℕ} (l : Fin n → ℤ) (c : ℤ) (m : ℕ)
    (hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) (u : ℂˣ) :
    monomialChar l (fun i : Fin n => u ^ (c - ((i : ℕ) : ℤ))) = (u : ℂ) ^ m := by
  rw [monomialChar_apply, ← Units.coe_prod]
  have h : ∏ i : Fin n, (u ^ (c - ((i : ℕ) : ℤ))) ^ l i = u ^ (m : ℤ) := by
    rw [← hm, ← prod_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, mul_comm]
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val]

private lemma key {n : ℕ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hM : MeanVal) (hD : DensCont)
    (l : Fin n → ℤ) (c : ℤ) (m : ℕ) (hcm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = m) :
    ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * half (t : ℂ) (pt θ) =
      ∫ θ : Fin n → UnitAddCircle, monomialChar l (pt θ) * (if m = 0 then 1 else 0) := by
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  obtain ⟨hhalf, -, hev, hnorm⟩ := hD n t ht0 ht1
  have hmono : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have h := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using h
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hFc : Continuous F := hmono.mul hhalf
  let a : UnitAddCircle → Fin n → UnitAddCircle := fun s i => (c - ((i : ℕ) : ℤ)) • s
  have ha : Continuous a := continuous_pi fun i => continuous_zsmul _
  have hshift : ∀ s, ∫ θ, F (a s + θ) = ∫ θ, F θ := fun s => integral_add_left_eq_self F (a s)
  have hG : Continuous (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ)) :=
    hFc.comp ((ha.comp continuous_fst).add continuous_snd)
  have hint : Integrable (Function.uncurry fun (s : UnitAddCircle) (θ : Fin n → UnitAddCircle) => F (a s + θ))
      ((volume : Measure UnitAddCircle).prod (volume : Measure (Fin n → UnitAddCircle))) :=
    hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ θ, F θ = ∫ s : UnitAddCircle, ∫ θ, F (a s + θ) := by
    simp only [hshift, integral_const, probReal_univ, one_smul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  dsimp only
  have hpt : ∀ s, pt (a s + θ) = (fun i : Fin n => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ))) * pt θ := by
    intro s
    rw [pt_shift]
    rfl
  simp only [hF, hpt, map_mul, monoChar_shift l c m hcm]
  have hz := hM n t ht0 ht1 (pt θ) (hnorm θ) c m
  have hcoe : ∀ s : UnitAddCircle, ((Circle.toUnits (AddCircle.toCircle s) : ℂˣ) : ℂ) = (AddCircle.toCircle s : ℂ) :=
    fun s => rfl
  calc _ = ∫ s : UnitAddCircle, monomialChar l (pt θ) * ((AddCircle.toCircle s : ℂ) ^ m *
        half (t : ℂ) (fun i => Circle.toUnits (AddCircle.toCircle s) ^ (c - ((i : ℕ) : ℤ)) * pt θ i)) := by
        congr 1
        funext s
        rw [hcoe, mul_comm (_ ^ m), mul_assoc]
        rfl
    _ = _ := by rw [integral_const_mul, hz]

theorem UpperTheory.Gal.Gen.halfInt_pf :
    UpperTheory.Gal.Gen.WtPos → UpperTheory.Gal.Gen.MeanVal → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.HalfInt := by
  intro hW hM hD n t ht0 ht1 l hl
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  by_cases h0 : l = 0
  · subst h0
    rw [key t ht0 ht1 hM hD (0 : Fin n → ℤ) 0 0 (by simp)]
    simp [monomialChar_zero]
  · obtain ⟨c, hc⟩ := hW n l hl h0
    have hm : ∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ)) = ((∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat : ℤ) :=
      (Int.toNat_of_nonneg hc.le).symm
    rw [key t ht0 ht1 hM hD l c _ hm]
    have hne : (∑ i : Fin n, l i * (c - ((i : ℕ) : ℤ))).toNat ≠ 0 := by omega
    simp [hne, h0]
end
