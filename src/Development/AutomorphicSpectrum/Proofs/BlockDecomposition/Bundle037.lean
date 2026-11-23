module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatIdeal

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  have h1 : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    unfold Lat.η Lat.IB
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  unfold Lat.dpE
  rw [Algebra.smul_def, pow_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h1)

theorem dpE_zero : Lat.dpE f ξ l M 0 = 1 := by
  unfold Lat.dpE
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

private theorem dpE_mul_dpE_eq_choose_mul (a b : ℕ) :
    Lat.dpE f ξ l M a * Lat.dpE f ξ l M b =
      (((a + b).choose a : ℕ) : B) * Lat.dpE f ξ l M (a + b) := by
  have h0 : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    rwa [Nat.add_sub_cancel_left] at h1
  have hC : (((a + b).choose a : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have key : ((a.factorial : ℚ))⁻¹ * ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : ℚ) * (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← h0, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ hC, one_mul]
  have key' : algebraMap ℚ B ((a.factorial : ℚ))⁻¹ * algebraMap ℚ B ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : B) * algebraMap ℚ B (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← map_mul, key, map_mul, map_natCast]
  unfold Lat.dpE
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, pow_add]
  linear_combination (Lat.η f ξ l M ^ a * Lat.η f ξ l M ^ b) * key'

private theorem mul_mem_set_f_mul_dpE {y z : B}
    (hy : y ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  obtain ⟨w, a, rfl⟩ := hy
  obtain ⟨w', b, rfl⟩ := hz
  refine ⟨w * w' * (((a + b).choose a : ℕ) : W), a + b, ?_⟩
  rw [map_mul, map_mul, map_natCast]
  linear_combination (f w * f w') * dpE_mul_dpE_eq_choose_mul f ξ l M a b

private theorem mul_mem_closure_f_mul_dpE {y z : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz' => exact AddSubgroup.subset_closure (mul_mem_set_f_mul_dpE f ξ l M hy' hz')
    | zero => rw [mul_zero]; exact zero_mem _
    | add z1 z2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg z _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_mul]; exact neg_mem h

private theorem mem_closure_f_mul_dpE_of_mem_sub {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  unfold Lat.sub at hy
  induction hy using Subring.closure_induction with
  | mem y hy' =>
    apply AddSubgroup.subset_closure
    rcases hy' with ⟨w, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨w, 0, by rw [dpE_zero, mul_one]⟩
    · exact ⟨1, k, by rw [map_one, one_mul]⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, 0, by rw [dpE_zero, map_one, mul_one]⟩
  | add y z _ _ h1 h2 => exact add_mem h1 h2
  | neg y _ h => exact neg_mem h
  | mul y z _ _ h1 h2 => exact mul_mem_closure_f_mul_dpE f ξ l M h1 h2

private theorem exists_repr_of_mem_closure_f_mul_dpE {y : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    ∃ (w₀ : W) (c : ℕ →₀ W), y = f w₀ + c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨w, k, rfl⟩ := hy'
    cases k with
    | zero => exact ⟨w, 0, by rw [dpE_zero, mul_one, Finsupp.sum_zero_index, add_zero]⟩
    | succ j =>
      refine ⟨0, Finsupp.single j w, ?_⟩
      rw [map_zero, zero_add, Finsupp.sum_single_index]
      simp
  | zero => exact ⟨0, 0, by rw [map_zero, Finsupp.sum_zero_index, add_zero]⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, c, rfl⟩ := h1
    obtain ⟨b, d, rfl⟩ := h2
    refine ⟨a + b, c + d, ?_⟩
    rw [Finsupp.sum_add_index', map_add (f := _)]
    · ring
    · intro i
      simp
    · intro i b1 b2
      simp [add_mul]
  | neg y _ h =>
    obtain ⟨a, c, rfl⟩ := h
    refine ⟨-a, -c, ?_⟩
    rw [Finsupp.sum_neg_index, map_neg, neg_add]
    · simp only [map_neg, neg_mul, Finsupp.sum, Finset.sum_neg_distrib]
    · intro i
      simp

private theorem exists_fin_sum_eq_finsupp_sum_f_mul_dpE (c : ℕ →₀ W) :
    ∃ (n : ℕ) (c' : Fin n → W), c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) =
      ∑ i : Fin n, f (c' i) * Lat.dpE f ξ l M (i + 1) := by
  have hs : c.support ⊆ Finset.range (c.support.sup id + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := id) hi
  refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
  rw [Finsupp.sum_of_support_subset c hs (fun i w => f w * Lat.dpE f ξ l M (i + 1))
    (fun _ _ => by simp)]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M (i + 1)) _).symm

private theorem f_xi_eq_f_pow_mul_dpE_one (hl : (l : ℚ) ≠ 0) :
    f ξ = f ((l : W) ^ M) * Lat.dpE f ξ l M 1 := by
  have h1 : Lat.dpE f ξ l M 1 = ((l : ℚ) ^ M)⁻¹ • f ξ := by
    unfold Lat.dpE Lat.η
    rw [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  rw [h1, Algebra.smul_def, ← mul_assoc, map_pow, map_natCast,
    ← map_natCast (algebraMap ℚ B) l, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hl),
    map_one, one_mul]

private theorem finsupp_sum_add_single_zero_f_mul_dpE (c : ℕ →₀ W) (v : W) :
    (c + Finsupp.single 0 v).sum (fun i w => f w * Lat.dpE f ξ l M (i + 1))
      = c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) + f v * Lat.dpE f ξ l M 1 := by
  rw [Finsupp.sum_add_index', Finsupp.sum_single_index]
  all_goals simp [add_mul]

theorem mem_I_iff (m : ℕ) (H : Lat.Hyp f ξ l m) (x : Lat.A f ξ l M) :
    x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  have hI : x ∈ Lat.I f ξ l M ↔ Lat.ι f ξ l M x ∈ Lat.IB f ξ := Iff.rfl
  rw [hI]
  constructor
  · intro hx
    have hsub : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (x : ↥(Lat.sub f ξ l M)).2
    obtain ⟨w₀, c, hc⟩ := exists_repr_of_mem_closure_f_mul_dpE f ξ l M (mem_closure_f_mul_dpE_of_mem_sub f ξ l M hsub)
    have hS : c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) ∈ Lat.IB f ξ :=
      by
        unfold Finsupp.sum
        exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M i))
    have hw : f w₀ ∈ Lat.IB f ξ := by
      have h2 := sub_mem hx hS
      rwa [hc, add_sub_cancel_right] at h2
    unfold Lat.IB at hw
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hw
    obtain ⟨w', rfl⟩ := H.gr 0 H.one_le w₀ b
      (by rw [pow_zero, mul_one, zero_add, pow_one, ← hb, mul_comm])
    have hl : (l : ℚ) ≠ 0 := by
      intro h
      apply H.l0
      have h3 : l = 0 := by exact_mod_cast h
      rw [h3, Nat.cast_zero]
    obtain ⟨n, c', hc'⟩ := exists_fin_sum_eq_finsupp_sum_f_mul_dpE f ξ l M (c + Finsupp.single 0 ((l : W) ^ M * w'))
    refine ⟨n, c', ?_⟩
    rw [← hc', finsupp_sum_add_single_zero_f_mul_dpE f ξ l M, hc]
    simp only [map_mul]
    rw [f_xi_eq_f_pow_mul_dpE_one f ξ l M hl]
    ring
  · rintro ⟨n, c, hc⟩
    rw [hc]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M _))

end

theorem mem_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M m H x
  exact mem_I_iff f ξ l M m H x

end GlobalTheory.CompanionTheory.LatIdeal
end

section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatSpan

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B]

theorem dpE_mul (f : W →+* B) (ξ : W) (l M i j : ℕ) :
    Lat.dpE f ξ l M i * Lat.dpE f ξ l M j =
      ((i + j).choose i : B) * Lat.dpE f ξ l M (i + j) := by
  have hc : (((i + j).choose i : ℕ) : ℚ) * ((i + j).factorial : ℚ)⁻¹ =
      ((i.factorial : ℚ))⁻¹ * ((j.factorial : ℚ))⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at h
    have h' : (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) =
        ((i + j).factorial : ℚ) := by exact_mod_cast h
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [← h']
    have hcne : (((i + j).choose i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
    field_simp
  unfold Lat.dpE
  rw [smul_mul_smul_comm, ← pow_add, ← hc, ← smul_smul, ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul ℚ]

theorem mem_span_of_mem_sub (f : W →+* B) (ξ : W) (l M : ℕ) (x : B) (hx : x ∈ Lat.sub f ξ l M) :
    letI : Algebra W B := f.toAlgebra;
    x ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
  letI : Algebra W B := f.toAlgebra
  have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
  have h0 : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]
  have hgen : ∀ i, Lat.dpE f ξ l M i ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hW : ∀ w : W, f w ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro w
    have h := Submodule.smul_mem _ w (hgen 0)
    rwa [hsm, h0, mul_one] at h
  have hnat : ∀ (n : ℕ) (y : B), y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      (n : B) * y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro n y hy
    have h := Submodule.smul_mem _ (n : W) hy
    rwa [hsm, map_natCast] at h
  have hmul : ∀ a b : B, a ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      a * b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨j, rfl⟩ := hb
        rw [dpE_mul]
        exact hnat _ _ (hgen _)
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ w hy
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
    | smul w y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ w hy
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact hW w
    · exact hgen i
  | zero => exact Submodule.zero_mem _
  | one => rw [← h0]; exact hgen 0
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | neg y _ hy => exact Submodule.neg_mem _ hy
  | mul y z _ _ hy hz => exact hmul y z hy hz

theorem mem_sub_iff : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  intro W B _ _ _ f ξ l M x
  constructor
  · intro hx
    letI : Algebra W B := f.toAlgebra
    have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_mem_sub f ξ l M x hx)
    refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M i), Finsupp.sum]
    have hsub : c.support ⊆ Finset.range (c.support.sup id + 1) := by
      intro i hi
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    rw [Finset.sum_congr rfl (fun i _ => hsm (c i) (Lat.dpE f ξ l M i))]
    refine Finset.sum_subset hsub fun i _ hi => ?_
    rw [Finsupp.notMem_support_iff.1 hi, map_zero, zero_mul]
  · rintro ⟨n, c, rfl⟩
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inl ⟨c i, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.LatSpan
end

section

set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

private theorem exists_sub_iota_mem_of_sub_involution_mem {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (b : B) (hb : b ∈ Lat.sub f ξ l M) : ∃ w : W, f w - b ∈ Lat.IB f ξ := by
  have hη : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    rw [Lat.η, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hle : Lat.sub f ξ l M ≤
      (((Ideal.Quotient.mk (Lat.IB f ξ)).comp f).range).comap (Ideal.Quotient.mk (Lat.IB f ξ)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨w, rfl⟩)
    · cases i with
      | zero => exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨1, by simp [Lat.dpE]⟩)
      | succ i =>
        have hd : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
          rw [Lat.dpE, Algebra.smul_def, pow_succ']
          exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hη)
        refine Subring.mem_comap.2 (RingHom.mem_range.2 ⟨0, ?_⟩)
        rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
        exact hd
  obtain ⟨w, hw⟩ := RingHom.mem_range.1 (Subring.mem_comap.1 (hle hb))
  exact ⟨w, Ideal.Quotient.eq.1 hw⟩

theorem pow_mem_span_sup_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∉ Lat.I f ξ l M →
      ∃ n : ℕ, (l : Lat.A f ξ l M) ^ n ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m hH x hx
  have hxmem : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (show ↥(Lat.sub f ξ l M) from x).2
  obtain ⟨w, hw⟩ := exists_sub_iota_mem_of_sub_involution_mem f ξ l M _ hxmem
  have hxw : Lat.ofW f ξ l M w - x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M w - x) ∈ Lat.IB f ξ
    rw [map_sub, Lat.ι_ofW]
    exact hw
  have hξI : Lat.ofW f ξ l M ξ ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M ξ) ∈ Lat.IB f ξ
    rw [Lat.ι_ofW]
    exact Ideal.mem_span_singleton_self _
  have hwnot : ¬ ξ ∣ w := by
    rintro ⟨v, rfl⟩
    apply hx
    have h1 : Lat.ofW f ξ l M (ξ * v) ∈ Lat.I f ξ l M := by
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ hξI
    have h2 := (Lat.I f ξ l M).sub_mem h1 hxw
    simpa using h2
  have hq : Ideal.Quotient.mk (Ideal.span {ξ}) w ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hwnot
  obtain ⟨n, c, hc⟩ := hH.dv _ hq
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmem : (l : W) ^ n - w * u ∈ Ideal.span {ξ} := by
    rw [← Ideal.Quotient.eq]
    simpa using hc
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨n, ?_⟩
  have e : (l : Lat.A f ξ l M) ^ n = Lat.ofW f ξ l M ((l : W) ^ n) := by
    rw [map_pow, map_natCast]
  rw [e, show (l : W) ^ n = w * u + v * ξ by rw [hv]; ring, map_add (f := _), map_mul, map_mul]
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hξI))
  have e2 : Lat.ofW f ξ l M w * Lat.ofW f ξ l M u =
      x * Lat.ofW f ξ l M u + (Lat.ofW f ξ l M w - x) * Lat.ofW f ξ l M u := by ring
  rw [e2]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hxw))

end GlobalTheory.CompanionTheory.Lat
end

section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDP

theorem γB_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B']
    [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (g : B →+* B') {y : B}
    (hy : y ∈ Lat.IB f ξ) (hy' : g y ∈ Lat.IB f' ξ') (n : ℕ) :
    g ((Lat.γB f ξ).dpow n y) = (Lat.γB f' ξ').dpow n (g y) := by
  have h1 := (Lat.γB f ξ).factorial_mul_dpow_eq_pow (n := n) hy
  have h2 := (Lat.γB f' ξ').factorial_mul_dpow_eq_pow (n := n) hy'
  have hu : IsUnit (n.factorial : B') := by
    have := (IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ B')
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  rw [h2, ← map_pow, ← h1, map_mul, map_natCast]

theorem isDPMorphism_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W']
    [CommRing B'] [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)
    (g : B →+* B') (hmap : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M) (u : W')
    (hg : g (f ξ) = f' (u * ξ')) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ))
    (hc' : Lat.DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g hmap) := by
  have hB : ∀ x ∈ Lat.I f ξ l M, g (Lat.ι f ξ l M x) ∈ Lat.IB f' ξ' := by
    intro x hx
    have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
    simp only [Lat.IB, Ideal.mem_span_singleton] at hx' ⊢
    obtain ⟨c, hc0⟩ := hx'
    refine ⟨f' u * g c, ?_⟩
    rw [hc0, map_mul, hg, map_mul]; ring
  have hI : ∀ x ∈ Lat.I f ξ l M, Lat.map f ξ f' ξ' l M g hmap x ∈ Lat.I f' ξ' l M := by
    intro x hx
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g hmap x) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]; exact hB x hx
  refine ⟨Ideal.map_le_iff_le_comap.2 fun x hx => hI x hx, fun {n} x hx => ?_⟩
  apply Lat.ι_injective f' ξ' l M
  rw [Lat.ι_γ f' ξ' l M hc' (hI x hx)]
  simp only [Lat.ι_map]
  rw [Lat.ι_γ f ξ l M hc hx]
  have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
  exact (γB_map f ξ f' ξ' g hx' (hB x hx) n).symm

end GlobalTheory.CompanionTheory.LatDP
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem coface_rel (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i))
    (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)) :
    (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i) := by
  have key : ∀ j : Fin n,
      (k.succAbove i).succAbove ((i.predAbove k).succAbove j) = k.succAbove (i.succAbove j) :=
    fun j => Fin.succAbove_succAbove_succAbove_predAbove k i j
  apply AlgHom.coe_ringHom_injective
  refine (hwp n).uniq (K (n + 1 + 1)) _ _ ?_ ?_
  · rw [AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]
  · intro j
    have h1 : ((δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k))).comp (ι n j)
        = ((δ (n + 1) k).comp (δ n i)).comp (ι n j) := by
      rw [AlgHom.comp_assoc, hδ, hδ, AlgHom.comp_assoc, hδ, hδ, key]
    ext x
    exact AlgHom.congr_fun h1 x

end GlobalTheory.CompanionTheory.WpCoface
end
