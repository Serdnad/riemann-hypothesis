module

public import Mathlib.Data.Finset.Finsupp
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
public import Mathlib.NumberTheory.RamificationInertia.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

section

open Filter Topology Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {ι : Type*}

def ebox (s : Finset ι) (J : ι → ℕ) : Finset (ι →₀ ℕ) := s.finsupp fun i => range (J i + 1)

theorem mem_ebox {s : Finset ι} {J : ι → ℕ} {v : ι →₀ ℕ} :
    v ∈ ebox s J ↔ v.support ⊆ s ∧ ∀ i ∈ s, v i ≤ J i := by
  classical
  simp [ebox, Finset.mem_finsupp_iff, Nat.lt_succ_iff]

theorem sum_ebox (f : ι → ℕ → ℝ) (hf : ∀ i, f i 0 = 1) (s : Finset ι) (J : ι → ℕ) :
    ∑ v ∈ ebox s J, v.prod f = ∏ i ∈ s, ∑ j ∈ range (J i + 1), f i j := by
  classical
  rw [Finset.prod_sum, ebox, Finset.finsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Finsupp.prod_of_support_subset _ (Finsupp.support_indicator_subset s g) _ (fun i _ => hf i),
    ← Finset.prod_attach s]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.indicator_apply, dite_eq_left i.2]

theorem mem_ebox_support {v w : ι →₀ ℕ} : v ∈ ebox w.support w ↔ v ≤ w := by
  rw [mem_ebox, Finsupp.le_def]
  constructor
  · rintro ⟨hs, hle⟩ i
    by_cases hi : i ∈ w.support
    · exact hle i hi
    · have h0 : v i = 0 := by
        by_contra h
        exact hi (hs (Finsupp.mem_support_iff.mpr h))
      rw [h0]
      exact Nat.zero_le _
  · intro h
    refine ⟨fun i hi => ?_, fun i _ => h i⟩
    rw [Finsupp.mem_support_iff] at hi ⊢
    have := h i
    omega

def dif (R : ι → ℕ → ℝ) (i : ι) : ℕ → ℝ
  | 0 => 1
  | j + 1 => R i (j + 1) - R i j

theorem sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), dif R i j = R i J := by
  induction J with
  | zero => simp [dif, hR]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp [dif]

theorem prod_eq_sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (w : ι →₀ ℕ) :
    w.prod R = ∑ v ∈ ebox w.support w, v.prod (dif R) := by
  rw [sum_ebox (dif R) (fun i => rfl) w.support w, Finsupp.prod]
  exact Finset.prod_congr rfl fun i _ => (sum_dif R hR i (w i)).symm

theorem summable_prod {u : ι → ℕ → ℝ} (hu0 : ∀ i, u i 0 = 1) (hu : ∀ i j, 0 ≤ u i j) {t : ι → ℝ}
    (ht : Summable t) (hut : ∀ i J, ∑ j ∈ range (J + 1), u i j ≤ 1 + t i) :
    Summable fun v : ι →₀ ℕ => v.prod u := by
  classical
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    have h := hut i 0
    simp [hu0] at h
    linarith
  apply summable_of_sum_le (c := Real.exp (∑' i, t i)) (fun v => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
  intro F
  have hsub : F ⊆ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i) := by
    intro v hv
    rw [mem_ebox]
    exact ⟨fun i hi => Finset.mem_biUnion.mpr ⟨v, hv, hi⟩,
      fun i _ => Finset.le_sup (f := fun v : ι →₀ ℕ => v i) hv⟩
  calc ∑ v ∈ F, v.prod u
      ≤ ∑ v ∈ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i), v.prod u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
    _ = ∏ i ∈ F.biUnion (fun v => v.support), ∑ j ∈ range ((F.sup fun v => v i) + 1), u i j :=
        sum_ebox u hu0 _ _
    _ ≤ ∏ i ∈ F.biUnion (fun v => v.support), Real.exp (t i) := by
        apply Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => hu i j)
        intro i _
        calc _ ≤ 1 + t i := hut i _
          _ ≤ Real.exp (t i) := by linarith [Real.add_one_le_exp (t i)]
    _ = Real.exp (∑ i ∈ F.biUnion (fun v => v.support), t i) := (Real.exp_sum _ t).symm
    _ ≤ Real.exp (∑' i, t i) := Real.exp_le_exp.mpr (ht.sum_le_tsum _ (fun i _ => ht0 i))

theorem summable_sq_geom : Summable fun j : ℕ => 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
  have h0 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  refine (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left 8).congr fun j => ?_
  first
    | ring
    | (simp only [Pi.add_apply]; ring)
    | (simp; ring)

def cGeom : ℝ := ∑' j : ℕ, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j

variable {q : ι → ℝ}

def nrm (q : ι → ℝ) (v : ι →₀ ℕ) : ℝ := v.prod fun i e => q i ^ e

theorem nrm_pos (hq : ∀ i, 2 ≤ q i) (v : ι →₀ ℕ) : 0 < nrm q v := by
  unfold nrm Finsupp.prod
  exact Finset.prod_pos fun i _ => pow_pos (by linarith [hq i]) _

theorem abs_div_nrm (f : ι → ℕ → ℝ) (v : ι →₀ ℕ) :
    |v.prod f| / nrm q v = v.prod fun i e => |f i e| / q i ^ e := by
  unfold nrm Finsupp.prod
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]

theorem sum_dif_le (hq : ∀ i, 2 ≤ q i) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), |dif R i j| / q i ^ j ≤ 1 + cGeom * (q i ^ 2)⁻¹ := by
  have hq0 : 0 < q i := by linarith [hq i]
  rw [Finset.sum_range_succ']
  simp only [dif, pow_zero, div_one, abs_one]
  rw [add_comm]
  refine add_le_add le_rfl ?_
  have hterm : ∀ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1) ≤
      (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) := by
    intro j _
    have hqj : 0 < q i ^ (j + 1) := pow_pos hq0 _
    have hqne : q i ≠ 0 := hq0.ne'
    rw [div_le_iff₀ hqj]
    have hx : 1 ≤ (q i / 2) ^ j := one_le_pow₀ (by linarith [hq i])
    have hc : 0 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by positivity
    have e : (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1) =
        8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
      have h2 : (q i ^ 2)⁻¹ * q i ^ (j + 1) = q i ^ j / q i := by
        rw [pow_succ (q i) j, sq]
        first
          | (field_simp; ring)
          | field_simp
      calc (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1)
          = 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j * ((q i ^ 2)⁻¹ * q i ^ (j + 1)) := by ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * ((1 / 2 : ℝ) ^ j * q i ^ j) / q i := by rw [h2]; ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by rw [← mul_pow]; ring_nf
    rw [e]
    calc |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i := hRb i j
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
        first
          | exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hc hx) hq0.le
          | exact (div_le_div_iff_of_pos_right hq0).mpr (le_mul_of_one_le_right hc hx)
          | exact (div_le_div_right hq0).mpr (le_mul_of_one_le_right hc hx)
  calc ∑ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1)
      ≤ ∑ j ∈ range J, (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) :=
        Finset.sum_le_sum hterm
    _ = (q i ^ 2)⁻¹ * ∑ j ∈ range J, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (q i ^ 2)⁻¹ * cGeom := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact summable_sq_geom.sum_le_tsum _ (fun j _ => by positivity)
    _ = cGeom * (q i ^ 2)⁻¹ := mul_comm _ _

theorem summable_dif (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) :
    Summable fun v : ι →₀ ℕ => |v.prod (dif R)| / nrm q v := by
  have h := summable_prod (u := fun i e => |dif R i e| / q i ^ e) (fun i => by simp [dif])
    (fun i j => div_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hq i]) _))
    (hsum.mul_left cGeom) (fun i J => sum_dif_le hq hRb i J)
  exact h.congr fun v => (abs_div_nrm (dif R) v).symm

end Formalism.HermitianLattices.Ext.L3.A5
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

variable {K : Type} [Field K] [NumberField K]

def resChar (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (P.under ℤ)

theorem span_resChar (P : Ideal (𝓞 K)) : Ideal.span {(resChar P : ℤ)} = P.under ℤ := Int.ideal_span_absNorm_eq_self _

theorem under_ne_bot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P.under ℤ ≠ ⊥ := by
  intro h
  have hPb : P = ⊥ := Ideal.eq_bot_of_comap_eq_bot h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K) hPb

theorem under_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (P.under ℤ).IsMaximal := by
  haveI := hP
  exact Ideal.IsMaximal.under ℤ P

theorem resChar_prime {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (resChar P).Prime := by

  have h1 := span_resChar P
  have hmax := under_isMaximal hP
  rw [← h1] at hmax
  have hne : ((resChar P : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply under_ne_bot hP
    rw [← h1, h0]
    simp
  have hpr := (Ideal.span_singleton_prime hne).mp hmax.isPrime
  exact Nat.prime_iff_prime_int.mpr hpr

theorem exists_absNorm_eq_pow {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P = resChar P ^ k := by

  have hp := resChar_prime hP
  haveI : P.LiesOver (Ideal.span {((resChar P : ℕ) : ℤ)}) := ⟨span_resChar P⟩
  have h1 := Ideal.absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)
  rw [show (((resChar P : ℕ) : ℤ)).natAbs = resChar P by simp] at h1
  refine ⟨_, ?_, h1⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at h1
  exact hP.ne_top h1

theorem resChar_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    resChar P ≤ Ideal.absNorm P := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  rw [hk2]
  exact Nat.le_self_pow (by omega) _

theorem resChar_le_of_sq {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {q : ℕ}
    (hq : Ideal.absNorm P = q ^ 2) : resChar P ≤ q := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  have hp := resChar_prime hP
  have hdvd : resChar P ∣ q ^ 2 := by
    rw [← hq, hk2]
    exact dvd_pow_self _ (by omega)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h0 : resChar P ^ k = 0 := by rw [← hk2, hq]; simp
    exact hp.ne_zero (pow_eq_zero_iff (by omega) |>.mp h0)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (hp.dvd_of_dvd_pow hdvd)

set_option linter.deprecated false in
theorem card_filter_resChar_le (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (n : ℕ) :
    (s.filter (fun P => resChar P.1 = n)).card ≤ finrank ℚ K := by

  classical
  by_cases hn : ∃ P ∈ s, resChar P.1 = n
  · obtain ⟨P0, -, hP0⟩ := hn
    have hJ : Ideal.span {((n : ℕ) : ℤ)} = P0.1.under ℤ := by
      rw [← hP0]
      exact span_resChar P0.1
    haveI : (Ideal.span {((n : ℕ) : ℤ)}).IsMaximal := by
      rw [hJ]
      exact under_isMaximal P0.2
    have hJne : Ideal.span {((n : ℕ) : ℤ)} ≠ ⊥ := by
      rw [hJ]
      exact under_ne_bot P0.2
    calc (s.filter (fun P => resChar P.1 = n)).card
        ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((n : ℕ) : ℤ)}) (𝓞 K)).card := by
          refine Finset.card_le_card_of_injOn (fun P => P.1) (by
            intro P hP
            rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hJne]
            obtain ⟨-, hPn⟩ := Finset.mem_filter.mp hP
            refine ⟨P.2.isPrime, ⟨?_⟩⟩
            rw [← hPn]
            exact span_resChar P.1) (fun a _ b _ h => Subtype.ext h)
      _ ≤ finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hJne
  · push_neg at hn
    rw [Finset.filter_false_of_mem (fun P hP => hn P hP)]
    simp

theorem summable_resChar_sq :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((resChar P.1 : ℝ) ^ 2)⁻¹) := by

  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  refine summable_of_sum_le (c := (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) (fun P => by positivity)
    (fun u => ?_)
  calc ∑ P ∈ u, ((resChar P.1 : ℝ) ^ 2)⁻¹
      = ∑ n ∈ u.image (fun P => resChar P.1),
          ∑ P ∈ u.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ n ∈ u.image (fun P => resChar P.1),
          ((u.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => resChar P.1), (finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_filter_resChar_le u n
    _ = (finrank ℚ K : ℝ) * ∑ n ∈ u.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)

end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
end
end

section

namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

theorem surj_of_invol (hσ : ∀ x, σ (σ x) = x) : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩

theorem comap_isMaximal_invol (hσ : ∀ x, σ (σ x) = x) {P : Ideal B} (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (surj_of_invol hσ)

theorem fix_ι (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (a : A) : σ (ι a) = ι a :=
  (hfix _).2 ⟨a, rfl⟩

theorem comap_ι_comap (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (P : Ideal B) :
    (P.comap σ).comap ι = P.comap ι := by
  ext a
  simp only [Ideal.mem_comap, fix_ι hfix]

theorem comap_eq_comap_iff (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P Q : Ideal B} (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap ι = Q.comap ι ↔ Q = P ∨ Q = P.comap σ := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP

    have hout : ∀ R : Ideal B, R.IsMaximal → Q ≠ R → ∃ y ∈ Q, y ∉ R := by
      intro R hR hQR
      by_contra hc
      push_neg at hc
      exact hQR (hQ.eq_of_le hR.ne_top hc)
    obtain ⟨y, hyQ, hyP⟩ := hout P hP hne.1
    obtain ⟨z, hzQ, hzP'⟩ := hout _ hP' hne.2

    have hx : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.comap σ := by
      by_cases hy' : y ∈ P.comap σ
      · by_cases hz' : z ∈ P
        · refine ⟨y + z, Q.add_mem hyQ hzQ, fun h' => hyP ?_, fun h' => hzP' ?_⟩
          · simpa using P.sub_mem h' hz'
          · simpa using (P.comap σ).sub_mem h' hy'
        · exact ⟨z, hzQ, hz', hzP'⟩
      · exact ⟨y, hyQ, hyP, hy'⟩
    obtain ⟨x, hxQ, hxP, hxP'⟩ := hx
    have hfx : σ (x * σ x) = x * σ x := by rw [map_mul, hσ, mul_comm]
    obtain ⟨a, ha⟩ := (hfix _).1 hfx
    have haQ : a ∈ Q.comap ι := by
      rw [Ideal.mem_comap, ha]
      exact Q.mul_mem_right _ hxQ
    rw [← h, Ideal.mem_comap, ha] at haQ
    rcases hP.isPrime.mem_or_mem haQ with h1 | h1
    · exact hxP h1
    · exact hxP' h1
  · rintro (rfl | rfl)
    · rfl
    · exact (comap_ι_comap hfix P).symm

theorem exists_sub_mem_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) (b : B) : ∃ a : A, b - ι a ∈ P := by
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  rw [Ideal.mem_comap] at hv
  have hfx : σ (b * v + σ (b * v)) = b * v + σ (b * v) := by rw [map_add (f := _), hσ, add_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  refine ⟨a, ?_⟩
  have hv' : v = 1 - u := by rw [← huv]; ring
  have : b - ι a = b * u - σ b * σ v := by rw [ha, hv']; simp only [map_mul, map_sub, map_one]; ring
  rw [this]
  exact P.sub_mem (P.mul_mem_left _ hu) (P.mul_mem_left _ hv)

theorem card_quot_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) :
    Nat.card (A ⧸ P.comap ι) = Nat.card (B ⧸ P) := by
  let f : A ⧸ P.comap ι →+* B ⧸ P := Ideal.quotientMap P ι le_rfl
  have hinj : Function.Injective f := Ideal.quotientMap_injective
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_of_split hσ hfix hP hc b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    simpa using P.neg_mem ha
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem not_isPrime_map_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) : ¬ ((P.comap ι).map ι).IsPrime := by
  intro hpr
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  have hu' : u ∉ P.comap σ := by
    intro h
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ (P.comap σ).add_mem h hv))
  have hle1 : (P.comap ι).map ι ≤ P := Ideal.map_comap_le
  have hle2 : (P.comap ι).map ι ≤ P.comap σ := by
    rw [← comap_ι_comap hfix P]
    exact Ideal.map_comap_le
  have hfx : σ (u * σ u) = u * σ u := by rw [map_mul, hσ, mul_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  have hmem : u * σ u ∈ (P.comap ι).map ι := by
    rw [← ha]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap, ha]
    exact P.mul_mem_right _ hu
  rcases hpr.mem_or_mem hmem with h1 | h1
  · exact hu' (hle2 h1)
  · exact hu' (by rw [Ideal.mem_comap]; exact hle1 h1)

end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
end
