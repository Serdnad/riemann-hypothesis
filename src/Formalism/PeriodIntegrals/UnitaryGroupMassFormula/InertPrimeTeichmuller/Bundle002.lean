module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

theorem ultra_tail {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] (x : ℕ → E) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) (k j : ℕ) :
    ‖x (j + k) - x k‖ ≤ r ^ (k + 1) := by
  induction j with
  | zero =>
    simp only [zero_add, sub_self, norm_zero]
    positivity
  | succ j ih =>
    have h1 := h (j + k)
    have h2 : ‖x (j + 1 + k) - x k‖ ≤ max ‖x (j + k + 1) - x (j + k)‖ ‖x (j + k) - x k‖ := by
      have h4 := IsUltrametricDist.norm_add_le_max (x (j + k + 1) - x (j + k)) (x (j + k) - x k)
      rw [show j + 1 + k = j + k + 1 by ring]
      simpa using h4
    have h3 : r ^ (j + k + 1) ≤ r ^ (k + 1) := pow_le_pow_of_le_one hr0 hr1 (by omega)
    exact h2.trans (max_le (h1.trans h3) ih)

theorem ultra_limit {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]
    (x : ℕ → E) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) :
    Tendsto x atTop (𝓝 (limUnder atTop x)) ∧ ∀ k, ‖limUnder atTop x - x k‖ ≤ r ^ (k + 1) := by
  have hc : CauchySeq x := cauchySeq_of_le_geometric r r hr1 (fun n => by
    rw [dist_comm, dist_eq_norm, ← pow_succ']; exact h n)
  have ht := hc.tendsto_limUnder
  refine ⟨ht, fun k => ?_⟩
  have ht' : Tendsto (fun j => ‖x (j + k) - x k‖) atTop (𝓝 ‖limUnder atTop x - x k‖) :=
    (((tendsto_add_atTop_iff_nat k).mpr ht).sub_const (x k)).norm
  exact le_of_tendsto' ht' (fun j => ultra_tail x hr0 hr1.le h k j)

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

theorem pinv_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem pinv_nonneg : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

def tseq (τ : K →+* ℂ_[p]) (a : 𝓞 K) (k : ℕ) : ℂ_[p] := τ ((a ^ ((p ^ 2) ^ k) : 𝓞 K) : K)

def teich (τ : K →+* ℂ_[p]) (a : 𝓞 K) : ℂ_[p] := limUnder atTop (tseq τ a)

theorem tau_pow (τ : K →+* ℂ_[p]) (x : 𝓞 K) (n : ℕ) : τ ((x ^ n : 𝓞 K) : K) = τ (x : K) ^ n := by
  simp [map_pow]

theorem tau_sub (τ : K →+* ℂ_[p]) (x y : 𝓞 K) : τ ((x - y : 𝓞 K) : K) = τ (x : K) - τ (y : K) := by
  simp [map_sub]

theorem dvd_pow_q_sub (a b : 𝓞 K) (h : (p : 𝓞 K) ∣ a - b) (k : ℕ) :
    (p : 𝓞 K) ^ (k + 1) ∣ a ^ ((p ^ 2) ^ k) - b ^ ((p ^ 2) ^ k) := by
  have h1 := dvd_sub_pow_of_dvd_sub h (2 * k)
  rw [show (p ^ 2) ^ k = p ^ (2 * k) by rw [← pow_mul]]
  exact (pow_dvd_pow _ (by omega)).trans h1

theorem tseq_step (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K)
    (k : ℕ) : ‖tseq τ a (k + 1) - tseq τ a k‖ ≤ (p : ℝ)⁻¹ ^ (k + 1) := by
  have h1 := dvd_pow_q_sub (a ^ (p ^ 2)) a (hq a) k
  rw [← pow_mul, ← pow_succ'] at h1
  have := norm_tau_dvd τ h1
  simpa [tseq, map_sub] using this

theorem teich_spec (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K) :
    Tendsto (tseq τ a) atTop (𝓝 (teich τ a)) ∧
      ∀ k, ‖teich τ a - tseq τ a k‖ ≤ (p : ℝ)⁻¹ ^ (k + 1) :=
  ultra_limit (tseq τ a) pinv_nonneg pinv_lt_one (tseq_step τ hq a)

theorem teich_close (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K) :
    ‖teich τ a - τ (a : K)‖ ≤ (p : ℝ)⁻¹ := by
  have h := (teich_spec τ hq a).2 0
  simp only [tseq, pow_zero, pow_one, zero_add] at h
  exact h

theorem teich_pow (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K) :
    teich τ a ^ (p ^ 2) = teich τ a := by
  have h1 := ((teich_spec τ hq a).1).pow (p ^ 2)
  have h2 := (tendsto_add_atTop_iff_nat 1).mpr (teich_spec τ hq a).1
  have e : (fun k => tseq τ a k ^ (p ^ 2)) = fun k => tseq τ a (k + 1) := by
    funext k
    simp only [tseq]
    rw [← tau_pow, ← pow_mul, ← pow_succ]
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

theorem teich_c (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a b : 𝓞 K)
    (hb : (p : 𝓞 K) ∣ b - a ^ p) : teich τ b = teich τ a ^ p := by
  have h1 := ((teich_spec τ hq a).1).pow p
  have hd : Tendsto (fun k => tseq τ b k - tseq τ a k ^ p) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => (p : ℝ)⁻¹ ^ k) (fun k => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one pinv_nonneg pinv_lt_one)
    have h2 := dvd_pow_q_sub b (a ^ p) hb k
    have h3 := norm_tau_dvd τ h2
    have e : tseq τ b k - tseq τ a k ^ p = τ ((b ^ ((p ^ 2) ^ k) - (a ^ p) ^ ((p ^ 2) ^ k) : 𝓞 K) : K) := by
      simp only [tseq]
      have e2 : (a ^ ((p ^ 2) ^ k)) ^ p = (a ^ p) ^ ((p ^ 2) ^ k) := pow_right_comm _ _ _
      rw [tau_sub, ← tau_pow, e2]
    rw [e]
    exact h3.trans (pow_le_pow_of_le_one pinv_nonneg pinv_lt_one.le (by omega))
  have h4 := h1.add hd
  simp only [add_sub_cancel, add_zero] at h4
  exact tendsto_nhds_unique (teich_spec τ hq b).1 h4

end PI.OkpW
end
end

section

open NumberField

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

theorem c_frob (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) (hp2 : p ≠ 2)
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) (a : 𝓞 K) :
    (p : 𝓞 K) ∣ RingOfIntegers.mapRingHom c a - a ^ p := by
  classical
  haveI hmax := isMaximal_span_p (K := K) (p := p) hP
  have hle : Ideal.span {(p : 𝓞 K)} ≤
      (Ideal.span {(p : 𝓞 K)}).comap (RingOfIntegers.mapRingHom c) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show RingOfIntegers.mapRingHom c (p : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  let σ : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) →+* (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.quotientMap _ (RingOfIntegers.mapRingHom c) hle
  have hσ : ∀ y : 𝓞 K, σ (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (RingOfIntegers.mapRingHom c y) := fun y => Ideal.quotientMap_mk
  haveI : CharP (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p := CharP.quotient (𝓞 K) p
    (mem_nonunits_iff.mpr fun hu => hP.ne_top (Ideal.span_singleton_eq_top.mpr hu))
  haveI : ExpChar (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p := ExpChar.prime hp.out
  have h2 : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) = 0 := by exact_mod_cast h
    have hd := (CharP.cast_eq_zero_iff (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p 2).mp h'
    have hp3 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have := hp.out.two_le
    omega
  have hfixZ : ∀ z : ℤ, ((z : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}))) ^ p = z := fun z => by rw [← frobenius_def, map_intCast]
  have h2p : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ^ p = 2 := by rw [← frobenius_def, map_ofNat]
  have hdich : ∀ x : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), x ^ p = x ∨ x ^ p = σ x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ := add_c_int hK c hc a
    obtain ⟨n2, hn2⟩ := add_c_int hK c hc (a ^ 2)
    have ht : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a +
        σ (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a) = (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) := by
      rw [hσ, ← map_add (f := _), hn, map_intCast]
    have ht2 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a ^ 2 +
        σ (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a) ^ 2 = (n2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) := by
      have := congrArg (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})) hn2
      rw [map_add (f := _), map_intCast, map_pow, map_pow] at this
      rw [hσ, ← this, map_pow (Ideal.Quotient.mk _) ((RingOfIntegers.mapRingHom c) a)]
    generalize Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a = x at ht ht2 ⊢
    have hm : (2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * (x * σ x) = (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ^ 2 - n2 := by
      rw [← ht, ← ht2]; ring
    have hmp : (x * σ x) ^ p = x * σ x := by
      have h1 : ((2 : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * (x * σ x)) ^ p = 2 * (x * σ x) := by
        rw [hm, sub_pow_char, ← pow_mul, mul_comm 2 p, pow_mul, hfixZ, hfixZ]
      rw [mul_pow, h2p] at h1
      exact mul_left_cancel₀ h2 h1
    have hzero : x ^ 2 - (n : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) * x + x * σ x = 0 := by
      rw [← ht]; ring
    have hfr := congrArg (frobenius (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p) hzero
    rw [map_zero, map_add (f := _), map_sub, map_mul, map_pow, map_intCast, frobenius_def,
      frobenius_def, hmp] at hfr
    have hq : (x ^ p - x) * (x ^ p - σ x) = 0 := by
      rw [← hfr, ← ht]; ring
    rcases mul_eq_zero.mp hq with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hex : ∃ y : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), y ^ p ≠ y := by
    by_contra hcon
    push_neg at hcon
    haveI := finite_quot (K := K) (p := p) hK
    letI := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})
    letI : Field (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.Quotient.field _
    have hp1 : 1 < p := hp.out.one_lt
    have hsub : (Finset.univ : Finset (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) ⊆ ((Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})).roots.toFinset) := by
      intro y _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.X_pow_sub_X_ne_zero hp1)]
      simp [Polynomial.IsRoot, hcon y]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ] at h1
    have h2 := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})))
    rw [Polynomial.natDegree_X_pow_sub_X (R := (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})) hp1] at h2
    have h3 : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact natCard_quot (K := K) (p := p) hK
    have h4 : p ^ 2 ≤ p := h3 ▸ h1.trans h2
    nlinarith [hp1]
  obtain ⟨y, hy⟩ := hex
  have hyσ : y ^ p = σ y := (hdich y).resolve_left hy
  have hall : ∀ x : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}), σ x = x ^ p := by
    intro x
    rcases hdich x with hx | hx
    · have hxy : (x + y) ^ p ≠ x + y := by
        rw [add_pow_char, hx]
        intro h
        exact hy (add_left_cancel h)
      have h1 := (hdich (x + y)).resolve_left hxy
      rw [add_pow_char, hx, hyσ, map_add (f := _)] at h1
      rw [hx]
      exact (add_right_cancel h1).symm
    · exact hx.symm
  have := hall (Ideal.Quotient.mk _ a)
  rw [hσ, ← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at this
  exact this

end PI.OkpW
end
end
