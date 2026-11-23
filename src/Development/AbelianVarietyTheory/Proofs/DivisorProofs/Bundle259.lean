module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Trunc
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
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.Kron

open Polynomial

variable {F : Type} [Field F] (c : ℕ → F)

def ev : F[X] →ₗ[F] F := Polynomial.lsum fun i => c i • LinearMap.id

theorem ev_monomial (n : ℕ) (a : F) : ev c (monomial n a) = c n * a := by
  simp [ev, Polynomial.lsum_apply]

theorem ev_expand (q p : F[X]) (n : ℕ) (hp : p.natDegree < n) :
    ev c (q * p) = ∑ j ∈ Finset.range n, p.coeff j * ev c (q * X ^ j) := by
  conv_lhs => rw [p.as_sum_range' n hp]

  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial, show q * (C (p.coeff j) * X ^ j) = p.coeff j • (q * X ^ j) by
    rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]

theorem ev_zero_of_lt (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree < s) : ev c (q * p) = 0 := by
  rw [ev_expand c q p s hp]
  exact Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero]

theorem ev_top (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree ≤ s) : ev c (q * p) = p.coeff s * ev c (q * X ^ s) := by
  rw [ev_expand c q p (s + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ,
    Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero], zero_add]

theorem ev_X_pow_mul (m : ℕ) (q : F[X]) :
    ev c (q * X ^ m) = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * c (m + j) := by
  rw [mul_comm, ev_expand c _ q _ (Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_add, ← monomial_one_right_eq_X_pow, ev_monomial, mul_one]

theorem exists_kill (n : ℕ) (h : hankel c n = 0) :
    ∃ r : F[X], r ≠ 0 ∧ r.natDegree ≤ n ∧ ∀ j ≤ n, ev c (r * X ^ j) = 0 := by
  classical
  unfold hankel at h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine ⟨∑ k : Fin (n + 1), monomial (k : ℕ) (v k), ?_, ?_, ?_⟩
  · intro h0
    apply hv0
    funext k
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h0
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finsupp.single_apply, Fin.val_inj] using this
  · exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 k.2)
  · intro j hj
    have := congrFun hv ⟨j, Nat.lt_succ_of_le hj⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this

    rw [Finset.sum_mul, map_sum, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [monomial_mul_X_pow, ev_monomial, add_comm]

theorem exists_annihilator (N : ℕ) (hN : ∀ n, N ≤ n → hankel c n = 0) :
    ∃ q : F[X], q ≠ 0 ∧ ∀ j, ev c (q * X ^ j) = 0 := by
  classical
  have hex : ∃ d, ∃ q : F[X], q ≠ 0 ∧ q.natDegree = d ∧ d ≤ N ∧ ∀ j ≤ N, ev c (q * X ^ j) = 0 := by
    obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c N (hN N le_rfl)
    exact ⟨_, r, hr0, rfl, hrd, hr⟩
  obtain ⟨q0, hq00, hq0d, hdN, hq0⟩ := Nat.find_spec hex
  have hmin : ∀ r : F[X], r ≠ 0 → r.natDegree < Nat.find hex → ¬ ∀ j ≤ N, ev c (r * X ^ j) = 0 :=
    fun r hr0 hrd hr => Nat.find_min hex hrd ⟨r, hr0, rfl, by omega, hr⟩
  have hlc : (q0.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.2 hq00)
  obtain ⟨q, hqm, hqd, hqe⟩ : ∃ q : F[X], q.Monic ∧ q.natDegree = Nat.find hex ∧
      ∀ j, ev c (q * X ^ j) = (q0.leadingCoeff)⁻¹ * ev c (q0 * X ^ j) := by
    refine ⟨q0 * C (q0.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq00, ?_, fun j => ?_⟩
    · rw [natDegree_mul_C hlc, hq0d]
    · rw [show q0 * C (q0.leadingCoeff)⁻¹ * X ^ j = (q0.leadingCoeff)⁻¹ • (q0 * X ^ j) by
        rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]
  refine ⟨q, hqm.ne_zero, ?_⟩
  by_contra hne
  push_neg at hne
  have hs : ev c (q * X ^ Nat.find hne) ≠ 0 := Nat.find_spec hne
  have hlt : ∀ j < Nat.find hne, ev c (q * X ^ j) = 0 := fun j hj => by
    by_contra h; exact Nat.find_min hne hj h
  generalize Nat.find hne = s at hs hlt
  generalize Nat.find hex = d at hmin hqd hdN
  have hNs : N < s := by
    by_contra h
    push_neg at h
    apply hs
    rw [hqe, hq0 s h, mul_zero]
  obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c s (hN s hNs.le)
  have hrk : ∀ p : F[X], p.natDegree ≤ s → ev c (r * p) = 0 := fun p hp => by
    rw [ev_top c r p s (fun j hj => hr j hj.le) hp, hr s le_rfl, mul_zero]
  obtain ⟨r0, r1, hdiv, hr0deg⟩ : ∃ r0 r1 : F[X], r0 + q * r1 = r ∧ r0.degree < q.degree :=
    ⟨_, _, modByMonic_add_div r q, degree_modByMonic_lt r hqm⟩
  subst hdiv
  have hr0s : r0.natDegree < s := by
    by_cases hz : r0 = 0
    · rw [hz, natDegree_zero]; omega
    · have := natDegree_lt_natDegree hz hr0deg; omega
  by_cases h1 : r1 = 0
  · subst h1
    rw [mul_zero, add_zero] at hr0 hrd hr
    apply hmin r0 hr0 (hqd ▸ natDegree_lt_natDegree hr0 hr0deg)
    intro j hj
    exact hr j (by omega)
  · have hdeg : d + r1.natDegree ≤ s := by
      rw [← hqd, ← natDegree_mul hqm.ne_zero h1]
      have : q * r1 = r0 + q * r1 - r0 := by ring
      rw [this]
      exact (natDegree_sub_le _ _).trans (max_le hrd hr0s.le)
    have key := hrk (q * X ^ (s - d - r1.natDegree))
      (by rw [natDegree_mul_X_pow _ hqm.ne_zero, hqd]; omega)
    rw [add_mul, map_add (f := _)] at key
    have h0 : ev c (r0 * (q * X ^ (s - d - r1.natDegree))) = 0 := by
      rw [show r0 * (q * X ^ (s - d - r1.natDegree)) = q * (r0 * X ^ (s - d - r1.natDegree)) by ring]
      apply ev_zero_of_lt c q _ s hlt
      by_cases hz : r0 = 0
      · rw [hz, zero_mul, natDegree_zero]; omega
      · rw [natDegree_mul_X_pow _ hz]
        have := natDegree_lt_natDegree hz hr0deg
        omega
    have hne1 : r1 * q ≠ 0 := mul_ne_zero h1 hqm.ne_zero
    have hs' : s = (r1 * q).natDegree + (s - d - r1.natDegree) := by
      rw [natDegree_mul h1 hqm.ne_zero, hqd]; omega
    have hcoef : (r1 * q * X ^ (s - d - r1.natDegree)).coeff s = r1.leadingCoeff := by
      have := coeff_mul_X_pow (r1 * q) (s - d - r1.natDegree) (r1 * q).natDegree
      rw [← hs'] at this
      rw [this, coeff_natDegree, leadingCoeff_mul, hqm.leadingCoeff, mul_one]
    have h2 : ev c (q * r1 * (q * X ^ (s - d - r1.natDegree))) = r1.leadingCoeff * ev c (q * X ^ s) := by
      rw [show q * r1 * (q * X ^ (s - d - r1.natDegree)) = q * (r1 * q * X ^ (s - d - r1.natDegree)) by ring,
        ev_top c q _ s hlt (by rw [natDegree_mul_X_pow _ hne1]; omega), hcoef]
    rw [h0, h2, zero_add] at key
    exact hs ((mul_eq_zero.1 key).resolve_left (leadingCoeff_ne_zero.2 h1))

theorem isRat_of_ann (φ : PowerSeries F) (q : F[X]) (hq : q ≠ 0)
    (h : ∀ j, ev (fun i => PowerSeries.coeff i φ) (q * X ^ j) = 0) : IsRat φ := by
  classical
  let R : F[X] := ∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k) * X ^ (q.natDegree - k)
  refine ⟨PowerSeries.trunc q.natDegree ((R : PowerSeries F) * φ), R, ?_, ?_⟩
  · intro h0
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h0
    simp only [R, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single q.natDegree] at this
    · simp only [Nat.sub_self, if_true] at this
      exact hq (leadingCoeff_eq_zero.1 this)
    · intro k hk hkd
      have := Finset.mem_range.1 hk
      rw [if_neg (by omega)]
    · intro hk; exact absurd (Finset.self_mem_range_succ _) hk
  · ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + q.natDegree := ⟨n - q.natDegree, by omega⟩
      have hR : (R : PowerSeries F) = ∑ k ∈ Finset.range (q.natDegree + 1),
          PowerSeries.C (q.coeff k) * PowerSeries.X ^ (q.natDegree - k) := by
        show Polynomial.coeToPowerSeries.ringHom R = _

        rw [map_sum]
        simp [Polynomial.coeToPowerSeries.ringHom_apply]

      rw [hR, Finset.sum_mul, map_sum, ← h m, ev_X_pow_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
      rw [show m + q.natDegree - (q.natDegree - k) = m + k by omega]

end GlobalTheory.Nef.Kron

namespace GlobalTheory.Nef

theorem isRat_of_hankel_eventually_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ),
    (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  intro F _ φ N hN
  obtain ⟨q, hq, h⟩ := Kron.exists_annihilator _ N hN
  exact Kron.isRat_of_ann φ q hq h

end GlobalTheory.Nef
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PlaceResiduePowerBound

open WithZero

variable {F : Type} [Field F]

theorem pow_inj {e : ℕ} (he : e ≠ 0) {a b : ℤᵐ⁰} (h : a ^ e = b ^ e) : a = b :=
  le_antisymm ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.le)
    ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.ge)

theorem pow_le_one_iff' {e : ℕ} (he : e ≠ 0) {a : ℤᵐ⁰} : a ^ e ≤ 1 ↔ a ≤ 1 := by
  simpa using (pow_le_pow_iff_left₀ (zero_le' (a := a)) (zero_le' (a := (1 : ℤᵐ⁰))) he)

theorem pow_of_iff (v q : Valuation F ℤᵐ⁰) (hq : Function.Surjective q)
    (h : ∀ x, v x ≤ 1 ↔ q x ≤ 1) : ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  obtain ⟨π, hπ⟩ := hq (exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hvπ0 : v π ≠ 0 := (Valuation.ne_zero_iff v).2 hπ0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, v π = exp b := ⟨log (v π), (exp_log hvπ0).symm⟩
  have hb0 : b < 0 := by
    have h1 : v π ≤ 1 := (h π).2 (by rw [hπ, ← exp_zero, exp_le_exp]; norm_num)
    have h2 : v π ≠ 1 := by
      intro h1'
      have : q π⁻¹ ≤ 1 := (h _).1 (by rw [map_inv₀, h1', inv_one])
      rw [map_inv₀, hπ, ← exp_neg, ← exp_zero, exp_le_exp] at this
      norm_num at this
    rw [hb, ← exp_zero, exp_le_exp] at h1
    rw [hb, ne_eq, exp_eq_one] at h2
    omega
  have hbe : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
  refine ⟨(-b).toNat, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero, zero_pow (by omega)]
  have hqx : q x ≠ 0 := (Valuation.ne_zero_iff q).2 hx
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
  obtain ⟨c, hc⟩ : ∃ c : ℤ, q x = exp c := ⟨log (q x), (exp_log hqx).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a := ⟨log (v x), (exp_log hvx).symm⟩
  have hqu : q (x * π ^ c) = 1 := by
    rw [map_mul, map_zpow₀, hc, hπ, ← exp_zsmul, ← exp_add, exp_eq_one, smul_eq_mul]; ring
  have hvu : v (x * π ^ c) = exp (a + c * b) := by
    rw [map_mul, map_zpow₀, ha, hb, ← exp_zsmul, ← exp_add, smul_eq_mul]
  have h1 : v (x * π ^ c) ≤ 1 := (h _).2 hqu.le
  have h2 : v (x * π ^ c)⁻¹ ≤ 1 := (h _).2 (by rw [map_inv₀, hqu, inv_one])
  rw [hvu, ← exp_zero, exp_le_exp] at h1
  rw [map_inv₀, hvu, ← exp_neg, ← exp_zero, exp_le_exp] at h2
  have h3 : a + c * b = 0 := by omega
  rw [ha, hc, ← exp_nsmul, exp_inj, nsmul_eq_mul, hbe]
  linear_combination h3

theorem root (v : Valuation F ℤᵐ⁰) (hv : ∃ a, 1 < v a) :
    ∃ q : Valuation F ℤᵐ⁰, Function.Surjective q ∧ ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  classical
  have hS : ∃ n : ℕ, 0 < n ∧ ∃ x, v x = exp (n : ℤ) := by
    obtain ⟨a, ha⟩ := hv
    have ha0 : v a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
    obtain ⟨b, hb⟩ : ∃ b : ℤ, v a = exp b := ⟨_, (exp_log ha0).symm⟩
    rw [hb, ← exp_zero, exp_lt_exp] at ha
    exact ⟨b.toNat, by omega, a, by rw [hb, Int.toNat_of_nonneg ha.le]⟩
  have he0 : 0 < Nat.find hS := (Nat.find_spec hS).1
  obtain ⟨π, hπ⟩ := (Nat.find_spec hS).2
  have hdvd : ∀ x, x ≠ 0 → ∃ m : ℤ, v x = exp ((Nat.find hS : ℤ) * m) := by
    intro x hx
    obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a :=
      ⟨_, (exp_log ((Valuation.ne_zero_iff v).2 hx)).symm⟩
    refine ⟨a / (Nat.find hS : ℤ), ?_⟩
    have hr0 : 0 ≤ a % (Nat.find hS : ℤ) := Int.emod_nonneg _ (by omega)
    have hr1 : a % (Nat.find hS : ℤ) < Nat.find hS := Int.emod_lt_of_pos _ (by omega)
    have hdec := Int.mul_ediv_add_emod a (Nat.find hS : ℤ)
    by_contra hne
    have hr : 0 < a % (Nat.find hS : ℤ) := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; rw [ha, exp_inj]; linear_combination -hdec - h
    have hval : v (x * π ^ (-(a / (Nat.find hS : ℤ)))) = exp (((a % (Nat.find hS : ℤ)).toNat : ℕ) : ℤ) := by
      rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, Int.toNat_of_nonneg hr0, exp_inj,
        smul_eq_mul]
      linear_combination -hdec
    exact Nat.find_min hS (show (a % (Nat.find hS : ℤ)).toNat < Nat.find hS by omega)
      ⟨by omega, _, hval⟩
  have hroot : ∀ x, ∃ c : ℤᵐ⁰, c ^ Nat.find hS = v x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero, zero_pow he0.ne']⟩
    · obtain ⟨m, hm⟩ := hdvd x hx
      exact ⟨exp m, by rw [hm, ← exp_nsmul, nsmul_eq_mul]⟩
  choose qf hqf using hroot
  have hle : ∀ {a b : ℤᵐ⁰}, a ^ Nat.find hS ≤ b ^ Nat.find hS → a ≤ b :=
    fun h => (pow_le_pow_iff_left₀ zero_le' zero_le' he0.ne').1 h
  let q : Valuation F ℤᵐ⁰ :=
    { toFun := qf
      map_zero' := pow_inj he0.ne' (by rw [hqf, map_zero, zero_pow he0.ne'])
      map_one' := pow_inj he0.ne' (by rw [hqf, map_one, one_pow])
      map_mul' := fun x y => pow_inj he0.ne' (by rw [hqf, mul_pow, hqf, hqf, map_mul])
      map_add_le_max' := fun x y => by
        have h := v.map_add x y
        rw [← hqf x, ← hqf y, ← hqf (x + y)] at h
        rcases le_max_iff.1 h with h | h
        · exact le_max_of_le_left (hle h)
        · exact le_max_of_le_right (hle h) }
  have hqq : ∀ x, q x = qf x := fun _ => rfl
  refine ⟨q, ?_, Nat.find hS, he0, fun x => by rw [hqq, hqf]⟩
  have hqπ : q π = exp 1 :=
    pow_inj he0.ne' (by rw [hqq, hqf, hπ, ← exp_nsmul, nsmul_eq_mul, mul_one])
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨0, map_zero q⟩
  · refine ⟨π ^ log t, ?_⟩
    rw [map_zpow₀, hqπ, ← exp_zsmul, smul_eq_mul, mul_one, exp_log ht]

theorem exists_one_lt {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : Valuation E ℤᵐ⁰) (hp : Function.Surjective p) : ∃ a : F, 1 < p (algebraMap F E a) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hp (exp (1 : ℤ))
  have hy1 : 1 < p y := by rw [hy, ← exp_zero, exp_lt_exp]; norm_num
  obtain ⟨f, hfm, hfy⟩ := Algebra.IsIntegral.isIntegral (R := F) y
  rw [hfm.as_sum] at hfy
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hfy
  have hlt : p (∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i) <
      p y ^ f.natDegree := by
    apply p.map_sum_lt (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy1)))
    intro i hi
    rw [map_mul, map_pow]
    calc p (algebraMap F E (f.coeff i)) * p y ^ i ≤ 1 * p y ^ i := mul_le_mul_of_nonneg_right (hcon _) zero_le'
      _ = p y ^ i := one_mul _
      _ < p y ^ f.natDegree := pow_lt_pow_right₀ hy1 (Finset.mem_range.1 hi)
  have hs : ∑ i ∈ Finset.range f.natDegree, algebraMap F E (f.coeff i) * y ^ i =
      -(y ^ f.natDegree) := by linear_combination hfy
  rw [hs, Valuation.map_neg, map_pow] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory.Nef.PlaceResiduePowerBound

namespace GlobalTheory.Nef

open WithZero

theorem place_res_exists_pow : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E],
    (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p,
      ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧
        ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  intro k F E _ _ _ _ _ _ _ _
  refine ⟨?_, fun ρ hρ p => ?_⟩
  · have hex : ∀ p : Place k E, ∃ q : Place k F,
        ∀ x, p.1 (algebraMap F E x) ≤ 1 ↔ q.1 x ≤ 1 := by
      intro p
      obtain ⟨a, ha⟩ := PlaceResiduePowerBound.exists_one_lt (F := F) p.1 p.2.1
      obtain ⟨q, hq, e, he, hpow⟩ := PlaceResiduePowerBound.root (p.1.comap (algebraMap F E)) ⟨a, ha⟩
      refine ⟨⟨q, hq, fun c hc => ?_⟩, fun x => ?_⟩
      · apply PlaceResiduePowerBound.pow_inj he.ne'
        rw [← hpow, Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, p.2.2 c hc, one_pow]
      · have h := hpow x
        rw [Valuation.comap_apply] at h
        rw [h, PlaceResiduePowerBound.pow_le_one_iff' he.ne']
    choose ρ hρ using hex
    exact ⟨ρ, hρ⟩
  · obtain ⟨e, he, hpow⟩ :=
      PlaceResiduePowerBound.pow_of_iff (p.1.comap (algebraMap F E)) (ρ p).1 (ρ p).2.1 (fun x => hρ p x)
    refine ⟨e, he, fun x => hpow x, fun x => ?_⟩
    have h : p.1 (algebraMap F E x) = (ρ p).1 x ^ e := hpow x
    unfold ord
    rw [h, log_pow, nsmul_eq_mul]
    ring

end GlobalTheory.Nef
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open IntermediateField

theorem finiteDimensional_adjoin_of_trdeg_le_one {k F : Type} [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F ≤ 1) (x : F) (hx : Transcendental k x) :
    FiniteDimensional k⟮x⟯ F := by
  have hind : AlgebraicIndependent k (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hb : IsTranscendenceBasis k (fun _ : Unit => x) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg : Algebra.IsAlgebraic k⟮x⟯ F := by
    have := hb.isAlgebraic_field
    rwa [Set.range_const] at this
  have : Algebra.EssFiniteType k⟮x⟯ F := Algebra.EssFiniteType.of_comp k k⟮x⟯ F
  obtain ⟨S, hS⟩ := IntermediateField.fg_top_iff.mpr this
  have hfin : FiniteDimensional k⟮x⟯ (adjoin k⟮x⟯ (S : Set F)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [hS] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := k⟮x⟯) (E := F)).toLinearEquiv

theorem essFiniteType_trdeg_of_isFF {k F : Type} [Field k] [Field F] [Algebra k F] (h : IsFF k F) :
    Algebra.EssFiniteType k F ∧ Algebra.trdeg k F ≤ 1 := by
  obtain ⟨t, ht, hfin⟩ := h
  have h1 : Algebra.EssFiniteType k k⟮t⟯ :=
    IntermediateField.essFiniteType_iff.mpr ⟨{t}, by simp⟩
  refine ⟨Algebra.EssFiniteType.comp k k⟮t⟯ F, ?_⟩
  open IntermediateField.algebraAdjoinAdjoin in
  have : Algebra.IsAlgebraic (Algebra.adjoin k {t}) F := Algebra.IsAlgebraic.trans _ k⟮t⟯ _
  have hind : AlgebraicIndependent k (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hb : IsTranscendenceBasis k (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_iff_isAlgebraic.mpr (by rwa [Set.range_const])
  rw [← hb.cardinalMk_eq_trdeg]
  simp

theorem isFF_main : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F →
    (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧
    ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  intro k F _ _ _ h
  obtain ⟨hfg, htr⟩ := essFiniteType_trdeg_of_isFF h
  refine ⟨fun x hx => finiteDimensional_adjoin_of_trdeg_le_one htr x hx, ?_⟩
  intro E _ _ _ _ _
  have hfgE : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k F E
  have h0 : Algebra.trdeg F E = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have htrE : Algebra.trdeg k E ≤ 1 := by
    rw [← trdeg_add_eq k F, h0, add_zero]; exact htr
  obtain ⟨t, ht, _⟩ := h
  have ht' : Transcendental k (algebraMap F E t) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr ht
  exact ⟨algebraMap F E t, ht', finiteDimensional_adjoin_of_trdeg_le_one htrE _ ht'⟩

end GlobalTheory.Nef
end
