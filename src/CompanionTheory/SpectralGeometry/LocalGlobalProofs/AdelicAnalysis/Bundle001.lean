module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.QuadricCount

open ComplexConjugate

variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def quadForm (B : Matrix ι ι k) (x : ι → k) : k :=
  (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x))

theorem quadForm_add (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k} (hB : B.IsSymm) (y z : ι → k) :
    quadForm B (y + z) = quadForm B y + quadForm B z + y ⬝ᵥ (B *ᵥ z) := by
  have hs : z ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  unfold quadForm
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hs]
  field_simp
  ring

theorem sum_char_dot (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {w : ι → k} (hw : w ≠ 0) :
    ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨c, hc⟩ := (AddChar.ne_one_iff).mp hψ
  have hi' : w i ≠ 0 := hi
  have he : (Pi.single i (c / w i) : ι → k) ⬝ᵥ w = c := by
    rw [single_dotProduct]
    field_simp
  have hS : ψ c * ∑ y : ι → k, ψ (y ⬝ᵥ w) = ∑ y : ι → k, ψ (y ⬝ᵥ w) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (Pi.single i (c / w i) : ι → k)) _ _ ?_
    intro x
    rw [Equiv.coe_addRight, add_dotProduct, he, AddChar.map_add_eq_mul, mul_comm]
  have h0 : (ψ c - 1) * ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by
    rw [sub_mul, hS, one_mul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

theorem gauss_mul_conj (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {t : k} (ht : t ≠ 0) :
    (∑ x, ψ (t * quadForm B x)) * conj (∑ x, ψ (t * quadForm B x)) =
      (Fintype.card k : ℂ) ^ Fintype.card ι := by
  classical
  have inner : ∀ z : ι → k, ∑ y : ι → k, ψ (t * (y ⬝ᵥ (B *ᵥ z))) =
      if z = 0 then (Fintype.card k : ℂ) ^ Fintype.card ι else 0 := by
    intro z
    split_ifs with hz
    · subst hz
      simp
    · have hw : t • (B *ᵥ z) ≠ 0 := by
        intro h
        have h' : B *ᵥ z = 0 := (smul_eq_zero.mp h).resolve_left ht
        exact hz (Matrix.eq_zero_of_mulVec_eq_zero hdet h')
      have := sum_char_dot ψ hψ hw
      simpa [dotProduct_smul, smul_eq_mul] using this
  have step : ∀ y : ι → k, ∑ x, ψ (t * quadForm B x) * conj (ψ (t * quadForm B y)) =
      ∑ z, ψ (t * quadForm B z) * ψ (t * (y ⬝ᵥ (B *ᵥ z))) := by
    intro y
    refine (Fintype.sum_equiv (Equiv.addLeft y) _ _ ?_).symm
    intro z
    rw [Equiv.coe_addLeft, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, quadForm_add h2 hB]
    congr 1
    ring

  rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, inner]
  simp [quadForm]

theorem norm_gauss (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ} (hM : Fintype.card ι = 2 * M) {t : k}
    (ht : t ≠ 0) : ‖∑ x, ψ (t * quadForm B x)‖ = (Fintype.card k : ℝ) ^ M := by
  have h := gauss_mul_conj ψ hψ h2 hB hdet ht
  rw [Complex.mul_conj', hM] at h
  have h' : ‖∑ x, ψ (t * quadForm B x)‖ ^ 2 = ((Fintype.card k : ℝ) ^ M) ^ 2 := by
    rw [← pow_mul, mul_comm M 2]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'

theorem count_mul_card (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (B : Matrix ι ι k) (s : k) :
    (Nat.card {x : ι → k // quadForm B x = s} : ℂ) * (Fintype.card k : ℂ) =
      ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
  classical
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have h1 : ∀ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) =
      if quadForm B x = s then (Fintype.card k : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_mulShift _ hprim]
    simp [sub_eq_zero]
  have h2 : ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) =
      ∑ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h2]
  simp_rw [h1]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_eq_mul]

theorem card_quadric_even (k : Type) [Field k] [Fintype k] (hchar : ringChar k ≠ 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  have hbound : ‖∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    have hterm : ∀ t ∈ Finset.univ.erase (0 : k),
        ‖ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤ (Fintype.card k : ℝ) ^ M := by
      intro t ht
      rw [norm_mul, AddChar.norm_apply, one_mul,
        norm_gauss ψ hψ1 h2 hB hdet hM (Finset.ne_of_mem_erase ht)]
    have := norm_sum_le_of_le _ hterm
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
    simp
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) =
      ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal]
    exact hbound
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  rw [hfac, abs_mul, abs_of_pos hq] at habs
  have hqM : (0 : ℝ) ≤ (Fintype.card k : ℝ) ^ M := by positivity
  have hfin : |(N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| * (Fintype.card k : ℝ) ≤
      (Fintype.card k : ℝ) ^ M * (Fintype.card k : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_right hfin hq

theorem quadric_count_even : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M :=
  fun k _ _ h ι _ _ M hM hM1 B hB hd s => card_quadric_even k h ι M hM hM1 B hB hd s

end GlobalTheory.CompanionTheory.SW.QuadricCount
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem geom_sum_int_le (D M : ℕ) (hD : 0 < D) (hM : 1 ≤ M) (x₀ C : ℝ) :
    ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * D * M := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-a) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max C 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact le_max_right _ _
  have hCK : C ≤ K := by rw [hK]; exact le_max_left _ _
  refine ⟨K * Real.exp (-a * x₀) / (1 - q), fun r hr => ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, n₀ = ⌈x₀ - Real.log r⌉ := ⟨_, rfl⟩
  have hn₀le : x₀ - Real.log r ≤ n₀ := by rw [hn₀]; exact Int.le_ceil _
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * r ^ (2 * D) * Real.exp (-a * n₀) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.exp_pos (-a * n₀); positivity

  have hsupp : Function.support (fun j : ℤ =>
      (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ))))) ⊆
      Set.range (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro j hj
    have hnot : ¬ ((j : ℝ) + Real.log r < x₀) := by
      intro h
      apply hj
      simp [h]
    have hge : n₀ ≤ j := by
      rw [hn₀]
      apply Int.ceil_le.mpr
      linarith [not_lt.mp hnot]
    refine ⟨(j - n₀).toNat, ?_⟩
    have : (((j - n₀).toNat : ℕ) : ℤ) = j - n₀ := Int.toNat_of_nonneg (by omega)
    simp only [this]
    omega
  have hinj : Function.Injective (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro m n h
    simpa using h
  rw [← hinj.tsum_eq hsupp]

  have hterm : ∀ n : ℕ,
      (if (((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))) ≤
        ENNReal.ofReal (A * q ^ n) := by
    intro n
    split_ifs with h
    · simp
    · rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hr' : r ^ (2 * D) = Real.exp (((2 * D : ℕ) : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr]
      have hq' : q ^ n = Real.exp ((n : ℝ) * (-a)) := by
        rw [hq, Real.exp_nat_mul]
      have key : Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
          Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ))) =
          r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        rw [hr', hq', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ha]
        congr 1
        push_cast
        ring
      have hpos : 0 ≤ r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        have := Real.exp_pos (-a * n₀)
        positivity
      calc C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
            Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))
          = C * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) := by rw [mul_assoc, key]
        _ ≤ K * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) :=
            mul_le_mul_of_nonneg_right hCK hpos
        _ = A * q ^ n := by rw [hA]; ring
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hsum : Summable (fun n : ℕ => A * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left A
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

  have hexp : Real.exp (-a * n₀) ≤ Real.exp (-a * x₀) * r ^ (2 * D * M) := by
    have hr' : r ^ (2 * D * M) = Real.exp (((2 * D * M : ℕ) : ℝ) * Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr]
    rw [hr', ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : (((2 * D * M : ℕ) : ℝ)) = a := by rw [ha]; push_cast; ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_left hn₀le ha0.le]
  have hpow : r ^ (2 * D * (M + 1)) = r ^ (2 * D) * r ^ (2 * D * M) := by
    rw [← pow_add]
    congr 1
    ring
  have hAle : A ≤ K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1)) := by
    rw [hA, hpow]
    calc K * r ^ (2 * D) * Real.exp (-a * n₀)
        ≤ K * r ^ (2 * D) * (Real.exp (-a * x₀) * r ^ (2 * D * M)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K * Real.exp (-a * x₀) * (r ^ (2 * D) * r ^ (2 * D * M)) := by ring
  calc A * (1 - q)⁻¹
      ≤ (K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1))) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right hAle (inv_nonneg.mpr h1q.le)
    _ = K * Real.exp (-a * x₀) / (1 - q) * r ^ (2 * D * (M + 1)) := by
        rw [div_eq_mul_inv]; ring

theorem geom_sum_int :
    ∀ (D M : ℕ), 0 < D → 1 ≤ M → ∀ (x₀ C : ℝ), ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) :=
  fun D M hD hM x₀ C => geom_sum_int_le D M hD hM x₀ C

end GlobalTheory.CompanionTheory.Adelic
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ArtinElem

variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]

noncomputable def coord (e : K ≃+* ∀ m, F m) (m : M) : K →+* F m :=
  (Pi.evalRingHom F m).comp e.toRingHom

noncomputable def liftT (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    TransvectionStruct ι K :=
  ⟨t.i, t.j, t.hij, e.symm (Pi.single m t.c)⟩

lemma coord_symm_single (e : K ≃+* ∀ m, F m) (m m' : M) (c : F m) :
    coord e m' (e.symm (Pi.single m c)) = (Pi.single m c : ∀ m, F m) m' := by
  simp [coord]

lemma mapMatrix_single (f : K →+* K') (a b : ι) (c : K) :
    f.mapMatrix (single a b c) = single a b (f c) := by
  ext x y
  simp only [RingHom.mapMatrix_apply, map_apply, single_apply]
  split_ifs <;> simp

lemma liftT_toMatrix (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (liftT e m t).toMatrix = 1 + single t.i t.j (e.symm (Pi.single m t.c)) := rfl

lemma mapMatrix_liftT_same (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (coord e m).mapMatrix (liftT e m t).toMatrix = t.toMatrix := by
  rw [liftT_toMatrix, map_add (f := _), map_one, mapMatrix_single, coord_symm_single, Pi.single_eq_same]
  rfl

lemma mapMatrix_liftT_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (t : TransvectionStruct ι (F m)) :
    (coord e m').mapMatrix (liftT e m t).toMatrix = 1 := by
  rw [liftT_toMatrix, map_add (f := _), map_one, mapMatrix_single, coord_symm_single,
    Pi.single_eq_of_ne h, single_zero, add_zero]

lemma mapMatrix_prod_same (e : K ≃+* ∀ m, F m) (m : M) (T : List (TransvectionStruct ι (F m))) :
    (coord e m).mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) =
      (T.map TransvectionStruct.toMatrix).prod := by
  induction T with
  | nil => simp
  | cons t T ih => simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_same]

lemma mapMatrix_prod_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (T : List (TransvectionStruct ι (F m))) :
    (coord e m').mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) = 1 := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_ne e h, mul_one]

noncomputable def big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m))) (l : List M) :
    List (TransvectionStruct ι K) :=
  l.flatMap fun m => (T m).map (liftT e m)

lemma mapMatrix_big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m)))
    (m' : M) (l : List M) (hl : l.Nodup) :
    (coord e m').mapMatrix (((big e T l).map TransvectionStruct.toMatrix).prod) =
      if m' ∈ l then ((T m').map TransvectionStruct.toMatrix).prod else 1 := by
  induction l with
  | nil => simp [big]
  | cons m l ih =>
    have ih' := ih (List.nodup_cons.mp hl).2
    have hm : m ∉ l := (List.nodup_cons.mp hl).1
    have hb : big e T (m :: l) = (T m).map (liftT e m) ++ big e T l := by simp [big]
    rw [hb, List.map_append, List.prod_append, map_mul, ih']
    by_cases h : m' = m
    · subst h
      rw [mapMatrix_prod_same]
      simp [hm]
    · rw [mapMatrix_prod_ne e h, one_mul]
      simp [h]

lemma matrix_ext_coord (e : K ≃+* ∀ m, F m) {A B : Matrix ι ι K}
    (h : ∀ m, (coord e m).mapMatrix A = (coord e m).mapMatrix B) : A = B := by
  ext a b
  apply e.injective
  funext m
  have := congrFun (congrFun (h m) a) b
  simpa [coord] using this

theorem factor_of_pi [Fintype M] (e : K ≃+* ∀ m, F m)
    (hF : ∀ (m : M) (A : Matrix ι ι (F m)),
      ∃ (L L' : List (TransvectionStruct ι (F m))) (D : ι → F m),
        A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
          (L'.map TransvectionStruct.toMatrix).prod)
    (A : Matrix ι ι K) :
    ∃ (L L' : List (TransvectionStruct ι K)) (D : ι → K),
      A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
        (L'.map TransvectionStruct.toMatrix).prod := by
  choose L L' D hD using fun m => hF m ((coord e m).mapMatrix A)
  refine ⟨big e L Finset.univ.toList, big e L' Finset.univ.toList,
    fun i => e.symm (fun m => D m i), matrix_ext_coord e fun m => ?_⟩
  have hnd := Finset.nodup_toList (Finset.univ : Finset M)
  have hdiag : (coord e m).mapMatrix (diagonal fun i => e.symm (fun m => D m i)) =
      diagonal (D m) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [coord]
    · simp [hab]
  rw [map_mul, map_mul, mapMatrix_big e L m _ hnd, mapMatrix_big e L' m _ hnd, hdiag]
  simpa using hD m

end GlobalTheory.CompanionTheory.SW.ArtinElem

namespace GlobalTheory.CompanionTheory.SW

theorem artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
    (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K),
      A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  classical
  letI : Fintype (MaximalSpectrum K) := Fintype.ofFinite _
  refine ArtinElem.factor_of_pi (F := fun m : MaximalSpectrum K => K ⧸ m.asIdeal)
    (IsArtinianRing.equivPi K).toRingEquiv (fun m B => ?_) A
  letI : Field (K ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec B

end GlobalTheory.CompanionTheory.SW
end
