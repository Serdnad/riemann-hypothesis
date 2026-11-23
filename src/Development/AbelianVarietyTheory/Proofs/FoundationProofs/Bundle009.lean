module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

@[expose] public section

section

open Filter Topology

namespace GlobalTheory

theorem one_div_succ_rpow_one_add_le_telescope {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    1 / (x + 1) ^ (1 + s) ≤ (1 / x ^ s - 1 / (x + 1) ^ s) / s := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < (x + 1) / x := div_pos hx1 hx
  have h1 : 1 - ((x + 1) / x)⁻¹ ≤ Real.log ((x + 1) / x) := Real.one_sub_inv_le_log_of_pos hq
  have h2 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
  have h3 : 1 + s * (1 / (x + 1)) ≤ ((x + 1) / x) ^ s := by
    rw [Real.rpow_def_of_pos hq]
    have h4 := Real.add_one_le_exp (Real.log ((x + 1) / x) * s)
    have h5 : s * (1 / (x + 1)) ≤ Real.log ((x + 1) / x) * s := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (h2 ▸ h1) hs.le
    linarith
  rw [Real.div_rpow hx1.le hx.le] at h3
  rw [Real.rpow_add hx1, Real.rpow_one]
  have hA : 0 < x ^ s := Real.rpow_pos_of_pos hx _
  have hB : 0 < (x + 1) ^ s := Real.rpow_pos_of_pos hx1 _
  generalize x ^ s = A at *
  generalize (x + 1) ^ s = B at *
  rw [le_div_iff₀ hs]
  have h6 : (1 + s * (1 / (x + 1))) / B ≤ B / A / B := by gcongr
  have h7 : B / A / B = 1 / A := by field_simp
  have h8 : (1 + s * (1 / (x + 1))) / B = 1 / B + 1 / ((x + 1) * B) * s := by field_simp
  linarith

theorem sum_range_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s)
      ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := by
  induction k with
  | zero =>
    have : (1 + s) ≠ 0 := by linarith
    simp [Finset.sum_range_succ, Real.zero_rpow this]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Finset.sum_range_succ]
    have h := one_div_succ_rpow_one_add_le_telescope (x := (k : ℝ) + 1) hs (by positivity)
    have e : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 1 + 1 := by push_cast; ring
    have e' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [e, e']
    have : (1 - 1 / ((k : ℝ) + 1 + 1) ^ s) / s = (1 - 1 / ((k : ℝ) + 1) ^ s) / s
        + (1 / ((k : ℝ) + 1) ^ s - 1 / ((k : ℝ) + 1 + 1) ^ s) / s := by ring
    linarith

theorem tsum_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + s) ≤ 1 + 1 / s := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun k => ?_
  calc ∑ n ∈ Finset.range k, 1 / (n : ℝ) ^ (1 + s)
      ≤ ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => by positivity)
    _ ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := sum_range_one_div_rpow_one_add_le hs k
    _ ≤ 1 + 1 / s := by
        have : 0 ≤ 1 / ((k : ℝ) + 1) ^ s := by positivity
        gcongr
        linarith

theorem prod_primesBelow_inv_one_sub_one_div_rpow_le :
    ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  intro s hs N
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  have hE := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) (by simp)
    (fun {m n} _ => by
      simp only [Nat.cast_mul]
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), one_div_mul_one_div])
    hsum.norm N
  have hP : ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹
      = ∏ p ∈ N.primesBelow, ∑' e : ℕ, 1 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hp0 : (0 : ℝ) ≤ p := by linarith
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) := Real.one_lt_rpow hp1 (by linarith)
    rw [← tsum_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 h1)]
    refine tsum_congr fun e => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) e, ← Real.rpow_mul hp0, mul_comm,
      Real.rpow_mul hp0, Real.rpow_natCast, one_div_pow]
  rw [hP, hE]
  exact (Summable.tsum_subtype_le _ _ (fun n => by positivity) hsum).trans
    (tsum_one_div_rpow_one_add_le hs)

end GlobalTheory
end

section

namespace GlobalTheory.JointEigenvectorsIndependent

theorem linearIndependent_of_joint_eigenvectors {ι α M : Type} [AddCommGroup M] [Module ℂ M]
    (f : ι → M) (χ : ι → α → ℂ) (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ)
    (hop : ∀ (a : α) (i : ι), (op a : M → M) (f i) = χ i a • f i)
    (hf : ∀ i : ι, f i ≠ (0 : M)) : LinearIndependent ℂ f := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert j s hj ih =>
    intro g hg
    rw [Finset.sum_insert hj] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨a, ha⟩ : ∃ a, χ i a ≠ χ j a := Function.ne_iff.mp (fun h => hij (hχ h))
      have h1 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ k a) • f k = 0 := by
        have h := congrArg (op a) hg

        rw [map_add (f := _), map_sum, map_zero, map_smul, hop, smul_smul] at h
        simpa only [map_smul, hop, smul_smul] using h
      have h2 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ j a) • f k = 0 := by
        have h := congrArg (fun x => χ j a • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (χ j a)] using h
      have h3 : ∑ k ∈ s, (g k * (χ k a - χ j a)) • f k = 0 := by
        have h4 : ∑ k ∈ s, (g k * χ k a) • f k = ∑ k ∈ s, (g k * χ j a) • f k :=
          add_left_cancel (h1.trans h2.symm)
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, h4, sub_self]
      have h5 := ih (fun k => g k * (χ k a - χ j a)) h3 i hi
      exact (mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr ha)
    have hsum : ∑ k ∈ s, g k • f k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hsum, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hf _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependent
end

section

namespace GlobalTheory

theorem exists_char_parity_mul_ne_one_mul_inv_ne_one : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N → (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := by
  intro N r χ sg hN hr hr7 hrN hsg
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hrle : r ≤ N := Nat.le_of_dvd hN hrN

  haveI : Fact (2 < N) := ⟨by omega⟩
  have hm1 : (-1 : ZMod N) ≠ 1 := ZMod.neg_one_ne_one
  obtain ⟨θ₁, hθ₁⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hm1
  have hsq : ∀ ψ : DirichletCharacter ℂ N, ψ (-1) * ψ (-1) = 1 := by
    intro ψ
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hθ₁' : θ₁ (-1) = -1 := by
    rcases mul_self_eq_one_iff.mp (hsq θ₁) with h | h
    · exact absurd h hθ₁
    · exact h

  have h16 : (16 : ZMod r) ≠ 1 := by
    intro h
    have h15 : ((15 : ℕ) : ZMod r) = 0 := by
      have : (16 : ZMod r) - 1 = 0 := by rw [h]; ring
      have e : ((15 : ℕ) : ZMod r) = (16 : ZMod r) - 1 := by push_cast; ring
      rw [e, this]
    rw [ZMod.natCast_eq_zero_iff] at h15
    have h35 : r ∣ 3 * 5 := by norm_num; exact h15
    rcases (Nat.Prime.dvd_mul hr).mp h35 with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h5; omega
  obtain ⟨κ, hκ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h16
  set ψ : DirichletCharacter ℂ N := DirichletCharacter.changeLevel hrN κ with hψ
  have hη4 : ψ ^ 4 ≠ 1 := by
    intro h
    have h' : DirichletCharacter.changeLevel hrN (κ ^ 4) = DirichletCharacter.changeLevel hrN 1 := by
      rw [map_pow, map_one]; exact h
    have hk := DirichletCharacter.changeLevel_injective hrN h'
    apply hκ
    have : (κ ^ 4) 2 = (1 : DirichletCharacter ℂ r) 2 := by rw [hk]
    have hu : IsUnit (2 : ZMod r) := by
      have : (2 : ZMod r) = ((2 : ℕ) : ZMod r) := by norm_cast
      rw [this, ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_primes Nat.prime_two hr).mpr (by omega)
    rw [MulChar.one_apply hu, MulChar.pow_apply' _ (by norm_num)] at this
    have e : (16 : ZMod r) = 2 ^ 4 := by norm_num
    rw [e, map_pow]; exact this
  set η : DirichletCharacter ℂ N := ψ ^ 2 with hηdef
  have hηsq : η ^ 2 ≠ 1 := by
    rw [hηdef, ← pow_mul]; exact hη4
  have hη1 : η ≠ 1 := by
    intro h; apply hηsq; rw [h, one_pow]
  have hη2 : η (-1) = 1 := by
    rw [hηdef, pow_two, MulChar.mul_apply, hsq]
  have hη2' : (η ^ 2) (-1) = 1 := by
    rw [pow_two, MulChar.mul_apply, hη2, mul_one]

  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : DirichletCharacter ℂ N, θ₀ (-1) = sg := by
    rcases hsg with h | h
    · exact ⟨1, by rw [h]; exact MulChar.one_apply (isUnit_one.neg)⟩
    · exact ⟨θ₁, by rw [h, hθ₁']⟩

  have hab : θ₀ ≠ θ₀ * η := by
    intro h; apply hη1; exact left_eq_mul.mp h
  have hbc : θ₀ * η ≠ θ₀ * η ^ 2 := by
    intro h; apply hη1
    have h' := mul_left_cancel h
    rw [pow_two] at h'
    exact left_eq_mul.mp h'
  have hac : θ₀ ≠ θ₀ * η ^ 2 := by
    intro h; apply hηsq; exact left_eq_mul.mp h
  have key : ∀ θ : DirichletCharacter ℂ N, ¬ (θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1) → θ = χ⁻¹ ∨ θ = χ := by
    intro θ h
    by_cases h1 : θ * χ = 1
    · exact Or.inl (eq_inv_of_mul_eq_one_left h1)
    · have h2 : θ * χ⁻¹ = 1 := by
        by_contra h2; exact h ⟨h1, h2⟩
      right
      have := eq_inv_of_mul_eq_one_left h2
      rwa [inv_inv] at this
  by_contra hno
  push_neg at hno
  have ha := key θ₀ (fun h => by have := hno θ₀ hθ₀ h.1; exact h.2 this)
  have hb := key (θ₀ * η) (fun h => by
    have := hno (θ₀ * η) (by rw [MulChar.mul_apply, hθ₀, hη2, mul_one]) h.1; exact h.2 this)
  have hc := key (θ₀ * η ^ 2) (fun h => by
    have := hno (θ₀ * η ^ 2) (by rw [MulChar.mul_apply, hθ₀, hη2', mul_one]) h.1; exact h.2 this)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    first
    | exact hab (ha.trans hb.symm)
    | exact hac (ha.trans hc.symm)
    | exact hbc (hb.trans hc.symm)

end GlobalTheory
end

section

namespace GlobalTheory.AlmostEt

open scoped NNReal

theorem valuation_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) :
    v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

theorem valuation_add_pow_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ)
    (hp : p.Prime) (y β : L) :
    v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have key : (y + β) ^ (q + 1) - y ^ (q + 1) - β ^ (q + 1) =
      ∑ i ∈ Finset.range q, y ^ (i + 1) * β ^ (q + 1 - (i + 1)) * ((q + 1).choose (i + 1) : L) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp
  rw [key]
  apply Valuation.map_sum_le
  intro i hi
  have hi : i < q := Finset.mem_range.mp hi
  set M := max (v y) (v β)
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
  have hsub : q + 1 - (i + 1) = (q - (i + 1)) + 1 := by omega
  rw [hk, hsub]
  push_cast
  simp only [map_mul, map_pow]
  have h1 : v y ^ (i + 1) ≤ M ^ (i + 1) := pow_le_pow_left₀ (by positivity) (le_max_left _ _) _
  have h2 : v β ^ (q - (i + 1)) ≤ M ^ (q - (i + 1)) := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  have h3 : v (k : L) ≤ 1 := valuation_natCast_le_one v k
  have hM : M ^ (i + 1) * M ^ (q - (i + 1)) = M ^ q := by
    rw [← pow_add]; congr 1; omega
  rw [pow_succ (v β)]
  calc _ ≤ M ^ (i + 1) * (M ^ (q - (i + 1)) * v β) * (v ((q : L) + 1) * 1) := by gcongr
    _ = _ := by simp only [Nat.add_sub_cancel, ← hM]; ring

end GlobalTheory.AlmostEt
end

section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_map_algEquiv_eq_of_le_one_iff_isIntegral (R Ω : Type) [CommRing R] [Nontrivial R]
    [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω]
    (hinj : Function.Injective (algebraMap R Ω)) (v : Valuation Ω ℝ≥0)
    (hv : ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) (g : Ω ≃ₐ[R] Ω) (x : Ω) : v (g x) = v x := by
  have hle : ∀ a b : Ω, v (g a) ≤ v (g b) ↔ v a ≤ v b := by
    intro a b
    by_cases hb : b = 0
    · subst hb
      simp
    · have hgb : g b ≠ 0 := by simpa using hb
      have hvb : 0 < v b := by simpa [pos_iff_ne_zero] using hb
      have hvgb : 0 < v (g b) := by simpa [pos_iff_ne_zero] using hgb
      have h1 : v (a / b) ≤ 1 ↔ v a ≤ v b := by rw [map_div₀, div_le_one hvb]
      have h2 : v (g (a / b)) ≤ 1 ↔ v (g a) ≤ v (g b) := by
        rw [map_div₀ g, map_div₀, div_le_one hvgb]
      rw [← h1, ← h2, hv, hv, isIntegral_algEquiv]
  have hlt : ∀ a b : Ω, v (g a) < v (g b) ↔ v a < v b := by
    intro a b
    rw [← not_le, ← not_le, hle]
  obtain ⟨k, l, hkl, heq⟩ : ∃ k l : ℕ, k < l ∧ (g ^ k) x = (g ^ l) x := by
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) x
    have hmap : p.map (algebraMap R Ω) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff hinj]
    have hsub : Set.range (fun k : ℕ => (g ^ k) x) ⊆ p.rootSet Ω := by
      rintro _ ⟨k, rfl⟩
      rw [Polynomial.mem_rootSet']
      refine ⟨hmap, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp [hpx]
    have hfin := (Polynomial.rootSet_finite p Ω).subset hsub
    have hni : ¬ Function.Injective (fun k : ℕ => (g ^ k) x) := fun hi =>
      Set.infinite_range_of_injective hi hfin
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  have hstep : ∀ k : ℕ, (g ^ (k + 1)) x = g ((g ^ k) x) := by
    intro k
    rw [pow_succ', AlgEquiv.mul_apply]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hanti : StrictAnti (fun n : ℕ => v ((g ^ n) x)) := strictAnti_nat_of_succ_lt hs
    have := hanti hkl
    simp only [heq] at this
    exact lt_irrefl _ this
  · have hs : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hmono : StrictMono (fun n : ℕ => v ((g ^ n) x)) := strictMono_nat_of_lt_succ hs
    have := hmono hkl
    simp only [heq] at this
    exact lt_irrefl _ this

end GlobalTheory
end

section

open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem linearIndependent_vecMul_of_span_rat :
    ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by
  intro E _ _ R _ _ _ τ hτ hrk n ι _ u hcard hu g
  classical
  have hq : ∀ c : ℚ, τ (algebraMap ℚ E c) = algebraMap ℝ R (algebraMap ℚ ℝ c) := by
    intro c
    have : τ.comp (algebraMap ℚ E) = (algebraMap ℝ R).comp (algebraMap ℚ ℝ) :=
      Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* R => f c) this
  set V : Submodule ℝ (Fin n → R) :=
    Submodule.span ℝ (Set.range fun k => (fun i => τ (u k i))) with hV
  have h1 : ∀ x : Fin n → E, (fun i => τ (x i)) ∈ V := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range u) := by rw [hu]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero =>
      have : (fun i => τ ((0 : Fin n → E) i)) = 0 := by ext i; simp
      rw [this]; exact V.zero_mem
    | add x y _ _ hx hy =>
      have : (fun i => τ ((x + y) i)) = (fun i => τ (x i)) + (fun i => τ (y i)) := by
        ext i; simp
      rw [this]; exact V.add_mem hx hy
    | smul c x _ hx =>
      have : (fun i => τ ((c • x) i)) = (algebraMap ℚ ℝ c) • (fun i => τ (x i)) := by
        ext i
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, hq]
      rw [this]; exact V.smul_mem _ hx
  have h2 : ∀ (i : Fin n) (r : R), Pi.single i r ∈ V := by
    intro i r
    have hle : Submodule.span ℝ (Set.range τ) ≤
        V.comap (LinearMap.single ℝ (fun _ : Fin n => R) i) := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      have := h1 (Pi.single i e)
      have h' : (fun j => τ ((Pi.single i e : Fin n → E) j)) = Pi.single i (τ e) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      rw [h'] at this
      exact this
    have hr : r ∈ Submodule.span ℝ (Set.range τ) := by rw [hτ]; trivial
    exact hle hr
  have h3 : ∀ y : Fin n → R, y ∈ V := by
    intro y
    rw [← Finset.univ_sum_single y]
    exact V.sum_mem fun i _ => h2 i _
  let φ : (Fin n → R) →ₗ[ℝ] (Fin n → R) :=
    { toFun := fun v => v ᵥ* g.1
      map_add' := fun v w => Matrix.add_vecMul _ _ _
      map_smul' := fun c v => Matrix.smul_vecMul _ _ _ }
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro y _
    have hy : y = φ (y ᵥ* (g⁻¹).1) := by
      simp [φ, Matrix.vecMul_vecMul]
    have hm : φ (y ᵥ* (g⁻¹).1) ∈ V.map φ := Submodule.mem_map_of_mem (h3 _)
    rw [hV, Submodule.map_span, ← Set.range_comp] at hm
    rw [hy]
    exact hm
  · rw [hcard, Module.finrank_pi_fintype, ← hrk]
    simp [mul_comm]

end GlobalTheory
end
