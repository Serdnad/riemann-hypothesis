module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle009
public import Mathlib.Data.Rat.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle010
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZero
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Valuation.Integers

@[expose] public section

section

open Filter Topology

theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le : ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  first | exact @GlobalTheory.prod_primesBelow_zeta_two_add_le_two | exact GlobalTheory.prod_primesBelow_zeta_two_add_le_two | (intros; apply GlobalTheory.prod_primesBelow_zeta_two_add_le_two <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le : ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  first | exact @GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | exact GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | (intros; apply GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_dirichletCharacter_parity_mul_ne_one_mul_inv_ne_one : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N → (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := by
  first | exact @GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one | exact GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one | (intros; apply GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem frob_sum_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (ι : Type) (s : Finset ι) (x : ι → L) (hx : ∀ i ∈ s, v (x i) ≤ 1) :
    v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    have hxa : v (x a) ≤ 1 := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, v (x i) ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hS : v (∑ i ∈ s, x i) ≤ 1 := by
      have : (∑ i ∈ s, x i) ∈ v.integer :=
        Subring.sum_mem _ (fun i hi => (Valuation.mem_integer_iff v _).2 (hxs i hi))
      exact (Valuation.mem_integer_iff v _).1 this
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp
      (⟨x a, (Valuation.mem_integer_iff v _).2 hxa⟩ : v.integer)
      ⟨∑ i ∈ s, x i, (Valuation.mem_integer_iff v _).2 hS⟩
    have hr' : (x a + ∑ i ∈ s, x i) ^ p = x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) := by
      have := congrArg (fun z : v.integer => (z : L)) hr
      push_cast at this
      rw [this]; ring
    have hrle : v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ 1 := by
      rw [Valuation.map_mul, Valuation.map_mul]
      have hr1 : v (r : L) ≤ 1 := (Valuation.mem_integer_iff v _).1 r.2
      calc v (x a) * v (∑ i ∈ s, x i) * v (r : L) ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by simp
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr']
    have heq : x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) - (x a ^ p + ∑ i ∈ s, x i ^ p)
        = (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) + ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) := by ring
    rw [heq]
    refine (Valuation.map_add v _ _).trans (max_le ?_ (ih hxs))
    rw [Valuation.map_mul]
    calc v (p : L) * v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ v (p : L) * 1 := by gcongr
      _ = v (p : L) := mul_one _

theorem frob_sum_sub_le' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) →
      v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) :=
  fun L _ v p hp ι s x hx => frob_sum_sub_le L v p hp ι s x hx

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ y β : L, v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.valuation_add_pow_sub_le | exact GlobalTheory.AlmostEt.valuation_add_pow_sub_le | (intros; apply GlobalTheory.AlmostEt.valuation_add_pow_sub_le <;> assumption)
end

section

open scoped NNReal TensorProduct

theorem _root_.GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) → ∀ (g : Ω ≃ₐ[R] Ω) (x : Ω), v (g x) = v x := by
  first | exact @GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | exact GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral | (intros; apply GlobalTheory.valuation_map_algEquiv_eq_of_le_one_iff_isIntegral <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem valuation_one_sub_pow_le {L : Type} [Field L] (v : Valuation L ℝ≥0) (η : L)
    (hη : v η ≤ 1) (n : ℕ) : v (1 - η ^ n) ≤ v (1 - η) := by
  rw [← mul_neg_geom_sum, v.map_mul]
  have hs : v (∑ i ∈ Finset.range n, η ^ i) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [v.map_pow]
    exact pow_le_one₀ (zero_le') hη
  calc v (1 - η) * v (∑ i ∈ Finset.range n, η ^ i) ≤ v (1 - η) * 1 := by gcongr
    _ = v (1 - η) := mul_one _

theorem valuation_sub_one_pow_eq_prime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ ζ : L,
      IsPrimitiveRoot ζ p → v (ζ - 1) ^ (p - 1) = v (p : L) := by
  intro L _ v p hp ζ hζ
  have hone : ∀ η : L, η ^ p = 1 → v η ≤ 1 := by
    intro η hη
    have h1 : v η ^ p = 1 := by rw [← v.map_pow, hη, v.map_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (zero_le') hp.ne_zero).mp h1)
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have hprod := hζ.prod_one_sub_pow_eq_order
  have hterm : ∀ k ∈ Finset.range n, v (1 - ζ ^ (k + 1)) = v (ζ - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Valuation.map_sub_swap v ζ 1]
    have hc : (k + 1).Coprime (n + 1) := by
      have h := Nat.coprime_of_lt_prime (Nat.succ_ne_zero k) (by omega : k + 1 < n + 1) hp
      first | exact h | exact h.symm
    have hprim : IsPrimitiveRoot (ζ ^ (k + 1)) (n + 1) := hζ.pow_of_coprime _ hc
    apply le_antisymm
    · exact valuation_one_sub_pow_le v ζ (hone ζ hζ.pow_eq_one) (k + 1)
    · obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
      calc v (1 - ζ) = v (1 - (ζ ^ (k + 1)) ^ i) := by rw [hi]
        _ ≤ v (1 - ζ ^ (k + 1)) :=
          valuation_one_sub_pow_le v _ (hone _ hprim.pow_eq_one) i
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← hprod, map_prod, Finset.prod_congr rfl hterm, Finset.prod_const,
    Finset.card_range]

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem valuation_nnreal_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    exact le_trans (v.map_add _ _) (max_le ih (by simp))

theorem valuation_nnreal_intCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (z : ℤ) : v (z : L) ≤ 1 := by
  cases z with
  | ofNat n => simpa using valuation_nnreal_natCast_le_one v n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_nnreal_natCast_le_one v (n + 1)

theorem natCast_eq_one_of_coprime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  intro L _ v p l hp hlp
  refine le_antisymm (valuation_nnreal_natCast_le_one v l) ?_
  by_contra hlt
  push_neg at hlt
  have hb : ((Nat.gcd l p : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p := Nat.gcd_eq_gcd_ab l p
  rw [hlp, Nat.cast_one] at hb
  have hL : (1 : L) = (l : L) * (Nat.gcdA l p : L) + (p : L) * (Nat.gcdB l p : L) := by
    have := congrArg (fun z : ℤ => (z : L)) hb
    push_cast at this
    exact this
  have h1 : v (1 : L) < 1 := by
    rw [hL]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdA l p))) hlt
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdB l p))) hp
  simp at h1

end GlobalTheory.AlmostEt
end

section

open scoped Matrix
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.linearIndependent_vecMul_of_span_rat' : ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by
  first | exact @GlobalTheory.linearIndependent_vecMul_of_span_rat | exact GlobalTheory.linearIndependent_vecMul_of_span_rat | (intros; apply GlobalTheory.linearIndependent_vecMul_of_span_rat <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_choose_small_padicVal_ax_induction : ∀ (p : ℕ), p.Prime → ∀ N : ℕ, 2 ≤ N → ∃ j e : ℕ, 0 < j ∧ j < N ∧ ¬ p ^ (e + 1) ∣ N.choose j ∧
  (e : ℚ) / ((N - j : ℕ) : ℚ) + (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p (N - j)) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p N) := by
  first | exact @GlobalTheory.exists_choose_small_valuation_ax | exact GlobalTheory.exists_choose_small_valuation_ax | (intros; apply GlobalTheory.exists_choose_small_valuation_ax; all_goals assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.normCompatible_system_frobenius_eq_zero : ∀ (O H : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [AddCommGroup H] [Module O H] (l : ℕ) [Fact l.Prime], ¬ IsUnit (l : O) → ∀ (q : ℕ) (hq : Nat.Coprime q l), 2 ≤ q → ∀ (M : Submodule O H), M.FG → ∀ (F : H →ₗ[O] H), (∀ x ∈ M, F x ∈ M) → ∀ (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H), (∀ r x, c r x ∈ M) → (∀ r x, F (c r x) = c r (x * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq))) → (∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ => Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), c (r + 1) x') → ∀ r x, c r x = 0 := by
  first | exact @GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | exact GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | (intros; apply GlobalTheory.NormSystemVanishing.normCompatible_eq_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finiteDimensional_fixedField_map_of_finiteIndex' : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G), N.FiniteIndex → (∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E)) → FiniteDimensional F (IntermediateField.fixedField (N.map act)) := by
  first | exact @GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex | exact GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex | (intros; apply GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex <;> assumption)
end
