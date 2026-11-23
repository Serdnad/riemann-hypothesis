module

public import Formalism.JacquetSubsetSums.JacquetSubsetSum
public import Mathlib.LinearAlgebra.Vandermonde
public import Formalism.PairingDivisors.StatementN
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle016
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle002
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.Primorial
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.Algebra.BigOperators.Fin
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

section

open Finset

namespace GlobalTheory

lemma packetSum_vdm_eq_det {r : ℕ} (β : Fin r → ℂ) :
    Formalism.PacketSums.vdm β = (∏ i : Fin r, ∏ _j ∈ Ioi i, (-1 : ℂ)) * (Matrix.vandermonde β).det := by
  rw [Matrix.det_vandermonde, ← Finset.prod_mul_distrib]
  unfold Formalism.PacketSums.vdm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  have : Finset.univ.filter (fun j => i < j) = Ioi i := by ext; simp
  rw [this]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

lemma packetSum_vdm_perm {r : ℕ} (α : Fin r → ℂ) (σ : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.vdm (fun i => α (σ i)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * Formalism.PacketSums.vdm α := by
  rw [packetSum_vdm_eq_det, packetSum_vdm_eq_det]
  have : Matrix.vandermonde (fun i => α (σ i)) = (Matrix.vandermonde α).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [this, Matrix.det_permute]
  ring

lemma packetSum_sign_cast_ne_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma packetSum_numK_perm {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK]
    (μ : Fin r → ℤ) (α : Fin r → ℂ) (y : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) =
      ((Equiv.Perm.sign y : ℤ) : ℂ) * ∑ w : WK,
        ((Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) : ℤ) : ℂ) *
          ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
  unfold Formalism.PacketSums.numK
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hp : ∏ i, α (y⁻¹ i) ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i) =
      ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
    rw [← Equiv.prod_comp y]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]
  rw [hp, ← mul_assoc]
  congr 1
  have hs : Equiv.Perm.sign (w : Equiv.Perm (Fin r)) =
      Equiv.Perm.sign y * Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [hs]; push_cast; ring

theorem packetSum : Formalism.PacketSums.PacketSum := by
  intro r WK _ T hbij μ α _ _
  set f : Equiv.Perm (Fin r) → ℂ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, α j ^ μ (σ⁻¹ j) with hf
  have hterm : ∀ y : Equiv.Perm (Fin r),
      Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α (y⁻¹ i)) =
        (∑ w : WK, f (y⁻¹ * (w : Equiv.Perm (Fin r)))) / Formalism.PacketSums.vdm α := by
    intro y
    rw [packetSum_numK_perm, packetSum_vdm_perm α y⁻¹, Equiv.Perm.sign_inv,
      mul_div_mul_left _ _ (packetSum_sign_cast_ne_zero y)]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_coe_sort T]
  rw [← Fintype.sum_bijective _ hbij (fun p : WK × T => f ((p.2 : Equiv.Perm (Fin r))⁻¹ * p.1)) f
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

end GlobalTheory
end

section

open Finset

namespace GlobalTheory

theorem ceSum_val_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (X : ℕ) :
    ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l ≤ Real.log X := by
  have h1 : ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l
      = ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def X (hS l hl), Nat.padicValNat_def]
  rw [h1, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hsub : S ⊆ S ∪ X.factorization.support := Finset.subset_union_left
  calc ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l
      ≤ ∑ l ∈ S ∪ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun l hl _ => ?_
        rcases Finset.mem_union.1 hl with h | h
        · exact mul_nonneg (Nat.cast_nonneg _)
            (Real.log_nonneg (by exact_mod_cast (hS l h).one_lt.le))
        · have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using h)
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    _ = ∑ l ∈ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.subset_union_right fun l _ hl => ?_).symm
        rw [Finsupp.notMem_support_iff.1 hl]
        simp

theorem ceSum_small_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (if l ≤ n then Real.log l else 0) ≤ n * Real.log 4 := by
  rw [← Finset.sum_filter]
  calc ∑ l ∈ S.filter (· ≤ n), Real.log (l : ℝ)
      ≤ ∑ l ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (l : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l hl _ => ?_
        · intro l hl
          rcases Finset.mem_filter.1 hl with ⟨hlS, hln⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hS l hlS⟩
        · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hl).2.one_lt.le)
    _ = Real.log (primorial n : ℝ) := by
        rw [primorial, Nat.cast_prod, Real.log_prod]
        intro l hl
        exact_mod_cast (Finset.mem_filter.1 hl).2.ne_zero
    _ ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log (by exact_mod_cast primorial_pos n)
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]

end GlobalTheory

namespace GlobalTheory


open Formalism.PairingDivisionLocalBalance in
theorem ceSum_term_le (f X l : ℕ) (hX : X ≠ 0) (hp : l.Prime) :
    ((f * padicValNat l 2 + mE l X : ℕ) : ℝ) * Real.log l ≤
      (padicValNat l X : ℝ) * Real.log l + (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
        + (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
        + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hv : (0 : ℝ) ≤ padicValNat l X := Nat.cast_nonneg _
  have hvl : 0 ≤ (padicValNat l X : ℝ) * Real.log l := mul_nonneg hv hlog
  have hB : 0 ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0) := by
    split_ifs
    · exact Real.log_nonneg (by have : (0 : ℝ) ≤ X := Nat.cast_nonneg _; linarith)
    · exact le_rfl
  have hC : 0 ≤ (if l ≤ X / 2 + 1 then Real.log l else 0) := by
    split_ifs
    · exact hlog
    · exact le_rfl
  by_cases h2 : l = 2
  · subst h2
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hm : mE 2 X = 2 + padicValNat 2 X := by simp [mE]
    have h22 : padicValNat 2 2 = 1 := by
      rw [Nat.padicValNat_def, Nat.multiplicity_self (by norm_num : 1 < 2)]
    have e : ((f * padicValNat 2 2 + mE 2 X : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ)
        = (padicValNat 2 X : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((f : ℝ) + 2) * Real.log 2 := by
      rw [hm, h22]; push_cast; ring
    rw [if_pos rfl, e]
    linarith
  · have hA : (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0) = 0 := if_neg h2
    have hv2 : padicValNat l 2 = 0 := by
      rw [Nat.padicValNat_def]
      apply multiplicity_eq_zero_of_not_dvd
      intro h
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    rw [hA, hv2]
    by_cases hd : (l - 1) ∣ X
    · have hm : mE l X = 1 + padicValNat l X := by simp [mE, h2, hd]
      rw [hm]
      push_cast
      have key : Real.log (l : ℝ) ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
          + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
        by_cases hXl : l = X + 1
        · rw [if_pos hXl]
          have : (l : ℝ) = (X : ℝ) + 1 := by exact_mod_cast hXl
          have e : Real.log (l : ℝ) = Real.log ((X : ℝ) + 1) := by rw [this]
          linarith
        · rw [if_neg hXl]
          have hl3 : 3 ≤ l := by have := hp.two_le; omega
          obtain ⟨k, hk⟩ := hd
          have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hX hk
          have hk1 : k ≠ 1 := by rintro rfl; apply hXl; omega
          have hk2 : (l - 1) * 2 ≤ (l - 1) * k := Nat.mul_le_mul_left _ (by omega)
          have hle : l - 1 ≤ X / 2 := by
            rw [Nat.le_div_iff_mul_le (by norm_num)]
            rw [hk]; exact hk2
          rw [if_pos (by omega)]
          linarith
      nlinarith
    · have hm : mE l X = 0 := by simp [mE, h2, hd]
      rw [hm]
      simp only [mul_zero, add_zero, Nat.cast_zero, zero_mul]
      linarith

end GlobalTheory

namespace GlobalTheory

theorem dividedPowerValuations_cESum : Formalism.PairingDivisionLocalBalance.CESum := by
  intro f X S hX hfX hS
  have hX0 : X ≠ 0 := by omega
  have hsum := Finset.sum_le_sum fun l hl => ceSum_term_le f X l hX0 (hS l hl)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hv := ceSum_val_le S hS X
  have hs := ceSum_small_le S hS (X / 2 + 1)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hXr : (16 : ℝ) ≤ X := by exact_mod_cast hX
  have hL0 : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hA : ∑ l ∈ S, (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
      ≤ ((f : ℝ) + 2) * Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hB : ∑ l ∈ S, (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
      ≤ Real.log ((X : ℝ) + 1) := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hL0
  have hlogX : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL4 : 4 * Real.log 2 ≤ Real.log ((X : ℝ) + 1) := by
    have : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; norm_num
  have hn : (((X / 2 + 1 : ℕ)) : ℝ) * 2 ≤ X + 2 := by
    have : (X / 2 + 1) * 2 ≤ X + 2 := by omega
    exact_mod_cast this
  have hf : (f : ℝ) * 2 ≤ X := by exact_mod_cast (by omega : f * 2 ≤ X)
  rw [h4] at hs
  have p1 : 0 ≤ ((X : ℝ) - 2 * f) * Real.log 2 := mul_nonneg (by linarith) hlog2
  have p2 : 0 ≤ ((X : ℝ) + 2 - ((X / 2 + 1 : ℕ) : ℝ) * 2) * Real.log 2 :=
    mul_nonneg (by linarith) hlog2
  have p3 : 0 ≤ ((X : ℝ) - 2) * (Real.log ((X : ℝ) + 1) - 4 * Real.log 2) :=
    mul_nonneg (by linarith) (by linarith)
  have p4 : 0 ≤ ((X : ℝ) - 16) * Real.log 2 := mul_nonneg (by linarith) hlog2
  nlinarith

end GlobalTheory
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] (v : Valuation L ℝ≥0) {p : ℕ} {θ : ℝ≥0}

theorem approxRoot_pow_le (hθ : θ ≤ 1) {u w : L} (h : v (u - w ^ p) ≤ θ * v u) :
    v (w ^ p) ≤ v u := by
  have e : w ^ p = u - (u - w ^ p) := by ring
  rw [e]
  refine (Valuation.map_sub v _ _).trans (max_le le_rfl (h.trans ?_))
  simpa using mul_le_mul' hθ (le_refl (v u))

theorem approxRoot_mul (hθ : θ ≤ 1) {u u' w w' : L} (h : v (u - w ^ p) ≤ θ * v u)
    (h' : v (u' - w' ^ p) ≤ θ * v u') : v (u * u' - (w * w') ^ p) ≤ θ * v (u * u') := by
  have e : u * u' - (w * w') ^ p = u * (u' - w' ^ p) + w' ^ p * (u - w ^ p) := by ring
  rw [e, map_mul]
  refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    calc v u * v (u' - w' ^ p) ≤ v u * (θ * v u') := mul_le_mul' le_rfl h'
      _ = θ * (v u * v u') := by ring
  · rw [map_mul]
    calc v (w' ^ p) * v (u - w ^ p) ≤ v u' * (θ * v u) :=
          mul_le_mul' (approxRoot_pow_le v hθ h') h
      _ = θ * (v u * v u') := by ring

theorem approxRoot_inv (hθ : θ < 1) {u w : L} (hu : u ≠ 0) (h : v (u - w ^ p) ≤ θ * v u) :
    v (u⁻¹ - (w⁻¹) ^ p) ≤ θ * v u⁻¹ := by
  have hvu : 0 < v u := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff v).mpr hu
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact h.trans_lt (by simpa using mul_lt_mul_of_pos_right hθ hvu)
  have heq : v (w ^ p) = v u := Valuation.map_eq_of_sub_lt v hlt
  have hw : w ^ p ≠ 0 := by
    intro h0; rw [h0, map_zero] at heq; exact hvu.ne' heq.symm
  have e : u⁻¹ - (w⁻¹) ^ p = (w ^ p - u) * (u⁻¹ * (w ^ p)⁻¹) := by
    rw [inv_pow]; field_simp
  rw [e, map_mul, map_mul, map_inv₀, map_inv₀, heq, Valuation.map_sub_swap]
  calc v (u - w ^ p) * ((v u)⁻¹ * (v u)⁻¹) ≤ θ * v u * ((v u)⁻¹ * (v u)⁻¹) :=
        mul_le_mul' h le_rfl
    _ = θ * (v u)⁻¹ := by field_simp

theorem approxRoot_closed : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  intro L _ v p F θ hθ u u' ⟨w, hwF, hw⟩ ⟨w', hw'F, hw'⟩
  have hθ1 : θ ≤ 1 := hθ.le
  refine ⟨⟨w * w', F.mul_mem hwF hw'F, approxRoot_mul v hθ1 hw hw'⟩, fun hu' => ?_, fun k => ?_⟩
  · refine ⟨w * w'⁻¹, F.mul_mem hwF (F.inv_mem hw'F), ?_⟩
    rw [div_eq_mul_inv]
    exact approxRoot_mul v hθ1 hw (approxRoot_inv v hθ hu' hw')
  · induction k with
    | zero => exact ⟨1, F.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨x, hxF, hx⟩ := ih
      refine ⟨x * w, F.mul_mem hxF hwF, ?_⟩
      rw [pow_succ]
      exact approxRoot_mul v hθ1 hx hw

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory

theorem sepFamily_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  intro L _ v G _ _ F ι s x y hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, fun _ => 1, fun _ => 1, fun _ => ⟨F.one_mem, F.one_mem, by simp, by simp⟩,
      fun σ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨n, a, b, hab, hsum⟩ := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    obtain ⟨hxF, hyF, hxv, hyv⟩ := hs j (Finset.mem_insert_self j s)
    refine ⟨n + n, Fin.append (fun i => x j * a i) (fun i => - a i),
      Fin.append b (fun i => y j * b i), ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.mul_mem hxF h1, h2, by rw [map_mul]; exact mul_le_one' hxv h3, h4⟩
      · simp only [Fin.append_right]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.neg_mem h1, F.mul_mem hyF h2, by rw [Valuation.map_neg]; exact h3,
          by rw [map_mul]; exact mul_le_one' hyv h4⟩
    · intro σ
      rw [Finset.prod_insert hj, ← hsum σ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, smul_mul']
      have e1 : ∑ i, x j * a i * σ • b i = x j * ∑ i, a i * σ • b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      have e2 : ∑ i, -a i * (σ • y j * σ • b i) = -(σ • y j * ∑ i, a i * σ • b i) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1, e2]; ring

end GlobalTheory
end

section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem laurent_terms_eq_zero_of_order_injOn {K ι : Type*} [Field K] (s : Finset ι)
    (f : ι → LaurentSeries K)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → (f i).order = (f j).order → i = j)
    (hsum : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  classical
  by_contra hne
  push Not at hne
  have hnon : (s.filter fun i => f i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hfi⟩ := hne
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hfi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun i => (f i).order) hnon
  obtain ⟨his, hfi⟩ := Finset.mem_filter.1 hi
  have h1 : (∑ j ∈ s, f j).coeff (f i).order = (f i).coeff (f i).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single_of_mem i his ?_
    intro j hj hji
    by_cases hfj : f j = 0
    · simp [hfj]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      exact lt_of_le_of_ne (hmin j (Finset.mem_filter.2 ⟨hj, hfj⟩))
        (fun h => hji (hinj i his j hj hfi hfj h).symm)
  rw [hsum] at h1
  exact hfi (HahnSeries.coeff_order_eq_zero.1 (by simpa using h1.symm))

theorem laurent_pow_indep_over_prime_pow_powers :
    ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (c : ℕ → LaurentSeries (ZMod p)), ∑ i ∈ Finset.range (p ^ n), c i ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ i = 0 → ∀ i < p ^ n, c i = 0 := by
  intro p _ n c hsum i hi
  have hX : ∀ j : ℕ, (HahnSeries.single (1 : ℤ) (1 : ZMod p) : LaurentSeries (ZMod p)) ^ j ≠ 0 :=
    fun j => pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)
  have hord : ∀ j : ℕ, c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j ≠ 0 →
      (c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j).order
        = ((p ^ n : ℕ) : ℤ) * (c j).order + j := by
    intro j hj
    rw [HahnSeries.order_mul (left_ne_zero_of_mul hj) (hX j), HahnSeries.order_pow,
      HahnSeries.order_pow, HahnSeries.order_single one_ne_zero]
    simp
  have key := laurent_terms_eq_zero_of_order_injOn (Finset.range (p ^ n))
    (fun j => c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j) ?_ hsum i
    (Finset.mem_range.2 hi)
  · exact pow_eq_zero_iff (by omega) |>.1 ((mul_eq_zero.1 key).resolve_right (hX i))
  · intro a ha b hb hfa hfb h
    have h' := (hord a hfa).symm.trans (h.trans (hord b hfb))
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hm := congrArg (fun z : ℤ => z % ((p ^ n : ℕ) : ℤ)) h'
    simp only [Int.mul_add_emod_self_left] at hm
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha'),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb')] at hm
    exact_mod_cast hm

end GlobalTheory
end

section

open scoped NNReal TensorProduct

theorem _root_.GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime : ∀ (p : ℕ) [Fact p.Prime] (f : LaurentSeries (ZMod p)), ∃ g : Fin p → LaurentSeries (ZMod p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ZMod p) * g j ^ p := by
  first | exact @GlobalTheory.laurentSeries_eq_sum_single_mul_pow | exact GlobalTheory.laurentSeries_eq_sum_single_mul_pow | (intros; apply GlobalTheory.laurentSeries_eq_sum_single_mul_pow <;> assumption)
end

section

open scoped Matrix
open NumberField

theorem _root_.GlobalTheory.T.exists_int_span_generators_of_isLattice_pi
    (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.IsFullLattice E Λ) :
    ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E,
      (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧
      Submodule.span ℚ (Set.range u) = ⊤ :=
  GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi E n Λ hΛ
end

section

open scoped Matrix
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span : ∀ (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U), Fintype.card ι = Fintype.card κ → (∀ k, v k ∈ Submodule.span ℤ (Set.range u)) → ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧ ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  first | exact @GlobalTheory.gram_det_index_sublattice | exact GlobalTheory.gram_det_index_sublattice | (intros; apply GlobalTheory.gram_det_index_sublattice <;> assumption)
end
