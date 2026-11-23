module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle149
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvOfIsPrimitive
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.GaussSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle145
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormsEqZeroOfPeriodSubConjCoboundary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Degree
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Data.Nat.Prime.Int

@[expose] public section

section

namespace GlobalTheory.K5.IntFrac

open Polynomial

theorem mem_adjoin_inv_of_isIntegral' {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  apply GlobalTheory.K5.LevClosed.mem_adjoin_inv_of_isIntegral <;> assumption

theorem mem_of_div_le_one : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  intro O Ω _ _ _ v hv B hB π hπB hπ0 hπ1 hdiv
  have hvπ : 0 < v π := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hπ0)
  have hA : ∀ n : ℕ, ∀ a ∈ B, v (a / π ^ n) ≤ 1 → a / π ^ n ∈ B := by
    intro n
    induction n with
    | zero => intro a ha _; simpa using ha
    | succ k ih =>
      intro a ha hle
      have hlt : v a < 1 := by
        have he : v a = v (a / π ^ (k + 1)) * v π ^ (k + 1) := by
          rw [map_div₀, map_pow, div_mul_cancel₀]
          exact pow_ne_zero _ hvπ.ne'
        rw [he]
        calc v (a / π ^ (k + 1)) * v π ^ (k + 1) ≤ 1 * v π ^ (k + 1) := by gcongr
          _ < 1 := by
            rw [one_mul]
            exact pow_lt_one₀ hvπ.le hπ1 (Nat.succ_ne_zero k)
      have he : a / π ^ (k + 1) = a / π / π ^ k := by rw [pow_succ', div_div]
      rw [he] at hle ⊢
      exact ih _ (hdiv a ha hlt) hle
  intro a ha b hb hab
  by_cases hb0 : b = 0
  · rw [hb0, div_zero]
    exact B.zero_mem
  have hvb : 0 < v b := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hb0)
  have hex : ∃ n, v π ^ (n + 1) < v b := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hvb hπ1
    cases m with
    | zero => exact absurd (hB b hb) (not_le.mpr (by simpa using hm))
    | succ k => exact ⟨k, hm⟩
  classical
  set n := Nat.find hex with hndef
  have hn : v π ^ (n + 1) < v b := Nat.find_spec hex
  have hle : v b ≤ v π ^ n := by
    by_cases h0 : n = 0
    · rw [h0, pow_zero]
      exact hB b hb
    · have hmin := Nat.find_min hex (show n - 1 < n by omega)
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1] at hmin
      exact not_lt.mp hmin
  have hvπn : 0 < v π ^ n := pow_pos hvπ n
  have hvw_le : v (b / π ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, div_le_one₀ hvπn]
    exact hle
  have hwB : b / π ^ n ∈ B := hA n b hb hvw_le
  have hvw : v (b / π ^ n) = 1 := by
    refine le_antisymm hvw_le (not_lt.mp fun hlt => ?_)
    have h2 := hB _ (hdiv _ hwB hlt)
    rw [div_div, ← pow_succ, map_div₀, map_pow, div_le_one₀ (pow_pos hvπ _)] at h2
    exact not_le.mpr hn h2
  have hw0 : b / π ^ n ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have hwinv : (b / π ^ n)⁻¹ ∈ B := by
    have hint : IsIntegral O (b / π ^ n)⁻¹ := (hv _).mp (by rw [map_inv₀, hvw, inv_one])
    have hmem := mem_adjoin_inv_of_isIntegral' (inv_ne_zero hw0) hint
    rw [inv_inv] at hmem
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hwB) hmem
  have haπ : a / π ^ n ∈ B := by
    apply hA n a ha
    have he : a / π ^ n = a / b * (b / π ^ n) := by field_simp
    rw [he, map_mul, hvw, mul_one]
    exact hab
  have he : a / b = a / π ^ n * (b / π ^ n)⁻¹ := by field_simp
  rw [he]
  exact B.mul_mem haπ hwinv

end GlobalTheory.K5.IntFrac
end

section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem gaussSum_mul_gaussSum_inv_prim {K : Type} [Field K] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter K n} {e : AddChar (ZMod n) K} (hχ : χ.IsPrimitive)
    (he : e.IsPrimitive) : gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (n : K) := by
  apply GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive <;> assumption

end GlobalTheory.KummerEisensteinGalois
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_coeffwiseConjugate_of_integral_quotient : ∀ (g : ℂ ≃+* ℂ) (N n : ℕ) (f D D' A A' : ℍ → ℂ) (s s' : Fin n → ℍ → ℂ), 0 < N → (∃ a, HasQ N f a) → QConj g N D D' → QConj g N A A' → (∀ j, QConj g N (s j) (s' j)) → D ≠ 0 → (∀ τ, f τ * D τ = A τ) → (∀ τ, f τ ^ n + ∑ j, s j τ * f τ ^ (j : ℕ) = 0) → ∃ f' : ℍ → ℂ, QConj g N f f' ∧ ∀ τ, f' τ * D' τ = A' τ := by
  first | exact @GlobalTheory.FN.conj_exists | exact GlobalTheory.FN.conj_exists | (intros; apply GlobalTheory.FN.conj_exists <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lrep_repU_of_dvd (M l : ℕ) (hl : l.Prime) (hlM : l ∣ M) :
    LRep M {δ : M2 | δ.det = l ∧ (M : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} (repU l) := by
  have hlM' : (l : ℤ) ∣ (M : ℤ) := by exact_mod_cast hlM
  have hpZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have key : ∀ γ : SL(2, ℤ), (M : ℤ) ∣ (γ : M2) 1 0 → ¬ (l : ℤ) ∣ (γ : M2) 0 0 := by
    intro γ hc ha
    have hdet : (γ : M2).det = 1 := γ.2
    rw [Matrix.det_fin_two] at hdet
    have : (l : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right (hlM'.trans hc) _)
    exact hpZ.not_dvd_one this
  have ent : ∀ (A : M2) (j : Fin l), (A * repU l j) 0 0 = A 0 0 ∧ (A * repU l j) 1 0 = A 1 0 ∧
      (A * repU l j) 0 1 = A 0 0 * (j : ℕ) + A 0 1 * l ∧
      (A * repU l j) 1 1 = A 1 0 * (j : ℕ) + A 1 1 * l := by
    intro A j
    simp [repU, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨γ, hγ⟩, j⟩ -
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, -, -⟩ := ent (γ : M2) j
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul, repU, Matrix.det_fin_two_of]
      rw [show (γ : M2).det = 1 from γ.2]
      simp
    · simpa [e2] using hc
    · simpa [e1] using key γ hc
  · rintro ⟨⟨γ, hγ⟩, j⟩ - ⟨⟨γ', hγ'⟩, j'⟩ - h
    simp only at h
    have hc : (M : ℤ) ∣ (γ : M2) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    obtain ⟨f1, f2, f3, f4⟩ := ent (γ' : M2) j'
    have h00 : (γ : M2) 0 0 = (γ' : M2) 0 0 := by rw [← e1, ← f1, h]
    have h10 : (γ : M2) 1 0 = (γ' : M2) 1 0 := by rw [← e2, ← f2, h]
    have h01 : (γ : M2) 0 0 * (j : ℕ) + (γ : M2) 0 1 * l = (γ' : M2) 0 0 * (j' : ℕ) + (γ' : M2) 0 1 * l := by
      rw [← e3, ← f3, h]
    have h11 : (γ : M2) 1 0 * (j : ℕ) + (γ : M2) 1 1 * l = (γ' : M2) 1 0 * (j' : ℕ) + (γ' : M2) 1 1 * l := by
      rw [← e4, ← f4, h]
    have hdiv : (l : ℤ) ∣ (γ : M2) 0 0 * (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) :=
      ⟨(γ' : M2) 0 1 - (γ : M2) 0 1, by rw [h00] at h01 ⊢; linear_combination h01⟩
    have hd2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) :=
      (hpZ.dvd_or_dvd hdiv).resolve_left (key γ hc)
    have hjj : j = j' := by
      have hj := j.2
      have hj' := j'.2
      obtain ⟨k, hk⟩ := hd2
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      subst hk0
      ext
      omega
    subst hjj
    have g01 : (γ : M2) 0 1 = (γ' : M2) 0 1 := by
      apply mul_right_cancel₀ hl0; rw [h00] at h01; linarith
    have g11 : (γ : M2) 1 1 = (γ' : M2) 1 1 := by
      apply mul_right_cancel₀ hl0; rw [h10] at h11; linarith
    have : γ = γ' := by
      ext i k; fin_cases i <;> fin_cases k <;> simp [h00, h10, g01, g11]
    subst this
    rfl
  · rintro δ ⟨hdet, hc, ha⟩
    haveI : Fact l.Prime := ⟨hl⟩
    have hlc : (l : ℤ) ∣ δ 1 0 := hlM'.trans hc
    rw [Matrix.det_fin_two] at hdet
    have hld : (l : ℤ) ∣ δ 1 1 := by
      have : (l : ℤ) ∣ δ 0 0 * δ 1 1 := ⟨1 + (δ 0 1) * ((δ 1 0) / l), by
        obtain ⟨t, ht⟩ := hlc
        rw [ht, Int.mul_ediv_cancel_left _ hl0]
        linear_combination hdet + (δ 0 1) * ht⟩
      exact (hpZ.dvd_or_dvd this).resolve_left ha
    have haZ : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ha
    let j : Fin l := ⟨(((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩
    have hjZ : ((j : ℕ) : ZMod l) = ((δ 0 1 : ℤ) : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ :=
      ZMod.natCast_zmod_val _
    have hb : (l : ℤ) ∣ δ 0 1 - δ 0 0 * (j : ℕ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hjZ]
      field_simp
      ring
    have hdd : (l : ℤ) ∣ δ 1 1 - δ 1 0 * (j : ℕ) := dvd_sub hld (dvd_mul_of_dvd_left hlc _)
    obtain ⟨e, he⟩ := hb
    obtain ⟨f, hf⟩ := hdd
    have hγdet : (!![δ 0 0, e; δ 1 0, f] : M2).det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hl0
      linear_combination -(δ 0 0) * hf + (δ 1 0) * he + hdet
    let γ : SL(2, ℤ) := ⟨!![δ 0 0, e; δ 1 0, f], hγdet⟩
    have hγ : γ ∈ Gamma0 M := by
      rw [Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa [γ] using hc)
    refine ⟨(⟨γ, hγ⟩, j), Set.mem_univ _, ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := ent (γ : M2) j
    ext i k; fin_cases i <;> fin_cases k
    · simpa [γ] using e1
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e3 ⊢
      rw [e3]; simp [γ]; linarith
    · simpa [γ] using e2
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e4 ⊢
      rw [e4]; simp [γ]; linarith

theorem lrep_repU (L l : ℕ) (hl : l.Prime) :
    (l ∣ L → LRep L (DU L l) (repU l)) ∧
      (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  refine ⟨fun h => lrep_repU_of_dvd L l hl h, fun _ => ?_⟩
  have hs : {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} =
      {δ : M2 | δ.det = l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0} := by
    ext δ
    simp only [DU, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, (Int.natCast_dvd_natCast.mpr (dvd_mul_right L l)).trans h4, h3⟩, h4⟩
  rw [hs]
  exact lrep_repU_of_dvd (L * l) l hl (dvd_mul_left l L)

theorem zrepU : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧
    (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) :=
  fun L l hl => lrep_repU L l hl

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem modGrowth_pow_bounds (y : ℝ) (hy : 0 < y) (A : ℕ) :
    max y y⁻¹ ^ A ≤ y ^ A + (y ^ A)⁻¹ ∧ y ^ A + (y ^ A)⁻¹ ≤ 2 * max y y⁻¹ ^ A := by
  rw [← inv_pow]
  have h1 : 0 < y ^ A := pow_pos hy A
  have h2 : 0 < y⁻¹ ^ A := pow_pos (inv_pos.mpr hy) A
  rcases le_total y y⁻¹ with h | h
  · rw [max_eq_right h]
    have : y ^ A ≤ y⁻¹ ^ A := pow_le_pow_left₀ hy.le h A
    constructor <;> linarith
  · rw [max_eq_left h]
    have : y⁻¹ ^ A ≤ y ^ A := pow_le_pow_left₀ (inv_pos.mpr hy).le h A
    constructor <;> linarith

theorem one_le_max_inv (y : ℝ) (hy : 0 < y) : 1 ≤ max y y⁻¹ := by
  rcases le_total 1 y with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hy).mpr h)

theorem mod_of_bound (F : ℍ → ℂ) (C : ℝ) (A : ℕ) (h : ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A) :
    Mod F := by
  refine ⟨max C 0, A, fun τ => ?_⟩
  obtain ⟨b1, _⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hM : 0 ≤ max τ.im τ.im⁻¹ ^ A :=
    pow_nonneg (le_trans zero_le_one (one_le_max_inv _ τ.im_pos)) A
  calc ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := h τ
    _ ≤ max C 0 * max τ.im τ.im⁻¹ ^ A := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 (le_max_right _ _)

theorem bound_of_mod (F : ℍ → ℂ) (hF : Mod F) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ τ : ℍ, ‖F τ‖ ≤ C * max τ.im τ.im⁻¹ ^ A := by
  obtain ⟨C, A, h⟩ := hF
  refine ⟨2 * max C 0, A, by positivity, fun τ => ?_⟩
  obtain ⟨_, b2⟩ := modGrowth_pow_bounds τ.im τ.im_pos A
  have hh : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ :=
    add_nonneg (pow_pos τ.im_pos A).le (inv_pos.mpr (pow_pos τ.im_pos A)).le
  calc ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := h τ
    _ ≤ max C 0 * (τ.im ^ A + (τ.im ^ A)⁻¹) := mul_le_mul_of_nonneg_right (le_max_left _ _) hh
    _ ≤ max C 0 * (2 * max τ.im τ.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left b2 (le_max_right _ _)
    _ = _ := by ring

theorem mod_add (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ + G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C + D) (A + B) fun τ => ?_
  have hM := one_le_max_inv _ τ.im_pos
  have eA : max τ.im τ.im⁻¹ ^ A ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_right A B)
  have eB : max τ.im τ.im⁻¹ ^ B ≤ max τ.im τ.im⁻¹ ^ (A + B) := pow_le_pow_right₀ hM (Nat.le_add_left B A)
  calc ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le _ _
    _ ≤ C * max τ.im τ.im⁻¹ ^ A + D * max τ.im τ.im⁻¹ ^ B := add_le_add (h1 τ) (h2 τ)
    _ ≤ C * max τ.im τ.im⁻¹ ^ (A + B) + D * max τ.im τ.im⁻¹ ^ (A + B) :=
        add_le_add (mul_le_mul_of_nonneg_left eA hC) (mul_le_mul_of_nonneg_left eB hD)
    _ = _ := by ring

theorem mod_mul (F G : ℍ → ℂ) (hF : Mod F) (hG : Mod G) : Mod (fun τ => F τ * G τ) := by
  obtain ⟨C, A, hC, h1⟩ := bound_of_mod F hF
  obtain ⟨D, B, hD, h2⟩ := bound_of_mod G hG
  refine mod_of_bound _ (C * D) (A + B) fun τ => ?_
  have hM := le_trans zero_le_one (one_le_max_inv _ τ.im_pos)
  calc ‖F τ * G τ‖ = ‖F τ‖ * ‖G τ‖ := norm_mul _ _
    _ ≤ (C * max τ.im τ.im⁻¹ ^ A) * (D * max τ.im τ.im⁻¹ ^ B) :=
        mul_le_mul (h1 τ) (h2 τ) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hM A))
    _ = _ := by ring

theorem mod_const (c : ℂ) : Mod fun _ => c :=
  mod_of_bound _ ‖c‖ 0 fun τ => by simp

theorem im_slz_arg (δ : M2) (hc : δ 1 0 = 0) (τ : ℍ) :
    (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im
      = (δ 0 0 : ℝ) / (δ 1 1 : ℝ) * τ.im := by
  rw [hc]
  simp [Complex.div_im]
  rcases eq_or_ne ((δ 1 1 : ℤ) : ℝ) 0 with h | h
  · simp [h]
  · field_simp

theorem max_inv_mul_le (r y : ℝ) (hr : 0 < r) (hy : 0 < y) :
    max (r * y) (r * y)⁻¹ ≤ max r r⁻¹ * max y y⁻¹ := by
  have h1 := one_le_max_inv r hr
  have h2 := one_le_max_inv y hy
  rw [mul_inv]
  apply max_le
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) hy.le (by linarith)
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_pos.mpr hy).le (by linarith)

theorem mod_slz (F : ℍ → ℂ) (k : ℕ) (δ : M2) (hdet : 0 < δ.det) (hc : δ 1 0 = 0) (hF : Mod F) :
    Mod (slz k δ F) := by
  obtain ⟨C, A, hC0, hC⟩ := bound_of_mod F hF
  have hdet' : δ.det = δ 0 0 * δ 1 1 := by rw [Matrix.det_fin_two, hc]; ring
  have had : (0 : ℝ) < (δ 0 0 : ℝ) * (δ 1 1 : ℝ) := by
    have : (0 : ℤ) < δ 0 0 * δ 1 1 := hdet' ▸ hdet
    exact_mod_cast this
  have hd : (δ 1 1 : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at had; exact lt_irrefl _ had
  have hrpos : (0 : ℝ) < (δ 0 0 : ℝ) / (δ 1 1 : ℝ) := by
    have : (δ 0 0 : ℝ) / (δ 1 1 : ℝ) = (δ 0 0 : ℝ) * δ 1 1 / ((δ 1 1 : ℝ) ^ 2) := by
      field_simp
    rw [this]; exact div_pos had (by positivity)
  set r : ℝ := (δ 0 0 : ℝ) / (δ 1 1 : ℝ) with hr
  set K : ℝ := ‖((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹‖ with hK
  set R : ℝ := max r r⁻¹ with hR
  have hR1 : 1 ≤ R := one_le_max_inv r hrpos
  refine mod_of_bound _ (K * (C * R ^ A)) A fun τ => ?_
  have him := im_slz_arg δ hc τ
  rw [← hr] at him
  have hz : 0 < (((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)))).im := by
    rw [him]; exact mul_pos hrpos τ.im_pos
  set w : ℍ := ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))) with hw
  have hwim : w.im = r * τ.im := by
    rw [hw, ofComplex_apply_of_im_pos hz]; exact him
  have hMw : max w.im w.im⁻¹ ^ A ≤ R ^ A * max τ.im τ.im⁻¹ ^ A := by
    rw [← mul_pow, hwim]
    exact pow_le_pow_left₀ (le_trans zero_le_one (one_le_max_inv _ (mul_pos hrpos τ.im_pos)))
      (max_inv_mul_le r τ.im hrpos τ.im_pos) A
  have hslz : slz k δ F τ = (((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹) * F w := by
    rw [slz, hw]; simp [hc]
  rw [hslz, norm_mul, ← hK]
  have hK0 : 0 ≤ K := norm_nonneg _
  calc K * ‖F w‖ ≤ K * (C * max w.im w.im⁻¹ ^ A) := mul_le_mul_of_nonneg_left (hC w) hK0
    _ ≤ K * (C * (R ^ A * max τ.im τ.im⁻¹ ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMw hC0) hK0
    _ = _ := by ring

theorem mod_algebra : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) :=
  ⟨fun F G hF hG => ⟨mod_add F G hF hG, mod_mul F G hF hG⟩, mod_const,
    fun F k δ hdet hc hF => mod_slz F k δ hdet hc hF⟩

end GlobalTheory.EisM
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem | exact GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem | (intros; apply GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem <;> assumption)
end

end

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.hasModerateGrowth_algebra_slash_stable : (∀ F G : ℍ → ℂ, Mod F → Mod G → Mod (fun τ => F τ + G τ) ∧ Mod (fun τ => F τ * G τ)) ∧ (∀ c : ℂ, Mod fun _ => c) ∧ (∀ (F : ℍ → ℂ) (k : ℕ) (δ : M2), 0 < δ.det → δ 1 0 = 0 → Mod F → Mod (slz k δ F)) := by
  first | exact @GlobalTheory.EisM.mod_algebra | exact GlobalTheory.EisM.mod_algebra | (intros; apply GlobalTheory.EisM.mod_algebra <;> assumption)

end
end

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.heckeU_leftRepresentatives_level_change : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧ (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  first | exact @GlobalTheory.EisM.zrepU | exact GlobalTheory.EisM.zrepU | (intros; apply GlobalTheory.EisM.zrepU <;> assumption)

end
end
