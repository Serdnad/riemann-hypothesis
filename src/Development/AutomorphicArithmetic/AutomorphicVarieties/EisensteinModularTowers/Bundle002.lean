module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_cg {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {x y : ℤ}
    (h : x ≡ y [ZMOD M]) : ζ ^ x = ζ ^ y := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨k, hk⟩ := h.dvd
  have : y = x + (M : ℤ) * k := by linarith
  rw [this, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

private theorem eisF_shift {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ) (hM : 0 < M)
    (hζ : ζ ^ M = 1) (n : ℕ) :
    eisF j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * eisF j M ζ a₁ a₂ n := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  unfold eisF
  split_ifs with hn
  · subst hn
    simp only [Nat.cast_zero, mul_zero, zpow_zero, one_mul]
    unfold const0
    by_cases hd : (M : ℤ) ∣ a₁
    · have : ζ ^ (a₂ + e * a₁) = ζ ^ a₂ :=
        zpow_cg hM hζ (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (by simpa using hd.mul_left e)))
      rw [this]
    · simp only [if_neg hd]
  · unfold coefPos
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hnd : (n : ℤ) = ((n / d : ℕ) : ℤ) * d := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    rw [mul_sub]
    congr 1
    · split_ifs with h
      · have : ζ ^ ((a₂ + e * a₁) * d) = ζ ^ (e * (n : ℤ)) * ζ ^ (a₂ * d) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := ((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)
          refine h2.trans ?_
          rw [show (a₂ + e * ((n / d : ℕ) : ℤ)) * d = e * (((n / d : ℕ) : ℤ) * d) + a₂ * d by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]
    · split_ifs with h
      · have : ζ ^ (-((a₂ + e * a₁) * d)) = ζ ^ (e * (n : ℤ)) * ζ ^ (-(a₂ * d)) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := (((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)).neg
          refine h2.trans ?_
          rw [show -((a₂ + e * -((n / d : ℕ) : ℤ)) * d) = e * (((n / d : ℕ) : ℤ) * d) + -(a₂ * d) by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]

theorem UpperTheory.smoothedEisensteinCoeff_shift_second_index :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ), 0 < M → ζ ^ M = 1 → ∀ n : ℕ, smF c j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * smF c j M ζ a₁ a₂ n := by
  intro K _ _ c j M ζ a₁ a₂ e hM hζ n
  unfold smF
  rw [show c * (a₂ + e * a₁) = c * a₂ + e * (c * a₁) by ring, eisF_shift j M ζ a₁ a₂ e hM hζ,
    eisF_shift j M ζ (c * a₁) (c * a₂) e hM hζ]
  ring
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_congr_mod {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  obtain ⟨k, hk⟩ := h.dvd
  have hz : ζ ^ (M : ℤ) = 1 := by
    rw [zpow_natCast, hζ]
  have hb : b = a + M * k := by
    omega
  rw [hb, zpow_add₀ (by rintro rfl; simp [zero_pow hM.ne'] at hζ), zpow_mul, hz, one_zpow, mul_one]

private theorem eisF_congr_mod {K : Type} [Field K] [CharZero K] (j : ℕ) {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1)
    {a₁ b₁ a₂ b₂ : ℤ} (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ b₁ b₂ n := by
  unfold eisF
  split_ifs
  · unfold const0 frc
    have hd : ((M : ℤ) ∣ a₁ ↔ (M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁]
    rw [zpow_congr_mod hM hζ h₂, show a₁ % (M : ℤ) = b₁ % M from h₁]
    simp only [hd]
  · unfold coefPos
    refine Finset.sum_congr rfl fun d _ => ?_
    have hc : ∀ x : ℤ, (x ≡ a₁ [ZMOD M] ↔ x ≡ b₁ [ZMOD M]) :=
      fun x => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    simp only [hc, zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)).neg]

theorem UpperTheory.smoothedEisenstein_congr_of_modEq :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K), 0 < M → ζ ^ M = 1 → ∀ {a₁ b₁ a₂ b₂ : ℤ}, a₁ ≡ b₁ [ZMOD M] → a₂ ≡ b₂ [ZMOD M] → smF c j M ζ a₁ a₂ = smF c j M ζ b₁ b₂ := by
  intro K _ _ c j M ζ hM hζ a₁ b₁ a₂ b₂ h₁ h₂
  funext n
  unfold smF
  rw [eisF_congr_mod j hM hζ h₁ h₂, eisF_congr_mod j hM hζ (h₁.mul_left c) (h₂.mul_left c)]
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.congruence_action_invariant :
    ∀ (l : ℕ) [Fact l.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ (z : (ZMod (l ^ L))ˣ) (t : SL(2, ZMod (l ^ L)) → (ZMod (l ^ L))ˣ → GL (Fin 2) (ZMod (l ^ L))), (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = h i 0) → (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = (u : ZMod (l ^ L)) * h i 1) → ∀ (V : Type) [AddCommMonoid V] (f : GL (Fin 2) (ZMod (l ^ L)) → V), ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ L)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ L))ˣ => (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m]), f (t h (a * z)) = ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ L)).val : ℕ) : ZMod (l ^ m))), f γ := by
  intro l _ L m _ hmL z t ht0 ht1 V _ f
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  set φ := ZMod.castHom hd (ZMod (l ^ m)) with hφ
  have hcast : ∀ x : ZMod (l ^ L), ((x.val : ℕ) : ZMod (l ^ m)) = φ x := by
    intro x
    rw [ZMod.natCast_val, hφ, ZMod.castHom_apply]
  have hmod : ∀ a : (ZMod (l ^ L))ˣ, (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m] ↔ φ a = 1 := by
    intro a
    rw [← ZMod.natCast_eq_natCast_iff, hcast, Nat.cast_one]
  have hdet : ∀ h u, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det
      = (u : ZMod (l ^ L)) := by
    intro h u
    have h1 : (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det = 1 := h.prop
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [ht0, ht0, ht1, ht1]
    linear_combination (u : ZMod (l ^ L)) * h1
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => t p.1 (p.2 * z))
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, ht0, hcast, hdet]
    refine ⟨hp.1, ?_⟩
    rw [Units.val_mul, map_mul, (hmod _).mp hp.2, one_mul]
  · intro p _ q _ hpq
    have hu : p.2 * z = q.2 * z := by
      apply Units.ext
      rw [← hdet p.1, ← hdet q.1, hpq]
    have ha : p.2 = q.2 := mul_right_cancel hu
    have hh : p.1 = q.1 := by
      ext i j
      fin_cases j
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0) hpq
        simpa [ht0] using this
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1) hpq
        simp only [ht1] at this
        rw [hu] at this
        exact (Units.mul_right_inj _).mp this
    exact Prod.ext hh ha
  · intro γ hγ
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, hcast] at hγ
    set g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) := (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) with hg
    set u : (ZMod (l ^ L))ˣ := Matrix.GeneralLinearGroup.det γ with hu
    have hug : (u : ZMod (l ^ L)) = g.det := rfl
    set M : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) :=
      !![g 0 0, (↑u⁻¹ : ZMod (l ^ L)) * g 0 1; g 1 0, (↑u⁻¹ : ZMod (l ^ L)) * g 1 1] with hM
    have hMdet : M.det = 1 := by
      rw [hM, Matrix.det_fin_two_of]
      have h2 : (↑u⁻¹ : ZMod (l ^ L)) * g.det = 1 := by
        rw [← hug, Units.inv_mul]
      rw [Matrix.det_fin_two] at h2
      linear_combination h2
    refine ⟨(⟨M, hMdet⟩, u * z⁻¹), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hγ.1⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmod, Units.val_mul, map_mul, hug, hγ.2, ← map_mul, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, map_one]
    · apply Units.ext
      have hz : u * z⁻¹ * z = u := by group
      have e0 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = g i 0 := by
        intro i
        refine (ht0 _ _ i).trans ?_
        fin_cases i <;> rfl
      have e1 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = g i 1 := by
        intro i
        refine (ht1 _ _ i).trans ?_
        rw [hz]
        fin_cases i
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 0 1) = g 0 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 1 1) = g 1 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
      ext i j
      fin_cases j
      · exact e0 i
      · exact e1 i
  · intro p _
    rfl
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.ring_hom_eisenstein_coeff {K : Type} [Field K] [CharZero K] (s : K →+* K) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ)
    (h : s (ζ ^ a₂) = ζ ^ b₂) (n : ℕ) : s (eisF j M ζ a₁ a₂ n) = eisF j M ζ a₁ b₂ n := by
  have hz : ∀ k : ℤ, s (ζ ^ (a₂ * k)) = ζ ^ (b₂ * k) := by
    intro k
    rw [zpow_mul, zpow_mul, map_zpow₀, h]
  have hz' : ∀ k : ℤ, s (ζ ^ (-(a₂ * k))) = ζ ^ (-(b₂ * k)) := by
    intro k
    rw [zpow_neg, zpow_neg, map_inv₀, hz]
  unfold eisF const0 coefPos
  split_ifs
  · simp only [map_div₀, map_mul, map_add (f := _), map_sub, map_one, map_ofNat, h]
  · simp only [map_ratCast]
  · simp only [map_neg, map_ratCast]
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_sub]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    · split_ifs
      · rw [map_mul, map_pow, map_div₀, map_natCast, map_natCast, hz]
      · exact map_zero s
    · split_ifs
      · rw [map_mul, map_pow, map_neg, map_div₀, map_natCast, map_natCast, hz']
      · exact map_zero s

theorem UpperTheory.ringHom_apply_smoothedEisensteinCoeff :
    ∀ {K : Type} [Field K] [CharZero K] (s : K →+* K) (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ), ζ ≠ 0 → s (ζ ^ a₂) = ζ ^ b₂ → ∀ n : ℕ, s (smF c j M ζ a₁ a₂ n) = smF c j M ζ a₁ b₂ n := by
  intro K _ _ s c j M ζ a₁ a₂ b₂ _ h n
  have hc : s (ζ ^ (c * a₂)) = ζ ^ (c * b₂) := by
    rw [mul_comm c a₂, mul_comm c b₂, zpow_mul, zpow_mul, map_zpow₀, h]
  unfold smF
  rw [map_sub, map_mul, map_mul, UpperTheory.ring_hom_eisenstein_coeff s j M ζ a₁ a₂ b₂ h n,
    UpperTheory.ring_hom_eisenstein_coeff s j M ζ (c * a₁) (c * a₂) (c * b₂) hc n]
  simp only [map_pow, map_zpow₀, map_intCast]
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.eisenstein_coeff_root_pow {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β n : ℕ) :
    eisF j M (ζ ^ β) a₁ a₂ n = eisF j M ζ a₁ ((β : ℤ) * a₂) n := by
  have hz : ∀ t : ℤ, (ζ ^ β) ^ t = ζ ^ ((β : ℤ) * t) := fun t => by
    rw [zpow_mul, zpow_natCast]
  unfold eisF const0 coefPos
  simp only [hz, mul_neg, mul_assoc]

theorem UpperTheory.smoothedEisenstein_root_pow :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β : ℕ), ζ ≠ 0 → smF c j M (ζ ^ β) a₁ a₂ = smF c j M ζ a₁ ((β : ℤ) * a₂) := by
  intro K _ _ c j M ζ a₁ a₂ β _
  funext n
  unfold smF
  rw [UpperTheory.eisenstein_coeff_root_pow, UpperTheory.eisenstein_coeff_root_pow, mul_left_comm (β : ℤ) c a₂]
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.twistedEisensteinPiece_trivialCharacter_eq :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N L m w : ℕ) (c d : ℤ) (v v' : ℤ × ℤ) (ζ : K) (z₀ : ZMod (l ^ m)), 1 ≤ m → m ≤ L → ∀ r : ℕ, pieceT N l L m (w + 2) (1 : DirichletCharacter K (l ^ m)) c d v v' ζ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = -((l : K) ^ ((L : ℤ) * ((w : ℤ) - 2))) * ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀), cmul (smF c (w + 1) (N * l ^ L) ζ (rowT N l L γ 0 v).1 (rowT N l L γ 0 v).2) (smF d 1 (N * l ^ L) ζ (rowT N l L γ 1 v').1 (rowT N l L γ 1 v').2) r := by
  intro K _ _ l _ N L m w c d v v' ζ z₀ _ hmL r
  unfold pieceT
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  have hexp : ((L : ℤ) * (((w + 2 : ℕ) : ℤ) - 4)) = (L : ℤ) * ((w : ℤ) - 2) := by
    push_cast
    ring
  have hk : w + 2 - 1 = w + 1 := by omega
  rw [hexp, hk]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  have hu : IsUnit ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m))) := by
    rw [ZMod.natCast_val]
    have hdet : IsUnit (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
    exact hdet.map (ZMod.castHom hd (ZMod (l ^ m)))
  rw [MulChar.one_apply hu, one_mul]
end
