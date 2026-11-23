module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem T_mem_Gam (N l : ℕ) : ModularGroup.T ∈ Gam N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]

private theorem mul_Tm_mem (N l M : ℕ) [NeZero M] {γ : SL(2, ZMod M)} (h : γ ∈ Gs N l M) (b : ℕ) :
    γ * Tm M b ∈ Gs N l M := by
  simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  exact Subgroup.mul_mem _ h (Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ (T_mem_Gam N l) b))

theorem UpperTheory.sum_levelSubgroupMod_eq_smul_sum_reps :
    ∀ (N l M : ℕ) [NeZero M] (R : Finset SL(2, ZMod M)), IsReps N l M R → ∀ (V : Type) [AddCommMonoid V] (f : SL(2, ZMod M) → V), (∀ γ ∈ R, ∀ b : ℕ, f (γ * Tm M b) = f γ) → ∑ γ ∈ Gs N l M, f γ = M • ∑ γ ∈ R, f γ := by
  intro N l M _ R hR V _ f hf
  obtain ⟨hsub, huniq⟩ := hR
  have key : ∑ p ∈ R ×ˢ Finset.range M, f p.1 = ∑ γ ∈ Gs N l M, f γ := by
    refine Finset.sum_bij (fun p _ => p.1 * Tm M p.2) ?_ ?_ ?_ ?_
    · intro p hp
      exact mul_Tm_mem N l M (hsub (Finset.mem_product.1 hp).1) _
    · intro p hp q hq hpq
      have hp' := Finset.mem_product.1 hp
      have hq' := Finset.mem_product.1 hq
      exact (huniq _ (mul_Tm_mem N l M (hsub hp'.1) p.2)).unique
        ⟨hp'.1, Finset.mem_range.1 hp'.2, rfl⟩ ⟨hq'.1, Finset.mem_range.1 hq'.2, hpq⟩
    · intro γ hγ
      obtain ⟨p, ⟨h1, h2, h3⟩, -⟩ := huniq γ hγ
      exact ⟨p, Finset.mem_product.2 ⟨h1, Finset.mem_range.2 h2⟩, h3.symm⟩
    · intro p hp
      exact (hf _ (Finset.mem_product.1 hp).1 _).symm
  rw [← key, Finset.sum_product, Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem fib_card {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (z : H) :
    Fintype.card G = Fintype.card H * (Finset.univ.filter (fun y => f y = z)).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hc : ∀ b ∈ (Finset.univ : Finset H),
      (Finset.univ.filter (fun a => f a = b)).card = (Finset.univ.filter (fun y => f y = z)).card :=
    fun b _ => MonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf z)
  rw [Finset.card_univ, Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact h

theorem UpperTheory.card_fiber_reduction_eq_totient :
    ∀ (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N], ¬ l ∣ N → ∀ z : (ZMod (l ^ (m + n)))ˣ, (Finset.univ.filter (fun y => redTop l n m N y = z)).card = Nat.totient (N * N) := by
  intro l _ n m N _ hN z
  have hl : l.Prime := Fact.out
  have hdvd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (topM l n m (N * N)) :=
    ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  have key := fib_card (ZMod.unitsMap hdvd) (ZMod.unitsMap_surjective hdvd) z
  have hred : ∀ y, redTop l n m N y = ZMod.unitsMap hdvd y := fun y => rfl
  simp only [hred]
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at key
  have hcop : (l ^ (m + n)).Coprime (N * N) := by
    have h1 : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hN
    exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h1 h1)
  have htot : (topM l n m (N * N)).totient = (l ^ (m + n)).totient * (N * N).totient :=
    Nat.totient_mul hcop
  rw [htot] at key
  have hpos : 0 < (l ^ (m + n)).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
  exact (Nat.eq_of_mul_eq_mul_left hpos key).symm
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.repM_apply_zt_eq_pow_redTop :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (y : (ZMod (topM l n m (N * N)))ˣ), (repM (topM l n m (N * N)) y : Ω ≃ₐ[ℚ] Ω) (zt ε l (m + n)) = zt ε l (m + n) ^ ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))).val := by
  intro Ω _ _ _ ε l hl n m N _ y
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ^ (m + n) ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  haveI : NeZero (l ^ (m + n)) := ⟨hl0⟩
  have h1 : zt ε l (m + n) ^ (l ^ (m + n)) = 1 := by
    have h := (isPrimitiveRoot_eOm ε hl0).pow_eq_one
    rw [Nat.cast_pow] at h
    exact h
  have hd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  have h2 : zt ε l (m + n) ^ topM l n m (N * N) = 1 := by
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, h1, one_pow]
  rw [repM_apply _ y h2]
  have e : ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))) =
      (((y : ZMod (topM l n m (N * N))).val : ℕ) : ZMod (l ^ (m + n))) := by
    show ZMod.castHom hd (ZMod (l ^ (m + n))) (y : ZMod (topM l n m (N * N))) = _
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  rw [e, ZMod.val_natCast, ← pow_eq_pow_mod _ h1]
end
