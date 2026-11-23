module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

private theorem qParam_one_eq (τ : ℍ) :
    Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * τ) := by
  simp [Function.Periodic.qParam]

private theorem disc_vadd (τ : ℍ) :
    ModularForm.discriminant ((1 : ℝ) +ᵥ τ) = ModularForm.discriminant τ := by
  have h := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
    one_mem_strictPeriods_SL (τ : ℂ)
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at h
  have e : UpperHalfPlane.ofComplex ((τ : ℂ) + ((1 : ℝ) : ℂ)) = (1 : ℝ) +ᵥ τ := by
    ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]
    simp [add_comm]
  rw [e] at h
  simpa [CuspForm.coe_discriminant] using h

private theorem qParam_ne (τ : ℍ) : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 :=
  Function.Periodic.qParam_ne_zero _

theorem dd_div_q_and_q_div_dd :
    (∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => DD τ / Complex.exp (2 * Real.pi * Complex.I * τ))
      fun n => (c n : ℂ)) ∧
    ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ)
      fun n => (c n : ℂ) := by
  obtain ⟨U, hU0, hU⟩ := GlobalTheory.exists_hasQExpansion_discriminant
  have hu : GlobalTheory.HasQExpansion 1 (fun τ ↦ ModularForm.discriminant τ / Function.Periodic.qParam 1 τ)
      (PowerSeries.map (Int.castRingHom ℂ) U) :=
    .of_qParam_mul (hU.congr fun τ ↦ by field_simp [qParam_ne τ])
  have hcast : ∀ (V : PowerSeries ℤ) (g : ℍ → ℂ),
      GlobalTheory.HasQExpansion 1 g (PowerSeries.map (Int.castRingHom ℂ) V) →
        HasQ 1 g fun n => ((PowerSeries.coeff n V : ℤ) : ℂ) := by
    intro V g hg
    have := (hasQ_coeff_iff_hasQExpansion 1 g _).mpr (by exact_mod_cast hg)
    simpa [PowerSeries.coeff_map] using this
  refine ⟨⟨fun n => PowerSeries.coeff n U, hU0, ?_⟩, ?_⟩
  · have := hcast U _ hu
    convert this using 2 with τ
    rw [qParam_one_eq]; rfl

  set f : ℍ → ℂ := fun τ ↦ Function.Periodic.qParam 1 τ / ModularForm.discriminant τ with hf
  have hper : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ := fun τ ↦ by
    simp only [hf, GlobalTheory.qParam_one_vadd, disc_vadd]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
    ((GlobalTheory.HasQExpansion.qParam 1).mdifferentiable one_pos).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty f := by
    have ht := (tendsto_const_nhds (x := (1 : ℂ))).div (hu.tendsto one_pos)
      (by simp [PowerSeries.coeff_map, hU0])
    have : f = fun τ ↦ 1 / (ModularForm.discriminant τ / Function.Periodic.qParam 1 τ) := by
      funext τ; simp only [hf]; field_simp
    rw [this]
    exact ht.isBigO_one ℝ
  have h1 := GlobalTheory.HasQExpansion.of_periodic one_pos
    (GlobalTheory.periodic_comp_ofComplex_of_vadd hper) hhol hbdd
  have h2 := (h1.mul hu).unique one_pos ((GlobalTheory.HasQExpansion.const 1 (1 : ℂ)).congr fun τ ↦ by
    simp only [hf]; field_simp [qParam_ne τ, ModularForm.discriminant_ne_zero τ])
  have hUV : U * U.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit U 1 (by simpa using hU0)
  have h3 : UpperHalfPlane.qExpansion 1 f =
      PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1) := by
    have e := congrArg (· * PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1)) h2
    simp only [mul_assoc, ← map_mul, hUV, map_one, mul_one, one_mul] at e
    exact e
  refine ⟨fun n => PowerSeries.coeff n (U.invOfUnit 1), ?_, ?_⟩
  · simp
  · have := hcast _ _ (h3 ▸ h1)
    convert this using 2 with τ
    simp only [hf, qParam_one_eq]; rfl

end GlobalTheory.FN
end
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.heckeTqRepresentatives_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime → tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  first | exact @GlobalTheory.tqFam_cosets_distinct | exact GlobalTheory.tqFam_cosets_distinct | (intros; apply GlobalTheory.tqFam_cosets_distinct <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeUlRepresentatives_right_mul_perm : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin l), ∀ i, ∃ γ' : Lev N l, ulFam l i * mat γ = mat γ' * ulFam l (π i) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulFam_perm | exact GlobalTheory.HeckeFamilyMatrices.ulFam_perm | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulFam_perm <;> assumption)
end
