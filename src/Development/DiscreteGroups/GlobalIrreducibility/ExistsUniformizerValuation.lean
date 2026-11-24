module

import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

noncomputable section

open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord_le (x y : kˣ) :
    valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hx : φ (valuation k (x : k)) ≠ 0 := by simp
  have hy : φ (valuation k (y : k)) ≠ 0 := by simp
  have ho : ∀ z : kˣ, ord k z = -WithZero.log (φ (valuation k (z : k))) := fun _ => rfl
  rw [← φ.strictMono.le_iff_le, ← WithZero.exp_log hx, ← WithZero.exp_log hy, WithZero.exp_le_exp, ho x, ho y]
  omega

theorem ord_inv_eq_neg_ord (x : kˣ) : ord k x⁻¹ = -ord k x := by
  have h := ord_mul k x⁻¹ x
  rw [inv_mul_cancel, ord_eq_zero (k := k) (x := 1) (by simp)] at h
  omega

theorem ord_pow_bis (x : kˣ) (n : ℕ) : ord k (x ^ n) = n * ord k x := by
  induction n with
  | zero => simp [ord_eq_zero]
  | succ n ih => rw [pow_succ, ord_mul, ih]; push_cast; ring

theorem exists_uniformizer_valuation : ∃ t : kˣ, valuation k (t : k) = uniformizer k := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have h0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact absurd ht.symm (by simp)
  exact ⟨Units.mk0 t h0, ht⟩

theorem exists_ball_char_trivial (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ s : kˣ, ∀ y ∈ cball s, ψ y = 1 := by
  have hU : {x : k | ‖(ψ x : ℂ) - 1‖ < 1 / 2} ∈ nhds (0 : k) := by
    have hc : Continuous fun x : k => ‖(ψ x : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp hψ).sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  refine ⟨s, fun y hy => ?_⟩
  have hn : ∀ n : ℕ, n • y ∈ cball s := by
    intro n
    induction n with
    | zero => simp [cball]
    | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hy
  have h := _root_.GlobalTheory.IterationConvergence.main (z := (ψ y : ℂ)) fun n => by
    have := hs (hn n)
    simp only [Set.mem_ofPred_eq, AddChar.map_nsmul_eq_pow] at this
    simpa using this
  exact Circle.ext (by rw [h, Circle.coe_one])

theorem exists_hasConductor_of_continuous_ne_one (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ c : kˣ, HasConductor ψ c := by
  apply @GlobalTheory.SplitWeil.exists_hasConductor_of_continuous <;> assumption


theorem residue_eq_iff_valuation_lt (a b : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] a = IsLocalRing.residue 𝒪[k] b ↔ valuation k ((a : k) - b) < 1 := by
  apply @GlobalTheory.StepData.residue_eq_iff_lt <;> assumption


end DiscreteGroups.sglob.DzType
