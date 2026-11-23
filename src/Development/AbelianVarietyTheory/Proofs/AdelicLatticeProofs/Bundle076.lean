module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Formalism.UnipotentAdelicQuotients.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle051
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.np_of_finrank_two' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_finrank_two | exact GlobalTheory.CNorm.np_of_finrank_two | (intros; apply GlobalTheory.CNorm.np_of_finrank_two <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.np_of_odd_prime_degree' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_odd_prime_degree | exact GlobalTheory.CNorm.np_of_odd_prime_degree | (intros; apply GlobalTheory.CNorm.np_of_odd_prime_degree <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem _root_.GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)), IsStdChar D ψ (-1) → (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)) → (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0) → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ) → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T x ∈ Λ ↔ ∀ y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T y ∈ Λ → ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  first | exact @GlobalTheory.RatSelfDual.finRat_mem_iff | exact GlobalTheory.RatSelfDual.finRat_mem_iff | (intros; apply GlobalTheory.RatSelfDual.finRat_mem_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem _root_.GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) ∧ ∀ w z : RW T S, (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z - Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)) + Complex.I * (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (jO S T sS sT z) - Real.pi * Complex.I * (omO S T w (jO S T sS sT z) : ℂ) * f (iotaW σ T S w)) = 0 := by
  first | exact @GlobalTheory.VacUnique.Ann.vacuum_annihilation | exact GlobalTheory.VacUnique.Ann.vacuum_annihilation | (intros; apply GlobalTheory.VacUnique.Ann.vacuum_annihilation <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem classNumberFinite_holds : HeckeCharacterZeroLocus.ClassNumberFinite := by
  classical
  intro F _ _ n S hS U hUo _
  obtain ⟨T₀, hT₀, hx⟩ := GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL F n S (fun B _ _ =>
    ⟨(hS B).1, fun g h hg hh => (hS B).2.1 g hg h hh, fun g hg => (hS B).2.2 g hg⟩)
  have hK := GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup F n S (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
    (fun g => Iff.rfl)
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.compact_meets_finitely_many_leftCosets_open _ U _ hUo hK
  refine ⟨Finset.image₂ (fun (s : T₀) (t : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) =>
    (⟨s.1, hT₀ s.1 s.2⟩ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) * t) T₀.attach T₁, ?_⟩
  intro x
  obtain ⟨γ, hγ, s, hs, k, hk, hki, hxe⟩ := hx x.1 x.2
  obtain ⟨t, ht, u, hu, hke⟩ := hT₁ ⟨k, hk⟩ hki
  refine ⟨γ, hγ, _, Finset.mem_image₂_of_mem (Finset.mem_attach T₀ ⟨s, hs⟩) ht, u, hu, ?_⟩
  have hke' : k = t.1 * u.1 := congrArg Subtype.val hke
  rw [hxe, hke']
  simp only [Subgroup.coe_mul, mul_assoc]

end GlobalTheory
end
