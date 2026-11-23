module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle259
import Formalism.RealPlaceAnalysis.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle054
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeneratorCompatibilityCompositePullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest Cas etr epow)

namespace GlobalTheory.CompanionTheory.RgExhUnit

theorem etr_two_eq_cas {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : etr E 2 = Cas E := by
  simp [etr, Cas, epow]

theorem cas_apply_of_scalChar {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ)
    (hS : CompanionTheory.RgExh.ScalChar ⟨V, E, hE⟩ χ) (u : V) :
    Cas E u = (∑ a, χ a * χ a -
      ∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)) • u := by
  rcases n with _ | m
  · simp [Cas]
  · have h := GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli V m E χ u hE
      (fun Y => by
        have := LinearMap.congr_fun (hS Y) u
        simpa using this) 2
    rw [etr_two_eq_cas, GlobalTheory.CasimirEigen.gelfVal_two_eq] at h
    exact h

theorem re_sum_mul_self {n : ℕ} (χ : Fin n → ℂ) :
    (∑ a, χ a * χ a).re = ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Complex.mul_re, sq]

theorem unitIneq : CompanionTheory.RgExh.U.UnitIneq := by
  intro n
  refine ⟨∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a, ?_⟩
  intro ε V _ _ E hE χ γ u hU hS hu hK
  have h1 := Formalism.REAL.wdCas V n ε E γ u hE hU hK
  have hin : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [cas_apply_of_scalChar V E hE χ hS u, inner_smul_right, hin] at h1
  have h2 := congrArg Complex.re h1
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  have hsum : 0 ≤ ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    split_ifs <;> positivity
  have hrho : (∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)).re =
      ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.mul_re]
  have hc : (∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a) * ‖u‖ ^ 2 =
      (Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε)) * ‖u‖ ^ 2 -
        ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    rw [Complex.re_mul_ofReal, Complex.ofReal_re, Complex.sub_re, re_sum_mul_self, hrho] at h2
    exact h2
  have hnn : 0 ≤ Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    show 0 ≤ ∑ a, Formalism.REAL.rhoC ε a * Formalism.REAL.rhoC ε a
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have hle : ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a ≤
      Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    refine le_of_mul_le_mul_right ?_ hpos
    rw [hc]
    linarith
  show _ ≤ Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) + _
  linarith

end GlobalTheory.CompanionTheory.RgExhUnit
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.flat_bounded_acyclic_base_change : ∀ (R K : Type) [CommRing R] [CommRing K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p)) (hac : C.Acyclic), (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjFlat.acyclic_extendScalars_of_bounded_flat | exact GlobalTheory.CompanionTheory.PointSurjFlat.acyclic_extendScalars_of_bounded_flat | (intros; apply GlobalTheory.CompanionTheory.PointSurjFlat.acyclic_extendScalars_of_bounded_flat <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.lbIso_pull_of_generator_ratio_eq : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q), Flat g → LocallyOfFinitePresentation g → Surjective g →
    ∀ (M : LB P), M.IsLB → ∀ (N : LB Q), N.IsLB → ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∀ (T : LB.Gen (N.pull (g ≫ f))), T.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ Z), a ≫ g = b ≫ g → ∀ (w : W) (i : N.ι) (k : M.ι), f (g (a w)) ∈ N.U i → g (a w) ∈ M.U k →
        gm a w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹ =
          gm b w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹) →
      LBIso M (N.pull f) := by
  first | exact @GlobalTheory.CompanionTheory.RigGlue.lbIso_of_same_descent | exact GlobalTheory.CompanionTheory.RigGlue.lbIso_of_same_descent | (intros; apply GlobalTheory.CompanionTheory.RigGlue.lbIso_of_same_descent <;> assumption)
end
