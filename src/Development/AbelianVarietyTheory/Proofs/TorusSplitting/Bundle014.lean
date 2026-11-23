module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrame
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periodTorus_isTorusAt_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (T : I2.PT E) (ψ : (Fin Uw.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → IsTorusOf (Uw.F.Di (Uw.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (Uw.e j).1) (Uw.Pm k x) Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ (∀ th, T.ph th = I2.phiFD (U.X k) th x.1) ∧ ∀ m, (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ τ, T.dim τ ≤ m := by
  first | exact @GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf | exact GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf | (intros; apply GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

open scoped Pointwise

theorem phiC_smul_of_nonneg {E : Type} [Field E] [NumberField E] (cj : E → E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (b : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X) {t : ℝ} (ht : 0 ≤ t) :
    Formalism.MainNotions.ModuliIntegralCharts.phiC cj (t • b) = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj b := by
  rw [phiC_eq_sInf, phiC_eq_sInf, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ht]
  congr 1
  ext x
  constructor
  · rintro ⟨l, h1, h2, rfl⟩
    exact ⟨l b, ⟨l, h1, h2, rfl⟩, (map_smul l t b).symm⟩
  · rintro ⟨_, ⟨l, h1, h2, rfl⟩, rfl⟩
    exact ⟨l, h1, h2, (map_smul l t b).symm⟩

theorem phiC_smul_pull : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (X X' : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X'] [Module (𝓞 E) X'] (e : X ≃ₗ[𝓞 E] X') (β' : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X') (t : ℝ), 0 ≤ t → ∃ β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X, (∀ a b, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a b = t * (β' : X' →ₗ[ℤ] X' →ₗ[ℤ] ℝ) (e a) (e b)) ∧ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β' := by
  intro E _ _ cj X X' _ _ _ _ e β' t ht
  refine ⟨t • pullS cj e β', fun a b => ?_, ?_⟩
  · rw [← pullS_apply cj e β' a b]
    rfl
  · rw [phiC_smul_of_nonneg cj _ ht, phiC_pull]

end GlobalTheory.EtaVal
end
