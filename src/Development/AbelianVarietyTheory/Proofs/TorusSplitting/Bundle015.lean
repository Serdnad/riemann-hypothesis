module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symB_phiC_eq_mul_of_pullback : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (X X' : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X'] [Module (𝓞 E) X'] (e : X ≃ₗ[𝓞 E] X') (β' : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X') (t : ℝ), 0 ≤ t → ∃ β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X, (∀ a b, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a b = t * (β' : X' →ₗ[ℤ] X' →ₗ[ℤ] ℝ) (e a) (e b)) ∧ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β' := by
  first | exact @GlobalTheory.EtaVal.phiC_smul_pull | exact GlobalTheory.EtaVal.phiC_smul_pull | (intros; apply GlobalTheory.EtaVal.phiC_smul_pull <;> assumption)
end

section

set_option autoImplicit false

namespace GlobalTheory

theorem semichar_unit_frame : ReciprocityTheory.ChartRestriction.G.PullbackSections.PPSemicharSt := by
  intro E _ _ _ H Dw l Xo c σ r U _ k x W Wu _ a
  have hF : GlobalTheory.EtaAn.AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr :=
    ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, fun j hj => by
      rw [← W.pt]; exact Wu.c5 j hj, Wu.c6⟩
  have h : Wu.χl (W.Pm a) =
      ((Int.negOnePow ((W.F.Di (W.ik k)).EF a (H.w0 • a)) : ℤˣ) : ℤ) :=
    GlobalTheory.ahFrame_factor_eq_negOnePow E H Dw l Xo _ _ _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per hF a
  rw [h, Int.cast_negOnePow]

end GlobalTheory
end
