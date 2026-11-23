module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle011

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.WeightProbe
variable {S : Scheme.{0}}

theorem exists_symLift_top (P : PolAV S) {N : ℕ} (hN : Odd N) {T : Over S} (x : T ⟶ P.A) (hx : x ^ N = 1) :
    ∃ U : ThetaGrp P.A P.L N T, SymLift P.A P.L N N x U := by
  have g := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have lft := (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube
    GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2
  have neg := GlobalTheory.exists_gen_negLB g
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local g P.isAb P.isLB hN
    ((GlobalTheory.symLift_odd g lft neg).1 S P N hN T x hx).1
  obtain ⟨nu, hnu⟩ := neg S P N T
  exact SymLiftOdd.exists_symLift g P.isAb P.isLB hN hx θ hθ hnu


open GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank VVCompare CommPairing in
theorem act_pull (P : PolAV S) {N : ℕ} (hN : Odd N) {T T' : Over S} (u : T' ⟶ T) {x : T ⟶ P.A}
    {θ : ThetaGrp P.A P.L N T} {θ' : ThetaGrp P.A P.L N T'} (H : SymLift P.A P.L N N x θ)
    (H' : SymLift P.A P.L N N (u ≫ x) θ') {s t : LB.Sec (LPow P.A P.L N T)} (a : IsActOf P.A P.L N θ s t) :
    IsActOf P.A P.L N θ' (pullS P.A N u s) (pullS P.A N u t) := by
  obtain ⟨ξ, Hξ, v⟩ := SymLiftGlobal.exists_symLift_pull_val P.isLB u H
  have c := SymLiftOdd.symLift_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns P.isAb P.isLB hN θ' ξ H' Hξ
  refine VVCompare.isTwistPull_of_sv P.A P.isLB θ'.isGen fun y J hJ => ?_
  have e : tval θ' (𝟙 _) y J = tval θ (𝟙 _ ≫ (u ▷ P.A).left) y J := (val_corr hJ c _).trans (v _ _ y J hJ)
  have e' : (𝟙 _ ≫ (translT P.A θ'.pt).left) ≫ (u ▷ P.A).left =
      (𝟙 _ ≫ (u ▷ P.A).left) ≫ (translT P.A θ.pt).left := by
    rw [H'.pt_eq, H.pt_eq, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  rw [VVCompare.sv_pullS P.A _ u t _ y hJ, VVCompare.sv_pullS P.A _ u s _ y hJ, e']
  exact (VVCompare.sv_of_isTwistPull P.A a _ y hJ).trans (congrArg (fun q => Units.val q * _) e.symm)

end GlobalTheory.WeightProbe
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TwistSpanExample

theorem span_holds : TwistBCSpanStatement := twistBCSpan_of GlobalTheory.twistBaseChange

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) {k : ℕ}

end GlobalTheory.TwistSpanExample
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelMove

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)

section Identification

variable (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
  (oP : letI := H.starRing; P.toPre.OAct (𝓞 E))

end Identification

theorem exists_lattice_part {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 0 < n) (y : D.X) : ∃ p : QkPt D F n, p.y = y :=
  exists_qkPt GlobalTheory.abelianSchemeLaws_all.1.mulN (Or.inr GlobalTheory.abelianSchemeLaws_all.1.polBaseChange) hB hn.ne' y

end GlobalTheory.LevelMove
end
end

section

noncomputable section

namespace GlobalTheory.ReadingIndependence

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Theta Formalism.BasicNotions.TH

theorem jInjRd_of_laws {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : JInjRd T j a n := by
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  refine jInjRd_of_wt T hM hj a n (fun p y ψ => ?_)
    (GlobalTheory.Frames.algebraic_laws hS _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ _ _ _ (T.Q.Xo j) T.Q.c _ _ ψ y

section General

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ}
  {X : Comp → Data E r} (V : HSp D) (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
  (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)

end General

end GlobalTheory.ReadingIndependence
end
end
