module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle095
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Htat

theorem lie_bc_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (PositivityTheory.HtPt.Htat.lie_proj S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  change _ ≫ _ = _ ≫ _ at h
  rw [Category.comp_id] at h
  exact h

end PositivityTheory.HtPt.Htat
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siua

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

theorem siu_kodaira_of
    (h : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  intro hA hC K _ ι _ Ω _ _ y D a hD hV _ hN hg
  let _ : DecidableEq K := fun x y => Classical.propDecidable (x = y)
  have : Nonempty K := hV.1
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hI : genIdeal y = mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
  have hP := isProjVarF_map_of_isArithVar hV
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  have hdim : FieldNumbers.relDim (mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
  have hnef : IsNef ℚ y a := fun W hW hle hW1 =>
    NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hN W
      ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
      (hI.le.trans hle)
  have hpos : 0 < NumbersDVR.intNum ℚ (mIdealOver ℚ y) (fun _ : Fin (d + 1) => a) := by
    rw [← hI]; exact hg
  obtain ⟨k, hk, σ, hσ, hσ0⟩ := h hA hC ℚ K ι Ω y d a hnz hdim hnef hpos
  refine ⟨k, σ, hk, hσ0, fun c hc => ?_⟩
  have h1 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hσ c) hc
  have h2 : σ * ∏ j, y ⟨j, c j⟩ ^ (-(k • a - 1) j) ∈ chartRingOver ℚ y c := h1
  have h3 : ∀ j, -(((1 : ℕ) : ℤ) * ((k : ℤ) • a - 1) j) = -(k • a - 1) j := fun j => by simp
  simp only [h3]
  exact h2

end PositivityTheory.HtPt.Siua
end
