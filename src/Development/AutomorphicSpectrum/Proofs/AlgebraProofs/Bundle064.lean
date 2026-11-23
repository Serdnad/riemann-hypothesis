module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle041
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle001
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionBallIndicator
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHolds
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFrameOfFullFlag
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFurtherTermIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle063
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SegreFlagIndepHomogeneousImpliesGeneral
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.FF

theorem places_form_curve : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 :=
  @PositivityTheory.HtPt.Cc.inh_ff

end GlobalTheory.CompanionTheory.Ar.FF
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → SubquotientStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate | exact GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.gaussian_projection_ball_indicator : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ y in coneSet h J ∩ A,
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      ∫⁻ y in coneSet h J ∩ A, tangentGaussProfile n m ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

theorem polyNum_eq_sum {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (V : Ideal (MRing ι F)) (e : ℕ)
    (hV : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V e) {N : ℕ} (d : Fin N → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (c n : ℕ) (Y : Fin n → K → ℤ) (hG : G.IsHomogeneous c)
    (hcn : c + n = e) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I V e (Fin.append d Y)
                              (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
      ∑ μ ∈ G.support, G.coeff μ * intNumL F V (classList d μ ++ List.ofFn Y) := by
  rw [SegreFlagIndep.prod_X_natAdd, SegreFlagIndep.polyNum_mul_monomial, SegreFlagIndep.monoList_ones]
  refine Finset.sum_congr rfl fun α hα => ?_
  congr 1
  have hdeg : α.degree = c := by
    have := hG (mem_support_iff.mp hα)
    rwa [Finsupp.degree_eq_weight_one]
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList d α ++ List.ofFn Y).length = e := by
    rw [List.length_append, SegreFlagIndep.length_monoList, hdeg, List.length_ofFn, hcn]
  rw [SegreFlagIndep.listNum, dite_eq_left hlen,
    Numbers.agree FieldNumbers.IntNumUnique.full (IntNumPoint.proof FieldNumbers.IntNumBase.full)
      FieldNumbers.IntNumBase.full I hI V e _ hV,
    BundleExamples.intNum_get_cast F V _ e hlen]
  refine FlagTypings.intNumL_perm F V (List.Perm.append_right _ ?_)
  rw [BundleExamples.monoList_eq]
  exact FlagTypings.monoList_perm d α

theorem segreFlagIndep (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι := by
  classical
  intro x e hV N E _ _ B fl₁ fl₂ I hI G hG c n Y hGc hcn
  obtain ⟨w, hw⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₁
  obtain ⟨v, hv⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₂
  rw [polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn, polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn]
  have hI' := VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι (pointIdeal F x)
  have hP : IsMultiProjPrime (pointIdeal F x) := ⟨hV.1.1, hI'.1 hV.1.2.1, hV.1.2.2⟩
  exact GlobalTheory.T.sum_intNumL_classList_eq_of_isSymmetric F Ω K ι x e hP hV.2 N E B w v _ _ hw hv c G hG hGc (List.ofFn Y)
    (by rw [List.length_ofFn]; omega)

end GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem flag_further_term_independent :
    GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagVerticalSymmetric.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagRestriction.proof
      FurtherIndep.segreFlagIndep)

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.field_extension_intersection_invariance : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁), IsModelOver (pointIdeal O (bcCoord x z)) d → ∀ (c : K → ℕ) (f : MRing ι O), IsMultiHomog f c → f ∉ (pointIdeal O x) → ∀ l : List (K → ℤ), l.length = d → (open Classical in cycEval (fun W => if (C ϖ : MRing (Sum.elim ι ι') O) ∈ W then vNumL W (l.map (pullDeg (K' := K'))) else 0) (divCycle (pointIdeal O (bcCoord x z)) (rename (liftVar ι') f))) = (modelDeg O x z : ℤ) * (open Classical in cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W l else 0) (divCycle (pointIdeal O x) f)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.field_extension_intersection_invariance | exact GlobalTheory.CompanionTheory.Relay.field_extension_intersection_invariance | (intros; apply GlobalTheory.CompanionTheory.Relay.field_extension_intersection_invariance <;> assumption)
end

section


theorem _root_.GlobalTheory.T.dual_stacked_exceptional_coords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords <;> assumption)
end

section


theorem _root_.GlobalTheory.T.dual_stacked_graph_bihomogeneous : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | exact GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_form_gauss_bound_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.NormFormGaussBound.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | exact GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem _root_.GlobalTheory.T.kleiman_genericPointSectionInput : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput | exact GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput | (intros; apply GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput <;> assumption)
end
