module

import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle065
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle036
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle068
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle020
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DimZero

theorem isIso_hom_of_relDim_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension 0 A.hom) : IsIso A.hom := by
  apply GlobalTheory.ZM.Model.isIso_of_dim_zero <;> assumption

theorem over_hom_eq_of_mono {S : Scheme.{0}} {T A : Over S} [Mono A.hom] (x y : T ⟶ A) : x = y := by
  ext1
  rw [← cancel_mono A.hom, Over.w x, Over.w y]

theorem eq_one_of_g_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (hg : P.g = 0) (z : sp (R₀ := R) R ⟶ P.A) :
    z = 1 := by
  have hd : SmoothOfRelativeDimension 0 P.A.hom := hg ▸ P.smoothDim
  haveI := isIso_hom_of_relDim_zero P.A P.isAb hd
  exact over_hom_eq_of_mono _ _

end GlobalTheory.CompanionTheory.Ar.DimZero
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.family_hodge_lattice_data : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I → ∃ D : ConjData C p O d, (∀ a, D.ρH a = rhoH F.B a) ∧ ∀ i y, y ∈ D.H i ↔ y ∈ stdLat (C.v i).valuationSubring.toSubring (transH (F.φ i) (F.ψ i) (F.lam i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.family_conj_H_lattices | exact GlobalTheory.CompanionTheory.Ar.Flat.family_conj_H_lattices | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.family_conj_H_lattices <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem setCrofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  intro n e δ h W f hW hf hδ A hA hAs
  have hle : e + 1 ≤ n := chowGroups_le hW hf hδ
  have hδpos : 1 ≤ δ := ChowDegreePos.proof n (e + 1) δ W f (Nat.succ_pos e) hW hf hδ
  have hfib := ConeFibreDegree.full n e δ h W f hW hf hδ
  have hfin : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)),
      fibreCount h W π w ≠ ⊤ := by
    filter_upwards [hfib] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top δ
  obtain ⟨K, hK0, hKtop, hK⟩ := GlobalTheory.T.hausdorff_cone_ball_measure n (e + 1) (Nat.succ_pos e) hle
  have hball : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤ :=
    ConeBallFinite.full n e h W f hW hf
  have hmass : ∀ B : Set (EuclideanSpace ℂ (Fin n)),
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} < ⊤ := fun B =>
    lt_of_le_of_lt (measure_mono (show _ ⊆ coneBall h W from fun y hy => And.intro hy.1 hy.2.1)) hball

  have key : ∀ B : Set (EuclideanSpace ℂ (Fin n)), IsOpen B → IsScaleStable B →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
          cntOver (coneSet h W ∩ B) π (firstCoordVec (e + 1)) =
      K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} := by
    intro B hB hBs
    have h1 := hK h W hW hfin B hB.measurableSet
      (fun y hy t ht => by
        have := hBs y hy (t : ℂ) (by exact_mod_cast ht.ne')
        simpa using this) (hmass B)
    have h2 := GlobalTheory.T.ball_average_fibre_count n e (coneSet h W ∩ B)
      ((isScaleStable_coneSet h hW).inter hBs) (isSigmaCompact_cone_inter h W hB) id measurable_id
    simp only [id] at h2
    rw [← h2, h1]
  have hΓ : gaussM (e + 1) n Set.univ = ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π := by
    rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcnt : ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
      cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ * (δ : ℝ≥0∞) := by
    rw [hΓ, ← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top δ)]
    refine lintegral_congr_ae ?_
    filter_upwards [GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ] with π hπ
    have : cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) = (δ : ℝ≥0∞) := by
      rw [Set.inter_univ, cntOver]
      have : (ptsOver (coneSet h W) π (firstCoordVec (e + 1))).encard = δ := hπ
      rw [this]
      simp
    rw [this]
  have hcb : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ Set.univ} = coneBall h W := by
    ext y
    simp [coneBall, coneSet]
  have hmf : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) =
      (δ : ℝ≥0∞) * planeMass n e :=
    ConeMassOfFibre.full n (e + 1) δ h W hW hfib
  have hV0 : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top δ

  have hVΓ : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * gaussM (e + 1) n Set.univ =
      K * planeMass n e := by
    have h0 := key Set.univ isOpen_univ (fun _ _ _ _ => Set.mem_univ _)
    rw [hcnt, hcb, hmf] at h0
    refine (ENNReal.mul_left_inj hδ0 hδtop).1 ?_
    rw [mul_assoc, h0]
    ring
  have hA1 := key A hA hAs
  refine (ENNReal.mul_right_inj hV0 hVtop).1 ?_
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * (planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)))
      = planeMass n e * (volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1))) := by ring
    _ = planeMass n e * (K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A}) := by rw [hA1]
    _ = (K * planeMass n e) * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by ring
    _ = _ := by rw [← hVΓ]; ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof)
    (GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft.proof GlobalTheory.T.pair_number_pullback
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.BirationalJoin.proof)

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement :=
  PositivityTheory.Xgn.A_s_joinright.of_pullback GlobalTheory.T.pair_number_pullback

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight
end

section


theorem _root_.GlobalTheory.T.dual_stacked_exceptional_chart : GroundTheory.Heights₂.Heights.DualStackedExcChart.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem _root_.GlobalTheory.T.kleiman_nef_criteria_hold : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | exact GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem _root_.GlobalTheory.T.siu_inequality_integral_holds : SiuZStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.siuZ | exact GlobalTheory.CompanionTheory.Ar.Giv.siuZ | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.siuZ <;> assumption)
end
