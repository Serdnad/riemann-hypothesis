module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle018
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPotentialCharts
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.PotentialChartsRegularBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle149
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormula
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle148
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermOfRange
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartReg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.snc_model_embedded_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∃ R : AnLogRes (mCoordIdeal y) J e, IsEmbedded R.A (mCoordIdeal y) R.U R.lift := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem lie_generic_eigenspaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (A : HodgeCpt Y S x) (F₀ : Type) [Field F₀] (ξ₀ : Spec (CommRingCat.of F₀) ⟶ Y.X) (ι : F₀ →+* Ω), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f ι → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module F₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j₁ : Li₀ →+ A.Li) (V₀ : CMType H ⊕ CMType H → Submodule F₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (A.M.pt (j₁ e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left) ∧ IsExtOver ι j₁ ∧ (∀ s e, e ∈ V₀ s ↔ j₁ e ∈ A.Vgen s) ∧ ∀ s, LinearIndependent F₀ (b s) ∧ Submodule.span F₀ (Set.range (b s)) = V₀ s :=
  @PositivityTheory.Xgp.exists_flags_lie_compact_dominated

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_potential_charts_with_radii : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (r : Fin D.nCharts → (Fin D.n → ℂ) → ℝ), IsSmoothHerm ref → IsConjInvariantH ref → (∀ a t, 0 < r a t) → ∃ (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)) (κ : Equiv.Perm (Fin P.N)), ThRef M ref P.th ∧ Adapted M P S ∧ FromSnc M P ∧ SymmCharts M P κ ∧ ∀ j, ∃ (a : Fin D.nCharts) (t₀ : Fin D.n → ℂ) (ε : ℝ), ‖t₀‖ ≤ 1 / 2 ∧ 0 < ε ∧ 2 * ε ≤ r a t₀ ∧ ε ≤ 1 / 4 ∧ ((∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj ((D.chart a).γ (t₀ + (ε : ℂ) • t)) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • t)))) ∨ ∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • star t)))) := by
  first | exact @LevelTowerAlt.exists_potential_charts | exact LevelTowerAlt.exists_potential_charts
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.adapted_subsets_for_potential_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), IsSmoothHerm ref → ThRef M ref P.th → Adapted M P S → LogHom D ref.a w → ChartPsh D w → ChartCont D w → ChartBdd D w → ∃ B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData M.atlas, B.toPotentialCharts = P ∧ (∀ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), B.ph (M.proj z) = w z - Real.log (ref.h z)) ∧ (IsConjInvariantH ref → ConjOff D w → ∀ z ∈ mcPts (mCoordIdeal D.y), B.ph (M.proj (conjVec z)) = B.ph (M.proj z)) := by
  first | exact @LevelTowerAlt.potential_charts_regular_bound | exact LevelTowerAlt.potential_charts_regular_bound
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.regularized_hodge_height_limit : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb Bm : HermLine J) (Pn : ReciprocityTheory.AnForm.M.LocPot M.Xc) (i : ℕ) (f G₀ : M.Xc → ℝ) (g : ((Σ k, J k) → ℂ) → ℝ), ReciprocityTheory.AnForm.M.IsPotential M.atlas Pn → (∀ x, ∀ y₀ ∈ (Pn).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pn).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Pn).φ x y' - (fun z => Real.log (Nb.h z)) (s y') = (G y').re) → M.atlas.SmoothOn S.R.Yo f → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → Real.log (Bm.h z) = Real.log (S.ref.h z) + f (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)) → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → g z = G₀ (M.proj z)) → (∀ j, MeasureTheory.AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (MeasureTheory.volume.restrict (M.atlas.chart j).target)) → ReciprocityTheory.AnForm.M.MIntegrable M.atlas (positionPot S.R.th Pn f i) G₀ → ptsIntegral (mCoordIdeal D.y) (pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) g = ReciprocityTheory.AnForm.M.mInt M.atlas (positionPot S.R.th Pn f i) G₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem stepGap_eq_of_base_block : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (x₀ : BM.Rb.X) (z z' : (Σ k, ι k) → ℂ), x₀ ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z' ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → basePart M.blk z = basePart M.blk z' → (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → stepGap M BM p z = stepGap M BM p z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p x₀ z z' hx₀ hz hz' horb hbase hblk
  obtain ⟨l, hl⟩ := BM.O_cover x₀
  have hx : x₀ ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := ⟨hl, hx₀⟩
  have horb' : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.basePart M.blk z') (BM.Rb.lift x₀ x₀) := by
    rw [← hbase]
    exact horb
  have hbm : GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z = GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono M (BM.F l) p z' := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.baseMono
    rw [hbase]
  have hfs : (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z =
      (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm ι (M.dy p)).h z' := by
    show GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z =
      GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm (M.dy p) z'
    unfold GroundTheory.Heights₂.Heights.LowerBoundFree.refNorm
    refine Finset.prod_congr rfl (fun k _ => ?_)
    by_cases h0 : M.dy p k = 0
    · simp [h0]
    · have hcoord : ∀ i, z ⟨k, i⟩ = z' ⟨k, i⟩ := by
        intro i
        by_cases hk : M.blk p = some k
        · exact hblk k hk i
        · by_cases hb : ∀ p' : Ψ × Fin N, M.blk p' ≠ some k
          · exact congrFun hbase ⟨⟨k, hb⟩, i⟩
          · exfalso
            apply h0
            unfold GlobalTheory.CompanionTheory.Ar.PB.FlagModel.dy
            rw [dite_eq_right hb, if_neg hk]
      simp only [hcoord]
  have hh : Real.log ((BM.hom p).h z) = Real.log ((BM.hom p).h z') := by
    cases hp : M.blk p with
    | none =>
      rw [GlobalTheory.T.log_block_metric_off_boundary K ι Φ y Ψ N j M n BM p l x₀ z hp hx hz horb,
        GlobalTheory.T.log_block_metric_off_boundary K ι Φ y Ψ N j M n BM p l x₀ z' hp hx hz' horb', hbm, hbase]
    | some k₀ =>
      obtain ⟨I₀, hI₀, hne⟩ := GlobalTheory.T.block_metric_row_echelon_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hl hz horb
      obtain ⟨C, B, hCB⟩ := GlobalTheory.CompanionTheory.Ar.PB.StepW.GrChart.exists_isGrChart N j p.2 I₀ M.j_le hI₀
      have hfun : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z = GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' := by
        funext I
        unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.plk
        rw [hbase]
        simp only [hblk k₀ hp]
      have hne' : GlobalTheory.CompanionTheory.Ar.PB.StepW.plk M (BM.F l) k₀ z' I₀ ≠ 0 := by
        rw [← hfun]
        exact hne
      rw [GlobalTheory.T.block_metric_explicit_matrix_form K ι Φ y Ψ N j M n BM p k₀ l x₀ z I₀ C B hp hCB hx hz horb hne,
        GlobalTheory.T.block_metric_explicit_matrix_form K ι Φ y Ψ N j M n BM p k₀ l x₀ z' I₀ C B hp hCB hx hz' horb' hne', hfun, hbm]
  unfold GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap
  rw [hh, hfs]

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.flag_adjacent_two_frames_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep.normRhs_indep | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep.normRhs_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep.normRhs_indep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_change_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → FramesOK (aOf 𝔐 bW bO φ) x₀ m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_height_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ (h : ModelOK (aOf 𝔐 bW bO φ) x₀ m) (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∃ xdeg : CMType H × Fin (D.p + D.q) → (K₀ ⊕ StepIx (CMType H) D.p D.q) → ℤ, Fl.RootLines xdeg (fun _ => 1) ∧ ∀ τ i, (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) = -∑ k ∈ Finset.Iic i, xdeg (τ, k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)


theorem _root_.GlobalTheory.T.lintegral_fibre_logNorm_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.coefficients' : Coefficients := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Top.coefficients | exact GlobalTheory.CompanionTheory.Ar.PB.Top.coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Top.coefficients <;> assumption)
end

section


theorem _root_.GlobalTheory.T.levi_chart_regularity_statement_holds : GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.nbarLeviChartReg | exact GlobalTheory.CompanionTheory.Ar.Giv.nbarLeviChartReg | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.nbarLeviChartReg <;> assumption)
end
