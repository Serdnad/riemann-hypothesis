module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle623
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle624
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle625
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle485
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle530
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle626
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle531
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridSquareFlipSmallRouteEqInvSmulBigRoute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Irr

variable {D : D7}

theorem thPair_self_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (v : VolM D T.rank S.rank) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) :
    thPair v.μ v.𝓕 f₀ f₀ ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D T.rank S.rank) := i5
  haveI : Countable (ratMx D T.rank S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := v.covol
  haveI := hμ
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have e : ∀ w, f₀ w * star (f₀ w) = ((‖f₀ w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
  have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (v.μ.restrict v.𝓕) :=
    Integrable.of_bound (hf.cont.norm.pow 2).measurable.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2)
  intro h0
  have h2 : (∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ) = 0 := by
    have : thPair v.μ v.𝓕 f₀ f₀ = ((∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ : ℝ) : ℂ) := by
      unfold thPair
      simp_rw [e]
      exact integral_ofReal
    rw [this] at h0
    exact_mod_cast h0
  have h3 : ∫⁻ w in v.𝓕, ‖f₀ w‖ₑ ^ 2 ∂v.μ = 0 := by
    have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [en]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => by positivity), h2,
      ENNReal.ofReal_zero]
  exact hne (GlobalTheory.OrientedHeis.eq_zero_of_lintegral_eq_zero (ratMx D T.rank S.rank) v.μ v.𝓕 hF f₀ hf.cont
    (fun γ hγ w => GlobalTheory.OrientedHeis.theta_norm_periodic hψ hf γ hγ w) h3)

theorem irr : ∀ D : D7, Irr D := by
  intro D ψ hψ S T Γ ℓ hℓ f₀ hf₀ hne hann f hf
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI := v.covol.1
  haveI : SFinite v.μ := inferInstance
  obtain ⟨hint, hmoy⟩ := GlobalTheory.T.moyal_orthogonality_heisenberg_thetaFunctions D ψ hψ S T v f f₀ hf.1 hf₀.1
  have heq : (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) =
      thPair v.μ v.𝓕 f₀ f₀ • f := funext fun x => by rw [hmoy x]; rfl
  have hth : IsThetaFunO ψ S T (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) := by
    rw [heq]; exact GlobalTheory.OrientedHeis.theta_smul _ hf.1
  have hsup := hℓ.sup f₀ hf₀.1 v.μ _ hint hth
  rw [heq, hℓ.smul _ _ hf.1] at hsup
  have hz : ∀ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * ℓ (heisO ψ S T w f₀) = 0 := fun w => by
    by_cases hw : w ∈ Ann ψ S T Γ
    · rw [hann w hw, mul_zero]
    · rw [(GlobalTheory.T.heisenbergVacuumCommutant_preserves_latticeVacua D ψ hψ S T Γ).2.2 v f f₀ hf hf₀ w hw, zero_mul]
  simp_rw [hz, integral_zero] at hsup
  exact (mul_eq_zero.1 hsup).resolve_left (thPair_self_ne_zero hψ v hf₀.1 hne)

end GlobalTheory.Irr
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.offIdempotent_finitePoint_mem_completedTensorLattice : ∀ (D : D7) (S T : HSp D) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ (L : Lt D.host.E T.rank) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E), y ∈ tens (stdL D.host.E S.rank) L → GlobalTheory.LiftLevel.partAt (1 - e - cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L)) := by
  first | exact @GlobalTheory.LiftLevel.OffTens.partAt_finW_off_mem_hatA | exact GlobalTheory.LiftLevel.OffTens.partAt_finW_off_mem_hatA | (intros; apply GlobalTheory.LiftLevel.OffTens.partAt_finW_off_mem_hatA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.idempotentPart_finitePoint_mem_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  first | exact @GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh | exact GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh | (intros; apply GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_idele_generates_polarisationIdeal_conjPlaces : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ a : AE D, (∃ b : AE D, a * b = e) ∧ GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a := by
  first | exact @GlobalTheory.LiftLevel.exists_isGen | exact GlobalTheory.LiftLevel.exists_isGen | (intros; apply GlobalTheory.LiftLevel.exists_isGen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.latticeVector_adjointRow_integral : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) := by
  first | exact @GlobalTheory.LiftDat.rowAdj_isIntM_of_mem | exact GlobalTheory.LiftDat.rowAdj_isIntM_of_mem | (intros; apply GlobalTheory.LiftDat.rowAdj_isIntM_of_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      ∃ c : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c • Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  first | exact @GlobalTheory.ExpansionInvariance.vac_move_low | exact GlobalTheory.ExpansionInvariance.vac_move_low | (intros; apply GlobalTheory.ExpansionInvariance.vac_move_low <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Chain GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors : ∀ (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (D : D7) (k : Fin D.R.m) (a b : ℕ),
    a = k → b = (k : ℕ) + 1 → ∀ (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f →
    ∀ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ (h : KSm M) (h' : KSm M'), LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, It φ (inclK h' y) = x} := by
  first | exact @GlobalTheory.Chain.KFinOnto.itW_onto_kFin | exact GlobalTheory.Chain.KFinOnto.itW_onto_kFin | (intros; apply GlobalTheory.Chain.KFinOnto.itW_onto_kFin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.weilAction_moves_standardVacuum_topNode_eq_char_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  first | exact @GlobalTheory.TopLevelInv.vac_move_high_eq | exact GlobalTheory.TopLevelInv.vac_move_high_eq | (intros; apply GlobalTheory.TopLevelInv.vac_move_high_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  exact @GlobalTheory.SquareAgree.algVec_correspond
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.lowerTowerLifts_vanish_on_fock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X := by
  first | exact @GlobalTheory.LowerMembersRule.lowFock | exact GlobalTheory.LowerMembersRule.lowFock | (intros; apply GlobalTheory.LowerMembersRule.lowFock <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RightArrowCusp

theorem vert_par : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ i j : ℕ, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F _ G hG i j hi hj
  cases i with
  | zero =>
    rw [GlobalTheory.Grid.parV_zero D hj]
    rcases j with _ | j
    · rfl
    · show (if j + 1 < D.R.m then GlobalTheory.Grid.nodeY R (j + 1) else GlobalTheory.Grid.nodeX R).S = _
      split_ifs with h
      · simp [Nat.min_eq_left hj]
      · have : j + 1 = D.R.m := by omega
        rw [this]
  | succ i => exact (hG.spaces.vert i j hi hj).par

theorem meas_haar_fund : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → (G.meas t i j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V i j).V) (G.meas t i j).fd (G.meas t i j).ν := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F hC G hG t i j hi hj
  have aux : ∀ {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop) K, m.Is df K →
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
    intro N m df K h
    by_cases hd : df
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have cst : ∀ {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat),
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ S.V) m.fd m.ν →
      (GlobalTheory.Grid.Node.MeasDat.cast e m).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ S'.V) (GlobalTheory.Grid.Node.MeasDat.cast e m).fd (GlobalTheory.Grid.Node.MeasDat.cast e m).ν := by
    intro S S' e m h
    subst e
    exact h
  rcases i with _ | i
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col 0 (Nat.zero_le _))
    · show (GlobalTheory.Grid.meas0 R t j).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ (GlobalTheory.Grid.row0 R (j + 1)).V) (GlobalTheory.Grid.meas0 R t j).fd (GlobalTheory.Grid.meas0 R t j).ν
      unfold GlobalTheory.Grid.meas0
      split_ifs with h
      · apply cst
        by_cases h2 : j + 1 + 1 < D.R.m
        · have := hC.models.νY t (j + 1) h2
          exact ⟨this.1.1, this.2⟩
        · have := hC.models.νY' t
          have e : D.R.m - 1 = j + 1 := by omega
          rw [e] at this
          exact ⟨this.1.1, this.2⟩
      · apply cst
        have := hC.models.νX t
        exact ⟨this.1.1, this.2⟩
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col (i + 1) hi)
    · exact aux _ _ _ (hG.meas.vert i j hi hj)

theorem thetaKO_eq_kerA : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ) (Ls : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (hs1 : Submodule.IsLattice D.host.E Ls) (hs2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT Ls) (Lt : Submodule (𝓞 D.host.E) (G'.V (.grid (i + 1) j)).V) (ht1 : Submodule.IsLattice D.host.E Lt) (ht2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid (i + 1) j)).hT Lt) (ω : GlobalTheory.Grid.WRep (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2) (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2)), HEq (ω.toSgn true) (W.om (.chi i j)) → ∀ (Φ : Sch G' (.right i j)) (g : GA D (G'.V (.grid i j))) (h : GA D (G'.V (.grid (i + 1) j))), thetaKO ω h g Φ = W.kerA (.right i j) Φ g h := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j Ls hs1 hs2 Lt ht1 ht2 ω hω Φ g h
  have e : ω.toSgn true = W.om (.chi i j) := eq_of_heq hω
  show (ω (h, g)) Φ 0 = (W.om (.chi i j) (negGA _ h, g)) Φ 0
  rw [← e]
  rfl

theorem isThetaFunO_neg_reLat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S U : HSp D) (L : Submodule (𝓞 D.host.E) S.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) (L' : Submodule (𝓞 D.host.E) U.V) (h1' : Submodule.IsLattice D.host.E L') (h2' : Formalism.HermitianLatticesTheory.IsUnimodular U.hT L') (Φ : WO (negSp S) U → ℂ), IsThetaFunO ψ (negSp S) U Φ → IsThetaFunO ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat S L h1 h2)) (GlobalTheory.VolRatioCompare.reLat U L' h1' h2') Φ := by
  intro D ψ S U L h1 h2 L' h1' h2' Φ h
  exact ⟨h.1, h.2, h.3, h.4⟩

theorem isCuspListed_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D) (X : Node) (c : ℂ) (F : Fn G X), IsCuspListed θ X F → IsCuspListed θ X (c • F) := by
  intro D T L sc G θ X c F ⟨h1, h2, h3⟩
  refine ⟨Formalism.IndefR.Mult.isAutFunSm_smul _ _ h1 c, Formalism.IndefR.Mult.isCuspFun_smul _ h2 c, ?_⟩
  rcases X with ⟨i, j⟩ | i | j
  · intro τ
    have e : (fun g => star ((c • F) g)) = star c • fun g => star (F g) := by
      funext g; simp [Pi.smul_apply, smul_eq_mul, star_mul', mul_comm]
    show IsTypeAt _ _ _ _ fun g => star ((c • F) g)
    rw [e]
    exact GlobalTheory.Mem.Th.isTypeAt_smul _ (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)

theorem kerA_mul_left_invariant : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ Φ : Sch G' (.right i j), IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) Φ → ∀ F : Fn G' (.grid i j), IsCuspListed W.θ (.grid i j) F → ∀ h, ∀ γ ∈ GQ (G'.V (.grid i j)), ∀ g, W.kerA (.right i j) Φ (γ * g) h * F (γ * g) = W.kerA (.right i j) Φ g h * F g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j hi hj Φ hΦ F hF h γ hγ g
  have hω := W.om_is (.chi i j) (by first | exact ⟨hi, hj⟩ | exact ⟨hj, hi⟩ | simpa using ⟨hi, hj⟩)
  show thetaKO (W.om (.chi i j)) (negGA _ h) (γ * g) Φ * F (γ * g) = thetaKO (W.om (.chi i j)) (negGA _ h) g Φ * F g
  rw [GlobalTheory.UpArrowConv.thetaKO_left_snd hω hΦ _ γ hγ g, hF.1.left γ hγ g]

theorem isAutFunSm_reLat_iff : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (φ : GA D V → ℂ), IsAutFunSm θ (GlobalTheory.VolRatioCompare.reLat V L h1 h2) φ ↔ IsAutFunSm θ V φ := by
  intro D θ V L h1 h2 φ
  exact ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
    fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem isCuspOfType_iff_isCuspListed : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}, sc.cGap = 1 → ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (L : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT L) (Mo : Formalism.IndefR.Mult.DSModel (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) (GlobalTheory.Grid.parV D i j)) (Λ : Submodule (𝓞 D.host.E) (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank → D.host.E)) (β : GL (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank) (Lev.EAf D)) (φ : Fn G' (.grid i j)), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ ⟨GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2, GlobalTheory.Grid.parV D i j, Mo, Λ, β⟩ φ ↔ IsCuspListed W.θ (.grid i j) φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hsc G' W hW i j hi hj L h1 h2 Mo Λ β φ
  rw [hW.θ]
  refine and_congr (isAutFunSm_reLat_iff R.θ _ L h1 h2 φ) (and_congr Iff.rfl ?_)
  show (∀ τ, IsTypeAt R.θ (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) τ (GlobalTheory.Grid.parV D i j τ) φ) ↔
    ∀ τ, IsTypeAt R.θ (G'.V (.grid i j)) τ (Node.par D sc.cGap (.grid i j) τ) fun g => star (φ g)
  refine forall_congr' fun τ => ?_
  rw [hsc]
  have hp : GlobalTheory.Grid.parV D i j τ = Formalism.IndefR.Mult.dualPar (GlobalTheory.ChiGrid.parV D 1 i j τ) := by
    unfold GlobalTheory.Grid.parV GlobalTheory.ChiGrid.parV
    rw [GlobalTheory.GridParDCount.grid_eq_num D τ]
  rw [hp]
  exact GlobalTheory.T.isTypeAt_dualPar_iff_star_isTypeAt R.θ (G'.V (.grid i j)) τ _ φ


open GlobalTheory.GridJoin in
theorem lift_right_of_smooth {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} (hsc : sc.cGap = 1) {G' : GridData R.toLevCh sc} (W : G'.Weil)
    (hW : W.Over R) (ρ : RealMatch W) (hρ : RealMatch.Over R ρ) (M : Vol G') (t : T) (hM : M.Is t) (i j : ℕ) (hi : i < D.R.m)
    (hj : j ≤ D.R.m) (Ns Nt : GlobalTheory.Grid.Node D) (hs : SameSp (G'.V (.grid i j)) Ns.V) (ht : SameSp (G'.V (.grid (i + 1) j)) Nt.V)
    (hSs : Ns.S = GlobalTheory.Grid.parV D i j) (hSt : Nt.S = GlobalTheory.Grid.parV D (i + 1) j) (m : Ns.MeasDat) (hm1 : m.ν.IsHaarMeasure)
    (hm2 : IsFundamentalDomain (GQ Ns.V) m.fd m.ν) (ω : GlobalTheory.Grid.WRep Nt.V Ns.V) (hω : HEq (ω.toSgn true) (W.om (.chi i j)))
    (H : ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg Nt.V) Ns.V Φ →
      GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsSmooth R.θ (A := Ns) (B := Nt) m fun h g => thetaKO ω h g Φ) :
    ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f →
      ∀ (Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank) (F : Fn G' (.grid i j)), IsCuspListed W.θ (.grid i j) F →
        LiftConv W M (.right i j) (W.fock (.chi i j) f Q) F ∧
          IsCuspListed W.θ (.grid (i + 1) j) (liftA W M (.right i j) (W.fock (.chi i j) f Q) F) := by
  obtain ⟨Vs, Ss, Ms, Λs, βs⟩ := Ns
  obtain ⟨Vt, St, Mt, Λt, βt⟩ := Nt
  obtain ⟨Ls, hs1, hs2, rfl⟩ := hs
  obtain ⟨Lt, ht1, ht2, rfl⟩ := ht
  dsimp only at hSs hSt
  subst hSs hSt
  intro e he φ f hf Q F hF
  have hΦ0 := GlobalTheory.T.isThetaFunction_fock_vector_rightward_arrow hW ρ hρ t i j hi hj e he φ f hf Q
  have hΦ : IsThetaFunO R.ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2))
      (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2) (W.fock (.chi i j) f Q) :=
    hW.ψ ▸ isThetaFunO_neg_reLat W.ψ _ _ Lt ht1 ht2 Ls hs1 hs2 _ hΦ0
  have hK := thetaKO_eq_kerA W i j Ls hs1 hs2 Lt ht1 ht2 ω hω (W.fock (.chi i j) f Q)
  have hFs := (isCuspOfType_iff_isCuspListed hsc W hW i j hi.le hj Ls hs1 hs2 Ms Λs βs F).2 hF
  obtain ⟨hI, hT⟩ := H _ hΦ F hFs
  have hMX := (hM.vtx (.grid i j) ⟨hi.le, hj⟩).haar_fund
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_const_setIntegral_haar_fundamentalDomains_unitary (M.ν (.grid i j)) m.ν (M.fd (.grid i j)) m.fd hMX.1 hm1 hMX.2 hm2
  have key := fun h => hc (fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g) (kerA_mul_left_invariant W i j hi hj _ hΦ0 F hF h)
  have e2 : ∀ h, (fun g => thetaKO ω h g (W.fock (.chi i j) f Q) * F g) =
      fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g := fun h => funext fun g => by rw [hK g h]
  refine ⟨fun h => (key h).1.2 (e2 h ▸ hI h), ?_⟩
  have e : liftA W M (.right i j) (W.fock (.chi i j) f Q) F =
      c • fun h => ∫ g in m.fd, thetaKO ω h g (W.fock (.chi i j) f Q) * F g ∂m.ν := by
    funext h
    rw [liftA_apply, (key h).2]
    exact congrArg (c * ·) (congrArg (fun φ : GA D (G'.V (.grid i j)) → ℂ => ∫ g in m.fd, φ g ∂m.ν) (e2 h).symm)
  rw [e]
  exact isCuspListed_smul _ _ c _ ((isCuspOfType_iff_isCuspListed hsc W hW (i + 1) j hi hj Lt ht1 ht2 Mt Λt βt _).1 hT)

end GlobalTheory.RightArrowCusp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.gridSquareFlip_smallRoute_eq_inv_smul_bigRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G ((A.comp (routeSmall t i j)).comp Bp)) (Tl : ∀ w, (locGrid G t w).Args → ℂ), (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t i j)).comp Bp)) (Tl w)) → (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp)) ((locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w))) → GlobalTheory.FlipRun.RepFin B ρ t _ τ Tl → ∃ τ' : TotT G ((A.comp (routeBig t i j)).comp Bp), GlobalTheory.FlipRun.RepFin B ρ t _ τ' (fun w => (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w)) ∧ ∀ M : Vol G, M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F ∧ liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F := by
  first | exact @GlobalTheory.FlipRun.oneFlip | exact GlobalTheory.FlipRun.oneFlip | (intros; apply GlobalTheory.FlipRun.oneFlip <;> assumption)
end
