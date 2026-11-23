module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelValueRationalStep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMMulVecFix
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle470
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle461
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle475
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle457
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle469
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle136
import Formalism.LocalToGlobal.Columns.Bundle011
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle002
public import Formalism.LocalToGlobal.GroupLattices.ClassLocalOfEq
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
import Mathlib.RingTheory.Ideal.Int
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ w, ‖om (x * a, y * b) f w‖ ≤ C * ((1 + normInf θ S a) * (1 + normInf θ T b)) ^ N := by
  first | exact @GlobalTheory.Mem.LiftBound.om_growth | exact GlobalTheory.Mem.LiftBound.om_growth | (intros; apply GlobalTheory.Mem.LiftBound.om_growth <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC



theorem kerEnt_latT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, (∃ y ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat (i + 1)).L, ((I.tw l l0 Z).fm u μ).emb (i + 1) y = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c' ∧ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  intro B X I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi φ
  have hL1 := fun x => GlobalTheory.T.localisation_formLattice_iff_classValues_weylLattice (I.stp u μ (i + 1)) B.fields.emb (lamT (B.hcW u) (i + 1)) ((l.fmL u μ).fam (i + 1))
    B.places w _ (Pl.iL w) (Pl.iL_int w) x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun c' => ?_⟩

    · rw [← (((I.tw l l0 Z).fm u μ).emb_basis (i + 1)).2, ← ((((I.tw l l0 Z).fm u μ).lat (i + 1)).b.sum_repr y), map_sum]
      exact Submodule.sum_mem _ fun a _ => by
        rw [LinearMap.map_smulₛₗ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · obtain ⟨v', hv'⟩ := GlobalTheory.T.coefficientField_form_value_mem_polynomialModel I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi y c'
      exact ⟨v', hv', (GlobalTheory.T.mem_localisedWeylLattice_iff_targetPairing_integral I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (y.1 c') v' hv').1
        ((hL1 y).1 hy c')⟩
  · rintro ⟨hF, hc⟩
    obtain ⟨x, rfl⟩ := GlobalTheory.T.exists_coefficientField_form_of_polynomialModel_values I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi φ hF
      (fun c' => (hc c').imp fun _ h => h.1)
    refine ⟨x, (hL1 x).2 fun c' => ?_, rfl⟩
    obtain ⟨v', hv', hn⟩ := hc c'
    exact (GlobalTheory.T.mem_localisedWeylLattice_iff_targetPairing_integral I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (x.1 c') v' hv').2 hn

end GlobalTheory.Mem.Col2.TC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_polynomialModel_value_rational_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∃ v : ValQ O u μ i, evC O u μ i v = f := by
  first | exact @GlobalTheory.CmpEx.exists_valQ | exact GlobalTheory.CmpEx.exists_valQ | (intros; apply GlobalTheory.CmpEx.exists_valQ <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section



theorem GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (Lv : SymmetricTwistedLevelData W), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → I.StdLv l Z l0 Lv → (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) → ∃ (Pt : TwPTiedS Lv) (E : TwPEvzS Pt), TwPAtGS Pt ∧ I.StdP l Z l0 Pt E := by
  intro B X I hI hP l Z l0 inQ H F T J W Lv hQ hF hW hLv hTop
  have hQ' : ∀ a v, v ∈ T.Q a ↔ I.UnderQ a v := fun a v => (T.Q_iff a v).trans (hQ a v)
  have hC := fun u a => GlobalTheory.T.tuplePrimedSpaceClasses_level_and_comparison I hI hP l Z u a (T.Q a) (F u).clsP (hQ' a) (J.Q_off u a) (hF u).1.what₂
  choose K hLb hfin hrd hU hchi using hC
  have hV := fun u a => GlobalTheory.T.formsX_tupleChain_of_levelReading I hI hP l Z u a (T.Q a) (K u a) (hQ' a) (J.Q_off u a) (hrd u a)
  choose V hN hE using hV
  choose k hk hkT using hTop
  have hTil := fun u a ha h1 => GlobalTheory.Mem.Col2.TwP.til_tw I hI hP l Z hF hW hLv u a ha h1 (K u a) (hrd u a) (hk u a ha h1) (hkT u a ha h1)
  choose Tl hz hev using hTil
  choose jM hj0 hj1 hj2 hj3 hj4 using fun u a => GlobalTheory.Mem.Col2.PerConj.period_conj I hI hP l Z u a
  let Pt : TwPTiedS Lv :=
    { cls := fun u a _ => K u a
      Lb := fun u a _ => hLb u a
      chi_fin := fun u a _ => hfin u a
      val := fun u a _ => V u a
      norm := fun u a _ => hN u a
      til := fun u a ha h1 => Tl u a ha h1 }
  let E : TwPEvzS Pt :=
    { eWz := fun u a => LinearEquiv.refl ℂ _
      evz := fun u a ha h1 φ c s s' hs => hev u a ha h1 φ c s s' hs
      jM := jM
      per := fun u a _ => ⟨hj1 u a, hj2 u a, hj3 u a⟩ }
  refine ⟨Pt, E, ⟨fun u a _ v hv => hU u a v hv, fun u a _ κ κ' h h' => hchi u a κ κ' h h'⟩, ⟨fun u a _ => hrd u a, fun u a _ z c s s' h => hE u a z c s s' h, fun u a ha h1 => hz u a ha h1, fun u a z => rfl⟩⟩

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.Bl

abbrev DatP : Type 1 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
  (Wt : Set B.places.Pl), R3.Dat (w.st Z) w.I hX T Wt → Prop

def AtDat (P : DatP) : Prop :=
  StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt),
    GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → P K B f T w Z hX Wt z

end GlobalTheory.Mem.Top.Bl

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_rational_unitary_equiv_rowStage_compat : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∀ (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X'),
    (∀ x, RowAd.ptE X (e x) = x.1) →
    ∃ eΓ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* GQ X.toD7.sp.X',
      (∀ γ, Bridge.ratF X.toD7.sp.X' (eΓ γ) = e (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)) ∧
      ∀ γ, ∃ γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E, Bridge.IsRatMat X.toD7.sp.X' (eΓ γ) γE ∧
        MatEq γE γ.1 := by
  first | exact @GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv | exact GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv | (intros; apply GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnLayerConditions_trueColumns_laterStages : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1) := by
  first | exact @GlobalTheory.Mem.Top.ColOwe.colLay_colT | exact GlobalTheory.Mem.Top.ColOwe.colLay_colT | (intros; apply GlobalTheory.Mem.Top.ColOwe.colLay_colT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.OnePrimeEach

theorem exists_ratPrime_mem {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal := by
  haveI := w.isMaximal
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 L ⧸ w.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem exists_mem_of_prime (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ P.asIdeal := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 L)).injective_int]; exact bot_le)
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 L)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ']
      exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) (Ideal.mem_bot.1 hmem)

theorem ratPrime_unique {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpw : (p : 𝓞 L) ∈ w.asIdeal) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 L))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hqw)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def ratP (v : HeightOneSpectrum (𝓞 H.F)) : ℕ := (exists_ratPrime_mem v).choose

theorem ratP_prime (v : HeightOneSpectrum (𝓞 H.F)) : (ratP H v).Prime := (exists_ratPrime_mem v).choose_spec.1

theorem ratP_mem (v : HeightOneSpectrum (𝓞 H.F)) : ((ratP H v : ℕ) : 𝓞 H.F) ∈ v.asIdeal :=
  (exists_ratPrime_mem v).choose_spec.2

theorem ratP_eq (v : HeightOneSpectrum (𝓞 H.F)) {p : ℕ} (hp : p.Prime) (h : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ratP H v = p := ratPrime_unique v (ratP_prime H v) hp (ratP_mem H v) h

def primeK (p : ℕ) : HeightOneSpectrum (𝓞 H.K) :=
  if hp : p.Prime then (exists_mem_of_prime H.K hp).choose else (exists_mem_of_prime H.K Nat.prime_two).choose

theorem primeK_mem {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 H.K) ∈ (primeK H p).asIdeal := by
  unfold primeK
  rw [dite_eq_left hp]
  exact (exists_mem_of_prime H.K hp).choose_spec

def sel (v : HeightOneSpectrum (𝓞 H.F)) : HeightOneSpectrum (𝓞 H.E) :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose

theorem sel_mem (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ PvSet H (primeK H (ratP H v)) v :=
  (GlobalTheory.PlaceOverPair.exists_mem_pvSet H (ratP_prime H v) (primeK H (ratP H v)) (primeK_mem H (ratP_prime H v)) v
    (ratP_mem H v)).choose_spec

theorem sel_above (v : HeightOneSpectrum (𝓞 H.F)) : sel H v ∈ aboveF (L := H.E) H.F v := (sel_mem H v).1

theorem sel_under (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.F) = v := by
  have h := sel_above H v
  rw [aboveF, Set.Finite.mem_toFinset] at h
  exact h

theorem sel_underK (v : HeightOneSpectrum (𝓞 H.F)) : (sel H v).under (𝓞 H.K) = primeK H (ratP H v) := (sel_mem H v).2

theorem sel_mem_of {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    sel H v ∈ PvSet H (primeK H p) v := by
  have h := sel_mem H v
  rwa [ratP_eq H v hp hv] at h

def splitPlacesTwoPrimes : PlacesOverCommonPrime H :=
  ⟨primeK H H.pde, primeK H H.pde', primeK_mem H H.pde_prime, primeK_mem H H.pde'_prime, fun v _ => sel H v,
    fun v _ => sel H v, fun v hv => sel_mem_of H H.pde_prime v hv, fun v hv => sel_mem_of H H.pde'_prime v hv⟩

end GlobalTheory.Mem.Top.Bl.OnePrimeEach


open GlobalTheory.Mem.Top.Bl.OnePrimeEach in
theorem GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places : ∀ B : Base, ∃ (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (d : PlacesOverCommonPrime B.host), Formalism.L2.Col.IsSel B.fields Pv ∧ (∀ v, Pv v ∈ aboveF (L := B.host.E) B.host.F v) ∧ Half B Pv ∧ (∀ v hv, Pv v = d.P v hv) ∧ ∀ v hv, Pv v = d.P' v hv := by
  intro B
  refine ⟨sel B.host, splitPlacesTwoPrimes B.host, ?_, sel_above B.host, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro v
    exact congrArg HeightOneSpectrum.asIdeal (sel_under B.host v)
  · intro v v' p hp hv hv'
    rw [sel_underK, sel_underK, ratP_eq B.host v hp hv, ratP_eq B.host v' hp hv']

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem splitPlace_embedding_at_orbitPosition_eq_induced : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  intro K B f T w _ _ _ Z t _ _ _ _ _ _ _ _ _ _ _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro q s x
  have h := (t.g.cmp.tie u v hg).pos_emb q s x
  have key : ∀ (X : Formalism.L2.Herm.Herm0 (w.D Z)) (Bm : GL (Fin (w.D Z).R.k) (w.D Z).host.E), X = t.full.1.to0 →
      (Formalism.L2.G.Cmp.locAt X u v hg Bm).iw q x = iw0 t.full.1.g u v hg q x := by
    rintro X Bm rfl; rfl
  rw [key _ _ t.herm_eq] at h
  rw [← h]
  have h3 : Formalism.L2.Forms.sigD (w.D Z) x = (w.D Z).host.conj x := Formalism.BasicNotions.bridge_star_holds (w.D Z).R (w.D Z).host x
  rw [h3]
  show _ = (t.cmp.embW u v hg) (Formalism.L2.G.Cmp.tEL (w.D Z) _ _)
  congr 2
  by_cases hs : s.val % 2 = 1
  · have : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    simp [hs, this]
  · have : Even s.val := by rw [Nat.even_iff]; omega
    simp [hs, this]

end GlobalTheory.Mem.Top.KerOne
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.QpIsOf

theorem qpIs_qpSet : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), ColPin w → ∀ (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch), tp.xi = w.I.xi → GlobalTheory.Mem.HD.TupPins tp →
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := by
  intro B f T w _ Z nch tp hxi _ a p
  classical
  have hr := w.ok.xi_reads a
  have hsel : Formalism.L2.Col.IsSel B.fields w.I.sel := w.ok.sel_ok
  have hf := GlobalTheory.OpenChrRam.qprime_finite B.fields.F B.fields.E B.fields.K ((w.I.tup a : Formalism.L2.DIV.Chr _ _ _))
    (w.I.tup a).2.1.1.1.1.2
  have hpm : ∀ (v : HeightOneSpectrum (𝓞 B.fields.F)) (P : HeightOneSpectrum (𝓞 B.fields.E)),
      Ideal.under (𝓞 B.fields.F) P.asIdeal = v.asIdeal → ((p : 𝓞 B.fields.E) ∈ P.asIdeal ↔ (p : 𝓞 B.fields.F) ∈ v.asIdeal) := by
    intro v P h
    rw [← h, Ideal.under, Ideal.mem_comap, map_natCast]
  have hx : ∀ P, (tp.xi a).UnrAt P ↔ (w.I.xi a).UnrAt P := fun P => by rw [congrFun hxi a]; exact Iff.rfl
  refine (GlobalTheory.Mem.HD.ReQ.mem_qpSet tp a p).trans ?_
  refine Iff.trans (and_congr_right fun _ => exists_congr fun P => and_congr_right fun _ => not_congr (hx P)) ?_
  show (p.Prime ∧ ∃ P, (p : 𝓞 B.fields.E) ∈ P.asIdeal ∧ ¬ (w.I.xi a).UnrAt P) ↔
    p.Prime ∧ ∃ P ∈ Formalism.L2.Col.QE w.I.sel (w.I.tup a : Formalism.L2.DIV.Chr _ _ _), (p : 𝓞 B.fields.E) ∈ P.asIdeal
  rw [Formalism.L2.Col.QE, dite_eq_left hf]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨P, hp, hP⟩
    refine ⟨w.I.sel (P.under (𝓞 B.fields.F)),
      Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr _).2 ⟨P, rfl, hP⟩)), ?_⟩
    rw [hpm _ _ (hsel _), ← hpm _ P rfl]
    exact hp
  · rintro ⟨P, hP, hp⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨P', hP', hr'⟩ := (GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr v).1 (hf.mem_toFinset.1 hv)
    refine ⟨P', ?_, hr'⟩
    rw [hpm v P' (by rw [← hP']; rfl), ← hpm v _ (hsel v)]
    exact hp

end GlobalTheory.Mem.Top.Bl.QpIsOf
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.ServedPlace

theorem places_prime : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T := by
  intro K B f T w hK hF hP Z t Wt nch n Y hMu hQ O hO hU E hE Fl hfl hw u v hg hμ tt hStd
  have hok : Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v := by
    intro w' hw' hpw
    obtain ⟨P0, hP0, hu⟩ := (tt.ch.Q_iff _ w').1 hw'
    rw [n.xi] at hu
    have hq := GlobalTheory.Mem.ReadTwist.mem_qprime_iff (w.ok.xi_reads ((w.D Z).what₂.muAt v)) w'
    have hab : P0.under (𝓞 (w.D Z).host.F) = w' := by
      unfold Formalism.L2.Host.aboveF at hP0
      rw [Set.Finite.mem_toFinset] at hP0
      exact hP0
    have hv := hq.2 ⟨P0, hab, hu⟩
    have hPQ : w.I.sel w' ∈ ColIn.Q w.I ((w.D Z).what₂.muAt v) :=
      (Formalism.L2.Col.mem_QE w.I.sel (w.I.tup _) _).2 ⟨w', hv, rfl⟩
    have hund : (w.I.sel w').under (𝓞 B.host.F) = w' := GlobalTheory.TwistPlaces.under_eq_iff.2 (w.ok.sel_ok w')
    have hp : Nat.Prime ((w.D Z).what₂.places.resChar v) := hg.1
    have hmem : ((((w.D Z).what₂.places.resChar v : ℕ)) : 𝓞 B.host.E) ∈ (w.I.sel w').asIdeal := by
      rw [← hund] at hpw
      have := hpw
      simp only [HeightOneSpectrum.under, Ideal.under, Ideal.mem_comap, map_natCast] at this
      exact this
    have hQp := (hQ ((w.D Z).what₂.muAt v) ((w.D Z).what₂.places.resChar v)).2 ⟨hp, w.I.sel w', hPQ, hmem⟩
    exact Y.Qp_muAt v hQp
  exact ⟨hok, fun w' hw' => Formalism.MainNotions.G.CmpJ.badQ_notOver u v hg _ hok w' hw', hg.2.2.2.2.2⟩

end GlobalTheory.ServedPlace
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem stepZeroClasses_servedPlace_eq_localOrbitPairs_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ cls0 : ((w.D Z).gat u v hg).comp → ((w.D Z).gat u v hg).P.Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0,
        (∀ (a a' : ((w.D Z).gat u v hg).comp) (L L' : ((w.D Z).gat u v hg).P.Tup), ((w.D Z).gat u v hg).P.IsLatTup L →
          ((w.D Z).gat u v hg).P.IsLatTup L' →
          (cls0 a L = cls0 a' L' ↔ a = a' ∧ ∃ γ : (((w.D Z).gat u v hg).lev a).Γ, L' = (((w.D Z).gat u v hg).lev a).smul γ L)) ∧
        ∀ x, ∃ a L, ((w.D Z).gat u v hg).P.IsLatTup L ∧ cls0 a L = x := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  have e : ((w.D Z).mem u).C.cls 0 ≃ ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0 := TC.eCls0 w.I w.l u ((w.D Z).what₂.muAt v)
  obtain ⟨W, Qq, O', Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e', hH, heq⟩ :=
    t.g.gat u v hg
  obtain ⟨c⟩ := Formalism.L2.G.TwTie0.class_local_of_eq (w.D Z) t.g.herm.lev0 u e hS nV r m lam0 dom hk I ψ e' hH ((w.D Z).gat u v hg) heq
  exact ⟨c.cls, c.cls_iff, c.cls_surj⟩

end GlobalTheory.Mem.Top.KerOne
end
