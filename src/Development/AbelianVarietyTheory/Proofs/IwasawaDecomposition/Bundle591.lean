module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle573
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle536
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle503
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle580
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove


theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := {
       xi := by with_unfolding_all exact (n.tp.xi :)
       xi_inj := by with_unfolding_all exact (n.tp.xi_inj :)
       xi_fin := by with_unfolding_all exact (n.tp.xi_fin :)
       xi_triv := by with_unfolding_all exact (n.tp.xi_triv :)
       xi_tame := by with_unfolding_all exact (n.tp.xi_tame :)
       psi := by with_unfolding_all exact (n.tp.psi :)
       trueColumnChoices_heckeChar_reference_eq_one := by with_unfolding_all exact (n.tp.trueColumnChoices_heckeChar_reference_eq_one :)
       xi_star := by with_unfolding_all exact (n.tp.xi_star :)
       xi_star' := by with_unfolding_all exact (n.tp.xi_star' :)
       xi_tw := by with_unfolding_all exact (n.tp.xi_tw :)
       psi_is := by with_unfolding_all exact (n.tp.psi_is :)
       psi_un := by with_unfolding_all exact (n.tp.psi_un :) }
     xi := by with_unfolding_all exact (n.xi :)
     psi := by with_unfolding_all exact (n.psi :)
     tie := {
       twOf_eq := by with_unfolding_all exact (n.tie.twOf_eq :)
       twSide_eq := by with_unfolding_all exact (n.tie.twSide_eq :)
       Q_eq := by with_unfolding_all exact (n.tie.Q_eq :)
       psi_eq := by with_unfolding_all exact (n.tie.psi_eq :)
       embedding_baseField_condition := by with_unfolding_all exact (n.tie.embedding_baseField_condition :) }
     Q := n.Q
     chrPsi := by with_unfolding_all exact (n.chrPsi :) }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  dsimp only [nchUp, xdUp, upL]
  -- Abstract the new division stage before comparing the twisting conditions.
  generalize (Db.setDivZ Z N h).V = V'
  obtain ⟨⟨E, N0, S⟩, hE, hAt, hCl⟩ := g.tw
  cases hE
  refine ⟨⟨⟨twEOf _, N0, S⟩, rfl, ?_, ?_⟩, g.sep⟩
  · with_unfolding_all exact hAt
  · with_unfolding_all exact hCl
end

end GlobalTheory.LayerMove
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.group_tie_of_local_coefficient : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (_ : LC hL x), Formalism.L2.DIV.GrpTie (Dof x) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1 (x.m.z.R.eG.trans x.m.z.cG) := by
  first | exact @GlobalTheory.HeightCounting.Fin3.grpTie_of_LC | exact GlobalTheory.HeightCounting.Fin3.grpTie_of_LC | (intros; apply GlobalTheory.HeightCounting.Fin3.grpTie_of_LC <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.twistConductors_avoid_excludedPrimes : AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  first | exact @GlobalTheory.LowAvoid.conductors_avoid_lowAll | exact GlobalTheory.LowAvoid.conductors_avoid_lowAll | (intros; apply GlobalTheory.LowAvoid.conductors_avoid_lowAll <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.goodForms_nonisomorphicTypeParts_inf_eq_bot : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (i : Fin D.R.m) (π π' : Φ), π ≠ π' → y.prtW F.lv2 i (rep π) ⊓ y.prtW F.lv2 i (rep π') = ⊥ := by
  first | exact @GlobalTheory.Mem.R3.Rw.TypesDisj.prtW_inf_eq_bot | exact GlobalTheory.Mem.R3.Rw.TypesDisj.prtW_inf_eq_bot | (intros; apply GlobalTheory.Mem.R3.Rw.TypesDisj.prtW_inf_eq_bot <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.rowFiniteTypeParts_span_and_orthogonal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ b : Bool, (⨆ π, y.prtE F.lv2 b (rep π)) = (y.C F.lv2).EEc b ∧ ∀ π π', π ≠ π' → ∀ x ∈ y.prtE F.lv2 b (rep π), ∀ x' ∈ y.prtE F.lv2 b (rep π'), (y.C F.lv2).ipE b x x' = 0 := by
  first | exact @GlobalTheory.Mem.R3.Rw.TypesRows.parts_span_orth | exact GlobalTheory.Mem.R3.Rw.TypesRows.parts_span_orth | (intros; apply GlobalTheory.Mem.R3.Rw.TypesRows.parts_span_orth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.exists_finite_representatives_rowFiniteTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  first | exact @GlobalTheory.RowTypeReps.reps_exist | exact GlobalTheory.RowTypeReps.reps_exist | (intros; apply GlobalTheory.RowTypeReps.reps_exist <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.baseRowCount_eq_finrank_typePart_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ π : D.what₂.FT, D.what₂.nRows0 π = Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  first | exact @GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE | exact GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE | (intros; apply GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RowsLift

theorem rows_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH hM hg p hp i
  have hA := GlobalTheory.T.exists_baseLevelRow_of_nonzero_goodRowsPart D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp
  have hB : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ := by
    intro h0
    apply hA
    rw [← Submodule.finrank_eq_zero, ← hH.prim.dimParts i p, h0, finrank_bot]
  refine ⟨?_, fun v hv => ?_⟩
  · intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    have : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ R.Wp3 i p := hw.1
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).2 this
  · obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_nonzero_rational_lift_mem_base_part D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp i hB
    exact ⟨x, hx, GlobalTheory.T.base_level_frames_hermitian_ne_zero_off_place D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg i v hv x hx0⟩

end GlobalTheory.RowsLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.Mem.R3

theorem dat_ext_heq {X : Stages} {px : PreX X.B.toPre} {I : Col2.ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
    {Wt : Set X.B.places.Pl} {d₁ d₂ : Dat X I hX T Wt} (hXg : d₁.Xg = d₂.Xg) (htr : d₁.tr = d₂.tr)
    (hcore : d₁.core = d₂.core) (hR : HEq d₁.R d₂.R) (hcG : HEq d₁.cG d₂.cG) (hgeo : HEq d₁.geo d₂.geo) : d₁ = d₂ := by
  cases d₁ with
  | @mk Xg tr core alg alg_eq R cG geo pins lev idG good mu fieldValues_mem_fixedField Ks_le =>
  cases d₂ with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le_LL0' Ks_le' =>
  dsimp only at hXg htr hcore hR hcG hgeo
  subst hXg htr hcore
  have halg : alg = alg' := Algebra.algebra_ext _ _ fun y => X.B.embLL.injective ((alg_eq y).trans (alg_eq' y).symm)
  subst halg
  cases eq_of_heq hR
  cases eq_of_heq hcG
  cases eq_of_heq hgeo
  rfl

end GlobalTheory.Mem.R3

namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw

theorem coreJ_coreJ {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) (T : Formalism.L2.Pj.CoreJ a.D) :
    coreJ (a := b) c (coreJ b T) = coreJ c T := (by with_unfolding_all exact ((Eq.refl (coreJ c T)) :))

theorem moved_eq_datTw : ∀ {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T} {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (N : TwNew (GlobalTheory.HeightCounting.Up.Dof x)) (m : GlobalTheory.Mem.R3.Rw.Moved (GlobalTheory.HeightCounting.Up.oTw x N)), m.Copy → HEq m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq m.z.cG x.m.z.cG → HEq m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → m.z = GlobalTheory.HeightCounting.Up.datTw x N := by
  intro K B f T w P x N m hc hR hcG hgeo
  have h1 : x.m.z.core = coreJ (a := P.Z₀) x.o.Z P.z.core := (by with_unfolding_all exact ((eq_of_heq x.copy.core) :))
  have h2 : m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core := (by with_unfolding_all exact ((eq_of_heq hc.core) :))
  have h3 : coreJ (a := x.o.Z) (oTw x N).Z x.m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core :=
    (congrArg (coreJ (a := x.o.Z) (oTw x N).Z) h1).trans (coreJ_coreJ _ _ _)
  have h4 : HEq (datTw x N).cG x.m.z.cG := (by with_unfolding_all exact ((HEq.refl x.m.z.cG) :))
  exact dat_ext_heq (d₁ := m.z) (d₂ := datTw x N) ((by with_unfolding_all exact ((m.Xg.trans x.m.Xg.symm) :))) ((by with_unfolding_all exact ((m.tr.trans x.m.tr.symm) :)))
    ((by with_unfolding_all exact ((h2.trans h3.symm) :))) ((by with_unfolding_all exact (hR :))) (hcG.trans h4.symm) ((by with_unfolding_all exact (hgeo :)))

end GlobalTheory.HeightCounting.Up
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.Mv

namespace GlobalTheory.HeightCounting.Up.MvTw

section Gen

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C)
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m}

section Comp
variable (R : RealDat3 a.D A3 Ks)

def once : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) := real3 c R

def thru : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) :=
  (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thruY : letI := alg c iK; type_of% (once c R).ioY := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioY :))

def thruX : letI := alg c iK; type_of% (once c R).ioX := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioX :))

theorem thruY_eq : letI := alg c iK; (once c R).ioY = thruY b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioY c R.toRealDat).symm :)) : HEq (once c R).ioY R.ioY)
    ((by with_unfolding_all exact ((HEq.trans (real_ioY b R.toRealDat) ((by with_unfolding_all exact ((real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruY b c R)) :))))

theorem thruX_eq : letI := alg c iK; (once c R).ioX = thruX b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioX c R.toRealDat).symm :)) : HEq (once c R).ioX R.ioX)
    ((by with_unfolding_all exact ((HEq.trans (real_ioX b R.toRealDat) ((by with_unfolding_all exact ((real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruX b c R)) :))))

theorem thru_eq : once c R = thru b c R :=
  letI := alg c iK
  (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (once c R)) (thruY_eq b c R) (thruX_eq b c R)) :))

end Comp

variable {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat) (y' : HdB b R.toRealDat)



theorem pkT_move (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (GlobalTheory.Mem.R3.Tr.reps_parts_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.Mem.R3.Rw.chT_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.Mem.R3.Rw.lfT_of_same B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.Mem.R3.Rw.rr_eta_tr B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Gen

section Dat

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}



theorem transportModuliCoreWithConstants_comp (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc b.st.B px → b.st.B.LL)) (tr : TrI b.st.B px)
    (co : Formalism.L2.Pj.CoreJ b.st.toD7) (al : Algebra co.Q.c.F b.st.toD7.what₂.LL)
    (ale : ∀ y : co.Q.c.F, b.st.B.embLL (algebraMap co.Q.c.F b.st.toD7.what₂.LL y) = y)
    (R : RealDat3 b.st.toD7 (famR b.st I hX (usedOf I T Wt) Xg tr) co.Q.c.F)
    (hXg : Xg = z₀.Xg) (htr : tr = z₀.tr)
    (hc : HEq co (coreJ (a := a) b z₀.core)) (hR : HEq R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c co) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := al) R) (real3 (a := a) c (iK := z₀.alg) z₀.R) := by
  have hc' := eq_of_heq hc
  subst hXg htr hc'
  have e : al = ((by with_unfolding_all exact ((alg (a := a) b z₀.alg) :))) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    refine Eq.trans (ale y) ?_
    exact (by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :))
  subst e
  have hR' : R = ((by with_unfolding_all exact ((real3 (a := a) b (iK := z₀.alg) z₀.R) :))) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  refine ⟨?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := a) c z₀.core)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (thru_eq (a := a) b c (iK := z₀.alg) z₀.R).symm) :))



theorem copy_comp (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (hXg : z.Xg = z₀.Xg) (htr : z.tr = z₀.tr)
    (hc : HEq z.core (coreJ (a := a) b z₀.core)) (hR : HEq z.R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c z.core) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := z.alg) z.R) (real3 (a := a) c (iK := z₀.alg) z₀.R) :=
  (by with_unfolding_all exact ((transportModuliCoreWithConstants_comp b c z₀ z.Xg z.tr z.core z.alg z.alg_eq z.R hXg htr hc hR) :))

end Dat

section Main

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}



theorem moved_again (o o' : q.Over) (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hc : m.Copy) (hh : m.Coh) :
    ∃ m' : Moved o', m'.z = DatCopy.copy (a := o.Z) o'.Z s m.z ∧ m'.Copy ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_move (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.Mem.R3.Rw.rr_eta_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hk := copy_comp (a := Z₀) o.Z o'.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :)))
  have hW := forcedContentPlaces_eq_transport_sameFiniteGroup (a := o.Z) o'.Z s m.z
  refine ⟨{ z := DatCopy.copy (a := o.Z) o'.Z s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((cp_holds (a := o.Z) o'.Z s m.z m.intersectionNumber_baseChange) :))
            exAt := DatCopy.copy_exAt (a := o.Z) o'.Z s m.exAt
            inGeo := (by with_unfolding_all exact ((cp_inGeo (a := o.Z) o'.Z s m.z m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := o.Z) o'.Z (m.core h).1) :)), (by with_unfolding_all exact ((m.core h).2.1 :)), (by with_unfolding_all exact ((m.core h).2.2.1 :)),
              (by with_unfolding_all exact ((m.core h).2.2.2 :))⟩
            eta := fun j v => Eq.trans ((by with_unfolding_all exact ((he j ((by with_unfolding_all exact (v :)))) :)) : _ = etaOf m.z.R m.z.F j v) (m.eta j v)
            W1 := fun F0 => Eq.trans ((by with_unfolding_all exact ((hW ((by with_unfolding_all exact (F0 :)))) :)) : _ = m.z.W1 ((by with_unfolding_all exact (F0 :)))) ((by with_unfolding_all exact ((m.W1 ((by with_unfolding_all exact (F0 :)))) :)))
            y := (by with_unfolding_all exact ((hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c ((by with_unfolding_all exact (u :)))).j) hA))
              (m.tA c ((by with_unfolding_all exact (u :))))) :)) }, rfl, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hk.1 :))
  · exact (by with_unfolding_all exact (hk.2 :))
  · exact (by with_unfolding_all exact (hh.tupT :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PY :)) : HEq (fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PY.ψ m.y.PY.ψ) hh.PY) :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PW :)) : HEq (fun i => ((fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PW i).ψ) (fun i => (m.y.PW i).ψ)) hh.PW) :))
  · exact (by with_unfolding_all exact ((a2.trans hh.rep) :))
  · exact (by with_unfolding_all exact ((fun c => (a3 c).trans (hh.jE c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a4 c).trans (hh.jM c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a5 c).trans (hh.jX c)) :))
  · exact (by with_unfolding_all exact ((a6.trans hh.eW) :))
  · exact (by with_unfolding_all exact ((a7.trans hh.jMt) :))

end Main

theorem moved_tw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (N : TwNew (Dof x)) : ∃ m : Moved (oTw x N), m.z = datTw x N ∧ m.Copy ∧ m.Coh :=
  moved_again x.o (oTw x N) (sgTw x N) x.m x.copy x.coh

end GlobalTheory.HeightCounting.Up.MvTw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  first | exact @GlobalTheory.HeckeLocN.exists_twRing_of_large | exact GlobalTheory.HeckeLocN.exists_twRing_of_large | (intros; apply GlobalTheory.HeckeLocN.exists_twRing_of_large <;> assumption)
end
