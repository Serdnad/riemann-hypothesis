module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle148
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle140
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BaseSignsOfVal
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle161
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomTop

theorem jetMoments : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments :=
  GlobalTheory.MomT.jetMoments_of_unitPeriod
    (GlobalTheory.T.unitPeriodTranslates_moments_finite GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomEq.eq_and_alg.2)
    GlobalTheory.MomEq.eq_and_alg.1 GlobalTheory.MomLat.latticeFactsAll

end GlobalTheory.MomTop
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Cv

theorem view_at_built : ∀ (R : ∀ D : D7, Obj D → Prop), (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) (nch : NChoice (w.D Z)), ColView w Z O.ex.tw nch → GlobalTheory.LvT.WtSign.BaseSigns B → Formalism.L2.Theta.RealTied (w.D Z) → R (w.D Z) O) → ∀ (K : Ctx) (β : BPt K), β.Is HasCols → R β.D β.O := by
  intro R H K β hβ
  have hS := GlobalTheory.Fc.Sg.baseSigns_of_bPt K β
  refine positionOf_ind (P := fun _ _ _ _ w Z c => ColView w Z c.O.tw c.O.nch)
    (R := fun K X f T c => ∀ (Y : Lay X.toD7), layObj Y = c.O → ∀ p : LedPart K.C Y,
      GlobalTheory.LvT.WtSign.BaseSigns X.B → Formalism.L2.Theta.RealTied X.toD7 → R p.pt.D (Obj.ofPt p.pt)) ?_ hβ β.Y β.hY β.p hS β.c.real
  intro K B f T w Z c hv Y hY p hS hreal
  let Z' : w.Lt := { Z with V := { Z.V with div := (setDiv (w.D Z) (nPrime p.L) p.ht).div } }
  have etw : Y.tw = w.tw Z := (congrArg Obj2.tw hY).trans hv.tw_eq
  obtain ⟨tp, htp⟩ := hv.tup
  refine H B f T w Z' (Obj.ofPt p.pt) (nchTr (nPrime p.L) p.ht c.O.nch) ⟨hv.jets, ⟨hv.rowInt.ref, hv.rowInt.tw⟩, ?_, ⟨{ tp with }, htp⟩⟩ hS
    ⟨hreal.cdScale, hreal.dsig, hreal.dsig_all, hreal.vol⟩
  show twTr (nPrime p.L) p.ht Y.tw = w.tw Z'
  rw [etw]
  rfl

end GlobalTheory.Fc.Cv
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

theorem _root_.GlobalTheory.T.workingFamClass_copies_eq_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (GlobalTheory.Cp.D3 3 𝒜 Fm ↔ W3 𝒜 Fm) ∧ (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm ↔ W1 𝒜 Fm)) ∧ ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → GlobalTheory.Cp.Duty Fm := by
  first | exact @GlobalTheory.Fc.copies_frozen | exact GlobalTheory.Fc.copies_frozen | (intros; apply GlobalTheory.Fc.copies_frozen <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedEvaluation_branching_all_tuples_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), GlobalTheory.PerQ.LowerTieTwAt (I.rec7 l Z) (I.tw l l0 Z) u a := by
  first | exact @GlobalTheory.PerQ.lowerTieTwAt_all | exact GlobalTheory.PerQ.lowerTieTwAt_all | (intros; apply GlobalTheory.PerQ.lowerTieTwAt_all <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep : (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  first | exact @GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | exact GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | (intros; apply GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep <;> assumption)
end
