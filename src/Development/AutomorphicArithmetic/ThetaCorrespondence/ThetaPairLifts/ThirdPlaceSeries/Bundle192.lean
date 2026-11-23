module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle096
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle078
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle097
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle189
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle072
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle830
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle832
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle446
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle185
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle179
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle175
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle190
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle570

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
end
theorem Mv.exists_at_alt {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) :
    ∃ a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL m.D (m.cf cf) (m.ch C) (m.tp tp), _root_.GlobalTheory.LayerMove.AtSameAltAlt m a a' := by
  obtain ⟨⟨nb, pack⟩, all, chr_eq, host, frameN, chrN, chrGal, Pq', Pq_over, pq, jE_eq, mt_eq, Pq_eq, hlow, split, ratIn,
    r1, r2, r3, depth⟩ := a
  obtain ⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, eq⟩ := nb
  subst eq
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at pack
  obtain ⟨rfl, rfl, rfl⟩ := pack
  have hmt : mtL L M = all.gal.mt := eq_of_heq mt_eq
  refine ⟨@_root_.GlobalTheory.Mem.Top.Bl.NAtData.mk hL m.D _ _ _
    (⟨@_root_.GlobalTheory.HeightCounting.NormChoiceConstructed.mk hL m.D m.pre.D (m.pre.cf cf0) jE (m.pre.sideA_alt A) ((_root_.UpperTheory.One.M.mvCg_alt trivial) m.pre cg) (m.pre.automorphy_of_move au) rep (m.pre.herm_wCell_last_mul_mulVec_eq_of_inWb row) low Pq S hk eig θ
      (m.pre.sideB_alt Bs) (m.pre.mt M) (m.pre.ch C0) (m.pre.tp tp0) (m.pre.choiceSide_alt ch) (m.pre.mtInput mt) big (m.pre.loc L)
      (m.pre.ndSpec_alt Sp) (m.pre.autSpec_alt Au) ((by with_unfolding_all exact (ss :))) m.withLoc_pre, m.pack_pre tp0⟩)
    ((_root_.UpperTheory.One.M.mvAll_alt trivial) m all)
    ((by with_unfolding_all exact ((congrArg (fun p : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L C0) =>
      (⟨m.cf p.1, m.tp p.2⟩ : Σ c : CharFrame m.D, TupTied m.D c (m.ch (chL L C0)))) chr_eq) :)))
    (m.host host) ((by with_unfolding_all exact (frameN :))) (m.chrN chrN) (m.chrGal chrGal) ((by with_unfolding_all exact (Pq' :))) ((by with_unfolding_all exact (Pq_over :))) ((by with_unfolding_all exact (pq :))) ((by with_unfolding_all exact (jE_eq :)))
    ((by with_unfolding_all exact ((heq_of_eq (congrArg m.mt hmt)) :))) ((by with_unfolding_all exact (Pq_eq :))) ((by with_unfolding_all exact (hlow :))) (m.oSplit split) ((by with_unfolding_all exact ((m.pre.ratIn ratIn) :))) ((by with_unfolding_all exact (r1 :))) ((by with_unfolding_all exact (r2 :)))
    ((by with_unfolding_all exact (r3 :))) ((by with_unfolding_all exact ((m.pre.rowDepth depth) :))), ?_⟩
  refine ⟨HEq.rfl, (by with_unfolding_all exact ((HEq.refl Pq') :)), (by with_unfolding_all exact ((HEq.refl (ratL L S)) :)), (by with_unfolding_all exact ((HEq.refl hk) :)), (by with_unfolding_all exact ((HEq.refl rep) :)), (by with_unfolding_all exact ((HEq.refl eig) :)), ?_⟩
  rintro ⟨h1, h2, fr, h3, h4⟩
  exact ⟨(by with_unfolding_all exact ((m.pre.labConj_alt (A := A) h1) :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact ((m.pre.omFrame fr) :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact ((m.pre.phtOn_alt (A := A) h4) :))⟩
end GlobalTheory.LayerMove
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem rowsAD_in_setting_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) →
    KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  intro hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
  have hstep : KillingConditions.StepAD L X :=
    { a09 := _root_.GlobalTheory.T.adm_at_inert_of_range hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
      a78 := _root_.GlobalTheory.T.unramified_places_declared' hP D L P nch HW F Cm X C₂ hS
      goodR := hS.canon.fam.good }
  have hst1 : TruncatedSeriesCountingIdentities.IntegralityFromMetric D := GlobalTheory.T.integralityFromMetric_of_designConditionAll hP.artin hP.bk hP.tate hP.euler D hS.facts.duties.2.2.1
  have h78 := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt hP.artin hP.tate hP.euler D
  have hG2 : ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π :=
    fun i hi π hπ => (_root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS i hi π hπ).2.1
  refine ⟨GlobalTheory.T.starInequality_rowsAD_of_global_theorems D L HW X (rowC C₂) hS.canon.data hstep hst1 h78 hG2 hS.kill hS.sha, ?_⟩
  have h := GlobalTheory.T.nonPlacePart_localBound_le_middleRange D L P HW X (rowC C₂) 120 (by norm_num) hS.canon.data
    (_root_.GlobalTheory.T.invariantsBoundNonsplit_of_setup hP D L P nch HW F Cm X C₂ hS)
  have e : (60 : ℝ) * 120 = 7200 := by norm_num
  rwa [e] at h
end GlobalTheory.NLink
end
end
