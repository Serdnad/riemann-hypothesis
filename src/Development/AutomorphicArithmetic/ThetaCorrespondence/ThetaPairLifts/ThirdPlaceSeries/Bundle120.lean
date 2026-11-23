module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle073
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle112
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle091
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle084
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle100
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle101
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059

@[expose] public section

section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.WtSz
open GlobalTheory.CompHS
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
open GlobalTheory.CompHS
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz

theorem wts_le_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1) := by
  intro hS
  have hL : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (∃ A, SizeAt p i PP A) ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 10) ∧
      WtNum p i PP := by
    refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 10) _root_.GlobalTheory.CovTop.WtShape.wtN_z))
      fun Fm CH _ h => ?_
    obtain ⟨⟨C1, _, a1, ha1⟩, ⟨C2, _, a2, ha2⟩, ⟨C3, _, a3, ha3⟩⟩ := h
    exact ⟨0, le_rfl, max a1 (max a2 a3), fun x hx hle ι p hp i =>
      ⟨⟨C1, ha1 x hx ((le_max_left _ _).trans hle) ι p hp i⟩,
        ⟨C2, ha2 x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
        ha3 x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt hL fun Fm x hx ι p i _ _ h hi _ _ =>
    at_pt p i _ h.1.choose h.2.1.choose hi h.1.choose_spec h.2.1.choose_spec h.2.2
end GlobalTheory.CovTop.WtSz
end
end
end

section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
theorem wt_size_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  intro hS
  have hL : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => SizeAt p i PP C ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 0) ∧ WtNum p i PP := by
    refine (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) _root_.GlobalTheory.CovTop.WtShape.wtN_z)).imp
      fun Fm CH _ hh => ?_
    obtain ⟨⟨C, hC, a, ha⟩, ⟨C', -, b, hb⟩, ⟨C'', -, c, hc⟩⟩ := hh
    exact ⟨C, hC, max a (max b c), fun x hx hle ι p hp i =>
      ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i,
       ⟨C', hb x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
       hc x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt hL fun Fm x hx ι p i C _ h _ Y _ => by
    obtain ⟨h1, ⟨A, h2⟩, h3⟩ := h
    exact fun j hj => sum_abs_wt_le_point p i h1 h2 h3 hj
end GlobalTheory.CovTop.WtRun
end
end

section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CovTop.FlatSz
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.CovTop.FlatSz
namespace GlobalTheory.CovTop.FlatSz
theorem flatDegVal_covers_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ =>
    |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by
  intro _
  have h1 := _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt
    (Q := fun Fm x _ ι _ _ _ PP => ∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 0) (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)
    (fun _ _ _ _ _ _ C _ h _ _ _ => ⟨C, h⟩)
  have h2 := _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt
    (Q := fun _ _ _ _ p i _ PP => WtNum p i PP) _root_.GlobalTheory.CovTop.WtShape.wtN_z
    (fun _ _ _ _ _ _ _ _ h _ _ _ => h)
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_covers_of_imp (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt h1 h2)
    (fun _ _ _ _ p i _ _ h => abs_flatDegVal_le p i h.1.choose_spec h.2)
end GlobalTheory.CovTop.FlatSz
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
namespace GlobalTheory.BigTop.Fun.ThbTie
end GlobalTheory.BigTop.Fun.ThbTie
open GlobalTheory.BigTop.Fun.ThbTie in
theorem GlobalTheory.BigTop.Fun.thb_tie_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hd : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hT : ThbSt) : _root_.GlobalTheory.BigTop.Fun.LeafThetaBound @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hd hT
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono hQ ?_
  intro D L hT' Gi Gl Kc Y cX ex Csz p CF d C CH _ htie
  refine ⟨htie, fun hq => ?_⟩
  obtain ⟨a, ha⟩ := htie.2
  have hsq := ha.sq
  have hin : ∀ (ij : Sq D) (s : ℤ), 1 ≤ s → s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 →
      Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 (bTH D C p.Z.x p.Z.b) ∧
        ∀ c, d.zTd ij c s ≠ 0 ∧ Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) (bTH D C p.Z.x p.Z.b) := by
    intro ij s h1 h2
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ s)
    have h1' : 1 ≤ n := by omega
    have h2' : n ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by omega
    exact hq ij.1 ij.2 n h1' h2' _ _ (hsq.inside ij n h1' h2').1
  have hB0 : ∀ ij : Sq D, 0 ≤ bTH D C p.Z.x p.Z.b := by
    intro ij
    have hr : 1 ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
      have := D.R.m_add_three_le_k
      unfold GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      omega
    exact htLe_nonneg (hin ij 1 le_rfl (by exact_mod_cast hr)).1
  have hB : d.O.bTH C p.Z.x p.Z.b = bTH D C p.Z.x p.Z.b := rfl
  have hzT : ∀ ij s, d.O.zT ij s = 1 := hsq.base
  refine ⟨fun ij s h1 h2 => ?_, fun ij s => ?_, fun ij c s => ?_⟩
  · have h2' : s ≤ (GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 : ℤ) :=
      h2.trans_eq (congrArg (fun n : ℕ => (n : ℤ)) (sqRank_half (D := D) ij))
    exact ⟨by rw [hzT]; exact one_ne_zero, fun c => ((hin ij s h1 h2').2 c).1⟩
  · rw [hzT, hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact (hin ij s hs.1 hs.2).1
    · have := (hsq.outside ij s hs).2.1
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 _
      rw [this]
      exact htLe_one_zero (hB0 ij)
  · rw [hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact ((hin ij s hs.1 hs.2).2 c).2
    · obtain ⟨e1, e2, -⟩ := hsq.outside ij s hs
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) _
      rw [e1 c, e2]
      exact htLe_one_zero (hB0 ij)
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree
namespace GlobalTheory.BigTop.Fun.OneSqTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem lf_std_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint) : _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun _ _ d _ _ => Formalism.L2.Theta.IsStdChar _ d.W.ψ (-1) := by
  obtain ⟨CF0, h⟩ := hS.atPt big_std
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => _root_.GlobalTheory.BigTop.Fun.evPt_mono e fun x hx i p _ hq d hd => ?_⟩⟩
  obtain ⟨a, ha⟩ := hd.2
  exact hq d.G d.W d.n a ha.ok
end GlobalTheory.BigTop.Fun.OneSqTie
open GlobalTheory.BigTop.Fun.OneSqTie in
theorem GlobalTheory.BigTop.Fun.oneSq_of_log_derivative_bound_thA (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hdl : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hA : _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) (hO : OneSqSt) : _root_.GlobalTheory.BigTop.Fun.LeafUniqueSquareRoot @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hO
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and hQ (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and hA (_root_.GlobalTheory.BigTop.Fun.OneSqTie.lf_std_alt hS))) ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun ⟨hq, hth, hstd⟩ => ?_⟩
  obtain ⟨a, ha⟩ := hd.2
  have key := hq d.W a.S.toGridChoice a.rm hstd ha.ok.field CF p.R.mu d.rq d.zA d.zA' d.zT d.zTd d.gT d.ch d.N0 d.Sd d.Se
    d.dl d.Bw hth ha.sq
  have e1 : (p.S false).μ = p.R.mu := rfl
  have e2 : p.P.A3.fam3.base3.μ0 = p.P.A3.A.μ0 := rfl
  have hsq := ha.sq
  have hm : d.O.m = D.R.m := rfl
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hkm := D.R.m_add_three_le_k
  obtain ⟨ka, hka⟩ := D.R.k_even
  obtain ⟨mb, hmb⟩ := D.R.m_even
  obtain ⟨tc, htc⟩ := D.R.t_odd
  have hs : GlobalTheory.ChiGrid.sLen D = D.R.k + D.R.m + 5 := by unfold GlobalTheory.ChiGrid.sLen; rw [hr]; omega
  have E : ∀ ij : Sq D, sqRank D ij =
      2 * (D.R.r + (ij.2 : ℕ) * D.R.t + (ij.1 : ℕ) * GlobalTheory.ChiGrid.sLen D) + (D.R.t + GlobalTheory.ChiGrid.sLen D) := by
    intro ij; unfold sqRank GlobalTheory.ChiGrid.rankV; ring
  have E' : ∀ ij : Sq D, GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = d.O.hd ij := by
    intro ij
    show (GlobalTheory.ChiGrid.rankV D ((ij.1 : ℕ) + 1) ((ij.2 : ℕ) + 1) + GlobalTheory.ChiGrid.rankV D ij.1 ij.2) / 2 = sqRank D ij / 2
    congr 1
    unfold sqRank GlobalTheory.ChiGrid.rankV; ring
  have hev : ∀ ij : Sq D, sqRank D ij = 2 * (sqRank D ij / 2) := by
    intro ij
    rw [E ij, hs]
    omega
  have hN : d.O.N = D.R.k + D.R.m * D.R.t + D.R.m * GlobalTheory.ChiGrid.sLen D + D.R.m := by
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = _
    rw [hs]; ring
  refine ⟨fun ij => hsq.rq_base ij, fun w ij => (key w ij).1, fun l hl => ((hsq.err l).1 hl).1, fun ij => hev ij,
    fun ij => ?_, fun ij => ?_, fun q _ => ?_, fun w ij => ?_⟩
  · show sqRank D ij ≤ 2 * d.O.N
    rw [hN, E ij]
    have h1 : (ij.2 : ℕ) * D.R.t + D.R.t ≤ D.R.m * D.R.t := by
      calc (ij.2 : ℕ) * D.R.t + D.R.t = ((ij.2 : ℕ) + 1) * D.R.t := by ring
        _ ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
    have h2 : (ij.1 : ℕ) * GlobalTheory.ChiGrid.sLen D + GlobalTheory.ChiGrid.sLen D ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := by
      calc (ij.1 : ℕ) * GlobalTheory.ChiGrid.sLen D + GlobalTheory.ChiGrid.sLen D = ((ij.1 : ℕ) + 1) * GlobalTheory.ChiGrid.sLen D := by ring
        _ ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := Nat.mul_le_mul_right _ (by omega)
    rw [hr]
    omega
  · show D.R.m - 1 - (ij.2 : ℕ) + 1 ≤ D.R.m
    omega
  · classical
    show (if q = d.G.pl.v0 then 1 else 2) ≤ (if q = d.G.pl.v0 then _ else 2)
    split_ifs <;> omega
  · have h := (key w ij).2
    have hd2 : 2 * GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = d.O.dd ij := by
      rw [E' ij]; exact (hev ij).symm
    rw [hd2, E' ij] at h
    exact h
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
namespace GlobalTheory.BigTop.Fun.IntTie
end GlobalTheory.BigTop.Fun.IntTie
open GlobalTheory.BigTop.Fun.IntTie in
theorem GlobalTheory.BigTop.Fun.int_tie_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hd : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hB : BotSmall) (hN : BotNe) : _root_.GlobalTheory.BigTop.Fun.LeafIntegrality @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hd (gBig_dep (gBig_and hB hN))
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨h1, h2, ⟨-, -, hsmall⟩, hne⟩ := hq
  change 1 ≤ CF at h1
  change CF ≤ C at h2
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  obtain ⟨S, del, -, -, hNI, hdl⟩ := hsq.int
  obtain ⟨δ, t0, hP⟩ := hsq.norms
  choose P P' hb hz hz' using hP
  have hI := hNI δ t0 D.what₂.LL D.what₂.embLL (Sq D) P P' d.zA d.zA'
    (fun ij => hsmall δ t0 _ (P ij) (P' ij) _ ij.1 ij.2 _ (hb ij))
    (fun ij => hne δ t0 _ (P ij) (P' ij) ij.1 ij.2 (hb ij))
    (fun ij => ⟨hz ij, hz' ij⟩)
  rw [← hdl] at hI
  show NonArchimedeanDefectBound d.dl d.zA d.zA' (d.O.bDel C p.Z.b)
  refine integralNormBound_mono hI ?_
  clear hQ hne hsmall hb hz hz' hNI
  have eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := by
    have := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    norm_cast
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)
    unfold GlobalTheory.ChiGrid.sLen
    rw [hr]
    congr 3
    omega
  have eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) := hsq.weight
  have eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    rw [GlobalTheory.FunObj.SqNum.log_levQ]
    rfl
  have ef : (d.O.f : ℝ) = D.R.f := rfl
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ))) +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * Real.log p.Z.b +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) ^ 2 * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := ⟨_, rfl⟩
  have e1 : d.O.bDel C p.Z.b = C * X := by
    unfold FunData.bDel
    rw [eN, eB, eS, ef, hX]
    ring
  have e2 : GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) = CF * X := by
    unfold GlobalTheory.NormSum.intBound
    rw [hX]
    ring
  have h0 := hI.2.1 ∅
  rw [Finset.sum_empty] at h0
  change 0 ≤ GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) at h0
  change GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) ≤ _
  rw [e1, e2]
  rw [e2] at h0
  have hX0 : 0 ≤ X := (mul_nonneg_iff_of_pos_left (by linarith)).1 h0
  exact mul_le_mul_of_nonneg_right h2 hX0
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates
end GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.LargeParameterEstimates
theorem parOf_further_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m,
    (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 5) ≤ (parOf (Fm.L x i) j).w'' / (parOf (Fm.L x i) j).S ∧
    4 * (parOf (Fm.L x i) j).x ^ 2 * (parOf (Fm.L x i) j).L ^ 2 * (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 7) <
      (parOf (Fm.L x i) j).b ^ ((4 : ℝ) / 5) := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := ev_large eps he
  refine ⟨x0, fun x hx hle i p _ _ j => ?_⟩
  obtain ⟨hxp, E1, E2, E3, E4⟩ := hx0 x hle
  have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hee : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hsz := Fm.sizes x hx i
  have hN : SizeN (Fm.L x i) := hsz.1
  have hK : SizeK (Fm.L x i) := hsz.2.2.1
  have hD := (Fm.params x hx i).logDel
  have hS := (Fm.L x i).Sc_pos
  rw [(Fm.L x i).Sc_eq] at hS
  unfold SizeN szTh at hN
  unfold SizeK szTh at hK
  rw [hxx, hee] at hN hK hD
  constructor
  · show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5) ≤
      (Fm.L x i).sc.x * Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) /
        Real.exp ((Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 3)) / ((Fm.L x i).sc.x * ((Fm.D x i).R.n : ℝ)) / (Fm.L x i).Sc
    rw [(Fm.L x i).Sc_eq, hxx, hee]
    have hk : (0 : ℝ) ≤ (Fm.D x i).R.k := Nat.cast_nonneg _
    have hn : (0 : ℝ) < (Fm.D x i).R.n := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hN.1
    have hΔ : ((Fm.D x i).s.Del : ℝ) ≤ Real.exp (x ^ (eps / 4) / 2) := by
      have h4 : 0 < 4 * ((Fm.D x i).s.Del : ℝ) := pos_of_mul_pos_right hS hk
      exact (Real.log_le_iff_le_exp (by linarith)).1 hD
    exact w_over_S_real hxp hk hn hS hK.2 hN.2 hΔ E1 E2 E3
  · show 4 * (Fm.L x i).sc.x ^ 2 * ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ 2 *
        Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 7) <
      Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) ^ ((4 : ℝ) / 5)
    rw [hxx, hee]
    exact pow_real hxp E4
theorem parOf_large_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (parOf (Fm.L x i) j).Large :=
  _root_.GlobalTheory.ExpTie.atPts_mono (_root_.GlobalTheory.ExpTie.atPts_and_alt (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.ExpTie.parOf_hyp_alt _root_.GlobalTheory.T.exists_large_parameter_estimates_at_pts) _root_.GlobalTheory.ExpTie.parOf_further_alt) fun _ _ _ _ _ H j => by
    obtain ⟨⟨hH, hR⟩, hE⟩ := H
    obtain ⟨X', A, hR', hB⟩ := hR j
    exact large_of_rows_pow (hH j) hR' hB (hE j).1 (hE j).2
end GlobalTheory.ExpTie
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem onto_at_chosen_alt : _root_.GlobalTheory.BigOn.SurjectiveOntoX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ →
    EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 σ :=
  fun h 𝒜 σ hD hR hM =>
    _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigOn.More p)
      (fun C CH _ _ _ p => (p.S false).ON (p.N C CH)) h 𝒜 σ hD hR hM
end GlobalTheory.Fc.Ind
end
end
