module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle164
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle140
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle165
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle153
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle066
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle152
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPendingObjectSymmetricFormsLevel
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricLevelClausesHold
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
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem overCols_goodE : ∀ (𝒮 : Slots) (R : V4.Slot), OverCols (IsGoodE 𝒮) ∧ OverCols (sAnd (IsGoodE 𝒮) R) := by
  intro 𝒮 R
  have h : OverCols (IsGoodE 𝒮) :=
    (overCols_built 𝒮).2 (GoodE 𝒮) fun _ _ _ _ _ _ _ g => ⟨g.1.choose⟩
  exact ⟨h, OverCols.and_left h⟩

end GlobalTheory.Fc.Cv

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section
namespace GlobalTheory.LvT.Built.TrueCols

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem trueColumns_chain_last_step_sharp_bound (h : I.Ok) (hJ : I.JetsIn) (hS : GlobalTheory.LvT.WtSign.BaseSigns B) (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word) (a : I.ι) : Conclusion5Sharp (tw (I.tw l l0 Z) u a) := by
  obtain ⟨Bd, hch, hsp, hse, hk, hBd⟩ := GlobalTheory.T.fivePointLaws_trueChains B X I h hJ l l0 Z u a
  have hT : Module.finrank ℚ Bd.E * (I.rec7 l Z).R.N (I.rec7 l Z).R.m + 1 < Bd.J.T := by
    subst hBd
    show Module.finrank ℚ B.host.E * B.R.N B.R.m + 1 < B.T u
    have h1 := X.a_gt
    have h2 := X.T_gt u
    have hf : Module.finrank ℚ B.host.E = 2 * B.R.f := by
      rw [B.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    rw [hf]
    have h3 : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < (B.T u : ℝ) := lt_trans h1 h2
    exact_mod_cast h3
  have hW : TwColumn.WtSigns Bd.ch :=
    (GlobalTheory.LvT.WtSign.wtSigns_assemble_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G u Bd.ch).2 hS
  have := (GlobalTheory.LvT.Built.Assemble.sharpBound_stability_latticeColumnChain (I.rec7 l Z) u Bd hsp hse hk hT hW).1
  rwa [hch] at this

theorem row_true : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word),
      Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ ∀ w : (I.rec7 l Z).what₂.places.Pl,
        (I.rec7 l Z).what₂.places.resChar w = ((I.rec7 l Z).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (I.rec7 l Z) μ →
        μ ≠ (I.rec7 l Z).what₂.mu0 → (I.rec7 l Z).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (I.rec7 l Z) u w,
        Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((I.rec7 l Z).R.m : ℝ) * EatT (I.rec7 l Z) u w)) := by
  intro B X I h hJ hS l l0 Z Dx u
  refine ⟨?_, fun w hw μ _ _ _ x hx => ?_⟩
  · have h0 := trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u I.mu0
    rw [← own_eq I l l0 Z u] at h0
    exact (levelChainSharpColumnValuation_ownChain_iff (I.rec7 l Z) u).1 h0
  · have hTw : TupleChainSharpColumnValuation (I.tw l l0 Z) u μ :=
      TwSharp.tupleChainSharpColumnValuation_of_twisted (I.rec7 l Z) u (I.tw l l0 Z) μ (GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns B X I h l l0 Z u μ)
        (trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u μ)
    exact GlobalTheory.Proof.ColumnWeightTwisted.colGeTw_of_tupleChainSharpColumnValuation (I.rec7 l Z) (I.tw l l0 Z) u μ hTw w hw x hx

end GlobalTheory.LvT.Built.TrueCols
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.RedPt0

theorem formsMap_of_symmetricComparison_lowerMap_finiteChar : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → (∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)) → Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u := by
  intro D u Ch chOf Tf hL hB hC
  obtain ⟨P, h4⟩ := GlobalTheory.RedPt0Pend.exists_integralPendingObject_symmetricFormsLevel D u Ch chOf Tf hL hB hC
  exact Formalism.MainNotions.product_first_zeroth_parts.classMap_estimate_of_partial P h4 (Formalism.L2.GlobalTheoryTheory.Br.symmetric_level_clauses_hold D u Ch chOf Tf hL hB)

end GlobalTheory.RedPt0
end
