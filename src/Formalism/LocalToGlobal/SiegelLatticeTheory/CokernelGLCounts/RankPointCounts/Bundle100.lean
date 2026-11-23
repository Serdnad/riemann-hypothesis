module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle096
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountAtHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle098
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsCompactIntLowSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle099
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle074
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle053
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

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutLeavesDeep_of_betaInt (D : Formalism.BasicNotions.D7)
    (hB : ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
      (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
      (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)), BetaInt ⟨δ, M, hA⟩ u u' F0 what₂) :
    Formalism.L2.SG.Pf.Coef.CutLeavesDeep D := by
  intro _ δ M hA _ u u' hc hP F0 what₂ hR
  refine ⟨fun γ w F' L U hE p => ⟨Formalism.L2.SG.Pf.CountAt.countAt_holds (M := M) (δ := δ) (γ := γ) (w := w) (F' := F') (L := L) (U := U) (hE := hE) (p := p) ..,
    by intros; apply Formalism.L2.SG.Pf.ProdEP2Uni.unimodAt_holds⟩,
    Formalism.L2.SG.Pf.TupGlobApprox.stabApprox _ u u', ?_⟩
  exact fStarC_of_int ⟨δ, M, hA⟩ ⟨hc, hR, hP⟩ (hB δ M hA u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem level_congr_mod_sq (D : D7) (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD Formalism.MainNotions.S.Lat.gS D ^ 2] := by
  have h : Formalism.MainNotions.S.Lat.gS D ^ 2 ∣ D.modT := by unfold Formalism.MainNotions.S.Lat.gS; exact D.gg_dvd_modT
  exact (D.T_modEq_of_dvd u h).trans (D.T_modEq_of_dvd u' h).symm

theorem prodConvNew_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConvNew X u u' ψ := by
  have hg : ∀ v, TypAt X v → 0 < gAt X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos X u u' ψ hψ hs (level_congr_mod_sq D u u') hg
  refine prodConvNew_gen X u u' ψ hb hψ hs hloc fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos X hg v⟩
  by_cases hv : TypAt X v
  · exact pp_pos_typ_gen X hb ψ hψ hs u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord X u u' ψ hψ hs hv l

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem coordCovol_of (hL : KapLaw) (hN : NOfib) (hB : BlockCovol) : Formalism.L2.SG.Pf.LsNc5.CoordCovol :=
  coordCovol_of_cut hL kapSurj_holds hN hB (fun X u => cVal_prod X u)

end Formalism.L2.SG.Pf.NcReal.JX
end
