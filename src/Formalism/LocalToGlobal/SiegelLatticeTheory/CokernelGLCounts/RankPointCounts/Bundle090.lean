module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfL
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohLp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle077
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle085
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle089
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle088
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle087
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle083
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LprEx

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem scal_rep (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hP : IsPartner γ Z F'')
    (hGr : Gval (lf D F0) (repF γ) ≠ 0) :
    ∃ β, IsPair γ.lam (lf D F0) (repF γ) F'' β (gS D) ∧ s0 γ.lam (lf D F0) (repF γ) F'' β D.R.k = 1 ∧
      IsScalar γ.lam (lf D F0) (repF γ) F'' β := by
  obtain ⟨hE, γ', ⟨pr, hp1, hp2, hps, hpsc⟩, h3, h3e⟩ := hP
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGF : Gval (lf D F0) F'' ≠ 0 := hE.1.2.2
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := pr
  simp only [Formalism.L2.SG.Corank.Pair.pfst, Formalism.L2.SG.Corank.Pair.psnd] at hp1 hp2
  obtain ⟨rfl, hc1⟩ := hp1
  obtain ⟨rfl, hc2⟩ := hp2
  exact scal_move (hrows.1 _ mp) ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨⟨repF _, h2⟩, hGr⟩ ⟨⟨F'', h3⟩, hGF⟩ h2e.symm h3e.symm
    ⟨bp, ip, hps, hpsc⟩

variable (Zd : LocDat D)



theorem lprExist_of (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprExist Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'' hP p
  obtain ⟨w, hγ, -⟩ := hC
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  have hF : FixedHyp D γ.lam (lf D F0) := hR.2.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGr : Gval (lf D F0) (repF γ) ≠ 0 := gval_repF γ w hγ
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) := by
    obtain ⟨hgen, -⟩ := hγ.1
    obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
    have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
      (h1e.trans h2e.symm)
    exact (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hE := hP.1
  obtain ⟨β, hPair, hs, hsc⟩ := scal_rep hrows γ Z F'' hP hGr
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u'
  have hG := Formalism.L2.SG.Pf.ScalarFramePf.gfacts_of γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1
    hE.2.2.2.1.1 hPair hs hsc hGr hE.1.2.2 hT hT'
  have hIo := hI D Zd γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 h2.2.1 hE.1.2.1 hPair
    hgenR hE.2.2.1 hs hsc hGr hE.1.2.2 hT hT' p
  have hξ := admissibility_witness_unitriangular γ.lam (lf D F0) F''
  have hG2 := gfacts_frameAct (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hG
  have hI2 := iotaEl_frameAct Zd p (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hIo
  obtain ⟨hId, hRe⟩ := Formalism.L2.SG.Pf.ScalarFramePf.identResp_lt Zd p γ.lam (frame (lf D F0)) _ (frame F'') β
    (Tu D u) (Tu D u') hG2 hI2
  exact ⟨Formalism.L2.SG.Pf.ScalarFramePf.phiP Zd p γ.lam (frame (lf D F0)) _ (frame F'') β hG2, hId, hRe.2.2.2.1,
    hRe.2.2.1, hRe.2.2.2.2⟩

theorem lprPart_of_iota (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprPart Zd u u' F0 what₂ :=
  lprPart_of' Zd (lprExist_of Zd hI)

end LprEx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem gS_typed (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O, ∃ w' ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w ∧
        w * w' = 1 := by
  obtain ⟨sg, hsg, hq, -⟩ := typed_data Zd p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E),
    Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p, ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

theorem localLattice_mono {A B : Submodule (𝓞 D.host.E) (VS D).V} (h : A ≤ B) : lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_O_M {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O) : a ∈ (Zd.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.hO Zd p]; exact ha

theorem smul_gS_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [← Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h1 : ((gS D : ℕ) : D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • y := by
      rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) y, map_natCast]
    rw [SetLike.mem_coe, h1]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • v) = o • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
      show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hv

theorem untyped_mem (hs : (Zd.M p).split = none) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  have e := Formalism.L2.SG.Pf.StabIntSh.gS_mul_uP Zd.δ Zd.M Zd.agree p hs
  have hv' : v = (D.s.atP p).ιE (uP p : D.host.E) • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
    rw [smul_smul, mul_comm, e, one_smul]
  rw [hv']
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p) (smul_gS_mem Zd p F F' hv)

theorem typed_q_mem (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨w, -, w', hw', he, hww⟩ := gS_typed Zd p g hs
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' • v) := by
    rw [he, smul_smul, mul_assoc, hww, mul_one]
  rw [e]
  exact smul_gS_mem Zd p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw' hv)

theorem l1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')
    (f : Fin (D.R.rS + 1) → Vp D p) (s : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hs : ∀ a, s a ∈ (D.s.atP p).O)
    (hf : ∀ i : Fin D.R.rS, f i.castSucc = (s i.castSucc * frFac Zd.δ p i.castSucc) • baseChange₂ D p (G.fl.e i))
    (hprim : (locH Zd p).Prim (lattice₂ D Zd.M p Λ) f) (hXS : XLam Λ G = XS D G.fl) {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) (hvX : v ∈ (locH Zd p).X f) : v ∈ lattice₂ D Zd.M p (XLam Λ G) := by
  have hvE : v ∈ Submodule.span (D.s.atP p).Ep (Set.range f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) hvX
  have hvO := hprim.2.2 v hv hvE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Zd.M p).L.O).1 hvO
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (D.s.atP p).Ep).1 hvX
  have key : (c (Fin.last D.R.rS) : (D.s.atP p).Ep) = 0 := by
    have h0 : ∑ a, ((c a : (D.s.atP p).Ep) - Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a) • f a = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (f := fun a => Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a • f a)]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
      rw [he, ← hc, sub_eq_zero]
      rfl
    have := Fintype.linearIndependent_iff.1 hprim.2.1 _ h0 (Fin.last D.R.rS)
    simpa using this
  rw [← hc, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) ?_
  · rw [hf, hXS, Formalism.L2.SG.Pf.BBTie.bt_latP_XS Zd p (Formalism.L2.SG.Pf.locDiffC_holds D Zd) G.fl, mul_smul]
    have hm : frFac Zd.δ p i.castSucc • baseChange₂ D p (G.fl.e i) ∈ Submodule.span (Zd.M p).L.O
        (Set.range fun a : Fin D.R.rS => frFac Zd.δ p a.castSucc • baseChange₂ D p (G.fl.e a)) := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.smul_mem _ (⟨s i.castSucc, mem_O_M Zd p (hs _)⟩ : (Zd.M p).L.O) hm
  · have : c (Fin.last D.R.rS) • f (Fin.last D.R.rS) = 0 := by
      rw [Subring.smul_def, key, zero_smul]
    rw [this]; exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
end
end

section

noncomputable section

open scoped Classical
open Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat

open FsLA BwdBetaS OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

def projL {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

def moveL {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u' (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

theorem pc_of_orth {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) {y : S.V} (hy : ∀ k, S.hT (u k) y = 0) :
    pc u y = 0 := by
  have h0 : (fun k => S.hT (u k) y) = 0 := funext fun k => hy k
  rw [pc, h0, Matrix.mulVec_zero]

theorem lin_zero {ι : Type*} [Fintype ι] (u : ι → S.V) : lin u 0 = 0 := by simp [lin]

theorem isometry_extension_two {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (u u' : ι → S.V) (w : κ → S.V) (hG : gram S u' u' = gram S u u) (hdet : (gram S u u).det ≠ 0)
    (hdetw : (gram S w w).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range w))
    (hkey : ∀ y y', (∀ k, S.hT (u k) y = 0) → (∀ k, S.hT (u k) y' = 0) →
      S.hT (lin w (pc w y)) (lin w (pc w y')) = 0) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ (∀ i, g (u i) = u' i) ∧
      (∀ y, (∀ k, S.hT (u k) y = 0) → g y = y - lin w (pc w y)) := by
  let P : S.V →ₗ[E] S.V := LinearMap.id - projL u
  let β : S.V →ₗ[E] S.V := (LinearMap.id - projL w) ∘ₗ P + moveL u u'
  have hβ : ∀ v, β v = ((v - lin u (pc u v)) - lin w (pc w (v - lin u (pc u v)))) + lin u' (pc u v) :=
    fun v => rfl
  have hsp' : ∀ c, lin u' c ∈ Submodule.span E (Set.range w) := fun c =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsp i)
  have hGe : ∀ i j, S.hT (u' i) (u' j) = S.hT (u i) (u j) := fun i j => congrFun (congrFun hG i) j
  have hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y := by
    intro x y
    set x' := x - lin u (pc u x) with hx'
    set y' := y - lin u (pc u y) with hy'
    have hx'u : ∀ k, S.hT (u k) x' = 0 := fun k => hT_u_rem u hdet x k
    have hy'u : ∀ k, S.hT (u k) y' = 0 := fun k => hT_u_rem u hdet y k
    have hk := hkey x' y' hx'u hy'u
    rw [hβ, hβ]

    have t1 : S.hT (x' - lin w (pc w x')) (lin u' (pc u y)) = 0 := (hT_span_rem w hdetw x' _ (hsp' _)).2
    have t2 : S.hT (lin u' (pc u x)) (y' - lin w (pc w y')) = 0 := (hT_span_rem w hdetw y' _ (hsp' _)).1
    have t3 : S.hT (lin u' (pc u x)) (lin u' (pc u y)) = S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      rw [hT_lin_lin, hT_lin_lin]; simp only [hGe]
    have t4 : S.hT (x' - lin w (pc w x')) (lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw x' _ (lin_sub w _)).2
    have t5 : S.hT (lin w (pc w x')) (y' - lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw y' _ (lin_sub w _)).1
    have t6 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) = S.hT x' y' := by
      have e1 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) =
          S.hT (x' - lin w (pc w x')) y' := by
        rw [map_sub, t4, sub_zero]
      have e2 : S.hT (lin w (pc w x')) y' = 0 := by
        have := t5
        rw [map_sub, hk, sub_zero] at this
        exact this
      rw [e1, map_sub S.hT x' (lin w (pc w x')), LinearMap.sub_apply, e2, sub_zero]
    have hxy : S.hT x y = S.hT x' y' + S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      have dx : x = x' + lin u (pc u x) := by rw [hx']; abel
      have dy : y = y' + lin u (pc u y) := by rw [hy']; abel
      conv_lhs => rw [dx, dy]
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [(hT_span_rem u hdet x _ (lin_sub u _)).2, (hT_span_rem u hdet y _ (lin_sub u _)).1]
      ring
    rw [← hx', ← hy']
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [t1, t2, t3, t6, hxy]
    ring
  have hinj : Function.Injective β := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    refine (Submodule.mem_bot E).2 (S.nondeg.1 v fun y => ?_)
    rw [← hiso v y, hv, map_zero, LinearMap.zero_apply]
  have hbij : Function.Bijective β := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  refine ⟨LinearEquiv.ofBijective β hbij, hiso, fun i => ?_, fun y hy => ?_⟩
  · show β (u i) = u' i
    rw [hβ, pc_self u hdet, lin_single, lin_single, sub_self]
    have : pc w (0 : S.V) = 0 := by
      have := pc_smul w 0 0
      simpa using this
    rw [this, lin_zero, sub_zero, zero_add]
  · show β y = y - lin w (pc w y)
    rw [hβ, pc_of_orth u hy, lin_zero, lin_zero, sub_zero, add_zero]

variable {r : ℕ}

theorem norm_om_ne {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) : 1 + TA * S.hT Ω Ω ≠ 0 := by
  have hx := om_zcoef A B hdet hΩ
  set c := (Zhat A B)⁻¹ (Fin.last r) (Fin.last r) with hc
  set x := Ω - c • B.z with hxd
  have hΩe : Ω = x + c • B.z := by rw [hxd]; abel
  have hxx : S.hT x x = 0 := NMoveP.hT_X_X B hx hx
  have hxz : S.hT x B.z = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rw [NMoveP.fvecL] at h
    rw [BwdNA.hsw S B.z x, h, star_zero]
  have hzx : S.hT B.z x = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rwa [NMoveP.fvecL] at h
  have hnorm : S.hT Ω Ω = star c * c * (-TB) := by
    rw [hΩe]
    simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, hxx, hxz, hzx,
      B.z_norm, smul_eq_mul, starRingEnd_apply, mul_zero, zero_add, add_zero]
    ring
  have hcl : c = leadMinorE (Zhat A B) r / (Zhat A B).det := inv_last _
  intro h0
  apply hG
  unfold Gflag Dl
  rw [FsLA.leadMinorE_full]
  rw [hnorm, hcl, star_div₀] at h0
  have hs : star (Zhat A B).det ≠ 0 := star_ne_zero.2 hdet
  field_simp at h0
  linear_combination h0

theorem key_X {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) {q : S.V}
    (hq : q ∈ Submodule.span E (Set.range (Sum.elim A.fvec B.fvec))) (hqA : ∀ a, S.hT (A.fvec a) q = 0)
    (hqΩ : S.hT Ω q = 0) : q ∈ A.X := by
  obtain ⟨x, hx, c, rfl⟩ := dec A B hdet hΩ hq hqA
  have hΩx : S.hT Ω x = 0 := by
    rw [BwdNA.hsw S x Ω]
    have : x ∈ A.X := hx
    have h := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 (show Ω ∈ orth S A.X from ?_) x this
    · rw [h, star_zero]
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun y hy => ?_
      change y ∈ Submodule.span E (Set.range A.e) at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [← fvec_cs, hΩ.2]
        simp [Fin.castSucc_ne_last]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      | smul t y _ hy => rw [BwdNA.hT_smulL, hy, mul_zero]
  have hΩz : S.hT Ω A.z = 1 := by
    rw [BwdNA.hsw S A.z Ω, ← fvec_last, hΩ.2]
    simp
  have h1 : S.hT Ω (x + c • (A.z + TA • Ω)) = c * (1 + TA * S.hT Ω Ω) := by
    rw [map_add (f := _), hΩx, zero_add, map_smul, map_add (f := _), map_smul, hΩz, smul_eq_mul, smul_eq_mul]
  rw [h1] at hqΩ
  have hc : c = 0 := (mul_eq_zero.1 hqΩ).resolve_right (norm_om_ne A B hdet hΩ hG)
  rw [hc, zero_smul, add_zero]
  exact hx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem starExists2_of_good (hP : CtxP u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_parts Zd u u' F0 what₂ hP (cohGen_of Zd (cohInt_holds Zd) (cohDG_holds Zd) hGood)
    (cohIota_holds Zd) hGood

theorem starExists2_holds (hP : CtxP u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_good Zd u u' F0 what₂ hP (cohGood_of Zd globGramNe_holds)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem bwdTerm'_holds : BwdTerm' Zd u u' F0 what₂ := bwdTerm'_of_gx (genXiRev_holds Zd)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def BaseAt (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Prop :=
  ∃ c : UP p, phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = (c : GG p) • a.mat ∧
    ∀ x : UP p, ((x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) ↔ (x : GG p) • a.mat = a.mat)

end Formalism.L2.SG.Pf.CountAt
end
end
