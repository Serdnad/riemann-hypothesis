module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle063
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle069
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle066
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle062
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle068
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle009
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle071
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle060
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem normRepElig_of (hN : PairVal.NormRepExists D u u' F0 what₂) : NormRepElig u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨y, hy⟩ := hN γ w hγ.2 (PCount.eligRel_holds γ w hγ) hγ.1.1
  exact ⟨(w, y), hy⟩

theorem locClsE_of (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hO : ∀ Zd : TermLoc.LocDat D, PCount.InOrbZ Zd u u') : LocClsE M δ u u' F0 what₂ := by
  intro γ w hγ p
  refine ⟨fun a b => ?_, hO ⟨δ, M, hA⟩ w (zT γ) (PCount.atMat_zT hN hrows hγ (PCount.eligRel_holds γ w hγ)) p⟩
  obtain ⟨Λ, hΛ, F', hF'⟩ := dnInDens_of (normRepElig_of hN) hrows γ w hγ
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hA u u' hT F0 what₂ hrows Λ hΛ (zT γ) F' hF' p
  simp only [yT, LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI a b) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolIn

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Formalism.L2.SG.Pf.ZsVolGrp Formalism.L2.SG.Pf.ZsVolShape Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def FrameShapeP : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ s ∈ NLam γ.lam (lf D F0) ∩ NLam γ.lam F', ∀ uu uu' : MatR D, IsUpUni uu → IsUpUni uu' →
      (∀ b, s (F0.fvec b) = ∑ c, uu c b • F0.fvec c) → (∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c) →
        Formalism.L2.SG.Pf.StabIntSh.EntryShape D uu.conjTranspose
          (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS)

theorem stabInCZ_of (hF : FrameShapeP M δ u u' F0 what₂) : Formalism.L2.SG.Pf.ZsVolOrb.StabInCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨_, _, hL, hU, hZ⟩ := hN
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hP.1.pos.ne'
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  refine (Subgroup.closure_le _).2 ?_
  rintro a ⟨s, ⟨hsF, hsF'⟩, uu, huu, ha⟩
  have hsF0 := hsF
  have hsF'0 := hsF'
  obtain ⟨⟨hiso, _⟩, hf1, hf2⟩ := hsF
  obtain ⟨⟨_, _⟩, hg1, hg2⟩ := hsF'
  obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
  obtain ⟨uu', huu', hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl s hg1 hg2
  have heq : uu = uu0 :=
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 huu hu0
  subst heq
  have hZc := Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhat_conj F0 F'.fl s hiso uu uu' hu0 hu'
  have hdet : IsUnit uu.conjTranspose.det := by
    rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0)]; exact isUnit_one
  let a' : GLR D := Matrix.nonsingInvUnit uu.conjTranspose hdet
  have ha' : (a' : MatR D) = uu.conjTranspose := rfl
  have hshape := hF γ w F' L U ⟨hA, hT, hR, hP, hE, ⟨‹_›, ‹_›, hL, hU, hZ⟩⟩ s ⟨hsF0, hsF'0⟩ uu uu' huu0 huu' hu0 hu'
  have hmem : a ∈ stZSet M δ u u' (ZhatL (lf D F0) F') L := by
    refine (mem_stZSet_iff M δ u u' hA _ L a).2 ⟨a', by rw [ha', ha], by rw [ha']; exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_conjT huu0,
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS, Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn huu', ?_, by rw [ha']; exact hshape⟩
    rw [ha', Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq]
    show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
      (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) = Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS
    rw [show uu.conjTranspose * (Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) *
        (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) =
      uu.conjTranspose * Zhat F0 F'.fl * (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) * uu' *
        Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS by simp only [Matrix.mul_assoc],
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one, ← hZc]
  exact (mem_CZ M δ u u' _ L hLd a).2 hmem

end Formalism.L2.SG.Pf.ZsVolIn

end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps
  Formalism.L2.SG.NGCut.NormalVectorPairings

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.MainEqNml

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def OccTG (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u) : Prop :=
  t ∈ (Y.tO u u).genSet ∧ (Y.tO u u).vec t ≠ 0 ∧ clsG Y u t = c ∧ ptPN t = γ

theorem occ_iffG (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν ↔ ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    have e : t ∈ (Y.tO u u).genSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, ⟨e, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    have e : t ∈ (genT (Y.tO u u)).ngSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, e, h2, h3, h4, h5⟩

variable {Y u}

theorem relC_of_occG (hE : ScalEquivOn (Y.tO u u)) {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS}
    {t0 t : TauC Y u u} (h0 : OccTG Y u c γ t0) (h : OccTG Y u c γ t) : RelC Y u u t0 t := by
  unfold Formalism.L2.SG.Pf.MainEqSteps.ScalEquivOn at hE
  obtain ⟨h01, h02, h03, h04⟩ := h0
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hmem : t ∈ clsG Y u t := ⟨h1, rfl, (hE.1 t h1).1, (hE.1 t h1).2⟩
  rw [h3, ← h03] at hmem
  exact ⟨hmem.2.1, hmem.2.2.1⟩

end Formalism.L2.SG.Pf.MainEqNml

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqNml

theorem nmlInvG_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : Formalism.L2.SG.NGCut.NormalInvariants.Gen.NmlInvG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iffG Y u νL νB ng c γ ν0).1 hν0
  have hE : ScalEquivOn (Y.tO u u) := stepClassG_holds D X Y u (g_ge_three hctx) hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u := fun ν =>
    if h : ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν →
      OccTG Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν := by
    intro ν hν
    have h := (occ_iffG Y u νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occG hE ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occG hE ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occG hE ht0 hp1) (relC_of_occG hE ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem ident_generic {r : ℕ} (Lam₁ Lam₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂) :
    H.Ident (⟨Lam₁, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨Lam₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (_root_.Formalism.L2.SG.Pf.ScalarFramePf.qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.SendsTo (_root_.Formalism.L2.SG.Pf.ScalarFramePf.qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).toLinearMap 1 1 (f₁ (Fin.last r)) (f₂ (Fin.last r)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ?_⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz

end Generic

section Concrete

variable {D : D7} (Zd : LocDat D) (p : PlF D)

theorem omp_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Zd.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)]
  congr 2 <;> ring

theorem betaP_fix {ι : Type} [Fintype ι] (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u y : ι → (VS D).V)
    (hform : ∀ v, g v = v + ∑ k, (VS D).hT (u k) v • y k) (w : Vp D p)
    (hw : ∀ k, (locH Zd p).h w (baseChange₂ D p (u k)) = 0) : betaP p g w = w := by
  have hk : ∀ k, ∑ i, w i * (D.s.atP p).ιE ((VS D).hT (u k) ((VS D).frame i)) = 0 := by
    intro k
    have e := hw k
    conv_lhs at e => rw [vp_eq_sum p w]
    rw [h_sum_left] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermitian_base_change_smul Zd p]
    rfl
  conv_lhs => rw [vp_eq_sum p w]

  rw [map_sum]
  simp only [map_smul, betaP_bc, hform, map_add (f := _), baseChangeAt_sum, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul]
  rw [← vp_eq_sum p w, Finset.sum_comm]
  simp only [← Finset.sum_smul, hk, zero_smul, Finset.sum_const_zero, add_zero]

theorem gdl_eq (f g : Fin (D.R.rS + 1) → (VS D).V) (l : ℕ) : GDl f g l = leadMinorE (starZh f g) l := by
  unfold GDl leadMinorE
  split_ifs <;> rfl

theorem xspan_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => F.fvec a.castSucc) = F.X := by
  have : (fun a : Fin D.R.rS => F.fvec a.castSucc) = F.e := funext fun a => by simp [FlagG.fvec]
  rw [this]; rfl

end Concrete

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def StarIdentU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)) →
    ∀ F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z → starCompat γ F'₂ →
      starInU γ F'₂ →
      ∀ p, ∃ φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂),
        LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ'

def StarFrameU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
      starInU γ F'₂

variable {u u' F0 what₂}

theorem starFrameU_holds : StarFrameU u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨hZ, hZ₁, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  obtain ⟨h1, h2⟩ := star_frame_orthogonal γ
  obtain ⟨F₂, hZh, hom, hsp⟩ := FsLA.frame_la F0 (starFrame γ) h1 h2 Z hZ hZ₁ hx
  refine ⟨⟨F₂, F₂.z⟩, hZh, ⟨?_, ?_⟩, fun b => hsp b⟩
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))) = Z := hZh
    rw [e, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    exact hx
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))) = Z := hZh
    rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full, e]
    exact hom

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormRelC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').nzSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

end Formalism.L2.SG.Pf.FormRel

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel

theorem formNGC_of_rel (h : FormRelC) : Formalism.L2.SG.NGVanish.FormNGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u u' hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u').nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u' hx ν hν t hnz hv

theorem formGC_of_rel (h : FormRelC) : Formalism.L2.SG.Pf.MainEqVanish.FormGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u).nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u hx ν hν t hnz hv

end Formalism.L2.SG.Pf
end
end
