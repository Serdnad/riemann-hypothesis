module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle032
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf.MainEqFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ := ∏ p, L.aZ p (d p)

variable {D : D7}

theorem localLeG_of_fam {Z : LocDat D} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (C1 C0n : ℕ) (AAre : ℝ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS (C1 : ℝ))
    (h : ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ Fm : LocFam Z Cl Nu,
      FamOKS N γ S C0n AAre (fun L => ampG L) Fm) :
    LocalInputLeG X N C1 C0n AAre := by
  intro γ hγ S
  obtain ⟨Fm, hR, hex, hOm, hD, hn, hV0, hrw, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  have hrank : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    rw [finrank_Vp]
    have h1 := D.R.r_eq
    have h2 : 2 * D.R.rS + 2 = D.R.m := by
      have hm2 := D.R.two_le_m
      obtain ⟨j, hj⟩ := D.R.m_even
      simp only [Formalism.BasicNotions.Ranks.rS]; omega
    omega
  have hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ) := fun p hp =>
    hQ (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p) (Z.agree p).1 (Vp D p) (locH Z p) (hrank p) (Fm.FP p) (hR p hp)
  have hq2 : ∀ p ∈ Fm.P, 2 ≤ LocNG.qF (D.s.atP p).Fp := fun p hp => Formalism.MainNotions.KappaEndpoints.two_le_residue_card (Z.agree p).1
  have hqH : ∀ p ∈ Fm.P, ¬ (Fm.FP p).PrimeTo → (LocNG.qF (D.s.atP p).Fp : ℝ) ≤ (Fm.FP p).Hp := fun p hp hpr =>
    Formalism.L2.SG.Pf.residue_le_height_nonprime (Z.agree p).1 (hR p hp) (hex p hp) hpr
  have hH1 : ∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp := by
    intro p hp
    by_cases hpr : (Fm.FP p).PrimeTo
    · exact le_of_eq ((hNG p hp (Fm.R p) (Fm.d0 p)).2.2.2 hpr).1.symm
    · have h2 : (2 : ℝ) ≤ (LocNG.qF (D.s.atP p).Fp : ℝ) := by exact_mod_cast hq2 p hp
      linarith [hqH p hp hpr]
  have hHp : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp := fun p hp => le_trans zero_le_one (hH1 p hp)
  have hB : Fm.toL.Basic := by
    refine ⟨fun p d => ?_, fun p => hH1 p.1 p.2, fun p => hq2 p.1 p.2, fun p hp => hqH p.1 p.2 ((hOm p).1 hp),
      fun p => ENNReal.toReal_nonneg, hV0, hrw⟩
    show 0 ≤ LocNG.Datum.wt (Fm.d0 p.1) d.1
    unfold LocNG.Datum.wt LocNG.volRel
    positivity
  exact ⟨Fm.toL, hB, (ngAt_toL Fm C1 hk hNG hD hn hHp).2, hM, hU, ha, hH, hpos, hle⟩

def StepFamG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

end Formalism.L2.SG.Pf.MainEqFam

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqFam

theorem stepLocPinnedG_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFamG) : StepLocPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Loc.HermSp.LprU

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LprExist : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      ∃ ψ₀ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'),
        (locH Zd p).Ident (tLoc Zd p γ) ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩
          (LinearEquiv.refl _ _) ψ₀ ∧
        (locH Zd p).SendsTo ψ₀.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last _)) (locF' Zd p F' (Fin.last _)) ∧
        ψ₀ '' (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' =
          (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F') ∧
        ∀ g, (Zd.M p).split = some g →
          Prod.map ψ₀ (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
            (locH Zd p).iotaGraph g (tLoc Zd p γ) =
            (locH Zd p).iotaGraph g
              ⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def LprNondeg : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f') ∧
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (locF' Zd p F')) ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (tLoc Zd p γ).f').det ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F')).det ∧
      Iso' (locH Zd p) (tLoc Zd p γ).f' ∧ Iso' (locH Zd p) (locF' Zd p F')

variable {u u' F0 what₂}



theorem lprPart_of (hE : LprExist Zd u u' F0 what₂) (hN : LprNondeg Zd u u' F0 what₂) : LprPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p ψ hI hz
  obtain ⟨ψ₀, hI₀, hz₀, hL, hι⟩ := hE hrows γ Z hC F' hP p
  obtain ⟨n1, n2, d1, d2, k1, k2⟩ := hN hrows γ Z hC F' hP p
  have h : ψ = ψ₀ := psi_unique (H := locH Zd p) (tLoc Zd p γ)
    ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩ (LinearEquiv.refl _ _) ψ ψ₀
    n1 n2 d1 d2 k1 k2 hI hI₀ hz hz₀
  rw [h]
  exact ⟨hL, hι⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP OmL

namespace OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem mat_frameAct {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (frameAct (frame F') ξ b)) =
      Zhat F0 F'.fl * ξ.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  exact Matrix.ext fun a b => Formalism.L2.SG.Pf.AtPt.brS_frameAct (lf D F0) F' ξ a b

theorem map_det_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) :
    ((Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE).det =
      (D.s.atP p).ιE (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det := (RingHom.map_det _ _).symm

theorem det_ne_of_unit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V)
    (h : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det ≠ 0 := by
  intro h0
  rw [zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, h0, map_zero, mul_zero, zero_mul] at h
  exact not_isUnit_zero h

theorem gdl_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (l : ℕ) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl F0.fvec F'.fvec l = Formalism.MainNotions.S.Dl F0 F' l := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs <;> rfl

end OmD

open OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem modeMatrixDet_eq_adjointDet : OmDet Zd u u' F0 what₂ := by
  intro _ γ Z _ F'₂ φ φ' hS F' hP
  obtain ⟨p⟩ := Formalism.L2.SG.Pf.LocModel.plF_nonempty D
  have hT2 := hS.2.1 p
  have hunγ := hT2.1.1.2.2.2.1
  rw [dl_last] at hunγ
  have hdγ : (ZhatL (lf D F0) (repF γ)).det ≠ 0 := by
    have h1 := det_ne_of_unit Zd p F0
      (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) hunγ
    rw [mat_frameAct, Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  refine ⟨hdγ, fun hZ => ?_⟩
  have hZ2 : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z := hS.1
  have hD2 : (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = 0 := by
    rw [dl_last, zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, hZ2, hZ, map_zero, mul_zero, zero_mul]
  have hId : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' D.R.rS *
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) =
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS *
        (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) := hT2.2.2.2.1.2.2.2.2.2
  rw [hD2, mul_zero] at hId
  obtain ⟨uγ, huγ⟩ := hT2.1.1.2.2.2.1
  rw [← huγ] at hId
  have hDr := (Units.mul_left_eq_zero uγ).1 hId.symm
  have e := Formalism.L2.SG.Pf.ScalarFramePf.dl_loc Zd p F0.fvec F'₂.fl.fvec (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p)
    (Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p) D.R.rS (Nat.le_succ _)
  rw [show (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS = _ from e] at hDr
  have hu1 : IsUnit (∏ i : Fin D.R.rS, (Zd.M p).L.cj
      (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.castLE (Nat.le_succ _) i))) :=
    IsUnit.prod_univ_iff.2 fun i => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map _
  have hu2 : IsUnit (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p (Fin.castLE (Nat.le_succ _) i)) :=
    IsUnit.prod_univ_iff.2 fun i => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _
  have hg := (hu1.mul hu2).mul_right_eq_zero.1 hDr
  rw [map_eq_zero_iff _ (D.s.atP p).ιE.injective, gdl_eq] at hg
  have hG := hP.1.1.2.2
  apply hG
  apply Eq.trans (fwdCut_gval_congr (lf D F0) F' F'₂ (hP.1.2.2.2.2.trans hS.1.symm))
  show Formalism.MainNotions.S.Gflag F0 F'₂.fl = 0
  unfold Formalism.MainNotions.S.Gflag
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.Dl_succ, hg, show Zhat F0 F'₂.fl = Z from hS.1, hZ]
  simp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

def BridgeIso : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (m : ℕ) (n s : E) (P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) E),
    IsLo L₁ → IsUp U₁ → IsLo L₂ → IsUp U₂ → P₁ = L₁ * X₁ * U₁ → P₂ = L₂ * X₂ * U₂ →
    (∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 ∧
      X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0) →
    X₁ (Fin.last m) (Fin.last m) = s → X₂ (Fin.last m) (Fin.last m) = s → IsUnit (s + n) → n ∈ M.R →
    ∀ (Y₁ Y₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R),
      (∀ a b : Fin m, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin m, (be₁ a : E) = P₁ a.castSucc (Fin.last m) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last m) ∧
        (al₁ a : E) = P₁ (Fin.last m) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last m) a.castSucc) →
      (∀ a b, P₁ a b ∈ M.R) → (∀ a b, P₂ a b ∈ M.R) →
      ∀ Z₁ Z₂ : M.Mat (m + 1), Z₁.Z.map M.R.subtype = P₁ + n • Ecorner m →
        Z₂.Z.map M.R.subtype = P₂ + n • Ecorner m → M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂ = M.nIso Z₁ Z₂

section Det

variable {K : Type*} [CommRing K] {m : ℕ}

theorem det_shift {n s : K} {P X L U : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hL : IsLo L) (hU : IsUp U)
    (hP : P = L * X * U) (hX : ∀ a : Fin m, X a.castSucc (Fin.last m) = 0 ∧ X (Fin.last m) a.castSucc = 0)
    (hs : X (Fin.last m) (Fin.last m) = s) : (P + n • Ecorner m).det = (s + n) * leadM P m := by
  have e : P + n • Ecorner m = L * (X + n • Ecorner m) * U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU, hP]
  have hX' : ∀ a : Fin m, (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a.castSucc (Fin.last m) = 0 ∧
      (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) a.castSucc = 0 := fun a => by
    simp [Ecorner, (hX a).1, (hX a).2, Fin.castSucc_ne_last]
  rw [e, Matrix.det_mul, Matrix.det_mul, det_lo' hL, det_up' hU, one_mul, mul_one, det_of_corner _ hX',
    leadM_add_corner, hP, leadM_mul hL hU]
  simp [Ecorner, hs]

end Det

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem lead_eq_head (M : Loc.Model F E) {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (Y : M.Mat m)
    (hY : ∀ a b : Fin m, (Y.Z a b : E) = P a.castSucc b.castSucc) : leadM P m = (Y.Z.map M.R.subtype).det := by
  unfold leadM
  rw [dite_eq_left (Nat.le_succ m)]
  congr 1
  ext a b
  exact (hY a b).symm

end Model

theorem bridgeBA_of (hI : BridgeIso) : BridgeBA := by
  intro F _ _ _ E _ _ _ _ M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂
    be₁ be₂ al₁ al₂ hY hba hi₁ hi₂
  have hX₁ : ∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).1, (hX a).2.1⟩
  have hX₂ : ∀ a : Fin m, X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).2.2.1, (hX a).2.2.2⟩
  have hu₁ : IsUnit (P₁ + n • Ecorner m).det := by
    rw [det_shift hL₁ hU₁ hP₁ hX₁ h₁, lead_eq_head M P₁ Y₁ fun a b => (hY a b).1]
    exact hsn.mul Y₁.unit
  have hu₂ : IsUnit (P₂ + n • Ecorner m).det := by
    rw [det_shift hL₂ hU₂ hP₂ hX₂ h₂, lead_eq_head M P₂ Y₂ fun a b => (hY a b).2]
    exact hsn.mul Y₂.unit
  have hint : ∀ {P : Matrix (Fin (m + 1)) (Fin (m + 1)) E}, (∀ a b, P a b ∈ M.R) →
      ∀ a b, (P + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) E) a b ∈ M.R := fun hP a b => by
    simp only [Matrix.add_apply, Matrix.smul_apply, Ecorner, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact M.R.add_mem (hP a b) (by rw [mul_one]; exact hn)
    · rw [mul_zero, add_zero]; exact hP a b
  refine ⟨mkMat M _ (hint hi₁) hu₁, mkMat M _ (hint hi₂) hu₂, rfl, rfl, ?_⟩
  exact hI M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂ be₁ be₂ al₁ al₂ hY hba
    hi₁ hi₂ _ _ rfl rfl

theorem partnerCount_of_iso {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D)
    (hI : IntGenP Zd) (hB : BridgeIso) : PartnerIsomorphismCount Zd :=
  partnerCount_of_integral Zd hT2 hI (bridgeBA_of hB)

end Formalism.L2.SG.Pf.PCount
end
end
