module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
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

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.Pf.MainEqCut

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.MainEqSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abs

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

def ScalEquivOn (X : PB.Terms τ Rw I H H₁) : Prop :=
  (∀ t ∈ X.genSet, X.s0 t t = 1 ∧ X.scal t t) ∧
  (∀ t ∈ X.genSet, ∀ t' ∈ X.genSet, X.rowOf t = X.rowOf t' → X.s0 t t' = 1 → X.scal t t' →
    X.s0 t' t = 1 ∧ X.scal t' t) ∧
  (∀ t ∈ X.genSet, ∀ t' ∈ X.genSet, ∀ t'' ∈ X.genSet, X.rowOf t = X.rowOf t' → X.rowOf t' = X.rowOf t'' →
    X.s0 t t' = 1 → X.scal t t' → X.s0 t' t'' = 1 → X.scal t' t'' → X.s0 t t'' = 1 ∧ X.scal t t'')

end Abs

section Conc

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

theorem classInputG_of (h : ScalEquivOn (Y.tO u u)) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf)
    (ng : PN.Pts D.host.E D.R.rS → ℝ) : PN.ClassInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) := by
  obtain ⟨hrefl, hsymm, htrans⟩ := h
  have hset : ∀ t, t ∈ (genT (Y.tO u u)).ngSet ↔ t ∈ (Y.tO u u).genSet := fun t => by
    simp [PB.Terms.ngSet, PB.Terms.genSet, genT]
  have hs0 : ∀ t t', (genT (Y.tO u u)).s0 t t' = 1 ↔
      (Y.tO u u).s0 t t' = 1 ∧ (Y.tO u u).scal t t' := fun t t' => by
    simp only [genT]
    split_ifs with hc <;> simp [hc]
  intro t ht t' ht'
  rw [hset] at ht ht'
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (genT (Y.tO u u)).s0 t t' = 1) ↔
    clsG Y u t = clsG Y u t'
  rw [hs0]
  constructor
  · rintro ⟨hrow, hs, hsc⟩
    obtain ⟨hs', hsc'⟩ := hsymm t ht t' ht' hrow hs hsc
    ext t''
    simp only [clsG, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hg, hr, h1, h2⟩
      exact ⟨hg, hr.trans hrow, htrans t' ht' t ht t'' hg hrow.symm hr.symm hs' hsc' h1 h2⟩
    · rintro ⟨hg, hr, h1, h2⟩
      exact ⟨hg, hr.trans hrow.symm, htrans t ht t' ht' t'' hg hrow hr.symm hs hsc h1 h2⟩
  · intro hcl
    have hmem : t' ∈ clsG Y u t' := ⟨ht', rfl, (hrefl t' ht').1, (hrefl t' ht').2⟩
    rw [← hcl] at hmem
    simp only [clsG, Set.mem_setOf_eq] at hmem
    obtain ⟨-, hr, h1, h2⟩ := hmem
    exact ⟨hr.symm, h1, h2⟩

def AmpVanishG (νL : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ c γ ν, J2of Y u u νL γ = 0 → grpGC Y u c γ ν = 0

theorem ampInputG_of_vanish (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (h : AmpVanishG Y u νL) : PN.AmpInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) := by
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => by
    unfold J2of
    split_ifs <;> positivity
  refine ⟨fun c γ ν => div_nonneg (sq_nonneg _) (hJ γ), fun γ => hJ γ, fun c γ ν => ?_⟩
  have hset : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := by
    ext t
    simp [PB.Terms.ngSet, PB.Terms.genSet, genT]
  have hg : PN.grp (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν = grpGC Y u c γ ν := by
    unfold PN.grp grpGC
    rw [hset]
    rfl
  rw [hg]
  change ‖grpGC Y u c γ ν‖ ^ 2 ≤ a2GC Y u νL c γ ν * J2of Y u u νL γ
  unfold a2GC
  rcases (hJ γ).eq_or_lt with h0 | hpos
  · rw [h c γ ν h0.symm, norm_zero]
    simp
  · rw [div_mul_cancel₀ _ hpos.ne']

end Conc

def StepClassG : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → ConcTie X Y →
    ScalEquivOn (Y.tO u u)

def StepNormalsG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.NormalsInput (genT (Y.tO u u)) (NOfG Y u νL νB ng)
          ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
            (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f))

def StepPointsG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.PointsInput (genT (Y.tO u u)) (NOfG Y u νL νB ng)

def StepHeightG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.HeightInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) ((X.B.g : ℝ) ^ D.R.f)

def StepNormOneG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS),
        PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ∧ 1 ≤ NDPt D.host.rdE γ

theorem stepHeightG_of_normOne (h : StepNormOneG) : StepHeightG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng γ hγ => ?_⟩
  obtain ⟨hG, hD⟩ := hC C' Cl h1 h2 D large₂ X Y u hc νL νB ng γ hγ
  refine ⟨hG, hD, ?_⟩
  have key : ((X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)))⁻¹ ≤
      (X.B.g : ℝ) ^ D.R.f := by
    rcases Nat.eq_zero_or_pos X.B.g with h0 | hpos
    · have hN : 0 < (2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E) :=
        Nat.mul_pos (by omega) Fintype.card_pos
      rw [h0, Nat.cast_zero, zero_pow hN.ne', inv_zero]
      positivity
    · have hg : (1 : ℝ) ≤ X.B.g := by exact_mod_cast hpos
      exact (inv_le_one_of_one_le₀ (one_le_pow₀ hg)).trans (one_le_pow₀ hg)
  change HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ≤
    (X.B.g : ℝ) ^ D.R.f * NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ * NDPt D.host.rdE γ
  unfold HPt
  have hGD : 0 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ * NDPt D.host.rdE γ := by
    have := mul_le_mul hG hD zero_le_one (zero_le_one.trans hG)
    linarith
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right key hGD

theorem g_ge_three {Cg cb Cw cT CT C0 C' Cl : ℝ} {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X}
    {u u' : D.what₂.Word} (hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u') :
    ∀ i, 3 ≤ D.host.g i := by
  obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
  unfold Formalism.MainNotions.S.StandingHypotheses at hH
  dsimp only at hH
  obtain ⟨-, -, h3, h4, -, -, -, -, -, -, h11, h12, h13, h14, h15, h16, -, -, h19, -, -, -, h23, -, h25⟩ := hH
  have hm2 := D.R.two_le_m
  have hk16 : (16 : ℝ) ≤ D.R.k := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    have : 16 ≤ D.R.k := by omega
    exact_mod_cast this
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb : 1 < large₂.sc.b := by
    unfold Formalism.BasicNotions.Scale.b
    have := Real.add_one_lt_exp (ne_of_gt hL); linarith
  have hkb : (3 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (16 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    exact le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) this 8)
  intro i
  fin_cases i
  · exact_mod_cast hkb.trans h12
  · exact_mod_cast hkb.trans h14

end Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqSteps

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.NGAnalytic.MassDataLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inst

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev anY : AnIn :=
  anOf (Y.tO u u') (Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1) (Formalism.L2.SG.RealObj.degX X)
    ((locOf X u u' ψ).volZZ / (((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP) *
      ((locOf X u u' ψ).volPP * (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)))
    (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D) (Formalism.L2.SG.RealObj.IntOO X u u' 1) sd C Th D.R.rS
    (Fintype.card (InfinitePlace X.B.I.F))
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq),
      KtopVOf X u u' Y.M Y.δ (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq)⟩

def FrameVolAt : Prop :=
  (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).unitLevelVolume / (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).volZZ =
    (2 * D.host.v) ^ (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) *
      (X.B.g : ℝ) ^ (D.R.f * (D.R.rS + 1) * (2 * D.R.rS + 3))

theorem kapN_pos (hg : 0 < (X.B.g : ℝ)) : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  have hgS : 0 < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
    unfold Formalism.MainNotions.S.Lat.gS
    first
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos D.host.g_prime.1.pos D.host.g_prime.2.pos)
      | exact Nat.cast_pos.2 (Nat.mul_pos (D.host.g_prime 0).one_lt.le (D.host.g_prime 1).one_lt.le)
  positivity

theorem massDataValid_bk_of {large₂ : SizeData₂ D} {Cg cb Cw cT CT C0 C' Cl : ℝ} (hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u')
    (hrd : 0 < 2 * D.host.v) (hg : 0 < (X.B.g : ℝ)) (hT : MassDataTie X hb X0 ψ)
    (hLS : InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hMs : InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hCol : InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hInd : InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hVol : InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hKpp : KppVolAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hTy : InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq)
    (hPC : ProdConv X u u' ψ) (hPr : PrimX X u) (hPr' : PrimX X u') (hKap : KapX X u u')
    (hNu : Formalism.L2.SG.RealObj.InNuX X u u' 1) (hInf : Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Pos)
    (hFV : FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) :
    ∃ Irat Ire : ℝ, MassDataAdmissible X Y u u' (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire := by
  obtain ⟨hM, hψ, hStd, hMC, hLC, -, hdet⟩ := hT
  have hH : HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hM, hc.2.2.1, Y.FN_fund u, Y.FN_fund u'⟩
  have hk := kapN_pos X hg
  have hDst : (bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Dstar = DstC X :=
    Formalism.L2.SG.IntegralApproximation.MassDataDstarX_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq
      (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hH hKpp
  set B := bk X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq with hB
  have hCoo : 0 ≤ Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
    unfold Formalism.L2.SG.RealObj.DisintegrationConstant
    split_ifs with h
    · exact h.choose_spec.1.le
    · exact le_rfl
  have hdeg : 0 < B.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hPos
    exact h
  have hNI : PN.NormInputs B := by
    refine ⟨hPos, rfl, ?_, ?_, ?_, hLS hH, hMs hH, hCol hH, ?_, ?_, hInd hH⟩
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 =
        Formalism.L2.SG.MassDataConc.kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 *
          (Formalism.L2.SG.RealObj.IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)
      unfold Formalism.L2.SG.RealObj.IntOO Formalism.L2.SG.RealObj.IntC
      rw [hNu, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCoo]
      field_simp
    · show Formalism.L2.SG.RealObj.IntOO X u u' 1 ≤ 1 / Formalism.L2.SG.RealObj.degX X
      have hd : 0 < Formalism.L2.SG.RealObj.degX X := hdeg
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hInf.2.2
    · exact inVolumes_of_compat X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ)
        (anY X Y u u' ψ sd C Th vR Q i0 i0' νq) hVol hH ⟨ψ, hψ, hStd, hMC⟩ hdet
    · exact inOrdinary_bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq hPC
    · exact hTy hH hPC (locTieX_of X ψ u (hLC u) hPr) (locTieX_of X ψ u' (hLC u') hPr')
        (typFacts_of X u u' (Formalism.L2.SG.Pf.gSplitX_holds X) (tCongX X u u') hKap)
  have hLam : 0 < PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
      (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) := by
    unfold PN.abelian₂
    exact mul_pos (pow_pos hrd _) (Real.rpow_pos_of_pos hrd _)
  refine ⟨(B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)),
    (B.c0 * B.c0')⁻¹ * B.IntC / 2 ^ (D.R.f * (D.R.rS + 1)) /
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f *
        (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3)), ?_, ?_, hNI, ?_⟩
  · exact Formalism.L2.SG.IntegralApproximation.Gam1TieC_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ sd C Th vR Q Y.M Y.δ i0 i0' νq Y
  · show B.d * B.d' / B.Dstar = duC X Y u * duC X Y u' / DstC X
    rw [hDst]
    rfl
  · have hL1 : PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f ≠ 0 := by
      unfold PN.abelian₂; exact (pow_pos hrd _).ne'
    have hL2 : (2 * D.host.v) ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos hrd _).ne'
    refine ⟨hrd, hg, hFV, ?_, ?_⟩
    · field_simp
    · field_simp

end Inst

section Closed

def pairSys0 {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ :=
  ⟨Empty, Empty.elim, Empty.elim, fun p => p.elim, fun p => p.elim, fun _ => False⟩

def idx0 (D : D7) : Fin D.R.k := ⟨0, by have := D.R.m_add_three_le_k; omega⟩

abbrev bk0 {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    S3.MassData (TypX X) :=
  bk X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

abbrev canonicalAnalyticData {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : AnIn :=
  anY X Y u u' ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u))
    (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)

def OnTied (P : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I → Full X → D.what₂.Word → D.what₂.Word →
    (Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) → AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ → Prop) : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → P D X hb Y u u' X0 ψ

end Closed

end Formalism.L2.SG.NGAnalytic.MassDataLemmas
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section P

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def CtxP : Prop :=
  (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ IsRowReps D F0 what₂ ∧ Lat.PrimeHyp D u (Tu D u')

def FrGlobP : Prop := CtxP u u' F0 what₂ → FrGlob Zd u u' F0 what₂

def TauOneReduction : Prop := CtxP u u' F0 what₂ → Tau1 Zd u u' F0 what₂

def ExistP : Prop := CtxP u u' F0 what₂ → Exist Zd.M Zd.δ u u'

def SumFrP : Prop := CtxP u u' F0 what₂ → SumFr Zd.M Zd.δ u u' F0 what₂

variable {u u' F0 what₂}

theorem normRepExists_ctx (h : CtxP u u' F0 what₂) : PairVal.NormRepExists D u u' F0 what₂ := normRepExists_of (NormRepX.norm_representative_holds D u u' h.2.2) (Formalism.L2.SG.Closed.TermFun_holds D u u') h.2.1

theorem frCount_ctx (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : FrCount Zd.M Zd.δ u u' F0 what₂ := pcount_frCount Zd (normRepExists_ctx h) h.2.1 (hG h) hI (inOrbZ_holds Zd u u') (hτ h) hT

theorem partnerCount_ctx {θ0 : ∀ p, Option ((Zd.M p).Cls D.R.rS)}
    (hU : LocUnram Zd.M Zd.δ u u' θ0) (hR : ThRestricted Zd.M Zd.δ u u' F0 what₂ θ0)
    (hE : ExistP Zd u u' F0 what₂) (hS : SumFrP Zd u u' F0 what₂)
    (hG : FrGlobP Zd u u' F0 what₂) (hI : IntGenP Zd) (hτ : TauOneReduction Zd u u' F0 what₂) (hT : PartnerIsomorphismCount Zd)
    (h : CtxP u u' F0 what₂) : PartnerCount Zd.M Zd.δ u u' F0 what₂ := partnerCount_of hU hR h.2.1 (normRepExists_ctx h) eligRel_holds
    (restr_of Zd.3 h.2.1 (normRepExists_ctx h) eligRel_holds) (hE h) (hS h) (frCount_ctx Zd hG hI hτ hT h)

end P

end Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem partnerCount_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hP : Lat.PrimeHyp D u (Tu D u')) {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LsDatumB.LocUnram M δ u u' θ0) (hR : LsDatumB.ThRestricted M δ u u' F0 what₂ θ0)
    (hE : PCount.ExistP ⟨δ, M, hA⟩ u u' F0 what₂) (hS : PCount.SumFrP ⟨δ, M, hA⟩ u u' F0 what₂)
    (hG : PCount.FrGlobP ⟨δ, M, hA⟩ u u' F0 what₂) (hI : PCount.IntGenP ⟨δ, M, hA⟩)
    (hτ : PCount.TauOneReduction ⟨δ, M, hA⟩ u u' F0 what₂) (hT : PCount.PartnerIsomorphismCount ⟨δ, M, hA⟩) :
    LsDatumB.PartnerCount M δ u u' F0 what₂ := PCount.partnerCount_ctx ⟨δ, M, hA⟩ hU hR hE hS hG hI hτ hT ⟨hc, hrows, hP⟩

end Formalism.L2.SG.Pf
end
end
