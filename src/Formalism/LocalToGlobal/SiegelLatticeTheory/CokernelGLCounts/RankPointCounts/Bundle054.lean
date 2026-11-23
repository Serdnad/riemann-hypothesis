module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.GmapInvOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle023
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle037
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfFrameBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageEveryPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsAdaptedColumn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm

theorem liftAtSomeC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) : LiftAtSomeC X Y u u' κ := by
  intro R ρ s hrel
  have hG : s.1.toTerm.G ≠ 0 := by
    intro h0
    apply s.2.1
    show Formalism.L2.SG.TermOp.Gt s.1 = 0
    unfold Formalism.L2.SG.TermOp.Gt
    exact if_pos h0
  exact Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' s.1.toTerm hG hrel

theorem atPtRelevantC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) :
    AtPtRelevantC X Y u u' := fun t w h =>
  Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' (X.Fu u) (Y.what₂ u) t w h

theorem liftIotaC_of (hD : Formalism.L2.SG.Pf.IotaDictC) {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.RowForm.ScalT.LiftIotaC X Y u u' := by
  intro s₁ s₂ hG₁ hG₂ hg₁ hg₂ hrow
  have hlam : s₁.lam = s₂.lam := congrArg (fun r => r.1.1) hrow
  have hlam' : s₁.lam' = s₂.lam' := congrArg (fun r => r.2.1.1) hrow
  have hio : Formalism.L2.SG.TermOp.iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = Formalism.L2.SG.TermOp.iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ :=
    congrArg (fun r => r.2.2) hrow
  exact (hD D X Y u u' s₁ s₂ hG₁ hG₂ hg₁ hg₂ hlam hlam').mp hio

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def DecompPhaseC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ ∧
        Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                  ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) *
          (X.psiInfU u g * conj (X.psiInfU u' g')) =
          Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem decompPhaseC_of (h3 : LiftDecompC X Y u u' κ) (h6 : PhaseTieC X Y u u' κ) : DecompPhaseC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := h3 R ρ s hrel
  exact ⟨hpt, g, hg, g', hg', hdec, h6 R ρ s hrel g hg g' hg' hdec⟩

theorem normalFormC_of' (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) :
    NormalFormC X Y u u' vR i0 i0' νq κ := by
  intro R ρ s hrel
  obtain ⟨hpt, g, hg, g', hg', hdec, hph⟩ := h3 R ρ s hrel
  have hDF : ∃ p : X.B.I.Ginf × X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) p.1 p.2 := by
    obtain ⟨h, h', hh⟩ := h4 one_pos _ hpt (h4' R ρ s hrel)
    exact ⟨(h, h'), hh⟩
  have hcS : hDF.choose.1 ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hDF.choose_spec.1
  have hcS' : hDF.choose.2 ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hDF.choose_spec.2.1
  have hcSi : hDF.choose.1⁻¹ ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hcS
  refine ⟨(Formalism.L2.SG.RealObj.InfCut.piIso X u hDF.choose.1 hcS).trans (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg),
    (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').trans (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg'), ?_⟩
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcT : Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
      Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * (vR s.1.toTerm : ℂ) :=
    Formalism.L2.SG.PairVal.cTerm_of_atPt vR _ hat (fun w' hw' => h2 _ w' _ hw' hat)
  have hV : Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) =
      (X.piU u hDF.choose.1⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
          (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
        (X.piU u' hDF.choose.2)) := by
    unfold Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative Formalism.L2.SG.RealObj.unscaledFrameConjugatedOperator
    rw [if_pos hpt, dite_eq_left hDF]
  have hO : Formalism.L2.SG.TermOp.OOt s.1 =
      (((vR s.1.toTerm : ℝ) : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g'))) •
        (((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
          ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
            Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
              (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
            ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))) := by
    rw [h5 R ρ s hrel g hg g' hg' hdec, ← smul_smul]
    congr 1
    rw [hdec]
    exact ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' _ _ _ _
      (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x)
  have e1 : ∀ z, X.piU u hDF.choose.1 (X.piU u hDF.choose.1⁻¹ z) = z := fun z => by
    rw [← ContinuousLinearMap.mul_apply, ← (X.piU_rep u).2.1 _ hcS _ hcSi, mul_inv_cancel, (X.piU_rep u).1,
      ContinuousLinearMap.one_apply]
  have e2 : ∀ y, X.piU u' hDF.choose.2 ((Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').symm y) = y :=
    fun y => (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').apply_symm_apply y
  unfold chiOO frameVal
  rw [hO, hcT, hV, smul_smul, ← hph]
  have hsc : ∀ a c r : ℂ, a * (r * c) = a * c * r := fun a c r => by ring
  rw [hsc]
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, Formalism.L2.SG.RealObj.InfCut.piIso_apply, e1, e2]

end Formalism.L2.SG.Pf.RowForm
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem equiv_of_corr {X L S : Type*} (P : X → Prop) (cl : X → S) (G : Set L) (R : X → L → Prop)
    (ha : ∀ x, P x → ∃ y ∈ G, R x y) (hb : ∀ y ∈ G, ∃ x, P x ∧ R x y)
    (hc : ∀ x x' y y', P x → P x' → R x y → R x' y' → (y = y' ↔ cl x = cl x')) :
    Nonempty ({O | ∃ x, P x ∧ O = cl x} ≃ G) := by
  refine ⟨{ toFun := fun O => ⟨(ha _ O.2.choose_spec.1).choose, (ha _ O.2.choose_spec.1).choose_spec.1⟩
            invFun := fun y => ⟨cl (hb y.1 y.2).choose, _, (hb y.1 y.2).choose_spec.1, rfl⟩
            left_inv := ?_
            right_inv := ?_ }⟩
  · rintro ⟨O, hO⟩
    apply Subtype.ext
    have h1 := (ha _ hO.choose_spec.1).choose_spec
    have h2 := (hb _ h1.1).choose_spec
    have h3 := (hc _ _ _ _ hO.choose_spec.1 h2.1 h1.2 h2.2).1 rfl
    show cl (hb _ h1.1).choose = O
    exact (hO.choose_spec.2.trans h3).symm
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    have h2 := (hb y hy).choose_spec
    have hm : ∃ x, P x ∧ cl (hb y hy).choose = cl x := ⟨_, h2.1, rfl⟩
    have h4 := (ha _ hm.choose_spec.1).choose_spec
    show (ha _ hm.choose_spec.1).choose = y
    exact (hc _ _ _ _ hm.choose_spec.1 h2.1 h4.2 h2.2).2 hm.choose_spec.2.symm

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def unipotentFrameFixers {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {n | n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag (lf D F0) (j + 1), n x - x ∈ Xflag (lf D F0) j) ∧
    (∀ x ∈ orth (VS D) (Xsp (lf D F0)), n x - x ∈ Xsp (lf D F0)) ∧ (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z}

def Moves {T' : D.host.E} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  (∀ a, n (F'.fl.e a) = F''.fl.e a) ∧ n F'.fl.z = F''.fl.z

def IsPartner (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧
    ∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
      Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls F'

def cls (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :=
  {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧ CntLocal.NilradicalFlagMoved F0 γ.lam F' F''}

theorem frPart_eq (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) :
    frPart γ Z = {O | ∃ F', IsPartner γ Z F' ∧ O = cls γ Z F'} := by
  ext O
  constructor
  · rintro ⟨F', h1, h2, h3⟩
    exact ⟨F', ⟨h1, h2⟩, h3⟩
  · rintro ⟨F', ⟨h1, h2⟩, h3⟩
    exact ⟨F', h1, h2, h3⟩

def RelN (γ : TermDef.Term D u u' F0 what₂) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  ∃ n ∈ unipotentFrameFixers F0, Moves n F'₂ F' ∧ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

def Ctx (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ w : Point D.host.E (D.R.rS + 1), EligAt γ w ∧ ∃ w' : Point D.host.E (D.R.rS + 1),
    Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 ∧ kind w' = kind w ∧ AtMat w' Z

def StarHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ZhatL (lf D F0) F'₂ = Z ∧
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) ∧
    ∀ p, φ p = LinearEquiv.refl _ _

def Coherent (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ₀ ∧
    {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite

variable (u u' F0 what₂)

def StarExists2 : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' ∧ Coherent Zd γ F'₂ φ φ'

def FwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F', IsPartner γ Z F' → ∃ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', RelN γ F'₂ F' Λ₂

def BwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∃ F', IsPartner γ Z F' ∧ RelN γ F'₂ F' Λ₂

def UniqC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F' F'' Λ₂ Λ₃, IsPartner γ Z F' → IsPartner γ Z F'' → RelN γ F'₂ F' Λ₂ → RelN γ F'₂ F'' Λ₃ →
        (Λ₂ = Λ₃ ↔ cls γ Z F' = cls γ Z F'')

variable {u u' F0 what₂}

theorem fStarC_of_route2 (h1 : StarExists2 Zd u u' F0 what₂) (h2 : FwdC Zd u u' F0 what₂) (h3 : BwdC Zd u u' F0 what₂)
    (h4 : UniqC Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ
  have hC : Ctx γ Z := ⟨w, hγ, w', hG', hk, hZ⟩
  obtain ⟨F'₂, φ, φ', hS, hCoh⟩ := h1 γ Z hC
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hCoh
  letI := hΛ₀
  refine ⟨F'₂, φ, φ', hS.1, hS.2.2, hS.2.1, ⟨Λ₀, inferInstance, hfin⟩, ?_⟩
  rw [frPart_eq]
  exact equiv_of_corr (IsPartner γ Z) (cls γ Z) (GlobSet Zd γ F'₂ φ φ') (RelN γ F'₂)
    (h2 γ Z hC F'₂ φ φ' hS) (h3 γ Z hC F'₂ φ φ' hS) (h4 γ Z hC F'₂ φ φ' hS)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting

noncomputable section

namespace Formalism.L2.SG.Pf.PhaseLiftCell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem realLink' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.RealObj.ZhatO (Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 v) =
      (ZhatOM (ZhatL (lf D (X.Fu u)) s.frame)).map (fun x => X.B.I.φ v (X.ιE.symm x)) := by
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfam : ∀ (w : D.what₂.Word) (a : Fin (D.R.rS + 1)),
      Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) a =
        rv X.B.I v (X.crd ((X.Fu w).fvec a)) := by
    intro w a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.flagZVector w, HidaSetting.zR]
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.Fu_e w, HidaSetting.eR]
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ZhatOM, Formalism.L2.SG.RealObj.ZX, Formalism.L2.SG.RealObj.Zhat,
    Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Matrix.map_apply, Complex.ofReal_one, one_pow, inv_one,
    one_smul]
  rw [hfam u a, hfam u' b]
  have h1 : Formalism.MainNotions.S.uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
      X.B.I.P v := hM1 v
  rw [h1, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, Formalism.L2.SG.PoincareInHH.Cut.hJ_crd]
  have h2 : ZhatL (lf D (X.Fu u)) s.frame a b = (VS D).hT ((X.Fu u).fvec a) (s.lin ((X.Fu u').fvec b)) := by
    rw [← Formalism.L2.SG.Pf.Act.frame_mapLF hiso (X.Fu u') b]
    rfl
  rw [h2, map_mul, map_mul]
  simp only [map_pow, map_neg, map_one]
  rw [X.φ_eq, RingEquiv.apply_symm_apply]
  rfl

theorem liftCell_of_atSome {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) : Formalism.L2.SG.Pf.FinitePhase.LiftCellC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) :=
    Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcell := ((Formalism.L2.SG.TermDef.atPt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) (Formalism.L2.SG.Pf.cell_function_holds _ _ _)
    ⟨s.1.frame, s.1.rep.2.2.2.2⟩ _).1 hat).2
  obtain ⟨L, U, hL, hU, hLU⟩ := hcell
  refine ⟨L, U, hL, hU, hLU, fun v => ?_⟩
  rw [realLink' X u u' s.1 v]
  exact congrArg (fun Z => Z.map (fun x => X.B.I.φ v (X.ιE.symm x))) hLU

theorem phaseAgreement_of_lift {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) (hF : Formalism.L2.SG.Pf.FinitePhase.FinPhaseC X Y u u' κ) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.FinitePhase.phaseTieC_of X Y u u' κ (liftCell_of_atSome X Y u u' κ h1) hF

end Formalism.L2.SG.Pf.PhaseLiftCell
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_pi_of_unique {ι : Type*} {α : ι → Type*} (T : Finset ι) (h : ∀ i ∉ T, Nonempty (Unique (α i))) :
    Nat.card (∀ i, α i) = ∏ᶠ i, Nat.card (α i) := by
  haveI : ∀ i : {i // i ∉ T}, Unique (α i) := fun i => (h i.1 i.2).some
  rw [Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ T) α), Nat.card_prod,
    Nat.card_unique (α := ∀ i : {i // i ∉ T}, α i), mul_one, Nat.card_pi]
  rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
  · exact (Finset.prod_coe_sort T (fun i => Nat.card (α i)))
  · intro i hi
    by_contra hT
    haveI := (h i hT).some
    exact hi Nat.card_unique

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def LocFullC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z →
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) →
    ∀ p, ∀ M ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p),
      ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ' ∧ M = lattice₂ D Zd.M p Λ'

variable {Zd u u' F0 what₂}

theorem patchC_of (hP : LatPatch) (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT hC
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hC
  have hfull := hL γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT
  set S : ∀ p : PlF D, Set (Submodule (Zd.M p).L.O (Vp D p)) :=
    fun p => locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) with hS
  have hex : ∀ f : ∀ p, S p, ∃! Λ : Submodule (𝓞 D.host.E) (VS D).V,
      Submodule.IsFullLattice D.host.E Λ ∧ ∀ p, lattice₂ D Zd.M p Λ = (f p).1 := fun f =>
    hP D Zd Λ₀ hΛ₀ (fun p => (f p).1) (fun p => hfull p _ (f p).2)
      (hfin.subset fun p hp hS' => hp (Set.mem_singleton_iff.1 ((Set.ext_iff.1 hS' (f p).1).1 (f p).2)))
  let e : GlobSet Zd γ F'₂ φ φ' ≃ ∀ p, S p :=
    { toFun := fun Λ p => ⟨lattice₂ D Zd.M p Λ.1, Λ.2.2 p⟩
      invFun := fun f => ⟨(hex f).choose, (hex f).choose_spec.1.1, fun p => by
        rw [(hex f).choose_spec.1.2 p]; exact (f p).2⟩
      left_inv := fun Λ => by
        apply Subtype.ext
        exact (hex _).unique (hex _).choose_spec.1 ⟨Λ.2.1, fun p => rfl⟩
      right_inv := fun f => by
        funext p
        exact Subtype.ext ((hex f).choose_spec.1.2 p) }
  rw [Nat.card_congr e]
  obtain ⟨T, hTs⟩ := hfin.exists_finset
  refine card_pi_of_unique (α := fun p => S p) T (fun p hp => ?_)
  have hsing : S p = {lattice₂ D Zd.M p Λ₀} := by
    by_contra hne
    exact hp ((hTs p).2 hne)
  rw [hsing]
  exact ⟨Set.uniqueSingleton _⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem stK_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StK X p :=
  MassDataIdxSteps.stK_holds X p

theorem stRed_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StRed X p :=
  MassDataIdxSteps.stRed_of_embP X p (MassDataIdxSteps.embP_holds X p)

theorem stImA_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) :
    MassDataIdxSteps.StImA X hb p :=
  MassDataIdxSteps.stImA_of X hb p (MassDataIdxSteps.reduction_image_every_place X hb p)

theorem stImB_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    MassDataIdxSteps.StImB X u p :=
  MassDataIdxSteps.stImB_of_adaptQ X u p (MassDataIdxSteps.stAdaptQ_holds X hb u p)

theorem inIndicesAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  local_indices_at_instance

end Formalism.L2.SG.Pf.MassDataX
end
