module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle059
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle053
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle043
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle056
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneDir2

variable {D : D7} (Zd : LocDat D)

theorem nm_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1
  rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
  · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
    by_cases hb : Fin.last D.R.rS = b
    · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
    · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
      rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
  · intro c _ hc
    have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
    rw [(hNU _ _).1 hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem one_dir {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hRL : IsRowLat D F0 Λ)
    (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hP₁ : Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F₁) (hA₁ : AdmWit Λ (gS D) (lf D F0) F₁ 1)
    (hA₂ : AdmWit Λ (gS D) (lf D F0) F₂ 1) (hdc : Formalism.L2.SG.TermDef.DCRel Λ (lf D F0) F₁ F₂) (p : PlF D) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Zd.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Zd.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₂) * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatL (lf D F0) F₁) * Formalism.L2.SG.LsDatumB.sgnP p) *
          ρ := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hdc
  have hEn := stepExp D Λ (lf D F0) n hn
  have hEm := stepExp D Λ F₁ m hm
  have hrel := stepGram D (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hEn.2 hEm.2 hfr
  have hXS : XLam Λ (lf D F0) = XS D (lf D F0).fl := hRL.2.2
  have hz : (lf D F0).fl.z ∈ Λ := hRL.2.1.2.2.1.1
  have hNb := entry_mem D Λ (lf D F0) n hn hXS hz
  have hMb := entry_mem D Λ F₁ m hm hP₁.2.2.2 hP₁.1.1
  have hNU : ∀ a b, b < a → fmat D (lf D F0) n a b = 0 := fun a b h => (hEn.1 a b).1 h
  have hNd : ∀ a, fmat D (lf D F0) n a a = 1 := fun a => (hEn.1 a a).2 rfl
  have hMU : ∀ a b, b < a → fmat D F₁ m a b = 0 := fun a b h => (hEm.1 a b).1 h
  have hMd : ∀ a, fmat D F₁ m a a = 1 := fun a => (hEm.1 a a).2 rfl
  cases hs : (Zd.M p).split with
  | none => exact modeL Zd p hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel
  | some g =>
    refine modeG Zd p g hs u u' _ _ _ _ hNU hNd hMU hMd hNb hMb hrel ?_
    obtain ⟨sg, hsg, -, hq⟩ := typed_split Zd p hs
    have hgP := gS_mem_of_split p hsg
    have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
      have : gS D ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact_mod_cast this
    have hφ := fun a => Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
      (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 Λ hRL.2.1.1.fg hRL.2.2 hRL.2.1.2.2.2 hgP a
    have hκ := (Formalism.L2.SG.Pf.BBTie.bt_kappa Zd p sg hsg).1
    have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := by
      intro h
      exact sg.q_irr.ne_zero (Subtype.ext h)
    have hOO : (Zd.M p).L.O = (D.s.atP p).O := (Zd.agree p).2.2.2.1
    rw [locU_mul, locU_sub_one]
    intro i j
    rw [locU_apply]
    obtain ⟨w, hwO, hw⟩ := (hφ i).2
    have hinv : Ring.inverse (frFac Zd.δ p i) = w := by
      calc Ring.inverse (frFac Zd.δ p i) = (w * frFac Zd.δ p i) * Ring.inverse (frFac Zd.δ p i) := by
            rw [hw, one_mul]
        _ = w := by rw [mul_assoc, frFac_mul_inv, mul_one]
    induction i using Fin.lastCases with
    | last =>
      rw [nm_last Λ (lf D F0) F₁ n m hn hm j, map_zero, mul_zero, zero_mul]
      exact ⟨0, Subring.zero_mem _, by rw [mul_zero]⟩
    | cast d =>
      set x := (fmat D (lf D F0) n * fmat D F₁ m - 1) d.castSucc j with hxdef
      have hint : (D.s.atP p).ιE (x / (gS D : D.host.E)) ∈ (Zd.M p).L.O := by
        rw [hOO]
        exact iota_mem_O p _ (fun P hP => cong_at D Λ (lf D F0) F₁ F₂ n m hn hm hfr hRL.2.1.2.2.2 hP₁.2.2.1
          hA₁ hA₂ hP₁.1.1 P (hgP P hP) hg d j)
      have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) *
          ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
            (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) := by
        rw [← mul_assoc, ← mul_assoc, ← map_mul (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), mul_inv_cancel₀ hq0,
          map_one, one_mul, ← map_mul, mul_div_cancel₀ x hg]
      refine ⟨w * ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
          (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) * (D.s.atP p).ιE (x / (gS D : D.host.E))) * frFac Zd.δ p j,
        Subring.mul_mem _ (Subring.mul_mem _ hwO (Subring.mul_mem _ hκ hint)) (hφ j).1, ?_⟩
      rw [hinv, hx, hq]
      ring

end OneDir2

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace CohCut

def t2 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ : Submodule (Zd.M p).L.O (Vp D p)) : Loc.Term (Vp D p) (Zd.M p) D.R.rS :=
  ⟨Λ, (tLoc Zd p γ).f, locF' Zd p F'₂, (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def vP (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → Vp D p :=
  (locH Zd p).MMfam (t2 Zd p γ F'₂ ⊥)

end CohCut

open CohCut

def CohHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  Ctx γ Z ∧ ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
    ∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) (φ' p)

variable (u u' F0 what₂)

def CohGen : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (locH Zd p).IsGeneric (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

def CohGood : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)}.Finite

variable {u u' F0 what₂}

theorem locSet_eq_single {p : PlF D} {γ : TermDef.Term D u u' F0 what₂}
    {F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)}
    {φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)}
    (hmem : lattice₂ D Zd.M p γ.lam ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ')
    (hN : Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂)) :
    locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ' = {lattice₂ D Zd.M p γ.lam} := by
  ext Λ₂
  rw [Set.mem_singleton_iff]
  constructor
  · intro h2
    have hL : (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f = (locH Zd p).Lset Λ₂ (tLoc Zd p γ).f := by
      have h := h2.2.1
      exact (Set.image_id _).symm.trans h
    have hX := Formalism.MainNotions.S.Loc.HermSp.CohU.X_le_MMfam (H := locH Zd p) (t2 Zd p γ F'₂ ⊥)
    exact (Formalism.MainNotions.S.Loc.HermSp.CohU.lat_eq_of_Lset hN hX hmem.1.1.1 h2.1.1.1 hmem.1.2.1 h2.1.2.1 hL).symm
  · intro h
    rw [h]
    exact hmem

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def OmV {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (v : S.V) : Prop :=
  v ∈ Submodule.span E (Set.range F'.fvec) ∧ ∀ a, S.hT (F.fvec a) v = if a = Fin.last r then 1 else 0

theorem fvec_cs {T : E} (F : FlagG S r T) (i : Fin r) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

theorem fvec_last {T : E} (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem hT_comb {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E) (a : Fin (r + 1)) :
    S.hT (F.fvec a) (∑ b, c b • F'.fvec b) = (Zhat F F' *ᵥ c) a := by

  rw [map_sum]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

theorem eq_zero_of_orth {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0)
    {d : S.V} (hd : d ∈ Submodule.span E (Set.range F'.fvec)) (h : ∀ a, S.hT (F.fvec a) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hd
  have hc : Zhat F F' *ᵥ c = 0 := funext fun a => by rw [← hT_comb]; exact h a
  rw [Matrix.eq_zero_of_mulVec_eq_zero hdet hc]
  simp

theorem exists_om {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) :
    ∃ v, OmV F F' v := by
  set c : Fin (r + 1) → E := (Zhat F F')⁻¹ *ᵥ Pi.single (Fin.last r) 1 with hc
  refine ⟨∑ b, c b • F'.fvec b, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, fun a => ?_⟩
  rw [hT_comb, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  by_cases ha : a = Fin.last r
  · subst ha; simp
  · simp [ha]

theorem om_unique {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {v w : S.V}
    (hv : OmV F F' v) (hw : OmV F F' w) : v = w := by
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hv.1 hw.1) fun a => by
    rw [map_sub, hv.2, hw.2, sub_self]
  exact sub_eq_zero.1 this

theorem comb_eq {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {Ω : S.V}
    (hΩ : OmV F F' Ω) (c : Fin (r + 1) → E) (hc : ∀ i : Fin r, S.hT (F.e i) (∑ b, c b • F'.fvec b) = 0) :
    ∑ b, c b • F'.fvec b = S.hT F.z (∑ b, c b • F'.fvec b) • Ω := by
  set v := ∑ b, c b • F'.fvec b with hv
  have hvs : v ∈ Submodule.span E (Set.range F'.fvec) := (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hvs (Submodule.smul_mem _ (S.hT F.z v) hΩ.1))
    fun a => by
      rw [map_sub, map_smul, hΩ.2, smul_eq_mul]
      refine Fin.lastCases ?_ (fun i => ?_) a
      · rw [fvec_last]; simp
      · rw [fvec_cs, hc i]; simp [Fin.castSucc_ne_last]
  exact sub_eq_zero.1 this

end OmP

open OmP

section Cls

variable {D : Formalism.BasicNotions.D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem omCls_of_om {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS T')
    (hZ : ZhatL (lf D F0) F'₂ = ZhatL (lf D F0) F') (hdet : (ZhatL (lf D F0) F'₂).det ≠ 0) {Ω₂ Ω' : (VS D).V}
    (h₂ : OmV F0 F'₂.fl Ω₂) (h' : OmV F0 F'.fl Ω') (hX : Ω' - Ω₂ ∈ Xsp (lf D F0)) : OmCls F0 F'₂ F' := by
  intro c hc
  have hZ' : Zhat F0 F'₂.fl = Zhat F0 F'.fl := hZ
  have hdet₂ : (Zhat F0 F'₂.fl).det ≠ 0 := hdet
  have hdet' : (Zhat F0 F'.fl).det ≠ 0 := by rw [← hZ']; exact hdet
  have hc₂ : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'₂.fl.fvec b) = 0 := hc
  have hc' : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'.fl.fvec b) = 0 := by
    intro i
    rw [← fvec_cs, hT_comb, ← hZ', ← hT_comb, fvec_cs]
    exact hc₂ i
  have hμ : (VS D).hT F0.z (∑ b, c b • F'.fl.fvec b) = (VS D).hT F0.z (∑ b, c b • F'₂.fl.fvec b) := by
    rw [← fvec_last, hT_comb, hT_comb, hZ']
  have e₂ := comb_eq F0 F'₂.fl hdet₂ h₂ c hc₂
  have e' := comb_eq F0 F'.fl hdet' h' c hc'
  have hs : ∑ b, c b • (frame F' b - frame F'₂ b) =
      ∑ b, c b • F'.fl.fvec b - ∑ b, c b • F'₂.fl.fvec b := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => smul_sub _ _ _
  rw [hs, e', e₂, hμ, ← smul_sub]
  exact Submodule.smul_mem _ _ hX

end Cls

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def OmDet : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' →
        (ZhatL (lf D F0) (repF γ)).det ≠ 0 ∧ Matrix.det Z ≠ 0

def OmLoc : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 → ∀ Ω₂ Ωγ : (VS D).V, OmV F0 F'₂.fl Ω₂ → OmV F0 (repF γ).fl Ωγ →
        Ω₂ - Ωγ ∈ Xsp (lf D F0)

def OmRep : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 →
    ∀ F', IsPartner γ Z F' → ∀ Ω' Ωγ : (VS D).V, OmV F0 F'.fl Ω' → OmV F0 (repF γ).fl Ωγ →
      Ω' - Ωγ ∈ Xsp (lf D F0)

variable {u u' F0 what₂}

theorem omPart_of (h0 : OmDet Zd u u' F0 what₂) (h1 : OmLoc Zd u u' F0 what₂) (h2 : OmRep u u' F0 what₂) :
    OmPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'₂ φ φ' hS F' hP
  obtain ⟨hdγ, hdZ⟩ := h0 hrows γ Z hC F'₂ φ φ' hS F' hP
  have hZ₂ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hZ' : ZhatL (lf D F0) F' = Z := hP.1.2.2.2.2
  have hd₂ : (ZhatL (lf D F0) F'₂).det ≠ 0 := by rw [hZ₂]; exact hdZ
  have hd' : (ZhatL (lf D F0) F').det ≠ 0 := by rw [hZ']; exact hdZ
  obtain ⟨Ωγ, hγ⟩ := exists_om F0 (repF γ).fl hdγ
  obtain ⟨Ω₂, h₂⟩ := exists_om F0 F'₂.fl hd₂
  obtain ⟨Ω', h'⟩ := exists_om F0 F'.fl hd'
  have e1 := h1 hrows γ Z hC F'₂ φ φ' hS hdγ hdZ Ω₂ Ωγ h₂ hγ
  have e2 := h2 hrows γ Z hC hdγ hdZ F' hP Ω' Ωγ h' hγ
  refine omCls_of_om F0 F'₂ F' (hZ₂.trans hZ'.symm) hd₂ h₂ h' ?_
  have : Ω' - Ω₂ = (Ω' - Ωγ) - (Ω₂ - Ωγ) := by abel
  rw [this]
  exact Submodule.sub_mem _ e2 e1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.NGCut.PtPf
  Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqPoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepPointsG_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPointsG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u t hr
    show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, -, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := frame_mem _ hP.1.1 hP.2.2.2
  have hE := blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell
  rw [← hpt]
  exact hE

open Formalism.L2.SG.TermOp.Vanish in
theorem stepPointsG_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPointsG := by
  refine stepPointsG_of ?_ hAt
  intro D X Y u u'
  unfold Formalism.L2.SG.TermOp.KExpCut.OOVanish
  intro t ht
  exact ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht

end Formalism.L2.SG.Pf.MainEqPoints
end
end
