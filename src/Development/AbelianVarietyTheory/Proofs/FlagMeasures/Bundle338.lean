module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountIsometryPairsWithGivenFixedSpace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle328
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle332
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSublatticeLiftsModuloFixingUnipotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

theorem isUpperUnitriangularFinMatrix_mul_of_both {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem triMove_main : ∀ {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (f' : Fin (D.R.rS + 1) → Vp D p), MovesTo F0 F0' F F' ρ U U' → Ext p ρ g → Tri (D.s.atP p).Ep (scaled Z p (frame F')) f' → Tri (D.s.atP p).Ep (scaled Z p (frame F0)) (fun a => g (scaled Z p (frame F) a)) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F0')) (fun b => g (f' b)) := by
  intro D Z p T T' F0 F0' F F' ρ U U' g f' hM hE hf'
  obtain ⟨_, hU, hU', hρ, hρ'⟩ := hM
  have hs : ∀ (h : Fin (D.R.rS + 1) → (VS D).V) a, g (scaled Z p h a) = scaled Z p (fun b => ρ (h b)) a := by
    intro h a
    simp only [scaled, map_smul]
    rw [hE]
  have uniOf : ∀ W : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni W → Uni W :=
    fun W hW => ⟨fun a b hab => (hW a b).1 hab, fun a => (hW a a).2 rfl⟩
  obtain ⟨A1, hA1, -⟩ := tri_scaled D Z (frame F0) (fun b => ρ (frame F b)) U (uniOf U hU) (fun b => hρ b)
  obtain ⟨A2, hA2, -⟩ := tri_scaled D Z (frame F0') (fun b => ρ (frame F' b)) U' (uniOf U' hU') (fun b => hρ' b)
  refine ⟨⟨A1 p, (hA1 p).1, fun b => ?_⟩, ?_⟩
  · show g (scaled Z p (frame F) b) = _
    rw [hs]; exact (hA1 p).2 b
  · obtain ⟨A, hA, hc⟩ := hf'
    refine ⟨A2 p * A, isUpperUnitriangularFinMatrix_mul_of_both _ _ (hA2 p).1 hA, fun b => ?_⟩
    show g (f' b) = _

    rw [hc b, map_sum]
    have h2 : ∀ a, g (A a b • scaled Z p (frame F') a) =
        ∑ d, (A a b * A2 p d a) • scaled Z p (frame F0') d := by
      intro a
      rw [map_smul, hs, (hA2 p).2 a, Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]

end GlobalTheory.LocOver
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

theorem form_ext_left {D : D7} (Z : LocDat D) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (w w' : Vp D p)
    (h : ∀ x, (locH Z p).h (g (baseChange₂ D p x)) w' = (locH Z p).h (baseChange₂ D p x) w) (x : Vp D p) :
    (locH Z p).h (g x) w' = (locH Z p).h x w := by

  have hx : x ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by
    rw [span_baseChange_eq_top p]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    exact h z
  | zero =>
    rw [map_zero, (locH Z p).h_zero_left, (locH Z p).h_zero_left]
  | add y y' _ _ hy hy' =>
    rw [map_add (f := _), (locH Z p).h_add_left, (locH Z p).h_add_left, hy, hy']
  | smul a y _ hy =>
    rw [map_smul, (locH Z p).h_smul_left, (locH Z p).h_smul_left, hy]

theorem exists_ext_unitary : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), ρ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, GlobalTheory.LocOver.Ext p ρ g ∧ Formalism.MainNotions.S.LocNG.IsUnitary (locH Z p) g := by
  intro D Z p ρ hρ

  obtain ⟨g, hg⟩ := GlobalTheory.HL.RatExt.exists_equiv (D.s.atP p).ιE
    ((VS D).frame.equivFun.symm.trans (ρ.trans (VS D).frame.equivFun))
  have hext : GlobalTheory.LocOver.Ext p ρ g := by
    intro x
    have h1 := hg ((VS D).frame.equivFun x)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1
  have hρ' : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ

  have hA : ∀ a b, (locH Z p).h (g (baseChange₂ D p a)) (g (baseChange₂ D p b)) =
      (locH Z p).h (baseChange₂ D p a) (baseChange₂ D p b) := by
    intro a b
    rw [hext a, hext b]
    show LocFacts₂ Z.M p _ _ = LocFacts₂ Z.M p _ _
    rw [baseChangeAt_form Z.M p (Z.hcj p), baseChangeAt_form Z.M p (Z.hcj p)]
    exact congrArg _ (hρ' b a)

  have hB : ∀ b x, (locH Z p).h (g x) (g (baseChange₂ D p b)) = (locH Z p).h x (baseChange₂ D p b) :=
    fun b x => form_ext_left Z p g (baseChange₂ D p b) (g (baseChange₂ D p b)) (fun a => hA a b) x
  have hC : ∀ a y, (locH Z p).h (g (baseChange₂ D p a)) (g y) = (locH Z p).h (baseChange₂ D p a) y := by
    intro a y
    rw [(locH Z p).h_herm (g y) (g (baseChange₂ D p a)), (locH Z p).h_herm y (baseChange₂ D p a), hB]
  refine ⟨g, hext, ?_⟩
  intro x y
  exact form_ext_left Z p g y (g y) (fun a => hC a y) x

end GlobalTheory.LocOver
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
  Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie
open scoped Classical

namespace GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scale

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_scale (H : HermSp M V) (c d : E) (x y : V) :
    H.h (c • x) (d • y) = M.L.cj d * c * H.h x y := by
  rw [H.h_smul_left, H.h_herm (d • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]
  ring

theorem Dl_scale (H : HermSp M V) {r : ℕ} (s s' : Fin (r + 1) → E) (f f' : Fin (r + 1) → V) (l : ℕ)
    (hl : l ≤ r + 1) :
    H.Dl (fun a => s a • f a) (fun b => s' b • f' b) l =
      (∏ i : Fin l, M.L.cj (s (Fin.castLE hl i)) * s' (Fin.castLE hl i)) * H.Dl f f' l := by
  unfold HermSp.Dl
  rw [dif_pos hl, dif_pos hl]
  have hsub : (H.Zhat (fun a => s a • f a) (fun b => s' b • f' b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => M.L.cj (s (Fin.castLE hl i))) *
        (H.Zhat f f').submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => s' (Fin.castLE hl i)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, HermSp.Zhat, Matrix.of_apply, h_scale]
    ring
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  ring

end Scale

section Glob

variable {D : D7}

theorem locU_f_eq (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) :
    (locU Z p Λ F F' Tn T'n).f = fun a => sgnP D p a • (locTerm Z p Λ F F' Tn T'n).f a := by
  funext a
  show frFac Z.δ p a • _ = sgnP D p a • ((sgnP D p a * frFac Z.δ p a) • _)
  rw [smul_smul, ← mul_assoc, localSign_sq, one_mul]

theorem locU_f'_eq (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) :
    (locU Z p Λ F F' Tn T'n).f' = fun b => sgnP' D p b • (locTerm Z p Λ F F' Tn T'n).f' b := by
  funext b
  show frFac Z.δ p b • _ = sgnP' D p b • ((sgnP' D p b * frFac Z.δ p b) • _)
  rw [smul_smul, ← mul_assoc, sgnP'_sq, one_mul]

theorem locU_isTerm : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ p : PlF D, (locH Z p).IsTerm (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' := by
  intro D Z u u' F0 Λ hR F' hPD hG p
  have hD1 : Formalism.MainNotions.S.Dl F0 F'.fl (D.R.rS + 1) ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact Formalism.L2.SG.Closed.DNeZeroAt_holds D.host.E (VS D) τ (D.sp.cm.cmUnram.2.1 τ) (D.sp.Y_sig 0) D.R.rS
      (Tu D u) (Tu D u') (Formalism.L2.SG.GramJoint.sig_hS D τ) (Formalism.L2.SG.GramJoint.Tu_pos D u)
      (Formalism.L2.SG.GramJoint.Tu_pos D u') F0 F'.fl hG
  have hT := bt_isTerm Z (locEqC_holds D Z) (locSatC_holds D Z) (locDiffC_holds D Z) (locUnimodC_holds D Z) p F0 Λ F'
    hR hPD hG hD1
  set t := locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht
  set U := locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with hU
  have hf := locU_f_eq Z p Λ (lf D F0) F' (Tu D u) (Tu D u')
  have hf' := locU_f'_eq Z p Λ (lf D F0) F' (Tu D u) (Tu D u')
  set c : ℕ → (D.s.atP p).Ep := fun l => if hl : l ≤ D.R.rS + 1 then
    ∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i)) * sgnP' D p (Fin.castLE hl i) else 1 with hc
  have hDl : ∀ l, l ≤ D.R.rS + 1 → (locH Z p).Dl U.f U.f' l = c l * (locH Z p).Dl t.f t.f' l := by
    intro l hl
    rw [hf, hf', Dl_scale _ _ _ _ _ l hl, hc]
    simp only [dif_pos hl]
    rfl
  have hcu : ∀ l, IsUnit (c l) := by
    intro l
    simp only [hc]
    split_ifs
    · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun i _ =>
        ((bt_isUnit_sq (localSign_sq p _)).map (Z.M p).L.cj).mul (bt_isUnit_sq (sgnP'_sq p _))
    · exact isUnit_one
  have hcl : c (D.R.rS + 1) = c D.R.rS := by
    simp only [hc, dif_pos le_rfl, dif_pos (Nat.le_succ _)]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.castLE_rfl, id, sgnP_last₂, bt_sgnP'_last, map_one, mul_one]
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hT.1
  · have h := bt_isFrame Z (locSatC_holds D Z) (locDiffC_holds D Z) p F0 Λ hR.2.1.1.fg hR.2.2
      hR.2.1.2.2.1.1 hR.2.1.2.2.2.2 (fun _ => 1) (fun _ => one_mul 1) rfl 1
      (fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm) (fun a => Matrix.one_apply_eq a)
      (bt_pair_li F0 F' hG).1 (bt_Tu_ne u)
    simp only [one_mul, inv_one, bt_frameAct_one] at h
    exact h
  · have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
    have h := bt_isFrame Z (locSatC_holds D Z) (locDiffC_holds D Z) p F'.fl Λ hR.2.1.1.fg hPD.2.2.2 hPD.1.1
      hPD.2.2.1.2 (fun _ => 1) (fun _ => one_mul 1) rfl _ hu.1 hu.2 (bt_pair_li F0 F' hG).2.1 (bt_Tu_ne u')
    simp only [one_mul] at h
    exact h
  · rw [hDl _ le_rfl]
    exact (hcu _).mul hT.2.2.2.1
  · have e : (locH Z p).Gdet U.f U.f' U.T U.T' = (c D.R.rS * (Z.M p).L.cj (c D.R.rS)) *
        (locH Z p).Gdet t.f t.f' t.T t.T' := by
      unfold Loc.HermSp.Gdet Loc.HermSp.normE
      rw [hDl _ le_rfl, hDl _ (Nat.le_succ _), hcl]
      simp only [map_mul]
      rw [show U.T = t.T from rfl, show U.T' = t.T' from rfl]
      ring
    rw [e]
    intro h0
    exact hT.2.2.2.2.1 ((IsUnit.mul_right_eq_zero ((hcu _).mul ((hcu _).map (Z.M p).L.cj))).1 h0)
  · intro g hg
    obtain ⟨h1, h2, h3⟩ := hT.2.2.2.2.2 g hg
    refine ⟨h1, h2, fun b => ?_⟩
    have hagree := (Z.agree p).2.2.2.2.2
    obtain ⟨sg, hs⟩ : ∃ sg, (D.s.atP p).split = some sg := by
      rcases hs : (D.s.atP p).split with _ | sg
      · rw [hg, hs] at hagree; exact hagree.elim
      · exact ⟨sg, rfl⟩
    have hsg : sgnP' D p b = sgnP D p b := by
      unfold sgnP'; rw [hs]
    have e : U.f' b - U.f b = sgnP D p b • (t.f' b - t.f b) := by
      rw [hf, hf']
      beta_reduce
      rw [hsg, smul_sub]
    have hm := Submodule.smul_mem _ (⟨sgnP D p b, bt_sq_one_mem Z p (localSign_sq p b)⟩ : (Z.M p).L.O) (h3 b)
    show U.f' b - U.f b ∈ _
    rw [e]
    exact hm
  · have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
    have hinv := inv_unitri _ hu.1 hu.2
    obtain ⟨Ap, hAp, -⟩ := GlobalTheory.LocOver.tri_scaled D Z (frame F') (frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹)
      ((admXi D Λ (lf D F0) F')⁻¹.map (fun x : 𝓞 D.host.E => (x : D.host.E)))
      ⟨fun a b h => by simp [hinv.1 a b h], fun a => by simp [hinv.2 a]⟩ (fun b => rfl)
    exact ⟨Ap p, (hAp p).1, (hAp p).2⟩

end Glob

end GlobalTheory.LocOver
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_unitriangular_frame_change_local_scalings : ∀ (D : D7) (Z : LocDat D), ∀ (f g : Fin (D.R.rS + 1) → (VS D).V) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Chg f A g → ∃ Ap : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ p, Uni (Ap p) ∧ Chg (scaled Z p f) (Ap p) (scaled Z p g)) ∧ {p : PlF D | ¬ ∀ a b, Ap p a b ∈ (Z.M p).L.O}.Finite := by
  first | exact @GlobalTheory.LocOver.tri_scaled | exact GlobalTheory.LocOver.tri_scaled | (intros; apply GlobalTheory.LocOver.tri_scaled <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localisedBaseFrames_relevantPair : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → ∀ p : PlF D, (∃ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P) ∧ ∀ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → P.RelG (LocNG.theta (Z.M p)) := by
  first | exact @GlobalTheory.LocBaseRel.atBase_relG | exact GlobalTheory.LocBaseRel.atBase_relG | (intros; apply GlobalTheory.LocBaseRel.atBase_relG <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  first | exact @GlobalTheory.CovDomGrp.latMap_Lc_iff | exact GlobalTheory.CovDomGrp.latMap_Lc_iff | (intros; apply GlobalTheory.CovDomGrp.latMap_Lc_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  first | exact @GlobalTheory.St.G.record_facts | exact GlobalTheory.St.G.record_facts | (intros; apply GlobalTheory.St.G.record_facts <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.count_isometry_pairs_with_given_fixed_space : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' s n : ℕ) (U : Submodule K V), 1 ≤ x → 1 ≤ x' → 1 ≤ n → Module.finrank K U + s = (Module.finrank K V) → GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L₀) = n → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}).encard : ℕ∞) : ℝ≥0∞) ≤ if (n : ℝ) ≤ (D₀ : ℝ) * x * x' then ENNReal.ofReal (((2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' / n) ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * cf K + 1) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (3 * (2 * j + 1)) * ((4 * s * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * s * (Formalism.HermitianLatticesTheory.fDeg K))) else 0 := by
  first | exact @GlobalTheory.DegCnt.FixedSpaceCount.main | exact GlobalTheory.DegCnt.FixedSpaceCount.main | (intros; apply GlobalTheory.DegCnt.FixedSpaceCount.main <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.deepPoint_bound_cuspidalIsometricIntertwinerFamily : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) → ‖vv B Fr (B.tens B.w) x‖ ^ 2 ≤ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal := by
  first | exact @GlobalTheory.DeepFamilyGap.deep_bound_family | exact GlobalTheory.DeepFamilyGap.deep_bound_family | (intros; apply GlobalTheory.DeepFamilyGap.deep_bound_family <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselEnergy_normalised_frame_change : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p * Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) = ENNReal.ofReal (lamN L cN ^ 4 / D.GamLev k r ‖cStd / L.c‖⁻¹ 1 0) * B.normSq Bs (conjF (cStd / L.c) F) := by
  first | exact @GlobalTheory.ThA.energy_change_of_frame | exact GlobalTheory.ThA.energy_change_of_frame | (intros; apply GlobalTheory.ThA.energy_change_of_frame <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.gaussianSum_stabiliserUnfolding : GaugeUnfold := by
  first | exact @GlobalTheory.StabUnfold.gaugeUnfold | exact GlobalTheory.StabUnfold.gaugeUnfold | (intros; apply GlobalTheory.StabUnfold.gaugeUnfold <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_sublattice_lifts_modulo_fixing_unipotent : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), SubOK D (L0X D Λ (lf D F0)) P s Q → ∃ reps : Finset (P →ₗ[𝓞 D.host.E] (hS D).V), (reps.card : ℝ) ≤ NT D u ^ (2 * D.R.rS) * Q ^ D.R.rS ∧ (∀ φ ∈ reps, ∀ p, φ p ∈ XLam Λ (lf D F0)) ∧ ∀ φ : P →ₗ[𝓞 D.host.E] (hS D).V, (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∃ φ₀ ∈ reps, ∃ n ∈ N1 D Λ (lf D F0), ∀ p : P, n (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) = D.sp.iXY 0 (p : (D.sp.X 0).V) + φ₀ p := by
  first | exact @GlobalTheory.LoopC.Lifts.main | exact GlobalTheory.LoopC.Lifts.main | (intros; apply GlobalTheory.LoopC.Lifts.main <;> assumption)
end
