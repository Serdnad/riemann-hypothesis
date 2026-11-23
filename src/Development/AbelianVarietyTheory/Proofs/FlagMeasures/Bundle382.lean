module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle372
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle290
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle264
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle070
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle369
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalInnerLatticeEqOfInnerPreimageEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericTermClassesEqRowsInDoubleCoset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFramesPrescribedLocalClasses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalStabiliserGluedLatticeLocalData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueUnimodularLatticeRepsMoveIsometryFrames
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne

@[expose] public section

section

noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSpanLat

variable {D : D7}

theorem localComplementUnitary_fixes_both_frames {Z : LocDat D} {p : PlF D} (P : LocNG.FPair (locH Z p) D.R.rS)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ P.UW0) :
    ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact fun _ => ⟨rfl, rfl⟩
  | mul x y _ _ hx hy =>
    intro b
    change x (y _) = _ ∧ x (y _) = _
    rw [(hy b).1, (hy b).2]; exact hx b
  | inv x _ hx =>
    intro b
    refine ⟨?_, ?_⟩
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).1]
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).2]

theorem h_zero_left {Z : LocDat D} {p : PlF D} (y : Vp D p) : (locH Z p).h 0 y = 0 := by
  show LocFacts₂ Z.M p 0 y = 0
  simp [LocFacts₂]

theorem frame_ne_zero {Z : LocDat D} {p : PlF D} (Fr : LocNG.FrameD (locH Z p) D.R.rS) (hT : Fr.T ≠ 0)
    (a : Fin (D.R.rS + 1)) : Fr.f a ≠ 0 := by
  intro h0
  induction a using Fin.lastCases with
  | last =>
    have h1 := Fr.h_zz
    rw [h0, h_zero_left] at h1
    have h2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep Fr.T = 0 := neg_eq_zero.mp h1.symm
    exact hT ((map_eq_zero_iff _ (RingHom.injective _)).mp h2)
  | cast i =>
    have h1 := Fr.h_es i i
    rw [h0, h_zero_left, if_pos rfl] at h1
    exact zero_ne_one h1

theorem frFac_unit {p : PlF D} (δ : ∀ p, (D.s.atP p).Fp) (a : Fin (D.R.rS + 1)) (v : Vp D p)
    (hv : frFac δ p a • v ≠ 0) : IsUnit (frFac δ p a) := by
  unfold frFac at hv ⊢
  by_cases hu : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (D.R.rS - a.val))
  · exact isUnit_ringInverse.mpr hu
  · rw [Ring.inverse_non_unit _ hu, zero_smul] at hv
    exact absurd rfl hv

def fixSub (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Submodule D.host.E (VS D).V where
  carrier := {u | g (baseChange₂ D p u) = baseChange₂ D p u}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [baseChange_smul₂, map_smul, ha]

theorem xplus_le {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (S : Submodule D.host.E (VS D).V)
    (h : ∀ a, frame F a ∈ S) : Xplus F ≤ S := by
  show F.fl.X ⊔ Submodule.span _ {F.fl.z} ≤ S
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    have := h i.castSucc
    simpa [frame, FlagG.fvec] using this
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have := h (Fin.last _)
    simpa [frame, FlagG.fvec] using this

theorem le_of_loc (Z : LocDat D) (Λ₂ : LV D) (h2 : Submodule.IsLattice D.host.E Λ₂) (N : LV D)
    (hN : ∀ z ∈ N, ∀ p, baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₂) : N ≤ Λ₂ := by
  intro x hx
  exact GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z h2.fg (hN x hx)

theorem fix_span {u u' : D.what₂.Word}
    (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) (p : PlF D)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ (FP p).UW0) :
    Xplus F ⊔ Xplus F' ≤ fixSub p g := by
  have hN := (hR p).2.2.2.2.2.2
  refine sup_le (xplus_le F _ fun a => ?_) (xplus_le F' _ fun a => ?_)
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).1
    have hne := frame_ne_zero (FP p).A hN.2.1 a
    rw [(hB p).1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F a)) = baseChange₂ D p (frame F a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).2
    have hne := frame_ne_zero (FP p).B hN.2.2.2.1 a
    rw [(hB p).2.1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F' a)) = baseChange₂ D p (frame F' a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa

theorem inf_span_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') := by
  intro D X Y u u' F F' w _ _ Z FP hB hR Λ₀ h0 Λ h1 hloc
  apply le_antisymm
  · refine le_inf (le_of_loc Z Λ₀ h0 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg] at hm
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hm
    have : g y = g (baseChange₂ D p z) := by rw [hfix]; exact hyz
    rw [g.injective this] at hy
    exact hy
  · refine le_inf (le_of_loc Z Λ h1 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₀ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg, ← hfix]
    exact Submodule.mem_map_of_mem hm

end GlobalTheory.FrameSpanLat
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Unfold.LocStab

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have := D.R.two_le_m; obtain ⟨t, ht⟩ := D.R.m_even
  unfold Ranks.rS Ranks.r; omega

theorem relIndex_comap_subtype {G : Type*} [Group G] (U X Y : Subgroup G) (hY : Y ≤ U) :
    (X.comap U.subtype).relIndex (Y.comap U.subtype) = X.relIndex Y := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hY]

theorem stabilizer_eq_comap {G α : Type*} [Group G] (U : Subgroup G) [MulAction U α] (S : Subgroup G) (d : α)
    (h : ∀ g : U, g.1 ∈ S ↔ g • d = d) : MulAction.stabilizer U d = S.comap U.subtype := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.coe_subtype, h g]

theorem comap_subtype_inf {G : Type*} [Group G] (U A : Subgroup G) :
    (U ⊓ A).comap U.subtype = A.comap U.subtype := by
  ext g; simp

end GlobalTheory.Unfold.LocStab

namespace GlobalTheory.Unfold.LocStab



theorem local_stabilisers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel _ hMv hSt Λ₀ d0 hLO
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hstab : ∀ p (d : LocNG.Datum (FP p)),
      MulAction.stabilizer ↥(FP p).UW0 d = (LocNG.Datum.Stab d).comap (FP p).UW0.subtype :=
    fun p d => stabilizer_eq_comap _ _ d (fun g => hSt p d g)
  have hle : ∀ p (d : LocNG.Datum (FP p)), LocNG.Datum.Stab d ≤ (FP p).UW0 :=
    fun p d => Subgroup.closure_le _ |>.2 fun g hg => hg.1
  choose τ0 hτ0 hτ0L using hLO.2
  have hc := fun p => GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
    (hRel p) (d0 p) (τ0 p) (hτ0 p)
  have hA : ∀ p, (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype =
      ((FP p).UW0 ⊓ LocNG.Aut (τ0 p).abelian₂).comap (FP p).UW0.subtype := by
    intro p; rw [comap_subtype_inf, hτ0L p]
  refine ⟨fun p => ?_, ?_, fun d hd p => ?_⟩
  · rw [hA p, hstab p]
    refine ⟨?_, ?_⟩
    · rw [relIndex_comap_subtype _ _ _ inf_le_left, Subgroup.relIndex_eq_one.2 (hc p).1]
      exact one_ne_zero
    · rw [relIndex_comap_subtype _ _ _ (hle p (d0 p))]
      exact (hc p).2.1
  · have hAt : ∀ p, GlobalTheory.LocOver.AtBase Z p F F' (Tu D u) (Tu D u') (FP p) := fun p => by
      obtain ⟨h1, h2, h3, h4⟩ := hB p
      exact ⟨h1, h2, h3, h4⟩
    refine (GlobalTheory.T.finite_places_not_primeTo_baseFrameInvariants D Z u u' F F' hG FP hAt).subset fun p hp hpr => hp ?_
    have h2 := GlobalTheory.T.datumStabilizer_preserves_termLattice_goodPlace (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) hpr (d0 p) (τ0 p) (hτ0 p)
    rw [hA p, hstab p]
    exact congrArg _ (le_antisymm (hc p).1 (le_inf (hle p (d0 p)) h2))
  · obtain ⟨τ, hτ⟩ := hd p
    have h3 := (hc p).2.2
    have hτc := GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) (d p) τ hτ
    rw [hstab p, hstab p, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p))]
    refine ⟨h3 (d p) τ hτ, hτc.2.2 (d0 p) (τ0 p) (hτ0 p), ?_⟩
    rw [GlobalTheory.HL.invVol, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p)), LocNG.Datum.wt, LocNG.volRel, one_div_div]

end GlobalTheory.Unfold.LocStab
end
end

section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GluedCong

theorem bc_eq (D : D7) (Z : LocDat D) (p : PlF D) (v : (VS D).V) :
    (GlobalTheory.HL.placesOf Z).bc p ((VS D).frame.equivFun v) = baseChange₂ D p v := by
  funext i; rfl

theorem lat_eq (D : D7) (Z : LocDat D) (p : PlF D) (L : LV D) :
    (GlobalTheory.HL.placesOf Z).lat p (L.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))) = lattice₂ D Z.M p L := by
  unfold GlobalTheory.HL.Places.lat lattice₂
  congr 1
  ext z
  simp only [Set.mem_image, Submodule.map_coe, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (bc_eq D Z p v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, bc_eq D Z p v⟩

theorem smul_mem_gmap (D : D7) (γ : GV D) (I : Ideal (𝓞 D.host.E))
    (L : LV D) (v : (VS D).V) (s : 𝓞 D.host.E) (h : s • v ∈ I • L) :
    s • γ v ∈ I • Formalism.HermitianLatticesTheory.gmap γ L := by
  have hg1 : I • Formalism.HermitianLatticesTheory.gmap γ L = (I • L).map ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_smul'']
  rw [hg1]
  refine Submodule.mem_map.2 ⟨s • v, h, ?_⟩
  exact (γ : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower s v



theorem glued_loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr' P hP
  obtain ⟨sg, hsp, hdict⟩ := GlobalTheory.T.split_and_smul_completedLattice_le_at_level_prime D Z P hP
  have hL0 := hL
  obtain ⟨hlat, hloc⟩ := hL
  obtain ⟨τ, hτ, hτL⟩ := hloc (below D P)
  obtain ⟨B, hB1, hB2, hBy⟩ := GlobalTheory.T.local_adaptedIsometry_frame_upperTriangular_expansion D (lf D (X.Fu u)) F g hA Z (below D P) (FP (below D P)).A.f (hB (below D P)).1
  obtain ⟨B', hB1', hB2', hBx⟩ := GlobalTheory.T.local_adaptedIsometry_frame_upperTriangular_expansion D (lf D (X.Fu u')) F' g' hA' Z (below D P) (FP (below D P)).B.f (hB (below D P)).2.1
  have hU := GlobalTheory.T.frameScale_isUnit_at_prime_over_level D (Tu D u) (Tu D u') (X.Fu u) F F' Z FP hB Λ y hL0 g hA hr P hP
  have hmemg : ∀ (γ : GV D) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T), IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ) →
      ∀ a, γ (frame (lf D F0) a) ∈ Λ := by
    intro γ T F0 h a
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.1 (GlobalTheory.T.fixedFlag_frameVector_mem_rowLattice D F0 _ h a)
    have e : γ (frame (lf D F0) a) = v := by
      rw [← hve]
      show γ (γ⁻¹ v) = v
      exact γ.apply_symm_apply v
    rw [e]; exact hv
  have hyL : ∀ a, baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g (X.Fu u) hr a, rfl⟩
  have hxL : ∀ a, baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g' (X.Fu u') hr' a, rfl⟩
  obtain ⟨ξp, hξO, hξ1, hξ2, hξc⟩ := GlobalTheory.T.term_families_congr_mod_unitriangular (locH Z (below D P)) (FP (below D P)) (y (below D P)) τ sg hsp hτ
    (fun b => baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) b))) (fun b => baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) b))) B B' hB1 hB1'
    (fun a => by rw [hB2, hB2'])
    (fun a => by
      rw [hB2]
      exact ⟨(hU a).2, frFac Z.δ (below D P) a, (hU a).1, Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z (below D P) a)⟩)
    hBy hBx hyL hxL
  have hfg : (Λ.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))).FG := hlat.fg.map _
  have hpos : 0 < gS D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.HL.LocCongApprox.loc_cong_approx (GlobalTheory.HL.placesOf Z) (nV D) D.R.rS _ hfg
    (gS D) hpos (below D P) (fun a => (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)))
    (fun b => (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b))) ξp hξO hξ1 hξ2
    (fun a => by
      rw [lat_eq, bc_eq, ← hτL]
      exact hyL a)
    (fun b => by
      rw [← Submodule.map_smul'', lat_eq]
      have h1 := hdict Λ _ (hτL ▸ hξc b)
      simp only [bc_eq]
      exact h1)
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  obtain ⟨v, hv⟩ : ∃ v, v = g' (frame (lf D (X.Fu u')) b) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • g (frame (lf D (X.Fu u)) a) := ⟨_, rfl⟩
  have hφv : (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b)) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)) = (VS D).frame.equivFun v := by

    rw [hv, map_sub, map_sum]
    simp only [map_smul]
  rw [hφv] at h
  obtain ⟨s, hs, hsv⟩ := h
  rw [← Submodule.map_smul''] at hsv
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hzs : z = s • v := by
    apply ((VS D).frame.equivFun).injective
    have e1 : (VS D).frame.equivFun z = s • (VS D).frame.equivFun v := hzv
    rw [e1]
    exact (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).map_smul_of_tower s v).symm
  have hiso : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hA.1) hA'.1
  have hfr : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b = (g⁻¹ * g') (frame (lf D (X.Fu u')) b) := by
    unfold mapLF
    rw [dite_eq_left hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(g⁻¹ * g')) _ _) b).symm
  have htarget : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b = g⁻¹ v := by

    rw [hfr, hv, map_sub, map_sum, LinearEquiv.mul_apply]
    unfold frameAct
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun a _ => ?_)
    exact (((g⁻¹ : GV D).map_smul _ _).trans (congrArg _ (g.symm_apply_apply _))).symm
  have hsv' : s • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    rw [← hzs]; exact hz
  refine ⟨s, hs, ?_⟩
  rw [htarget]
  exact smul_mem_gmap D g⁻¹ (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)}) Λ v s hsv'

end GlobalTheory.Unfold.GluedCong
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.innerDatum_stable_iff_identifications_compatible : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h b₁ b₂ : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → b₁ ∈ Aut0 F0 lam → b₂ ∈ Aut0 F0' lam' → h ∈ H0 F F' → (∀ x ∈ orth (VS D) (Xsp F), h x - (g * b₁ * g⁻¹) x ∈ Xsp F) → (∀ x ∈ orth (VS D) (Xsp F'), h x - (g * γ * b₂ * γ⁻¹ * g⁻¹) x ∈ Xsp F') → (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ ↔ IotaCompat lam F0 (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') (b₁ * γ * b₂⁻¹ * γ⁻¹) (gS D)) := by
  first | exact @GlobalTheory.GdatIota.gdat_iff_iotaCompat | exact GlobalTheory.GdatIota.gdat_iff_iotaCompat | (intros; apply GlobalTheory.GdatIota.gdat_iff_iotaCompat <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.innerPreimage_eq_of_local_innerLattice_eq : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := by
  first | exact @GlobalTheory.Unfold.LsubG.lsub_eq_of_local | exact GlobalTheory.Unfold.LsubG.lsub_eq_of_local | (intros; apply GlobalTheory.Unfold.LsubG.lsub_eq_of_local <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localInnerLattice_eq_of_innerPreimage_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS), Fr.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ G = Lsub Λ₂ G → (locH Z p).Lset (lattice₂ D Z.M p Λ₁) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) Fr.f := by
  first | exact @GlobalTheory.Unfold.InnerLoc.lset_eq_of_lsub_eq | exact GlobalTheory.Unfold.InnerLoc.lset_eq_of_lsub_eq | (intros; apply GlobalTheory.Unfold.InnerLoc.lset_eq_of_lsub_eq <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nonGeneric_term_classes_eq_rows_in_double_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → ClsRow (Y.tO u u').ngSet (clsOf Y u u') := by
  first | exact @GlobalTheory.Unfold.RowCls.clsRow_ngSet | exact GlobalTheory.Unfold.RowCls.clsRow_ngSet | (intros; apply GlobalTheory.Unfold.RowCls.clsRow_ngSet <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tsum_rationalClasses_eq_prod_localSums : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP) (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → BaseOK (Tu D u) (Tu D u') F F' P d0 → MassLaw F F' P d0 V → ∀ φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞, (∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d') → (∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0) → (∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p) else 0) = ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1 := by
  first | exact @GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | exact GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | (intros; apply GlobalTheory.GenMass.tsum_classes_eq_prod_locSums <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_frames_prescribed_local_classes : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (f f' : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p), (∀ p ∈ P, Tri (D.s.atP p).Ep (scaled Z p (frame F)) (f p) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (f' p)) → ∃ (G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), StdOff Z P F G F' G' ∧ ∀ p ∈ P, ∃ A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni A ∧ Uni A' ∧ (∀ a b, A a b ∈ (Z.M p).L.O ∧ A' a b ∈ (Z.M p).L.O ∧ A a b - A' a b ∈ Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta (Z.M p))}) ∧ Chg (f p) A (scaled Z p (frame G)) ∧ Chg (f' p) A' (scaled Z p (frame G')) := by
  first | exact @GlobalTheory.FrameChoice.choose_frames | exact GlobalTheory.FrameChoice.choose_frames | (intros; apply GlobalTheory.FrameChoice.choose_frames <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_rationalStabiliser_gluedLattice_localData : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → TotPos (Gval F F') → ∀ (Λ : LV D) (y : Dat Z FP), Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') → Λ ∈ globSet G G' y → (stabY F F' y).Finite := by
  first | exact @GlobalTheory.StabYFin.stabY_finite | exact GlobalTheory.StabYFin.stabY_finite | (intros; apply GlobalTheory.StabYFin.stabY_finite <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.glueUnimodularLatticeReps_move_isometry_frames : ∀ (D : D7) (T T' : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (n : GV D), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame G a = n (frame F a)) → (∀ a, frame G' a = n (frame F' a)) → ∀ s : Finset (LV D), Glue F F' s → ∃ s' : Finset (LV D), Glue G G' s' ∧ glueSum G G' s' = glueSum F F' s := by
  first | exact @GlobalTheory.GlueMove.glue_move | exact GlobalTheory.GlueMove.glue_move | (intros; apply GlobalTheory.GlueMove.glue_move <;> assumption)
end
