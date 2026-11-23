module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle375
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle376
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle381
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle366
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle359
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle383
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle387
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocNoDef
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem N_unitary (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : ∀ n ∈ Fr.N, IsUnitary H n := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => intro a b; rfl
  | mul x y _ _ hx hy => intro a b; rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]
  | inv x _ hx =>
    intro a b
    have hxx : ∀ v, x (x⁻¹ v) = v := fun v => by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [← hx (x⁻¹ a) (x⁻¹ b), hxx, hxx]

theorem frame_mem_lamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) (b : Fin (r + 1)) : Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  induction b using Fin.lastCases with
  | last =>
    have h1 : ∀ a, H.h (Fr.f (Fin.last r)) (Fr.es a) = 0 := fun a => by
      rw [H.h_herm (Fr.es a), Fr.h_sz, map_zero]
    have h2 : ∀ a : Fin r, H.h (Fr.f (Fin.last r)) (Fr.e a) = 0 := fun a =>
      Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne)
    refine ⟨fun a => by rw [h1]; exact M.L.O.zero_mem, fun a => by rw [h2]; exact M.L.O.zero_mem, xz, ?_, hxzL⟩
    simp [FrameD.prF, h1, h2, hxz, FrameD.z]
  | cast a =>
    have h1 : ∀ c, H.h (Fr.f a.castSucc) (Fr.es c) = if a = c then 1 else 0 := fun c => Fr.h_es a c
    have h2 : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.e c) = 0 := fun c =>
      Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    refine ⟨fun c => ?_, fun c => by rw [h2]; exact M.L.O.zero_mem, 0, ?_, by simp⟩
    · rw [h1]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · have h2' : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.f c.castSucc) = 0 := h2
      simp [FrameD.prF, h1, h2', FrameD.e]

theorem noDefect_gen (H : HermSp M V) {r : ℕ} (P : FPair H r) (hR : P.RelG (theta M)) (hP : P.PrimeTo)
    (d : Datum P) (t : Term V M r) (ht : IsTermOver P d t) : ¬ BBne (H := H) t := by
  rintro ⟨v, hvΛ, hvE, hvO⟩
  have hs : M.split = none := hP.1
  have hMM : H.MMfam t = Sum.elim t.f t.f' := by
    unfold HermSp.MMfam; rw [hs]
  rw [hMM] at hvE hvO
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩ := ht
  have hu := N_unitary H P.A n hn
  have hu' := N_unitary H P.B n' hn'

  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    rw [hΛ] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [hu]
    exact GlobalTheory.T.frameStandardLattice_hermitian_integral H P.A d.L d.hL x0 hx0 y0 hy0
  have hmem : ∀ i, Sum.elim t.f t.f' i ∈ t.abelian₂ := by
    rintro (b | b)
    · simp only [Sum.elim_inl, hf]
      rw [hΛ]
      exact Submodule.mem_map_of_mem (f := ((n : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.A d.L d.hL b)
    · simp only [Sum.elim_inr, hf']
      rw [hΛ']
      exact Submodule.mem_map_of_mem (f := ((n' : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.B d.L' d.hL' b)
  have hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l := by
    intro l
    rw [hf, hf']
    exact GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes H _ _ _ _ (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.A n hn) (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.B n' hn') l
  have hG : H.Gdet t.f t.f' t.T t.T' = P.Gv := by
    simp only [HermSp.Gdet, hDl, hT, hT', FPair.Gv]
  have hfr : ∀ (Fr : FrameD H r) (g : V ≃ₗ[E] V), IsUnitary H g → ∀ a b,
      H.h (g (Fr.f a)) (g (Fr.f b)) =
        if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E Fr.T) else 0 := by
    intro Fr g hg a b
    rw [hg]
    split_ifs with hab
    · rw [hab.1, hab.2]; exact Fr.h_zz
    · apply Fr.h_iso
      tauto
  have hdet := GlobalTheory.T.gramDet_joinedFamily_eq_pm_norm_difference H t.f t.f' t.T t.T'
    (by intro a b; rw [hf, hT]; exact hfr P.A n hu a b)
    (by intro a b; rw [hf', hT']; exact hfr P.B n' hu' a b)
    (by rw [hDl]; exact hR.2.1)
  rw [hG] at hdet
  have hU : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    obtain ⟨h1, y, hy, hxy⟩ := hP.2.1
    rcases hdet with h | h
    · rw [h]; exact ⟨h1, y, hy, hxy⟩
    · rw [h]
      refine ⟨M.L.O.neg_mem h1, -y, M.L.O.neg_mem hy, ?_⟩
      rw [neg_mul_neg]; exact hxy
  exact hvO (GlobalTheory.T.saturated_span_of_gramDet_isUnit_integralLattice H t.abelian₂ hint (Sum.elim t.f t.f') hmem hU v hvΛ hvE)

end Gen

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t :=
  fun _ _ FP p hR hP d t ht => noDefect_gen _ (FP p) hR hP d t ht

end GlobalTheory.LocNoDef

end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AdmFrame

theorem frame_mem_locP (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : IsLift Λ (lf D F0)) (hF : FrameOK D Λ (lf D F0))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frame (lf D F0) a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction a using Fin.lastCases with
  | last =>
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    simp only [one_smul, frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
    exact hL.1
  | cast i =>
    obtain ⟨c, -, hc1, hc⟩ := hF.1.1 P
    have hci : c i = 1 := hc1 hP i
    have hmem : (lf D F0).fl.e i ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F0)) := by
      rw [hc]
      refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
      rw [one_smul]
      have : (lf D F0).fl.e i = c i • (lf D F0).fl.e i := by rw [hci, one_smul]
      rw [this]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := hmem
    refine ⟨s, hs, ?_⟩
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    exact (inf_le_left : XLam Λ (lf D F0) ≤ Λ) hx

theorem lift_transport (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂) {T : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (hL : IsLift Λ₁ F) : IsLift Λ₂ (mapLF γ F) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  refine ⟨?_, ?_⟩
  · rw [← h]
    exact ⟨F.fl.z, hL.1, rfl⟩
  · show γ F.zt = γ F.fl.z
    rw [hL.2]

theorem exists_admissible_integralFrame_of_localTerms_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  have hγ : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hrow' : IsRowLat D (X.Fu u') t₀.lam' := (Y.rowsOK u').1 _ t₀.mem'
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  have hpd' := Formalism.L2.SG.TermDef.pd_self (X.Fu u') t₀.lam' hrow'
  have hpd := Formalism.L2.SG.TermDef.pd_self (X.Fu u) t₀.lam hrow
  refine ⟨lift_transport D _ hγ _ _ hlam _ hpd'.1, ?_, GlobalTheory.T.integralRowFrame_map_isometry D _ hγ _ _ hlam _ _ hpd'.2.2⟩
  have hloc := GlobalTheory.T.movedReferenceFrame_congruent_unitriangular D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  obtain ⟨ξ, h1, h2, h3⟩ := GlobalTheory.T.glue_frame_congruences_unitriangular_integral (VS D) D.R.rS t₀.lam (gS D) (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
    (frame (lf D (X.Fu u))) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))))
    (fun P hP a => frame_mem_locP D (X.Fu u) t₀.lam hpd.1 hpd.2.2 P hP a) hloc
  exact ⟨ξ, h1, h2, h3⟩

end GlobalTheory.HL.AdmFrame
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (∀ n, n ∈ NRat (lf D (X.Fu u)) ↔ c.grp ρ n ∈ G.N) ∧ (∀ m, m ∈ NRat (lf D (X.Fu u')) ↔ c.grp (ρ * t₀.lin) m ∈ G.N') ∧ (∀ (σ n : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) Λ, c.lat (σ * n) Λ = (c.lat σ Λ).map (((c.grp σ n : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E))) ∧ (∀ (σ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (x : G.GLV), ∃ n, c.grp σ n = x) ∧ (∀ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∀ (p : PlF D) g Λ, GlobalTheory.LocOver.Ext p σ g → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Y.M p) g (lattice₂ D Y.M p Λ))) ∧ ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  first | exact @GlobalTheory.HL.GrpCoord.grp_coords | exact GlobalTheory.HL.GrpCoord.grp_coords | (intros; apply GlobalTheory.HL.GrpCoord.grp_coords <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ClsStable

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E]

theorem h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (y : V) : H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := H.h_smul_left 0 0 y
    simpa using this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H.h_add_left, ih]

theorem h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (x : V) : H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by

  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.h_herm]

theorem zhat_chg {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ)
    (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hg : GlobalTheory.LocOver.Chg f A g) (hg' : GlobalTheory.LocOver.Chg f' A' g') :
    H.Zhat g g' = A.transpose.map M.L.cj * H.Zhat f f' * A' := by
  ext a b
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [hg a, hg' b, h_sum_left]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [H.h_smul_left, h_sum_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h_smul_right]
  ring

theorem intUni_mul {M : Loc.Model F E} {r : ℕ} {B A : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hB : IntUni M B) (hA : IntUni M A) : IntUni M (B * A) := by
  refine ⟨fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hB.1 a c h, zero_mul]
    · rw [hA.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hB.2.1, hA.2.1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hB.1 a c h, zero_mul]
      · rw [hA.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hB.2.2 a c) (hA.2.2 c b)

theorem span_mul_mem {M : Loc.Model F E} {t x o : E} (hx : x ∈ Submodule.span M.L.O {t}) (ho : o ∈ M.L.O) :
    x * o ∈ Submodule.span M.L.O {t} ∧ o * x ∈ Submodule.span M.L.O {t} := by
  have h1 : (⟨o, ho⟩ : M.L.O) • x ∈ Submodule.span M.L.O {t} := Submodule.smul_mem _ _ hx
  have h2 : (⟨o, ho⟩ : M.L.O) • x = o * x := rfl
  rw [h2] at h1
  exact ⟨by rw [mul_comm]; exact h1, h1⟩

theorem zhat_mem_clsLoc_of_chg : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Y0 f f' g g' A A' hA hA' hint hg hg' hY
  obtain ⟨B, B', hB, hB', hBB, hZ⟩ := hY
  have hIA : IntUni M A := ⟨hA.1, hA.2, fun a b => (hint a b).1⟩
  have hIA' : IntUni M A' := ⟨hA'.1, hA'.2, fun a b => (hint a b).2.1⟩
  refine ⟨B * A, B' * A', intUni_mul hB hIA, intUni_mul hB' hIA', fun a b => ?_, ?_⟩
  · have e : (B * A) a b - (B' * A') a b =
        ∑ c, (B a c - B' a c) * A c b + ∑ c, B' a c * (A c b - A' c b) := by
      simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) (Submodule.sum_mem _ fun c _ => ?_)
    · exact (span_mul_mem (hBB a c) (hIA.2.2 c b)).1
    · exact (span_mul_mem (hint c b).2.2 (hB'.2.2 a c)).2
  · rw [zhat_chg H r f f' g g' A A' hg hg', hZ, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ClsStable
end
end
