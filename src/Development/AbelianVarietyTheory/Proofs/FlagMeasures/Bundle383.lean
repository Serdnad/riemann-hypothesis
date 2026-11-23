module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle373
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle366
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle365
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle372
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle374
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem span_coef_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] (H : Loc.HermSp M V) (c : E) (e : V) (S : Set V) (N : Submodule M.L.O E)
    (hS : ∀ w ∈ S, c * H.h w e ∈ N) : ∀ w ∈ Submodule.span M.L.O S, c * H.h w e ∈ N := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    have h0 : H.h 0 e = 0 := by simpa using H.h_smul_left 0 0 e
    rw [h0, mul_zero]
    exact N.zero_mem
  | add x y _ _ hx hy =>
    rw [H.h_add_left, mul_add]
    exact N.add_mem hx hy
  | smul r x _ hx =>
    have hmem := N.smul_mem r hx
    rw [Subring.smul_def, smul_eq_mul] at hmem
    rw [Subring.smul_def, H.h_smul_left, mul_left_comm]
    exact hmem



theorem span_coefIdeal_eq_span_frFac : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∀ (p : PlF D) (a : Fin D.R.rS), Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (GlobalTheory.RowLatXS.Ia Λ G.fl a : Set D.host.E)) = Submodule.span (Z.M p).L.O {frFac Z.δ p a.castSucc} := by
  intro D T G Z A hA Λ hL hloc p a
  obtain ⟨n, hn, L, -, hΛ⟩ := hloc p

  have hFj : (A p).Fj (a.val + 1) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa (a.val + 1) : Set (VS D).V)) :=
    (GlobalTheory.T.local_flag_scaled_frame_eq_baseChange_flag D T G Z A hA p (a.val + 1)).symm
  have hXle : G.fl.Xa (a.val + 1) ≤ G.fl.X := Submodule.span_mono (Set.image_subset_range _ _)

  have hint : ∀ y : D.host.E, IsIntegral ℤ y → (D.s.atP p).ιE y ∈ (Z.M p).L.O := by
    intro y hy
    rw [Formalism.L2.SG.Pf.LocFacts.lf_hO Z p, (D.s.atP p).O_def]
    exact (hy.map (D.s.atP p).ιE.toIntAlgHom).tower_top
  apply le_antisymm
  ·
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, hxΛ, hxX, rfl⟩ := ht
      have hv1 : baseChange₂ D p x ∈ (A p).Fj (a.val + 1) := by
        rw [hFj]; exact Submodule.subset_span ⟨x, hxX, rfl⟩
      have hv2 : baseChange₂ D p x ∈ LocNG.img n ((A p).LamStd L) := by
        rw [← hΛ]; exact Submodule.subset_span ⟨x, hxΛ, rfl⟩
      have hO := GlobalTheory.T.flagStep_locallyStandard_dualCoeff_integral (A p) n hn L a (baseChange₂ D p x) hv1 hv2
      rw [← GlobalTheory.T.scaled_local_dual_coeff_eq_global_coeff D T G Z A hA p a x (hXle hxX)]
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨⟨_, hO⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
    | zero =>
      rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hrO : (D.s.atP p).ιE (algebraMap (𝓞 D.host.E) D.host.E r) ∈ (Z.M p).L.O :=
        hint _ (NumberField.RingOfIntegers.isIntegral r).algebraMap
      have hmem := Submodule.smul_mem _ (⟨_, hrO⟩ : (Z.M p).L.O) hx
      rw [Subring.smul_def, smul_eq_mul] at hmem
      rw [Algebra.smul_def, map_mul]
      exact hmem
  ·
    rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨v, hvΛ, hvF, hv1⟩ := GlobalTheory.T.exists_flagStep_locallyStandard_dualCoeff_one (A p) n hn L a
    rw [← hΛ] at hvΛ
    rw [hFj] at hvF
    set Xr : Submodule D.host.E (VS D).V := G.fl.Xa (a.val + 1) with hXr
    set W : Submodule D.host.E (Fin (nV D) → D.host.E) :=
      Xr.map ((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)) with hW

    have hsat : v ∈ lattice₂ D Z.M p (Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)) := by
      have hFG : (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)).FG := hL.fg.map _
      have key : (PI.LocLatEq.latL (D.s.atP p)
            (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D) ⊓ W.restrictScalars (𝓞 D.host.E)) : Set (Vp D p)) =
          (PI.LocLatEq.latL (D.s.atP p) (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p)) ∩
            Submodule.span (D.s.atP p).Ep (PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E))) :=
        inf_eq_inter_span _ _ _ _ (D.s.atP p) _ _ _ hFG
      have himg : baseChange₂ D p '' (Xr : Set (VS D).V) =
          PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E)) := by
        rw [hW, Submodule.map_coe, Set.image_image]
        apply Set.image_congr
        intro x _
        rw [Formalism.L2.SG.Pf.LocFacts.localBaseChange_eq]
        rfl
      have hvΛ' : v ∈ (PI.LocLatEq.latL (D.s.atP p) (Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p)) := by
        rw [← Formalism.L2.SG.Pf.LocFacts.localLattice_coe Z p Λ]; exact hvΛ
      have hvF' : v ∈ Submodule.span (D.s.atP p).Ep
          (PI.LocLatEq.bc (D.s.atP p) '' (W : Set (Fin (nV D) → D.host.E))) := by
        rw [← himg]; exact hvF
      have hmap : (Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)).map (Formalism.L2.SG.Pf.LocFacts.phi D) =
          Λ.map (Formalism.L2.SG.Pf.LocFacts.phi D) ⊓ W.restrictScalars (𝓞 D.host.E) := by
        ext y
        constructor
        · rintro ⟨x, ⟨hxΛ, hxX⟩, rfl⟩
          exact ⟨⟨x, hxΛ, rfl⟩, ⟨x, hxX, rfl⟩⟩
        · rintro ⟨⟨x, hxΛ, rfl⟩, ⟨x', hx'X, hx'⟩⟩
          have hxx : x' = x := (VS D).frame.equivFun.injective hx'
          subst hxx
          exact ⟨x', ⟨hxΛ, hx'X⟩, rfl⟩
      have h3 : v ∈ (PI.LocLatEq.latL (D.s.atP p)
          ((Λ ⊓ Xr.restrictScalars (𝓞 D.host.E)).map (Formalism.L2.SG.Pf.LocFacts.phi D)) : Set (Vp D p)) := by
        rw [hmap, key]; exact ⟨hvΛ', hvF'⟩
      rw [← Formalism.L2.SG.Pf.LocFacts.localLattice_coe Z p] at h3
      exact h3
    have key := span_coef_mem (locH Z p) (frFac Z.δ p a.castSucc) ((A p).es a)
      (baseChange₂ D p '' ((Λ ⊓ Xr.restrictScalars (𝓞 D.host.E) : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V))
      (Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (GlobalTheory.RowLatXS.Ia Λ G.fl a : Set D.host.E))) ?_ v hsat
    · rw [hv1, mul_one] at key
      exact key
    · rintro _ ⟨x, ⟨hxΛ, hxX⟩, rfl⟩
      rw [GlobalTheory.T.scaled_local_dual_coeff_eq_global_coeff D T G Z A hA p a x (hXle hxX)]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨x, hxΛ, hxX, rfl⟩, rfl⟩

end GlobalTheory.RowLatXS
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.SideEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) :
    frame F (Fin.last D.R.rS) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem xflag_top {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xflag F D.R.rS = Xsp F := by
  simp only [Xflag, Xsp, FlagG.Xa, FlagG.X]
  congr 1
  have : {i : Fin D.R.rS | i.1 < D.R.rS} = Set.univ := by ext i; simp [i.2]
  rw [this, Set.image_univ]

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {i j : ℕ} (h : i ≤ j) : Xflag F i ≤ Xflag F j := by
  exact Submodule.span_mono (Set.image_mono fun k (hk : k.1 < i) => (lt_of_lt_of_le hk h : k.1 < j))

theorem xflag_eq_range {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    Xflag F j = Submodule.span D.host.E (Set.range fun i : {i : Fin D.R.rS // i.1 < j} => F.fl.e i.1) := by
  simp only [Xflag, FlagG.Xa]
  congr 1
  ext x; simp

theorem finrank_xflag_eq {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Fintype.card {i : Fin D.R.rS // i.1 < j} := by
  rw [(LinearEquiv.ofEq _ _ (xflag_eq_range F j)).finrank_eq]
  exact finrank_span_eq_card (F.fl.e_indep.comp (fun i : {i : Fin D.R.rS // i.1 < j} => i.1) Subtype.val_injective)

theorem finrank_xflag {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (G : LFlag (D.sp.Y 0) D.R.rS T') (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Module.finrank D.host.E (Xflag G j) := by
  rw [finrank_xflag_eq, finrank_xflag_eq]

theorem map_xflag_le {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
  simp only [Xflag, FlagG.Xa]
  rw [Submodule.map_span_le]
  rintro _ ⟨i, hi, rfl⟩
  have h1 := hg.2 (Fin.castSucc i)
  rw [frame_castSucc, frame_castSucc] at h1
  have e : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) = (g (F.fl.e i) - G.fl.e i) + G.fl.e i := by
    simp
  rw [e]
  refine add_mem ?_ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hle := xflag_mono G (show (Fin.castSucc i).val ≤ j from le_of_lt hi)
  exact hle h1

theorem map_xflag {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j := by
  haveI : FiniteDimensional D.host.E (Xflag G j) :=
    FiniteDimensional.span_of_finite D.host.E ((Set.toFinite _).image _)
  refine Submodule.eq_of_le_of_finrank_eq (map_xflag_le hg j) ?_
  rw [LinearEquiv.finrank_map_eq]
  exact finrank_xflag F G j

theorem map_xsp {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  rw [← xflag_top, ← xflag_top]; exact map_xflag hg _

theorem adapt_mul {T : D.host.E} {F G H : LFlag (D.sp.Y 0) D.R.rS T} {g g' : GV D} (hg : Adapt g F G)
    (hg' : Adapt g' G H) : Adapt (g' * g) F H := by
  refine ⟨mul_mem hg'.1 hg.1, fun a => ?_⟩
  have e : (g' * g) (frame F a) - frame H a = g' (g (frame F a) - frame G a) + (g' (frame G a) - frame H a) := by
    change g' (g (frame F a)) - frame H a = _
    rw [map_sub]; abel
  rw [e]
  refine add_mem ?_ (hg'.2 a)
  rw [← map_xflag hg' a.val]
  exact Submodule.mem_map_of_mem (hg.2 a)

theorem adapt_inv {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    Adapt g⁻¹ G F := by
  refine ⟨inv_mem hg.1, fun a => ?_⟩
  have hm := map_xflag hg a.val
  have h2 := hg.2 a
  rw [← hm] at h2
  obtain ⟨y, hy, hye⟩ := h2
  have e : g⁻¹ (frame G a) - frame F a = -y := by
    have : g (frame F a - y) = frame G a := by
      rw [map_sub]; simp only [LinearEquiv.coe_coe] at hye; rw [hye]; abel
    rw [← this]
    show g.symm (g (frame F a - y)) - frame F a = -y
    rw [LinearEquiv.symm_apply_apply]; abel
  rw [e]; exact neg_mem hy

theorem z_mem_orth {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : F.fl.z ∈ orth (VS D) (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  simp only [Xsp, FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact F.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem nrat_adapt {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) : Adapt n F F := by
  refine ⟨hn.1, fun a => ?_⟩
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_top]
    exact hn.2.2 _ (z_mem_orth F)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inj (g : GV D) {M N : LV D} (h : Formalism.HermitianLatticesTheory.gmap g M = Formalism.HermitianLatticesTheory.gmap g N) : M = N := by
  have := congrArg (Formalism.HermitianLatticesTheory.gmap g⁻¹) h
  rwa [← gmap_mul, ← gmap_mul, inv_mul_cancel, gmap_one, gmap_one] at this

theorem map_toO (g : GV D) (U : Submodule D.host.E (VS D).V) :
    (toO (VS D) U).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      toO (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext x
  simp only [toO, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply]

theorem map_orth {g : GV D} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (U : Submodule D.host.E (VS D).V) :
    (orth (VS D) U).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) =
      orth (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext y
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩ x ⟨u, hu, rfl⟩
    rw [hg u w]; exact hw u hu
  · intro h
    refine ⟨g.symm y, fun x hx => ?_, by simp⟩
    have := h (g x) ⟨x, hx, rfl⟩
    rw [← hg x (g.symm y)]
    simpa using this

theorem lsub_map {T : D.host.E} {F G : LFlag (D.sp.Y 0) D.R.rS T} {g : GV D} (hg : Adapt g F G) (Λ : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap g Λ) G = Formalism.HermitianLatticesTheory.gmap g (Lsub Λ F) := by
  have hinj : Function.Injective ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) :=
    g.injective
  simp only [Lsub, Lrep, Formalism.HermitianLatticesTheory.gmap]
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj, map_toO, map_toO, map_orth hg.1,
    map_xsp hg]

theorem side : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (v : D.what₂.Word) (B : LFlag (D.sp.Y 0) D.R.rS ((Tu D v : ℕ) : D.host.E)) (ψ₀ ψ₁ : GV D) (Λa Λb : LV D), Λa ∈ Y.what₂ v → Λb ∈ Y.what₂ v → Adapt ψ₀ (lf D (X.Fu v)) B → Adapt ψ₁ (lf D (X.Fu v)) B → Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ Λa) B = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ Λb) B → Λb = Λa ∧ ∃ n ∈ NRat (lf D (X.Fu v)), n * (ψ₁⁻¹ * ψ₀) ∈ Aut0 (lf D (X.Fu v)) Λa := by
  intro D X Y v B ψ₀ ψ₁ Λa Λb ha hb A0 A1 hL
  have As : Adapt (ψ₁⁻¹ * ψ₀) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul A0 (adapt_inv A1)
  have hsub : Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₁⁻¹ * ψ₀) Λa) (lf D (X.Fu v)) = Lsub Λb (lf D (X.Fu v)) := by
    apply gmap_inj ψ₁
    rw [← lsub_map A1, ← lsub_map A1, ← gmap_mul, mul_inv_cancel_left]
    exact hL
  obtain ⟨n, hn, hnΛ⟩ := GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu v) Λa Λb (ψ₁⁻¹ * ψ₀) ((Y.rowsOK v).1 Λa ha)
    ((Y.rowsOK v).1 Λb hb) As hsub
  have Ans : Adapt (n * (ψ₁⁻¹ * ψ₀)) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul As (nrat_adapt hn)
  have heq : Λa = Λb := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y v v).2 Λb hb Λa ha _ Ans hnΛ
  exact ⟨heq.symm, n, hn, Ans, hnΛ.trans heq.symm⟩

end GlobalTheory.Unfold.SideEq
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatClassFin

theorem fg_of_le_fg {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    {N L : Submodule (𝓞 K) V} (hL : L.FG) (h : N ≤ L) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hL
  have h1 := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_of_le_right h]
  rw [← e]; exact h1.map _

theorem frame_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : LFlag S r T) (a : Fin (r + 1)) : frame F a ∈ Xplus F := by
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  | cast i =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc i) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem classes_fin : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D T T' F F' hpos A N d c hN hd hc
  classical
  set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef
  set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef
  have hcompl : IsCompl U W := GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive (VS D) U hpos
  let hW : ↥W →ₗ⋆[D.host.E] ↥W →ₗ[D.host.E] D.host.E := (VS D).hT.domRestrict₁₂ W W
  have hWs : hW.IsSymm := (VS D).herm.domRestrict W
  have hWp : ∀ x : ↥W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (hW x x) := fun x hx =>
    hpos x.1 x.2 (fun h => hx (Subtype.ext h))
  obtain ⟨s, hslat, hs⟩ := GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale hW hWs hWp d c hd hc
  let ι : ↥W →ₗ[𝓞 D.host.E] (VS D).V := W.subtype.restrictScalars (𝓞 D.host.E)
  let Mof : Submodule (𝓞 D.host.E) ↥W → LV D := fun L => A ⊔ L.map ι
  let Sset : Set (LV D) :=
    ⋃ L ∈ s, {Λ' | A.FG ∧ L.FG ∧ Mof L ≤ Λ' ∧ ∀ x ∈ Λ', (N : D.host.E) • x ∈ Mof L}
  have hfin : Sset.Finite := by
    refine Set.Finite.biUnion s.finite_toSet fun L _ => ?_
    by_cases hA : A.FG
    · by_cases hL : L.FG
      · refine (GlobalTheory.T.finite_lattices_between_of_smul_le' (Mof L) (hA.sup (hL.map ι)) N hN).subset ?_
        rintro Λ' ⟨-, -, h1, h2⟩
        exact ⟨h1, h2⟩
      · exact Set.finite_empty.subset (by rintro Λ' ⟨-, h, -⟩; exact absurd h hL)
    · exact Set.finite_empty.subset (by rintro Λ' ⟨h, -⟩; exact absurd h hA)
  refine ⟨hfin.toFinset, fun Λ hΛ hAΛ hNΛ hdΛ hcΛ => ?_⟩
  set L' : Submodule (𝓞 D.host.E) ↥W := Λ.comap ι with hL'
  have hL'lat : Submodule.IsLattice D.host.E L' := GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers Λ hΛ W
  have hsc : ∀ x ∈ L', ∀ y ∈ L', (d : D.host.E) * hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
    fun x hx y hy => hdΛ x.1 hx y.1 hy
  have hdu : ∀ y : ↥W, (∀ x ∈ L', hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) →
      (c : D.host.E) • y ∈ L' := by
    intro y hy
    show (c : D.host.E) • (y : (VS D).V) ∈ Λ
    exact hcΛ y.1 y.2 (fun x hx => hy ⟨x, hx.2⟩ hx.1)
  obtain ⟨M₀, hM₀s, g, hg, hgM⟩ := hs L' hL'lat hsc hdu
  have hgiso : ∀ x y : ↥W, (VS D).hT (g x : (VS D).V) (g y : (VS D).V) = (VS D).hT (x : (VS D).V) (y : (VS D).V) :=
    fun x y => hg x y
  obtain ⟨γ, hγi, hγU, hγW⟩ := GlobalTheory.T.exists_isometry_extend_orthogonal_by_identity (VS D) U hcompl g hgiso
  have hγH : γ ∈ H0 F F' :=
    ⟨hγi, fun a => hγU _ (Submodule.mem_sup_left (frame_mem_Xplus F a)),
      fun a => hγU _ (Submodule.mem_sup_right (frame_mem_Xplus F' a))⟩
  have hmem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ ↔ γ x ∈ Λ := fun x => by
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; rfl
  have hAsub : ∀ a ∈ A, a ∈ Λ ∧ a ∈ U := fun a ha => by
    rw [← hAΛ] at ha; exact ⟨ha.1, ha.2⟩
  refine ⟨Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ, ?_, γ, hγH, by simpa using Formalism.HermitianLatticesTheory.genusBasic_gmap_inv γ⁻¹ Λ⟩
  rw [Set.Finite.mem_toFinset]
  have hAfg : A.FG := by
    rw [← hAΛ]; exact fg_of_le_fg hΛ.fg inf_le_left
  have hWsymm : ∀ w (hw : w ∈ W) (hwΛ : w ∈ Λ), γ.symm w ∈ M₀.map ι := by
    intro w hw hwΛ
    have h1 : (⟨w, hw⟩ : ↥W) ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by rw [hgM]; exact hwΛ
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearEquiv.eq_symm_apply]
    show γ ((g.symm ⟨w, hw⟩ : ↥W) : (VS D).V) = w
    rw [hγW, LinearEquiv.apply_symm_apply]
  refine Set.mem_biUnion hM₀s ⟨hAfg, (hslat M₀ hM₀s).fg, ?_, ?_⟩
  · refine sup_le (fun a ha => ?_) ?_
    · rw [hmem, hγU a (hAsub a ha).2]; exact (hAsub a ha).1
    · rintro _ ⟨m, hm, rfl⟩
      rw [hmem]
      show γ ((m : ↥W) : (VS D).V) ∈ Λ
      rw [hγW]
      have h1 : g m ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by
        rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]; exact hm
      rw [hgM] at h1
      exact h1
  · intro x hx
    rw [hmem] at hx
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp (hNΛ _ hx)
    have hx' : (N : D.host.E) • x = γ.symm u + γ.symm w := by
      rw [← map_add (f := _), huw, map_smul, LinearEquiv.symm_apply_apply]
    have hu' : γ.symm u = u := by
      rw [LinearEquiv.symm_apply_eq]; exact (hγU u hu.2).symm
    rw [hx', hu']
    refine Submodule.add_mem_sup ?_ (hWsymm w hw.2 hw.1)
    rw [← hAΛ]; exact hu

end GlobalTheory.LatClassFin
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.glued_unimodular_lattice_iff_local_completions : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  first | exact @GlobalTheory.GenMass.GlueLoc.glue_iff_local | exact GlobalTheory.GenMass.GlueLoc.glue_iff_local | (intros; apply GlobalTheory.GenMass.GlueLoc.glue_iff_local <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedReferenceFrame_congruent_unitriangular : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam)) := by
  first | exact @GlobalTheory.HL.LocCong.loc_cong | exact GlobalTheory.HL.LocCong.loc_cong | (intros; apply GlobalTheory.HL.LocCong.loc_cong <;> assumption)
end
