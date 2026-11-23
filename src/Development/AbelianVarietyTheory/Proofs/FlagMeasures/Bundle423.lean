module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle292
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodOfHpEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle381
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle421
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle417
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle420
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedCountGluedLatticesEqMassMulLocal
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle418
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizer
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle419
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AmpLoc



theorem global_amp_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  intro D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv R S1 Om d hout hOm hover Q
  have hT : G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) :=
    (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv).1
  have hW := fun p => GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
    D.R.rS D.R.k (FP p) (G.S p) (c.c p)
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places _ _ _ G hk _ _ hT
  have hOmS : G.Om ⊆ (S1 : Set (PlF D)) := by
    intro p hp
    by_contra hn
    exact hp ((hW p).2.2.2.1 (hout p hn))
  obtain ⟨κ, hκ, hdec⟩ := GlobalTheory.T.amplitude_expansion_over_finite_places _ _ _ G hk _ ⟨_, hT⟩ S1 hOmS
  rw [hdec Q, norm_mul, hκ, one_mul]

  have hloc : ∀ p : {p // p ∈ S1},
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1)
          (fun Λ => ¬ (G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1) Λ) =
        LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) ∧
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1) ((G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1)) =
        LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t) := by
    intro p
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).lf
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).char0
    have hu : (Function.update (G.datOf (c.lat ρ t₀.lam)) p.1 ((c.c p.1).dat (d p))) p.1 = (c.c p.1).dat (d p) :=
      Function.update_self _ _ _
    obtain ⟨h, hh, hδ⟩ := GlobalTheory.T.localDatum_of_term_in_movedLattice_orbit D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv p.1 (d p)
      (hover p) _ hu
    rw [hu] at hδ
    obtain ⟨e1, e2⟩ := (hW p.1).2.2.2.2 (R p.1) (d p)
    rw [e1, e2, ← hδ]
    constructor
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq hb
        exact hq ((GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.1 hb)
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact not_congr ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq
        exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.2 hq
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
  have hzero : ∀ p ∈ S1, (FP p).PrimeTo →
      (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ) = 0 := by
    intro p _ hp
    have hBB := (hgood p (fun hm => hm ((hW p).2.2.2.1 hp))).1
    unfold Frames.amp
    calc
      _ = ∑' _ : MulAction.orbitRel.Quotient (G.S p).St (Submodule _ (G.S p).V), (0 : ℂ) := by
        apply tsum_congr
        intro o
        rw [if_neg]
        rintro ⟨ht, hb⟩
        exact hb (hBB _ _ ht)
      _ = 0 := tsum_zero
  congr 1
  symm
  let emb : {p // p ∈ S1} ↪ PlF D := Function.Embedding.subtype _
  let embF : Finset {p // p ∈ S1} ↪ Finset (PlF D) := ⟨fun A => A.map emb, Finset.map_injective emb⟩
  calc _ = ∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p ∈ S1,
          (if p ∈ A.map emb then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [← Finset.prod_coe_sort S1]
        refine Finset.prod_congr rfl fun p _ => ?_
        have hm : (p.1 ∈ A.map emb) ↔ p ∈ A := Finset.mem_map' emb
        by_cases hp : p ∈ A
        · rw [if_pos hp, if_pos (hm.2 hp), (hloc p).1]
        · rw [if_neg hp, if_neg (fun h => hp (hm.1 h)), (hloc p).2]
    _ = ∑ B ∈ (Om.powerset.filter (fun A => Q A.Nonempty)).map embF, ∏ p ∈ S1,
          (if p ∈ B then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) :=
        by rw [Finset.sum_map]; rfl
    _ = _ := by
        apply Finset.sum_subset
        · intro B hB
          obtain ⟨A, hA, rfl⟩ := Finset.mem_map.1 hB
          rw [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
          refine ⟨fun x hx => ?_, ?_⟩
          · obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
            exact y.2
          · show Q (A.map emb).Nonempty
            rw [Finset.map_nonempty]
            exact hA.2
        · intro B hB hn
          rw [Finset.mem_filter, Finset.mem_powerset] at hB
          by_cases hall : ∀ p ∈ B, ¬ (FP p).PrimeTo
          · exfalso
            apply hn
            have e : (B.subtype (· ∈ S1)).map emb = B := Finset.subtype_map_of_mem hB.1
            refine Finset.mem_map.2 ⟨B.subtype (· ∈ S1), ?_, e⟩
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨fun q hq => (hOm q).2 (hall q.1 (Finset.mem_subtype.1 hq)), ?_⟩
            rw [← Finset.map_nonempty (f := emb), e]
            exact hB.2
          · push_neg at hall
            obtain ⟨p, hpB, hp⟩ := hall
            exact Finset.prod_eq_zero (hB.1 hpB) (by rw [if_pos hpB]; exact hzero p (hB.1 hpB) hp)

end GlobalTheory.HL.AmpLoc
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocApprox

theorem iota_gS_typed {D : D7} (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w := by
  obtain ⟨sg, hsg, hq, -⟩ := Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.typed_data Z p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]

end GlobalTheory.LocApprox

namespace GlobalTheory.LocApprox



theorem approx : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), ∀ x ∈ lattice₂ D Z.M p Λ, x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) → ∃ l ∈ Lrep Λ F, x - baseChange₂ D p l ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) := by
  intro D Z p hc Λ hΛ T F x hx hxp
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  rcases hs : (Z.M p).split with _ | g
  · refine ⟨0, zero_mem _, ?_⟩
    have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = 1 := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    rw [ht, map_one, map_zero, sub_zero]
    exact Submodule.subset_span ⟨x, hx, one_smul _ _⟩
  · have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = (g.q : (D.s.atP p).Fp) := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    obtain ⟨w, hw, he⟩ := iota_gS_typed Z p g hs
    rw [ht]
    have hspan := GlobalTheory.LocExt.perp_le Z p F hxp
    have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) (Xsp F)) hΛ.fg
    have hxL : x ∈ lattice₂ D Z.M p (Lrep Λ F) := by
      have : x ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) (Xsp F))) : Set (Vp D p)) := by
        rw [hsat]; exact ⟨hx, hspan⟩
      exact this
    clear hx hxp hspan hsat
    induction hxL using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact ⟨l, hl, by rw [sub_self]; exact zero_mem _⟩
    | zero => exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ ihu ihv =>
      obtain ⟨l, hl, h⟩ := ihu
      obtain ⟨l', hl', h'⟩ := ihv
      refine ⟨l + l', add_mem hl hl', ?_⟩
      rw [map_add (f := _), show u + v - (baseChange₂ D p l + baseChange₂ D p l') = (u - baseChange₂ D p l) + (v - baseChange₂ D p l') by abel]
      exact add_mem h h'
    | smul o v _ ih =>
      obtain ⟨l, hl, h⟩ := ih
      have ho : (o : (D.s.atP p).Ep) ∈ (D.s.atP p).O := hO ▸ o.2
      obtain ⟨a, o', ho', hco⟩ := hc _ ho
      refine ⟨a • l, Submodule.smul_mem _ a hl, ?_⟩
      have hbl : baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨l, hl.1, rfl⟩
      have e1 : baseChange₂ D p (a • l) = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [← baseChange_smul₂]; congr 1; exact (algebraMap_smul D.host.E a l).symm
      have key : ∀ (oo ia ig th : (D.s.atP p).Ep) (vv b : Vp D p), oo = ia + ig * o' → ig = th * w →
          oo • vv - ia • b = oo • (vv - b) + th • ((w * o') • b) := by
        intro oo ia ig th vv b h1 h2
        subst h1 h2
        simp only [smul_sub, add_smul, smul_smul, ← mul_assoc]
        abel
      have hov : o • v = (o : (D.s.atP p).Ep) • v := rfl
      have hob : (o : (D.s.atP p).Ep) • (v - baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.smul_mem _ o h
      have hwo : w * o' ∈ (Z.M p).L.O := hO ▸ mul_mem hw ho'
      have k1 := key (o : (D.s.atP p).Ep) _ _ _ v (baseChange₂ D p l) hco he
      have h3 : (w * o') • baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := (lattice₂ D Z.M p Λ).smul_mem ⟨_, hwo⟩ hbl
      have h4 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • ((w * o') • baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.subset_span ⟨_, h3, rfl⟩
      have h5 : (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) := by
        rw [k1]; exact add_mem hob h4
      have h6 : o • v - baseChange₂ D p (a • l) = (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [hov, e1]
      rw [h6]
      exact h5

end GlobalTheory.LocApprox
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

noncomputable section

open GlobalTheory.LabPin

namespace GlobalTheory.DepthZeroSer

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rt_rt' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (h h' : GAf L n) (f : GAf L n → ℂ) :
    NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext x; simp [NG.rt, mul_assoc]

theorem rt_one' {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (f : GAf L n → ℂ) :
    NG.rt L n 1 f = f := by
  funext x; simp [NG.rt]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : GlobalTheory.SmGL.IrrRep G) : Nontrivial τ.V := by
  haveI := τ.irr
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  ext x
  simp [Subsingleton.elim x 0]

theorem serFix_of_locS {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (j : ℚ_[g] ≃+* s.w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s τ)
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  classical
  obtain ⟨i, T, hi, -, hT, hTS, hTeq⟩ := hloc
  set ρ' := τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) j.toRingHom) with hρ'
  set θ : s.v.adicCompletion (maximalRealSubfield L) ≃+* ℚ_[g] := i.trans j.symm with hθdef
  have hθ : ∀ z, Valued.v z < 1 ↔ ‖θ z‖ < 1 := fun z => GlobalTheory.T.valuation_lt_one_iff_norm_lt_one_padic_cmCompletion L s g i j hi hj z
  have hτθ : ∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom A) = ρ' (Matrix.GeneralLinearGroup.map θ.toRingHom A) := by
    intro A
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply]
    congr 1
    ext a b
    simp [θ]
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  haveI := nontrivial_of_irr τ
  intro ℓ hℓ φ hφS hφfix
  let N : {y : GAf L n // TrivOutside {s.v}ᶜ y} → Submodule ℂ (GAf L n → ℂ) :=
    fun y => LinearMap.range ((NG.rt L n y.1).comp T)
  have hspan := GlobalTheory.T.finiteType_eq_iSup_splitTrivial_translates_local L n π s τ.V T hT hTS (fun x hx a => ⟨_, (hTeq x hx a).symm⟩)
  have hNst : ∀ y x, TrivOutside {s.v} x → ∀ f ∈ N y, NG.rt L n x f ∈ N y := by
    rintro y x hx f ⟨b, rfl⟩
    refine ⟨τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) b, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hTeq x hx b, rt_rt', rt_rt', (hI.2.1 x y.1 hx y.2).eq]
  have hsupst : ∀ (J : Finset _) x, TrivOutside {s.v} x → ∀ f ∈ ⨆ j ∈ J, N j, NG.rt L n x f ∈ ⨆ j ∈ J, N j := by
    intro J x hx f hf
    have : (⨆ j ∈ J, N j) ≤ (⨆ j ∈ J, N j).comap (NG.rt L n x) := by
      refine iSup₂_le fun j hj => ?_
      intro f hf
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hNst j x hx f hf))
    exact this hf
  have hdich : ∀ y (J : Finset _), Disjoint (N y) (⨆ j ∈ J, N j) ∨ N y ≤ ⨆ j ∈ J, N j :=
    fun y J => GlobalTheory.T.splitTrivialTranslate_localComponent_disjoint_or_le L n s τ i T hT hTeq y.1 y.2 _ (hsupst J)
  have hφ : φ ∈ ⨆ y, N y := hspan ▸ hφS
  obtain ⟨F, hF⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  obtain ⟨J, -, hJsup, hJuniq⟩ := GlobalTheory.T.exists_independent_subfamily_same_iSup _ _ N hdich F
  rw [← hJsup] at hF
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum N φ).1 hF
  choose c hc using fun y => (μ y).2
  have hφsum : φ = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
    rw [← hμ]; exact Finset.sum_congr rfl fun y _ => (hc y).symm
  have hinj : ∀ (y : {y : GAf L n // TrivOutside {s.v}ᶜ y}), Function.Injective (fun b => NG.rt L n y.1 (T b)) := by
    intro y b b' h
    apply hT
    have := congrArg (NG.rt L n y.1⁻¹) h
    simpa [rt_rt', rt_one'] using this
  have hfix : ∀ y ∈ J, c y ∈ GlobalTheory.GLp.fixK1 ρ' := by
    intro y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro kk
    obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n kk))
    have hlift : IsLift s x (1 : GL (Fin n) (ZMod g)) :=
      ⟨hx1, fun p q => by
        have H := GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt _ s.v g n θ (fun z => (hθ z).2) (kk : GL (Fin n) ℤ_[g]) kk.2 p q
        rw [hx2]
        exact H⟩
    have hx := hφfix x hlift
    have hθx : Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n x) = GlobalTheory.GLp.inc g n kk := by
      rw [hx2]; ext; simp

    rw [hφsum, map_sum] at hx
    have hx' : ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.inc g n kk) (c y))) = ∑ y ∈ J, NG.rt L n y.1 (T (c y)) := by
      rw [← hx]; refine Finset.sum_congr rfl fun y _ => ?_
      rw [← hθx, ← hτθ, hTeq x hx1, rt_rt', rt_rt', (hI.2.1 x y.1 hx1 y.2).eq]
    exact hinj y (hJuniq _ _ (fun y _ => ⟨_, rfl⟩) (fun y _ => ⟨_, rfl⟩) hx' y hy)
  have hfix' : ∀ y ∈ J, ∀ kk ∈ (GlobalTheory.GLp.red g n).ker, ρ' (GlobalTheory.GLp.inc g n kk) (c y) = c y := by
    intro y hy kk hkk
    have := hfix y hy
    simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at this
    exact this ⟨kk, hkk⟩
  have hℓ' : ∀ γ, ∃ kk ∈ (GlobalTheory.GLp.red g n).ker,
      Matrix.GeneralLinearGroup.map θ.toRingHom (s.loc n (ℓ γ)) = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n kk :=
    fun γ => GlobalTheory.T.exists_padic_lift_mul_principalCongruence_of_reduction _ s.v g n θ (fun z => (hθ z).1) _ γ (hℓ γ).2
  choose kk hkk hkkeq using hℓ'
  have hterm : ∀ γ, NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (ρ' (GlobalTheory.GLp.lift g n γ) (c y))) := by
    intro γ

    rw [hφsum, map_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [rt_rt', (hI.2.1 (ℓ γ) y.1 (hℓ γ).1 y.2).eq, ← rt_rt', ← hTeq _ (hℓ γ).1, hτθ, hkkeq, map_mul,
      Module.End.mul_apply, hfix' y hy _ (hkk γ)]
  rw [finsum_eq_sum_of_fintype]
  calc ∑ γ, a.coeff γ • NG.rt L n (ℓ γ) φ = ∑ y ∈ J, NG.rt L n y.1 (T (GlobalTheory.GLp.actK ρ' a (c y))) := by

        simp only [hterm, Finset.smul_sum, GlobalTheory.GLp.actK, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_smul]
        exact Finset.sum_comm
    _ = φ := by
        rw [hφsum]
        exact Finset.sum_congr rfl fun y hy => by rw [ha _ (hfix y hy)]

theorem serFix_of_locS' {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime]
    (π : NG.FinTyp L n) (s : SplitPlace L) {w : HeightOneSpectrum (𝓞 L)} (h : s.w = w)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion L)))
    (j : ℚ_[g] ≃+* w.adicCompletion L) (hj : Continuous j) (a : MonoidAlgebra ℂ (GL (Fin n) (ZMod g)))
    (hloc : GlobalTheory.HeightCounting.IsLocS π.S s (h ▸ τ))
    (ha : ∀ y ∈ GlobalTheory.GLp.fixK1 (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)),
      GlobalTheory.GLp.actK (τ.ρ.comp (Matrix.GeneralLinearGroup.map j.toRingHom)) a y = y) :
    SerFix π s a := by
  subst h
  exact serFix_of_locS π s τ j hj a hloc ha

theorem serFix_of_comp : ∀ (D : D7) (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D), IsComp I rep cp → ∀ σ k v (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), (∀ y ∈ fixK1 (cp σ k v).ρ, actK (cp σ k v).ρ a y = y) → ∀ s : SplitPlace D.host.E, s.w = D.naut.plGw k v → GlobalTheory.LabPin.SerFix (rep σ) s a := by
  intro D I rep cp hc σ k v a ha s hs
  obtain ⟨s₀, h₀, τ, hloc, hcp⟩ := hc σ k v
  obtain rfl : s = s₀ := GlobalTheory.T.cmSplitPlace_eq_of_prime_eq _ s s₀ (hs.trans h₀.symm)
  rw [hcp] at ha
  exact serFix_of_locS' (rep σ) s h₀ τ (I.i k v) (I.cont k v) a hloc ha

end GlobalTheory.DepthZeroSer

end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weighted_count_glued_lattices_eq_mass_mul_local : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → TotPos (Gval F F') → ∀ (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → MassLaw F F' P d0 V → ∀ s : Finset (LV D), Glue G G' s → ENNReal.ofReal (glueSum G G' s) = ENNReal.ofReal V * ∏ p ∈ P, locSum G G' p (R p) (d0 p) := by
  first | exact @GlobalTheory.GlueCount.glue_count | exact GlobalTheory.GlueCount.glue_count | (intros; apply GlobalTheory.GlueCount.glue_count <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

theorem rowMainEqP_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBGP) : GlobalTheory.SnPos.RowMainEqP :=
  GlobalTheory.T.equalWordGenericBound_of_cutBound_positive hCh Formalism.L2.SG.Pf.MainEqCut.meanAmplitudeGeneric_holds
    (GlobalTheory.T.generic_height_bound_of_local_estimates Formalism.L2.SG.NGCut.sizes_of_hypotheses hC hN hP (stepHeightG_of_normOne hO)
      (GlobalTheory.T.analyticGenericBound_of_choiceStep_positive hTi hB (GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps hE hV hL hT)))

end GlobalTheory.SnPos
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbIntG.orbInt_integrable | exact GlobalTheory.CellOrbIntG.orbInt_integrable | (intros; apply GlobalTheory.CellOrbIntG.orbInt_integrable <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  first | exact @GlobalTheory.Unfold.FixFin.conj_aut_finite | exact GlobalTheory.Unfold.FixFin.conj_aut_finite | (intros; apply GlobalTheory.Unfold.FixFin.conj_aut_finite <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  first
  | exact GlobalTheory.DblCos.finite_double_cosets
  | intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀
    exact GlobalTheory.DblCos.finite_double_cosets D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀.toIsLattice
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.genericScalarClassTerms_formFamily : GlobalTheory.SnFam.FamGen := by
  first | exact @GlobalTheory.SnFamGenAll.famGen | exact GlobalTheory.SnFamGenAll.famGen | (intros; apply GlobalTheory.SnFamGenAll.famGen <;> assumption)
end
