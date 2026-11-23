module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle360
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle337
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle349
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameTermCountSublatticeBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle389
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle390
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle324
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MovedTermLoc

theorem uni_mul {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem uni_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (A : Matrix (Fin n) (Fin n) R)
    (hA : Uni A) : Uni (A.map f) :=
  ⟨fun a b h => by simp [Matrix.map_apply, hA.1 a b h], fun a => by simp [Matrix.map_apply, hA.2 a]⟩

theorem map_inv_of_det {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ f.map_zero f.map_one]

theorem chg_scaled {D : D7} (Z : LocDat D) (p : PlF D) (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hg : Chg f A g) :
    Chg (scaled Z p f) (fun a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b))
      (scaled Z p g) := by
  intro b
  simp only [scaled]
  rw [hg b, Formalism.L2.SG.Pf.BBTie.bt_bc_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  have h := Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)
  linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h



theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → ∀ (N N' : G.GLV), (∀ b, N (G.f b) = ∑ a, U a b • G.f a) → (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) → ∀ (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' → ∃ (t : Loc.Term (Vp D p) (Y.M p) D.R.rS) (d : LocNG.Datum (FP p)), LocNG.IsTermOver (FP p) d t ∧ (c.c p).lat t.abelian₂ = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) ∧ (∀ b, (c.c p).e (t.f b) = m ((G.S p).f b)) ∧ ∀ b, (c.c p).e (t.f' b) = m' ((G.S p).f' b) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv p ξ hξ N N' hN hN' m m' hm hm'
  have hR : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  have hPD : Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' t₀.frame := t₀.rep.2.2.2.2
  have hGt : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := fun h0 => hG ((GlobalTheory.T.frame_pair_gram_invariant_unchanged_isometry D _ _ _ _ ρ U U' hMv).symm.trans h0)
  obtain ⟨g, hgE, hgU⟩ := GlobalTheory.T.exists_unitary_extension_rational_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hMv.1
  obtain ⟨hT0, -⟩ := GlobalTheory.T.unsignedLocalTerm_row_lattice_isTerm D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hR t₀.frame hPD hGt p
  set ξ0 := admXi D t₀.lam (lf D (X.Fu u)) t₀.frame with hξ0
  set t0 := locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u') with ht0
  have hTg := GlobalTheory.T.isTerm_unitary_move_localTerm (Y.M p) (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS g t0 hgU hT0

  have hUu : Uni U := ⟨fun a b h => (hMv.2.1 a b).1 h, fun a => (hMv.2.1 a a).2 rfl⟩
  have hU'u : Uni U' := ⟨fun a b h => (hMv.2.2.1 a b).1 h, fun a => (hMv.2.2.1 a a).2 rfl⟩
  have hξ0u : Uni ξ0 := admissibility_witness_unitriangular t₀.lam (lf D (X.Fu u)) t₀.frame
  have hξ0i : Uni ξ0⁻¹ := inv_unitri _ hξ0u.1 hξ0u.2
  have hξu : Uni ξ := ⟨hξ.1, hξ.2.1⟩
  have hξi : Uni ξ⁻¹ := inv_unitri _ hξu.1 hξu.2
  have hξ0w : AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ0 := by
    have he : admXi D t₀.lam (lf D (X.Fu u)) t₀.frame = hPD.2.1.choose := by
      unfold admXi
      exact dite_eq_left hPD.2.1
    rw [hξ0, he]
    exact hPD.2.1.choose_spec
  set alg := algebraMap (𝓞 D.host.E) D.host.E with halg
  set B0 := U' * (ξ0⁻¹).map alg with hB0
  set B1 := U' * (ξ.map alg)⁻¹ with hB1
  set C := (ξ0 * ξ⁻¹).map alg with hC
  have hB0u : Uni B0 := uni_mul _ _ hU'u (uni_map _ _ hξ0i)
  have hCu : Uni C := uni_map _ _ (uni_mul _ _ hξ0u hξi)
  have hBC : B0 * C = B1 := by
    rw [hB0, hB1, hC, Matrix.map_mul, ← map_inv_of_det alg ξ (Formalism.L2.SG.Pf.BBTie.bt_unitri_det _ hξu.1 hξu.2),
      Matrix.mul_assoc, ← Matrix.mul_assoc ((ξ0⁻¹).map alg), ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (Formalism.L2.SG.Pf.BBTie.bt_unitri_det _ hξ0u.1 hξ0u.2),
      Matrix.map_one _ alg.map_zero alg.map_one, Matrix.one_mul]

  have hf : ∀ b, (move g t0).f b = scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, U a b • frame F00 a) b := by
    intro b
    show g (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p (frame (lf D (X.Fu u)) b)) = frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p _
    rw [map_smul, hgE]
    exact congrArg (fun x => frFac _ p b • baseChange₂ D p x) (hMv.2.2.2.1 b)
  have hf' : ∀ b, (move g t0).f' b = scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, B0 a b • frame F'0 a) b := by
    intro b
    show g (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p (_root_.Formalism.MainNotions.S.Lat.frameAct (frame t₀.frame) ξ0⁻¹ b)) = frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p _
    rw [map_smul, hgE]
    congr 2

    simp only [_root_.Formalism.MainNotions.S.Lat.frameAct, map_sum, map_smul, hMv.2.2.2.2, Finset.smul_sum, smul_smul, hB0, Matrix.mul_apply,
    Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.map_apply, mul_comm]
  have hTri1 : Tri (D.s.atP p).Ep (FP p).A.f (move g t0).f := by
    obtain ⟨Ap, hAp, -⟩ := tri_scaled D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) (frame F00) (fun b => ∑ a, U a b • frame F00 a) U hUu (fun b => rfl)
    rw [(hAt p).1.1]
    exact ⟨Ap p, (hAp p).1, fun b => by rw [hf b]; exact (hAp p).2 b⟩
  have hTri2 : Tri (D.s.atP p).Ep (FP p).B.f (move g t0).f' := by
    obtain ⟨Ap, hAp, -⟩ := tri_scaled D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) (frame F'0) (fun b => ∑ a, B0 a b • frame F'0 a) B0 hB0u (fun b => rfl)
    rw [(hAt p).1.2.1]
    exact ⟨Ap p, (hAp p).1, fun b => by rw [hf' b]; exact (hAp p).2 b⟩
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS (FP p) (move g t0) hTg
    (hAt p).1.2.2.1.symm (hAt p).1.2.2.2.symm hTri1 hTri2

  set A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    fun a b => Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b * (D.s.atP p).ιE (C a b) with hA'
  set tf' := scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, B1 a b • frame F'0 a) with htf'
  have hChg1 : Chg (move g t0).f (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (move g t0).f := by
    intro b
    simp [Matrix.one_apply]
  have hChg2 : Chg (move g t0).f' A' tf' := by
    have hc : Chg (fun b => ∑ a, B0 a b • frame F'0 a) C (fun b => ∑ a, B1 a b • frame F'0 a) := by
      intro b
      rw [← hBC]
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [mul_comm]
    have h := chg_scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p _ _ C hc
    intro b
    refine (h b).trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hf' a]
  have hfin : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Ranks.r, Ranks.rS]
    omega
  have hA'u : Uni A' := by
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · simp [hA', hCu.1 a b h]
    · show Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a * (D.s.atP p).ιE (C a a) = 1
      rw [hCu.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p a)]
  have hcong := GlobalTheory.T.admissibility_witnesses_congr_mod_theta_local D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam t₀.frame hR hPD ξ0 ξ hξ0w hξ p
  have hint : ∀ a b, (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (Y.M p).L.O ∧
      A' a b ∈ (Y.M p).L.O ∧ (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b - A' a b ∈
        Submodule.span (Y.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Y.M p))} := by
    intro a b
    rcases lt_or_ge b a with h | h
    · have e0 : A' a b = 0 := by simp [hA', hCu.1 a b h]
      rw [e0, Matrix.one_apply_ne (ne_of_lt h).symm, sub_zero]
      exact ⟨Subring.zero_mem _, Subring.zero_mem _, Submodule.zero_mem _⟩
    · obtain ⟨k, hkO, hkb⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_step (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (Formalism.L2.SG.Pf.locDiffC_holds D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) a b h
      have e1 : A' a b = k * (D.s.atP p).ιE (C a b) := by
        show Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b * (D.s.atP p).ιE (C a b) = _
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p a), one_mul]
      have hCO : (D.s.atP p).ιE (C a b) ∈ (Y.M p).L.O := Formalism.L2.SG.Pf.BBTie.bt_iota_int (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ((ξ0 * ξ⁻¹) a b)
      have hAO : A' a b ∈ (Y.M p).L.O := by rw [e1]; exact Subring.mul_mem _ hkO hCO
      refine ⟨?_, hAO, ?_⟩
      · by_cases hab : a = b
        · subst hab; rw [Matrix.one_apply_eq]; exact Subring.one_mem _
        · rw [Matrix.one_apply_ne hab]; exact Subring.zero_mem _
      · rcases eq_or_lt_of_le h with hab | hab
        · subst hab
          rw [hA'u.2 a, Matrix.one_apply_eq, sub_self]; exact Submodule.zero_mem _
        · have hc := hcong a b
          rw [Matrix.one_apply_ne (ne_of_lt hab), sub_zero] at hc
          rw [Matrix.one_apply_ne (ne_of_lt hab), zero_sub, e1, ← neg_mul]
          have := Submodule.smul_mem _ (⟨-k, Subring.neg_mem _ hkO⟩ : (Y.M p).L.O) hc
          exact this
  have hT := GlobalTheory.T.hermitian_frame_witness_integral_change (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) hfin (hAt p).2 d (move g t0) hd
    1 A' (move g t0).f tf' (⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩)
    hA'u hint hChg1 hChg2
  have hlat := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).2.2.2.2.1 ρ hMv.1 p g
    t₀.lam hgE
  have hfc := GlobalTheory.T.scaled_unitriangular_change_eq_local_image D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G c p N m hm U
  have hfc' := GlobalTheory.T.scaled_unitriangular_change_eq_local_image D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G c p N' m' hm' B1
  refine ⟨⟨(move g t0).abelian₂, (move g t0).f, tf', (move g t0).T, (move g t0).T'⟩, d, hT, hlat.symm, fun b => ?_,
    fun b => ?_⟩
  · show (c.c p).e ((move g t0).f b) = _
    rw [hf b]; exact hfc.1 hN b
  · exact hfc'.2 hN' b

end GlobalTheory.HL.MovedTermLoc
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (D.sp.Y 0) D.R.rS T) (F' F'0 : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 → IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  first | exact @GlobalTheory.LocOver.witt_frames_at_point | exact GlobalTheory.LocOver.witt_frames_at_point | (intros; apply GlobalTheory.LocOver.witt_frames_at_point <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.baseData_of_global_term : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ w : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ∃ (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 F'1 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : ∀ p, LocNG.Datum (FP p)), (∃ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ a, frame F00 a = n (frame (lf D F0) a)) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w ∧ Gval F00 F'0 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D F0) F'1)) w ∧ (∀ p, AtBase Z p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Z.M p)) ∧ LocNG.IsTermOver (FP p) (d0 p) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' = scaled Z p (frame F'1)) ∧ {p : PlF D | ¬ ((FP p).PrimeTo ∧ LocNG.IsTermOver (FP p) (d0 p) ⟨lattice₂ D Z.M p Λ, scaled Z p (frame F00), scaled Z p (frame F'0), ((Tu D u : ℕ) : (D.s.atP p).Fp), ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩)}.Finite := by
  first | exact @GlobalTheory.BaseTerm.base_data_of_global_term | exact GlobalTheory.BaseTerm.base_data_of_global_term | (intros; apply GlobalTheory.BaseTerm.base_data_of_global_term <;> assumption)
end

section

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopAct

variable {n m : ℕ}

def IsMatOn (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ b, g *ᵥ f b = ∑ c, M c b • f c

theorem isMatOn_mul {g h : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g f M₁) (hh : IsMatOn h f M₂) : IsMatOn (g * h) f (M₁ * M₂) := by
  intro b
  rw [← Matrix.mulVec_mulVec, hh b, Matrix.mulVec_sum]
  have e : ∀ c, g *ᵥ (M₂ c b • f c) = ∑ d, (M₂ c b * M₁ d c) • f d := by
    intro c
    rw [Matrix.mulVec_smul, hg c, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem isMatOn_unique {g : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hf : LinearIndependent ℂ f) (hM : IsMatOn g f M₁) (hN : IsMatOn g f M₂) : M₁ = M₂ := by
  ext c b
  have h : ∑ d, (M₁ d b - M₂ d b) • f d = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← hM b, ← hN b, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hf _ h c)

theorem isMatOn_conj {g P Pi : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g (fun j => P *ᵥ f j) A) (hP : Pi * P = 1) : IsMatOn (Pi * g * P) f A := by
  intro b
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg b, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]

variable {N : ℕ}

theorem stabU_mul {Z a b : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z)
    (hb : b ∈ GlobalTheory.LoopV.stabU Z) : a * b ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul ha.1 hb.1, ?_⟩
  have e : Z * (a * b) * Z⁻¹ = (Z * a * Z⁻¹) * (Z * b * Z⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hZ]
  rw [e]
  exact Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_mul ha.2 hb.2

theorem stabU_inv {Z a : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z) :
    a⁻¹ ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨(Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1).1, ?_⟩
  have hai := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1
  have e : Z * a⁻¹ * Z⁻¹ = (Z * a * Z⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZ, Matrix.mul_assoc]
  rw [e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv ha.2).1

theorem stabU_map_eq_ofRoots {K : Type} [Field K] (ψ : K →+* ℂ) (p : Point K N) (x : Matrix (Fin N) (Fin N) ℂ)
    (hx : x ∈ GlobalTheory.LoopV.stabU ((ptMat p).map ψ)) :
    x = GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (fun q => x q.1.1 q.1.2) := by
  obtain ⟨σ, d, hd, hw⟩ := GlobalTheory.LoopV.Cell.ptMat_monomial p
  have hd' : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero ψ).2 (hd i)
  have hw' : ∀ i j, (ptMat p).map ψ i j = if j = σ i then ψ (d i) else 0 := by
    intro i j; rw [Matrix.map_apply, hw]; split_ifs <;> simp
  ext a b
  unfold GlobalTheory.LoopV.ofRoots
  by_cases hr : (a, b) ∈ GlobalTheory.LoopV.roots (ptMat p)
  · rw [dite_eq_left hr]
  · rw [dite_eq_right hr]
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [if_neg hab.ne]
      have hσ : σ.symm a < σ.symm b := by
        rw [GlobalTheory.LoopV.Cell.mono_roots hd hw] at hr
        push_neg at hr
        rcases (hr hab).lt_or_eq with h | h
        · exact h
        · exact absurd (σ.symm.injective h) hab.ne
      have h0 := (hx.2 (σ.symm a) (σ.symm b)).1 hσ
      rw [GlobalTheory.LoopV.Cell.mono_conj hd' hw'] at h0
      simp only [Equiv.apply_symm_apply, mul_eq_zero, inv_eq_zero, hd', false_or, or_false] at h0
      exact h0
    · rw [if_pos rfl]; exact (hx.1 a a).2 rfl
    · rw [if_neg hab.ne']; exact (hx.1 a b).1 hab

end GlobalTheory.LoopAct

end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frameTermCount_sublattice_bound : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntFr D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  first | exact @GlobalTheory.LoopC.FrCount.main | exact GlobalTheory.LoopC.FrCount.main | (intros; apply GlobalTheory.LoopC.FrCount.main <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.RatIsomReal

theorem realPts_eq_image : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (Γ : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
    (∀ n ∈ Γ, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) →
      GlobalTheory.DegVol.realPts (phiV C) Γ = trI C '' {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
        RatLink X x n ∧ y = x.1 ∧ n ∈ Γ} := by
  intro D X C Γ hΓ
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n (hΓ n hn)
    exact ⟨x.1, ⟨x, n, hx, rfl, hn⟩, GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)⟩
  · rintro ⟨_, ⟨x, n, hx, rfl, hn⟩, rfl⟩
    exact ⟨n, hn, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm.RatIsomReal
end
end

section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.l2SG_phiOf_eq_l2SG_wT_of_goodLoc : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  first | exact @GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | exact GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | (intros; apply GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported <;> assumption)
end

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.BaseFrame

theorem normal0_one (k r j : ℕ) (hj : j ≤ r) (h0 : j = 0) (z : Fin (2 * r + k + 1) → ℂ) :
    GlobalTheory.Amp.IsNormal0 k r hj (fun _ => 0) 1 z z 1 := by
  subst h0
  refine ⟨?_, by simp, by simp, monotone_const, fun a b _ => by simp, fun a ha => absurd ha (Nat.not_lt_zero _),
    fun a _ => by simp, ?_⟩
  · show (1 : Matrix _ _ ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  · refine ⟨monotone_const, ?_, fun a => a.elim0, fun a => a.elim0⟩
    simp [Matrix.det_fin_zero]

end GlobalTheory.TypeAsm.BaseFrame

open GlobalTheory.TypeAsm.BaseFrame in
theorem GlobalTheory.TypeAsm.baseFrame_real : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u → N.j = 0 → N.T = Tu D u → N.ist = X.fY →
      ∀ τ : D.what₂.Tau, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) (fun _ => 0)
        (phiV C τ) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) 1 := by
  intro D large₂ X u C hStd N hF hF' hj hT hist τ
  have hv : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := (GlobalTheory.TypeAsm.hostC D large₂ hStd).2.2.1
  rw [hv]
  have hFe : ∀ a : Fin D.R.rS, (F0 X u).e a.castSucc = X.eX a := by
    intro a
    show (lf D (X.Fu u)).fl.fvec a.castSucc = X.eX a
    rw [fv_cast]
    exact congrFun (X.Fu_e u) a
  have hFz : (F0 X u).z = X.zu u := by
    show (lf D (X.Fu u)).fl.fvec (Fin.last _) = X.zu u
    rw [fv_last]
    exact X.flagZVector u
  have hpe : ∀ a : Fin D.R.rS, phiV C τ (X.eX a) =
      (((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) :=
    fun a => GlobalTheory.CovDom.ModelIso.qi_e X C τ a
  have hpf : ∀ a : Fin D.R.rS, phiV C τ (X.fY a) =
      ((((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) :=
    fun a => GlobalTheory.CovDom.ModelIso.qi_f X C τ a
  have hpz : phiV C τ (X.zu u) = zB X (C.Qi τ) u τ := rfl
  obtain ⟨hzW, hzT⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hTz : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hzT]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  refine ⟨⟨GlobalTheory.TypeAsm.GramPf.phiV_add C τ, GlobalTheory.TypeAsm.GramPf.phiV_smul C τ, GlobalTheory.TypeAsm.GramPf.phiV_herm C τ,
    GlobalTheory.TypeAsm.GramPf.phiV_span C τ⟩, hzW, hzW, hTz, ⟨1, normal0_one _ _ _ N.j_le hj _⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hF, hF', hFe, Matrix.one_mulVec, hpe]
    exact ⟨rfl, rfl⟩
  · intro b _
    rw [hist, hpf]
    push_cast
    rfl
  · rw [hF, hFz, hpz]
  · rw [hF', hFz, Matrix.one_mulVec, hpz]
end

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_points_base_lattice_stabilizer_fixed_frame_unipotent : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u →
      GlobalTheory.DegVol.realPts (fun τ => phiV C τ) (N.Gam (VS D).L0 : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) =
        trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
  first | exact @GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf | exact GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf | (intros; apply GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf <;> assumption)
end
