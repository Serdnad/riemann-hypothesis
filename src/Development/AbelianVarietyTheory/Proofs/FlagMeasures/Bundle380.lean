module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle349
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle341
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle337
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle338
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle042
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardExactGramIntegralFrameClassesLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle368
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle369
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrame
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.mass_bound_low_types_alt : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  first | exact @GlobalTheory.WedgeKappaL.kappa_bound | exact GlobalTheory.WedgeKappaL.kappa_bound | (intros; apply GlobalTheory.WedgeKappaL.kappa_bound <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.linearIndependent_changedRationalFrames_of_unitriangular : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  first | exact @GlobalTheory.GenMass.changed_frames_linInd | exact GlobalTheory.GenMass.changed_frames_linInd | (intros; apply GlobalTheory.GenMass.changed_frames_linInd <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StIntLat

theorem stMat_int_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ y : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ, (∃ x ∈ G.K0, y = fun v p => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2)) ↔ ∀ p : Formalism.L2.SG.RealObj.FreeE w, (fun v => y v p) ∈ ((((ddS D ^ (-(((p.1.2.val - p.1.1.val : ℕ)) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) 1)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c y
  have hT : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u').ne'
  have hli : LinearIndependent D.host.E G.f' := by
    have h0 : LinearIndependent D.host.E (frame F'0) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F'0.fl hT
    have h1 := h0.map' (c.e : (VS D).V →ₗ[D.host.E] G.V) c.e.ker
    have e : G.f' = (c.e : (VS D).V →ₗ[D.host.E] G.V) ∘ frame F'0 := by
      funext a; exact c.f'_eq a
    rw [e]; exact h1
  have hStCo := GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hK := GlobalTheory.T.integralStabiliser_iff_rational_coords D X Y u u' hSt hk w F00 F'0 FP hZ hG hAB G c
  have hexp : ∀ a b : Fin (D.R.rS + 1), a < b →
      (-(((b.val - a.val : ℕ)) : ℤ)) = -((b : ℤ) - (a : ℤ)) := by
    intro a b hab
    have : a.val ≤ b.val := le_of_lt hab
    rw [Nat.cast_sub this]
  constructor
  · rintro ⟨x, hx, rfl⟩ p
    have hxSt : x ∈ G.St := by
      intro q
      obtain ⟨g', hg', he⟩ := hx q
      exact ⟨g', hg'.1.1, he⟩
    obtain ⟨B, -, hB, -⟩ := hStCo.1 x hxSt
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hB⟩
    have hmem := (hK x hxSt _ hspec).1 hx p.1.1 p.1.2 p.2.1
    refine ⟨GlobalTheory.HL.TraceConjugationCover.stMat G x p.1.1 p.1.2, ?_, ?_⟩
    · rw [hexp _ _ p.2.1]; exact hmem
    · funext v; simp [Formalism.L2.SG.NGCut.SplitEmbedding.embS]
  · intro h
    choose lam hlam hlamE using h
    let B : Formalism.L2.SG.PairVal.MatR D := fun a b =>
      if a = b then 1 else if hab : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
        then lam ⟨(a, b), hab⟩ else 0
    have hBU : IsUpUni B := by
      intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have h1 : i ≠ j := fun h => (lt_irrefl j) (h ▸ hji)
        have h2 : ¬ (i < j ∧ Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1) := fun h => (lt_asymm hji) h.1
        simp only [B, if_neg h1, dif_neg h2]
      · simp only [B, if_pos hij]
    have hBblk : ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 →
        B a b = 0 := by
      intro a b hne
      have h1 : a ≠ b := fun h => hne (h ▸ rfl)
      have h2 : ¬ (a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1) := fun h => hne h.2
      simp only [B, if_neg h1, dif_neg h2]
    obtain ⟨x, ⟨hxSt, hxB⟩, -⟩ := hStCo.2 B hBU hBblk
    have hxK : x ∈ G.K0 := by
      refine (hK x hxSt B hxB).2 fun a b hab => ?_
      have h1 : a ≠ b := ne_of_lt hab
      by_cases h2 : a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1
      · simp only [B, if_neg h1, dif_pos h2]
        have := hlam ⟨(a, b), h2⟩
        rw [hexp _ _ hab] at this
        exact this
      · simp only [B, if_neg h1, dif_neg h2]
        exact FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)
    have hspec := GlobalTheory.HL.TraceConjugationCover.stMat_spec G x ⟨B, hxB⟩
    have hM : GlobalTheory.HL.TraceConjugationCover.stMat G x = B := by
      funext a b
      have e2 : ∑ d, (GlobalTheory.HL.TraceConjugationCover.stMat G x d b - B d b) • G.f' d = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, ← hspec b, ← hxB b, sub_self]
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e2 a)
    refine ⟨x, hxK, ?_⟩
    funext v p
    have e1 := congrFun (hlamE p) v
    simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at e1
    rw [hM, ← e1]
    have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
    simp only [B, if_neg h1, dif_pos p.2]
    all_goals first | rfl | (congr 1)

end GlobalTheory.HL.StIntLat
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (D.sp.Y 0) D.R.rS T) (F₃ : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  first | exact @GlobalTheory.LocOver.base_frames_at_point | exact GlobalTheory.LocOver.base_frames_at_point | (intros; apply GlobalTheory.LocOver.base_frames_at_point <;> assumption)
end

section

noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem nO_eq_nLam_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  intro D X θ C u
  have key : ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
      ((GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ↔
        n ∈ Formalism.MainNotions.S.Lat.NLam (VS D).L0 (lf D (X.Fu u))) := by
    intro n γ hγ
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).1 h1, (GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved X n γ hγ).1 h4⟩, (GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved X u n γ hγ).1 h2,
        (GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates X u n γ hγ).1 h3⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).2 h1, (GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved X u n γ hγ).2 h2, (GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates X u n γ hγ).2 h3⟩,
        (GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved X n γ hγ).2 h4⟩
  refine ⟨fun γ hγ => ?_, fun s hs => ?_⟩
  · obtain ⟨n, hn⟩ := exists_equiv X γ hγ.1.1
    have hnL := (key n γ hn).1 hγ
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hnL.1.1
    exact ⟨x.1, (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u x.1).2 ⟨x, n, hx, rfl, hnL⟩,
      GlobalTheory.T.besselModelTransport_conj_placeMatrices X C x.1 γ (GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace X n γ hx hn)⟩
  · obtain ⟨x, n, hx, rfl, hnL⟩ := (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u s).1 hs
    obtain ⟨γ, hγ⟩ := exists_mat X n
    exact ⟨γ, (key n γ hγ).2 hnL, GlobalTheory.T.besselModelTransport_conj_placeMatrices X C x.1 γ (GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace X n γ hx hγ)⟩

end GlobalTheory.CovDomGrp
end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_exactGramIntegralFrameClasses_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  first | exact @GlobalTheory.LoopC.FrEx.cntCl_ExSet_le | exact GlobalTheory.LoopC.FrEx.cntCl_ExSet_le | (intros; apply GlobalTheory.LoopC.FrEx.cntCl_ExSet_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.exists_rectangular_conj_instanceMatrix_standardPsi : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)), StdPsi hF PY → ∃ (U : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) (U' : Matrix (Fin D.R.r) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧ ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ y))).2) = U * ((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF) * U' := by
  first | exact @GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi | exact GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi | (intros; apply GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  first | exact @GlobalTheory.LabFix.mem_VT_of_sum_fixed | exact GlobalTheory.LabFix.mem_VT_of_sum_fixed | (intros; apply GlobalTheory.LabFix.mem_VT_of_sum_fixed <;> assumption)
end

section


theorem _root_.GlobalTheory.T.termsOverRow_compatible : GlobalTheory.TypeAsm.CompatC := by
  first | exact @GlobalTheory.TypeAsm.CompatPf.compatC | exact GlobalTheory.TypeAsm.CompatPf.compatC | (intros; apply GlobalTheory.TypeAsm.CompatPf.compatC <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf) ∧ (∀ x y, ιA (hA X.B.I (embA X wt ιA x) (embA X wt ιA y)) = hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) x y) ∧ Function.Injective (embA X wt ιA) ∧ (∀ x a, hA X.B.I (incl X.B.I (X.eR a)) (embA X wt ιA x) = 0 ∧ hA X.B.I (incl X.B.I (X.fR a)) (embA X wt ιA x) = 0) ∧ (∀ x, hA X.B.I (incl X.B.I (X.zR u)) (embA X wt ιA x) = 0) ∧ ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  first | exact @GlobalTheory.St.G.MHat.mhat_coords | exact GlobalTheory.St.G.MHat.mhat_coords | (intros; apply GlobalTheory.St.G.MHat.mhat_coords <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_unitary_extend_by_identity_on_fixSet : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  first | exact @GlobalTheory.St.rational_unitary_extend_by_identity | exact GlobalTheory.St.rational_unitary_extend_by_identity | (intros; apply GlobalTheory.St.rational_unitary_extend_by_identity <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  first | exact @GlobalTheory.St.unitary_fix_acts_on_complement_frame | exact GlobalTheory.St.unitary_fix_acts_on_complement_frame | (intros; apply GlobalTheory.St.unitary_fix_acts_on_complement_frame <;> assumption)
end
