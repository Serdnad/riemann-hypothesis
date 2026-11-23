module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsGroupFixesAdelicLatticeIffColumnsLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle399
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle066
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle401
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle392
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle369
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle377
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IoEqOfGraph
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle076
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle285
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle386
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle403
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle086
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle404
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle402
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columns_group_fixes_adelic_lattice_iff_columns_lattice : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ((h : X.B.I.Gf) ∈ X.B.I.Kset ↔ ((∀ x, x ∈ hat D.host.F (Mq wt) ↔ y.1.1 *ᵥ x ∈ hat D.host.F (Mq wt)) ∧ ∀ x, (∀ z ∈ hat D.host.F (Mq wt), hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) z x ∈ OAd D.host.F D.host.E) → (y.1.1 - 1) *ᵥ x ∈ hat D.host.F (Mq wt))) := by
  first | exact @GlobalTheory.St.G.stabK_iff | exact GlobalTheory.St.G.stabK_iff | (intros; apply GlobalTheory.St.G.stabK_iff <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem tg_of_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  intro D X Y u u' F F' w hZ hG t hpt
  have hcF : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), 1, ?_, ?_, by rw [hZ]; simp⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne, fun h => h ▸ Matrix.one_apply_eq i⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq i⟩
  have hGw := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq F F' w hcF
  have hw : Formalism.L2.SG.PairVal.ptOf t.toTerm = w := Formalism.L2.SG.NGCut.NormalVectorPairings.toPts_inj _ _ hpt
  have hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
    by_contra h
    apply hG
    rw [← hGw, ← hpt]
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dite_eq_right h]
    exact Formalism.L2.SG.NGCut.NormalVectorPairings.GPt_junk D u u'
  obtain ⟨F'', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hex
  rw [hw] at hcell
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨F'', hP⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ := hmk
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ _ _).1 hmk'
  have hcell' : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w := ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).2.1 _ _ hrel w).1 hcell
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h0
    apply hG
    rw [← hGw]
    exact (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') _ _ w hcell').trans h0
  obtain ⟨-, γ, hγ, ⟨A, hA, hc⟩, ⟨B, hB, hd⟩⟩ := GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D (X.Fu u)) F t.frame F' w
    (Formalism.L2.SG.Corank.tu_ne_zero u) (Formalism.L2.SG.Corank.tu_ne_zero u') hGt hcell' hZ
  exact ⟨Formalism.HermitianLatticesTheory.gmap γ t.lam, γ, ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F.fl hA hc a⟩,
    ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F'.fl hB hd a⟩, rfl⟩

end GlobalTheory.Unfold
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedTerm_frame_admissibleIntegral : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D (X.Fu u)) u' (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) := by
  first | exact @GlobalTheory.Unfold.AdmGlued.glued_frame_PD | exact GlobalTheory.Unfold.AdmGlued.glued_frame_PD | (intros; apply GlobalTheory.Unfold.AdmGlued.glued_frame_PD <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicPart_eq_span_scaledFrame_unitriangular : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ e' : Fin D.R.rS → (VS D).V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ XLam Λ G = Submodule.span (𝓞 D.host.E) {y | ∃ (a : Fin D.R.rS) (x : D.host.E), x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧ y = x • e' a} := by
  first | exact @GlobalTheory.RowLatXS.xlam_eq_span_scaled | exact GlobalTheory.RowLatXS.xlam_eq_span_scaled | (intros; apply GlobalTheory.RowLatXS.xlam_eq_span_scaled <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.terms_same_rational_inner_class_are_translates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → t.lam = t₀.lam ∧ t.lam' = t₀.lam' ∧ ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t₀.lam (a * t₀.lin * a'⁻¹) t.lin := by
  first | exact @GlobalTheory.Unfold.CntC.translates | exact GlobalTheory.Unfold.CntC.translates | (intros; apply GlobalTheory.Unfold.CntC.translates <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.ClFin

theorem classes_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite ∧ ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  have hpos := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hw hG
  refine ⟨GlobalTheory.T.finite_isometriesFixingBothFrames_stabilizing_lattice D F F' hpos Λ₀ hΛ₀, ?_⟩
  obtain ⟨N, hN, hNs⟩ := GlobalTheory.T.orbitLattice_between_frameAndComplementParts D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨d, c, hd, hc, hdc⟩ := GlobalTheory.T.based_flag_pair_lattice_containment D X Y u u' F F' w hw hG Z FP hB hR Λ₀ (by first | exact hΛ₀ | exact hΛ₀.toIsLattice)
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_classes_lattices_fixedFramePart_boundedScale D F F' hpos (Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F')) N d c hN hd hc
  exact ⟨S, fun Λ hΛ hloc => hS Λ hΛ (GlobalTheory.T.localOrbitLattices_inf_frameSpan_eq D X Y u u' F F' w hw hG Z FP hB hR Λ₀ (by first | exact hΛ₀ | exact hΛ₀.toIsLattice) Λ hΛ hloc)
    (hNs Λ hΛ hloc) (hdc Λ hΛ hloc).1 (hdc Λ hΛ hloc).2⟩

end GlobalTheory.Unfold.ClFin
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.IotaLocal

theorem iotaGraph_eq_of_gdat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ :=
  GlobalTheory.IotaLocA.io_eq_of_graph

end GlobalTheory.Unfold.IotaLocal
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.KeyIff

variable {D : D7}

theorem one_mem {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : (1 : GV D) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

theorem dcoset_eq_iff {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ : GV D) :
    ({δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₁ * n'} : Set (GV D)) =
        {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} ↔
      ∃ n ∈ NRat F, ∃ n' ∈ NRat F', γ₂ = n * γ₁ * n' := by
  constructor
  · intro h
    have hm : γ₂ ∈ {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} :=
      ⟨1, one_mem F, 1, one_mem F', by simp⟩
    rw [← h] at hm
    exact hm
  · rintro ⟨n, hn, n', hn', rfl⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F hn),
        n'⁻¹ * b, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F' hn') hb, ?_⟩
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha hn, n' * b,
        Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' hn' hb, by group⟩

theorem key_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  intro D X Y u u' t t'
  have hkey : key t = key t' ↔
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ nmlOf Y u u' t = nmlOf Y u u' t' := Prod.ext_iff
  have hrow : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := by
    show rowOf Y.TR (Y.cs u) (Y.cs u') t = rowOf Y.TR (Y.cs u) (Y.cs u') t' ↔ _
    simp only [rowOf, Prod.mk.injEq, Subtype.mk.injEq]
  have hnml : nmlOf Y u u' t = nmlOf Y u u' t' ↔
      ∃ n ∈ NRat (lf D (X.Fu u)), ∃ n' ∈ NRat (lf D (X.Fu u')), t'.lin = n * t.lin * n' :=
    dcoset_eq_iff _ _ _ _
  rw [hkey, hrow, hnml]
  unfold KeyEq
  constructor
  · rintro ⟨⟨hl, hl', hi⟩, hc⟩
    exact ⟨hl, hl', hc, (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').1 hi⟩
  · rintro ⟨hl, hl', hc, hi⟩
    exact ⟨⟨hl, hl', (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').2 hi⟩, hc⟩

end GlobalTheory.Unfold.KeyIff
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Fibre

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem finrank_eq {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp, rank_eq]

theorem theta_eq_one {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {p : PlF D}
    (h : (FP p).PrimeTo) : LocNG.theta (Z.M p) = 1 := by
  unfold LocNG.theta
  rw [h.1]

theorem isLat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D) (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → t.abelian₂.FG ∧ Submodule.span (D.s.atP p).Ep (t.abelian₂ : Set (Vp D p)) = ⊤ := GlobalTheory.T.localTermLattice_over_innerDatum_fg_span

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t := GlobalTheory.T.localTerm_noDefect_primeTo_invariants

theorem full_of_local_span {D : D7} (Z : LocDat D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ) (p : PlF D)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let A := GlobalTheory.HL.placesOf Z
  have hcoord : Submodule.span D.host.E (LatLoc.cL Λ : Set (Fin (nV D) → D.host.E)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hzero⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have := (A.loc p).lf
    have := (A.loc p).char0
    have := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
    let ψ : (Fin (nV D) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
      ∑ i : Fin (nV D), (A.loc p).ιE (φ fun j => if i = j then 1 else 0) • LinearMap.proj i
    have hψ (z : Fin (nV D) → D.host.E) : ψ (A.bc p z) = (A.loc p).ιE (φ z) := by
      rw [φ.pi_apply_eq_sum_univ z, map_sum]
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, map_mul, GlobalTheory.HL.Places.bc]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hlat : A.lat p (LatLoc.cL Λ) ≤ (LinearMap.ker ψ).restrictScalars (A.L p).O := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      have hz' : φ z ∈ (⊥ : Submodule D.host.E D.host.E) := by
        rw [← hzero]
        exact Submodule.mem_map_of_mem (Submodule.subset_span hz)
      change ψ (A.bc p z) = 0
      rw [hψ, (Submodule.mem_bot D.host.E).mp hz', map_zero]
    have hker : Submodule.span (A.loc p).Ep (A.lat p (LatLoc.cL Λ) : Set _) ≤ LinearMap.ker ψ :=
      Submodule.span_le.mpr hlat
    rw [LatLoc.localLattice_eq] at hspan
    change Submodule.span (A.loc p).Ep (A.lat p (LatLoc.cL Λ) : Set (Fin (nV D) → (A.loc p).Ep)) = ⊤ at hspan
    rw [hspan] at hker
    apply hφ
    apply LinearMap.ext
    intro z
    have hz := LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := A.bc p z)))
    rw [hψ] at hz
    exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp hz
  refine { toIsLattice := hΛ, span_eq_top := ?_ }
  have hm : (Submodule.span D.host.E (Λ : Set (VS D).V)).map (LatLoc.cE D).toLinearMap = ⊤ := by
    rw [← Submodule.span_image]
    exact hcoord
  apply eq_top_iff.mpr
  intro x _
  have hx : LatLoc.cE D x ∈ (Submodule.span D.host.E (Λ : Set (VS D).V)).map (LatLoc.cE D).toLinearMap := by
    rw [hm]
    exact Submodule.mem_top
  obtain ⟨y, hy, heq⟩ := hx
  have : y = x := (LatLoc.cE D).injective heq
  simpa [this] using hy

theorem fibre : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ y : Dat Z FP, (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) → {p | y p ≠ d0 p}.Finite → ((globSet G G' y).encard : ℝ≥0∞) = ∏ p ∈ P, ((locSet G G' p (y p)).encard : ℝ≥0∞) := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS y hrel hfin
  obtain ⟨hBased, hRelG, hPrime, hTerm0, Λ₀, hΛ₀, hΛ₀t⟩ := hB
  obtain ⟨-, -, -, -, hloc⟩ := hS
  have hLG := LatLoc.lattices_local_global D Z
  haveI : Infinite (PlF D) := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.F
  obtain ⟨p₀, hp₀⟩ : ∃ p : PlF D, p ∉ P := by
    by_contra h
    push_neg at h
    exact Set.infinite_univ (α := PlF D) (P.finite_toSet.subset fun p _ => h p)
  have hΛ₀full : Submodule.IsFullLattice D.host.E Λ₀ :=
    full_of_local_span Z Λ₀ hΛ₀ p₀ (isLat D Z FP p₀ (d0 p₀) _ (hΛ₀t p₀ hp₀)).2

  have single : ∀ p, p ∉ P → ∃! L, L ∈ locSet G G' p (y p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have key := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_eq p)
      (hRelG p) (hPrime p hp) A A' (fun a b h => ⟨hA.1 a b h, hA'.1 a b h⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
      (scaled Z p (frame G)) (scaled Z p (frame G'))
      (fun j => by rw [hc j, (hBased p).1]; rfl) (fun j => by rw [hc' j, (hBased p).2.1]; rfl)
      (d0 p) (hTerm0 p) (y p)
    exact key.1 (hrel p hp)

  have std : ∀ p, p ∉ P → y p = d0 p → lattice₂ D Z.M p Λ₀ ∈ locSet G G' p (y p) := by
    intro p hp hy
    rw [hy]
    obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hloc p hp
    have hT : LocNG.IsTermOver (FP p) (d0 p) (tm FP G G' p (lattice₂ D Z.M p Λ₀)) :=
      GlobalTheory.T.hermitian_frame_witness_integral_change (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_eq p) (hRelG p) (d0 p)
        (tm FP F F' p (lattice₂ D Z.M p Λ₀)) (hΛ₀t p hp) A A' (scaled Z p (frame G)) (scaled Z p (frame G')) hA hA'
        (fun a b => ⟨(hint a b).1, (hint a b).2, by
          rw [theta_eq_one (hPrime p hp), map_one]
          refine Submodule.mem_span_singleton.2 ⟨⟨A a b - A' a b, (Z.M p).L.O.sub_mem (hint a b).1 (hint a b).2⟩, ?_⟩
          first
            | (rw [Algebra.smul_def, mul_one]; rfl)
            | (rw [Submodule.smul_def]; simp)
            | (simp [Algebra.smul_def])
            | (erw [smul_eq_mul, mul_one])
            | (change (A a b - A' a b) * 1 = _; rw [mul_one])⟩) hc hc'
    exact ⟨hT, noDefect D Z FP p (hRelG p) (hPrime p hp) (d0 p) _ hT⟩

  let Φ : LV D → ∀ q : P, Submodule (Z.M q).L.O (Vp D q) := fun Λ q => lattice₂ D Z.M q Λ
  have hinj : Set.InjOn Φ (globSet G G' y) := by
    intro Λ₁ h₁ Λ₂ h₂ e
    refine (hLG.1 Λ₁ Λ₂ (full_of_local_span Z Λ₁ h₁.1 p₀ (isLat D Z FP p₀ (y p₀) _ (h₁.2 p₀).1).2) (full_of_local_span Z Λ₂ h₂.1 p₀ (isLat D Z FP p₀ (y p₀) _ (h₂.2 p₀).1).2)).2 fun p => ?_
    by_cases hp : p ∈ P
    · exact congrFun e ⟨p, hp⟩
    · exact (single p hp).unique (h₁.2 p) (h₂.2 p)
  have himg : Φ '' globSet G G' y = Set.univ.pi (fun q : P => locSet G G' q (y q)) := by
    ext g
    constructor
    · rintro ⟨Λ, hΛ, rfl⟩ q -
      exact hΛ.2 q
    · intro hg
      let Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p) := fun p =>
        if h : p ∈ P then g ⟨p, h⟩ else (single p h).exists.choose
      have hLp : ∀ p, Lp p ∈ locSet G G' p (y p) := by
        intro p
        by_cases h : p ∈ P
        · simp only [Lp, dif_pos h]; exact hg ⟨p, h⟩ (Set.mem_univ _)
        · simp only [Lp, dif_neg h]; exact (single p h).exists.choose_spec
      have hlat : ∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤ :=
        fun p => isLat D Z FP p (y p) (tm FP G G' p (Lp p)) (hLp p).1
      have hfin' : {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite := by
        refine ((P.finite_toSet).union hfin).subset fun p hp => ?_
        by_contra hn
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hn
        exact hp ((single p hn.1).unique (hLp p) (std p hn.1 hn.2))
      obtain ⟨Λ, hΛ, hΛp⟩ := hLG.2 Λ₀ hΛ₀full Lp hlat hfin'
      refine ⟨Λ, ⟨hΛ, fun p => by rw [hΛp p]; exact hLp p⟩, ?_⟩
      funext q
      show lattice₂ D Z.M q Λ = g q
      rw [hΛp q]
      show (if h : (q : PlF D) ∈ P then g ⟨q, h⟩ else (single q h).exists.choose) = g q
      rw [dif_pos q.2]
  have e1 := hinj.encard_image
  rw [himg, Set.encard_pi_eq_prod_encard] at e1
  rw [← e1]
  exact (map_prod ENat.toENNRealRingHom (fun i : P => (locSet G G' i (y i)).encard) Finset.univ).trans
    (Finset.prod_coe_sort P (fun p => ((locSet G G' p (y p)).encard : ℝ≥0∞)))

end GlobalTheory.GenMass.Fibre
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGen

theorem genFam : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t) → (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, ∀ t'' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'') → FamQ Y u u' Not (Y.tO u u').genSet (gCls Y u u') := by
  intro D X Y u u' hsym htr
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t ∈ gCls Y u u' t := by
    intro t ht
    obtain ⟨h1, h2⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t (hG t ht) rfl rfl
    exact ⟨ht, rfl, h1, h2⟩

  have hrow : ∀ t t' : TauC Y u u', t' ∈ gCls Y u u' t → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t :=
    fun t t' h => h.2.1

  have hsub : ∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' →
      gCls Y u u' t' ⊆ gCls Y u u' t := by
    intro t ht t' ht' hr hs hc x hx
    obtain ⟨hxg, hxr, hxs, hxc⟩ := hx
    obtain ⟨h1, h2⟩ := htr t ht t' ht' x hxg hr hxr.symm hs hc hxs hxc
    exact ⟨hxg, hxr.trans hr.symm, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      obtain ⟨hs, hc⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t' (hG t ht) hr hn
      obtain ⟨hs', hc'⟩ := hsym t ht t' ht' hr hs hc
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs' hc') (hsub t ht t' ht' hr hs hc)
  · intro t ht t' ht' he
    have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.SnFamGen
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_besselMap_rankOne_factorisation_translateSpan : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → MultOne z (psiGen k r z c) σ π → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → NonVan z (psiGen k r z c) σ π w μG ν → ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l := by
  first | exact @GlobalTheory.SgInf.exists_isEll_DD | exact GlobalTheory.SgInf.exists_isEll_DD | (intros; apply GlobalTheory.SgInf.exists_isEll_DD <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  first | exact @GlobalTheory.Amp.LocalSetupGap.exists_setup_both | exact GlobalTheory.Amp.LocalSetupGap.exists_setup_both | (intros; apply GlobalTheory.Amp.LocalSetupGap.exists_setup_both <;> assumption)
end
