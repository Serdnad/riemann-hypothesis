module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle381
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMajorantLengthMomentLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle380
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle384
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle385
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle377
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle386
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularOfLocalStandardLatticeTranslates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeAutomorphismsEqAdaptedModUnipotent
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.BasePt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F i.castSucc = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem tri_of_adapt {T : D.host.E} (g : GV D) (F G : LFlag (D.sp.Y 0) D.R.rS T) (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h : ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val) :
    GlobalTheory.LocOver.Tri D.host.E (frame G) (frame (Formalism.L2.SG.Saturated.mapL g hg F)) := by
  have ex : ∀ b : Fin (D.R.rS + 1), ∃ l : Fin D.R.rS →₀ D.host.E,
      l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.val < b.val} ∧
        Finsupp.linearCombination D.host.E G.fl.e l = g (frame F b) - frame G b := fun b =>
    (Finsupp.mem_span_image_iff_linearCombination D.host.E).1 (h b)
  choose l hl hx using ex
  have hz : ∀ b (i : Fin D.R.rS), ¬ i.val < b.val → l b i = 0 := fun b i hi =>
    (Finsupp.mem_supported' D.host.E (l b)).1 (hl b) i hi
  refine ⟨fun a b => (if a = b then 1 else 0) + (if h : a.val < D.R.rS then l b ⟨a.val, h⟩ else 0), ⟨?_, ?_⟩, ?_⟩
  · intro a b hba
    dsimp only
    rw [if_neg (ne_of_gt hba), zero_add]
    split_ifs with h'
    · exact hz b _ (by show ¬ a.val < b.val; have := Fin.lt_def.1 hba; omega)
    · rfl
  · intro a
    dsimp only
    rw [if_pos rfl]
    split_ifs with h'
    · rw [hz a _ (by simp), add_zero]
    · rw [add_zero]
  · intro b
    rw [Formalism.L2.SG.Saturated.frame_mapL]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true,
      zero_smul, add_zero, frame_castSucc, Fin.eta]
    have e := hx b
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
    rw [e]
    abel

theorem term_at_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 →
      ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → t.G ≠ 0 ∧ ptPN t = toPts w := by
  intro D X Y u u' F F' w hZ hG t Λ hTG
  obtain ⟨g, ⟨hg, h1⟩, ⟨-, h2⟩, -⟩ := hTG
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hcell : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨1, 1, fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_lt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_gt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [hZ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨-, hB⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell
  obtain ⟨hcell2, hG2⟩ := hB _ _ (tri_of_adapt g (lf D (X.Fu u)) F hg h1) (tri_of_adapt g t.frame F' hg h2)
  replace hcell2 : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
    (congrArg (fun Z => IsInCell (ZhatOM Z) w) (Formalism.L2.SG.Saturated.zhat_mapL g hg (lf D (X.Fu u)) t.frame)).mp hcell2
  replace hG2 : Gval (lf D (X.Fu u)) t.frame = Gval F F' :=
    (Formalism.L2.SG.Saturated.gval_mapL g hg (lf D (X.Fu u)) t.frame).symm.trans hG2
  have hGt : t.G ≠ 0 := by rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, hG2]; exact hG
  have hat : t.toTerm.atPt w := ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, fun h0 => hG (hG2.symm.trans h0), hcell2⟩
  have hrel : t.toTerm.relevant := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t.toTerm w hat
  have hsp := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hat, hrel⟩
  have heq := Formalism.L2.SG.Pf.cellPtUnique_of Formalism.L2.SG.Pf.cell_point_uniqueness
    (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u) t.toTerm _ _ hsp hat
  exact ⟨hGt, by show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = toPts w; rw [heq]⟩

end GlobalTheory.Unfold.BasePt
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_add_isotropicSpan_mem_locallyStandardLattice : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  first | exact @GlobalTheory.IsotropicLift.exists_add_mem | exact GlobalTheory.IsotropicLift.exists_add_mem | (intros; apply GlobalTheory.IsotropicLift.exists_add_mem <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameProj
variable {D : D7}

private theorem localLattice_fg_span (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hc : Submodule.IsFullLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) := by
    refine { toIsLattice := GlobalTheory.Unfold.LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((GlobalTheory.Unfold.LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (GlobalTheory.Unfold.LatLoc.cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (GlobalTheory.Unfold.LatLoc.cL Λ) hc).2.1 p
  rw [GlobalTheory.Unfold.LatLoc.localLattice_eq]
  exact this

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)



open GlobalTheory.ThetaMove.CommonRef in
theorem lattice_between_parts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ N : ℕ, 0 < N ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')) := by
  intro D X Y u u' F F' w hZ hG Z FP hB hRel Λ₀ hΛ₀
  letI := hΛ₀
  have hU : ∀ y ∈ Xplus F ⊔ Xplus F', y ∈ orth (VS D) (Xplus F ⊔ Xplus F') → y = 0 := by
    intro y hyU hyW
    by_contra hy
    have hpos := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hZ hG y hyW hy
    have h0 : (VS D).hT y y = 0 := (mem_orth_iff _ y).1 hyW y hyU
    rw [h0, map_zero] at hpos
    exact lt_irrefl _ hpos
  have hdet := gram_det_isUnit _ hU
  have hcomm : ∀ p : PlF D, ∀ h ∈ (FP p).UW0, ∀ y,
      projP Z p (Xplus F ⊔ Xplus F') (h y) = h (projP Z p (Xplus F ⊔ Xplus F') y) :=
    fun p h hh y => localOrthogonalProj_comm_complementUnitary Z p F F' (FP p) (hB p).1 (hB p).2.1 h hh y
  generalize Xplus F ⊔ Xplus F' = U at hU hdet hcomm ⊢
  obtain ⟨N, hN, hNmem⟩ := exists_nat_smul_le (full_of_span (Submodule.IsFullLattice.span_eq_top (A := D.host.E) (M := Λ₀)))
    (hΛ₀.fg.map ((proj U).restrictScalars (𝓞 D.host.E)))
  have hcast : ∀ v : (VS D).V, (N : D.host.E) • v = (N : 𝓞 D.host.E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨Q, hQ⟩ : ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, Q = (N : D.host.E) • proj U := ⟨_, rfl⟩
  have hQx : ∀ x, Q x = (N : D.host.E) • proj U x := fun x => by rw [hQ]; rfl
  have hQ₀ : Λ₀.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Λ₀ := by
    rintro _ ⟨x, hx, rfl⟩
    show Q x ∈ Λ₀
    rw [hQx, hcast]
    exact hNmem _ ⟨x, hx, rfl⟩
  refine ⟨N, hN, ?_⟩
  intro Λ hΛ hloc
  have hQp : ∀ p : PlF D, ∀ x, baseChange₂ D p (Q x) = ((N : (D.s.atP p).Ep) • projP Z p U) (baseChange₂ D p x) := by
    intro p x
    rw [hQx, LinearMap.smul_apply, baseChange_smul₂, baseChangeAt_proj Z p, map_natCast]
  obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
  obtain ⟨g, hg, hgp⟩ := hloc p
  have hspan₀ := (localLattice_fg_span Z Λ₀ hΛ₀ p).2
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
    rw [← hgp]
    have e : (LocNG.img g (lattice₂ D Z.M p Λ₀) : Set (Vp D p)) =
        (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) '' (lattice₂ D Z.M p Λ₀ : Set (Vp D p)) := rfl
    rw [e, Submodule.span_image, hspan₀, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  have hΛfull := isFullLattice_of_local_span Z p Λ hΛ hspan
  have hlat' : Submodule.IsLattice D.host.E (Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E))) :=
    Submodule.IsLattice.of_fg D.host.E (hΛ.fg.sup (hΛ.fg.map _))
  have hlatFull : Submodule.IsFullLattice D.host.E (Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E))) := by
    refine { toIsLattice := hlat', span_eq_top := ?_ }
    apply top_unique
    rw [← hΛfull.span_eq_top]
    exact Submodule.span_mono (by intro x hx; exact Submodule.mem_sup_left hx)
  have heq : Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E)) = Λ := by
    refine ((GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 _ Λ hlatFull hΛfull).2 fun p => ?_
    rw [localLattice_sup, sup_eq_left, localLattice_map Z p Q _ (hQp p)]
    obtain ⟨h, hh, himg⟩ := hloc p
    obtain ⟨Qp, hQpdef⟩ : ∃ Qp : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p, Qp = (N : (D.s.atP p).Ep) • projP Z p U :=
      ⟨_, rfl⟩
    rw [← hQpdef]
    have hc : ∀ y, Qp (h y) = h (Qp y) := by
      intro y
      rw [hQpdef, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hcomm p h hh y]
    have hL : (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O) ≤ lattice₂ D Z.M p Λ₀ :=
      calc (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O)
          = lattice₂ D Z.M p (Λ₀.map (Q.restrictScalars (𝓞 D.host.E))) :=
            (localLattice_map Z p Q Qp (fun x => hQpdef ▸ hQp p x) Λ₀).symm
        _ ≤ lattice₂ D Z.M p Λ₀ := localLattice_mono Z p hQ₀
    have := img_map_le Z p Qp h hc _ hL
    rwa [himg] at this
  have key : ∀ y ∈ Λ, Q y ∈ Λ := fun y hy => by
    rw [← heq]
    exact Submodule.mem_sup_right ⟨y, hy, rfl⟩
  intro x hx
  refine Submodule.mem_sup.2 ⟨Q x, ⟨key x hx, ?_⟩, (N : D.host.E) • x - Q x, ⟨?_, ?_⟩, add_sub_cancel _ _⟩
  · show Q x ∈ U
    rw [hQx]
    exact U.smul_mem _ (proj_mem U x)
  · refine Λ.sub_mem ?_ (key x hx)
    rw [hcast]
    exact Λ.smul_mem _ hx
  · show (N : D.host.E) • x - Q x ∈ orth (VS D) U
    rw [hQx, ← smul_sub]
    exact Submodule.smul_mem _ _ (sub_proj_mem_orth U hdet x)

end GlobalTheory.FrameProj
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlobalApprox

theorem bcP_osmul (D : D7) (q : PlF D) (a : 𝓞 D.host.E) (m : (VS D).V) :
    baseChange₂ D q (a • m) = (D.s.atP q).ιE (a : D.host.E) • baseChange₂ D q m := by
  rw [← IsScalarTower.algebraMap_smul D.host.E a m]
  exact baseChange_smul₂ (D := D) q _ m

theorem osmul_mem (D : D7) (Z : LocDat D) (q : PlF D) (M : LV D) (m : (VS D).V) (hm : m ∈ M)
    (o : (D.s.atP q).Ep) (ho : o ∈ (D.s.atP q).O) : o • baseChange₂ D q m ∈ lattice₂ D Z.M q M := by
  have hO : (Z.M q).L.O = (D.s.atP q).O := (Z.agree q).2.2.2.1
  have ho' : o ∈ (Z.M q).L.O := by rw [hO]; exact ho
  have hgen : baseChange₂ D q m ∈ lattice₂ D Z.M q M := Submodule.subset_span ⟨m, hm, rfl⟩
  exact (lattice₂ D Z.M q M).smul_mem (⟨o, ho'⟩ : (Z.M q).L.O) hgen

theorem approx_gen (D : D7) (Z : LocDat D) (p : PlF D) (M : LV D) (m : (VS D).V) (hm : m ∈ M)
    (c : (D.s.atP p).Ep) (hc : c ∈ (D.s.atP p).O) :
    ∃ l ∈ M, (∃ w ∈ lattice₂ D Z.M p M, baseChange₂ D p l - c • baseChange₂ D p m = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w) ∧
      ∀ p' : PlF D, p' ≠ p → ∃ w ∈ lattice₂ D Z.M p' M, baseChange₂ D p' l = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • w := by
  obtain ⟨a, ⟨o, ho, hao⟩, hfar⟩ := GlobalTheory.T.exists_integer_congruent_local_mod_g_one_place D p c hc
  refine ⟨a • m, M.smul_mem a hm, ⟨o • baseChange₂ D p m, osmul_mem D Z p M m hm o ho, ?_⟩, ?_⟩
  · rw [bcP_osmul, ← sub_smul, hao, mul_smul]
  · intro p' hp'
    obtain ⟨o', ho', hao'⟩ := hfar p' hp'
    exact ⟨o' • baseChange₂ D p' m, osmul_mem D Z p' M m hm o' ho', by rw [bcP_osmul, hao', mul_smul]⟩

theorem smul_step {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (g c : R) (b b' x w w' : V)
    (h : b - x = g • w) (h' : b' - c • b = g • w') : b' - c • x = g • (w' + c • w) := by
  rw [smul_add, ← h', smul_comm g c w, ← h, smul_sub]
  abel

theorem approx : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (M : LV D) (x : Vp D p), x ∈ lattice₂ D Z.M p M → ∃ l ∈ M, (∃ w ∈ lattice₂ D Z.M p M, baseChange₂ D p l - x = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • w) ∧ ∀ p' : PlF D, p' ≠ p → ∃ w ∈ lattice₂ D Z.M p' M, baseChange₂ D p' l = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • w := by
  intro D Z p M x hx
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  have hx' : x ∈ Submodule.span (Z.M p).L.O (baseChange₂ D p '' (M : Set (VS D).V)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨l, hl, ⟨w, hw, hlw⟩, hfar⟩ := approx_gen D Z p M m hm 1 (Subring.one_mem _)
    rw [one_smul] at hlw
    exact ⟨l, hl, ⟨w, hw, hlw⟩, hfar⟩
  | zero =>
    refine ⟨0, M.zero_mem, ⟨0, (lattice₂ D Z.M p M).zero_mem, by simp⟩, fun p' _ => ?_⟩
    exact ⟨0, (lattice₂ D Z.M p' M).zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l₁, hl₁, ⟨w₁, hw₁, e₁⟩, f₁⟩ := hy
    obtain ⟨l₂, hl₂, ⟨w₂, hw₂, e₂⟩, f₂⟩ := hz
    refine ⟨l₁ + l₂, M.add_mem hl₁ hl₂, ⟨w₁ + w₂, (lattice₂ D Z.M p M).add_mem hw₁ hw₂, ?_⟩, ?_⟩
    · rw [map_add (f := _), smul_add, ← e₁, ← e₂]
      abel
    · intro p' hp'
      obtain ⟨v₁, hv₁, g₁⟩ := f₁ p' hp'
      obtain ⟨v₂, hv₂, g₂⟩ := f₂ p' hp'
      exact ⟨v₁ + v₂, (lattice₂ D Z.M p' M).add_mem hv₁ hv₂, by rw [map_add (f := _), g₁, g₂, smul_add]⟩
  | smul r y _ hy =>
    obtain ⟨l, hl, ⟨w, hw, e⟩, _⟩ := hy
    have hr : (r : (D.s.atP p).Ep) ∈ (D.s.atP p).O := by rw [← hO]; exact r.2
    obtain ⟨l', hl', ⟨w', hw', e'⟩, hfar'⟩ := approx_gen D Z p M l hl (r : (D.s.atP p).Ep) hr
    refine ⟨l', hl', ⟨w' + r • w, (lattice₂ D Z.M p M).add_mem hw' ((lattice₂ D Z.M p M).smul_mem r hw), ?_⟩, hfar'⟩
    exact smul_step _ (r : (D.s.atP p).Ep) (baseChange₂ D p l) (baseChange₂ D p l') y w w' e e'

end GlobalTheory.GlobalApprox
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isUnimodular_of_local_standardLattice_translates : ∀ (D : D7) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS) (Λ : LV D), Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  first | exact @GlobalTheory.Unfold.StdDual.unimodular_of_local | exact GlobalTheory.Unfold.StdDual.unimodular_of_local | (intros; apply GlobalTheory.Unfold.StdDual.unimodular_of_local <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u, ∃ A N : Subgroup (GV D), (A : Set (GV D)) = Aut0 (lf D (X.Fu u)) Λ ∧ (N : Set (GV D)) = NLam Λ (lf D (X.Fu u)) ∧ N ≤ A ∧ (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) ∧ N.relIndex A = Nat.card (autLz D (X.Fu u) Λ) ∧ 0 < Nat.card (autLz D (X.Fu u) Λ) := by
  first | exact @GlobalTheory.AutQuot.autQuot | exact GlobalTheory.AutQuot.autQuot | (intros; apply GlobalTheory.AutQuot.autQuot <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluedLattice_weightedCount_le_explicit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  first | exact @GlobalTheory.GlueCount.glueSum_le | exact GlobalTheory.GlueCount.glueSum_le | (intros; apply GlobalTheory.GlueCount.glueSum_le <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_continuous_besselMap_smoothVectors : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ l : H → Wp, IsBesselMapSm z (psiGen k r z c) σ π l ∧ ∀ u ∈ DD σ w, l u = be (psiGen k r z c) π μS σ u v ξ := by
  first | exact @GlobalTheory.SgInf.exists_besselExt | exact GlobalTheory.SgInf.exists_besselExt | (intros; apply GlobalTheory.SgInf.exists_besselExt <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.inverseMajorantLength_moment_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  first | exact @GlobalTheory.InvLenMomentGap.inv_len_moment_gap | exact GlobalTheory.InvLenMomentGap.inv_len_moment_gap | (intros; apply GlobalTheory.InvLenMomentGap.inv_len_moment_gap <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.oneMajorantLength_moment_lowestKType : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν (q : ℕ), n1 ν + (r + 1) * q ≤ q0 → (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) := by
  first | exact @GlobalTheory.MomOneGap.moment_one_gap | exact GlobalTheory.MomOneGap.moment_one_gap | (intros; apply GlobalTheory.MomOneGap.moment_one_gap <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integralUnipotent_eq_latticeUnipotent_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  first | exact @GlobalTheory.CovDomGrp.nO_eq_nLam_coords | exact GlobalTheory.CovDomGrp.nO_eq_nLam_coords | (intros; apply GlobalTheory.CovDomGrp.nO_eq_nLam_coords <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sum_frameClassWeights_le_datumBound : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  first | exact @GlobalTheory.TypeAsm.PerRow.sum_clsOm_le_datBd | exact GlobalTheory.TypeAsm.PerRow.sum_clsOm_le_datBd | (intros; apply GlobalTheory.TypeAsm.PerRow.sum_clsOm_le_datBd <;> assumption)
end
