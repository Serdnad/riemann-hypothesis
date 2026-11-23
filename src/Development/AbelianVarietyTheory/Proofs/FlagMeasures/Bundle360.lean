module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle345
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibilityWitnessesCongrModThetaLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
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

theorem _root_.GlobalTheory.T.unitriangular_mul_inv_superdiagonalSum_sub : ∀ {E : Type} [Field E] {n : ℕ} (B C : Matrix (Fin n) (Fin n) E), (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) → (∀ i j, j < i → C i j = 0) → (∀ i, C i i = 1) → (∀ i j, j < i → (B * C⁻¹) i j = 0) ∧ (∀ i, (B * C⁻¹) i i = 1) ∧ Formalism.L2.SG.PairVal.sgUp (B * C⁻¹) = Formalism.L2.SG.PairVal.sgUp B - Formalism.L2.SG.PairVal.sgUp C := by
  first | exact @GlobalTheory.unitri_mul_inv_sgUp | exact GlobalTheory.unitri_mul_inv_sgUp | (intros; apply GlobalTheory.unitri_mul_inv_sgUp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.ZhatRat

theorem mapFlag_fvec {D : D7} {r : ℕ} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (h : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : FlagG (VS D) r T) (b : Fin (r + 1)) :
    (Formalism.L2.SG.TermOp.mapFlag γ h F).fvec b = γ (F.fvec b) := by
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.TermOp.mapFlag]
  · simp only [FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.TermOp.mapFlag]

theorem frm_one {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u 1 v a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  rw [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun a' => ?_) a
  · rw [Fin.snoc_last, FlagG.fvec, Fin.snoc_last, X.flagZVector u]
    rfl
  · rw [Fin.snoc_castSucc, FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u]
    rfl

end GlobalTheory.ZhatRat


open GlobalTheory.ZhatRat in
theorem GlobalTheory.zhatRat_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (τ : D.what₂.Tau), (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)).map (embS D τ) = Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 (X.pl.symm τ) := by
  intro D X Y W u u' s τ
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  rw [← mapL_lf W u]
  refine (congrArg (fun Z => Matrix.map Z (embS D τ)) (zhatL_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) s.frame)).trans ?_
  ext a b
  simp only [Matrix.map_apply]
  have hM1' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1
  have hM3' : ∀ y, X.crd (s.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3
  have hL : (s.frame).fl.fvec b = s.lin ((X.Fu u').fvec b) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hiso]
    exact mapFlag_fvec _ hiso _ _
  change embS D τ (brS (VS D) (s.frame.fl.fvec b) ((X.Fu u).fvec a)) = _
  rw [hL]
  unfold brS Formalism.L2.SG.RealObj.ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_one, frm_one, hM1', Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3', Formalism.L2.SG.Pf.Level.hJ_rv, X.φ_eq,
    X.pl.apply_symm_apply, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecompOrth

variable {D : D7}

theorem mem_orth_of_basis {n : ℕ} (U : Submodule D.host.E (VS D).V)
    (b : Module.Basis (Fin n) D.host.E U) (y : (VS D).V)
    (hy : ∀ i, (VS D).hT (b i : (VS D).V) y = 0) : y ∈ orth (VS D) U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u hu
  have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
    have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm

  rw [hu', map_sum]
  simp [hy]

theorem exists_decomp (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (x : (VS D).V) : ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b := by
  let b := Module.finBasis D.host.E U
  let L : U →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E) :=
    LinearMap.pi (fun i => ((VS D).hT (b i : (VS D).V)).comp U.subtype)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0 := fun i => congrFun hy i
    have hmem : (y : (VS D).V) ∈ U ⊓ orth (VS D) U := ⟨y.2, mem_orth_of_basis U b y hy'⟩
    rw [hU] at hmem
    exact Subtype.ext ((Submodule.mem_bot _).1 hmem)
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨y, hy⟩ := hsurj (fun i => (VS D).hT (b i : (VS D).V) x)
  refine ⟨x - y, mem_orth_of_basis U b _ (fun i => ?_), y, y.2, by abel⟩
  have := congrFun hy i
  simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [map_sub, this, sub_self]

theorem gram_det_ne_zero {n : ℕ} (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (b : Module.Basis (Fin n) D.host.E U) :
    (Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V)).det ≠ 0 := by
  intro h
  obtain ⟨α, hα0, hα⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hα0
  have hy : ∀ i, (VS D).hT (b i : (VS D).V) (((∑ j, α j • b j : U)) : (VS D).V) = 0 := by
    intro i
    have := congrFun hα i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this

    rw [Submodule.coe_sum, map_sum]
    simpa [mul_comm] using this
  have hmem : ((∑ j, α j • b j : U) : (VS D).V) ∈ U ⊓ orth (VS D) U :=
    ⟨Subtype.prop _, mem_orth_of_basis U b _ hy⟩
  rw [hU, Submodule.mem_bot] at hmem
  have h0 : ∑ j, α j • b j = 0 := Subtype.ext hmem
  funext j
  exact Fintype.linearIndependent_iff.1 b.linearIndependent α h0 j

end GlobalTheory.DecompOrth

namespace GlobalTheory.DecompOrth

variable {D : D7}

noncomputable def formLeft (Z : LocDat D) (p : PlF D) (w : Vp D p) : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep where
  toFun v := LocFacts₂ Z.M p v w
  map_add' x y := (locH Z p).h_add_left x y w
  map_smul' a x := (locH Z p).h_smul_left a x w

theorem formLeft_apply (Z : LocDat D) (p : PlF D) (w v : Vp D p) :
    formLeft Z p w v = LocFacts₂ Z.M p v w := rfl

theorem eq_zero_of_local_orth (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (Z : LocDat D) (p : PlF D) (v : Vp D p)
    (hv : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)))
    (horth : ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) : v = 0 := by
  let b := Module.finBasis D.host.E U
  have hspan : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) ≤
      Submodule.span (D.s.atP p).Ep (Set.range fun j => baseChange₂ D p (b j : (VS D).V)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm

    rw [hu', map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [baseChange_smul₂]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan hv)
  set G := Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V) with hGdef
  set A := G.map (D.s.atP p).ιE with hA
  have hAβ : Matrix.mulVec A β = 0 := by
    funext i
    have h1 := horth (b i) (b i).2
    have h2 : LocFacts₂ Z.M p (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) (baseChange₂ D p (b i : (VS D).V)) =
        formLeft Z p (baseChange₂ D p (b i : (VS D).V)) (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) := rfl

    rw [h2, map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [formLeft_apply, baseChangeAt_form Z.M p (Z.hcj p), brS] at h1
    simp only [Matrix.mulVec, dotProduct, hA, hGdef, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
    simpa [mul_comm] using h1
  have hdet : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne_zero U hU b)).map _
  have hβ : β = 0 := by
    have := congrArg (fun w => Matrix.mulVec A⁻¹ w) hAβ
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  simp [hβ]

end GlobalTheory.DecompOrth

theorem GlobalTheory.decomp_orth_complement : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 :=
  fun _ U hU => ⟨GlobalTheory.DecompOrth.exists_decomp U hU,
    fun Z p v hv horth => GlobalTheory.DecompOrth.eq_zero_of_local_orth U hU Z p v hv horth⟩
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem scaled_local_coef_eq :
    ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (a : Fin D.R.rS) (x : (VS D).V), x ∈ G.fl.X → frFac Z.δ p a.castSucc * (locH Z p).h (baseChange₂ D p x) ((A p).es a) = (D.s.atP p).ιE (G.fl.coefX x a) := by
  intro D T G Z A hA p a x hx

  have hes : ∀ b : Fin D.R.rS, frFac Z.δ p b.castSucc * (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) =
      if b = a then 1 else 0 := by
    intro b
    have h1 := (A p).h_es b a
    rw [hA p] at h1
    rw [← (locH Z p).h_smul_left]
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  have hunit : ∀ b : Fin D.R.rS, IsUnit (frFac Z.δ p b.castSucc) := by
    intro b
    have h1 := (A p).h_es b b
    rw [hA p] at h1
    rw [if_pos rfl, (locH Z p).h_smul_left] at h1
    exact isUnit_iff_exists_inv.mpr ⟨_, by simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1⟩
  have hzero : ∀ b : Fin D.R.rS, b ≠ a → (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) = 0 := by
    intro b hb
    have h1 := hes b
    rw [if_neg hb] at h1
    exact (hunit b).mul_right_eq_zero.mp h1

  have hxs : x ∈ Submodule.span D.host.E (Set.range G.fl.e) := hx
  have hexp : x = ∑ b, G.fl.coefX x b • G.fl.e b := by
    have h2 := G.fl.e_indep.linearCombination_repr ⟨x, hxs⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h2
    simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos hxs]
    exact h2.symm

  have hsum : ∀ (s : Finset (Fin D.R.rS)) (v : Fin D.R.rS → Vp D p) (y : Vp D p),
      (locH Z p).h (∑ b ∈ s, v b) y = ∑ b ∈ s, (locH Z p).h (v b) y := by
    intro s v y
    induction s using Finset.induction_on with
    | empty => simpa using (locH Z p).h_zero_left y
    | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, (locH Z p).h_add_left, ih]
  have hbc : baseChange₂ D p x = ∑ b, (D.s.atP p).ιE (G.fl.coefX x b) • baseChange₂ D p (G.fl.e b) := by
    conv_lhs => rw [hexp]

    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => baseChange_smul₂ p _ _
  rw [hbc, hsum, Finset.mul_sum, Finset.sum_eq_single a]
  · rw [(locH Z p).h_smul_left, mul_left_comm, hes a, if_pos rfl, mul_one]
  · intro b _ hb
    rw [(locH Z p).h_smul_left, hzero b hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.RowLatXS
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitRel

open Formalism.MainNotions.S.Loc ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

theorem framePairFixator_unitary_and_fixes_frame (P : Formalism.MainNotions.S.LocNG.FPair H r) {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    Formalism.MainNotions.S.LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold Formalism.MainNotions.S.LocNG.FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x.symm u) (x.symm v) = H.h u v
      have := hx.1 (x.symm u) (x.symm v)
      simpa using this.symm
    · show x.symm (P.A.f b) = P.A.f b
      conv_lhs => rw [← (hx.2 b).1]
      simp
    · show x.symm (P.B.f b) = P.B.f b
      conv_lhs => rw [← (hx.2 b).2]
      simp

theorem perp_stable {g : V ≃ₗ[E] V} (hu : Formalism.MainNotions.S.LocNG.IsUnitary H g) {f : Fin (r + 1) → V}
    (hf : ∀ b, g (f b) = f b) {x : V} (hx : x ∈ H.perp (H.X f)) : g x ∈ H.perp (H.X f) := by
  intro v hv
  have hfix : Set.EqOn (g : V →ₗ[E] V) (LinearMap.id : V →ₗ[E] V) (Set.range fun a : Fin r => f a.castSucc) := by
    rintro _ ⟨a, rfl⟩
    simpa using hf a.castSucc
  have hv' : g v = v := LinearMap.eqOn_span' hfix hv
  have := hu x v
  rw [hv'] at this
  rw [this]
  exact hx v hv

theorem rel_equivalence (P : Formalism.MainNotions.S.LocNG.FPair H r) :
    Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := P)) := by
  refine ⟨fun d => ?_, fun {d d'} h => ?_, fun {d d' d''} h h' => ?_⟩
  · refine ⟨1, P.UW0.one_mem, ?_, ?_, ?_⟩
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x' y' x y hx' hx
      have e1 : y' = x' := Subtype.ext (by simpa using hx')
      have e2 : y = x := Subtype.ext (by simpa using hx)
      subst e1; subst e2; exact Iff.rfl
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    refine ⟨g⁻¹, P.UW0.inv_mem hg, ?_, ?_, ?_⟩
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h1 y x this).symm
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h2 y x this).symm
    · intro x' y' x y hx' hx
      have a1 : (x' : V) = g y' := by rw [hx']; show (x' : V) = g (g.symm x'); simp
      have a2 : (x : V) = g y := by rw [hx]; show (x : V) = g (g.symm x); simp
      exact (h3 y' x' y x a1 a2).symm
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    obtain ⟨g', hg', h1', h2', h3'⟩ := h'
    have hs := framePairFixator_unitary_and_fixes_frame P hg
    refine ⟨g' * g, P.UW0.mul_mem hg' hg, ?_, ?_, ?_⟩
    · intro x y hxy
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h1 x z rfl).trans (h1' z y hxy)
    · intro x y hxy
      let z : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).2) x.2⟩
      exact (h2 x z rfl).trans (h2' z y hxy)
    · intro x' y' x y hx' hx
      let z' : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x', perp_stable hs.1 (fun b => (hs.2 b).2) x'.2⟩
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h3 x' z' x z rfl rfl).trans (h3' z' y' z y hx' hx)

theorem relEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS)
    (p : PlF D), Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := FP p)) :=
  fun _ _ FP p => rel_equivalence (FP p)

end GlobalTheory.OrbitRel
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admissibility_witnesses_congr_mod_theta_local : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), IsRowLat D F0 Λ → Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F' → ∀ ξ ξ' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit Λ (gS D) (lf D F0) F' ξ → AdmWit Λ (gS D) (lf D F0) F' ξ' → ∀ (p : PlF D) (a b : Fin (D.R.rS + 1)), (D.s.atP p).ιE (((ξ * ξ'⁻¹) a b : 𝓞 D.host.E) : D.host.E) - (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))} := by
  first | exact @GlobalTheory.WitCong.witness_congr | exact GlobalTheory.WitCong.witness_congr | (intros; apply GlobalTheory.WitCong.witness_congr <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagBaseChange

theorem isUnit_frFac {D : D7} {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (p : PlF D)
    (A : LocNG.FrameD (locH Z p) D.R.rS) (hA : A.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    (b : Fin D.R.rS) : IsUnit (frFac Z.δ p b.castSucc) := by
  rcases A with ⟨f, es, T0, h1, h2, h3, h4, h5⟩
  dsimp only at hA
  subst hA
  have hb := h4 b b
  dsimp only at hb
  rw [if_pos rfl, (locH Z p).h_smul_left] at hb
  exact ⟨⟨_, _, hb, (mul_comm _ _).trans hb⟩, rfl⟩

theorem span_bcP_Xa_eq_Fj : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (j : ℕ), Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa j : Set (VS D).V)) = (A p).Fj j := by
  intro D T G Z A hA p j
  unfold LocNG.FrameD.Fj LocNG.FrameD.e FlagG.Xa
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      obtain ⟨u, hu⟩ := GlobalTheory.FlagBaseChange.isUnit_frFac G Z p (A p) (hA p) i
      have hmem : (A p).f i.castSucc ∈
          Submodule.span (D.s.atP p).Ep ((fun a : Fin D.R.rS => (A p).f a.castSucc) '' {a : Fin D.R.rS | (a : ℕ) < j}) :=
        Submodule.subset_span ⟨i, hi, rfl⟩
      have hf : (A p).f i.castSucc = frFac Z.δ p i.castSucc • baseChange₂ D p (G.fl.e i) := by
        rw [hA p]
        dsimp only
        rw [Formalism.L2.SG.Pf.frame_castSucc_sat]
      rw [hf, ← hu] at hmem
      have hv := Submodule.smul_mem _ (↑u⁻¹ : (D.s.atP p).Ep) hmem
      rw [smul_smul, Units.inv_mul, one_smul] at hv
      exact hv
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [baseChange_smul₂]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    dsimp only
    rw [hA p]
    dsimp only
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨G.fl.e i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩
    rw [Formalism.L2.SG.Pf.frame_castSucc_sat]

end GlobalTheory.FlagBaseChange
end
