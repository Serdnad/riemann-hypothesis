module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

instance sf2 : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
  rw [← ENNReal.coe_ofNat, ← ENNReal.smul_def]
  infer_instance

section PiProd

variable {ι : Type} [Fintype ι] {α β : ι → Type} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]

def piProdEquiv : ((i : ι) → α i × β i) ≃ᵐ ((i : ι) → α i) × ((i : ι) → β i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv x := rfl
  right_inv p := rfl
  measurable_toFun := (Measurable.of_eval fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    (Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

theorem measurePreserving_piProd (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (piProdEquiv (α := α) (β := β)) (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) := by
  have hf := (piProdEquiv (α := α) (β := β)).measurable
  refine ⟨hf, ?_⟩
  refine (Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (Measure.FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn)
    (Measure.FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn) ?_).symm
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hA' : ∀ i, MeasurableSet (A i) := fun i => hA i (Set.mem_univ i)
  have hB' : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)

  have hpre : (piProdEquiv (α := α) (β := β)) ⁻¹' (Set.univ.pi A ×ˢ Set.univ.pi B) =
      Set.univ.pi fun i => A i ×ˢ B i := by
    ext x
    simp [piProdEquiv, Set.mem_univ_pi, forall_and]
  rw [Measure.map_apply hf ((MeasurableSet.univ_pi hA').prod (MeasurableSet.univ_pi hB')), hpre,
    Measure.pi_pi, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.prod_prod _ _

end PiProd

section Loc

variable {n r : ℕ}

private theorem continuous_Dl_diagonal (l : ℕ) :
    Continuous (fun c : Fin (r + 1) → ℂ => Formalism.L2.SG.RealObj.Dl (Matrix.diagonal c) l) := by
  unfold Formalism.L2.SG.RealObj.Dl
  split_ifs with hl
  · exact (Continuous.matrix_diagonal continuous_id).matrix_submatrix _ _ |>.matrix_det
  · exact continuous_const

theorem gv_cont (T T' : ℝ) : Continuous (fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c)) := by
  unfold Formalism.L2.SG.RealObj.Gv
  exact ((continuous_Dl_diagonal _).norm.pow 2).sub (continuous_const.mul ((continuous_Dl_diagonal _).norm.pow 2))

theorem wtLoc_cont (k : ℕ) (T T' : ℝ) : Continuous (fun c : Fin (r + 1) → ℂ => wtLoc k T T' c) := by
  unfold wtLoc Formalism.L2.SG.RealObj.JacV
  refine ((gv_cont T T').pow _).mul (continuous_finsetProd _ fun l _ => ?_)
  unfold Formalism.L2.SG.RealObj.modC
  exact (((continuous_Dl_diagonal l).norm).pow 2).pow 2

theorem wtLoc_nonneg (k : ℕ) (T T' : ℝ) {c : Fin (r + 1) → ℂ} (hc : c ∈ GoodLoc (r := r) T T') :
    0 ≤ wtLoc k T T' c := by
  unfold wtLoc Formalism.L2.SG.RealObj.JacV
  exact mul_nonneg (pow_nonneg hc.2.le _) (Finset.prod_nonneg fun _ _ => sq_nonneg _)

theorem measurableSet_goodLoc (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have h1 : IsOpen {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {c : Fin (r + 1) → ℂ | 0 < Gv T T' (Matrix.diagonal c)} :=
    isOpen_lt continuous_const (gv_cont T T')
  rw [GoodLoc, Set.setOf_and]
  exact (h1.inter h2).measurableSet

def nuLoc (k : ℕ) (T T' C : ℝ) : Measure (Fin (r + 1) → ℂ) :=
  ((dcLoc (r := r)).restrict (GoodLoc (r := r) T T')).withDensity (fun c => ENNReal.ofReal (C * wtLoc k T T' c))

instance (k : ℕ) (T T' C : ℝ) : SigmaFinite (nuLoc (r := r) k T T' C) := by
  unfold nuLoc dcLoc
  exact SigmaFinite.withDensity_ofReal _

variable (ε : Fin n → Bool)

def phiLoc (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (x : (Fin (r + 1) → ℂ) × (Formalism.REAL.UJ ε × Formalism.REAL.UJ ε)) :
    Formalism.REAL.UJ ε :=
  x.2.1 * h x.1 * x.2.2⁻¹

theorem phiLoc_meas {h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} (hh : Measurable h) : Measurable (phiLoc ε h) := by
  unfold phiLoc
  exact ((measurable_fst.comp measurable_snd).mul (hh.comp measurable_fst)).mul
    (measurable_snd.comp measurable_snd).inv

theorem muG_eq_map (k : ℕ) (T T' : ℝ) (μS μS' : Measure (Formalism.REAL.UJ ε)) [SFinite μS] [SFinite μS']
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (hh : Measurable h) (C : ℝ)
    (hD : DisintLoc ε k T T' μS μS' h C) :
    Formalism.REAL.muG ε = ((nuLoc (r := r) k T T' C).prod (μS.prod μS')).map (phiLoc ε h) := by
  have hp := phiLoc_meas ε hh
  refine Measure.ext fun s hs => ?_
  have hφ : Measurable (s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞)) := measurable_const.indicator hs
  have hm : Measurable fun p => s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h p) := hφ.comp hp
  have hw : Measurable fun c : Fin (r + 1) → ℂ => ENNReal.ofReal (C * wtLoc k T T' c) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont k T T').measurable)
  have hg := hm.lintegral_prod_right' (ν := μS.prod μS')
  rw [← lintegral_indicator_one hs, hD _ hφ, Measure.map_apply hp hs, ← lintegral_indicator_one (hp hs)]
  have hind : ((phiLoc ε h) ⁻¹' s).indicator
      (1 : (Fin (r + 1) → ℂ) × (Formalism.REAL.UJ ε × Formalism.REAL.UJ ε) → ℝ≥0∞) =
      fun p => s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h p) := by
    funext p
    by_cases hx : phiLoc ε h p ∈ s <;> simp [hx]
  rw [hind, lintegral_prod _ hm.aemeasurable, nuLoc, lintegral_withDensity_eq_lintegral_mul _ hw hg]
  refine lintegral_congr fun c => ?_
  congr 1
  have hc : Measurable fun y : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h (c, y)) := hm.comp measurable_prodMk_left
  beta_reduce
  rw [lintegral_prod _ hc.aemeasurable]
  rfl

end Loc

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.FormRegularity

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames
  Formalism.MainNotions.S.Lat

section Mat

variable {r : ℕ}

def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.1)

theorem sgn_sq : sgn r * sgn r = 1 := by
  rw [sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem zhatO_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ZhatO Z = Z * sgn r := by
  ext a b
  rw [ZhatO, sgn, Matrix.mul_diagonal, mul_comm]

theorem isLoUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsLoUni L) : IsLoUni (L.map ψ) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, map_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, map_one]

theorem isLoUni_star {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsLoUni L) : IsLoUni (L.map star) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, star_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, star_one]

theorem isLoUni_sgnT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsUpUni U) :
    IsLoUni (sgn r * U * sgn r)ᵀ := by
  intro i j
  simp only [Matrix.transpose_apply, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [(h j i).1 hij]; ring
  · subst hij
    rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp

theorem det_lo {K : Type*} [Field K] {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => (h i j).1 (OrderDual.toDual_lt_toDual.1 hij))]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem det_up {K : Type*} [Field K] {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem isUpUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsUpUni U) : IsUpUni (U.map ψ) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, map_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, map_one]

theorem cancel {L A B U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L.det ≠ 0) (hU : U.det ≠ 0)
    (h : L * A * U = L * B * U) : A = B :=
  ((Matrix.isUnit_iff_isUnit_det L).2 (Ne.isUnit hL)).mul_left_cancel
    (((Matrix.isUnit_iff_isUnit_det U).2 (Ne.isUnit hU)).mul_right_cancel h)

theorem sgLo_eq {K : Type} [Field K] (L : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.L2.SG.PairVal.sgLo L = ∑ a : Fin r, L a.succ a.castSucc := by
  unfold Formalism.L2.SG.PairVal.sgLo
  rw [Fin.sum_univ_castSucc, dite_eq_right (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (by simp)]
  rfl

theorem sgUp_eq {K : Type} [Field K] (U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.L2.SG.PairVal.sgUp U = ∑ a : Fin r, U a.castSucc a.succ := by
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc, dite_eq_right (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (by simp)]
  rfl

theorem sgn_adj (a : Fin r) : (-1 : ℂ) ^ (r - a.castSucc.1) * (-1 : ℂ) ^ (r - a.succ.1) = -1 := by
  have h : r - a.castSucc.1 = (r - a.succ.1) + 1 := by
    simp only [Fin.coe_castSucc, Fin.val_succ]; omega
  rw [h, ← pow_add]
  exact Odd.neg_one_pow ⟨r - a.succ.1, by ring⟩

end Mat

theorem psiInf_neg {E : Type} [Field E] [NumberField E] (g : ℕ) (x : E) :
    Formalism.L2.SG.PairVal.psiInf g (-x) = (Formalism.L2.SG.PairVal.psiInf g x)⁻¹ := by
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [← Complex.exp_neg, map_neg]
  congr 1
  push_cast
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem zx_eq (u u' : D.what₂.Word) (δ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ZX X u u' 1 δ v = Zhat (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
      (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (δ v)) := by
  simp only [ZX, frm, FlagExtensionRegularity.famSc_one]

theorem psi_of_frame (u : D.what₂.Word) (s : X.B.I.Ginf)
    (P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ)
    (hP : ∀ v a, uMat (s v) *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) a =
       ∑ c, P v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) c)
    (y : D.host.E) (hy : ∀ v, ∑ a : Fin D.R.rS, (P v a.succ a.castSucc + star (P v a.succ a.castSucc)) =
       X.B.I.φ v (X.ιE.symm y) + star (X.B.I.φ v (X.ιE.symm y))) :
    X.psiInfU u s = Formalism.L2.SG.PairVal.psiInf X.B.g y := by
  have hfr := fun v => HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v
  have hrc : ∀ v a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (uMat (s v)) a = P v a.succ a.castSucc := fun v a =>
    HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ _ _ _ _ (hfr v).2.2.2.1 (fun a => ((hfr v).2.2.2.2.1 a).2) _ _ (hP v) a
  unfold HidaSetting.psiInfU psiInf psiR
  simp only [hrc, hy]
  rw [PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm y), RingEquiv.apply_symm_apply]

end Main

end Formalism.L2.SG.RealObj.FormRegularity
end
end
