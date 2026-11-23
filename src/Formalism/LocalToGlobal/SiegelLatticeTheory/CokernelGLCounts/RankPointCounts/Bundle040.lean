module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolKap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle004
public import Mathlib.GroupTheory.Index
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.Bundle030
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle027

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj Matrix

variable {K : Type*} [Field K] {N : ℕ} (p : Point K N)

abbrev cv (a : Fin N) : K := pval p.1 a.val

theorem cv_ne (a : Fin N) : cv p a ≠ 0 :=
  pval_ne p.1 (fun b hb => (p.2.1 b hb).1) a.val (by rw [p.2.2]; exact a.isLt)

theorem cv_pinv (a : Fin N) : cv p (pinv p a) = cv p a := pval_pinv p a

theorem pinv_inj {a b : Fin N} (h : pinv p a = pinv p b) : a = b := by
  have := congrArg (pinv p) h
  rwa [pinv_pinv, pinv_pinv] at this

theorem ptMat_mul_mono : ptMat p * mono (pinv p) (fun a => (cv p a)⁻¹) = 1 := by
  rw [ptMat_eq_mono]
  funext a b
  rw [mul_mono_apply _ (pinv_pinv p)]
  by_cases h : a = b
  · subst h
    simp only [mono, if_true, Matrix.one_apply_eq]
    rw [cv_pinv]; exact mul_inv_cancel₀ (cv_ne p a)
  · have hne : pinv p b ≠ pinv p a := fun e => h (pinv_inj p e).symm
    simp only [mono, hne, if_false, zero_mul, Matrix.one_apply_ne h]

theorem ptMat_inv : (ptMat p)⁻¹ = mono (pinv p) (fun a => (cv p a)⁻¹) :=
  Matrix.inv_eq_right_inv (ptMat_mul_mono p)

theorem conj_apply (M : Matrix (Fin N) (Fin N) K) (a b : Fin N) :
    ((ptMat p)⁻¹ * M * ptMat p) a b = (cv p a)⁻¹ * M (pinv p a) (pinv p b) * cv p b := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem conj'_apply (M : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (ptMat p * M * (ptMat p)⁻¹) i j = cv p i * M (pinv p i) (pinv p j) * (cv p j)⁻¹ := by
  rw [ptMat_inv]
  conv_lhs => rw [ptMat_eq_mono]
  rw [mul_mono_apply _ (pinv_pinv p), mono_mul_apply]
  simp only [cv, pval_pinv]

theorem ptMat_isUnit : IsUnit (ptMat p).det := Matrix.isUnit_det_of_right_inverse (ptMat_mul_mono p)

def IsBlockDiagonalMatrix (X : Matrix (Fin N) (Fin N) K) : Prop := ∀ a b : Fin N, blkOf p.1 a.val ≠ blkOf p.1 b.val → X a b = 0

theorem blk_lt_of_lt {a b : Fin N} (hab : a < b) (hne : blkOf p.1 a.val ≠ blkOf p.1 b.val) :
    blkOf p.1 a.val < blkOf p.1 b.val :=
  lt_of_le_of_ne (blkOf_mono p.1 a.val b.val (le_of_lt hab)) hne

theorem X_of_st {β b : Matrix (Fin N) (Fin N) K} (hβ : IsLoUni β) (hb : IsUpUni b) (hW : β * ptMat p * b = ptMat p) :
    (ptMat p)⁻¹ * β * ptMat p = b⁻¹ ∧ UpU ((ptMat p)⁻¹ * β * ptMat p) ∧ IsBlockDiagonalMatrix p ((ptMat p)⁻¹ * β * ptMat p) := by
  have hu := ptMat_isUnit p
  have h1 : (ptMat p)⁻¹ * β * ptMat p * b = 1 := by
    rw [show (ptMat p)⁻¹ * β * ptMat p * b = (ptMat p)⁻¹ * (β * ptMat p * b) by simp only [Matrix.mul_assoc], hW,
      Matrix.nonsing_inv_mul _ hu]
  have hX : (ptMat p)⁻¹ * β * ptMat p = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  refine ⟨hX, ?_, ?_⟩
  · rw [hX]; exact upU_inv hb
  · intro a c hne
    rw [conj_apply]
    rcases lt_or_gt_of_ne (show a ≠ c from fun e => hne (by rw [e])) with h | h
    · have hb' := (lt_of_blk_lt p a c (blk_lt_of_lt p h hne)).2
      rw [(hβ _ _).1 hb', mul_zero, zero_mul]
    · have hup : UpU ((ptMat p)⁻¹ * β * ptMat p) := by rw [hX]; exact upU_inv hb
      have := (hup a c).1 h
      rwa [conj_apply] at this

theorem st_of_X {X : Matrix (Fin N) (Fin N) K} (hX : UpU X) (hB : IsBlockDiagonalMatrix p X) :
    IsLoUni (ptMat p * X * (ptMat p)⁻¹) ∧ IsUpUni X⁻¹ ∧
      ptMat p * X * (ptMat p)⁻¹ * ptMat p * X⁻¹ = ptMat p ∧ (ptMat p * X * (ptMat p)⁻¹).det = 1 := by
  have hu := ptMat_isUnit p
  have hXd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  refine ⟨fun i j => ⟨fun hij => ?_, fun hij => ?_⟩, upU_inv hX, ?_, ?_⟩
  · rw [conj'_apply]
    by_cases hs : blkOf p.1 i.val = blkOf p.1 j.val
    · have := (pinv_lt_iff p i j hs).1 hij
      rw [(hX _ _).1 this, mul_zero, zero_mul]
    · have h2 := (lt_of_blk_lt p i j (blk_lt_of_lt p hij hs)).2
      have hs' : blkOf p.1 (pinv p i).val ≠ blkOf p.1 (pinv p j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact hs
      rw [hB _ _ hs', mul_zero, zero_mul]
  · subst hij
    rw [conj'_apply, (hX _ _).2 rfl, mul_one, mul_inv_cancel₀ (cv_ne p i)]
  · rw [Matrix.mul_assoc (ptMat p * X), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXd, Matrix.mul_one]
  · rw [Matrix.det_mul, Matrix.det_mul, upU_det hX, mul_one, ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hu,
      Matrix.det_one]

end Formalism.L2.SG.Pf.BlockPermutation
end
end

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem det_upper {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular id := fun i j hij => h1 i j hij
  rw [Matrix.det_of_upperTriangular hb]
  simp [h2]

theorem det_lower {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular OrderDual.toDual := fun i j hij => h1 i j hij
  rw [Matrix.det_of_lowerTriangular X hb]
  simp [h2]

theorem lmat_mem_R (hs : (Z.M p).split = some g) {x y : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O)
    (hy : y ∈ (Z.M p).L.O)
    (hc : ∃ o ∈ (Z.M p).L.O, x - (Z.M p).L.cj y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o) :
    g.e.symm ((g.e x).1, (g.e y).2) ∈ (Z.M p).R := by
  obtain ⟨o, ho, he⟩ := hc
  refine mem_R_of Z p g hs (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hx).1)
    (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hy).2) ⟨(g.e o).1, (comp_mem Z p g ho).1, ?_⟩
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun t => (g.e t).1) he
  simp only [map_sub, map_mul, AlgEquiv.commutes, g.e_cj, Prod.fst_sub, Prod.swap_prod_mk, Prod.fst_mul,
    Prod.fst_swap, Prod.algebraMap_apply] at h
  rw [h]
  rfl

end ModeG

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

def IntM (X : Formalism.L2.SG.LsDatumB.MatP D p) : Prop := ∀ i j, X i j ∈ (Z.M p).L.O

def Cq (X : Formalism.L2.SG.LsDatumB.MatP D p) : Prop :=
  ∀ i j, ∃ o ∈ (Z.M p).L.O, X i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o

theorem cq_mul_left {A X : Formalism.L2.SG.LsDatumB.MatP D p} (hA : IntM Z p A) (hX : Cq Z p g X) : Cq Z p g (A * X) := fun i j => by
  choose o ho he using hX
  refine ⟨∑ k, A i k * o k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (ho k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k j]
  ring

theorem cq_mul_right {X B : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) (hB : IntM Z p B) : Cq Z p g (X * B) := fun i j => by
  choose o ho he using hX
  refine ⟨∑ k, o i k * B k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ho i k) (hB k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he i k]
  ring

theorem cq_neg {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g (-X) := fun i j => by
  obtain ⟨o, ho, he⟩ := hX i j
  exact ⟨-o, Subring.neg_mem _ ho, by rw [Matrix.neg_apply, he, mul_neg]⟩

theorem cq_transpose {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g Xᵀ := fun i j => hX j i

theorem cq_map_cj {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g (X.map (Z.M p).L.cj) := fun i j => by
  obtain ⟨o, ho, he⟩ := hX i j
  refine ⟨(Z.M p).L.cj o, PI.LocCntLat.GC.cj_mem_O _ ho, ?_⟩
  rw [Matrix.map_apply, he, map_mul, AlgEquiv.commutes]

theorem map_cj_mul (A B : Formalism.L2.SG.LsDatumB.MatP D p) : (A * B).map (Z.M p).L.cj = A.map (Z.M p).L.cj * B.map (Z.M p).L.cj := by
  ext i j

  simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_cj_one : (1 : Formalism.L2.SG.LsDatumB.MatP D p).map (Z.M p).L.cj = 1 := by
  ext i j
  simp [Matrix.one_apply, apply_ite]

theorem map_cj_inv (A : Formalism.L2.SG.LsDatumB.MatP D p) (hA : IsUnit A.det) : (A⁻¹).map (Z.M p).L.cj = (A.map (Z.M p).L.cj)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← map_cj_mul, Matrix.nonsing_inv_mul A hA, map_cj_one]

end Cong

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol MeasureTheory

theorem typFacts_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u u' : D.what₂.Word) : TypFacts X u u' := by
  apply typFacts_of (h1 := gSplitX_holds X) (h3 := Formalism.L2.SG.LocVolKap.kapX X hb u u')
  exact tCongX X u u'

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

theorem index_eq_relIndex (hD : Data W S N' K π) :
    ((Hk W K g).map (πk W S N' K π hD)).index = ((Hs W K g).map π).relIndex (K ⊓ S) := by
  let e : ↥(K ⊓ S) →* ↥(Ak S K) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simp only [Ak, Subgroup.mem_subgroupOf]; exact x.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Surjective e := fun a =>
    ⟨⟨a.1.1, a.1.2, by have h := a.2; simp only [Ak, Subgroup.mem_subgroupOf] at h; exact h⟩, rfl⟩
  rw [← Subgroup.index_comap_of_surjective _ he]
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨k.1, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hk
    · have h2 := congrArg (fun y : ↥(Ak S K) => ((y : ↥K) : G)) hkx
      simpa [πk, e] using h2
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy.1⟩, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hy
    · apply Subtype.ext
      apply Subtype.ext
      simpa [πk, e] using hyx

theorem card_cells' (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hs W K g).map π).relIndex (K ⊓ S) := (card_cells W S N' K π g hD).trans (index_eq_relIndex W S N' K π g hD)

end Formalism.L2.SG.Pf.CountAb
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def orbR (M : Loc.Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {Z' | ∃ l ρ : Matrix (Fin n) (Fin n) E, Formalism.MainNotions.S.TieN.IntLow M l ∧ Formalism.MainNotions.S.TieN.IntUp M ρ ∧ Z' = l * Z * ρ}

def zAt {m : ℕ} (a : Loc.Pt E (m + 1)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
  Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2

def muA (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) :
    Measure ((Loc.IL (m + 1) → E) × (Loc.IN a → E)) :=
  (Measure.pi fun _ : Loc.IL (m + 1) => M.mu).prod (Measure.pi fun _ : Loc.IN a => M.mu)

def IsZO (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) :
    Prop :=
  ∃ xy, (∀ i j, zAt a xy i j ∈ M.R) ∧ O = orbR M (zAt a xy)

def wtZ (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) : ℝ :=
  (muA M a {xy | zAt a xy ∈ O}).toReal

def OrbCut (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : Prop :=
  ∀ (k : ℂ) (V : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E) → ℂ),
    (∀ O, ¬ IsZO M a O → V O = 0) →
    (∀ O, IsZO M a O → ∃ xy, zAt a xy ∈ O ∧ V O = k * M.bbIntegrand a c xy * (wtZ M a O : ℂ)) →
    HasSum V (k * M.BB a c) ∧ Summable (fun O => ‖V O‖)

end Loc

section Shift

variable {D : Formalism.BasicNotions.D7}

def shM (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : MatP D p :=
  Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0

def ModShift (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ a, modPt δ T T' p w = some a → a.mat = modMat δ T T' p w + shM δ T T' p w

def NAutNe (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) : Prop :=
  ∀ c : (M p).Cls D.R.rS, (M p).nAut c ≠ 0

end Shift

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG2

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_low {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, a < b → lmat Z p g l ρ a b = 0) ∧ ∀ a, lmat Z p g l ρ a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hl0 a b h, hρ0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem corner_fix {L R C : Formalism.L2.SG.LsDatumB.MatP D p} (hL0 : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1)
    (hR0 : ∀ a b, b < a → R a b = 0) (hR1 : ∀ a, R a a = 1)
    (hC : ∀ a b, ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) → C a b = 0) : L * C * R = C := by
  have hLl : ∀ a, L a (Fin.last D.R.rS) = if a = Fin.last D.R.rS then 1 else 0 := by
    intro a
    split_ifs with h
    · subst h; exact hL1 _
    · exact hL0 a _ (lt_of_le_of_ne (Fin.le_last a) h)
  have hRl : ∀ b, R (Fin.last D.R.rS) b = if b = Fin.last D.R.rS then 1 else 0 := by
    intro b
    split_ifs with h
    · subst h; exact hR1 _
    · exact hR0 _ b (lt_of_le_of_ne (Fin.le_last b) h)
  ext a b
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last D.R.rS) (fun d _ hd => by
      rw [Finset.sum_eq_zero (fun c _ => by rw [hC c d (fun h => hd h.2), mul_zero]), zero_mul]) (by simp),
    Finset.sum_eq_single (Fin.last D.R.rS) (fun c _ hc => by rw [hC c _ (fun h => hc h.1), mul_zero]) (by simp),
    hLl a, hRl b]
  by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS
  · subst ha; subst hb; simp
  · rw [if_neg hb, mul_zero, hC a b (fun h => hb h.2)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]
  · rw [if_neg ha, zero_mul, zero_mul, hC a b (fun h => ha h.1)]

end ModeG2

end Formalism.L2.SG.Pf.FibQ
end
end

section

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting NumberField

def NOfibLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

theorem nofib_of (hL : NOfibLat) : NOfib := by
  intro D X u
  obtain ⟨h1, h2, h3⟩ := nOinf_closed_under_mul_inv X u
  exact ⟨h1, h2, h3, hL X u⟩

end Formalism.L2.SG.Pf.NcReal.JX
end
