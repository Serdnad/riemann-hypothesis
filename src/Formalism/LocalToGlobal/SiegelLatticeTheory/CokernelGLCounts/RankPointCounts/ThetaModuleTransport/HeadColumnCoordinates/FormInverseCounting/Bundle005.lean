module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.MemHeadColsIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.DetAddCor
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.MemSpanOfSharpG
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem mem_relC_of_mk (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (t t' : O) (u u' : Fin (r + 1) → O) (α β : O)
    (h : (Submodule.Quotient.mk u : MbMod Z) = α • bCls Z - (t * β) • eCl Z)
    (h' : (Submodule.Quotient.mk u' : MbMod (cjT O cj hO Z)) =
      β • bCls (cjT O cj hO Z) - (t' * α) • eCl (cjT O cj hO Z)) :
    (Sum.elim u u' : Ix r → O) ∈ relC O cj (Z.map O.subtype) t t' := by
  rw [bCls, eCl, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h h'
  obtain ⟨w, hw, hwe⟩ := (mem_headCols_iff _ _).1 h
  obtain ⟨v, hv, hve⟩ := (mem_headCols_iff _ _).1 h'
  rw [mem_relC_iff O cj hO Z t t']
  refine ⟨v + β • Pi.single (Fin.last r) 1, w + α • Pi.single (Fin.last r) 1, ?_, ?_⟩
  · have hl : ((v + β • Pi.single (Fin.last r) 1 : Fin (r + 1) → O)) (Fin.last r) = β := by simp [hv]
    rw [hl, Matrix.mulVec_add, Matrix.mulVec_smul, ← bvec_eq, ← hwe]
    show u = _
    abel
  · have hl : ((w + α • Pi.single (Fin.last r) 1 : Fin (r + 1) → O)) (Fin.last r) = α := by simp [hw]
    rw [hl, Matrix.mulVec_add, Matrix.mulVec_smul, ← bvec_eq, ← hve]
    show u' = _
    abel

theorem mem_relC_of_K (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (t t' : O) (u u' : Fin (r + 1) → O) (hu : u ∈ headCols Z) (hu' : u' ∈ headCols (cjT O cj hO Z)) :
    (Sum.elim u u' : Ix r → O) ∈ relC O cj (Z.map O.subtype) t t' := by
  apply mem_relC_of_mk O cj hO Z t t' u u' 0 0
  · rw [(Submodule.Quotient.mk_eq_zero _).2 hu]; simp
  · rw [(Submodule.Quotient.mk_eq_zero _).2 hu']; simp

theorem gramC_herm (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hT : cj T = T) (hT' : cj T' = T') (k j : Ix r) :
    cj (gramC cj Z T T' k j) = gramC cj Z T T' j k := by
  rcases k with a | a <;> rcases j with b | b <;>
    simp [gramC, hcj, apply_ite cj, hT, hT', and_comm]

theorem formC_add_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y Y' W : Ix r → O) :
    formC O cj Z T T' (Y + Y') W = formC O cj Z T T' Y W + formC O cj Z T T' Y' W := by
  simp [formC, add_mul, Finset.sum_add_distrib]

theorem formC_add_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W W' : Ix r → O) :
    formC O cj Z T T' Y (W + W') = formC O cj Z T T' Y W + formC O cj Z T T' Y W' := by
  simp [formC, mul_add, Finset.sum_add_distrib]

theorem formC_sub_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y Y' W : Ix r → O) :
    formC O cj Z T T' (Y - Y') W = formC O cj Z T T' Y W - formC O cj Z T T' Y' W := by
  have := formC_add_left O cj Z T T' (Y - Y') Y' W
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem formC_sub_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W W' : Ix r → O) :
    formC O cj Z T T' Y (W - W') = formC O cj Z T T' Y W - formC O cj Z T T' Y W' := by
  have := formC_add_right O cj Z T T' Y (W - W') W'
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem formC_rel_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hG : IsUnit (gramC cj Z T T').det) (hO : ∀ x ∈ O, cj x ∈ O) (Y W : Ix r → O)
    (hY : Y ∈ relC O cj Z T T') : formC O cj Z T T' Y W ∈ O := by
  obtain ⟨c, hc⟩ := hY
  rw [formC_of_rel O cj Z T T' hG Y W (fun i => (c i : E)) hc]
  exact O.sum_mem fun j _ => O.mul_mem (c j).2 (hO _ (W j).2)

theorem formC_rel_right (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hT : cj T = T) (hT' : cj T' = T')
    (hG : IsUnit (gramC cj Z T T').det) (hO : ∀ x ∈ O, cj x ∈ O) (Y W : Ix r → O)
    (hW : W ∈ relC O cj Z T T') : formC O cj Z T T' Y W ∈ O := by
  obtain ⟨d, hd⟩ := hW
  have hinv := Matrix.nonsing_inv_mul (gramC cj Z T T') hG
  have key : ∀ i, ∑ j, (gramC cj Z T T')⁻¹ i j * cj (W j : E) = cj (d i : E) := by
    intro i
    have h1 : ∀ j, cj (W j : E) = ∑ k, cj (d k : E) * gramC cj Z T T' j k := by
      intro j

      rw [hd j, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_mul, gramC_herm cj hcj Z T T' hT hT']
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ k, ∑ j, (gramC cj Z T T')⁻¹ i j * (cj (d k : E) * gramC cj Z T T' j k) =
        cj (d k : E) * ((gramC cj Z T T')⁻¹ * gramC cj Z T T') i k := by
      intro k
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [h2, hinv, Matrix.one_apply]
    simp
  unfold formC
  have h3 : ∀ i, ∑ j, (Y i : E) * (gramC cj Z T T')⁻¹ i j * cj (W j : E) = (Y i : E) * cj (d i : E) := by
    intro i
    rw [← key i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h3]
  exact O.sum_mem fun i _ => O.mul_mem (Y i).2 (hO _ (d i).2)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem corner_mul {K : Type} [Field K] {r : ℕ} (a d : K) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then d else 0) * X *
      (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then a else 0) =
      Matrix.of fun i j => cor r i j (d * X (Fin.last r) (Fin.last r) * a) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, cor]
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;>
    simp [hi, hj, Finset.sum_ite_eq', Finset.sum_ite_eq, mul_assoc]

theorem det_corner_blocks_ne {K : Type} [Field K] {r : ℕ} (a d : K) (B C : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hB : B.det ≠ 0)
    (h : B.det * C.det - a * d * ((B.submatrix Fin.castSucc Fin.castSucc).det *
      (C.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0) :
    (Matrix.fromBlocks (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then a else 0) B C
      (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then d else 0)).det ≠ 0 := by
  set A : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then a else 0
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then d else 0
  set J : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K := Matrix.fromBlocks 0 1 1 0
  have hJ : Matrix.fromBlocks B A D C * J = Matrix.fromBlocks A B C D := by
    simp [J, Matrix.fromBlocks_multiply]
  have hJJ : J * J = 1 := by
    simp [J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hJd : J.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [← hJ, Matrix.det_mul]
  refine mul_ne_zero ?_ hJd
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, corner_mul]
  have hsub : C - (Matrix.of fun i j => cor r i j (d * B⁻¹ (Fin.last r) (Fin.last r) * a)) =
      C + Matrix.of fun i j => cor r i j (-(d * B⁻¹ (Fin.last r) (Fin.last r) * a)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, cor]
    split_ifs <;> ring
  have hinv : B⁻¹ (Fin.last r) (Fin.last r) = (B.submatrix Fin.castSucc Fin.castSucc).det / B.det := by
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last,
      Ring.inverse_eq_inv', smul_eq_mul]
    have h2 : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
      rw [Fin.val_last]; exact Even.neg_one_pow ⟨r, rfl⟩
    rw [h2, one_mul, div_eq_inv_mul]
  rw [hsub, det_add_cor, hinv]
  intro h0
  apply h
  have : B.det * (C.det + -(d * ((B.submatrix Fin.castSucc Fin.castSucc).det / B.det) * a) *
      (C.submatrix Fin.castSucc Fin.castSucc).det) = B.det * C.det - a * d * ((B.submatrix Fin.castSucc Fin.castSucc).det *
      (C.submatrix Fin.castSucc Fin.castSucc).det) := by
    field_simp
    ring
  rw [← this, h0]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem splitSecondProj_algebraMap (a : F) : ph2 g (algebraMap F E a) = a := by
  show (g.e (algebraMap F E a)).2 = a
  rw [AlgEquiv.commutes]
  rfl

theorem ph2_cj_eq_ph1 (x : E) : ph2 g (M.L.cj x) = ph1 g x := by
  show (g.e (M.L.cj x)).2 = (g.e x).1
  rw [g.e_cj]
  rfl

theorem gram_map_secondProj_transpose (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).map
        (ph2 g) =
      ((gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
        (algebraMap F E T')).map (ph1 g)).transpose := by
  have hcor : ∀ (φ : E →+* F) (a b : Fin (r + 1)) (c : E), φ (cor r a b c) = cor r a b (φ c) := by
    intro φ a b c
    unfold cor
    split_ifs <;> simp
  have hcorS : ∀ (a b : Fin (r + 1)) (c : F), cor r a b c = cor r b a c := by
    intro a b c
    unfold cor
    simp only [and_comm]
  have h1 : ∀ x, ph1 g (M.L.cj x) = ph2 g x := by
    intro x
    show (g.e (M.L.cj x)).1 = (g.e x).2
    rw [g.e_cj]
    rfl
  have ha1 : ∀ a : F, ph1 g (algebraMap F E a) = a := by
    intro a
    show (g.e (algebraMap F E a)).1 = a
    rw [AlgEquiv.commutes]
    rfl
  unfold gramG
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  congr 1
  · ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hcor, map_neg, splitSecondProj_algebraMap, ha1]
    exact hcorS _ _ _
  all_goals
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hcor, map_mul, map_add (f := _), map_neg,
      map_sub, RingHom.coe_coe, splitSecondProj_algebraMap, ph2_cj_eq_ph1, h1, ha1]
    first | ring1 | (rw [hcorS]; done) | (rw [hcorS]; ring1)

theorem det_pM_ne (x : F) (hx : x ≠ 0) : (pM r x⁻¹).det ≠ 0 := by
  unfold pM
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (inv_ne_zero hx)

theorem gramUnit_split_holds : GramUnitG := by
  intro F _ _ _ E _ _ _ _ M g r T T' TT Zh Z Zσ h
  obtain ⟨-, -, -, -, -, hdet, hx⟩ := h
  have hq := q_ne g
  have h1 : ph1 g (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det ≠ 0 := by
    rw [det_ph, map_gramG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero (mul_ne_zero (det_pM_ne _ hq) ?_) (det_pM_ne _ hq)
    unfold gHat
    obtain ⟨-, hd2⟩ := (isUnit_iff_ph (g := g) _).1 hdet
    obtain ⟨hx1, -⟩ := (isUnit_iff_ph (g := g) _).1 hx
    refine det_corner_blocks_ne (-T) (-T') _ _ (by rwa [← det_ph]) ?_
    have hm : ((Zh.map (ph1 g)).transpose.submatrix Fin.castSucc Fin.castSucc).det =
        ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [det_ph]
      exact Matrix.det_transpose _
    rw [hm, Matrix.det_transpose]
    simp only [Matrix.submatrix_map, ← det_ph]
    convert hx1 using 1
    simp only [map_sub, map_mul, splitFirstProj_conj, splitFirstProj_algebraMap]
    ring
  have h2 : ph2 g (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det ≠ 0 := by
    rw [det_ph, gram_map_secondProj_transpose, Matrix.det_transpose, ← det_ph]
    exact h1
  exact (isUnit_iff_ph (g := g) _).2 ⟨h1, h2⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
