module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.CoordU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DlUnitOfHead
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.LocCntUGOf
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def p1 (g : SplitG M.L) : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom

def p2 (g : SplitG M.L) : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom

theorem adeleInfiniteComponent_apply (x : E) : p1 g x = (g.e x).1 := rfl
theorem adele_ext_components (x : E) : p2 g x = (g.e x).2 := rfl

theorem map_inv_of {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n] (f : E →+* K)
    (A : Matrix n n E) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

theorem inv_last {K : Type} [CommRing K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    A⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse A.det * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp

theorem kap_common {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hk : KapEq Zh₁ Zh₂)
    (h₁ : IsUnit Zh₁.det) (h₂ : IsUnit Zh₂.det) :
    Zh₁⁻¹ (Fin.last r) (Fin.last r) = Zh₂⁻¹ (Fin.last r) (Fin.last r) := by
  rw [inv_last, inv_last]
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  unfold KapEq at hk
  rw [← hu₁, ← hu₂] at hk ⊢
  simp only [Ring.inverse_unit]
  apply (u₁ * u₂).isUnit.mul_left_cancel
  push_cast
  calc (u₁ : E) * u₂ * (↑u₁⁻¹ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)
      = u₂ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det * (u₁ * ↑u₁⁻¹) := by ring
    _ = u₂ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det := by rw [Units.mul_inv, mul_one]
    _ = u₁ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det := hk.symm
    _ = u₁ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det * (u₂ * ↑u₂⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (u₁ : E) * u₂ * (↑u₂⁻¹ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det) := by ring

variable (hs : M.split = some g)
include hs

theorem zzMinus_firstProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (p1 g) = (g.q : F)⁻¹ • Zh.map (p1 g) := by
  ext b a
  simp only [ZZm, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), Matrix.smul_apply,
    smul_eq_mul, adeleInfiniteComponent_apply]
  rw [zz_comp hs, e_cor]
  simp only [ind, AlgEquiv.apply_symm_apply]
  split_ifs <;> ring

theorem zzMinus_secondProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (p2 g) = -(g.q : F)⁻¹ • (Zh.map (p2 g)).transpose := by
  ext b a
  simp only [ZZm, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), Matrix.smul_apply,
    smul_eq_mul, adele_ext_components, Matrix.transpose_apply]
  rw [zz_comp hs, e_cor]
  simp only [ind, AlgEquiv.apply_symm_apply]
  split_ifs <;> ring

theorem det_map_unit {n : Type} [Fintype n] [DecidableEq n] (f : E →+* F) (A : Matrix n n E)
    (hA : IsUnit A.det) : IsUnit (A.map f).det := by
  have := hA.map f
  rwa [RingHom.map_det] at this

theorem zm_unit {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F) :
    IsUnit (ZZm g Zh T T').det := by
  have hq := q_ne g
  apply Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.isUnit_of_comp g
  · rw [← adeleInfiniteComponent_apply, RingHom.map_det]
    change (((ZZm g Zh T T').map (p1 g))).det ≠ 0
    rw [zzMinus_firstProj hs, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq)) (det_map_unit hs (p1 g) Zh hZh).ne_zero
  · rw [← adele_ext_components, RingHom.map_det]
    change (((ZZm g Zh T T').map (p2 g))).det ≠ 0
    rw [zzMinus_secondProj hs, Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq))) (det_map_unit hs (p2 g) Zh hZh).ne_zero

theorem inv_smul_q {n : Type} [Fintype n] [DecidableEq n] (c : F) (hc : c ≠ 0) (X : Matrix n n F)
    (hX : IsUnit X.det) : (c⁻¹ • X)⁻¹ = c • X⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul _ hX]

theorem inv_smul_qT {n : Type} [Fintype n] [DecidableEq n] (c : F) (hc : c ≠ 0) (X : Matrix n n F)
    (hX : IsUnit X.det) : (-c⁻¹ • X.transpose)⁻¹ = -c • (X⁻¹).transpose := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, mul_inv_cancel₀ hc, one_smul,
    ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hX, Matrix.transpose_one]

theorem lastCoordinate_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
    (l : Fin (r + 1) → M.R) :
    p1 g (laG (ZZm g Zh T T') l) = ∑ b, (g.q : F) * (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (l b) := by
  have hq := q_ne g

  simp only [laG, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := congrFun (congrFun (map_inv_of (p1 g) _ (zm_unit hs hZh T T')) (Fin.last r)) b
  rw [Matrix.map_apply] at h
  rw [h, zzMinus_firstProj hs, inv_smul_q hs _ hq _ (det_map_unit hs (p1 g) Zh hZh), Matrix.smul_apply, smul_eq_mul]

theorem lastCoordinate_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
    (l : Fin (r + 1) → M.R) :
    p2 g (laG (ZZm g Zh T T') l) = ∑ b, -(g.q : F) * (Zh.map (p2 g))⁻¹ b (Fin.last r) * p2 g (l b) := by
  have hq := q_ne g

  simp only [laG, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := congrFun (congrFun (map_inv_of (p2 g) _ (zm_unit hs hZh T T')) (Fin.last r)) b
  rw [Matrix.map_apply] at h
  rw [h, zzMinus_secondProj hs, inv_smul_qT hs _ hq _ (det_map_unit hs (p2 g) Zh hZh), Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply]

theorem lambda_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p1 g (lamC Zh y) = ∑ b, (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (y b) := by

  simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem lambda_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p2 g (lamC Zh y) = ∑ b, (Zh.map (p2 g))⁻¹ (Fin.last r) b * p2 g (y b) := by

  simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

theorem firstProj_conj_split (x : E) : p1 g ((M.L.cj : E →+* E) x) = p2 g x := by
  rw [adeleInfiniteComponent_apply, adele_ext_components, e_cjR]

theorem secondProj_conj_split (x : E) : p2 g ((M.L.cj : E →+* E) x) = p1 g x := by
  rw [adeleInfiniteComponent_apply, adele_ext_components, e_cjR]

theorem lambdaStar_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p1 g (lamStarC (M.L.cj : E →+* E) Zh y) = ∑ b, (Zh.map (p2 g))⁻¹ b (Fin.last r) * p1 g (y b) := by

  simp only [lamStarC, map_sum, map_mul, firstProj_conj_split hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

theorem lambdaStar_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p2 g (lamStarC (M.L.cj : E →+* E) Zh y) = ∑ b, (Zh.map (p1 g))⁻¹ b (Fin.last r) * p2 g (y b) := by

  simp only [lamStarC, map_sum, map_mul, secondProj_conj_split hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem corner_inverse_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) :
    p1 g (Zh⁻¹ (Fin.last r) (Fin.last r)) = (Zh.map (p1 g))⁻¹ (Fin.last r) (Fin.last r) := by
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem corner_inverse_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) :
    p2 g (Zh⁻¹ (Fin.last r) (Fin.last r)) = (Zh.map (p2 g))⁻¹ (Fin.last r) (Fin.last r) := by
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem ite_ind (a b : Fin (r + 1)) (x : F) :
    (if b = Fin.last r ∧ a = Fin.last r then x else 0) = ind r a b * x := by
  unfold ind
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

theorem sum_mul_ind (x : Fin (r + 1) → F) (b : Fin (r + 1)) (u : F) :
    ∑ a, x a * (ind r a b * u) = if b = Fin.last r then x (Fin.last r) * u else 0 := by
  have : ∑ a, x a * (ind r a b * u) = (∑ a, x a * ind r a b) * u := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
  rw [this, sum_ind_l]
  split_ifs <;> simp

section Rows

variable (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (c : Ix r → M.L.O)

abbrev GG : Matrix (Ix r) (Ix r) E :=
  gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')

theorem row_inl (b : Fin (r + 1)) :
    g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inl b)) =
      (∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).1 * (g.e (c (Sum.inr a) : E)).1 +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inr (Fin.last r)) : E)).1 -
            T * (g.e (c (Sum.inl (Fin.last r)) : E)).1 else 0),
        ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).2 * (g.e (c (Sum.inr a) : E)).2 +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inr (Fin.last r)) : E)).2 -
            T * (g.e (c (Sum.inl (Fin.last r)) : E)).2 else 0)) := by

  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, e_gram]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.fst_mul]
    have h1 : ∑ a, (g.e (c (Sum.inl a) : E)).1 * (ind r a b * -T) =
        if b = Fin.last r then (g.e (c (Sum.inl (Fin.last r)) : E)).1 * -T else 0 := sum_mul_ind _ _ _
    have h2 : ∑ a, (g.e (c (Sum.inr a) : E)).1 * ((g.q : F)⁻¹ * ((g.e (Zh b a)).1 + ind r a b * T)) =
        ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).1 * (g.e (c (Sum.inr a) : E)).1 +
          ∑ a, (g.e (c (Sum.inr a) : E)).1 * (ind r a b * ((g.q : F)⁻¹ * T)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, h2, sum_mul_ind]
    split_ifs <;> ring
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.snd_mul]
    have h1 : ∑ a, (g.e (c (Sum.inl a) : E)).2 * (ind r a b * -T) =
        if b = Fin.last r then (g.e (c (Sum.inl (Fin.last r)) : E)).2 * -T else 0 := sum_mul_ind _ _ _
    have h2 : ∑ a, (g.e (c (Sum.inr a) : E)).2 * ((g.q : F)⁻¹ * ((g.e (Zh b a)).2 + ind r a b * T)) =
        ∑ a, (g.q : F)⁻¹ * (g.e (Zh b a)).2 * (g.e (c (Sum.inr a) : E)).2 +
          ∑ a, (g.e (c (Sum.inr a) : E)).2 * (ind r a b * ((g.q : F)⁻¹ * T)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, h2, sum_mul_ind]
    split_ifs <;> ring

theorem row_inr (b : Fin (r + 1)) :
    g.e (∑ i, (c i : E) * GG (g := g) Zh T T' i (Sum.inr b)) =
      (∑ a, ((g.q : F)⁻¹ * (g.e (Zh a b)).2 * (g.e (c (Sum.inl a) : E)).1 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2) * (g.e (c (Sum.inr a) : E)).1) +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inl (Fin.last r)) : E)).1 -
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T') * (g.e (c (Sum.inr (Fin.last r)) : E)).1 else 0),
        ∑ a, ((g.q : F)⁻¹ * (g.e (Zh a b)).1 * (g.e (c (Sum.inl a) : E)).2 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1) * (g.e (c (Sum.inr a) : E)).2) +
          (if b = Fin.last r then (g.q : F)⁻¹ * T * (g.e (c (Sum.inl (Fin.last r)) : E)).2 -
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T') * (g.e (c (Sum.inr (Fin.last r)) : E)).2 else 0)) := by

  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_mul, e_gram]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.fst_mul]
    have h : ∀ a, (g.e (c (Sum.inl a) : E)).1 * ((g.q : F)⁻¹ * ((g.e (Zh a b)).2 + ind r a b * T)) +
        (g.e (c (Sum.inr a) : E)).1 * ((g.q : F)⁻¹ * (g.q : F)⁻¹ *
          (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2 - ind r a b * (T + T'))) =
        ((g.q : F)⁻¹ * (g.e (Zh a b)).2 * (g.e (c (Sum.inl a) : E)).1 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2) * (g.e (c (Sum.inr a) : E)).1) +
          ((g.e (c (Sum.inl a) : E)).1 * (ind r a b * ((g.q : F)⁻¹ * T)) +
            (g.e (c (Sum.inr a) : E)).1 * (ind r a b * (-((g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T'))))) := by
      intro a; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => h a]
    simp only [Finset.sum_add_distrib, sum_mul_ind]
    split_ifs <;> ring
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.snd_mul]
    have h : ∀ a, (g.e (c (Sum.inl a) : E)).2 * ((g.q : F)⁻¹ * ((g.e (Zh a b)).1 + ind r a b * T)) +
        (g.e (c (Sum.inr a) : E)).2 * ((g.q : F)⁻¹ * (g.q : F)⁻¹ *
          (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1 - ind r a b * (T + T'))) =
        ((g.q : F)⁻¹ * (g.e (Zh a b)).1 * (g.e (c (Sum.inl a) : E)).2 +
            (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1) * (g.e (c (Sum.inr a) : E)).2) +
          ((g.e (c (Sum.inl a) : E)).2 * (ind r a b * ((g.q : F)⁻¹ * T)) +
            (g.e (c (Sum.inr a) : E)).2 * (ind r a b * (-((g.q : F)⁻¹ * (g.q : F)⁻¹ * (T + T'))))) := by
      intro a; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => h a]
    simp only [Finset.sum_add_distrib, sum_mul_ind]
    split_ifs <;> ring

end Rows

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

section StepsT

def AlgGUT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    IsUnit (Zh₁.submatrix Fin.castSucc Fin.castSucc).det → IsUnit (Zh₂.submatrix Fin.castSucc Fin.castSucc).det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

end StepsT

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem thetaMbeG_of_coordT (h1 : CoordGU) (h2 : AlgGUT) (M : Model F E) (r n : ℕ) : ThetaMbeG M r n := by
  intro hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂ hu₂
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hmode
  have hg := hyp.1
  have hr2 : IsUnit (H.Dl f₂ f₂' r) := by
    apply dl_unit_of_head hs H f₂ f₂' t₁.T t₁.T'
    have : headDet M Z₂ = ((HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T').submatrix Fin.castSucc
        Fin.castSucc).det := by
      unfold headDet; rw [e₂]
    rw [← this]; exact hu₂
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hunit : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    have : IsUnit (H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1)) := by rw [hrel]; exact hr2.mul (dl_succ_unit hyp)
    exact isUnit_of_mul_isUnit_right this
  have hzz : ∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R := by
    intro a b
    have := (Z₂ a b).2
    rw [show ((Z₂ a b : M.R) : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b from
      congrFun (congrFun e₂ a) b] at this
    exact this
  have hG1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
      (H.Dl t₁.f t₁.f' r * M.L.cj (H.Dl t₁.f t₁.f' r))) := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hg.1.2.2.2.2.1
    unfold HermSp.Gdet HermSp.normE at hG
    apply isUnit_of_cj_fixed g _ hG
    simp only [map_sub, map_mul, M.L.cj_cj, cj_alg]
    ring
  rw [h1 F E M g hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hunit hzz]
  refine h2 F E M g hs r t₁.T t₁.T' (hg.1.2.2.2.2.2 g hs).1 (hg.1.2.2.2.2.2 g hs).2.1 _ _ Z₁ Z₂ e₁ e₂
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hyp.1.1.2.1.2.2.2.1
  · rw [← dl_full]; exact dl_succ_unit hyp
  · rw [← dl_full]; exact hunit
  · rw [← dl_eq_det]; exact hD
  · rw [← dl_eq_det]; exact hr2
  · rw [← dl_full, ← dl_full, ← dl_eq_det, ← dl_eq_det]
    linear_combination hrel.symm
  · rw [← dl_full, ← dl_eq_det]
    exact hG1
  · rw [← dl_full, ← dl_eq_det]
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hA : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) :=
      (dl_succ_unit hyp).mul ((dl_succ_unit hyp).map M.L.cj)
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hunit.mul (hunit.map M.L.cj)
    have : IsUnit ((H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
        (H.Dl f₂ f₂' r * M.L.cj (H.Dl f₂ f₂' r))) * (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [key]; exact hB.mul hG1
    exact isUnit_of_mul_isUnit_left this

theorem locCntUG_of_algGUT (h : AlgGUT) : Formalism.L2.SG.LocalCountModules.LocCntUG.LocCntUG :=
  locCntUG_of (fun _ _ _ _ _ _ _ _ _ M _ r n => thetaMbeG_of_coordT coordGU_holds h M r n)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end
