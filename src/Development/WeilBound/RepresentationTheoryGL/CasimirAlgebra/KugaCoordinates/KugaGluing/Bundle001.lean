module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
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

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def kgT : Lie E a →ₗ[ℝ] ℂ where
  toFun X := ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)
  map_add' X Y := by simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← coordL_apply, map_smul, coordL_apply]

theorem kgT_apply (X : Lie E a) : kgT X = ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) := rfl

def kgH : Herm E a →ₗ[ℝ] Lie E a where
  toFun X := toL X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kgT_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) : kgT (toL (X * Y - Y * X)) = 0 := by
  have h : ∀ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = coord τ (Matrix.trace (X * Y - Y * X)) := by
    intro τ; simp only [Matrix.trace, Matrix.diag, map_sum]
  change ∑ τ : E →+* ℂ, ∑ i, coord τ ((X * Y - Y * X) i i) = 0
  simp only [h, Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, map_zero, Finset.sum_const_zero]

variable [_root_.NumberField.IsTotallyComplex E]

theorem kgT_star (X : Lie E a) : star (kgT X) = kgT X := by
  rw [kgT_apply, star_sum]
  simp_rw [star_sum, ← J.coord_conjugate]
  exact Fintype.sum_equiv (Function.Involutive.toPerm _ fun τ => star_star τ) _ _ fun τ => rfl

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem kg_coord_atEmb_self (τ : E →+* ℂ) (z : ℂ) : coord τ (atEmb τ z) = z := by
  rw [J.coord_eq]
  unfold atEmb
  split_ifs <;> simp_all

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem kg_coord_atEmb_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  classical
  rw [J.coord_eq]
  unfold atEmb
  split_ifs <;> simp only [Pi.single_eq_of_ne h, map_zero]

theorem kg_sum_coord_atEmb (τ : E →+* ℂ) (z : ℂ) :
    ∑ τ' : E →+* ℂ, coord τ' (atEmb τ z) = z + starRingEnd ℂ z := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := by
    intro h
    have h1 : (InfinitePlace.mk τ).IsReal :=
      InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1
  rw [Fintype.sum_eq_add τ (ComplexEmbedding.conjugate τ) hne.symm, J.coord_conjugate, kg_coord_atEmb_self]
  · rfl
  · rintro τ' ⟨h1, h2⟩
    refine kg_coord_atEmb_of_ne (fun h => ?_) z
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact h1 h
    · exact h2 (by rw [← h]; exact (star_star τ').symm)

theorem cx_kgT (τ : E →+* ℂ) (i j : Fin a) : cx τ (kgT (E := E) (a := a)) i j = if i = j then 1 else 0 := by
  have h : ∀ z : ℂ, kgT (toL (Matrix.single i j (atEmb τ z))) = if i = j then z + starRingEnd ℂ z else 0 := by
    intro z
    rw [kgT_apply]
    split_ifs with hij
    · subst hij
      rw [← kg_sum_coord_atEmb τ z]
      refine Finset.sum_congr rfl fun τ' _ => ?_
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    · refine Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => ?_
      simp only [toL]
      rw [Matrix.of_symm_apply, Matrix.single_apply]
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) hij
      · exact map_zero _
  unfold cx
  rw [h, h]
  split_ifs <;> norm_num [Complex.conj_I]

end
end PositivityTheory.Rg.Cz
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in
theorem kg_star_atEmb (τ : E →+* ℂ) (z : ℂ) : star (atEmb τ z) = atEmb τ (starRingEnd ℂ z) := by
  classical
  unfold atEmb
  funext w
  simp only [Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

theorem kg_cx_dmat_conj (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ)
    (τ : E →+* ℂ) (i j : Fin a) : (cx τ Ξ.dmat i j)ᴴ = cx τ Ξ.dmat j i := by
  have e : ∀ z, (Ξ.dmat (toL (Matrix.single i j (atEmb τ z))))ᴴ =
      Ξ.dmat (toL (Matrix.single j i (atEmb τ (starRingEnd ℂ z)))) := by
    intro z; rw [← hΞ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, kg_star_atEmb]
  have e2 : Ξ.dmat (toL (Matrix.single j i (atEmb τ (-Complex.I)))) =
      -Ξ.dmat (toL (Matrix.single j i (atEmb τ Complex.I))) := by
    rw [← map_neg]
    congr 1
    funext k l
    show Matrix.single j i (atEmb τ (-Complex.I)) k l = -(Matrix.single j i (atEmb τ Complex.I) k l)
    rw [Matrix.single_apply, Matrix.single_apply, atEmb_eq τ (-Complex.I), atEmb_eq τ Complex.I]
    split_ifs <;> simp
  unfold cx
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, e, e, map_one,
    Complex.conj_I, e2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  module

theorem kg_cas_herm (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ) (τ : E →+* ℂ) :
    (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)ᴴ = ∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, kg_cx_dmat_conj Ξ hΞ]

omit [NumberField E] in
theorem kg_star_iM {X : Matrix (Fin a) (Fin a) (Cinf E)} (hX : star X = X) : star (iM X) = -iM X := by
  ext i j w
  have h : star (X j i) = X i j := by rw [← Matrix.star_apply, hX]
  have h' : star (X j i w) = X i j w := congrFun h w
  simp only [iM, Matrix.star_apply, Matrix.smul_apply, Matrix.neg_apply, Pi.star_apply, Pi.neg_apply, smul_eq_mul,
    Pi.mul_apply, star_mul', h', Complex.star_def, Complex.conj_I]
  ring

def kgL : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a where
  toFun := toL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


omit [NumberField E] in
def kgD (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) : Herm E a →ₗ[ℝ] Herm E a where
  toFun Y := ⟨Z * Y.1 - Y.1 * Z, by
    have hY : star Y.1 = Y.1 := Y.2
    show star (Z * Y.1 - Y.1 * Z) = Z * Y.1 - Y.1 * Z
    rw [star_sub, star_mul, star_mul, hY, hZ, mul_neg, neg_mul, sub_neg_eq_add, neg_add_eq_sub]⟩
  map_add' Y Y' := Subtype.ext (by
    show Z * (Y.1 + Y'.1) - (Y.1 + Y'.1) * Z = (Z * Y.1 - Y.1 * Z) + (Z * Y'.1 - Y'.1 * Z)
    rw [mul_add, add_mul]; abel)
  map_smul' c Y := Subtype.ext (by
    show Z * (c • Y.1) - (c • Y.1) * Z = c • (Z * Y.1 - Y.1 * Z)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub])

omit [NumberField E] in
theorem kgD_val (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Herm E a) :
    (kgD Z hZ Y).1 = Z * Y.1 - Y.1 * Z := rfl

end
end PositivityTheory.Rg.Cz
end
end
