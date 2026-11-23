module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormBaseVectorRight
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section entries
variable (k r' : ℕ)

theorem entry_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) : M p q = (M *ᵥ bvec q) p := by
  rw [bvec, mulVec_single_one]; rfl

theorem dual_base_vector_eq_single : es0 k r' = bvec (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1)) := by
  funext p
  rw [last_basis_apply, bvec, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 (Fin.ext h1)) | (exfalso; exact h1 (congrArg Fin.val h2))

theorem heis_liftVec (hHA : HeisAct) (x : HPar k r') (z : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ liftVec k 1 r' z =
      liftVec k 1 r' z - herm (Hpk k (1 + r')) (liftVec k 1 r' z) (liftVec k 1 r' x.1) • e0 k r' := by
  rw [show heis0 k r' x = heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) from rfl, hHA, hermitian_form_base_vector_right,
    liftVec_out k r' z _ (Or.inr rfl), zero_smul, add_zero]

theorem heisenberg_dual_base_vector_formula (hHA : HeisAct) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  rw [show heis0 k r' x = heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) from rfl, hHA, hermitian_dual_base_vector_left,
    liftVec_out k r' x.1 _ (Or.inl rfl), star_zero, zero_smul, sub_zero, hermitian_form_base_vector_right, last_basis_apply, if_pos rfl,
    one_smul]
  exact (add_assoc _ _ _).symm

variable (c : ℂ) (g : Mat k r') (x : HPar k r')

theorem conj_gg (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, bvec_lev, ιLev_liftVec, heis_liftVec k r' hHA,
    reflection_mulVec_levelPos, Pi.sub_apply, Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, if_neg (by rw [levPos_val]; omega),
    smul_zero, sub_zero, bvec, mulVec_single_one]
  rfl

theorem conj_y (hHA : HeisAct) (i : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) ⟨2 * (1 + r') + k, by omega⟩ = x.1 i := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, levelEmbedding_mulVec_es0, heisenberg_dual_base_vector_formula k r' hHA, reflection_mulVec_levelPos,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, last_basis_apply,
    if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega)]
  simp

theorem conj_cb (hHA : HeisAct) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ =
      c * hb k r' x.1 x.2 := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, levelEmbedding_mulVec_es0, heisenberg_dual_base_vector_formula k r' hHA, rankOneMatrix_last_coord,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, liftVec_out k r' x.1 _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, last_basis_apply,
    if_neg (by simp only; omega), if_pos rfl]
  simp

theorem un_col (hHA : HeisAct) (j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g *ᵥ (heis0 k r' x *ᵥ bvec (levPos k 1 r' j)) =
      liftVec k 1 r' (g *ᵥ bvec j) -
        herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' x.1) • e0 k r' := by
  rw [bvec_lev, heis_liftVec k r' hHA, mulVec_sub, mulVec_smul, ιLev_liftVec, levi_embedding_mulVec_e0]

theorem un_gg (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, un_col k r' g x hHA, reflection_mulVec_levelPos, Pi.sub_apply,
    Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, if_neg (by rw [levPos_val]; omega), smul_zero, sub_zero, bvec,
    mulVec_single_one]
  rfl

theorem un_row (hHA : HeisAct) (j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ⟨2 * (1 + r') + k, by omega⟩ (levPos k 1 r' j) =
      -(c * herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' x.1)) := by
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, un_col k r' g x hHA, rankOneMatrix_last_coord, Pi.sub_apply,
    Pi.smul_apply, liftVec_out k r' _ _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, if_pos rfl]
  simp

theorem un_cb (hHA : HeisAct) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ =
      c * hb k r' x.1 x.2 := by
  have hv : ιLev k 1 r' g *ᵥ (heis0 k r' x *ᵥ es0 k r') =
      es0 k r' + liftVec k 1 r' (g *ᵥ x.1) + hb k r' x.1 x.2 • e0 k r' := by
    rw [heisenberg_dual_base_vector_formula k r' hHA, mulVec_add, mulVec_add, mulVec_smul, levelEmbedding_mulVec_es0, ιLev_liftVec, levi_embedding_mulVec_e0]
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, hv,
    rankOneMatrix_last_coord, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
    liftVec_out k r' _ _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, last_basis_apply, if_neg (by simp only; omega), if_pos rfl]
  simp

end entries

section bounds
variable (k r' : ℕ)

theorem exists_perm (y : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    ∃ j : Fin (2 * r' + k + 1),
      ‖herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' y)‖ = ‖y i‖ := by
  by_cases hA : i.val + 1 < 1 + r' ∨ 1 + r' + k < i.val + 1
  · refine ⟨⟨2 * (1 + r') + k - (i.val + 1) - 1, by omega⟩, ?_⟩
    rw [herm_bvec, norm_star, hpk_mulVec', if_pos (by rw [levPos_val]; simp only; omega), liftVec_apply,
      dite_eq_left (by simp only [levPos_val]; omega)]
    exact congrArg (fun t => ‖y t‖) (Fin.ext (by simp only [levPos_val]; omega))
  · refine ⟨i, ?_⟩
    rw [herm_bvec, norm_star, hpk_mulVec', if_neg (by rw [levPos_val]; omega)]
    split_ifs <;> simp [liftVec_lev]

theorem gN_nonneg' {n : ℕ} (M : Mat k n) : 0 ≤ gN M := Real.sqrt_nonneg _

theorem gN_entry {n : ℕ} (M : Mat k n) (p q : Fin (2 * n + k + 1)) : ‖M p q‖ ≤ gN M := by
  rw [← Real.sqrt_sq (norm_nonneg (M p q)), Complex.sq_norm]
  unfold gN
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (M p q) ≤ ∑ j, Complex.normSq (M p j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (M p j)) (fun j _ => Complex.normSq_nonneg _)
          (Finset.mem_univ q)
    _ ≤ ∑ i, ∑ j, Complex.normSq (M i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (M i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ p)

theorem gN_sub (M : Mat k (1 + r')) (g : Mat k r')
    (h : ∀ i j, M (levPos k 1 r' i) (levPos k 1 r' j) = g i j) : gN g ≤ gN M := by
  unfold gN
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (g i j)
      = ∑ i, ∑ j, Complex.normSq (M (levPos k 1 r' i) (levPos k 1 r' j)) := by simp only [h]
    _ ≤ ∑ i, ∑ q, Complex.normSq (M (levPos k 1 r' i) q) :=
        Finset.sum_le_sum fun i _ => sum_lev_le k r' (fun q => Complex.normSq (M (levPos k 1 r' i) q))
          fun q => Complex.normSq_nonneg _
    _ ≤ ∑ p, ∑ q, Complex.normSq (M p q) :=
        sum_lev_le k r' (fun p => ∑ q, Complex.normSq (M p q))
          fun p => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _

theorem hb_im (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : (hb k r' y s).im = s := by simp [hb]

theorem cs_le (c : ℂ) (x : HPar k r') (M : Mat k (1 + r'))
    (h : M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ = c * hb k r' x.1 x.2) :
    ‖c‖ * |x.2| ≤ gN M := by
  calc ‖c‖ * |x.2| ≤ ‖c‖ * ‖hb k r' x.1 x.2‖ := by
        gcongr
        have := Complex.abs_im_le_norm (hb k r' x.1 x.2)
        rwa [hb_im] at this
    _ = ‖M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩‖ := by rw [h, norm_mul]
    _ ≤ gN M := gN_entry k _ _ _

variable (c : ℂ) (g : Mat k r') (x : HPar k r')

theorem pt_conj (hHA : HeisAct) :
    gN g ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ∧
      ‖x.1‖ ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ∧
      ‖c‖ * |x.2| ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) := by
  refine ⟨gN_sub k r' _ g (conj_gg k r' c g x hHA), ?_, cs_le k r' c x _ (conj_cb k r' c g x hHA)⟩
  refine (pi_norm_le_iff_of_nonneg (gN_nonneg' k _)).2 fun i => ?_
  rw [← conj_y k r' c g x hHA i]
  exact gN_entry k _ _ _

theorem pt_un (hHA : HeisAct) :
    gN g ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * ‖x.1‖ ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * |x.2| ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
  refine ⟨gN_sub k r' _ g (un_gg k r' c g x hHA), ?_, cs_le k r' c x _ (un_cb k r' c g x hHA)⟩
  rw [← norm_smul]
  refine (pi_norm_le_iff_of_nonneg (gN_nonneg' k _)).2 fun i => ?_
  obtain ⟨j, hj⟩ := exists_perm k r' x.1 i
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, ← hj, ← norm_mul, ← norm_neg, ← un_row k r' c g x hHA j]
  exact gN_entry k _ _ _

end bounds

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

section

noncomputable section

open Matrix InnerProductSpace
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {n m : ℕ}

def gram (w : Fin m → EuclideanSpace ℂ (Fin n)) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => inner ℂ (w a) (w b)

theorem gram_comb (w : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ) :
    gram (fun a => ∑ b, τ b a • w b) = τᴴ * gram w * τ := by
  ext a b
  simp only [gram, of_apply, Matrix.mul_apply, conjTranspose_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [starRingEnd_apply]; ring

theorem gs_fac (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : LinearIndependent ℂ w) :
    ∃ (u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ), Orthonormal ℂ u ∧
      τ.BlockTriangular id ∧ (∀ j, τ j j ≠ 0) ∧ (∀ a, w a = ∑ b, τ b a • u b) ∧
      ∀ a, u a ∈ Submodule.span ℂ (Set.range w) := by
  set u := gramSchmidtNormed ℂ w with hudef
  have hu : Orthonormal ℂ u := gramSchmidtNormed_orthonormal hw
  have hspan : Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range w) := by
    rw [hudef, span_gramSchmidtNormed_range, span_gramSchmidt]
  refine ⟨u, fun b a => inner ℂ (u b) (w a), hu, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : j < i := hij
    simp only [hudef, gramSchmidtNormed, inner_smul_left]
    rw [gramSchmidt_inv_triangular ℂ w hij', mul_zero]
  · intro j hj
    have hg := gramSchmidt_ne_zero j hw
    have h0 : inner ℂ (u j) (w j) = inner ℂ (u j) (gramSchmidt ℂ w j) := by
      conv_lhs => rw [gramSchmidt_def'' ℂ w j]
      rw [inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero]
      intro i hi
      rw [inner_smul_right]
      simp only [hudef, gramSchmidtNormed, inner_smul_left,
        gramSchmidt_orthogonal ℂ w (Finset.mem_Iio.1 hi).ne', mul_zero]
    simp only at hj
    rw [h0] at hj
    simp only [hudef, gramSchmidtNormed, inner_smul_left, inner_self_eq_norm_sq_to_K] at hj
    simp [hg] at hj
  · intro a
    have : w a ∈ Submodule.span ℂ (Set.range u) := hspan ▸ Submodule.subset_span ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
    conv_lhs => rw [← hc]
    refine Finset.sum_congr rfl fun b _ => ?_
    show c b • u b = inner ℂ (u b) (w a) • u b
    rw [← hc, hu.inner_right_fintype]
  · intro a; rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩

theorem det_gram_of (w u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ)
    (hu : Orthonormal ℂ u) (hτ : τ.BlockTriangular id) (hw : ∀ a, w a = ∑ b, τ b a • u b) :
    (gram w).det = ((∏ j, ‖τ j j‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : gram u = 1 := by
    ext i j; simp [gram, orthonormal_iff_ite.1 hu, Matrix.one_apply]
  have hg : gram w = τᴴ * τ := by
    rw [show w = fun a => ∑ b, τ b a • u b from funext hw, gram_comb, h1, Matrix.mul_one]
  rw [hg, det_mul, det_conjTranspose, det_of_isUpperTriangular hτ]
  rw [show star (∏ j, τ j j) = ∏ j, star (τ j j) by
    simpa using map_prod (starRingEnd ℂ) (fun j => τ j j) Finset.univ]
  rw [← Finset.prod_mul_distrib, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← starRingEnd_apply, Complex.conj_mul']; push_cast; ring

theorem ga_eq (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l Y = (gram (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1))))).det.re := by
  unfold Ga; congr 2; ext a b
  simp only [gram, of_apply, EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]

theorem linInd_toLp {ι : Type*} (Y : ι → Fin n → ℂ) (hY : LinearIndependent ℂ Y) :
    LinearIndependent ℂ (fun a => (WithLp.toLp 2 (Y a) : EuclideanSpace ℂ (Fin n))) :=
  hY.map' (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap (LinearEquiv.ker _)

theorem ga_pos (k r : ℕ) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (hY : LinearIndependent ℂ Y)
    (l : Fin (r + 1)) : 0 < Ga k r l Y := by
  rw [ga_eq]
  have hw := (linInd_toLp Y hY).comp _ (Fin.castLE_injective (show l.val + 1 ≤ r + 1 by omega))
  obtain ⟨u, τ, hu, hτ, hd, hwe, -⟩ := gs_fac (fun a : Fin (l.val + 1) =>
    (WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) hw
  rw [det_gram_of _ u τ hu hτ hwe, Complex.ofReal_re]
  exact Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hd j)) 2

theorem norm_mulVec_le {k r : ℕ} (A : Mat k r) (y : Fin (2 * r + k + 1) → ℂ) :
    ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))‖ ≤
      gN A * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin (2 * r + k + 1)))‖ := by
  have hnn : (0 : ℝ) ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, gN, ← Real.sqrt_mul hnn]
  refine Real.sqrt_le_sqrt ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ y) i‖ ≤ ∑ j, ‖A i j‖ * ‖y j‖ := by
    simp only [mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  calc ‖(A *ᵥ y) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖y j‖) ^ 2 := by gcongr
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖y j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = ∑ j, Complex.normSq (A i j) * ∑ j, ‖y j‖ ^ 2 := by
      rw [← Finset.sum_mul]; simp only [Complex.normSq_eq_norm_sq]

end ReciprocityTheory.ChartRestriction.DS.Xi.GS
end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def phi2 (k r' : ℕ) (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  ιLev k 1 r' (Hpk k r') *ᵥ phiV k (1 + r') a

def Yx (k r' : ℕ) (x : HPar k r') (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  (heis0 k r' x)⁻¹ *ᵥ phi2 k r' a

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aAll_of (hb : AStepBase) (hs : AStepSucc) : ∀ k r : ℕ, 1 ≤ k → AAt k r := by
  intro k r hk
  induction r with
  | zero => exact hb k hk
  | succ r' ih => exact hs k (r' + 1) r' (by omega) hk ih

theorem bAll_of (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by
  intro k r hk
  induction r with
  | zero => intro δ hδ _; exact hb k hk δ hδ
  | succ r' ih =>
    intro δ hδ hδ'
    exact hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))

theorem xiExists_of (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA'
  obtain ⟨eS, heS, hBs⟩ := hB k r D.k_pos
  have he0 : 0 < min eS (1 / 10 : ℝ) := lt_min heS (by norm_num)
  have adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10)) := fun l => by
    simp only [sub_sub_cancel]; exact ⟨he0, min_le_right _ _⟩
  have adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS :=
    fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩
  exact ⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'),
    hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN)
      (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩

theorem xiExists_of_induction_steps (hAb : AStepBase) (hAs : AStepSucc) (hBb : BStepBase) (hBs : BStepSucc)
    (hC : CoefStep) (hX : XiIntStep) : XiExists :=
  xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
