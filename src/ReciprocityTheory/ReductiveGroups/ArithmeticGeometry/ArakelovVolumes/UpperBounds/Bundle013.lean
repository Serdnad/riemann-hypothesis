module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle011

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem det_ne_of_orth {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) : (mat x0 τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (ho τ)
  have h2 : gram τ.1 X.Gm (mat x0 τ) =
      (mat x0 τ)ᵀ * gram τ.1 X.Gm 1 * (mat x0 τ).map (starRingEnd ℂ) := by
    rw [← ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, Matrix.one_mul]
  rw [h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  unfold sgn
  split_ifs <;> norm_num

def nM (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := mat (nmat X z) τ

theorem nM_upper (z : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : a < b) : nM X z τ a b = 0 := by
  have h' : ¬ b < a := not_lt.2 h.le
  simp [nM, mat, nmat, h', h.ne]

theorem nM_diag (z : V (nd X)) (τ : X.Ψ) (a : Fin r) : nM X z τ a a = 1 := by
  simp [nM, mat, nmat]

theorem det_nM (z : V (nd X)) (τ : X.Ψ) : (nM X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [nM_diag]
  · unfold Matrix.IsLowerTriangular Matrix.BlockTriangular
    intro i j hij
    exact nM_upper X z τ (OrderDual.toDual_lt_toDual.1 hij)

theorem mat_cpt (x0 : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    mat (cpt X x0 z) τ = mat x0 τ * nM X z τ := rfl

def qI (m : Fin (r - X.p0)) : Fin r := ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩

def n1 (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  (nM X z τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le)

def Wm (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  (nM X z τ).submatrix (qI X) (Fin.castLE X.p0_le)

theorem det_unipotentFrame_eq_one (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [n1, nM_diag]
  · unfold Matrix.IsLowerTriangular Matrix.BlockTriangular
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp only [n1, Matrix.submatrix_apply]
    apply nM_upper X z τ
    rw [Fin.lt_iff_val_lt_val] at hij' ⊢
    simpa using hij'

def Zt (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin (r - X.p0)) ℂ :=
  (Wm X z τ * (n1 X z τ)⁻¹)ᵀ

def Am (z : V (nd X)) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ := 1 - Zt X z τ * (Zt X z τ)ᴴ

theorem sum_split (f : Fin r → ℂ) :
    ∑ k, f k = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) + ∑ m : Fin (r - X.p0), f (qI X m) := by
  have hr : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  rw [← (finCongr hr).sum_comp, Fin.sum_univ_add]
  rfl

theorem gramPos_cpt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    X.gramPos (cpt X x0 z) τ =
      (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) - (Wm X z τ)ᵀ * (Wm X z τ).map (starRingEnd ℂ) := by
  have hg : gram τ.1 X.Gm (mat (cpt X x0 z) τ) = (nM X z τ)ᵀ *
      Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
        (nM X z τ).map (starRingEnd ℂ) := by
    rw [mat_cpt, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, ho τ]
  ext c d
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Data.gramPos, hg, Matrix.submatrix_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, n1, Wm,
    Matrix.submatrix_apply]
  rw [sum_split X, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    have he : ((Fin.castLE X.p0_le e : Fin r) : ℕ) < X.p0 := by simp
    simp [sgn, he]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : ¬ ((qI X m : Fin r) : ℕ) < X.p0 := by simp [qI]
    simp [sgn, hm]

theorem unipotentFrame_transpose_mul (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)ᵀ * Zt X z τ = (Wm X z τ)ᵀ := by
  have hdet : IsUnit (n1 X z τ).det := by rw [det_unipotentFrame_eq_one]; exact isUnit_one
  unfold Zt
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one, Matrix.one_mul]

theorem transpose_conj {m n : Type*} (M : Matrix m n ℂ) : (Mᵀ)ᴴ = M.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem gramPos_eq (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    X.gramPos (cpt X x0 z) τ = (n1 X z τ)ᵀ * Am X z τ * ((n1 X z τ)ᵀ)ᴴ := by
  rw [gramPos_cpt X x0 ho z τ, transpose_conj]
  unfold Am
  have hW := unipotentFrame_transpose_mul X z τ
  calc (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) - (Wm X z τ)ᵀ * (Wm X z τ).map (starRingEnd ℂ)
      = (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) -
          ((n1 X z τ)ᵀ * Zt X z τ) * ((n1 X z τ)ᵀ * Zt X z τ)ᴴ := by
        rw [hW, transpose_conj]
    _ = (n1 X z τ)ᵀ * (1 - Zt X z τ * (Zt X z τ)ᴴ) * (n1 X z τ).map (starRingEnd ℂ) := by
        rw [Matrix.conjTranspose_mul, transpose_conj]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

theorem det_gramPos (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    (X.gramPos (cpt X x0 z) τ).det = (Am X z τ).det := by
  rw [gramPos_eq X x0 ho z τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_transpose, det_unipotentFrame_eq_one]
  simp

theorem mem_OmF_iff (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) : z ∈ OmF X x0 ↔ ∀ τ, (Am X z τ).PosDef := by
  have hdx : ∀ τ, (mat (cpt X x0 z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt, Matrix.det_mul, det_nM, mul_one]
    exact det_ne_of_orth X ho τ
  have hB : ∀ τ, IsUnit ((n1 X z τ)ᵀ).det := by
    intro τ
    rw [Matrix.det_transpose, det_unipotentFrame_eq_one]
    exact isUnit_one
  constructor
  · intro hz τ
    have hP := Data.gramPos_posDef (X := X) (show cpt X x0 z ∈ X.dom from hz) τ
    rw [gramPos_eq X x0 ho z τ] at hP
    have hC : ((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ = 1 := Matrix.nonsing_inv_mul _ (hB τ)
    have hA : Am X z τ = ((n1 X z τ)ᵀ)⁻¹ * ((n1 X z τ)ᵀ * Am X z τ * ((n1 X z τ)ᵀ)ᴴ) *
        (((n1 X z τ)ᵀ)⁻¹)ᴴ := by
      calc Am X z τ = (((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ) * Am X z τ *
            (((n1 X z τ)ᵀ)⁻¹ * (n1 X z τ)ᵀ)ᴴ := by rw [hC]; simp
        _ = _ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [hA]
    refine hP.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h3 := congrArg (fun u => Matrix.vecMul u (n1 X z τ)ᵀ) hvw
    simpa [Matrix.vecMul_vecMul, hC] using h3
  · intro hA
    show cpt X x0 z ∈ X.dom
    refine mem_dom_of_gramPos (X := X) (fun τ => ⟨hdx τ, ?_⟩)
    rw [gramPos_eq X x0 ho z τ]
    refine (hA τ).mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h3 := congrArg (fun u => Matrix.vecMul u ((n1 X z τ)ᵀ)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hB τ)] using h3

theorem leadingMinor_eq_gramDet (x : Frame X.Ψ r) (τ : X.Ψ) :
    dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos x τ).det := rfl

theorem norm_of_pos {c : ℂ} (hc : 0 < c) : ‖c‖ = c.re := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hc
  have hce : c = (c.re : ℂ) := Complex.ext rfl (by simp [← h2])
  conv_lhs => rw [hce]
  rw [Complex.norm_real, Real.norm_of_nonneg h1.le]

theorem rhF_eq_sum (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) : rhF X x0 z = -∑ τ, Real.log ‖(Am X z τ).det‖ := by
  unfold rhF
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [leadingMinor_eq_gramDet, det_gramPos X x0 ho z τ]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def NF (x : LoI X.Ψ r → ℂ) : Frame X.Ψ r := fun τ => Nmat x τ

def densY (y : Frame X.Ψ r) : ℝ := ∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ (-2 : ℤ)

lemma Nmat_low (x : LoI X.Ψ r → ℂ) (τ : X.Ψ) : (Nmat x τ).BlockTriangular OrderDual.toDual := by
  intro a b hab
  have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
  have h1 : ¬ b < a := not_lt.mpr hab'.le
  have h2 : a ≠ b := hab'.ne
  first
  | simp [Nmat, h1, h2]
  | (unfold Nmat; rw [Matrix.of_apply, dite_eq_right h1]; simp [h2, Ne.symm h2])

lemma det_Nmat (x : LoI X.Ψ r → ℂ) (τ : X.Ψ) : (Nmat x τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (Nmat_low X x τ)]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold Nmat
  rw [Matrix.of_apply, dite_eq_right (lt_irrefl a)]
  simp

private theorem det_gram' (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) :
    (ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm M).det = M.det * (X.Gm.map τ.1).det * (starRingEnd ℂ) M.det := by
  have e : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    first
    | exact Finset.sum_comm
  have hc : (M.map (starRingEnd ℂ)).det = (starRingEnd ℂ) M.det := by
    rw [RingHom.map_det]
    rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]

private theorem norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (τ : X.Ψ) :
    ‖(mat x0 τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x0 τ).det‖ = 1 := by
  have h := congrArg Matrix.det (hx0 τ)
  rw [det_gram', Matrix.det_diagonal] at h
  have hn : ‖(mat x0 τ).det * (X.Gm.map τ.1).det * (starRingEnd ℂ) (mat x0 τ).det‖ = 1 := by
    rw [h, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sgn
    split_ifs <;> simp
  rwa [norm_mul, norm_mul, Complex.norm_conj] at hn

lemma norm_dmin_last {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (x : LoI X.Ψ r → ℂ) (τ : X.Ψ) :
    ‖dmin X.Gm (rmul x0 (NF X x)) τ (Fin.last r)‖ = 1 := by
  have hl : ∀ M : Matrix (Fin r) (Fin r) ℂ, lminor M (Fin.last r) = M.det := by
    intro M
    unfold lminor
    first
    | rfl
    | (congr 1)
  have hdm : (mat (rmul x0 (NF X x)) τ).det = (mat x0 τ).det := by
    show (mat x0 τ * Nmat x τ).det = _
    rw [Matrix.det_mul, det_Nmat, mul_one]
  show ‖lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (rmul x0 (NF X x)) τ)) (Fin.last r)‖ = 1
  rw [hl, det_gram', hdm, norm_mul, norm_mul, Complex.norm_conj]
  exact norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one X hx0 τ

lemma normSq_det_orthogonalFrame {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (τ : X.Ψ) :
    Complex.normSq (mat x0 τ).det * ‖(X.Gm.map τ.1).det‖ = 1 := by
  rw [Complex.normSq_eq_norm_sq, ← norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one X hx0 τ]
  ring

def gI (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ENNReal) (v : Ix X.Ψ r → ℂ) : ENNReal :=
  φ (rmul x0 (uf X v)) * Wf X (rmul x0 (uf X v))

def GLo (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ENNReal) (x : LoI X.Ψ r → ℂ) : ENNReal :=
  if rmul x0 (NF X x) ∈ X.dom then φ (rmul x0 (NF X x)) * ENNReal.ofReal (densY X (rmul x0 (NF X x))) else 0

lemma uf_lu_eS (x : LoI X.Ψ r → ℂ) (y : UpI X.Ψ r → ℂ) :
    uf X (lu ((eS X.Ψ r).symm (x, y))) = rmul (NF X x) (UF X y) := by
  have h1 : ∀ τ : X.Ψ, 1 + sl ((eS X.Ψ r).symm (x, y)) τ = Nmat x τ := by
    intro τ
    ext a b
    by_cases h : b < a
    · have hab : a ≠ b := ne_of_gt h
      first
      | simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
    · first
      | simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  have h2 : ∀ τ : X.Ψ, up ((eS X.Ψ r).symm (x, y)) τ = Umat y τ := by
    intro τ
    ext a b
    by_cases h : b < a
    · first
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
    · first
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  funext τ a b
  show ((1 + sl ((eS X.Ψ r).symm (x, y)) τ) * up ((eS X.Ψ r).symm (x, y)) τ) a b =
    (Nmat x τ * Umat y τ) a b
  rw [h1, h2]

lemma rmul_assoc' (x b c : Frame X.Ψ r) : rmul x (rmul b c) = rmul (rmul x b) c := by
  funext τ
  exact (Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)).symm

lemma continuous_uf : Continuous (uf X) := by
  unfold uf
  first
  | fun_prop

lemma densY_eq {y : Frame X.Ψ r} :
    densY X y = (∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2)⁻¹ := by
  unfold densY
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  first
  | simp only [_root_.zpow_neg, zpow_ofNat]

theorem inner_eq {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {φ : Frame X.Ψ r → ENNReal}
    (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) (x : LoI X.Ψ r → ℂ) :
    ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) =
      GLo X x0 φ x * K0 X.Ψ r := by
  set Y := rmul x0 (NF X x) with hYd
  have hrw : ∀ y, gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) = φ (rmul Y (UF X y)) * Wf X (rmul Y (UF X y)) := by
    intro y; simp only [gI, uf_lu_eS, rmul_assoc', hYd]
  by_cases hY : Y ∈ X.dom
  · have hpt : ∀ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
        ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) =
        φ Y * (ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy X.Ψ r).indicator 1 (Lβ (β0 X Y) y)) := by
      intro y
      split_ifs with hd
      · rw [hrw, hφ Y hY _ (UF_mem X hd), Wf_rmul_UF X hY hd]; ring
      · push_neg at hd
        obtain ⟨τ, b, hb⟩ := hd
        have hC : Lβ (β0 X Y) y ∉ Cy X.Ψ r := fun hC => by
          have := ((hC (dI τ b)).1 rfl).1
          rw [Lβ_diag _ (β0_upper X hY) y τ b, hb, mul_zero, norm_zero] at this
          norm_num at this
        rw [Set.indicator_of_notMem hC]; simp
    have hmeas : Measurable fun y : UpI X.Ψ r → ℂ =>
        ENNReal.ofReal (Complex.normSq (jacU y)) * (Cy X.Ψ r).indicator 1 (Lβ (β0 X Y) y) :=
      measurable_normSq_jacU.mul ((measurable_one.indicator measurableSet_Cy).comp
        (LinearMap.continuous_of_finiteDimensional (Lβ (β0 X Y))).measurable)
    have hdiag : ∀ τ b, β0 X Y τ b b ≠ 0 := fun τ b h0 => by
      have := normSq_β0_diag X hY τ b
      rw [h0, map_zero] at this
      exact (abs_re_pos X hY τ b).ne this
    rw [lintegral_congr hpt, lintegral_const_mul _ hmeas, lintegral_upper _ (β0_upper X hY) hdiag,
      exponent_identity X hY (norm_dmin_last X hx0 x), GLo, if_pos hY, densY_eq, mul_assoc]
  · have hpt : ∀ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
        ENNReal.ofReal (Complex.normSq (jacU y)) * gI X x0 φ (lu ((eS X.Ψ r).symm (x, y))) else 0) = 0 := by
      intro y
      split_ifs with hd
      · rw [hrw, Wf_rmul_not_dom X hY (UF_mem X hd), mul_zero, mul_zero]
      · rfl
    rw [lintegral_congr hpt, lintegral_zero, GLo, if_neg hY, zero_mul]

theorem core {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {φ : Frame X.Ψ r → ENNReal} (hφm : Measurable φ)
    (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    (∫⁻ x, GLo X x0 φ x) * K0 X.Ψ r =
      ENNReal.ofReal (∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖ ^ r) * ∫⁻ v, φ (uf X v) * Wf X (uf X v) := by
  have hF : Measurable fun v => φ (uf X v) * Wf X (uf X v) :=
    (hφm.comp (continuous_uf X).measurable).mul ((measurable_Wf X).comp (continuous_uf X).measurable)
  have hdet : ∀ τ, (mat x0 τ).det ≠ 0 := fun τ h0 => by
    have := normSq_det_orthogonalFrame X hx0 τ
    rw [h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  have hg : Measurable (gI X x0 φ) := by
    have := hF.comp (LinearMap.continuous_of_finiteDimensional (LA (fun τ => mat x0 τ))).measurable
    exact this
  have h1 := lintegral_flat hg
  simp only [inner_eq X hx0 hφ] at h1
  have h2 : ∫⁻ v, gI X x0 φ v = ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ *
      ∫⁻ v, φ (uf X v) * Wf X (uf X v) := lintegral_comp_LA (fun τ => mat x0 τ) hdet hF
  rw [← lintegral_mul_const' _ _ (measureConstant_lt_top (ι := X.Ψ) (r := r)).ne, ← h1, h2]
  congr 2
  rw [map_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, ← inv_pow]
  congr 1
  have := normSq_det_orthogonalFrame X hx0 τ
  exact (eq_inv_of_mul_eq_one_right this).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end
