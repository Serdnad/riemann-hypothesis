module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle663
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle664
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
public import Mathlib.Algebra.Field.Rat
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Finset.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
public import Mathlib.Data.Rat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodFrame

theorem frame_hermForm_sum_left {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
  unfold hermForm
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]

theorem frame_hermForm_sum_right {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
  have hs : star (∑ i, c i • E i) = ∑ i, star (c i) • star (E i) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext k
    simp [mul_comm]
  simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_col {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) (i : Fin g) :
    (fun k => combMat l ε k i) = ∑ m, (ε i m : ℂ) • l m := by
  funext k
  simp [combMat, Finset.sum_apply]

theorem frame_im_hermForm {g r : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ)
    (l : Fin r → Fin g → ℂ) (hM : ∀ i j, (hermForm Hm (l i) (l j)).im = M i j)
    (A B : Matrix (Fin g) (Fin r) ℚ) (i k : Fin g) :
    (hermForm Hm (fun x => combMat l A x i) (fun x => combMat l B x k)).im
      = (((A * M.map (Int.cast : ℤ → ℚ) * Bᵀ) i k : ℚ) : ℝ) := by
  rw [frame_col, frame_col, frame_hermForm_sum_left]
  simp only [frame_hermForm_sum_right, Finset.mul_sum, Complex.im_sum]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  push_cast
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.mul_im, hM]
  ring

theorem riemann_relations_frame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  intro g r Hm M l ε φ D hD hH hpos _hl hM hεε hφφ hφε
  set P := combMat l ε with hP
  set Q := combMat l φ with hQ
  set E : Fin g → Fin g → ℂ := fun i k => P k i with hE
  set F : Fin g → Fin g → ℂ := fun j k => Q k j with hF
  have hEE : ∀ i j, (hermForm Hm (E i) (E j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM ε ε i j
    rw [hεε] at h
    simpa using h
  have hFF : ∀ i j, (hermForm Hm (F i) (F j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ φ i j
    rw [hφφ] at h
    simpa using h
  have hFE : ∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ ε i j
    rw [hφε] at h
    change (hermForm Hm (F i) (E j)).im = _ at h
    rw [h]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hind : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : hermForm Hm (F j) (∑ i, ((a i : ℝ) : ℂ) • E i) = 0 := by
      have hs : (∑ i, ((a i : ℝ) : ℂ) • E i) = ∑ i, a i • E i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ext k
        simp
      rw [hs, ha]
      simp [hermForm]
    rw [frame_hermForm_sum_right] at h1
    have h2 := congrArg Complex.im h1
    simpa [Complex.im_sum, Complex.mul_im, hFE] using h2
  have hdet : P.det ≠ 0 := by
    have h := GlobalTheory.det_ne_zero_of_real_indep_isotropic g Hm E hpos hind hEE
    exact h
  have hU : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := P⁻¹ * Q with hτ
  have hPτ : P * τ = Q := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hFτ : ∀ j, F j = ∑ i, τ i j • E i := by
    intro j
    funext k
    have h := congrFun (congrFun hPτ k) j
    simp only [Matrix.mul_apply] at h
    simp only [hF, hE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨hposτ, hsymτ⟩ := GlobalTheory.riemann_relations_period_matrix g g Hm E F τ hH hpos hFτ hEE hFE
  have hτs : ∀ i j, τ i j = τ j i := fun i j => by
    have h := hsymτ i j
    rw [hFF] at h
    simpa [sub_eq_zero] using h
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hY
  set a : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hEE])
  have hYA : Y * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hFτ j, frame_hermForm_sum_left] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, zero_add] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hY, Matrix.map_apply]
    rw [hτs j i]
  have hTim : ((D : ℂ) • τ).map Complex.im = (D : ℝ) • Y := by
    ext i j
    simp [hY]
  have hTre : (((D : ℂ) • τ).map Complex.im).map Complex.ofReal = (D : ℂ) • Y.map Complex.ofReal := by
    rw [hTim]
    ext i j
    simp
  have hYAc : Y.map Complex.ofReal * a.map Complex.ofReal = 1 := by
    ext i k
    have h := congrFun (congrFun hYA i) k
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hinv : ((((D : ℂ) • τ).map Complex.im).map Complex.ofReal)⁻¹ = (D : ℂ)⁻¹ • a.map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [hTre, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hDne, one_smul, hYAc]
  refine ⟨hU, ?_, ?_, ?_⟩
  · show ((D : ℂ) • τ)ᵀ = (D : ℂ) • τ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply]
    rw [hτs j i]
  · rw [Matrix.posDef_iff_dotProduct_mulVec, hTim]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial, hY, Matrix.map_apply]
      rw [hτs j i]
    · have e : star x ⬝ᵥ (((D : ℝ) • Y) *ᵥ x) = (D : ℝ) * (∑ i, ∑ j, (x i : ℂ) * τ i j * (x j : ℂ)).im := by
        simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Complex.im_sum,
          Finset.mul_sum, hY, Matrix.map_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [Complex.mul_im]
        ring
      rw [e]
      exact mul_pos (by exact_mod_cast hD) (hposτ x hx)
  · rw [hinv, smul_smul, Complex.ofReal_natCast, mul_inv_cancel₀ hDne, one_smul]
    ext i j
    rw [Matrix.map_apply, ← hAr i j]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, Pi.star_apply, Matrix.map_apply, hE, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring

end GlobalTheory.PeriodFrame
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  first | exact @GlobalTheory.PsiDoubleCoord.main | exact GlobalTheory.PsiDoubleCoord.main | (intros; apply GlobalTheory.PsiDoubleCoord.main <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints : ∀ (n : ℕ) (A V : Set (Fin n → ℤ)), A.Finite → ∃ (r : ℕ) (v : Fin r → Fin n → ℕ), (∀ t : Fin n → ℝ, ((∀ i, 0 ≤ t i) ∧ (∀ a ∈ A, ∑ i, (a i : ℝ) * t i ≤ 0) ∧ (∀ b ∈ V, ∑ i, (b i : ℝ) * t i = 0)) ↔ ∃ c : Fin r → ℝ, (∀ k, 0 ≤ c k) ∧ t = ∑ k, c k • fun i => (v k i : ℝ)) ∧ ∀ t : Fin n → ℕ, (∀ a ∈ A, ∑ i, a i * (t i : ℤ) ≤ 0) → (∀ b ∈ V, ∑ i, b i * (t i : ℤ) = 0) → ∃ (k : ℕ) (c : Fin r → ℕ), 0 < k ∧ k • t = ∑ j, c j • v j := by
  first | exact @GlobalTheory.MinkWeylReal.cone_orthant_fg | exact GlobalTheory.MinkWeylReal.cone_orthant_fg | (intros; apply GlobalTheory.MinkWeylReal.cone_orthant_fg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem symplecticPair_decomp {g r : ℕ} (hr : r = 2 * g) (M' : Matrix (Fin r) (Fin r) ℚ)
    (hM : M'ᵀ = -M') (ε φ : Matrix (Fin g) (Fin r) ℚ) (h1 : ε * M' * εᵀ = 0)
    (h2 : φ * M' * φᵀ = 0) (h3 : φ * M' * εᵀ = 1) (X : Matrix (Fin g) (Fin r) ℚ) :
    X = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
  have h4 : ε * M' * φᵀ = -1 := by
    have := congrArg Matrix.transpose h3
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM,
      Matrix.transpose_one] at this
    rw [← neg_neg (ε * M' * φᵀ), ← this]
    simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  have hPR : Matrix.fromRows ε φ * (M' * Matrix.fromCols (-φᵀ) εᵀ) = 1 := by
    rw [Matrix.mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_neg,
      h1, h2, h3, h4, neg_neg, neg_zero, Matrix.fromBlocks_one]
  let e : Fin g ⊕ Fin g ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  have hRP : (M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).mp hPR
  calc X = X * ((M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ) := by
        rw [hRP, Matrix.mul_one]
    _ = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
        rw [Matrix.mul_assoc M', Matrix.fromCols_mul_fromRows]
        simp only [Matrix.mul_add, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]

theorem isometry_fixing_rowSpace_shift : ∀ (g r r₀ rk : ℕ) (M T : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ), r = 2 * g → Mᵀ = -M → T * M * Tᵀ = M → c * T = c → (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) → ∃ b : Matrix (Fin g) (Fin g) ℚ, (∀ i j : Fin g, (rk ≤ i.val ∨ rk ≤ j.val) → b i j = 0) ∧ φ * T.map (Int.cast : ℤ → ℚ) = φ + bᵀ * (α * c.map (Int.cast : ℤ → ℚ)) := by
  intro g r r₀ rk M T c α φ β hr hMt hTM hcT hεε hφφ hφε hβ
  have keyZ : T * M * cᵀ = M * cᵀ := by
    calc T * M * cᵀ = T * M * (c * T)ᵀ := by rw [hcT]
      _ = T * M * Tᵀ * cᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc (T * M)]
      _ = M * cᵀ := by rw [hTM]
  have hcTZ : c * T = c := hcT
  have map_mul' : ∀ {a b d : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) (B : Matrix (Fin b) (Fin d) ℤ),
      (A * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ) :=
    fun A B => Matrix.map_mul (f := Int.castRingHom ℚ)
  set M' := M.map (Int.cast : ℤ → ℚ) with hM'
  set T' := T.map (Int.cast : ℤ → ℚ) with hT'
  set c' := c.map (Int.cast : ℤ → ℚ) with hc'
  have key : T' * M' * c'ᵀ = M' * c'ᵀ := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) keyZ
    simpa only [map_mul', Matrix.transpose_map] using this
  have hcT' : c' * T' = c' := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) hcTZ
    simpa only [map_mul'] using this
  have hMt' : M'ᵀ = -M' := by
    rw [hM', ← Matrix.transpose_map, hMt]; ext i j; simp
  set ε := α * c' with hε
  set X := φ * T' - φ with hX
  have hXc : X * M' * c'ᵀ = 0 := by
    rw [hX, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc φ T', Matrix.mul_assoc φ (T' * M'),
      key, Matrix.mul_assoc φ M', sub_self]
  have hXε : X * M' * εᵀ = 0 := by
    rw [hε, Matrix.transpose_mul, ← Matrix.mul_assoc, hXc, Matrix.zero_mul]
  have hdec := symplecticPair_decomp hr M' hMt' ε φ hεε hφφ hφε X
  rw [hXε, Matrix.zero_mul, add_zero] at hdec
  refine ⟨-(X * M' * φᵀ)ᵀ, ?_, ?_⟩
  · intro i j hij
    simp only [Matrix.neg_apply, Matrix.transpose_apply, neg_eq_zero]
    rcases hij with hi | hj
    ·
      have : (X * M' * φᵀ) j i = (X * M' * c'ᵀ * βᵀ) j i := by
        rw [Matrix.mul_assoc (X * M') c'ᵀ, ← Matrix.transpose_mul]
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hβ i hi m]
        simp only [Matrix.mul_apply]
      rw [this, hXc, Matrix.zero_mul, Matrix.zero_apply]
    · have hrow : ∀ m, X j m = 0 := by
        intro m
        have hφj : ∀ m, φ j m = (β * c') j m := hβ j hj
        rw [hX, Matrix.sub_apply, Matrix.mul_apply, hφj m]
        have : ∑ k, φ j k * T' k m = ((β * c') * T') j m := by
          simp only [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hφj k]; simp only [Matrix.mul_apply]
        rw [this, Matrix.mul_assoc, hcT', sub_self]
      simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]
  · rw [Matrix.transpose_neg, Matrix.transpose_transpose, ← hdec, hX]
    abel

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  first | exact @GlobalTheory.lbIso_of_generic_normal_local | exact GlobalTheory.lbIso_of_generic_normal_local | (intros; apply GlobalTheory.lbIso_of_generic_normal_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem posDef_eq_conjTranspose_mul_self_of_isUnit_det :
    ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef →
      ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  intro p P hP
  have h0 : (0 : Matrix (Fin p) (Fin p) ℂ) ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP.posSemidef
  have hB : star (CFC.sqrt P) * CFC.sqrt P = P := by
    rw [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self P h0]
  refine ⟨CFC.sqrt P, ?_, hB⟩
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  rw [← hB, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameFix

theorem coeff_mul_eq_of_same_combinations :
    ∀ (g r r₀ : ℕ) (l l' : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ)
      (T : Matrix (Fin r) (Fin r) ℤ), LinearIndependent ℤ l → (∀ i, l' i = ∑ j, T i j • l j) →
      (∀ i, w i = ∑ j, c i j • l j) → (∀ i, w i = ∑ j, c i j • l' j) → c * T = c := by
  intro g r r₀ l l' w c T hl hl' h1 h2
  ext i m
  have key : ∑ j, c i j • l' j = ∑ m, (c * T) i m • l m := by
    simp only [hl', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have hsum : ∑ m, ((c * T) i m - c i m) • l m = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← key, ← h2, h1, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hl (fun m => (c * T) i m - c i m) hsum m)

end GlobalTheory.FrameFix
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.dickson_exists_finite_subfamily_below : ∀ {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ), ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  first | exact @GlobalTheory.dickson_finite_below_every | exact GlobalTheory.dickson_finite_below_every | (intros; apply GlobalTheory.dickson_finite_below_every <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rat_matrix_common_denom : ∀ (a g : ℕ) (b : Fin a → Matrix (Fin g) (Fin g) ℚ), ∃ (D : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D ∧ ∀ k i j, (B k i j : ℚ) = D * b k i j := by
  intro a g b
  classical
  let D : ℕ := ∏ k, ∏ i, ∏ j, (b k i j).den
  have hdvd : ∀ k i j, (b k i j).den ∣ D := fun k i j =>
    dvd_trans (Finset.dvd_prod_of_mem (fun j => (b k i j).den) (Finset.mem_univ j))
      (dvd_trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (b k i j).den) (Finset.mem_univ i))
        (Finset.dvd_prod_of_mem (fun k => ∏ i, ∏ j, (b k i j).den) (Finset.mem_univ k)))
  refine ⟨D, fun k i j => ((D / (b k i j).den : ℕ) : ℤ) * (b k i j).num, ?_, ?_⟩
  · exact Finset.prod_pos fun k _ => Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (b k i j).den_pos
  · intro k i j
    obtain ⟨m, hm⟩ := hdvd k i j
    have hD : D = (b k i j).den * m := hm
    simp only
    rw [hD, Nat.mul_div_cancel_left _ (b k i j).den_pos]
    push_cast
    rw [mul_comm ((b k i j).den : ℚ) (m : ℚ), _root_.mul_assoc, Rat.den_mul_eq_num]

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.ringOfIntegers_projective_module_int_finrank : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  first | exact @GlobalTheory.finite_projective_int_of_ringOfIntegers | exact GlobalTheory.finite_projective_int_of_ringOfIntegers | (intros; apply GlobalTheory.finite_projective_int_of_ringOfIntegers <;> assumption)
end
