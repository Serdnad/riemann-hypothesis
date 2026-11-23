module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle203
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut.RealInt

open GlobalTheory.RealWeil

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def expM (H s g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ((g - 1)ᴴ * (H * s) * (g - 1) - H * g + (H * g)ᴴ)

theorem expM_herm {H s g : Matrix ι ι ℂ} (hQ : (H * s).PosDef) (hd : (g - 1).det ≠ 0) :
    (expM H s g + (expM H s g)ᴴ).PosDef := by
  have e : expM H s g + (expM H s g)ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
    have h1 : ((g - 1)ᴴ * (H * s) * (g - 1))ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.1.eq]
      simp only [Matrix.mul_assoc]
    unfold expM
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_sub _ (H * g), h1, conjTranspose_conjTranspose]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  rw [e]
  exact hQ.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)))

theorem expM_mul {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) :
    expM H s g * (g * ((1 / 2 : ℂ) • ((1 + s) * g') + (1 / 2 : ℂ) • (1 - s))) = -H * (g - 1) := by
  have hi' : g' * g = 1 := mul_eq_one_comm.1 hi
  have h1 : gᴴ * H = H * g' := by
    calc gᴴ * H = gᴴ * H * g * g' := by rw [Matrix.mul_assoc _ g, hi, Matrix.mul_one]
      _ = _ := by rw [hg]
  have hc' : g' * s = s * g' := by
    calc g' * s = g' * (s * g) * g' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
      _ = _ := by rw [hc, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  have a1 : ∀ x : Matrix ι ι ℂ, gᴴ * (H * x) = H * (g' * x) := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have a2 : ∀ x : Matrix ι ι ℂ, g * (s * x) = s * (g * x) := fun x => by rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
  have a3 : ∀ x : Matrix ι ι ℂ, g' * (s * x) = s * (g' * x) := fun x => by rw [← Matrix.mul_assoc, hc', Matrix.mul_assoc]
  have a4 : ∀ x : Matrix ι ι ℂ, s * (s * x) = x := fun x => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have a5 : ∀ x : Matrix ι ι ℂ, g' * (g * x) = x := fun x => by rw [← Matrix.mul_assoc, hi', Matrix.one_mul]
  unfold expM
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    a1, h1, a2, a3, a4, a5, hi, hi', ← hc, hc', hs, Matrix.neg_mul]
  module

theorem dot_expM {H s g : Matrix ι ι ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef) (z : ι → ℂ) :
    star z ⬝ᵥ expM H s g *ᵥ z = Complex.I * ((-(star z ⬝ᵥ H *ᵥ (g *ᵥ z)).im : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((-(star (Complex.I • s *ᵥ (g *ᵥ z - z)) ⬝ᵥ H *ᵥ (g *ᵥ z - z)).im : ℝ) : ℂ) := by
  have e1 : (g - 1) *ᵥ z = g *ᵥ z - z := by rw [sub_mulVec, one_mulVec]
  have e2 : star z ⬝ᵥ ((g - 1)ᴴ * (H * s) * (g - 1)) *ᵥ z = star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) := by
    rw [← e1, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have e3 : star z ⬝ᵥ (H * g)ᴴ *ᵥ z = star (star z ⬝ᵥ H *ᵥ (g *ᵥ z)) := by
    rw [mulVec_mulVec, ← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec]
  have e4 : ∀ w : ι → ℂ, star (Complex.I • s *ᵥ w) ⬝ᵥ H *ᵥ w = -Complex.I * (star w ⬝ᵥ (H * s) *ᵥ w) := fun w => by
    rw [star_smul, smul_dotProduct, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← hQ.1.eq, conjTranspose_mul, hH]
    simp
  have e5 : (star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)).im = 0 :=
    (Complex.nonneg_iff.1 (hQ.posSemidef.dotProduct_mulVec_nonneg _)).2.symm
  unfold expM
  rw [smul_mulVec, add_mulVec, sub_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, e2, e3, e4, ← mulVec_mulVec z H g]
  generalize star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) = u at e5
  generalize star z ⬝ᵥ H *ᵥ (g *ᵥ z) = w
  apply Complex.ext <;> simp [e5] <;> ring

theorem gauss_det {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    (expM H s g).det⁻¹ * (g - 1).det = ((H * s).det.re⁻¹ : ℝ) * (-s).det * (g.det * dP s g') := by
  have h0 := (GlobalTheory.MatrixGaussian.integral_gaussian ι _ (expM_herm hQ hd)).1
  have h1 := congrArg det (expM_mul hH hs hg hc hi)
  rw [det_mul, det_mul, det_mul] at h1
  have h2 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h3 := hQ.det_pos
  have h4 : ((H * s).det.re : ℂ) = (H * s).det := Complex.ext rfl (Complex.pos_iff.1 h3).2
  rw [Complex.ofReal_inv, h4]
  have h5 := h3.ne'
  unfold dP
  field_simp
  rw [← h2]
  linear_combination (-(-s).det) * h1

end Mat

section Coord

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def unvE (O : Type) (m n : ℕ) : ((Fin m × Fin n) × O → ℂ) ≃L[ℝ] (O → Fin m → Fin n → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse unvecL vecL vecL_unv unv_vecL


omit [DecidableEq O] in
theorem integral_unv (f : (O → Fin m → Fin n → ℂ) → ℂ) (hf : Integrable fun z : (Fin m × Fin n) × O → ℂ => f (unvecL z)) :
    Integrable f ∧ ∃ c : ℝ, 0 < c ∧ ∫ v, f v = c * ∫ z : (Fin m × Fin n) × O → ℂ, f (unvecL z) := by
  haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (O → Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := unvE O m n
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm := Measure.isAddLeftInvariant_eq_smul (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)
  have hp := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure (O → Fin m → Fin n → ℂ))
    (Measure.map e volume)
  generalize Measure.addHaarScalarFactor (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume) = c at hm hp
  refine ⟨?_, c, hp, ?_⟩
  · rw [hm]
    exact (he.integrable_map_iff.2 hf).smul_measure_nnreal
  · conv_lhs => rw [hm]
    rw [integral_smul_nnreal_measure, he.integral_map]
    rfl

theorem det_blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ).det := det_blockDiagonal _

theorem det_blk_sub_one (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a - 1).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det := by
  unfold RealWeil.blk
  rw [← blockDiagonal_one, ← blockDiagonal_sub, det_blockDiagonal]
  rfl

theorem inv_unitary {G a a' : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hi : a * a' = 1) (ha : aᴴ * G * a = G) :
    a * (G⁻¹ * aᴴ) = G⁻¹ := by
  have h1 : a'ᴴ * aᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have h2 : G * a = a'ᴴ * G := by
    conv_rhs => rw [← ha, Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine (inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, h1]

end Coord

open Classical in
theorem gaussR_unv {D : D7} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hQ : (HM S T * blk sT sS).PosDef)
    (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Ix S T → ℂ) : gaussR S T sS sT a b (unvecL z) =
      Complex.exp (-(Real.pi : ℂ) * (star z ⬝ᵥ expM (HM S T) (blk sT sS) (blk b a) *ᵥ z)) := by
  have e1 : actR S T a b (unvecL z) = unvecL (blk b a *ᵥ z) := funext fun τ => (cpt_blk b a z τ).symm
  have e2 : ∀ w : Ix S T → ℂ, jO S T sS sT (unvecL w) = unvecL (Complex.I • blk sT sS *ᵥ w) := fun w => funext fun τ => by
    show Complex.I • (sT τ * cpt w τ * sS τ) = _
    rw [← cpt_blk]
    rfl
  unfold gaussR
  rw [dot_expM HM_herm hQ, im_HM, im_HM, e1, ← map_sub, e2, ← Complex.exp_add, neg_neg, neg_neg]
  congr 1
  ring


open Classical in
theorem integral_gaussR : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  intro D S T sS sT hS hT
  refine ⟨(-blk sT sS).det, fun a a' b b' h => ?_⟩
  obtain ⟨hs, hQ⟩ := HM_cartan hS hT
  have hd : (blk b a - 1).det ≠ 0 := by
    rw [det_blk_sub_one]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (h τ).2.2.2.2.2.2
  have hi : blk b a * blk b' a' = 1 := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · exact (h τ).2.1
    · exact mul_eq_one_comm.1 (h τ).1
  have hc : blk sT sS * blk b a = blk b a * blk sT sS := by
    rw [blk_mul, blk_mul]
    congr 1 <;> funext τ
    · exact (h τ).2.2.2.2.2.1
    · exact (h τ).2.2.2.2.1.symm
  have hg : (blk b a)ᴴ * HM S T * blk b a = HM S T := by
    unfold HM
    rw [blk_conjTranspose, blk_mul, blk_mul]
    congr 1 <;> funext τ
    · rw [Matrix.mul_smul, Matrix.smul_mul, (h τ).2.2.2.1]
    · exact inv_unitary (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ) (h τ).1 (h τ).2.2.1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian _ _ (expM_herm hQ hd)
  simp only [← gaussR_unv hQ] at h1 h2
  obtain ⟨h3, c, hc0, h4⟩ := integral_unv _ h1
  refine ⟨h3, c * (HM S T * blk sT sS).det.re⁻¹, mul_pos hc0 (inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1), ?_⟩
  rw [h4, h2, ← det_blk_sub_one, mul_assoc, gauss_det HM_herm hs hQ hg hc hi hd, Finset.prod_mul_distrib, ← det_blk,
    ← detPlus_blockDiagonal, Complex.ofReal_mul]
  ring

end GlobalTheory.RatAut.RealInt

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ordL_mul_of_ne [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_mul_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {d : K} (hd : d ≠ 0) (x : K) :
    (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul_of_ne (mul_ne_zero hσd hd) hx, ordL_mul_of_ne hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem gram_eq_mul (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι]
    (v : ι → Fin n → K) :
    (Matrix.of fun i j => hform σ H (v i) (v j)) =
      cT σ (Matrix.of fun p i => v i p) * H * Matrix.of fun p i => v i p := by
  ext i j
  simp only [hform, cT, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cols_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {ι : Type} (v : ι → Fin n → K) :
    (Matrix.of fun p i => (M *ᵥ v i) p) = M * Matrix.of fun p i => v i p := by
  ext p i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem det_cT (σ : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι K) :
    (cT σ T).det = σ T.det := by
  unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem gram_det_change (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (b b' : Module.Basis ι K W) :
    ∃ d : K, d ≠ 0 ∧
      (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
        σ d * d * (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set T := b.toMatrix b' with hT
  have hcol : (Matrix.of fun p i => (b' i : Fin n → K) p) = (Matrix.of fun p i => (b i : Fin n → K) p) * T := by
    ext p j
    have hs := congrArg (fun x : W => (x : Fin n → K) p) (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [Matrix.of_apply, ← hs, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.of_apply, hT, Module.Basis.toMatrix_apply, mul_comm]
  have hTT : T * b'.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b'
  have hd : T.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hTT
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨T.det, hd, ?_⟩
  rw [gram_eq_mul σ H (fun i => (b' i : Fin n → K)), gram_eq_mul σ H (fun i => (b i : Fin n → K)), hcol,
    cT_mul]
  set B := Matrix.of fun p i => (b i : Fin n → K) p
  rw [show cT σ T * cT σ B * H * (B * T) = cT σ T * (cT σ B * H * B) * T by simp only [Matrix.mul_assoc]]
  simp only [Matrix.det_mul, det_cT]
  ring

theorem sign_basis [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι K W) (b' : Module.Basis ι' K W) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set e : ι' ≃ ι := b'.indexEquiv b
  have hsub : (Matrix.of fun i j => hform σ H ((b.reindex e.symm) i : Fin n → K) ((b.reindex e.symm) j)) =
      (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).submatrix e e := by
    ext i j
    simp [Module.Basis.reindex_apply]
  obtain ⟨d, hd, hdet⟩ := gram_det_change σ H W (b.reindex e.symm) b'
  rw [hdet, sign_mul_norm σ hσ hd, hsub, Matrix.det_submatrix_equiv_self]

theorem aeval_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    aeval (k⁻¹ * a * k).val Q = (k⁻¹).val * aeval a.val Q * k.val := by
  have hp : ∀ i : ℕ, ((k⁻¹ * a * k : GL (Fin n) K).val) ^ i = (k⁻¹).val * a.val ^ i * k.val := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [hp, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UnitaryClasses.SgnConj

namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ker_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) =
      (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).comap (Matrix.toLin' k.val) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.toLin'_apply, aeval_conj]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun y => k.val *ᵥ y) h
    simpa [Matrix.mulVec_mulVec] using this
  · intro h
    rw [h, Matrix.mulVec_zero]

def invEquiv {n : ℕ} (k : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' (k⁻¹).val) (Matrix.toLin' k.val)
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])

theorem map_invEquiv {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).map (invEquiv k : (Fin n → K) →ₗ[K] (Fin n → K)) =
      LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) := by
  rw [ker_conj, Submodule.map_equiv_eq_comap_symm]
  rfl

theorem sgnOn_conj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K),
    sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  intro K _ _ σ hσ n Q a k
  set V := LinearMap.ker (Matrix.toLin' (aeval a.val Q))
  set V' := LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q))
  let b0 := Module.finBasis K V
  let b'' : Module.Basis (Fin (Module.finrank K V)) K V' :=
    b0.map ((invEquiv k).ofSubmodules V V' (map_invEquiv Q a k))
  have hb'' : ∀ i, (b'' i : Fin n → K) = (k⁻¹).val *ᵥ (b0 i : Fin n → K) := by
    intro i
    simp [b'', Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, invEquiv]
  unfold sgnOn gramOn
  rw [sign_basis σ hσ 1 V' b'' (Module.finBasis K V')]
  congr 3
  rw [gram_eq_mul σ 1 (fun i => (b'' i : Fin n → K)), gram_eq_mul σ _ (fun i => (b0 i : Fin n → K))]
  simp only [hb'']
  rw [cols_mulVec, cT_mul]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.UnitaryClasses.SgnConj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionSpread

theorem triv_lbPow_pull {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (k : ℕ) (φ : Y ⟶ X)
    (h : ∃ t : (Hecke.lbPow M k).Gen, t.IsGen) : ∃ t : (Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
  have hP : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
  have hM' : (M.pull φ).IsLB := LB.isLB_pull hM φ
  have hP' : (Hecke.lbPow (M.pull φ) k).IsLB := LB.isLB_linComb hM' _ _
  have e : ∀ {Z : Scheme.{0}} {N : LB Z} (hN : N.IsLB) (h' : (Hecke.lbPow N k).IsLB),
      CechPic.cls _ h' = k • CechPic.cls N hN := by
    intro Z N hN h'
    apply (CechPic.cls_linComb hN (fun _ : Fin k => 𝟙 Z) (fun _ => 1) h').trans
    simp [CechPic.pull_id]
  rw [← CechPic.cls_eq_zero_iff hP']
  rw [← CechPic.cls_eq_zero_iff hP] at h
  rw [e hM' hP', CechPic.cls_pull hM φ hM', ← map_nsmul, ← e hM hP, h, map_zero]

theorem triv_basicOpen_of_triv_fibre : (∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro hinf R _ _ A _ hA M hM _hrig k hk hpow K _ g₀ ht₀
  haveI := hA.proper
  haveI := hA.smooth
  have hP := GlobalTheory.ProperFinite.nonempty_perf_of_isProper A.hom hM
  haveI : Surjective A.hom := by
    haveI : Surjective ((1 : 𝟙_ (Over (Sp R)) ⟶ A).left ≫ A.hom) := by
      rw [Over.w]
      change Surjective (𝟙 _)
      infer_instance
    exact Surjective.of_comp (1 : 𝟙_ (Over (Sp R)) ⟶ A).left A.hom
  have h₀ := IsPullback.of_hasPullback A.hom (spMap g₀)
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R A.left A.hom M hM hP inferInstance inferInstance K g₀
    _ _ _ h₀ (GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.ExpansionTotal.globalFns A hA h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := GlobalTheory.AbLaw.CubeOpen.exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ _ _ _ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      have hg := IsPullback.of_hasPullback A.hom (spMap g)
      refine (H T g _ _ _ hg (hu r hr)).1 ?_
      have hkT : IsUnit (k : T) := by simpa using hk.map g
      letI : (Over.pullback (spMap g)).Monoidal := (Over.instBraidedPullback (f := spMap g)).toMonoidal
      letI : GrpObj ((Over.pullback (spMap g)).obj A) := Functor.grpObjObj (F := Over.pullback (spMap g))
      have hp := IsPullback.of_hasPullback ((Over.pullback (spMap g)).obj A).hom
        (spMap (Ideal.Quotient.mk (Ideal.span {e})))
      refine hinf T e he he' ((Over.pullback (spMap g)).obj A)
        (Out.TLinPf.isAb_pullback (spMap g) A hA) (M.pull (pullback.fst A.hom (spMap g)))
        (LB.isLB_pull hM _) k hkT (triv_lbPow_pull hM k _ hpow) _ _ _ hp ?_
      have hq := hp.paste_horiz hg
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hq
      exact GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _
        ((H _ _ _ _ _ hq ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle))
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range ((A.hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ A.hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact GlobalTheory.AbLaw.CubeOpen.triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm)
    (hp.lift_fst _ _ _) ht

end GlobalTheory.TorsionSpread
end
end
