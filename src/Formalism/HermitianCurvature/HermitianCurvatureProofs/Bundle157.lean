module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053

@[expose] public section

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leviElement_mem_GV {k p ρ : ℕ} (q : Matrix (Fin p) (Fin p) ℂ) (hq : IsUnit q.det) : U.muP k p ρ q ∈ B.GV k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.slice_membership k p ρ).2.1 q (isUnit_iff_ne_zero.mp hq)

def MuPToOm : Prop := ∀ (k p ρ : ℕ) (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ), inWb k (p + ρ) z → inWb k (p + ρ) z' →
  ∀ y ∈ domP k (p + ρ) p z z', y ∈ B.GV k (p + ρ) →
  ∃ q : Matrix (Fin p) (Fin p) ℂ, IsUnit q.det ∧ ∃ V ∈ nhds y, IsCompact V ∧
    ∀ g ∈ V, g ∈ B.GV k (p + ρ) → U.muP k p ρ q * g ∈ JF.Om k (p + ρ) z z'

section zhat

variable {k p ρ : ℕ}

theorem corner_matrix_levi_block_three (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ)
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.muP k p ρ q * U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks ((qᴴ)⁻¹ * (G.wMat p * BlochKatoReduction))
        ((qᴴ)⁻¹ * (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z')))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) := by
  unfold U.muP
  rw [Ux3.block3_mul, Ux3.z_hat_of_block3 z z' hz hz']
  have hw : ∀ M : Matrix (Fin p) (Fin p) ℂ, G.wMat p * (G.wMat p * M * G.wMat p) = M * G.wMat p := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Ux3.wMat_mul_self, Matrix.one_mul]
  congr 2 <;> simp only [Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, hw, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc (G.wMat p), hw]; simp only [Matrix.mul_assoc]

theorem zhat_eq_blk (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks (G.wMat p * BlochKatoReduction)
        (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) :=
  Ux3.z_hat_of_block3 z z' hz hz' _ _ _ _ _ _ _ _ _

theorem minor_gen {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hl : m ≤ ρ + 1) (h : p + m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A (Bm.submatrix id (Fin.castLE hl))
        (Cm.submatrix (Fin.castLE hl) id) (Dm.submatrix (Fin.castLE hl) (Fin.castLE hl))) := by
  ext a b
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    simp [Matrix.reindex_apply, Ux3.eC_symm_castAdd h, Ux3.eC_symm_natAdd h hl]

theorem minor_low {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hmp : m ≤ p) (h : m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE hmp) (Fin.castLE hmp) := by
  have e : ∀ a : Fin m, (Ux3.eC p ρ).symm (Fin.castLE h a) = Sum.inl (Fin.castLE hmp a) := by
    intro a; rw [Equiv.symm_apply_eq]; ext; simp [Ux3.column_index_first_val]
  ext a b
  simp [Matrix.reindex_apply, e]

theorem zh_eq_blk (y : B.Mat k (p + ρ)) :
    G.wMat p * y.submatrix (fun a => U.eB k p ρ (Sum.inr a)) (fun b => U.eB k p ρ (Sum.inl (Sum.inl b))) =
      U.Zh k p ρ y := by
  ext a b
  rw [Ux3.wMat_mul_apply]
  simp only [Matrix.submatrix_apply, U.Zh]
  congr 1
  all_goals (ext; first | (rw [Ux3.block_index_last_val]; simp [Fin.val_rev]; omega) | (rw [Ux3.block_index_first_val]))

theorem minor_leviElement_mul_high (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) (m : ℕ) (hm : m ≤ ρ + 1) :
    Dmin k (p + ρ) z z' (U.muP k p ρ q * g) ⟨p + m, by omega⟩ =
      ((qᴴ)⁻¹).det * Dmin k (p + ρ) z z' g ⟨p + m, by omega⟩ := by
  have hg := Ux3.block3_eta g
  unfold Dmin
  rw [hg, corner_matrix_levi_block_three z z' hz hz', zhat_eq_blk z z' hz hz']
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det = _ * ((Matrix.reindex _ _ _).submatrix
      (Fin.castLE (show p + m ≤ p + ρ + 1 by omega)) (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det
  rw [minor_gen _ _ _ _ hm, minor_gen _ _ _ _ hm, Matrix.det_reindex_self, Matrix.det_reindex_self]
  set Q := (qᴴ)⁻¹
  have e : ∀ (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin m) ℂ) (Cm : Matrix (Fin m) (Fin p) ℂ)
      (Dm : Matrix (Fin m) (Fin m) ℂ),
      Matrix.fromBlocks (Q * A) (Q * Bm) Cm Dm = Matrix.fromBlocks Q 0 0 1 * Matrix.fromBlocks A Bm Cm Dm := by
    intro A Bm Cm Dm
    rw [Matrix.fromBlocks_multiply]
    simp
  have hsub : ∀ (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ),
      (Q * Bm).submatrix id (Fin.castLE hm) = Q * Bm.submatrix id (Fin.castLE hm) := by
    intro Bm; ext a b; simp [Matrix.mul_apply]
  rw [hsub, e, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem minor_leviElement_mul_low (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hA : IsUnit (U.Zh k p ρ y).det) (m : ℕ) (hmp : m ≤ p) :
    Dmin k (p + ρ) z z' (U.muP k p ρ (U.Zh k p ρ y)ᴴ * y) ⟨m, by omega⟩ = 1 := by
  have hg := Ux3.block3_eta y
  unfold Dmin
  conv_lhs => rw [hg]
  rw [corner_matrix_levi_block_three z z' hz hz', ← hg]
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show m ≤ p + ρ + 1 by omega))).det = 1
  rw [minor_low _ _ _ _ hmp, zh_eq_blk, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul _ hA]
  have : (1 : Matrix (Fin p) (Fin p) ℂ).submatrix (Fin.castLE hmp) (Fin.castLE hmp) = 1 := by
    ext a b; simp [Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

end zhat

section main

variable {k p ρ : ℕ}

theorem gf_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) :
    Gf k (p + ρ) z z' (U.muP k p ρ q * g) = Complex.normSq ((qᴴ)⁻¹).det * Gf k (p + ρ) z z' g := by
  have e1 : Fin.last (p + ρ + 1) = (⟨p + (ρ + 1), by omega⟩ : Fin (p + ρ + 2)) := Fin.ext rfl
  have e0 : (⟨p + ρ, by omega⟩ : Fin (p + ρ + 2)) = ⟨p + ρ, by omega⟩ := rfl
  unfold Gf
  rw [e1, minor_leviElement_mul_high z z' hz hz' q g (ρ + 1) le_rfl, minor_leviElement_mul_high z z' hz hz' q g ρ (by omega),
    Complex.normSq_mul, Complex.normSq_mul]
  ring

theorem det_Q_ne {A : Matrix (Fin p) (Fin p) ℂ} (hAd : A.det ≠ 0) : (((Aᴴ)ᴴ)⁻¹).det ≠ 0 := by
  rw [Matrix.conjTranspose_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hAd

theorem omPlus_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hy : y ∈ domP k (p + ρ) p z z') (hAd : (U.Zh k p ρ y).det ≠ 0) :
    U.muP k p ρ (U.Zh k p ρ y)ᴴ * y ∈ Q.OmPlus k (p + ρ) z z' := by
  have hQ := det_Q_ne hAd
  refine ⟨fun l hl => ?_, ?_⟩
  · by_cases hlp : l.val ≤ p
    · have e : l = ⟨l.val, by omega⟩ := Fin.ext rfl
      rw [e, minor_leviElement_mul_low z z' hz hz' y (isUnit_iff_ne_zero.mpr hAd) l.val hlp]
      exact one_ne_zero
    · have e : l = ⟨p + (l.val - p), by omega⟩ := Fin.ext (by simp only; omega)
      have hyl := hy.1 l (by omega) hl
      rw [e] at hyl ⊢
      rw [minor_leviElement_mul_high z z' hz hz' _ y (l.val - p) (by omega)]
      exact mul_ne_zero hQ hyl
  · rw [gf_muP z z' hz hz']
    exact mul_pos (Complex.normSq_pos.mpr hQ) hy.2

end main

theorem mem_of_sub_pre {k n : ℕ} {S : Set (B.Mat k n)} {f : B.Mat k n → B.Mat k n} {V : Set (B.Mat k n)}
    (hVO : V ⊆ {g | f g ∈ S}) {g : B.Mat k n} (hg : g ∈ V) : f g ∈ S := hVO hg

theorem mem_Om_of {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {x : B.Mat k r} (h1 : x ∈ B.GV k r)
    (h2 : x ∈ Q.OmPlus k r z z') : x ∈ JF.Om k r z z' := ⟨h1, h2⟩

theorem levi_move_into_big_cell : MuPToOm := by
  intro k p ρ z z' hz hz' y hy hyG
  have hDp : Dmin k (p + ρ) z z' y ⟨p, by omega⟩ ≠ 0 := hy.1 ⟨p, by omega⟩ (le_refl p) (by simp)
  have hAd : (U.Zh k p ρ y).det ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.Ux3.zhDmin k p ρ z z' y
    unfold U.DjU at h
    rw [← h]; exact hDp
  have hqu : IsUnit ((U.Zh k p ρ y)ᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hAd)
  have hy1 := omPlus_muP z z' hz hz' y hy hAd
  have hO : IsOpen {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} :=
    (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus z z').preimage (continuous_const.matrix_mul continuous_id)
  have hy1' : y ∈ {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} := hy1
  have hmem := hO.mem_nhds hy1'
  have hLC : LocallyCompactSpace (B.Mat k (p + ρ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (2 * (p + ρ) + k + 1) → Fin (2 * (p + ρ) + k + 1) → ℂ))
  obtain ⟨V, hV, hVO, hVc⟩ := local_compact_nhds hmem
  refine ⟨(U.Zh k p ρ y)ᴴ, hqu, ?_⟩
  refine ⟨V, hV, hVc, ?_⟩
  intro g hg hgG
  have h1 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ B.GV k (p + ρ) := by
    have hm := leviElement_mem_GV (k := k) (ρ := ρ) (U.Zh k p ρ y)ᴴ hqu
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hm hgG
  have h2 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z' :=
    mem_of_sub_pre (f := fun g => U.muP k p ρ (U.Zh k p ρ y)ᴴ * g) hVO hg
  exact mem_Om_of h1 h2

end Formalism.FourierDecayAlt.P.PBQ
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

theorem fn_eq_of_radR (hB : NF.RadBase k r z z' μs π π') (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ}
    (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : ∀ ζ, NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ)) :
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c' := by
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := Ψ.2
  funext g
  by_cases hg : g ∈ Q.Glev k r (Fin.last r) ∧ 0 < Q.GGl k r z z' g
  · obtain ⟨hgG, hG'⟩ := hg
    have hζq : Tz k r z * Tz k r z' < Complex.normSq (Q.zetaL k r z z' (Fin.last r) g) := by
      have h1 := hG'
      unfold Q.GGl at h1
      linarith
    obtain ⟨a, ha, b, hb, hgeq⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk hz hz' hT hT' hsec hgG hG'
    generalize Q.zetaL k r z z' (Fin.last r) g = ζ at hζq hgeq
    have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζq⟩
    have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζq⟩
    have e1 := he (c, NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq) a ha b hb
    have e2 := he (c', NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq') a ha b hb
    have e3 := h ζ
    rw [radR_apply _ hq, radR_apply _ hq'] at e3
    dsimp only at e1 e2 e3
    rw [hgeq, e1, e2, e3]
  · have n1 : (c, g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    have n2 : (c', g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    exact (h0 (c, g) n1).trans (h0 (c', g) n2).symm

theorem t_slice (hB : NF.RadBase k r z z' μs π π') (X : Q.ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2)
    (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ} (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c') {ζ : ℂ} (hζ : ζ ∈ Ann z z') :
    NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ) := by
  obtain ⟨-, hz, hz', -, -, hsec, -, -, -, -⟩ := hB
  have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζ⟩
  have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζ⟩
  rw [radR_apply _ hq, radR_apply _ hq', X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq),
    X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq')]
  dsimp only
  rw [h]

def pw (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i, crd (s i) (ζ - ζ0)) • X)

theorem pw_smooth (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (pw j s ζ0 X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff.comp (contDiff_id.sub contDiff_const))).smul
    contDiff_const

def wt (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i ∈ Finset.univ \ t, crd (s i) ζ) • X)

theorem wt_smooth (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (wt j s t X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff)).smul contDiff_const

theorem pw_expand (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    pw j s ζ0 X = fun ζ => ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • wt j s t X ζ := by
  funext ζ
  have hp : ∏ i, crd (s i) (ζ - ζ0) = ∏ i, (-crd (s i) ζ0 + crd (s i) ζ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub]
    ring
  simp only [pw, wt, hp, Finset.prod_add, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  ring


variable (z z' μs π π' Pr) in
def Bsl (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  if hG : Gd z z' μs π π' Pr then
    LinearMap.toContinuousLinearMap
      { toFun := fun X => VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0
        map_add' := fun X X' => by
          have e : pw j s ζ0 (X + X') = fun ζ => pw j s ζ0 X ζ + pw j s ζ0 X' ζ := by
            funext ζ
            simp only [pw, smul_add]
          rw [e, VV_add hG (pw_smooth j s ζ0 X) (pw_smooth j s ζ0 X')]
        map_smul' := fun c X => by
          have e : pw j s ζ0 (c • X) = fun ζ => c • pw j s ζ0 X ζ := by
            funext ζ
            simp only [pw]
            rw [smul_comm]
          rw [e, VV_smulR hG (pw_smooth j s ζ0 X)]
          rfl }
  else 0

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

theorem Bsl_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    Bsl z z' μs π π' Pr T c0 j s ζ0 X = VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0 := by
  unfold Bsl
  rw [dite_eq_left hG]
  rfl

theorem Bsl_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) (s : Fin j → Fin 2) :
    ContDiffOn ℝ ∞ (fun ζ0 => Bsl z z' μs π π' Pr T c0 j s ζ0) (Ann z z') := by
  rw [contDiffOn_clm_apply]
  intro X
  have key : ∀ ζ0, Bsl z z' μs π π' Pr T c0 j s ζ0 X = ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • VV z z' μs π π' Pr T c0 (wt j s t X) ζ0 := by
    intro ζ0
    rw [Bsl_apply hG, pw_expand, VV_sum hG _ _ (fun t => (wt_smooth j s t X).const_smul _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact VV_smulR hG (wt_smooth j s t X) _ ζ0
  refine (ContDiffOn.sum fun t _ => ?_).congr fun ζ0 _ => key ζ0
  exact (contDiff_prod fun i _ => (crd (s i)).contDiff.neg).contDiffOn.smul (VV_smooth hG hc0)


variable (z z' μs π π' Pr T c0) in
def AA (j : ℕ) (ζ0 : ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i)))

theorem AA_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (ζ0 : ℂ)
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp)) :
    AA z z' μs π π' Pr T c0 j ζ0 m =
      VV z z' μs π π' Pr T c0 (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) ζ0 := by
  have e : (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) =
      fun ζ => ∑ s : Fin j → Fin 2, pw j s ζ0 (m (fun i => e2 (s i))) ζ := by
    funext ζ
    rw [ml_expand m (ζ - ζ0), Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [pw, smul_smul]
  rw [e, VV_sum hG _ _ (fun s => pw_smooth j s ζ0 _)]
  unfold AA
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, Bsl_apply hG]

theorem AA_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) :
    ContDiffOn ℝ ∞ (AA z z' μs π π' Pr T c0 j) (Ann z z') := by
  have e : AA z z' μs π π' Pr T c0 j = fun ζ0 => ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i))) := rfl
  rw [e]
  exact ContDiffOn.sum fun s _ => (Bsl_smooth hG hc0 j s).clm_comp contDiffOn_const

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
end

section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section


section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem ttp_eq (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold Formalism.FourierDecayAlt.TBB.TTp
  rw [hz, hz']
  rfl

theorem isBoundedBilinearMap_compSh :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq' →L[ℂ] Wq) => q.1.comp q.2) :=
  { add_left := fun x₁ x₂ y => ContinuousLinearMap.add_comp x₁ x₂ y
    smul_left := fun c x y => ContinuousLinearMap.smul_comp c x y
    add_right := fun x y₁ y₂ => ContinuousLinearMap.comp_add x y₁ y₂
    smul_right := fun c x y => ContinuousLinearMap.comp_smul x c y
    bound := ⟨1, one_pos, fun x y => by simpa only [one_mul] using
      ContinuousLinearMap.opNorm_comp_le x y⟩ }


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_compSh {k r : ℕ} {f : B.Mat k r → (Wq →L[ℂ] Wp)} {A : B.Mat k r → (Wq' →L[ℂ] Wq)}
    (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (f2 g), hU1.inter hU2, ⟨hg1, hg2⟩, ?_,
    fun g hg hgv => by
      show (f g).comp (A g) = (f1 g).comp (f2 g)
      rw [he1 g hg.1 hgv, he2 g hg.2 hgv]⟩
  have hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (f1 g, f2 g)) (U1 ∩ U2) := by
    first
    | exact (hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right)
    | exact (hc1.mono Set.inter_subset_left).prod (hc2.mono Set.inter_subset_right)
  exact isBoundedBilinearMap_compSh.contDiff.comp_contDiffOn hp


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_fpmSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hA : B.CkOn ⊤ (B.GV P.k P.r) A) : B.CkOn ⊤ (B.GV P.k P.r) (fpmSh q f A p₀) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat P.k P.r => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf q.T.base.z q.T.base.z').pow p₀)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc (ckOn_compSh hf hA)

end sh

def PolyOp {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (d : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∃ (n : ℕ) (c : Fin n → B.Mat k r → ℂ) (L : Fin n → (Wq' →L[ℂ] Wq)),
    (∀ i, U.IsPolyDeg d (c i)) ∧ ∀ g, A g = ∑ i, c i g • L i

def FpmShDecay : Prop :=
  ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ) (d p₀ : ℕ),
    (∀ m : ℕ, B.InCC A₀ m f) → PolyOp d A →
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m (fpmSh q f A p₀)


end

end Formalism.FourierDecayAlt.P.CutBPEq
end
