module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele

@[expose] public section

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabFrameCompat

theorem exists_factor {P Q P' Q' : ℕ} (hc : P' + Q' + 1 = P + Q) {x : Fin P ⊕ Fin Q → ℂ}
    (hx : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0)
    {C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    (h1 : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q')
    (h2 : (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) {m : Type} [Fintype m]
    (Y : Matrix (Fin P ⊕ Fin Q) m ℂ) (hY : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) :
    ∃ U : Matrix (Fin P' ⊕ Fin Q') m ℂ, Y = C * U := by
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx h1 h2
  set X : Matrix (Fin P ⊕ Fin Q) Unit ℂ := replicateCol Unit x with hX
  have e : Y = C * (N * Y).toRows₁ + X * (N * Y).toRows₂ := by
    rw [← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hN, Matrix.one_mul]
  set U := (N * Y).toRows₁
  set V := (N * Y).toRows₂
  refine ⟨U, ?_⟩
  have hV : V = 0 := by
    have h3 : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x
        = Uᴴ *ᵥ ((Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x) + Vᴴ *ᵥ ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) := by
      conv_lhs => rw [e]
      rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Matrix.add_mul, add_mulVec,
        Matrix.mul_assoc, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec x Vᴴ]
    rw [hY, h2, mulVec_zero, zero_add] at h3
    have h4 : ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) () = star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x := by
      rw [← mulVec_mulVec]
      rfl
    ext u i
    have h5 := congrFun h3 i
    rw [Pi.zero_apply, mulVec, dotProduct, Fintype.sum_unique] at h5
    have h6 : star (V () i) * (star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x) = 0 := by
      rw [← h4]; exact h5.symm
    rcases mul_eq_zero.1 h6 with h | h
    · simpa using h
    · exact absurd h hx
  rw [hV, Matrix.mul_zero, add_zero] at e
  exact e

theorem exists_compatible_frame : ∀ (P Q P' Q' M M' : ℕ), P' + Q' + 1 = P + Q → M' = P' + Q' → ∀ (G : Matrix (Fin M) (Fin M) ℂ) (G' : Matrix (Fin M') (Fin M') ℂ) (B : Matrix (Fin M) (Fin M') ℂ) (x : Fin M → ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), Aᴴ * Formalism.UG.Jpq P Q * A = G → Bᴴ * G * B = G' → G'.det ≠ 0 → (Bᴴ * G) *ᵥ x = 0 → star (A *ᵥ x) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (A *ᵥ x) ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb (A *ᵥ x) j → ∃ A' : Matrix (Fin P' ⊕ Fin Q') (Fin M') ℂ, A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' ∧ ∀ (g : Matrix (Fin M) (Fin M) ℂ) (g' : Matrix (Fin M') (Fin M') ℂ) (t : UpqT P Q) (t' : UpqT P' Q'), g *ᵥ x = x → g * B = B * g' → UpqT.mat t * A = A * g → UpqT.mat t' * A' = A' * g' → t = j t' := by
  intro P Q P' Q' M M' hc hM G G' B x A hA hB hdet hBx hx j hj
  obtain ⟨C, h1, h2, h3⟩ := hj
  have hY : ((A * B)ᴴ * Formalism.UG.Jpq P Q) *ᵥ (A *ᵥ x) = 0 := by
    rw [mulVec_mulVec, conjTranspose_mul, ← hBx, ← hA]
    simp only [Matrix.mul_assoc]
  obtain ⟨A', hA'⟩ := exists_factor hc hx h1 h2 (A * B) hY
  have hG : A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' := by
    have : (C * A')ᴴ * Formalism.UG.Jpq P Q * (C * A') = G' := by
      rw [← hA', ← hB, ← hA, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [← this, ← h1, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨A', hG, ?_⟩
  intro g g' t t' hg hgB ht ht'
  have hl : (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') * A' = 1 := by
    have := Matrix.nonsing_inv_mul G' (Ne.isUnit hdet)
    rw [← this]
    conv_rhs => arg 2; rw [← hG]
    simp only [Matrix.mul_assoc]
  have e : Fin M' ≃ Fin P' ⊕ Fin Q' := (finCongr hM).trans finSumFinEquiv.symm
  have hr : A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  refine GlobalTheory.UnfoldingCompare.eq_of_frame hc hx h1 h2 ?_ ?_
  · have k : UpqT.mat t * C * A' = UpqT.mat (j t') * C * A' := by
      rw [(h3 t').2, Matrix.mul_assoc, Matrix.mul_assoc, ← hA', ht', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hA', ht, Matrix.mul_assoc, hgB, Matrix.mul_assoc]
    calc UpqT.mat t * C = UpqT.mat t * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [hr, Matrix.mul_one]
      _ = UpqT.mat (j t') * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [← Matrix.mul_assoc _ A', k, Matrix.mul_assoc _ A']
      _ = _ := by rw [hr, Matrix.mul_one]
  · rw [(h3 t').1, mulVec_mulVec, ht, ← mulVec_mulVec, hg]

end GlobalTheory.StabFrameCompat
end

section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabEmbClosed

theorem isClosedEmbedding_conj_fromBlocks {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m (n ⊕ Unit) ℂ) (N : Matrix (n ⊕ Unit) m ℂ) (hNM : N * M = 1) :
    IsClosedEmbedding
      (fun X : Matrix n n ℂ => M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun Y : Matrix m m ℂ => (N * Y * M).toBlocks₁₁) ?_ ?_ ?_
  · intro X
    have : N * (M * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * N) * M
        = fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) := by
      calc _ = (N * M) * fromBlocks X 0 0 (1 : Matrix Unit Unit ℂ) * (N * M) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hNM, Matrix.one_mul, Matrix.mul_one]
    simp only [this, toBlocks_fromBlocks₁₁]
  · have h : Continuous fun Y : Matrix m m ℂ => N * Y * M :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h.matrix_submatrix Sum.inl Sum.inl
  · exact (continuous_const.matrix_mul
      (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
        continuous_const)).matrix_mul continuous_const

theorem isClosedEmbedding_of_isStabEmb : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  intro P Q P' Q' hd x₀ hx j hj
  obtain ⟨C, hC, hCx, hj⟩ := hj
  obtain ⟨N, B, hNM, hMN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hd hx hC hCx
  have key : ∀ g : UpqT P' Q', (j g).mat =
      C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) * N := by
    intro g
    obtain ⟨h1, h2⟩ := hj g
    have h3 : (j g).mat * replicateCol Unit x₀ = replicateCol Unit x₀ := by
      rw [← replicateCol_mulVec, h1]
    have h4 : (j g).mat * C.fromCols (replicateCol Unit x₀) =
        C.fromCols (replicateCol Unit x₀) * fromBlocks g.mat 0 0 (1 : Matrix Unit Unit ℂ) := by
      rw [mul_fromCols, fromCols_mul_fromBlocks, h2, h3]
      simp
    rw [← h4, Matrix.mul_assoc, hMN, Matrix.mul_one]
  refine IsClosedEmbedding.of_comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q)).isEmbedding ?_
  have := (isClosedEmbedding_conj_fromBlocks _ N hNM).comp
    (GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P') (Q := Q'))
  convert this using 1
  funext g
  exact key g

end GlobalTheory.StabEmbClosed
end
