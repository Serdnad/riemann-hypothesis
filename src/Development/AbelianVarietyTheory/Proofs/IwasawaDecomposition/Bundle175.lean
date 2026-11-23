module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem kerAlg_exponent {P Q : ℕ} (B : Matrix (Fin P) (Fin Q) ℂ) (C : Matrix (Fin Q) (Fin P) ℂ)
    (h : IsUnit (1 - C * B).det) (a c : Fin P → ℂ) (b d s u : Fin Q → ℂ) :
    -(b ⬝ᵥ s) + -(d ⬝ᵥ u) + (a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
      + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c) =
    ((a + s ᵥ* C) ⬝ᵥ (c + B *ᵥ u) - s ⬝ᵥ u) -
      (a ᵥ* B + d - s ᵥ* (1 - C * B)) ⬝ᵥ (1 - C * B)⁻¹ *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) := by
  have h1 := Matrix.nonsing_inv_mul _ h
  have h2 := Matrix.mul_nonsing_inv _ h
  generalize (1 - C * B)⁻¹ = N at h1 h2 ⊢
  have h3 : C * B * N = N - 1 := by rw [← h2, Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
  have h4 : N * (C * B) = N - 1 := by rw [← h1, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
  have hM : (1 - B * C)⁻¹ = 1 + B * N * C := by
    apply Matrix.inv_eq_right_inv
    have : B * C * (B * N * C) = B * (C * B * N) * C := by simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, this, h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_one]
    abel
  have hMB : (1 + B * N * C) * B = B * N := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h4, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hM, hMB]
  have e1 : N *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) = u - N *ᵥ (b + C *ᵥ c) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_neg]; abel
  have e2 : (s ᵥ* (1 - C * B)) ⬝ᵥ N *ᵥ (b + C *ᵥ c) = s ⬝ᵥ (b + C *ᵥ c) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e1, dotProduct_sub, sub_dotProduct _ _ (N *ᵥ _), e2]
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, ← Matrix.dotProduct_mulVec, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub,
    dotProduct_comm b s]
  ring

theorem kerAlg_proj {P Q : ℕ} (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det)
    (h' : IsUnit Y'.toRows₂.det) :
    Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q =
      Matrix.fromRows (matA Y') 1 * (1 - (matA Y)ᴴ * matA Y')⁻¹ * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
  have hH : IsUnit (Y.toRows₂ᴴ).det := by rw [Matrix.det_conjTranspose]; exact h.star
  have e0 : Yᴴ * Jm P Q * Y' = (-Y.toRows₂ᴴ) * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
    rw [Matrix.neg_mul, Matrix.neg_mul, ← form_factor Y Y' h h', neg_neg]
  have e1 : Yᴴ * Jm P Q = (-Y.toRows₂ᴴ) * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
    conv_lhs => rw [frame_eq Y h]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, baseY, Jm, Formalism.UG.Jpq,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.neg_mul,
      ← Matrix.mul_neg]
    congr 1
    ext i (j | j) <;> simp
  have hN : IsUnit (-Y.toRows₂ᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det] at hH ⊢; exact hH.neg
  rw [e0, Matrix.mul_assoc _ Yᴴ, e1, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e2 := frame_eq Y' h'
  generalize matA Y' = B at e2 ⊢
  generalize Y'.toRows₂ = Z at e2 h' ⊢
  subst e2
  simp only [Matrix.mul_assoc, baseY]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ h', Matrix.nonsing_inv_mul_cancel_left _ _ hN]

theorem kerAlg : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  intro P Q Y Y' v φ v' φ' h h' hK A B a b c d M N
  have hs : star (scal Y v φ) = ((Y.toRows₂ᴴ).det)⁻¹ * Complex.exp (-(b ⬝ᵥ star (v ∘ Sum.inr))) := by
    rw [scal, star_mul', star_inv₀, Matrix.det_conjTranspose, Complex.star_def, ← Complex.exp_conj]
    congr 2
    simp [b, dotProduct]
  have hs' : scal Y' v' φ' = (Y'.toRows₂.det)⁻¹ * Complex.exp (-(d ⬝ᵥ (v' ∘ Sum.inr))) := rfl
  have ha : star (v ∘ Sum.inl) = a + star (v ∘ Sum.inr) ᵥ* Aᴴ := by
    have : a = star (v ∘ Sum.inl - A *ᵥ (v ∘ Sum.inr)) := rfl
    rw [this, star_sub, Matrix.star_mulVec]; abel
  have hb : b = Aᴴ *ᵥ star (φ ∘ Sum.inl) + star (φ ∘ Sum.inr) := by
    have : b = star ((φ ∘ Sum.inl) ᵥ* A + φ ∘ Sum.inr) := rfl
    rw [this, star_add, Matrix.star_vecMul]
  have hc : v' ∘ Sum.inl = c + B *ᵥ (v' ∘ Sum.inr) := by
    have : c = v' ∘ Sum.inl - B *ᵥ (v' ∘ Sum.inr) := rfl
    rw [this]; abel
  have hd : d = (φ' ∘ Sum.inl) ᵥ* B + φ' ∘ Sum.inr := rfl
  have hJ1 : star v ᵥ* Jm P Q = Sum.elim (star (v ∘ Sum.inl)) (-star (v ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.vecMul_fromBlocks]
    ext (i | i) <;> simp [Matrix.vecMul_neg]
  have hJ2 : Jm P Q *ᵥ star φ = Sum.elim (star (φ ∘ Sum.inl)) (-star (φ ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_mulVec]
    ext (i | i) <;> simp [Matrix.neg_mulVec]
  have e0 : (star v ᵥ* Jm P Q) ⬝ᵥ v' = (a + star (v ∘ Sum.inr) ᵥ* Aᴴ) ⬝ᵥ (c + B *ᵥ (v' ∘ Sum.inr))
      - star (v ∘ Sum.inr) ⬝ᵥ (v' ∘ Sum.inr) := by
    rw [← ha, ← hc, hJ1]
    simp [dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]
  have e1 : (star v ᵥ* Jm P Q + φ') ᵥ* Matrix.fromRows B 1 =
      a ᵥ* B + d - star (v ∘ Sum.inr) ᵥ* (1 - Aᴴ * B) := by
    have : star v ᵥ* Jm P Q + φ' = Sum.elim (star (v ∘ Sum.inl) + φ' ∘ Sum.inl)
        (-star (v ∘ Sum.inr) + φ' ∘ Sum.inr) := by
      rw [hJ1]; ext (i | i) <;> rfl
    rw [this, Matrix.sumElim_vecMul_fromRows, ha, hd]
    simp only [Matrix.add_vecMul, Matrix.vecMul_one, Matrix.vecMul_sub, Matrix.vecMul_vecMul]
    abel
  have e2 : Matrix.fromCols (-Aᴴ) 1 *ᵥ (Jm P Q *ᵥ star φ + v') =
      -(b + Aᴴ *ᵥ c) + (1 - Aᴴ * B) *ᵥ (v' ∘ Sum.inr) := by
    have : Jm P Q *ᵥ star φ + v' = Sum.elim (star (φ ∘ Sum.inl) + v' ∘ Sum.inl)
        (-star (φ ∘ Sum.inr) + v' ∘ Sum.inr) := by
      rw [hJ2]; ext (i | i) <;> rfl
    rw [this, Matrix.fromCols_mulVec_sumElim, hb]
    conv_lhs => rw [hc]
    simp only [Matrix.mulVec_add, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.neg_mulVec,
      Matrix.neg_mul]
    abel
  have key := kerAlg_exponent B Aᴴ hK a c b d (star (v ∘ Sum.inr)) (v' ∘ Sum.inr)
  rw [ker, kerAlg_proj Y Y' h h', form_factor Y Y' h h', ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _ * _),
    ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _), Matrix.dotProduct_mulVec _ (Matrix.fromRows _ _), e0, e1, e2,
    ← key, hs, hs', Complex.exp_add (-_ + -_), Complex.exp_add (-_) (-_), Matrix.det_mul, Matrix.det_mul]
  simp only [mul_inv, M, N, A, B]
  ring

end GlobalTheory.OscGauss

end
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

def fockQRight {σ : Type} (f : MvPolynomial σ ℚ) : MvPolynomial σ ℚ →ₗ[ℚ] ℚ where
  toFun g := Formalism.GradedWeylDivisibility.fockQ f g
  map_add' g g' := by
    show Formalism.GradedWeylDivisibility.fockQ f (g + g') = Formalism.GradedWeylDivisibility.fockQ f g + Formalism.GradedWeylDivisibility.fockQ f g'
    rw [(Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g g' f 1).1, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1,
      (Formalism.GradedWeylDivisibility.fockQPos σ g' f).1]
  map_smul' c g := by
    show Formalism.GradedWeylDivisibility.fockQ f (c • g) = c • Formalism.GradedWeylDivisibility.fockQ f g
    rw [smul_eq_mul, (Formalism.GradedWeylDivisibility.fockQPos σ f _).1, (Formalism.GradedWeylDivisibility.fockQBilin σ g 0 f c).2, (Formalism.GradedWeylDivisibility.fockQPos σ g f).1]

theorem fockQRight_apply {σ : Type} (f g : MvPolynomial σ ℚ) : fockQRight f g = Formalism.GradedWeylDivisibility.fockQ f g := rfl

theorem dual_bases_colProd : (∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h) →
  ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b g : ι → MvPolynomial (Fin N × Fin N) ℚ)
    (c : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ι → ℤ) (d : ι → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ℤ) (Nc : ℚ), Nc ≠ 0 ∧
    (∀ J, GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = ∑ k, (c J k : ℚ) • b k) ∧
    (∀ k, b k = ∑ J, (d k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ k, g k = ∑ J, (c J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0) ∧
    Submodule.span ℤ (Set.range g) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
  classical
  intro H N Y hY
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  haveI : Fintype (Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r)) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N _).fintype
  obtain ⟨b, d, hb, hd, hbd⟩ := GlobalTheory.StdDual.exists_dual_bases N (fun r : Fin N => Y.rowLen r) hanti
  set Nc := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) with hNc
  have hNc0 : Nc ≠ 0 := ((Formalism.GradedWeylDivisibility.fockQPos _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
    (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have H' := H N Y hY
  clear H
  set C := GlobalTheory.WeylMinorDual.colProd ℚ N Y hY with hCdef
  have hspanC : Submodule.span ℤ (GlobalTheory.StdDual.bidSet ℚ N (fun r : Fin N => Y.rowLen r)) =
      Submodule.span ℤ (Set.range C) := by
    rw [← GlobalTheory.StdDual.dualWeyl_intQ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY, Submodule.map_span,
      ← Set.range_comp]
    congr 2
    funext J
    exact Formalism.L2.DIV.fk_map_bidet (Int.castRingHom ℚ) _ _ _
  have hbC : Submodule.span ℤ (Set.range b) = Submodule.span ℤ (Set.range C) := hb.trans hspanC
  have hCb : ∀ J, C J ∈ Submodule.span ℤ (Set.range b) := fun J => hbC ▸ Submodule.subset_span ⟨J, rfl⟩
  have hbCm : ∀ k, b k ∈ Submodule.span ℤ (Set.range C) := fun k => hbC ▸ Submodule.subset_span ⟨k, rfl⟩
  choose c hc using fun J => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hCb J)
  choose d' hd' using fun k => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hbCm k)
  have hcQ : ∀ J, C J = ∑ k, (c J k : ℚ) • b k := fun J => by
    rw [← hc J]; simp only [Int.cast_smul_eq_zsmul]
  have hdQ : ∀ k, b k = ∑ J, (d' k J : ℚ) • C J := fun k => by
    rw [← hd' k]; simp only [Int.cast_smul_eq_zsmul]
  set g := fun k => ∑ J, (c J k : ℚ) • C J with hg
  have hdb : ∀ j k, Formalism.GradedWeylDivisibility.fockQ (d j) (b k) = if k = j then Nc else 0 := fun j k =>
    (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1.trans (hbd k j)
  have hdC : ∀ j J, Formalism.GradedWeylDivisibility.fockQ (d j) (C J) = (c J j : ℚ) * Nc := by
    intro j J

    rw [hcQ J, ← fockQRight_apply, map_sum]
    simp only [map_smul, fockQRight_apply, hdb, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hgi : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = ∑ J, (c J k : ℚ) * Formalism.GradedWeylDivisibility.fockQ (b i) (C J) := by
    intro i k

    rw [← fockQRight_apply, hg, map_sum]
    simp only [map_smul, fockQRight_apply, smul_eq_mul]
  have key : ∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0 := by
    intro i k
    have hmem : b i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.span_le_restrictScalars ℤ ℚ _ (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    have h1 := congrArg (fockQRight (d k)) (H' (b i) hmem)

    rw [map_sum, map_smul] at h1
    simp only [map_smul, fockQRight_apply, smul_eq_mul, hdC] at h1
    rw [hdb] at h1
    rw [hgi]
    apply mul_right_cancel₀ hNc0
    rw [Finset.sum_mul]
    exact Eq.trans (Finset.sum_congr rfl fun J _ => by ring) (h1.trans (mul_comm _ _))
  have hgd : ∀ k, g k = d k := by
    intro k
    have hg1 : g k ∈ Submodule.span ℤ (Set.range b) := by
      rw [hbC, hg]
      refine Submodule.sum_mem _ fun J _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)
    have hd1 : d k ∈ Submodule.span ℤ (Set.range b) := by
      have h2 : d k ∈ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
        rw [GlobalTheory.StdDual.weyl_intQ, ← hd]
        exact Submodule.subset_span ⟨k, rfl⟩
      have h3 := Submodule.map_mono (f := Formalism.GradedWeylDivisibility.intQ N N) (Formalism.GradedWeylDivisibility.weylLeDual ℤ N N le_rfl _ hanti) h2
      rwa [GlobalTheory.StdDual.dualWeyl_intQ, ← hb] at h3
    have hx := Submodule.sub_mem _ hg1 hd1
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have horth : ∀ i, Formalism.GradedWeylDivisibility.fockQ (g k - d k) (b i) = 0 := by
      intro i
      rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← fockQRight_apply, map_sub, fockQRight_apply, fockQRight_apply, key,
        ← (Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, hdb]
      split_ifs with h1 h2 h2 <;> first | rfl | simp | (exact absurd h1.symm h2) | (exact absurd h2.symm h1)
    have h0 : Formalism.GradedWeylDivisibility.fockQ (g k - d k) (g k - d k) = 0 := by
      rw [← fockQRight_apply]
      nth_rewrite 2 [← ha]

      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, fockQRight_apply, horth, smul_zero]
    by_contra hne
    exact (ne_of_gt ((Formalism.GradedWeylDivisibility.fockQPos _ (g k - d k) (g k - d k)).2 (sub_ne_zero.mpr hne))) h0
  refine ⟨Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r), inferInstance, inferInstance, b, g, c, d', Nc, hNc0,
    hcQ, hdQ, fun k => rfl, key, ?_⟩
  have : g = d := funext hgd
  rw [this, hd, GlobalTheory.StdDual.weyl_intQ]

end GlobalTheory.WeylLatDualProof
end
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem prod_zsum_expand {A : Type*} [CommRing A] {L : Type*} [Fintype L] [DecidableEq L]
    {α β : L → Type*} [∀ s, Fintype (β s)] (f : ∀ s, α s → A) (g : ∀ s, β s → A)
    (c : ∀ s, α s → β s → ℤ) (h : ∀ s j, f s j = ∑ k, c s j k • g s k) (j : ∀ s, α s) :
    ∏ s, f s (j s) = ∑ κ : (∀ s, β s), (∏ s, c s (j s) (κ s)) • ∏ s, g s (κ s) := by
  simp only [h, zsmul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

theorem norm_dual_zsum_le_one (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℂ_[p] M]
    (φ : Module.Dual ℂ_[p] M) {κ : Type*} [Fintype κ] (n : κ → ℤ) (x : κ → M)
    (hx : ∀ k, ‖φ (x k)‖ ≤ 1) : ‖φ (∑ k, n k • x k)‖ ≤ 1 := by

  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul, norm_mul]
  calc ‖(n k : ℂ_[p])‖ * ‖φ (x k)‖ ≤ 1 * 1 :=
        mul_le_mul (IsUltrametricDist.norm_intCast_le_one _ _) (hx k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem integral_minors_iff_basis : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  intro p _ Lt _ N nu hY ι _ b c d hc hd φ
  classical
  let Ψ : Lt → MvPolynomial (Fin N × Fin N) ℚ →+* MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] := fun s =>
    (MvPolynomial.map (algebraMap ℚ ℂ_[p])).comp (MvPolynomial.rename (sig N s)).toRingHom
  have hF : ∀ J : WeylLatticeDuality.ColChoice N nu,
      MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
        ∏ s, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s)) := by
    intro J
    have h1 : Int.castRingHom ℂ_[p] = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
    rw [h1, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J, map_prod]
    rfl
  have hG : ∀ κ : (∀ s, ι s), MvPolynomial.map (algebraMap ℚ ℂ_[p])
      (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) = ∏ s, Ψ s (b s (κ s)) := by
    intro κ
    rw [map_prod]
    rfl
  have hc' : ∀ s J, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) = ∑ k, c s J k • Ψ s (b s k) := by
    intro s J

    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  have hd' : ∀ s k, Ψ s (b s k) = ∑ J, d s k J • Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) := by
    intro s k
    conv_lhs => rw [hd]

    rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  constructor
  · intro h κ
    rw [hG, prod_zsum_expand (fun s k => Ψ s (b s k)) _ d hd' κ]
    refine norm_dual_zsum_le_one p φ _ _ fun J => ?_
    exact (le_of_eq (congrArg (fun x => ‖φ x‖) (hF J)).symm).trans (h J)
  · intro h J
    rw [hF, prod_zsum_expand (fun s J => Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) _ c hc' J]
    refine norm_dual_zsum_le_one p φ _ _ fun κ => ?_
    have := h κ
    rw [hG] at this
    exact this

end GlobalTheory.WeylLatDualProof
end
end

section

open MvPolynomial

noncomputable section
namespace GlobalTheory.WeylLatDualProof

theorem minY_colsOf_eq (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y : T → Matrix (Fin N) (Fin N) ℂ_[p])
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    PI.WwCauchyBinet.minY N nu J (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
        (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s))) := by
  unfold PI.WwCauchyBinet.minY GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (GlobalTheory.WeylMinorDual.colLen_le (hY s) c)
  simp [WeylLatticeDuality.colsOf, hj, Fin.castLE]

theorem map_nablaX_expand (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ)
    (hb : ∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k)
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∑ κ : (∀ s, ι s), (∏ s, ((c s (J s) (κ s) : ℤ) : ℂ_[p])) •
        MvPolynomial.map (algebraMap ℚ ℂ_[p]) (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) := by
  have h0 : (Int.castRingHom ℂ_[p]) = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
  rw [h0, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J]

  simp_rw [hb, map_sum, map_smul]

  rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.map_C]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp

theorem phi_DeX_expand : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  intro p _ Lt T _ _ _ e N nu hY ι _ b g c hb hg φ y
  have h1 := cauchy_binet_minors Lt ℂ_[p] N nu (fun s => WeylLatticeDuality.colsOf (y (e s)))
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : WeylLatticeDuality.DeX N nu (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, IncreasingRowChoicePerColumn N (nu s)), MvPolynomial.C (PI.WwCauchyBinet.minY N nu J
        (fun s => WeylLatticeDuality.colsOf (y (e s)))) *
        MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) := by
    convert h1 using 2
    all_goals try rfl
  have hG : ∀ s k, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) = ∑ J, ((c s J k : ℤ) : ℂ_[p]) *
        MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
          (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) := by
    intro s k
    rw [hg]

    simp [map_sum, smul_eq_C_mul]

  rw [h2, map_sum]

  simp_rw [MvPolynomial.C_mul', map_smul, map_nablaX_expand p N nu hY ι b c hb, minY_colsOf_eq p e N nu hY y,
  map_sum, map_smul, smul_eq_mul, hG, Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.WeylLatDualProof
end
end
