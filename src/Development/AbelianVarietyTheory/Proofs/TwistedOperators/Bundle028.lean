module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Mathlib.LinearAlgebra.Trace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle007
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle015
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle014
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocks
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.LinearAlgebra.Matrix.Basis

@[expose] public section

section


theorem _root_.GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated : ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  first | exact @GlobalTheory.exists_finiteDimensional_orbit_of_generated | exact GlobalTheory.exists_finiteDimensional_orbit_of_generated | (intros; apply GlobalTheory.exists_finiteDimensional_orbit_of_generated <;> assumption)
end

section


theorem _root_.GlobalTheory.T.trace_sum_single_comp_proj_eq : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  first | exact @GlobalTheory.trace_matrix_pi_operator | exact GlobalTheory.trace_matrix_pi_operator | (intros; apply GlobalTheory.trace_matrix_pi_operator <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X),
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) →
    ∀ ψ : π.IntertwiningMap ρ, LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap →
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  first | exact @GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | exact GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | (intros; apply GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_irreducible_subrep_with_groupAlgebra_fixed : ∀ (G G' W : Type) [Group G] [Finite G] [Fintype G'] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (i : G' → G) (c : G' → ℂ) (x : W), x ≠ 0 → ∑ g, c g • ρ (i g) x = x → ∃ U : Subrepresentation ρ, FiniteDimensional ℂ U.toSubmodule ∧ U.toRepresentation.IsIrreducible ∧ ∃ y : U.toSubmodule, y ≠ 0 ∧ ∑ g, c g • U.toRepresentation (i g) y = y := by
  first | exact @GlobalTheory.FixedVec.exists_irreducible_subrep_fixed | exact GlobalTheory.FixedVec.exists_irreducible_subrep_fixed | (intros; apply GlobalTheory.FixedVec.exists_irreducible_subrep_fixed <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (∀ i, G i) W), ρ.IsIrreducible → ∀ i, ∃ (n : ℕ) (τ : Representation ℂ (G i) (Fin n → ℂ)), τ.IsIrreducible ∧ (∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, Function.Injective φ ∧ ∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ Submodule.span ℂ {y | ∃ φ : (Fin n → ℂ) →ₗ[ℂ] W, (∀ g z, φ (τ g z) = ρ (Pi.mulSingle i g) (φ z)) ∧ y ∈ LinearMap.range φ} = ⊤ := by
  first | exact @GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | exact GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi | (intros; apply GlobalTheory.PiIsotypic.isotypic_factor_of_isIrreducible_pi <;> assumption)
end

section


theorem _root_.GlobalTheory.T.injective_sum_of_linIndep_intertwiners : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  first | exact @GlobalTheory.intertwiners_indep_injective | exact GlobalTheory.intertwiners_indep_injective | (intros; apply GlobalTheory.intertwiners_indep_injective <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic : ∀ (g : ℕ) (Λ' Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd' : Set (Fin g → ℂ)) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (c : Fin g → ℂ) (f : (Fin g → ℂ) → ℝ), Countable Λ' → (∀ z, L z ∈ Λ' ↔ z ∈ Λ₁) → IsAddFundamentalDomain Λ' Fd' volume → (∀ a ∈ Λ', ∀ z, f (z + a) = f z) → (∫ z in Fd', f z) / (volume Fd').toReal = 1 → IsAddFundamentalDomain Λ₁ ((fun z => L z + c) ⁻¹' Fd') volume ∧ (∫ z in (fun z => L z + c) ⁻¹' Fd', f (L z + c)) / (volume ((fun z => L z + c) ⁻¹' Fd')).toReal = 1 := by
  first | exact @GlobalTheory.AffineMean.affine_fundamentalDomain_mean | exact GlobalTheory.AffineMean.affine_fundamentalDomain_mean | (intros; apply GlobalTheory.AffineMean.affine_fundamentalDomain_mean <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le : ∀ (g : ℕ) (Λ Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd D₁ : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℝ), Countable Λ₁ → Λ ≤ Λ₁ → IsAddFundamentalDomain Λ Fd volume → IsAddFundamentalDomain Λ₁ D₁ volume → volume Fd ≠ ⊤ → (∀ a ∈ Λ₁, ∀ z, f (z + a) = f z) → (∫ z in D₁, f z) / (volume D₁).toReal = 1 → IntegrableOn f Fd volume ∧ (∫ z in Fd, f z) / (volume Fd).toReal = 1 := by
  first | exact @GlobalTheory.mean_fundamentalDomain_of_le | exact GlobalTheory.mean_fundamentalDomain_of_le | (intros; apply GlobalTheory.mean_fundamentalDomain_of_le <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | exact GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | (intros; apply GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul <;> assumption)
end

section

open scoped Matrix


theorem _root_.GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' : ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by
  first | exact @GlobalTheory.exists_dual_pair_isUnit_det_blocks | exact GlobalTheory.exists_dual_pair_isUnit_det_blocks | (intros; apply GlobalTheory.exists_dual_pair_isUnit_det_blocks <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem exists_gl_mul_cols_eq_zero_of_rank (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  classical

  let f := x.mulVecLin
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hcard : Fintype.card n = Fintype.card a + Fintype.card b := by
    rw [← Fintype.card_congr e, Fintype.card_sum]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrank : Module.finrank k (LinearMap.range f) = Fintype.card a := (Matrix.finrank_range_mulVecLin x).trans hx
  rw [hrank, Module.finrank_fintype_fun_eq_card, hcard] at hrn
  have hK : Module.finrank k (LinearMap.ker f) = Fintype.card b := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hK, Module.finrank_fintype_fun_eq_card, hcard] at hsum
  have hC : Module.finrank k C = Fintype.card a := by omega
  let bK : Module.Basis b k (LinearMap.ker f) :=
    (Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm
  let bC : Module.Basis a k C := (Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm
  let B : Module.Basis n k (n → k) :=
    ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e
  have hB : ∀ j, f (B (e (Sum.inr j))) = 0 := by
    intro j
    simp [B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  let P := (Pi.basisFun k n).toMatrix B
  have : Invertible P := (Pi.basisFun k n).invertibleToMatrix B
  refine ⟨unitOfInvertible P, fun i j => ?_⟩
  show (x * P) i (e (Sum.inr j)) = 0
  have hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i := by
    simp [P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hcol, hB j]
  rfl

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory


open Matrix Topology Module in
theorem _root_.GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card :
    ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  intro k m a b n _ _ _ _ _ e x hx hz v hv
  classical
  set x' := x.submatrix id (fun i => e (Sum.inl i))
  let Q : Matrix n a k := Matrix.of fun l i => if l = e (Sum.inl i) then 1 else 0
  let P : Matrix a n k := Matrix.of fun i l => if l = e (Sum.inl i) then 1 else 0
  have hQ : x' = x * Q := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [x', Q, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hP : x = x' * P := by
    ext i l
    obtain ⟨t, rfl⟩ := e.surjective l
    rcases t with t | t
    · rw [Matrix.mul_apply]
      simp only [x', P, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    · rw [Matrix.mul_apply]
      simp [x', P, hz]
  have hr : x'.rank = Fintype.card a := by
    apply le_antisymm
    · rw [← hx, hQ]; exact Matrix.rank_mul_le_left _ _
    · rw [← hx, hP]; exact Matrix.rank_mul_le_left _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker x'.mulVecLin
  have hxr : finrank k (LinearMap.range x'.mulVecLin) = Fintype.card a := by simpa only [Matrix.finrank_range_mulVecLin] using hr
  rw [hxr, finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker x'.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  have hvk : v ∈ LinearMap.ker x'.mulVecLin := hv
  rw [hker] at hvk
  exact (Submodule.mem_bot k).1 hvk

end GlobalTheory
end
