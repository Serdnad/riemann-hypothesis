module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle001
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle013
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.PID
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsEulerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle004
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

section

namespace GlobalTheory

open Finset

theorem exists_finite_reproducing_of_submodule {X : Type} (V : Submodule ℂ (X → ℂ))
    (F : Finset ↥V) :
    ∃ (S : Finset X) (u : X → ↥V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  first
  | exact @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | (apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation ..)

theorem finsupp_sum_multilinear_eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : ι → Type} (V : ∀ k, Submodule ℂ (X k → ℂ)) {R : Type} [AddCommGroup R] [Module ℂ R]
    (M : (∀ k, ↥(V k)) →ₘₗ[ℂ] R) {A : Type} (τ τ' : A →₀ ℂ)
    (φ φ' : A → ∀ k, ↥(V k))
    (h : ∀ z : ∀ k, X k, (τ.sum fun a c => c * ∏ k, (φ a k : X k → ℂ) (z k)) =
      τ'.sum fun a c => c * ∏ k, (φ' a k : X k → ℂ) (z k)) :
    (τ.sum fun a c => c • M (φ a)) = τ'.sum fun a c => c • M (φ' a) := by
  classical
  let T : Finset A := τ.support ∪ τ'.support
  let F : ∀ k, Finset ↥(V k) := fun k => T.image (fun a => φ a k) ∪ T.image (fun a => φ' a k)
  choose S u hSu using fun k => exists_finite_reproducing_of_submodule (V k) (F k)
  have key : ∀ w : ∀ k, ↥(V k), (∀ k, w k ∈ F k) →
      M w = ∑ z ∈ Fintype.piFinset S, (∏ k, (w k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro w hw
    have hw' : w = fun k => ∑ x ∈ S k, (w k : X k → ℂ) x • u k x :=
      funext fun k => hSu k (w k) (hw k)
    conv_lhs => rw [hw']
    rw [MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  have expand : ∀ (σ : A →₀ ℂ) (ψ : A → ∀ k, ↥(V k)), σ.support ⊆ T →
      (∀ a ∈ T, ∀ k, ψ a k ∈ F k) →
      (σ.sum fun a c => c • M (ψ a)) = ∑ z ∈ Fintype.piFinset S,
        (σ.sum fun a c => c * ∏ k, (ψ a k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro σ ψ hσ hψ
    unfold Finsupp.sum
    rw [Finset.sum_congr rfl fun a ha => congrArg (σ a • ·) (key (ψ a) (hψ a (hσ ha)))]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [expand τ φ Finset.subset_union_left
      (fun a ha k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    expand τ' φ' Finset.subset_union_right
      (fun a ha k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  exact Finset.sum_congr rfl fun z _ => by rw [h z]

end GlobalTheory
end

section

open scoped Matrix

noncomputable section

namespace GlobalTheory.SymplecticOneParam

variable {l : Type} [Fintype l] [DecidableEq l]

theorem eq_exp_of_continuous_oneParameter (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) (hc : Continuous g)
    (h0 : g 0 = 1) (hadd : ∀ s t, g (s + t) = g s * g t) :
    HasDerivAt g (deriv g 0) 0 ∧ ∀ t : ℝ, g t = NormedSpace.exp (t • deriv g 0) := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
  have hsm := GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (l ⊕ l) (l ⊕ l) ℝ) g hc h0 hadd
  have hdiff : Differentiable ℝ g := hsm.differentiable (by simp)
  set Z := deriv g 0 with hZ
  have hd0 : HasDerivAt g Z 0 := (hdiff 0).hasDerivAt
  have hdt : ∀ t, HasDerivAt g (g t * Z) t := by
    intro t
    have h1 : HasDerivAt (fun s => g (s - t)) Z t := by
      have h := hd0
      rw [← sub_self t] at h
      exact h.comp_sub_const t t
    have h2 := h1.const_mul (g t)
    have h3 : (fun s => g t * g (s - t)) = g := by
      funext s; rw [← hadd, add_sub_cancel]
    rwa [h3] at h2
  refine ⟨hd0, fun t => ?_⟩
  set h : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun s => g s * NormedSpace.exp (s • (-Z)) with hh
  have hderh : ∀ s, HasDerivAt h 0 s := by
    intro s
    have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Z) s
    have := (hdt s).fun_mul he
    have key : g s * Z * NormedSpace.exp (s • -Z) + g s * (-Z * NormedSpace.exp (s • -Z)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact this.congr_deriv key
  have hconst : h t = h 0 := is_const_of_deriv_eq_zero (fun s => (hderh s).differentiableAt)
    (fun s => (hderh s).deriv) t 0
  have hh0 : h 0 = 1 := by simp [hh, h0]
  have hinv : NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  calc g t = g t * (NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z)) := by rw [hinv, mul_one]
    _ = h t * NormedSpace.exp (t • Z) := by rw [hh, mul_assoc]
    _ = NormedSpace.exp (t • Z) := by rw [hconst, hh0, one_mul]

theorem exists_mem_sp_eq_exp : ∀ (l : Type) [Fintype l] [DecidableEq l] (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ),
    Continuous g → g 0 = 1 →
    (∀ s t, g (s + t) = g s * g t) → (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ t : ℝ, g t = NormedSpace.exp (t • Z) := by
  intro l _ _ g hc h0 hadd hsym
  obtain ⟨hd, hexp⟩ := eq_exp_of_continuous_oneParameter g hc h0 hadd
  refine ⟨deriv g 0, ?_, hexp⟩
  set Z := deriv g 0 with hZ
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  let T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap
  have hT : HasDerivAt (fun t => (g t)ᵀ) Zᵀ 0 := T.hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const (Matrix.J l ℝ)).fun_mul hd
  have hconst : (fun t => (g t)ᵀ * Matrix.J l ℝ * g t) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.transpose_mem (hsym t)
    rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at this
    exact this
  rw [hconst] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) (Matrix.J l ℝ))
  rw [h0, Matrix.transpose_one, mul_one, one_mul, add_eq_zero_iff_eq_neg] at huniq
  show Z ∈ skewAdjointMatricesLieSubalgebra (Matrix.J l ℝ)
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
    Matrix.IsAdjointPair, huniq, mul_neg]

end GlobalTheory.SymplecticOneParam
end
end

section

open Polynomial

namespace GlobalTheory.SymmetricSimilarTranspose

theorem exists_bilin_cyclic {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
        ∀ x y, B x y = B y x := by
  obtain ⟨l, h1, h2⟩ := GlobalTheory.SimilarTranspose.exists_form f hf
  let l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k :=
    (((Ideal.span {f}).restrictScalars k).liftQ l
      (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp
      (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap
  refine ⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l ((X * a) * b) = l (a * (X * b))
    congr 1; ring
  · intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h2 b fun a => ?_))
    have := hy (Ideal.Quotient.mk (Ideal.span {f}) a)
    rw [mul_comm]
    exact this
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l (a * b) = l (b * a)
    rw [mul_comm]

theorem exists_bilin {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : W →ₗ[k] W) :
    ∃ B : W →ₗ[k] W →ₗ[k] k, (∀ x y, B (T x) y = B x (T y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ x y, B x y = B y x := by
  classical
  have htor : Module.IsTorsion k[X] (Module.AEval' T) :=
    Module.AEval.isTorsion_of_finiteDimensional k W T
  obtain ⟨ι, _, p, hp, n, ⟨e⟩⟩ := Module.equiv_directSum_of_isTorsion htor
  choose B hB1 hB2 hB3 using
    fun i => exists_bilin_cyclic (p i ^ n i) (pow_ne_zero _ (hp i).ne_zero)
  let π : ∀ i, W →ₗ[k] (k[X] ⧸ Submodule.span k[X] {p i ^ n i}) := fun i =>
    (((DirectSum.component k[X] ι _ i).comp e.toLinearMap).restrictScalars k).comp
      (Module.AEval'.of T).toLinearMap
  have hπ : ∀ i x, π i x = e (Module.AEval'.of T x) i := fun i x => rfl
  have hT : ∀ i x, π i (T x) = (X : k[X]) • π i x := by
    intro i x
    rw [hπ, hπ, ← Module.AEval'.X_smul_of, map_smul]
    rfl
  refine ⟨∑ i, (B i).compl₁₂ (π i) (π i), ?_, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, hT, hB1]
  · intro y hy
    have h0 : e (Module.AEval'.of T y) = 0 := by
      ext i
      rw [← hπ, DirectSum.zero_apply]
      refine hB2 i _ fun z => ?_
      have := hy ((Module.AEval'.of T).symm (e.symm (DirectSum.lof k[X] ι _ i z)))
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply] at this
      rw [Finset.sum_eq_single i] at this
      · rw [hπ i ((Module.AEval'.of T).symm _)] at this
        simpa using this
      · intro j _ hj
        rw [hπ j ((Module.AEval'.of T).symm _)]
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      · simp
    simpa using h0
  · intro x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]
    exact Finset.sum_congr rfl fun i _ => hB3 i _ _

theorem main : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P.transpose = P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  obtain ⟨B, h1, h2, h3⟩ := exists_bilin (Matrix.toLin' A)
  obtain ⟨P, rfl⟩ := (Matrix.toBilin' (R₁ := k) (n := ι)).surjective B
  simp only [Matrix.toBilin'_apply', Matrix.toLin'_apply] at h1 h2 h3
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    refine (injective_iff_map_eq_zero P.mulVecLin).mpr fun y hy => h2 y fun x => ?_
    rw [Matrix.mulVecLin_apply] at hy
    rw [hy, dotProduct_zero]
  · ext i j
    have := h3 (Pi.single j 1) (Pi.single i 1)
    simpa using this
  · apply (Matrix.toBilin' (R₁ := k) (n := ι)).injective
    refine LinearMap.ext₂ fun x y => ?_
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, ← h1,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

end GlobalTheory.SymmetricSimilarTranspose
end

section

open scoped InnerProductSpace

namespace GlobalTheory

open Filter Topology

theorem hasSum_pi_prod_of_summable_norm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  intro ι _ _ J f hf
  classical
  have hnorm : Summable fun j : ∀ i, J i => ‖∏ i, f i (j i)‖ := by
    have := splitHeight_summable_pi_prod (α := J) (f := fun i x => ‖f i x‖)
      (fun i x => norm_nonneg (f i x)) hf
    refine this.congr fun j => ?_
    exact (norm_prod _ _).symm
  have hs : Summable fun j : ∀ i, J i => ∏ i, f i (j i) := hnorm.of_norm
  have hcof : Tendsto (fun S : ∀ i, Finset (J i) => Fintype.piFinset S) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun t => ⟨fun i => t.image (· i), fun S hS => ?_⟩
    intro x hx
    exact Fintype.mem_piFinset.2 fun i => hS i (Finset.mem_image_of_mem _ hx)
  have h1 : Tendsto (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i))
      atTop (𝓝 (∑' j : ∀ i, J i, ∏ i, f i (j i))) := hs.hasSum.comp hcof
  have hproj : ∀ i, Tendsto (fun S : ∀ i, Finset (J i) => S i) atTop atTop := by
    intro i
    refine Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨Function.update (fun j => (∅ : Finset (J j))) i b, fun S hS => ?_⟩
    have := hS i
    simpa using this
  have h2 : Tendsto (fun S : ∀ i, Finset (J i) => ∏ i, ∑ x ∈ S i, f i x)
      atTop (𝓝 (∏ i, ∑' j, f i j)) :=
    tendsto_finsetProd _ fun i _ => ((hf i).of_norm.hasSum).comp (hproj i)
  have h3 : (fun S : ∀ i, Finset (J i) => ∑ x ∈ Fintype.piFinset S, ∏ i, f i (x i)) =
      fun S => ∏ i, ∑ x ∈ S i, f i x := by
    funext S; exact (Finset.prod_univ_sum S fun i x => f i x).symm
  rw [h3] at h1
  have := tendsto_nhds_unique h1 h2
  rw [← this]; exact hs.hasSum

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  first | exact @GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | exact GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | (intros; apply GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul <;> assumption)
end

section

open Finset

theorem _root_.GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  first | exact @GlobalTheory.hasSum_eq_sum_of_matching_family | exact GlobalTheory.hasSum_eq_sum_of_matching_family | (intros; apply GlobalTheory.hasSum_eq_sum_of_matching_family <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ, HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  first | exact @GlobalTheory.hasSum_quotient_transport | exact GlobalTheory.hasSum_quotient_transport | (intros; apply GlobalTheory.hasSum_quotient_transport <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hasSum_cosets_eulerProduct_alt : ∀ {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)] (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G), J ≤ H → (∀ v a, p v (e v a) = a) → (∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) → (∀ v a, e v a ∈ H) → (∀ v a g, p v g = 1 → Commute (e v a) g) → (∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) → (∀ g ∈ H, {v | p v g ∉ K v}.Finite) → ∀ (Ψ : G → ℂ) (Φ : G → ℝ) (Z : ι → ℂ) (A : ι → ℝ) (z : ℂ), (∀ g ∈ H, ∀ k ∈ J, Ψ (g * k) = Ψ g) → (∀ g ∈ H, ∀ k ∈ J, Φ (g * k) = Φ g) → (∀ g ∈ H, ‖Ψ g‖ ≤ Φ g) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Ψ (g * e v a.out)) (Z v * Ψ g)) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Φ (g * e v a.out)) (A v * Φ g)) → Summable (fun v => A v - 1) → HasProd Z z → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) (z * Ψ 1) := by
  first | exact @GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | exact GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | (intros; apply GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect : ∀ (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)), Continuous c → c 0 ≠ 0 → IsOpen U → (∀ s, (s, 0) ∈ U) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U → (∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  first | exact @GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | exact GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | (intros; apply GlobalTheory.FuncEqSmooth.contDiff_of_func_eq <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) →
    (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  first | exact @GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | exact GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | (intros; apply GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero <;> assumption)
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 := by
  first | exact @GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | exact GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | (intros; apply GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' : ∀ ν : ℝ → ℂ, ν 0 = 1 → (∀ s t, ν (s + t) = ν s * ν t) → ContinuousAt ν 0 → ∃ a : ℂ, HasDerivAt ν a 0 := by
  first | exact @GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul | exact GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul | (intros; apply GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul <;> assumption)
end
