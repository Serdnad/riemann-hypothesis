module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle035
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle031
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemOfCharpolyCoeffMem
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CharpolyIso

open Module Polynomial GlobalTheory.TraceIso

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cp (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Module A V] [IsScalarTower k A V] (a : A) : k[X] :=
  LinearMap.charpoly (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [FiniteDimensional k V] [FiniteDimensional k W]

theorem cp_congr (e : V ≃ₗ[A] W) (a : A) : cp k V a = cp k W a := by
  unfold cp
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k) (Algebra.lsmul k k V a)]
  congr 1
  ext w
  simp [LinearEquiv.conj_apply]

theorem cp_prod (a : A) : cp k (V × W) a = cp k V a * cp k W a := by
  unfold cp
  rw [← LinearMap.charpoly_prodMap]
  congr 1

theorem charpoly_one_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (1 : V →ₗ[k] V) = (X - 1 : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), LinearMap.toMatrix_one,
    Matrix.charpoly_one]
  simp

theorem charpoly_zero_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (0 : V →ₗ[k] V) = (X : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), map_zero, Matrix.charpoly_zero]
  simp

theorem finrank_eq_zero_of_hom
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, cp k V a = cp k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add (f := _)]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have key := h r
  unfold cp at key
  rw [hV, hW, charpoly_one_eq, charpoly_zero_eq] at key
  have hdeg : finrank k V = finrank k W := by
    have := congrArg natDegree key
    have h1 : (X - 1 : k[X]).natDegree = 1 := by
      simpa using natDegree_X_sub_C (1 : k)
    simpa [natDegree_pow, h1] using this
  have h0 := congrArg (Polynomial.eval 0) key
  simp only [eval_pow, eval_sub, eval_X, eval_one, zero_sub] at h0
  by_contra hne
  have hW0 : finrank k W ≠ 0 := hdeg ▸ hne
  rw [zero_pow hW0] at h0
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h0

end

theorem nonempty_linear_equiv_of_charpoly_eq (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [cp_congr e₁, cp_congr e₂, cp_prod, cp_prod] at this
      have hS : cp k S a ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
      exact mul_right_cancel₀ hS this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf

theorem cp_asModule {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Γ V) (a : MonoidAlgebra k Γ) :
    haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
    cp k ρ.asModule a = LinearMap.charpoly (ρ.asAlgebraHom a) := by
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  unfold cp
  rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv.symm (ρ.asAlgebraHom a)]
  congr 1

theorem exists_equiv_of_charpoly_eq {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ a : MonoidAlgebra k Γ,
      LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  haveI : FiniteDimensional k σ.asModule := σ.asModuleEquiv.symm.finiteDimensional
  have key : ∀ a : MonoidAlgebra k Γ, cp k ρ.asModule a = cp k σ.asModule a := fun a => by
    rw [cp_asModule, cp_asModule, h]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

theorem exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V)
    (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
    (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) =
      LinearMap.charpoly (σ.asAlgebraHom a)) →
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) :=
  fun ρ σ hρ hσ h => exists_equiv_of_charpoly_eq ρ σ hρ hσ h

end GlobalTheory.CharpolyIso

end
end

section

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.DetAdResultant
theorem det_aeval_eq_resultant_of_splits {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (g : K[X]) (hg : g.Monic) (hs : g.Splits) :
    (aeval A g).det = resultant A.charpoly g := by
  rw [resultant_comm, resultant_eq_prod_eval g A.charpoly _ le_rfl hs, hg.leadingCoeff, one_pow, one_mul]
  let φ : K[X] →* K := Matrix.detMonoidHom.comp (aeval A).toMonoidHom
  have hφ : ∀ p, φ p = (aeval A p).det := fun p => rfl
  have h1 : ∀ x : K, φ (X - C x) = (-1) ^ Fintype.card ι * eval x A.charpoly := by
    intro x
    rw [hφ]
    simp only [map_sub, aeval_X, aeval_C, Matrix.eval_charpoly]
    rw [← Matrix.det_neg, neg_sub]
    rfl
  rw [← hφ]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hg]
  rw [map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, h1]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← pow_mul,
    Matrix.charpoly_natDegree_eq_dim, ← hs.natDegree_eq_card_roots]

theorem det_aeval_eq_resultant {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι E) (g : E[X]) (hg : g.Monic) :
    (aeval A g).det = resultant A.charpoly g := by
  let K := AlgebraicClosure E
  apply (algebraMap E K).injective
  have h := det_aeval_eq_resultant_of_splits (A.map (algebraMap E K)) (g.map (algebraMap E K))
    (hg.map _) (IsAlgClosed.splits _)
  rw [Matrix.charpoly_map, natDegree_map, natDegree_map, resultant_map_map] at h
  rw [← h, RingHom.map_det]
  congr 1
  have e : (algebraMap E K).mapMatrix (aeval A g) = (Algebra.ofId E K).mapMatrix (aeval A g) := rfl
  rw [e, ← aeval_algHom_apply, aeval_map_algebraMap]
  rfl
theorem det_det_charmatrix {E : Type} [Field E] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ E) (B : Matrix ι₂ ι₂ E) :
    ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix B.transpose).map (aeval A).toRingHom)).det =
      resultant A.charpoly B.charpoly := by
  rw [← Matrix.det_det, ← Matrix.charpoly, Matrix.charpoly_transpose]
  exact det_aeval_eq_resultant A B.charpoly (Matrix.charpoly_monic B)

theorem toMatrix_ad {E : Type} [Field E] {V₁ V₂ : Type} [AddCommGroup V₁] [Module E V₁]
    [AddCommGroup V₂] [Module E V₂] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (b₁ : Module.Basis ι₁ E V₁) (b₂ : Module.Basis ι₂ E V₂)
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂) :
    LinearMap.toMatrix (b₂.linearMap b₁) (b₂.linearMap b₁)
        (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      Matrix.reindex (Equiv.prodComm ι₂ ι₁) (Equiv.prodComm ι₂ ι₁)
        ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix (LinearMap.toMatrix b₂ b₂ f₂).transpose).map
          (aeval (LinearMap.toMatrix b₁ b₁ f₁)).toRingHom)) := by
  ext ⟨a, j⟩ ⟨b, k⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.linearMap_repr_apply]
  have hr : ∀ M : Matrix ι₁ ι₂ E, (Matrix.stdBasis E ι₁ ι₂).repr M (a, j) = M a j := fun M => rfl
  have hψ : LinearMap.toMatrix b₂ b₁ (b₂.linearMap b₁ (b, k)) = Matrix.single b k 1 := by
    simp [Module.Basis.linearMap, Matrix.stdBasis_eq_single]
  rw [hr, LinearMap.sub_apply, LinearMap.llcomp_apply', LinearMap.lcomp_apply', map_sub,
    LinearMap.toMatrix_comp b₂ b₁ b₁, LinearMap.toMatrix_comp b₂ b₂ b₁, hψ]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Matrix.comp_apply, Matrix.map_apply, Matrix.charmatrix_apply, Matrix.transpose_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply, hjk, Matrix.diagonal_apply_ne _ hjk]
    by_cases hab : a = b
    · subst hab; simp [Ne.symm hjk]
    · simp [hab, Ne.symm hab, Ne.symm hjk]

theorem det_ad_eq_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁]
    [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂),
    LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      resultant f₁.charpoly f₂.charpoly := by
  intro E _ V₁ V₂ _ _ _ _ _ _ f₁ f₂
  let b₁ := Module.finBasis E V₁
  let b₂ := Module.finBasis E V₂
  rw [← LinearMap.det_toMatrix (b₂.linearMap b₁), toMatrix_ad b₁ b₂, Matrix.det_reindex_self,
    det_det_charmatrix, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

end GlobalTheory.DetAdResultant
end

section

open Polynomial

theorem _root_.GlobalTheory.T.finrank_ker_map_le_of_first_order_kernel_ext : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  first | exact @GlobalTheory.finrank_ker_map_le_of_first_order_kernel | exact GlobalTheory.finrank_ker_map_le_of_first_order_kernel | (intros; apply GlobalTheory.finrank_ker_map_le_of_first_order_kernel <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_alternating_form_left_corank_le_one : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ → ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) → (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x := by
  first | exact @GlobalTheory.AltCorank.exists_alt_corank_le_one | exact GlobalTheory.AltCorank.exists_alt_corank_le_one | (intros; apply GlobalTheory.AltCorank.exists_alt_corank_le_one <;> assumption)
end

section

open TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' : ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | exact GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | (intros; apply GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id <;> assumption)
end

section

open TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  first | exact @GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | exact GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | (intros; apply GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields : ∀ (k : Type) [Field k] [CharZero k], (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) → ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  first | exact @GlobalTheory.units_modSq_finite_of_fields | exact GlobalTheory.units_modSq_finite_of_fields | (intros; apply GlobalTheory.units_modSq_finite_of_fields <;> assumption)
end

section

open TensorProduct Module

theorem _root_.GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  first | exact @GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective | exact GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective | (intros; apply GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective <;> assumption)
end

section

open NumberField IsDedekindDomain TensorProduct

theorem _root_.GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base : ∀ (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E'] [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K), ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  first | exact @GlobalTheory.exists_tensor_idem_of_algHom | exact GlobalTheory.exists_tensor_idem_of_algHom | (intros; apply GlobalTheory.exists_tensor_idem_of_algHom <;> assumption)
end

section


theorem _root_.GlobalTheory.T.free_finite_module_adicComplete_and_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  first | exact @GlobalTheory.freeModule_adicComplete_separated | exact GlobalTheory.freeModule_adicComplete_separated | (intros; apply GlobalTheory.freeModule_adicComplete_separated <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.charpoly_nilpotent_add_scalar' : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  first | exact @GlobalTheory.charpoly_nilpotent_add_scalar | exact GlobalTheory.charpoly_nilpotent_add_scalar | (intros; apply GlobalTheory.charpoly_nilpotent_add_scalar <;> assumption)
end

section

open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in
open Polynomial in
private lemma det_generic_sum_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (g : Fin m → G) :
    (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (ρ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det =
      (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (σ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det := by
  ext d
  let T : Subalgebra k (Bool → k) :=
    AlgHom.equalizer (Pi.evalAlgHom k (fun _ : Bool => k) true) (Pi.evalAlgHom k (fun _ : Bool => k) false)
  have key := _root_.GlobalTheory.coeff_det_generic_sum_mem_of_charpoly_coeff_mem T n
    (fun b => if b then ρ else σ) (by intro g j; simp [T, AlgHom.mem_equalizer, h]) m g d
  simpa [T, AlgHom.mem_equalizer] using key

open scoped BigOperators in
open Polynomial in
private lemma charpoly_sum_smul_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (c : Fin m → k) (g : Fin m → G) :
    (∑ i, c i • ρ (g i)).charpoly = (∑ i, c i • σ (g i)).charpoly := by
  have hd := det_generic_sum_eq_of_charpoly_eq n ρ σ h (m + 1) (Fin.cons 1 g)
  have key : ∀ τ : G →* Matrix (Fin n) (Fin n) k, (∑ i, c i • τ (g i)).charpoly =
      MvPolynomial.aeval (Fin.cons (X : k[X]) (fun i => -C (c i)) : Fin (m + 1) → k[X])
        (∑ i, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) k) •
          (τ ((Fin.cons 1 g : Fin (m + 1) → G) i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin (m + 1)) k)).det := by
    intro τ
    rw [AlgHom.map_det]
    unfold Matrix.charpoly
    congr 1
    ext i j
    simp [Fin.sum_univ_succ, Matrix.charmatrix_apply, Matrix.sum_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  rw [key ρ, key σ, hd]

open scoped BigOperators in
open Polynomial in
theorem _root_.GlobalTheory.charpoly_lift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) →
    ∀ a : MonoidAlgebra k G,
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly =
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  intro k G _ _ n ρ σ h a
  have hsum : ∀ τ : G →* Matrix (Fin n) (Fin n) k,
      MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G τ a =
        ∑ i, a.coeff (a.coeff.support.equivFin.symm i) • τ (a.coeff.support.equivFin.symm i) := by
    intro τ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_coe_sort a.coeff.support]
    exact (Equiv.sum_comp a.coeff.support.equivFin.symm (fun x : a.coeff.support => a.coeff x • τ x)).symm
  rw [hsum ρ, hsum σ]
  exact charpoly_sum_smul_eq_of_charpoly_eq n ρ σ h _ _ _

end GlobalTheory
end
