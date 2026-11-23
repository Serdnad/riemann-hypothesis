module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

@[expose] public section

section

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.LengthQuotientSpanValuation

open Module

section

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma length_quot_span (x : R) :
    Module.length R (R ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal R x :=
  Ring.ord_eq_addVal x

lemma length_self_eq_top : Module.length R R = ⊤ := by
  rw [← Ring.ord_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]

lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

end

theorem main {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type u_2} [AddCommGroup M] [Module R M] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {M' : Type u_4} [AddCommGroup M'] [Module R M'] (b' : Module.Basis ι R M')
    (b : Module.Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      (IsDiscreteValuationRing.addVal R : R → ℕ∞)
        (Matrix.det ((LinearMap.toMatrix b' b : (M' →ₗ[R] M) → Matrix ι ι R) f)) := by
  set A := LinearMap.toMatrix b' b f with hA
  by_cases hf : Function.Injective f
  · set N := LinearMap.range f with hN
    let e₀ : M' ≃ₗ[R] N := LinearEquiv.ofInjective f hf
    have h : Module.finrank R N = Module.finrank R M := by
      rw [← e₀.finrank_eq, Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]
    let a := Submodule.smithNormalFormCoeffs b h
    let bT := Submodule.smithNormalFormTopBasis b h
    let bB := Submodule.smithNormalFormBotBasis b h
    have ab_eq := Submodule.smithNormalFormBotBasis_def b h

    have hlen : Module.length R (M ⧸ N) = IsDiscreteValuationRing.addVal R (∏ i, a i) := by
      rw [(Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype,
        addVal_prod]
      exact Finset.sum_congr rfl fun i _ => length_quot_span _
    rw [hlen, IsDiscreteValuationRing.addVal_eq_iff_associated]

    let φ : M' ≃ₗ[R] M := b'.equiv b (Equiv.refl ι)
    have hdetA : A.det = LinearMap.det (N.subtype ∘ₗ ((φ.symm.trans e₀ : M ≃ₗ[R] N) : M →ₗ[R] N)) := by
      rw [← LinearMap.det_toMatrix b]
      congr 1
      ext i j
      simp [hA, LinearMap.toMatrix_apply, φ, e₀]
      rfl
    let e' : M ≃ₗ[R] N := bT.equiv bB (Equiv.refl ι)
    have hg : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (bT i) = a i • bT i := by
      intro i
      simp [e', Basis.equiv_apply, bB, bT, a, ab_eq]
    have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix bT, ← Matrix.det_diagonal]
      congr 1
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [hdetA, ← hdiag]
    exact LinearMap.associated_det_comp_equiv _ _ _
  · have hdet : A.det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by
        simpa [Function.Injective] using hf
      refine ⟨b'.repr (x - y), ?_, ?_⟩
      · intro h
        apply hne
        rw [← sub_eq_zero]
        apply b'.repr.injective
        rw [map_zero]
        exact Finsupp.ext fun i => by simpa using congrFun h i
      · rw [hA, LinearMap.toMatrix_mulVec_repr, map_sub, hxy, sub_self, map_zero]
        rfl
    rw [hdet, IsDiscreteValuationRing.addVal_zero]
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    let φ : M →ₗ[R] R := ∑ i, w i • b.coord i
    have hφ : ∀ x, φ x = ∑ i, w i * b.repr x i := by
      intro x
      simp [φ]
    have hle : LinearMap.range f ≤ LinearMap.ker φ := by
      rw [LinearMap.range_le_ker_iff]
      refine b'.ext fun j => ?_
      have := congrFun hw j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [LinearMap.comp_apply, hφ, LinearMap.zero_apply, ← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA, LinearMap.toMatrix_apply]
    let ψ := (LinearMap.range f).liftQ φ hle
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw0 (funext h)
    have hmem : (R ∙ w i) ≤ LinearMap.range ψ := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨Submodule.Quotient.mk (b i), ?_⟩
      simp [ψ, hφ, Finsupp.single_apply]
    have h1 : Module.length R (R ∙ w i) = ⊤ := by
      rw [← (LinearEquiv.toSpanNonzeroSingleton R R (w i) hi).length_eq, length_self_eq_top]
    have h2 : Module.length R (R ∙ w i) ≤ Module.length R (LinearMap.range ψ) :=
      Module.length_le_of_injective (Submodule.inclusion hmem) (Submodule.inclusion_injective hmem)
    have h3 : Module.length R (LinearMap.range ψ) ≤ Module.length R (M ⧸ LinearMap.range f) :=
      Module.length_le_of_surjective ψ.rangeRestrict (LinearMap.surjective_rangeRestrict ψ)
    rw [← top_le_iff, ← h1]
    exact h2.trans h3

end GlobalTheory.LengthQuotientSpanValuation
end

section

open TensorProduct

namespace GlobalTheory.LeftRightDerivations

variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]

def IsCounitDerivation (φ : H →ₗ[k] k) : Prop :=
  ∀ a b : H, φ (a * b) =
    Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a

noncomputable def contrRight (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H φ

@[simp] theorem contrRight_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrRight φ (a ⊗ₜ[k] b) = φ b • a := by
  simp [contrRight]

theorem contrRight_counit_comul (a : H) :
    contrRight (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by

  simp [contrRight, Coalgebra.lTensor_counit_comul]

theorem contrRight_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrRight φ (s * t) =
      contrRight (Coalgebra.counit (R := k)) s * contrRight φ t +
        contrRight (Coalgebra.counit (R := k)) t * contrRight φ s := by

  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrRight_tmul, hφ b d, Algebra.smul_def, map_add (f := _), map_mul]
      ring

theorem contrRight_one (φ : H →ₗ[k] k) : contrRight φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrRight_tmul]

section Ring

variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

theorem IsCounitDerivation.map_one {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) : φ 1 = 0 := by

  have h := hφ 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  simpa using h

noncomputable def derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrRight φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrRight_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrRight_mul hφ,
      contrRight_counit_comul, smul_eq_mul]

end Ring

end GlobalTheory.LeftRightDerivations
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

section Local

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

theorem nonempty_baseChange_subquotient_equiv [Module.Flat R S] {X : Type*} [AddCommGroup X]
    [Module R X] (A B : Submodule R X) :
    Nonempty ((S ⊗[R] (A ⧸ B.submoduleOf A)) ≃ₗ[S]
      (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S))) := by
  let h : S ⊗[R] A →ₗ[S] S ⊗[R] (A ⧸ B.submoduleOf A) := (B.submoduleOf A).mkQ.baseChange S
  let g : S ⊗[R] A →ₗ[S] (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) :=
    ((B.baseChange S).submoduleOf (A.baseChange S)).mkQ ∘ₗ A.toBaseChange S
  have hh : Function.Surjective h :=
    LinearMap.lTensor_surjective S (B.submoduleOf A).mkQ_surjective
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (A.toBaseChange_surjective S)
  have e₁ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.submoduleOf A).mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have e₂ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.mkQ ∘ₗ A.subtype).lTensor S) := by
    apply Module.Flat.lTensor_exact S
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
    rfl
  have e₃ : Function.Exact (B.subtype.lTensor S) (B.mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have hker : LinearMap.ker h = LinearMap.ker g := by
    ext x
    have h1 : x ∈ LinearMap.ker h ↔ (B.submoduleOf A).mkQ.lTensor S x = 0 := Iff.rfl
    have h2 : x ∈ LinearMap.ker g ↔ A.subtype.lTensor S x ∈ B.baseChange S := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rfl
    rw [h1, h2, e₁ x, ← e₂ x, LinearMap.lTensor_comp, LinearMap.comp_apply, e₃]
    rfl
  exact ⟨(h.quotKerEquivOfSurjective hh).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    g.quotKerEquivOfSurjective hg⟩

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_flat :
    Module.length S (S ⊗[R] X) =
      Module.length R X * Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
  IsLocalRing.length_baseChange R S X


variable {X} in
theorem length_baseChange_subquotient_flat (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) *
        Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  rw [← length_baseChange_flat]
  exact (nonempty_baseChange_subquotient_equiv R S A B).some.length_eq.symm

variable {R S}

end Local

section DVR

open IsDiscreteValuationRing hiding maximalIdeal

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

theorem length_quotient_span_singleton_eq_addVal {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (x : S) :
    Module.length S (S ⧸ Ideal.span {x}) = addVal S x := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  rcases eq_or_ne x 0 with rfl | hx
  · rw [addVal_zero, Ideal.span_singleton_zero,
      (Submodule.quotEquivOfEqBot (⊥ : Ideal S) rfl).length_eq]
    by_contra h
    have h' := Module.length_ne_top_iff.mp h
    rw [← isArtinianRing_iff_isFiniteLength] at h'
    exact not_isField S (IsArtinianRing.isField_of_isDomain S)
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
    rw [addVal_def' u hπ, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, length_quotient_pow_maximalIdeal]

variable [IsLocalHom (algebraMap R S)]

theorem map_maximalIdeal_eq_pow_ramificationIdx :
    (maximalIdeal R).map (algebraMap R S) =
      maximalIdeal S ^ ((maximalIdeal S).ramificationIdx R) := by
  have hp : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hpS : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hpS hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hn
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S) hp,
    Ideal.ramificationIdx'_spec (n := n) hn.le, hn]
  rw [hn]
  exact (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field S) n).not_ge

theorem length_fibre_eq_ramificationIdx :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) =
      ((maximalIdeal S).ramificationIdx R : ℕ) := by
  conv_lhs => rw [map_maximalIdeal_eq_pow_ramificationIdx]
  exact length_quotient_pow_maximalIdeal S _

theorem ramificationIdx_maximalIdeal_pos : 0 < (maximalIdeal S).ramificationIdx R := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have := map_maximalIdeal_eq_pow_ramificationIdx R S
  rw [h, pow_zero, Ideal.one_eq_top] at this
  exact (map_maximalIdeal_lt_top (algebraMap R S)).ne this


variable {R} in
theorem addVal_algebraMap_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) :
    addVal S (algebraMap R S ϖ) = ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [← length_fibre_eq_ramificationIdx, ← length_quotient_span_singleton_eq_addVal,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]


variable {R} in
theorem addVal_algebraMap (x : R) :
    addVal S (algebraMap R S x) = addVal R x * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.top_mul]
    exact_mod_cast (ramificationIdx_maximalIdeal_pos R S).ne'
  · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
    rw [addVal_def' u hϖ, map_mul, map_pow, addVal_mul, addVal_pow,
      addVal_algebraMap_uniformizer S hϖ,
      addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap R S)), zero_add, nsmul_eq_mul]

variable (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_dvr :
    Module.length S (S ⊗[R] X) =
      Module.length R X * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_flat, length_fibre_eq_ramificationIdx]


variable {X} in
theorem length_baseChange_subquotient_dvr (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_subquotient_flat, length_fibre_eq_ramificationIdx]

end DVR

section Uniformizer

open IsDiscreteValuationRing hiding maximalIdeal

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

end Uniformizer

end GlobalTheory
end
