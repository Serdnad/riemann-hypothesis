module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

section

open scoped TensorProduct BigOperators

namespace GlobalTheory.MultilinearContraction

section

variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

omit [Fintype ι] dι in
private theorem apply_update (φ : ∀ i, X i →ₗ[R] R) [inst : DecidableEq ι] (x : ∀ i, X i) (k : ι)
    (y : X k) (i : ι) :
    φ i (Function.update x k y i) = Function.update (fun i => φ i (x i)) k (φ k y) i := by
  by_cases h : i = k
  · subst h
    simp
  · simp [Function.update_of_ne h]

def contractMultilinear (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (Π i, X i) →ₘₗ[R] X j where
  toFun x := (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j
  map_update_add' := by
    intro inst x k y z
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁,
        Function.update_self, smul_add]
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_add (f := _),
        add_mul, add_smul]
  map_update_smul' := by
    intro inst x k c y
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁, Function.update_self, RingHom.id_apply]
      exact smul_comm _ _ _
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_smul,
        RingHom.id_apply, smul_eq_mul, mul_assoc, mul_smul]

@[simp] theorem contractMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contractMultilinear φ j x = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := rfl

noncomputable def contract (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (⨂[R] i, X i) →ₗ[R] X j :=
  PiTensorProduct.lift (contractMultilinear φ j)

theorem contract_def (φ : ∀ i, X i →ₗ[R] R) (j : ι) :
    contract φ j = PiTensorProduct.lift (contractMultilinear φ j) := rfl

@[simp] theorem contract_tprod (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contract φ j (⨂ₜ[R] i, x i) = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := by
  rw [contract_def, PiTensorProduct.lift.tprod, contractMultilinear_apply]

end

section

variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

def prodMultilinear (φ : ∀ i, X i →ₗ[R] R) : (Π i, X i) →ₘₗ[R] R :=
  (MultilinearMap.mkPiAlgebra R ι R).compLinearMap φ

@[simp] theorem prodMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodMultilinear φ x = ∏ i, φ i (x i) := rfl

noncomputable def prodForm (φ : ∀ i, X i →ₗ[R] R) : (⨂[R] i, X i) →ₗ[R] R :=
  PiTensorProduct.lift (prodMultilinear φ)

theorem prodForm_def (φ : ∀ i, X i →ₗ[R] R) :
    prodForm φ = PiTensorProduct.lift (prodMultilinear φ) := rfl

@[simp] theorem prodForm_tprod (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodForm φ (⨂ₜ[R] i, x i) = ∏ i, φ i (x i) := by
  rw [prodForm_def, PiTensorProduct.lift.tprod, prodMultilinear_apply]

end

end GlobalTheory.MultilinearContraction
end

section

universe u_1 u_2

namespace GlobalTheory.LengthDualFunctional

open Module

theorem exists_dual_ne_zero_comp_eq_zero {R : Type u_1} [CommRing R] [IsDomain R]
    {M : Type u_2} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (h : LinearMap.det f = 0) :
    ∃ φ : Module.Dual R M, φ ≠ 0 ∧ φ ∘ₗ f = 0 := by
  have hd : LinearMap.det f.dualMap = 0 := by
    rw [LinearMap.det_dualMap]; exact h
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.bot_lt_ker_of_det_eq_zero hd).ne'
  exact ⟨φ, hφ0, by simpa [LinearMap.dualMap_apply'] using hφ⟩

theorem length_self_eq_top (R : Type u_1) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Module.length R R = ⊤ := by
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨_, hA⟩ := hne
  haveI : IsArtinianRing R := hA
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem main : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] {M : Type u_2} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [Module.Free R M] [Module.Finite R M] {f : M →ₗ[R] M}, (LinearMap.det : (M →ₗ[R] M) → R) f = (0 : R) → Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  intro R _ _ _ M _ _ _ _ f h
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_ne_zero_comp_eq_zero h
  obtain ⟨m, hm⟩ : ∃ m, φ m ≠ 0 := by
    by_contra hc; push_neg at hc; exact hφ0 (LinearMap.ext hc)
  have hle : LinearMap.range f ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    simpa using congrArg (fun g => g x) hφ
  let ψ := (LinearMap.range f).liftQ φ hle
  let g : R →ₗ[R] M ⧸ LinearMap.range f := LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk m)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have := congrArg ψ hr
    simp [g, ψ] at this
    tauto
  have := Module.length_le_of_injective g hg
  rw [length_self_eq_top] at this
  exact top_le_iff.mp this

end GlobalTheory.LengthDualFunctional
end

section

namespace GlobalTheory.RelativeLengthSpanDet

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
theorem addVal_prod (s : Finset ι) (c : ι → R) :
    addVal R (∏ i ∈ s, c i) = ∑ i ∈ s, addVal R (c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  have : IsArtinianRing R := h.2
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem length_coker_of_det_eq_zero (P : Matrix ι ι R) (h : P.det = 0) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = ⊤ := by
  obtain ⟨w, hw, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
  have hk' : w k ≠ 0 := hk
  let g : R →ₗ[R] (ι → R) ⧸ LinearMap.range P.mulVecLin :=
    (LinearMap.range P.mulVecLin).mkQ ∘ₗ LinearMap.single R (fun _ : ι => R) k
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    have hr' : (Pi.single k r : ι → R) ∈ LinearMap.range P.mulVecLin :=
      (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨x, hx⟩ := hr'
    have h1 : w ⬝ᵥ P.mulVec x = 0 := by
      rw [Matrix.dotProduct_mulVec, hwP, zero_dotProduct]
    rw [Matrix.mulVecLin_apply] at hx
    rw [hx, dotProduct_single] at h1
    exact (mul_eq_zero.mp h1).resolve_left hk'
  exact top_le_iff.mp (length_self_eq_top (R := R) ▸ Module.length_le_of_injective g hg)

theorem length_coker_of_injective {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  set c := Submodule.smithNormalFormCoeffs b hr with hc
  set bt := Submodule.smithNormalFormTopBasis b hr with hbt
  set bb := Submodule.smithNormalFormBotBasis b hr with hbb
  have hdef : ∀ i, (bb i : M) = c i • bt i := Submodule.smithNormalFormBotBasis_def b hr
  have h1 : Module.length R (M ⧸ LinearMap.range f) = ∑ i, addVal R (c i) := by
    rw [(Submodule.quotientEquivPiSpan _ b hr).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (c i)
  have h2 := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (bt.equiv bb (Equiv.refl ι))
  have h3 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf : M →ₗ[R] _) = f := by
    ext x
    rfl
  have h4 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (bt.equiv bb (Equiv.refl ι) : M →ₗ[R] LinearMap.range f)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix bt, ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply, hdef, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [h3, h4] at h2
  rw [h1, (addVal_eq_iff_associated _ _).mpr h2, addVal_prod]

theorem length_coker (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det := by
  by_cases h : P.det = 0
  · rw [length_coker_of_det_eq_zero P h, h, addVal_zero]
  · have hinj : Function.Injective P.mulVecLin := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hx⟩)
    rw [length_coker_of_injective (Pi.basisFun R ι) _ hinj, ← Matrix.toLin'_apply',
      LinearMap.det_toLin']

end GlobalTheory.RelativeLengthSpanDet
end

section

universe u_1 u_2

namespace GlobalTheory.LengthQuotientValuationDet

open Module IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

theorem length_quotient_span_singleton {x : R} (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) = addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, length_quotient_pow_maximalIdeal, addVal_def' u hϖ]

theorem length_quotient_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) =
      (addVal R : R → ℕ∞) (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hassoc : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv _ _ _
  rw [(addVal_eq_iff_associated _ _).mpr hassoc]
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [hdet, addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ =>
    length_quotient_span_singleton (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end GlobalTheory.LengthQuotientValuationDet
end

section

open Module Function
open scoped TensorProduct Pointwise

namespace GlobalTheory

namespace Avoid

section Union

end Union

section Pick


open Module Function in
open scoped TensorProduct Pointwise in
theorem _root_.GlobalTheory.Avoid.exists_basis_map_one_tmul_of_surjective {K L V W ι : Type*} [CommRing K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    [Module.Finite L W] {d : ℕ} (hd : finrank L W = d) (G : L ⊗[K] V →ₗ[L] W)
    (hG : Surjective G) (v : ι → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ (σ : Fin d → ι) (b : Basis (Fin d) L W), Injective σ ∧ ∀ k, b k = G (1 ⊗ₜ v (σ k)) := by
  classical
  have hspanT : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul l y =>
      have hy : y ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
      have h1 : TensorProduct.mk K L V 1 y ∈
          Submodule.span K (TensorProduct.mk K L V 1 '' Set.range v) :=
        Submodule.apply_mem_span_image_of_mem_span _ hy
      have h2 := Submodule.span_le_restrictScalars K L _ h1
      rw [← Set.range_comp] at h2
      have h3 : l ⊗ₜ[K] y = l • ((1 : L) ⊗ₜ[K] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h3]
      exact Submodule.smul_mem _ l h2
    | add a b ha hb => exact add_mem ha hb
  have hw : Submodule.span L (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) = ⊤ := by
    have h : (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) =
        G '' Set.range fun i => (1 : L) ⊗ₜ[K] v i := by
      rw [← Set.range_comp]; rfl
    rw [h, Submodule.span_image, hspanT, Submodule.map_top, LinearMap.range_eq_top.mpr hG]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' L fun i => G ((1 : L) ⊗ₜ[K] v i)
  let b := Basis.mk hli (hspan.trans hw).ge
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := by rw [← hd, Module.finrank_eq_card_basis b]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, b.reindex e.symm, ha.comp e.injective, fun k => ?_⟩
  simp [b, Basis.mk_apply]

end Pick

section Minor

open exteriorPower


open Module Function in
open scoped TensorProduct Pointwise in
open exteriorPower in
theorem _root_.GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : Submodule.span K (Set.range c) = ⊤) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Fin r ↪o ι, pairingDual K V r (ιMulti K r fun k => c (J k)) x ≠ 0 := by
  classical
  by_contra hne
  push_neg at hne
  have hall : ∀ φ : ⋀[K]^r (Dual K V), pairingDual K V r φ x = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span K (Set.range (ιMulti_family K r c)) := by
      rw [ιMulti_family_span_of_span K hc]; exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      exact hne (Set.powersetCard.ofFinEmbEquiv.symm s)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul t y _ hy => simp [hy]
  let b := Basis.ofVectorSpace K V
  letI : LinearOrder (Basis.ofVectorSpaceIndex K V) := IsWellOrder.linearOrder WellOrderingRel
  let B := b.exteriorPower r
  have hcoord : ∀ s, B.coord s = ιMultiDual K r b s := fun s => B.ext fun t => by
    have hBt : B t = ιMulti_family K r b t := by simp [B, Module.Basis.exteriorPower]
    rw [Basis.coord_apply, B.repr_self, hBt]
    by_cases hst : s = t
    · subst hst
      rw [ιMultiDual_apply_diag, Finsupp.single_eq_same]
    · rw [ιMultiDual_apply_nondiag K r b s t hst, Finsupp.single_eq_of_ne hst]
  apply hx
  refine B.ext_elem fun s => ?_
  rw [map_zero, Finsupp.zero_apply, ← B.coord_apply, hcoord]
  exact hall _

end Minor

end Avoid

universe u v w x y

end GlobalTheory
end

section

namespace GlobalTheory.LocalSaturationContraction

variable {B : Type*} [CommRing B]

def satAt (b : B) (P : Ideal B) [hP : P.IsPrime] : Ideal B where
  carrier := {x | ∃ s, s ∉ P ∧ s * x ∈ Ideal.span {b}}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one P).1 hP.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy)
  smul_mem' := by
    rintro c x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    have : s * (c • x) = c * (s * x) := by rw [smul_eq_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hx

variable (b : B) (P : Ideal B) [P.IsPrime]

end GlobalTheory.LocalSaturationContraction
end
