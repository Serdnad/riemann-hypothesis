module

public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.GradedAlgebra.Basic

@[expose] public section

section

open TensorProduct

namespace GlobalTheory.ReducedAlg

theorem eq_zero_of_forall_lTensor_eq_zero {k : Type*} [Field k] {C M : Type*} [AddCommGroup C]
    [Module k C] [AddCommGroup M] [Module k M] {ι : Sort*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] (φ : ∀ i, M →ₗ[k] N i)
    (hφ : ∀ m, (∀ i, φ i m = 0) → m = 0) (z : C ⊗[k] M)
    (hz : ∀ i, (φ i).lTensor C z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis k C
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext j
  rw [Finsupp.coe_zero, Pi.zero_apply]
  have nat : ∀ (i : ι) (w : C ⊗[k] M),
      φ i (TensorProduct.equivFinsuppOfBasisLeft b w j) =
        TensorProduct.equivFinsuppOfBasisLeft b ((φ i).lTensor C w) j := by
    intro i w
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply hφ
  intro i
  rw [nat, hz i, map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem isReduced_tensor_of_forall_prime {k : Type*} [Field k] (C A : Type*) [CommRing C]
    [Algebra k C] [CommRing A] [Algebra k A] [IsReduced A]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsReduced (C ⊗[k] (A ⧸ p))) : IsReduced (C ⊗[k] A) := by
  classical
  refine ⟨fun x hx => ?_⟩
  refine eq_zero_of_forall_lTensor_eq_zero
    (fun p : {p : Ideal A // p.IsPrime} => (Ideal.Quotient.mkₐ k p.1).toLinearMap) ?_ x ?_
  · intro a ha
    have hmem : a ∈ nilradical A := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      intro J hJ
      have h1 := ha ⟨J, hJ⟩
      simpa [Ideal.Quotient.eq_zero_iff_mem] using h1
    exact IsReduced.eq_zero a (mem_nilradical.1 hmem)
  · intro p
    have := p.2
    have := h p.1
    have hF : ∀ w : C ⊗[k] A,
        Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1) w =
          (Ideal.Quotient.mkₐ k p.1).toLinearMap.lTensor C w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp
      | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    rw [← hF]
    exact IsReduced.eq_zero _
      (hx.map (Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1)))

theorem isReduced_field_tensor_domain {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A] :
    IsReduced (K ⊗[k] A) := by
  classical
  have hfp : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
    show Algebra.FormallySmooth k (Localization.AtPrime (⊥ : Ideal A))
    have hS : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
      ext x
      simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
    have hloc : IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A)) :=
      hS ▸ (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl (Localization.AtPrime (⊥ : Ideal A)))
    have e1 : Algebra.EssFiniteType A (FractionRing A) := .of_isLocalization _ (nonZeroDivisors A)
    have e2 : Algebra.EssFiniteType k (FractionRing A) := .comp k A _
    exact (Algebra.FormallySmooth.iff_of_equiv ((IsLocalization.algEquiv (nonZeroDivisors A)
      (FractionRing A) (Localization.AtPrime (⊥ : Ideal A))).restrictScalars k)).1 inferInstance
  obtain ⟨v, ⟨f, rfl⟩, hv, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hgen Algebra.isOpen_smoothLocus
  have hf0 : f ≠ 0 := by
    have := (PrimeSpectrum.mem_basicOpen f _).1 hv
    simpa using this
  have hsm : Algebra.Smooth k (Localization.Away f) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.1 hsub
  have hred : IsReduced (K ⊗[k] Localization.Away f) :=
    GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed K _
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k A (Localization.Away f)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ hinj)

theorem isReduced_field_tensor {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (K ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).2 hB⟩
  refine isReduced_tensor_of_forall_prime K B (fun p _ => ?_)
  have : Algebra.FiniteType k (B ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p)
      (Ideal.Quotient.mkₐ_surjective k p)
  exact isReduced_field_tensor_domain K (B ⧸ p)

theorem isReduced_tensor {k : Type*} [Field k] [PerfectField k] (A B : Type*)
    [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine isReduced_tensor_of_forall_prime A B (fun p _ => ?_)
  have : IsReduced (FractionRing (B ⧸ p) ⊗[k] A) := isReduced_field_tensor (FractionRing (B ⧸ p)) A
  have : IsReduced (A ⊗[k] FractionRing (B ⧸ p)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p)))
      (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p))).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k (B ⧸ p) (FractionRing (B ⧸ p))))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective (B ⧸ p) _))

universe u

end GlobalTheory.ReducedAlg
end

section

open TensorProduct

namespace GlobalTheory

namespace FlatDescent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

variable (A B N) in
def act : B ⊗[A] N →ₗ[B] N := LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)

@[simp] theorem act_tmul (b : B) (n : N) : act A B N (b ⊗ₜ n) = b • n := by
  simp [act]

structure IsDescentDatum (θ : N →ₗ[B] B ⊗[A] N) : Prop where
  counit : ∀ n, act A B N (θ n) = n
  coassoc : ∀ n, (θ.restrictScalars A).lTensor B (θ n) = (TensorProduct.mk A B N 1).lTensor B (θ n)

def invariants (θ : N →ₗ[B] B ⊗[A] N) : Submodule A N :=
  LinearMap.ker (θ.restrictScalars A - TensorProduct.mk A B N 1)

@[simp] theorem mem_invariants {θ : N →ₗ[B] B ⊗[A] N} {n : N} :
    n ∈ invariants θ ↔ θ n = 1 ⊗ₜ n := by
  simp [invariants, sub_eq_zero]

variable (B) in
def canonical (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[B] B ⊗[A] (B ⊗[A] M) :=
  (TensorProduct.mk A B M 1).baseChange B

variable (B) in
theorem isDescentDatum_canonical (M : Type*) [AddCommGroup M] [Module A M] :
    IsDescentDatum (canonical (A := A) B M) := by
  constructor <;> intro x
  · induction x using TensorProduct.inductionOn with
    | tmul b m => simp [canonical, smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction x using TensorProduct.inductionOn with
    | tmul b m => simp [canonical]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (B) in
def extend (P : Submodule A N) : B ⊗[A] P →ₗ[B] N := LinearMap.liftBaseChange B P.subtype

@[simp] theorem extend_tmul (P : Submodule A N) (b : B) (n : P) :
    extend B P (b ⊗ₜ n) = b • (n : N) := by
  simp [extend]

theorem act_lTensor_subtype (P : Submodule A N) (x : B ⊗[A] P) :
    act A B N (P.subtype.lTensor B x) = extend B P x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem apply_extend (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) = (invariants θ).subtype.lTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [mem_invariants.1 m.2, smul_tmul']
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem IsDescentDatum.bijective_extend [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : Function.Bijective (extend B (invariants θ)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) _
      (invariants θ).injective_subtype
    rw [← apply_extend, hx, map_zero, map_zero]
  · intro n
    have hex := Module.Flat.lTensor_exact B
      (LinearMap.exact_subtype_ker_map (θ.restrictScalars A - TensorProduct.mk A B N 1))
    obtain ⟨x, hx⟩ := (hex (θ n)).1 (by
      rw [LinearMap.lTensor_sub, LinearMap.sub_apply, h.coassoc, sub_self])
    exact ⟨x, (act_lTensor_subtype (invariants θ) x).symm.trans
      ((congrArg (act A B N) hx).trans (h.counit n))⟩

theorem IsDescentDatum.isBaseChange [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : IsBaseChange B (invariants θ).subtype :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bijective_extend) fun n => by simp

section Amitsur

variable (B) (M : Type*) [AddCommGroup M] [Module A M]

def toInvariants : M →ₗ[A] invariants (canonical (A := A) B M) :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m => by simp [canonical]

theorem bijective_toInvariants [Module.FaithfullyFlat A B] :
    Function.Bijective (toInvariants (A := A) B M) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B,
    ← Function.Bijective.of_comp_iff' (isDescentDatum_canonical (A := A) B M).bijective_extend]
  convert Function.bijective_id
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [toInvariants, smul_tmul']
  | add x y hx hy => simp_all

def amitsurDiff : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (canonical B M).restrictScalars A - TensorProduct.mk A B (B ⊗[A] M) 1

@[simp] theorem amitsurDiff_tmul (b : B) (m : M) :
    amitsurDiff B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := rfl

theorem amitsur_exact [Module.FaithfullyFlat A B] :
    Function.Injective (TensorProduct.mk A B M 1) ∧
      Function.Exact (TensorProduct.mk A B M 1) (amitsurDiff (A := A) B M) := by
  refine ⟨Module.FaithfullyFlat.tensorProduct_mk_injective M, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (bijective_toInvariants (A := A) B M).2 ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro ⟨m, rfl⟩
    simp

end Amitsur

section Morphisms

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']


variable (B) in
theorem bijective_baseChange_iff [Module.FaithfullyFlat A B] (g : M →ₗ[A] M') :
    Function.Bijective (g.baseChange B) ↔ Function.Bijective g :=
  Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g

end Morphisms

section Invertible

theorem invertible_of_isBaseChange [Module.FaithfullyFlat A B] {M : Type*} [AddCommGroup M]
    [Module A M] {j : M →ₗ[A] N} (hj : IsBaseChange B j) [Module.Invertible B N] :
    Module.Invertible A M := by
  have : Module.Finite A M := Descent.finite_of_isBaseChange hj
  have : Module.Projective A M := Descent.projective_of_isBaseChange hj
  let e : B ⊗[A] (Module.Dual A M ⊗[A] M) ≃ₗ[B] B ⊗[A] A :=
    AlgebraTensorModule.distribBaseChange A B _ _ ≪≫ₗ
      TensorProduct.congr (SymAlg.isBaseChange_dual hj).equiv hj.equiv ≪≫ₗ
        Module.Invertible.linearEquiv B N ≪≫ₗ (AlgebraTensorModule.rid A B B).symm
  have he : (contractLeft A M).baseChange B = e.toLinearMap := by
    ext ξ m
    apply (AlgebraTensorModule.rid A B B).injective
    simp [e, Module.Invertible.linearEquiv, hj.toDual_comp_apply, Algebra.algebraMap_eq_smul_one]
  refine ⟨(bijective_baseChange_iff B _).1 ?_⟩
  rw [he]
  exact e.bijective

variable (B) in
theorem IsDescentDatum.invertible_invariants [Module.FaithfullyFlat A B]
    {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) [Module.Invertible B N] :
    Module.Invertible A (invariants θ) :=
  invertible_of_isBaseChange h.isBaseChange


end Invertible

section Gluing



end Gluing

end FlatDescent

end GlobalTheory
end

section

open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Decomposition

variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']

end Decomposition

section Ideals

variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem ideal_map_comap_of_span (I : Ideal B) (N : Submodule K A)
    (h : Submodule.span L (j.toLinearMap '' N) = I.restrictScalars L) :
    (I.comap j).map j = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  have hle : Submodule.span L (j.toLinearMap '' N) ≤ ((I.comap j).map j).restrictScalars L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    refine Ideal.mem_map_of_mem j ?_
    exact h.le (Submodule.subset_span ⟨a, ha, rfl⟩)
  exact hle (h.ge hx)

theorem ideal_map_comap_of_stable (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I :=
  ideal_map_comap_of_span I _ (span_image_comap_eq hj s hs φ hφ (I.restrictScalars L) hI)

section Graded

variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]

end Graded

end Ideals

section Tensor

open Algebra.TensorProduct

variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

end Tensor

section Polynomial

open MvPolynomial

variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]


end Polynomial

end GlobalTheory.GaloisDescent
end
