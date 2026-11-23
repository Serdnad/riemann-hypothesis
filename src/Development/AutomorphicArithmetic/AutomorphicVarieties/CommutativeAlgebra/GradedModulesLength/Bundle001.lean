module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle002
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle001
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle001
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.int_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v → ∀ y : K, IsIntegral O y → y ≠ 0 → 0 ≤ v y := by
  intro O _ _ _ _ _ K _ _ _ _ v hv y hy hy0
  have v1 : v 1 = 0 := by
    have h := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [one_mul] at h
    linarith
  have vneg : ∀ z : K, z ≠ 0 → v (-z) = v z := by
    intro z hz
    have h1 := hv.mul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_one_mul, neg_neg, v1] at h1
    have h2 := hv.mul (-1) z (neg_ne_zero.mpr one_ne_zero) hz
    rw [neg_one_mul] at h2
    linarith
  have vpow : ∀ k : ℕ, v (y ^ k) = k * v y := by
    intro k
    induction k with
    | zero => simp [v1]
    | succ k ih =>
      rw [pow_succ, hv.mul _ _ (pow_ne_zero _ hy0) hy0, ih]
      push_cast
      ring
  have vsum : ∀ (s : Finset ℕ) (f : ℕ → K) (c : ℝ), (∀ i ∈ s, f i ≠ 0 → c ≤ v (f i)) →
      (∑ i ∈ s, f i) ≠ 0 → c ≤ v (∑ i ∈ s, f i) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => intro _ h; simp at h
    | insert a s ha ih =>
      intro hf hs
      rw [Finset.sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hs ⊢
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs
      by_cases hS : (∑ i ∈ s, f i) = 0
      · rw [hS, add_zero]
        exact hf a (Finset.mem_insert_self a s) hfa
      have h1 := hv.add _ _ hfa hS hs
      have h2 := hf a (Finset.mem_insert_self a s) hfa
      have h3 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hS
      exact le_trans (le_min h2 h3) h1
  by_contra hneg
  push_neg at hneg
  obtain ⟨p, hpm, hp⟩ := hy
  have hsum := hp
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hS : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) = -(y ^ p.natDegree) :=
    eq_neg_of_add_eq_zero_left hsum
  have hyn : y ^ p.natDegree ≠ 0 := pow_ne_zero _ hy0
  have hS0 : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) ≠ 0 := by
    rw [hS]
    exact neg_ne_zero.mpr hyn
  have hnpos : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      rw [h, Finset.sum_range_zero, pow_zero] at hS
      exact one_ne_zero (neg_eq_zero.mp hS.symm)
    · exact h
  have hterm : ∀ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i ≠ 0 →
      ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (algebraMap O K (p.coeff i) * y ^ i) := by
    intro i hi hne
    have hc : p.coeff i ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hmc : algebraMap O K (p.coeff i) ≠ 0 := by
      intro h
      apply hc
      exact (FaithfulSMul.algebraMap_injective O K) (by rw [h, map_zero])
    rw [hv.mul _ _ hmc (pow_ne_zero _ hy0), hv.base _ hc, vpow]
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hle : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ (i : ℝ) * v y := by
      apply mul_le_mul_of_nonpos_right _ hneg.le
      exact_mod_cast hi'
    have h0 : (0 : ℝ) ≤ ((IsDiscreteValuationRing.addVal O (p.coeff i)).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤
      v (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) :=
    vsum (Finset.range p.natDegree) (fun i => algebraMap O K (p.coeff i) * y ^ i) _ hterm hS0
  rw [hS, vneg _ hyn, vpow, Nat.cast_pred hnpos] at hbound
  linarith
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem prime_maximal_or_kernel (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (P : Ideal B) [hP : P.IsPrime]
    [Module.Finite O (B ⧸ P)] :
    P = maximalIdeal B ∨ ((∀ c : O, c ≠ 0 → algebraMap O B c ∉ P) ∧ ∃ σ : B →ₐ[O] K, RingHom.ker σ = P) := by
  classical
  haveI : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  have hcomap : ∀ a : O, algebraMap O (B ⧸ P) a = 0 ↔ algebraMap O B a ∈ P := by
    intro a
    rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  by_cases hc : ∃ c : O, c ≠ 0 ∧ algebraMap O B c ∈ P
  · obtain ⟨c, hc0, hcP⟩ := hc
    left
    apply IsLocalRing.eq_maximalIdeal
    have hQ : (P.comap (algebraMap O B)).IsMaximal := by
      apply Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _)
      intro h
      have hmem : c ∈ P.comap (algebraMap O B) := hcP
      rw [h] at hmem
      exact hc0 ((Submodule.mem_bot O).1 hmem)
    have hbot : (⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P)) = P.comap (algebraMap O B) := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap, hcomap]
    haveI : (⊥ : Ideal (B ⧸ P)).IsPrime := Ideal.isPrime_bot
    have hmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) (⊥ : Ideal (B ⧸ P)) (by
      change ((⊥ : Ideal (B ⧸ P)).comap (algebraMap O (B ⧸ P))).IsMaximal
      rw [hbot]
      exact hQ)
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact Ring.isField_iff_maximal_bot.2 hmax
  · push_neg at hc
    right
    refine ⟨hc, ?_⟩
    have hinj : Function.Injective (algebraMap O (B ⧸ P)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact hc a h0 ((hcomap a).1 ha)
    haveI : Module.IsTorsionFree O (B ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
    haveI : Module.IsTorsionFree O K :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective O K)
    haveI : Algebra.IsAlgebraic O (B ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let τ : (B ⧸ P) →ₐ[O] K := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨τ.comp (Ideal.Quotient.mkₐ O P), ?_⟩
    have hτ : RingHom.ker (τ : (B ⧸ P) →+* K) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O)
      ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      change τ (algebraMap O (B ⧸ P) a) = 0 ↔ a = 0
      rw [AlgHom.commutes]
      constructor
      · intro h
        exact FaithfulSMul.algebraMap_injective O K (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]
    have hτi : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot (τ : (B ⧸ P) →+* K)).2 hτ
    ext b
    rw [RingHom.mem_ker]
    change τ (Ideal.Quotient.mk P b) = 0 ↔ b ∈ P
    rw [map_eq_zero_iff τ hτi, Ideal.Quotient.eq_zero_iff_mem]

theorem UpperTheory.V.Alg.M.emb_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I →
    ∀ P : Ideal (𝒜 0), P.IsPrime → (∀ b : 𝒜 0, (b : A) ∈ I → b ∈ P) →
      (P = maximalIdeal (𝒜 0) ∨ ((∀ c : O, c ≠ 0 → algebraMap O (𝒜 0) c ∉ P) ∧ ∃ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = P)) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x I hM P hP hIP
  let φ : 𝒜 0 →ₗ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ (𝒜 0).subtype
  have hr : (LinearMap.range φ).FG := by
    have : LinearMap.range φ = (𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [this]; exact hM
  haveI : Module.Finite O (LinearMap.range φ) := Module.Finite.iff_fg.2 hr
  haveI : Module.Finite O (𝒜 0 ⧸ LinearMap.ker φ) := Module.Finite.equiv φ.quotKerEquivRange.symm
  let ψ : 𝒜 0 →ₗ[O] (𝒜 0 ⧸ P) := (Ideal.Quotient.mkₐ O P).toLinearMap
  have hk : LinearMap.ker φ ≤ LinearMap.ker ψ := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.2 (hIP b (Ideal.Quotient.eq_zero_iff_mem.1 hb))
  haveI : Module.Finite O (𝒜 0 ⧸ P) := by
    refine Module.Finite.of_surjective ((LinearMap.ker φ).liftQ ψ hk) fun y => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  exact prime_maximal_or_kernel O K (𝒜 0) P
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped nonZeroDivisors

private theorem length_quotient_eq_norm_valuation {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type} [CommRing D] [Algebra O D] [Module.Finite O D] [Module.Free O D] (a : D) :
    Module.length O (D ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal O (Algebra.norm O a) := by
  classical
  let b := Module.Free.chooseBasis O D
  let f : D →ₗ[O] D := Algebra.lmul O D a
  let Φ := LinearMap.toMatrix b b f
  have hdet : Algebra.norm O a = Φ.det := by
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  have hmul : Φ.mulVecLin = b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := b.equivFun.surjective y
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    simp only [Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f x
  have hI : (Ideal.span {a}).restrictScalars O = LinearMap.range f := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range, f,
      Algebra.coe_lmul_eq_mul]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
  have hmap : (LinearMap.range f).map b.equivFun.toLinearMap = LinearMap.range Φ.mulVecLin := by
    rw [hmul, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ← LinearMap.range_eq_map]
  let e : (D ⧸ Ideal.span {a}) ≃ₗ[O] KStar.Selmer.H2 Φ :=
    (Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a})).symm.trans
      ((Submodule.quotEquivOfEq _ _ hI).trans (Submodule.Quotient.equiv _ _ b.equivFun hmap))
  rw [e.length_eq, hdet]
  exact KStar.Selmer.length_cokernel_eq_addVal_det Φ

private theorem algHom_finite_domain_injective {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] (σ : D →ₐ[O] K) :
    Function.Injective σ := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite O D
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : (RingHom.ker σ).comap (algebraMap O D) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).1 h,
      fun h => by simp [h]⟩
  have hmem : x ∈ RingHom.ker σ := hx
  rw [Ideal.eq_bot_of_comap_eq_bot hker] at hmem
  exact hmem

attribute [local instance] FractionRing.liftAlgebra in
private theorem algebra_norm_eq_prod_embeddings {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    {K : Type} [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] [Module.Free O D]
    (a : D) : ∃ _ : Fintype (D →ₐ[O] K), algebraMap O K (Algebra.norm O a) = ∏ σ : D →ₐ[O] K, σ a := by
  classical
  have : IsScalarTower O (FractionRing O) K := FractionRing.isScalarTower_liftAlgebra O K
  let M := Algebra.algebraMapSubmonoid D O⁰
  let L := Localization M
  have hM : M ≤ D⁰ := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O D)).2 (nonZeroDivisors.ne_zero hm))
  have : IsDomain L := IsLocalization.isDomain_localization hM
  have hF : IsField L := by
    have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
    exact isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing O))
  letI : Field L := hF.toField
  letI : Algebra (FractionRing O) L := localizationAlgebra O⁰ D
  have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
  have hN : Algebra.norm (FractionRing O) (algebraMap D L a) =
      algebraMap O (FractionRing O) (Algebra.norm O a) :=
    Algebra.norm_localization O O⁰ a
  have hE := Algebra.norm_eq_prod_embeddings (FractionRing O) K (algebraMap D L a)
  let r : (L →ₐ[FractionRing O] K) → (D →ₐ[O] K) := fun τ =>
    (τ.restrictScalars O).comp (IsScalarTower.toAlgHom O D L)
  have hinj : Function.Injective r := by
    intro τ₁ τ₂ h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext M
    ext d
    exact DFunLike.congr_fun h d
  have hsurj : Function.Surjective r := by
    intro σ
    have hu : ∀ y : M, IsUnit ((σ : D →+* K) y) := by
      rintro ⟨_, m, hm, rfl⟩
      rw [AlgHom.coe_toRingHom, AlgHom.commutes]
      exact isUnit_iff_ne_zero.2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 (nonZeroDivisors.ne_zero hm))
    let τ₀ : L →+* K := IsLocalization.lift hu
    have hc : τ₀.comp (algebraMap (FractionRing O) L) = algebraMap (FractionRing O) K := by
      apply IsLocalization.ringHom_ext O⁰
      ext c
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply O D L, IsLocalization.lift_eq]
      simp
    refine ⟨{ τ₀ with commutes' := fun x => DFunLike.congr_fun hc x }, ?_⟩
    ext d
    simp [r, τ₀, IsLocalization.lift_eq]
  letI inst : Fintype (D →ₐ[O] K) := Fintype.ofSurjective r hsurj
  refine ⟨inst, ?_⟩
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) K, ← hN, hE]
  exact Fintype.prod_bijective r ⟨hinj, hsurj⟩ _ _ (fun τ => rfl)

theorem UpperTheory.V.Alg.M.length_quotient_span_eq_finsum_valuation :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] (a : D), a ≠ 0 →
      Finite (D →ₐ[O] K) ∧ Module.length O (D ⧸ Ideal.span {a}) ≠ ⊤ ∧
      (((Module.length O (D ⧸ Ideal.span {a})).toNat : ℕ) : ℝ) = ∑ᶠ σ : D →ₐ[O] K, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv D _ _ _ _ _ a ha
  classical
  have : Module.Free O D := inferInstance
  obtain ⟨hF, hN⟩ := algebra_norm_eq_prod_embeddings (O := O) (K := K) a
  have hn : Algebra.norm O a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hσ : ∀ σ : D →ₐ[O] K, σ a ≠ 0 := fun σ h => ha (algHom_finite_domain_injective σ (h.trans (map_zero _).symm))
  have h1 : v 1 = 0 := by
    have := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    linarith
  have hp : ∀ s : Finset (D →ₐ[O] K), v (∏ σ ∈ s, σ a) = ∑ σ ∈ s, v (σ a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ,
        hv.mul _ _ (hσ τ) (Finset.prod_ne_zero_iff.2 fun σ _ => hσ σ), ih]
  rw [length_quotient_eq_norm_valuation]
  refine ⟨inferInstance, fun h => hn (IsDiscreteValuationRing.addVal_eq_top_iff.1 h), ?_⟩
  rw [← hv.base _ hn, hN, hp, finsum_eq_sum_of_fintype]
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem der_satSq {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) (f : A) (hf : f ∈ satSq x) : D f = 0 := by
  obtain ⟨c, hc, hcf⟩ := hf
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have key : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
    intro g hg
    rw [sq] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      have ha' : x a = 0 := ha
      have hb' : x b = 0 := hb
      rw [hD', ha', hb']; simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, add_zero]
  have := key _ hcf
  rw [map_smul, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

private theorem len_le_of_inj {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (hN : Module.length O N ≠ ⊤) (ψ : M → N) (hψ : Function.Injective ψ) :
    Module.length O M ≤ Module.length O N := by
  obtain ⟨hfN, n, hn, hcn⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength (Module.length_ne_top_iff.1 hN)
  have hfM : Finite M := Finite.of_injective ψ hψ
  have hM : IsFiniteLength O M := isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨_, m, hm, hcm⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength hM
  have hle := Nat.card_le_card_of_injective ψ hψ
  rw [hcm, hcn] at hle
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  rw [hm, hn]
  exact_mod_cast (Nat.pow_le_pow_iff_right h1).1 hle

theorem UpperTheory.V.Alg.M.mprime_holds :
    LemmaM' := by
  intro O _ _ _ _ A X _ _ _ _ 𝒜 _ x j hx ι F hF c hc M _ _ D hD hDF hlift
  by_cases htop : cotLen x 𝒜 j F = ⊤
  · rw [htop]; exact le_top
  have hsat : ∀ μ, satSq x ≤ LinearMap.ker (D μ) := by
    intro μ f hf
    obtain ⟨D', hD', -, h⟩ := hlift μ
    rw [LinearMap.mem_ker, h, der_satSq x D' hD' f hf, map_zero]
  have hspan : ∀ μ, (cotSpan x F).comap (cotLat x 𝒜 j).subtype ≤
      LinearMap.ker (((satSq x).liftQ (D μ) (hsat μ)) ∘ₗ (cotLat x 𝒜 j).subtype) := by
    intro μ
    rw [LinearMap.ker_comp]
    refine Submodule.comap_mono ?_
    rw [cotSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDF μ i
  let ψ : M → ((cotLat x 𝒜 j ⧸ (cotSpan x F).comap (cotLat x 𝒜 j).subtype) →ₗ[O] O ⧸ Ideal.span {c}) :=
    fun μ => Submodule.liftQ _ _ (hspan μ)
  have hψ : Function.Injective ψ := by
    intro μ ν h
    apply hD
    have hj : ∀ f ∈ 𝒜 j, D μ f = D ν f := fun f hf =>
      LinearMap.congr_fun h (Submodule.Quotient.mk ⟨(satSq x).mkQ f, f, ⟨hf, hx f hf⟩, rfl⟩)
    have hi : ∀ μ i, i ≠ j → ∀ f ∈ 𝒜 i, D μ f = 0 := by
      intro μ i hi f hf
      obtain ⟨D', -, hw, h⟩ := hlift μ
      rw [h, hw i hi f hf, map_zero]
    refine LinearMap.ext fun f => ?_
    induction f using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, map_zero]
    | @homogeneous i m =>
      by_cases hij : i = j
      · subst hij; exact hj _ m.2
      · rw [hi μ i hij _ m.2, hi ν i hij _ m.2]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hp
  have hQ : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {c})) ≤ 1 := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk]
    exact Formalism.MainNotions.V.Pf.V2.length_hom_residue_le p hp.maximalIdeal_eq hp.ne_zero k
  have hle := Formalism.MainNotions.V.Pf.V2.length_hom_le hQ (Module.length_ne_top_iff.1 htop)
  exact (len_le_of_inj (ne_top_of_le_ne_top htop hle) ψ hψ).trans hle
end
