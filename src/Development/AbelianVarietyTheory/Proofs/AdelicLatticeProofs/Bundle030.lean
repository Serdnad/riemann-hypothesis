module

public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
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
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory

theorem exists_denominator_of_isField_localization (B A : Type) [CommRing B] [CommRing A]
    [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] (M : Submonoid B)
    (hF : IsField (Localization M)) (f : A)
    (hf : IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) :
    ∃ m ∈ M, ∃ b' : B, algebraMap B A m * f = algebraMap B A b' := by
  letI : Field (Localization M) := hF.toField
  haveI : CharZero (Localization M) := algebraRat.charZero _
  let K := Localization M
  let A' := Localization (Algebra.algebraMapSubmonoid A M)
  haveI : IsReduced A' := inferInstance
  haveI : Algebra.FiniteType K A' := by
    haveI : IsLocalization (Submonoid.map (algebraMap B A) M) A' :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid A M) A')
    have h := RingHom.finiteType_localizationPreserves (algebraMap B A) M K A'
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact h
  let g : A →ₐ[B] A' := IsScalarTower.toAlgHom B A A'
  let φ : A ⊗[B] A →ₐ[B] A' ⊗[K] A' :=
    Algebra.TensorProduct.lift
      (((Algebra.TensorProduct.includeLeft : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (((Algebra.TensorProduct.includeRight : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (fun _ _ => Commute.all _ _)
  have hn : IsNilpotent (g f ⊗ₜ[K] (1 : A') - (1 : A') ⊗ₜ[K] g f) := by
    have := hf.map φ
    simpa [φ] using this
  obtain ⟨k, hk⟩ := GlobalTheory.ClassFin.mem_range_algebraMap_of_isNilpotent_tmul_sub K A' (g f) hn
  obtain ⟨⟨β, t⟩, ht⟩ := IsLocalization.surj M k
  have h1 : algebraMap A A' (algebraMap B A t * f) = algebraMap A A' (algebraMap B A β) := by
    have := congrArg (algebraMap K A') ht
    rw [map_mul, hk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← this,
      mul_comm]
    rfl
  obtain ⟨⟨_, u, hu, rfl⟩, hc⟩ :=
    (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid A M) A').1 h1
  refine ⟨u * t, M.mul_mem hu t.2, u * β, ?_⟩
  simpa [map_mul, mul_assoc] using hc

theorem exists_common_denominator_of_isNilpotent :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  intro B A _ _ _ _ _ _ _ hinj s hs
  classical
  haveI : IsReduced B := isReduced_of_injective (algebraMap B A) hinj
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : p.IsPrime := hp.1.1
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp _
  have hF : IsField (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced
  have key : ∃ b ∈ p.primeCompl, ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simp⟩
    | insert a s _ ih =>
      obtain ⟨b, hb, h⟩ := ih (fun f hf => hs f (Finset.mem_insert_of_mem hf))
      obtain ⟨c, hc, c', hc'⟩ := exists_denominator_of_isField_localization B A p.primeCompl hF a
        (hs a (Finset.mem_insert_self _ _))
      refine ⟨b * c, mul_mem hb hc, fun f hf => ?_⟩
      rcases Finset.mem_insert.1 hf with rfl | hf
      · exact ⟨b * c', by rw [map_mul, map_mul, mul_assoc, hc']⟩
      · obtain ⟨b', hb'⟩ := h f hf
        exact ⟨c * b', by rw [map_mul, map_mul, ← hb']; ring⟩
  obtain ⟨b, hb, h⟩ := key
  exact ⟨b, fun h0 => hb (h0 ▸ p.zero_mem), h⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isUnit_of_forall_maximal {K A : Type} [Field K] [Infinite K] [CommRing A]
    [Algebra K A] [IsArtinianRing A] (Θ : A →ₗ[K] A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ c, Θ c ∉ 𝔪) : ∃ c, IsUnit (Θ c) := by
  classical
  have hfin := IsArtinianRing.setOf_isMaximal_finite A
  let s : Finset (Subspace K A) :=
    hfin.toFinset.image fun 𝔪 => (𝔪.restrictScalars K).comap Θ
  have hs : ⊤ ∉ s := by
    intro ht
    obtain ⟨𝔪, hm, he⟩ := Finset.mem_image.1 ht
    obtain ⟨c, hc⟩ := h 𝔪 (by simpa using hm)
    have : c ∈ (𝔪.restrictScalars K).comap Θ := by rw [he]; trivial
    exact hc this
  have hne := Subspace.biUnion_ne_univ_of_top_notMem hs
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
  refine ⟨c, ?_⟩
  by_contra hu
  obtain ⟨𝔪, hm, hle⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
  apply hc
  simp only [Set.mem_iUnion]
  exact ⟨_, Finset.mem_image.2 ⟨𝔪, by simpa using hm, rfl⟩, hle⟩

theorem hilbert90_baseChange : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  intro F E K _ _ _ _ _ _ _ τ m hm x hx
  classical
  set T := Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) with hT
  have hm0 : 0 < m := hm ▸ orderOf_pos τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K _
  have hpow : ∀ (i : ℕ) (y : K ⊗[F] E), T^[i] y = (T ^ i) y := fun i y => by
    rw [AlgHom.coe_pow]
  have htm : ∀ (i : ℕ) (k : K) (c : E), (T ^ i) (k ⊗ₜ c) = k ⊗ₜ ((τ ^ i) c) := by
    intro i k c
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, ih, AlgEquiv.mul_apply]; simp [hT]
  have hTm : ∀ y, (T ^ m) y = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k c => rw [htm, ← hm, pow_orderOf_eq_one]; rfl
    | add a b ha hb => rw [map_add (f := _), ha, hb]
  simp only [hpow] at hx
  let a : ℕ → K ⊗[F] E := fun i => ∏ j ∈ Finset.range i, (T ^ j) x
  have ha : ∀ i, x * T (a i) = a (i + 1) := by
    intro i
    simp only [a, map_prod, Finset.prod_range_succ', pow_zero, AlgHom.one_apply, pow_succ',
      AlgHom.mul_apply]
    ring
  have ha0 : a 0 = 1 := by simp [a]
  have ham : a m = 1 := hx
  let Θ : K ⊗[F] E →ₗ[K] K ⊗[F] E :=
    ∑ i ∈ Finset.range m, (LinearMap.mulLeft K (a i)).comp (T ^ i).toLinearMap
  have hΘ : ∀ c, Θ c = ∑ i ∈ Finset.range m, a i * (T ^ i) c := by
    intro c
    simp [Θ, LinearMap.sum_apply]
  have hfix : ∀ c, x * T (Θ c) = Θ c := by
    intro c
    have h1 : x * T (Θ c) = ∑ i ∈ Finset.range m, a (i + 1) * (T ^ (i + 1)) c := by

      rw [hΘ, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← mul_assoc, ha, pow_succ', AlgHom.mul_apply]
    have h2 := Finset.sum_range_succ' (fun i => a i * (T ^ i) c) m
    rw [Finset.sum_range_succ, ham, ha0, hTm, pow_zero, AlgHom.one_apply] at h2
    rw [h1, hΘ]
    exact (add_right_cancel h2).symm
  obtain ⟨c, hc⟩ := exists_isUnit_of_forall_maximal Θ (fun 𝔪 h𝔪 => by
    by_contra hcon
    push_neg at hcon
    letI : Field ((K ⊗[F] E) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let ι : E →+* (K ⊗[F] E) ⧸ 𝔪 :=
      (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeRight.toRingHom
    let φ : Fin m → (E →* (K ⊗[F] E) ⧸ 𝔪) := fun i =>
      ι.toMonoidHom.comp ((τ ^ (i : ℕ) : E ≃ₐ[F] E) : E →* E)
    have hφ : Function.Injective φ := by
      intro i j hij
      have : τ ^ (i : ℕ) = τ ^ (j : ℕ) := by
        ext c
        exact ι.injective (DFunLike.congr_fun hij c)
      exact Fin.ext (pow_injOn_Iio_orderOf (by simp [hm]) (by simp [hm]) this)
    have hli := (linearIndependent_monoidHom E ((K ⊗[F] E) ⧸ 𝔪)).comp φ hφ
    have := Fintype.linearIndependent_iff.1 hli (fun i => Ideal.Quotient.mk 𝔪 (a i)) (by
      ext c
      have h := Ideal.Quotient.eq_zero_iff_mem.2 (hcon (1 ⊗ₜ c))

      rw [hΘ, map_sum, Finset.sum_range] at h
      simp only [htm, map_mul] at h
      rw [Finset.sum_apply]
      exact h) ⟨0, hm0⟩
    simp only [ha0, map_one] at this
    exact one_ne_zero this)
  exact ⟨hc.unit, hfix c⟩

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem card_quot_span_algebraMap : ∀ (R O : Type) [CommRing R] [Nontrivial R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O] (t : R), Nat.card (O ⧸ Ideal.span {algebraMap R O t}) = Nat.card (R ⧸ Ideal.span {t}) ^ Module.finrank R O := by
  intro R O _ _ _ _ _ _ t
  classical
  let b := Module.Free.chooseBasis R O
  let f : O →+ (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) :=
    { toFun := fun x i => Ideal.Quotient.mk _ (b.repr x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hsurj : Function.Surjective f := by
    intro y
    choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm z, ?_⟩
    ext i
    show Ideal.Quotient.mk _ (b.equivFun (b.equivFun.symm z) i) = y i
    rw [LinearEquiv.apply_symm_apply, hz]
  have hker : f.ker = (Ideal.span {algebraMap R O t}).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · intro h
      have h' : ∀ i, ∃ a, a * t = b.repr x i := fun i => by
        have := congrFun h i
        exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
      choose a ha using h'
      refine ⟨b.equivFun.symm a, ?_⟩
      rw [mul_comm, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [← ha i, mul_comm]
    · rintro ⟨a, rfl⟩
      ext i
      show Ideal.Quotient.mk _ (b.repr _ i) = 0
      rw [mul_comm, ← Algebra.smul_def, map_smul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b.repr a i, by simp [mul_comm]⟩
  have e := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  rw [hker] at e
  have h1 : Nat.card (O ⧸ Ideal.span {algebraMap R O t}) =
      Nat.card (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) := e
  rw [h1, Nat.card_fun, Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex R O)]

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyInv

variable {R : Type} [CommRing R] {n : ℕ}

theorem map_mul_map_inv (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    M.map σ * (M⁻¹).map σ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_add (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 + M).map σ = 1 + M.map σ := by
  rw [Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_sub (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 - M).map σ = 1 - M.map σ := by
  rw [Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem one_add_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 + (1 - g) * (1 + g)⁻¹ = (2 : R) • (1 + g)⁻¹ := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) + (1 - g) = (2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [two_smul]; abel
  calc 1 + (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ + (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) + (1 - g)) * (1 + g)⁻¹ := (Matrix.add_mul _ _ _).symm
    _ = (2 : R) • (1 + g)⁻¹ := by rw [h2, Matrix.smul_mul, Matrix.one_mul]

theorem one_sub_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 - (1 - g) * (1 + g)⁻¹ = (2 : R) • (g * (1 + g)⁻¹) := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) - (1 - g) = (2 : R) • g := by
    rw [two_smul]; abel
  calc 1 - (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ - (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) - (1 - g)) * (1 + g)⁻¹ := (Matrix.sub_mul _ _ _).symm
    _ = (2 : R) • (g * (1 + g)⁻¹) := by rw [h2, Matrix.smul_mul]

theorem one_add_cayley_mul (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) (c : R)
    (hc : 2 * c = 1) : (1 + (1 - g) * (1 + g)⁻¹) * (c • (1 + g)) = 1 := by
  rw [one_add_cayley g h, smul_mul_smul_comm, hc, one_smul, Matrix.nonsing_inv_mul _ h]

private theorem eq_zero_of_mul_mul_eq_zero_of_isUnit_det (A B X : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (h : A * X * B = 0) : X = 0 := by
  calc X = (A⁻¹ * A) * X * (B * B⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
          Matrix.mul_one]
    _ = A⁻¹ * (A * X * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

private theorem isUnit_det_map_of_isUnit_det (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : IsUnit (M.map σ).det := by
  simpa [RingHom.map_det, RingHom.mapMatrix_apply] using h.map σ

theorem cayley_transform : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  intro R _ σ n G hσ hG hGu h2
  obtain ⟨c, hc⟩ := h2.exists_right_inv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg hP
    have hSP : (1 - g) * (1 + g)⁻¹ * (1 + g) = 1 - g := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + g)ᵀ) ((1 + g).map σ) _
        (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
      have e1 : (1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ = (1 - g)ᵀ := by
        rw [← Matrix.transpose_mul, hSP]
      have e2 : ((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ = (1 - g).map σ := by
        rw [← Matrix.map_mul, hSP]
      have e3 : (1 - gᵀ) * G * (1 + g.map σ) + (1 + gᵀ) * G * (1 - g.map σ)
          = (G - gᵀ * G * g.map σ) + (G - gᵀ * G * g.map σ) := by noncomm_ring
      calc (1 + g)ᵀ * (((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ)
            * (1 + g).map σ
          = ((1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ) * G * (1 + g).map σ
            + (1 + g)ᵀ * G * (((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (1 - g)ᵀ * G * (1 + g).map σ + (1 + g)ᵀ * G * (1 - g).map σ := by rw [e1, e2]
        _ = 0 := by
            rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
              map_one_add, map_one_sub, e3, hg, sub_self, add_zero]
    · rw [one_add_cayley g hP, Matrix.det_smul]
      exact (h2.pow _).mul (Matrix.isUnit_nonsing_inv_det _ hP)
  · intro g hP
    have hinv : (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = c • (1 + g) :=
      Matrix.inv_eq_right_inv (one_add_cayley_mul g hP c hc)
    rw [hinv, one_sub_cayley g hP, smul_mul_smul_comm, hc, one_smul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
  · intro S hS hP
    have hgP : (1 - S) * (1 + S)⁻¹ * (1 + S) = 1 - S := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [← sub_eq_zero]
    apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + S)ᵀ) ((1 + S).map σ) _
      (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
    have e1 : (1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ = (1 - S)ᵀ := by
      rw [← Matrix.transpose_mul, hgP]
    have e2 : ((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ = (1 - S).map σ := by
      rw [← Matrix.map_mul, hgP]
    have e3 : (1 - Sᵀ) * G * (1 - S.map σ) - (1 + Sᵀ) * G * (1 + S.map σ)
        = -((Sᵀ * G + G * S.map σ) + (Sᵀ * G + G * S.map σ)) := by noncomm_ring
    calc (1 + S)ᵀ * (((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ - G)
          * (1 + S).map σ
        = ((1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ) * G
            * (((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ)
          - (1 + S)ᵀ * G * (1 + S).map σ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (1 - S)ᵀ * G * (1 - S).map σ - (1 + S)ᵀ * G * (1 + S).map σ := by rw [e1, e2]
      _ = 0 := by
          rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
            map_one_add, map_one_sub, e3, hS, add_zero, neg_zero]
  · intro A
    have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hKG : ((G⁻¹).map σ)ᵀ * G = 1 := by
      calc ((G⁻¹).map σ)ᵀ * G = ((G⁻¹).map σ)ᵀ * (G.map σ)ᵀ := by rw [hG]
        _ = (G.map σ * (G⁻¹).map σ)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = 1 := by rw [map_mul_map_inv σ G hGu, Matrix.transpose_one]
    have hGK : G * ((G⁻¹).map σ)ᵀ = 1 := by
      rw [← Matrix.inv_eq_left_inv hKG]
      exact Matrix.mul_nonsing_inv _ hGu
    have hAA : (A.map σ).map σ = A := by
      ext i j
      simp [hσ]
    have hT : (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ = Aᵀ - G * A.map σ * G⁻¹ := by
      rw [Matrix.transpose_sub, Matrix.transpose_transpose]
    have hTs : (A - (G * A.map σ * G⁻¹)ᵀ).map σ
        = A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G) := by
      rw [Matrix.map_sub σ (map_sub σ), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul,
        hAA, Matrix.transpose_mul, Matrix.transpose_mul, hG]
    rw [hT, hTs]
    calc (Aᵀ - G * A.map σ * G⁻¹) * G + G * (A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G))
        = Aᵀ * G - G * A.map σ * (G⁻¹ * G)
          + (G * A.map σ - (G * ((G⁻¹).map σ)ᵀ) * (Aᵀ * G)) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = 0 := by
          rw [hGinvG, hGK, Matrix.mul_one, Matrix.one_mul]
          abel

end GlobalTheory.CayleyInv
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct Pointwise

namespace GlobalTheory.CNorm

theorem galois_places_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], (∀ (τ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (τ y)) ∧ ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → ∃ τ : E ≃ₐ[F] E, ∀ y : E, w'.valuation E y = w.valuation E (τ y) := by
  intro F E _ _ _ _ _ _
  refine ⟨fun σ w => ?_, fun w w' hu => ?_⟩
  · set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he
    have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E) := fun x => rfl
    have hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
      intro a
      apply RingOfIntegers.ext
      rw [hc]
      exact σ.commutes (a : F)
    refine ⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩
    · apply HeightOneSpectrum.ext
      ext a
      change e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal
      rw [hfix]
    · intro y
      exact valuation_of_eq_comap σ.toRingEquiv w _ rfl y
  · haveI := w.isPrime
    haveI := w'.isPrime
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := hu ▸ ⟨rfl⟩
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal
      w'.asIdeal w.asIdeal (E ≃ₐ[F] E)
    refine ⟨σ, fun y => valuation_of_eq_comap σ.toRingEquiv w w' ?_ y⟩
    ext x
    rw [Ideal.mem_comap, ← hσ]
    change _ ↔ σ • x ∈ _
    exact Ideal.smul_mem_pointwise_smul_iff.symm

end GlobalTheory.CNorm
end

end

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.cayleyTransform_unitary_skew_involutive : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  first | exact @GlobalTheory.CayleyInv.cayley_transform | exact GlobalTheory.CayleyInv.cayley_transform | (intros; apply GlobalTheory.CayleyInv.cayley_transform <;> assumption)

end
end
