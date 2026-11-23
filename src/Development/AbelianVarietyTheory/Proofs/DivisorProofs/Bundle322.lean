module

public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Mathlib.RingTheory.Trace.Defs
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.Algebra.Module.SpanRankOperations
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Trace.Basic
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle001
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.UnramPushout

open TensorProduct

theorem isReduced_nontrivial_tensor {A k k' : Type} [CommRing A] [Field k] [Field k']
    [Algebra A k] [Algebra A k'] [CharZero k] (P : Ideal A) [P.IsPrime]
    (hk : RingHom.ker (algebraMap A k) = P) (hk' : RingHom.ker (algebraMap A k') = P) :
    IsReduced (k ⊗[A] k') ∧ Nontrivial (k ⊗[A] k') := by
  have hu : ∀ {L : Type} [Field L] [Algebra A L], RingHom.ker (algebraMap A L) = P →
      P.primeCompl ≤ (IsUnit.submonoid L).comap (algebraMap A L) := by
    intro L _ _ h s hs
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hs (h ▸ (RingHom.mem_ker.mpr h0))
  let ι := Ideal.ResidueField.lift P (algebraMap A k) hk.ge (hu hk)
  let ι' := Ideal.ResidueField.lift P (algebraMap A k') hk'.ge (hu hk')
  letI : Algebra P.ResidueField k := ι.toAlgebra
  letI : Algebra P.ResidueField k' := ι'.toAlgebra
  haveI : IsScalarTower A P.ResidueField k :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap P _ _ _ r).symm
  haveI : IsScalarTower A P.ResidueField k' :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap P _ _ _ r).symm
  haveI : CharZero P.ResidueField := ⟨fun m n h => Nat.cast_injective (R := k) (by rw [← map_natCast ι, ← map_natCast ι, h])⟩
  haveI : CompatibleSMul A P.ResidueField k k' := by
    refine ⟨fun x m n => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A ⧸ P) x
    have hβ := map_ne_zero_of_mem_nonZeroDivisors _ P.injective_algebraMap_quotient_residueField hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [Ideal.algebraMap_quotient_residueField_mk] at hβ ⊢
    set β := algebraMap A P.ResidueField b
    set α := algebraMap A P.ResidueField a
    have e1 : n = b • (β⁻¹ • n) := by
      rw [← algebraMap_smul P.ResidueField b, smul_smul, mul_inv_cancel₀ hβ, one_smul]
    have e2 : b • ((α / β) • m) = a • m := by
      rw [← algebraMap_smul P.ResidueField b, ← algebraMap_smul P.ResidueField a, smul_smul,
        mul_div_cancel₀ _ hβ]
    have e3 : a • (β⁻¹ • n) = (α / β) • n := by
      rw [← algebraMap_smul P.ResidueField a, smul_smul, div_eq_mul_inv]
    conv_lhs => rw [e1]
    rw [← smul_tmul b ((α / β) • m) (β⁻¹ • n), e2, smul_tmul a m (β⁻¹ • n), e3]
  let e := Algebra.TensorProduct.equivOfCompatibleSMul P.ResidueField A A k k'
  have : IsReduced (k ⊗[P.ResidueField] k') := GlobalTheory.ReducedAlg.isReduced_tensor k k'
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.toEquiv.nontrivial⟩

theorem exists_local_pushout (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V]
    [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V') (hf' : f'.Flat)
    (hP : (maximalIdeal V).comap f = (maximalIdeal V').comap f')
    (hV : ((maximalIdeal V).comap f).map f = maximalIdeal V)
    (hV' : ((maximalIdeal V').comap f').map f' = maximalIdeal V')
    (h0 : CharZero (ResidueField V)) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B),
      g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧
        (maximalIdeal V').map g' = maximalIdeal B := by
  letI : Algebra A V := f.toAlgebra
  letI : Algebra A V' := f'.toAlgebra
  haveI : Module.Flat A V' := hf'
  set P := (maximalIdeal V).comap f with hPdef
  let C := V ⊗[A] V'
  let φ : C →ₐ[A] ResidueField V ⊗[A] ResidueField V' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A V (ResidueField V))
      (IsScalarTower.toAlgHom A V' (ResidueField V'))
  set Q := P.map (algebraMap A C) with hQ
  have hL : (maximalIdeal V).map (Algebra.TensorProduct.includeLeft : V →ₐ[A] C) = Q := by
    rw [← hV, hQ, AlgHom.coe_ideal_map, Ideal.map_map]
    congr 1
  have hR : (maximalIdeal V').map (Algebra.TensorProduct.includeRight : V' →ₐ[A] C) = Q := by
    rw [← hV', ← hP, hQ, AlgHom.coe_ideal_map, Ideal.map_map]
    congr 1
    ext a
    exact (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := V')).commutes a
  have hker : RingHom.ker φ = Q := by
    have e1 : RingHom.ker (IsScalarTower.toAlgHom A V (ResidueField V)) = maximalIdeal V :=
      ker_residue
    have e2 : RingHom.ker (IsScalarTower.toAlgHom A V' (ResidueField V')) = maximalIdeal V' :=
      ker_residue
    rw [Algebra.TensorProduct.map_ker _ _ residue_surjective residue_surjective, e1, e2, hL, hR,
      sup_idem]
  have hk : RingHom.ker (algebraMap A (ResidueField V)) = P := by
    ext a
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A V (ResidueField V),
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
    rfl
  have hk' : RingHom.ker (algebraMap A (ResidueField V')) = P := by
    rw [hP]
    ext a
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A V' (ResidueField V'),
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
    rfl
  obtain ⟨hred, hnt⟩ :=
    isReduced_nontrivial_tensor (k := ResidueField V) (k' := ResidueField V') P hk hk'
  have hrad : Q.IsRadical := by
    rintro x ⟨n, hn⟩
    rw [← hker, RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsNilpotent.eq_zero ⟨n, hn⟩
  have hne : Q ≠ ⊤ := by
    intro h
    have h1 : (1 : C) ∈ RingHom.ker φ := by rw [hker, h]; exact Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hm.isPrime
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : q.IsPrime := hq.1.1
  let B := Localization.AtPrime q
  have hmax : Q.map (algebraMap C B) = maximalIdeal B := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes B q Q hq
    rw [← IsLocalization.map_radical q.primeCompl B, hrad.radical,
      Localization.AtPrime.map_eq_maximalIdeal] at h1
    exact h1
  let g : V →+* B := (algebraMap C B).comp
    ((Algebra.TensorProduct.includeLeft : V →ₐ[A] C) : V →+* C)
  let g' : V' →+* B := (algebraMap C B).comp
    ((Algebra.TensorProduct.includeRight : V' →ₐ[A] C) : V' →+* C)
  have hgf : g.comp f = (algebraMap C B).comp (algebraMap A C) := by
    ext a
    exact congrArg (algebraMap C B)
      ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := V) (B := V')).commutes a)
  have hgf' : g'.comp f' = (algebraMap C B).comp (algebraMap A C) := by
    ext a
    exact congrArg (algebraMap C B)
      ((Algebra.TensorProduct.includeRight (R := A) (A := V) (B := V')).commutes a)
  rw [AlgHom.coe_ideal_map] at hL hR
  refine ⟨B, inferInstance, inferInstance, g, g', hgf.trans hgf'.symm, ?_, ?_, ?_⟩
  · have h1 : (algebraMap C B).Flat :=
      RingHom.flat_algebraMap_iff.2 (IsLocalization.flat B q.primeCompl)
    have h2 : (algebraMap V C).Flat := RingHom.flat_algebraMap_iff.2 (Module.Flat.baseChange A V V')
    exact RingHom.Flat.comp h2 h1
  · rw [← Ideal.map_map, hL, hmax]
  · rw [← Ideal.map_map, hR, hmax]

end GlobalTheory.UnramPushout
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem semilinear_pow_smul {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V]
    [Module F' V] [Module F V] (s : F' ≃ₐ[F] F') (T : Module.End F V)
    (hT : ∀ (c : F') (v : V), T (c • v) = s c • T v) (m : ℕ) (c : F') (v : V) :
    (T ^ m) (c • v) = (s ^ m) c • (T ^ m) v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih, hT, AlgEquiv.mul_apply, Module.End.mul_apply]

theorem pow_apply_of_mem_ker_sub_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (u : V) (hu : u ∈ LinearMap.ker (T - 1)) (m : ℕ) : (T ^ m) u = u := by
  have h1 : T u = u := by
    have h := LinearMap.mem_ker.mp hu
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, h1, ih]

theorem algebraMap_trace_eq_sum_pow {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    algebraMap F F' (Algebra.trace F F' x) = ∑ j : Fin (Module.finrank F F'), (s ^ (j : ℕ)) x := by
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  rw [trace_eq_sum_automorphisms]
  have hord : orderOf s = Module.finrank F F' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) := by
    intro i j hij
    simp only at hij
    rw [pow_inj_mod, hord, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hij
    exact Fin.ext hij
  have hbij : Function.Bijective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]⟩
  exact (Fintype.sum_bijective _ hbij _ _ (fun j => rfl)).symm

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem galoisDescent_semilinear_bijective : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (V : Type) [AddCommGroup V] [Module F' V] [Module F V] [IsScalarTower F F' V] (T : Module.End F V), (∀ (c : F') (v : V), T (c • v) = s c • T v) → T ^ Module.finrank F F' = 1 → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι F F'), Function.Bijective (fun v : ι → LinearMap.ker (T - 1) => ∑ i, b i • (v i : V)) := by
  intro F F' _ _ _ _ s hs V _ _ _ _ T hT hTn ι _ b
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  set n := Module.finrank F F' with hn
  have hnd := traceForm_nondegenerate F F'
  set d := (Algebra.traceForm F F').dualBasis hnd b with hd
  have hdb : ∀ i j, Algebra.trace F F' (d i * b j) = if j = i then 1 else 0 := fun i j => by
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd b i j
    simpa [Algebra.traceForm_apply] using h
  have key1 : ∀ i j, ∑ k : Fin n, (s ^ (k : ℕ)) (d i) * (s ^ (k : ℕ)) (b j) =
      if i = j then 1 else 0 := by
    intro i j
    have h := algebraMap_trace_eq_sum_pow s hs (d i * b j)
    simp only [map_mul] at h
    rw [← h, hdb]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hTk : ∀ (k : ℕ) (c : F') (v : V), (T ^ k) (c • v) = (s ^ k) c • (T ^ k) v :=
    semilinear_pow_smul s T hT
  have hfix : ∀ (u : LinearMap.ker (T - 1)) (k : ℕ), (T ^ k) (u : V) = u :=
    fun u k => pow_apply_of_mem_ker_sub_one T u u.2 k
  have hn0 : 0 < n := Module.finrank_pos
  have hcard : Fintype.card ι = n := (Module.finrank_eq_card_basis b).symm
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let A : Matrix (Fin n) ι F' := fun k j => (s ^ (k : ℕ)) (b j)
  let B : Matrix ι (Fin n) F' := fun i k => (s ^ (k : ℕ)) (d i)
  have hBA : B * A = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact key1 i j
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mpr hBA
  let k0 : Fin n := ⟨0, hn0⟩
  have key2 : ∀ l : Fin n, ∑ i, b i * (s ^ (l : ℕ)) (d i) = if k0 = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hAB k0) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [A, B, k0] using h
  constructor
  · intro v w hvw
    simp only at hvw
    have hk : ∀ k : ℕ, ∑ i, (s ^ k) (b i) • (v i : V) = ∑ i, (s ^ k) (b i) • (w i : V) := by
      intro k
      have h := congrArg (T ^ k) hvw

      simpa only [map_sum, hTk, hfix] using h
    have expand : ∀ (u : ι → LinearMap.ker (T - 1)) (j : ι), (u j : V) =
        ∑ k : Fin n, (s ^ (k : ℕ)) (d j) • ∑ i, (s ^ (k : ℕ)) (b i) • (u i : V) := by
      intro u j
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key1]
      simp [ite_smul]
    funext j
    apply Subtype.ext
    rw [expand v j, expand w j]
    simp_rw [hk]
  · intro w
    let Q : V → V := fun u => ∑ k : Fin n, (T ^ (k : ℕ)) u
    have hQ : ∀ u, Q u ∈ LinearMap.ker (T - 1) := by
      intro u
      simp only [Q]

      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, map_sum]
      rw [Fin.sum_univ_eq_sum_range (fun k => T ((T ^ k) u)),
        Fin.sum_univ_eq_sum_range (fun k => (T ^ k) u)]
      have hs1 : ∀ k : ℕ, T ((T ^ k) u) = (T ^ (k + 1)) u := fun k => by
        rw [pow_succ', Module.End.mul_apply]
      simp_rw [hs1]
      have h1 := Finset.sum_range_succ' (fun k => (T ^ k) u) n
      have h2 := Finset.sum_range_succ (fun k => (T ^ k) u) n
      rw [h2, hTn, pow_zero] at h1
      exact (add_right_cancel h1).symm
    refine ⟨fun i => ⟨Q (d i • w), hQ _⟩, ?_⟩
    simp only [Q, hTk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, key2]
    simp [ite_smul, k0]

end GlobalTheory.Shin
end

section

open IsLocalRing RingTheory.Sequence Pointwise

namespace GlobalTheory.AnnRegSeq

theorem free_of_maximalIdeal_eq_bot {B M : Type} [CommRing B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] (hm : maximalIdeal B = ⊥) : Module.Free B M := by
  have hF : IsField B := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  letI := hF.toField
  exact Module.Free.of_divisionRing B M

theorem maximalIdeal_eq_bot_of_le_sq {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (h : maximalIdeal B ≤ maximalIdeal B ^ 2) : maximalIdeal B = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) (maximalIdeal B)
    (maximalIdeal B).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two])
    (maximalIdeal_le_jacobson ⊥)

theorem exists_isSMulRegular_notMem_sq {B M : Type} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hass : maximalIdeal B ∉ associatedPrimes B M) (hsq : ¬ maximalIdeal B ≤ maximalIdeal B ^ 2) :
    ∃ x ∈ maximalIdeal B, x ∉ maximalIdeal B ^ 2 ∧ IsSMulRegular M x := by
  by_contra hcon
  push_neg at hcon
  have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ p ∈ insert (maximalIdeal B ^ 2) (associatedPrimes B M), (id p : Set B) := by
    intro z hz
    rw [Set.biUnion_insert]
    by_cases h2 : z ∈ maximalIdeal B ^ 2
    · exact Or.inl h2
    · right
      have : z ∈ ({r : B | IsSMulRegular M r}ᶜ) := hcon z hz h2
      rwa [← biUnion_associatedPrimes_eq_compl_regular B M] at this
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite ((associatedPrimes.finite B M).insert _)
    (f := id) (maximalIdeal B ^ 2) (maximalIdeal B ^ 2) (fun i hi h1 _ => by
      rcases hi with rfl | hi
      · exact absurd rfl h1
      · exact hi.isPrime)).mp hsub
  rcases hp with rfl | hp
  · exact hsq hle
  · have : p = maximalIdeal B := le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle
    exact hass (this ▸ hp)

theorem free_of_free_quotient {B M : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] {x : B} (hx : x ∈ maximalIdeal B)
    (reg : IsSMulRegular M x)
    [Module.Free (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M))] :
    Module.Free B M := by
  set I : Ideal B := Ideal.span {x} with hI
  set P : Submodule B M := I • ⊤ with hP
  have hIj : I ≤ (⊥ : Ideal B).jacobson := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact maximalIdeal_le_jacobson _ hx
  haveI : IsLocalRing (B ⧸ I) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
  haveI : Module.Finite (B ⧸ I) (M ⧸ P) := Module.Finite.of_restrictScalars_finite B _ _
  let b := Module.finBasis (B ⧸ I) (M ⧸ P)
  set r := Module.finrank (B ⧸ I) (M ⧸ P)
  choose v hv using fun i => Submodule.Quotient.mk_surjective P (b i)
  let φ : (Fin r → B) →ₗ[B] M := Fintype.linearCombination B v
  have hφ : ∀ c, φ c = ∑ i, c i • v i := fun c => by simp [φ, Fintype.linearCombination_apply]
  have hmk : ∀ c : Fin r → B, (Submodule.Quotient.mk (φ c) : M ⧸ P) =
      ∑ i, Ideal.Quotient.mk I (c i) • b i := by
    intro c
    rw [hφ]
    change Submodule.mkQ P (∑ i, c i • v i) = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hsurj : LinearMap.range φ = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIj ?_)
    intro m _
    choose c' hc' using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk m) i)
    have h1 : (Submodule.Quotient.mk (φ c') : M ⧸ P) = Submodule.Quotient.mk m := by
      rw [hmk]
      simp only [hc']
      exact b.sum_repr _
    rw [Submodule.Quotient.eq] at h1
    have h2 : m = φ c' - (φ c' - m) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨c', rfl⟩) (Submodule.mem_sup_right h1)
  have hker : LinearMap.ker φ = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_ hIj
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have h0 : ∑ i, Ideal.Quotient.mk I (k i) • b i = 0 := by
      rw [← hmk, hk]
      rfl
    have hki : ∀ i, k i ∈ I := fun i =>
      Ideal.Quotient.eq_zero_iff_mem.mp ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0 i)
    choose k' hk' using fun i => Ideal.mem_span_singleton'.mp (hki i)
    have hkx : k = x • k' := by
      ext i
      simp [← hk' i, mul_comm]
    have hk'ker : k' ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply reg
      show x • φ k' = x • 0
      rw [smul_zero, ← map_smul, ← hkx, hk]
    rw [hkx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hk'ker
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hsurj⟩)

theorem free_of_modDepthGE (n : ℕ) : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M],
    ReciprocityTheory.CA.ModDepthGE B M n → (maximalIdeal B).spanFinrank ≤ n → Module.Free B M := by
  induction n with
  | zero =>
    intro B _ _ _ M _ _ _ _ hsp
    exact free_of_maximalIdeal_eq_bot ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal B).fg_of_isNoetherianRing).mp (by omega))
  | succ n ih =>
    intro B _ _ _ M _ _ _ hd hsp
    by_cases hsq : maximalIdeal B ≤ maximalIdeal B ^ 2
    · exact free_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_le_sq hsq)
    obtain ⟨rs, hlen, hmem, hreg⟩ := hd
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hy : y ∈ maximalIdeal B := hmem y (by simp)
    have hass := ReciprocityTheory.CA.max_not_mem_ass_of_reg hy ((isRegular_cons_iff M y ys).mp hreg).1
    obtain ⟨x, hx, hx2, hxreg⟩ := exists_isSMulRegular_notMem_sq hass hsq
    have hd' := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hx hxreg ⟨y :: ys, hlen, hmem, hreg⟩
    haveI : IsLocalRing (B ⧸ Ideal.span {x}) :=
      ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
    haveI : Module.Finite (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) :=
      Module.Finite.of_restrictScalars_finite B _ _
    have hsp' : (maximalIdeal (B ⧸ Ideal.span {x})).spanFinrank ≤ n := by
      have h1 :=
        ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le B hx hx2
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1
      omega
    have hd'' : ReciprocityTheory.CA.ModDepthGE (B ⧸ Ideal.span {x})
        (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) n := by
      obtain ⟨zs, hzl, hzm, hzr⟩ := hd'
      let e : QuotSMulTop x M ≃ₗ[B] M ⧸ Ideal.span {x} • (⊤ : Submodule B M) :=
        Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm
      refine ⟨zs.map (Ideal.Quotient.mk _), by simp [hzl], ?_, ?_⟩
      · intro r hr
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
        exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hzm z hz)
      · rw [← Ideal.Quotient.algebraMap_eq]
        exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' zs).mpr ((e.isRegular_congr zs).mp hzr)
    haveI := ih (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) hd'' hsp'
    exact free_of_free_quotient hx hxreg

end GlobalTheory.AnnRegSeq
end

section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two : ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  first | exact @GlobalTheory.continuousOn_cHess_of_contDiffOn_two | exact GlobalTheory.continuousOn_cHess_of_contDiffOn_two | (intros; apply GlobalTheory.continuousOn_cHess_of_contDiffOn_two <;> assumption)
end
