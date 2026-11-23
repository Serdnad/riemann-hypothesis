module

public import GroundTheory.FunctionField.PlaceDefs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle213
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Mathlib.GroupTheory.GroupAction.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle183
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle184
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.ModEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfPeriodOfDvdSumPowersetCard
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Polynomial

namespace GlobalTheory
open GroundTheory.FunctionField GroundTheory.Arith.SchemeCoh KaehlerDifferential

theorem ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField (A : Type) [CommRing A] [IsDedekindDomain A] (h : ¬ IsField A) : ringKrullDim A = 1 := by
  have hle : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
  have h0 : ringKrullDim A ≠ 0 := fun h0 => h (by
      have : Ring.KrullDimLE 0 A := by
        rw [Ring.krullDimLE_iff, h0]
        rfl
      exact Ring.KrullDimLE.isField_of_isDomain)
  have hnn : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim A = d at hle h0 hnn ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe n =>
    have h1 : n ≤ 1 := by exact_mod_cast hle
    have h2 : n ≠ 0 := by exact_mod_cast h0
    rw [le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h2)]
    rfl

theorem exists_aeval_finite_of_ringKrullDim_eq_one : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A],
    ringKrullDim A = 1 → ∃ t : A, (Polynomial.aeval (R := k) t).Finite := by
  intro k A _ _ _ _ _ hdim
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hs : ringKrullDim A = s := by
    let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
    have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hfin.to_isIntegral x⟩
    have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hg
    rw [GlobalTheory.ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) A,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hs1 : s = 1 := by
    rw [hdim] at hs
    exact_mod_cast hs.symm
  subst hs1
  refine ⟨g (MvPolynomial.X 0), ?_⟩
  let e : k[X] →ₐ[k] MvPolynomial (Fin 1) k := Polynomial.aeval (MvPolynomial.X 0)
  have he : Function.Surjective e := by
    rw [← AlgHom.range_eq_top]
    change (Polynomial.aeval (R := k) (MvPolynomial.X (R := k) (0 : Fin 1))).range = ⊤
    rw [← Algebra.adjoin_singleton_eq_range_aeval, ← MvPolynomial.adjoin_range_X, Set.range_unique]
    rfl
  have hcomp : Polynomial.aeval (R := k) (g (MvPolynomial.X 0)) = g.comp e := by
    apply Polynomial.algHom_ext
    simp [e]
  rw [hcomp]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ he)

theorem aeval_injective_of_finite_of_not_isField : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (y : A),
    (Polynomial.aeval (R := k) y).Finite → ¬ IsField A → Function.Injective (Polynomial.aeval (R := k) y) := by
  intro k A _ _ _ _ y hy hA
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨p, hp, hp0⟩ := hne
  have hyi : IsIntegral k y := (show IsAlgebraic k y from ⟨p, hp0, hp⟩).isIntegral
  set B : Subalgebra k A := (Polynomial.aeval (R := k) y).range with hB
  haveI : Algebra.IsIntegral k B := by
    constructor
    rintro ⟨z, q, rfl⟩
    have : IsIntegral k (Polynomial.aeval y q) := by
      rw [Polynomial.aeval_eq_sum_range]
      refine IsIntegral.sum _ fun i _ => ?_
      exact (hyi.pow i).smul _
    exact (isIntegral_algHom_iff B.val Subtype.val_injective).1 this
  haveI : Algebra.IsIntegral k A := by
    constructor
    intro x
    have hx : (Polynomial.aeval (R := k) y).toRingHom.IsIntegralElem x := hy.to_isIntegral x
    obtain ⟨f, hfm, hf⟩ := hx
    let φ : k[X] →+* B := (Polynomial.aeval (R := k) y).rangeRestrict.toRingHom
    have hxB : IsIntegral B x := by
      refine ⟨f.map φ, hfm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have e : (algebraMap B A).comp φ = (Polynomial.aeval (R := k) y).toRingHom := RingHom.ext fun q => rfl
      rw [e]
      exact hf
    exact isIntegral_trans x hxB
  exact hA ((Algebra.IsIntegral.isField_iff_isField (algebraMap k A).injective).1 (Field.toIsField k))

theorem exists_D_algebraMap_fractionRing_ne_zero : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [IsFunctionField k (FractionRing A)],
    ∃ a : A, D k (FractionRing A) (algebraMap A (FractionRing A) a) ≠ 0 := by
  intro k A _ _ _ _ _
  have hnt := kaehlerDifferential_nontrivial (k := k) (K := FractionRing A)
  by_contra h
  push_neg at h
  have hall : ∀ x : FractionRing A, D k (FractionRing A) x = 0 := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, h a, h b]
    simp
  have htop : (⊤ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[FractionRing A⁄k])
  have hmem : ω ∈ (⊥ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) := htop ▸ Submodule.mem_top
  exact hω ((Submodule.mem_bot _).1 hmem)

theorem isFunctionField_fractionRing_of_ringKrullDim_eq_one (k A : Type) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hR : ringKrullDim A = 1) :
    IsFunctionField k (FractionRing A) := by
  have htrA : Algebra.trdeg k A = 1 := by
    obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    have hs := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_of_normalization k g hg hfin.to_isIntegral
    rw [hR] at hs
    have hs1 : s = 1 := by exact_mod_cast hs.symm
    subst hs1
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_normalization k g hg hfin.to_isIntegral]
    simp
  have htr : Algebra.trdeg k (FractionRing A) = 1 := by
    have : FaithfulSMul A (FractionRing A) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A _)
    have : Algebra.IsAlgebraic A (FractionRing A) :=
      IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := FractionRing A), htrA, trdeg_eq_zero (R := A) (A := FractionRing A),
      add_zero]
  have : Algebra.Transcendental k (FractionRing A) := by
    rw [← trdeg_ne_zero_iff, htr]
    exact one_ne_zero
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := FractionRing A)
  refine ⟨x, hx, ?_⟩
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set (FractionRing A)) → FractionRing A) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set (FractionRing A)))).2 hx)
      (by rw [htr, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType A (FractionRing A) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing A) (nonZeroDivisors A)
  have : Algebra.EssFiniteType k (FractionRing A) := Algebra.EssFiniteType.comp k A (FractionRing A)
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) (FractionRing A) :=
    Algebra.EssFiniteType.of_comp k _ (FractionRing A)
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem exists_separable_normalisation_reduced_fibres : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], ¬ IsField A → ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧ ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  intro k A _ _ _ _ _ _ hA
  have hdim : ringKrullDim A = 1 := ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField A hA
  haveI : IsFunctionField k (FractionRing A) :=
    isFunctionField_fractionRing_of_ringKrullDim_eq_one k A hdim
  obtain ⟨t, ht⟩ := exists_aeval_finite_of_ringKrullDim_eq_one k A hdim
  obtain ⟨a, ha⟩ := exists_D_algebraMap_fractionRing_ne_zero k A
  have key : ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧
      D k (FractionRing A) (algebraMap A (FractionRing A) y) ≠ 0 := by
    by_cases hD : D k (FractionRing A) (algebraMap A (FractionRing A) t) = 0
    · obtain ⟨M, hM⟩ := GlobalTheory.T.noether_normalization_finite_aeval_pow_add k A t a ht
      refine ⟨t ^ M + a, hM, ?_⟩
      rw [map_add (f := _), map_pow, map_add (f := _), Derivation.leibniz_pow, hD, smul_zero, smul_zero, zero_add]
      exact ha
    · exact ⟨t, ht, hD⟩
  obtain ⟨y, hy, hDy⟩ := key
  haveI := isSeparable_of_D_ne_zero hDy
  exact ⟨y, hy, GlobalTheory.T.reduced_fibres_almost_all_of_separable_dedekind_curve k A y hy (aeval_injective_of_finite_of_not_isField k A y hy hA) this⟩

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem exists_embeddings_agree_on_subfield_ne (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω]
    [CharZero L] (a : Ω) (ha : a ∉ Set.range (algebraMap L Ω)) :
    ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F),
      i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  haveI hred : IsReduced (Ω ⊗[L] Ω) := GlobalTheory.ReducedAlg.isReduced_tensor (k := L) Ω Ω
  have he : (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) ≠ 0 := by
    intro h
    have h1 : (a ⊗ₜ[L] (1 : Ω) : Ω ⊗[L] Ω) = (1 : Ω) ⊗ₜ[L] a := sub_eq_zero.mp h
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L Ω, φ 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff L (1 : Ω)).mp hc)
    have h2 := congrArg (fun x => TensorProduct.rid L Ω (LinearMap.lTensor Ω φ x)) h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h2
    apply ha
    refine ⟨(φ 1)⁻¹ * φ a, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  have hn : ¬ IsNilpotent (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) :=
    fun h => he h.eq_zero
  rw [nilpotent_iff_mem_prime] at hn
  push_neg at hn
  obtain ⟨J, hJ, heJ⟩ := hn
  haveI := hJ
  let g : (Ω ⊗[L] Ω) →+* FractionRing ((Ω ⊗[L] Ω) ⧸ J) :=
    (algebraMap ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J))).comp (Ideal.Quotient.mk J)
  refine ⟨FractionRing ((Ω ⊗[L] Ω) ⧸ J), inferInstance,
    g.comp (Algebra.TensorProduct.includeLeftRingHom),
    g.comp (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := Ω)).toRingHom, ?_, ?_⟩
  · ext l
    simp only [RingHom.comp_apply]
    congr 1
    show (algebraMap L Ω l) ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] (algebraMap L Ω l)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · intro h
    apply heJ
    have h3 : g (a ⊗ₜ[L] (1 : Ω)) = g ((1 : Ω) ⊗ₜ[L] a) := h
    have h4 := IsFractionRing.injective ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J)) h3
    exact Ideal.Quotient.eq.mp h4

end GlobalTheory
end

section

open GlobalTheory.Nef

namespace GlobalTheory

theorem exists_ne_zero_comb_mem_ker :
    ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  intro k F ι _ _ _ n m f hf S N ψ hlt
  let T : (Fin n → Fin m → k) →ₗ[k] (Fin n → F) :=
    { toFun := fun c i => ∑ j, c i j • f j
      map_add' := by
        intro a b; funext i; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext i; simp [Finset.smul_sum, smul_smul] }
  have hT : ∀ c, T c = fun i => ∑ j, c i j • f j := fun c => rfl
  let Ψ : (Fin n → Fin m → k) →ₗ[k] ((v : S) → Fin (N v) → k) :=
    LinearMap.pi fun v => (ψ v).comp T
  have hlt' : Module.finrank k ((v : S) → Fin (N v) → k) < Module.finrank k (Fin n → Fin m → k) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun]
    rw [Finset.sum_coe_sort S (fun v => N v), Module.finrank_pi_fintype]
    simpa [Module.finrank_fin_fun] using hlt
  have hk : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt'
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hk
  refine ⟨c, ?_, ?_⟩
  · intro h0
    apply hc0
    funext i j
    have hi : ∑ j, c i j • f j = 0 := congrFun h0 i
    exact Fintype.linearIndependent_iff.1 hf (c i) hi j
  · intro v hv
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨v, hv⟩
    simpa [Ψ, hT] using this

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ f ∈ V, rd f ∈ R) → (∀ f ∈ V', rd f ∈ R) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h h' : B, h ∈ R → h' ∈ R → h * h' = 1 → (∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A))) → ∀ T : V →ₗ[K] V', T ≠ 0 → (∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  first | exact @GlobalTheory.commuting_multiplier_eq_const_smul_generator | exact GlobalTheory.commuting_multiplier_eq_const_smul_generator | (intros; apply GlobalTheory.commuting_multiplier_eq_const_smul_generator <;> assumption)
end

section


theorem _root_.GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S), ψ h ≠ 0 → ∀ T : Set F, (∀ x ∈ T, (h : F) * x ∈ S) → Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first | exact @GlobalTheory.adjoin_hom_extend_of_denominator | exact GlobalTheory.adjoin_hom_extend_of_denominator | (intros; apply GlobalTheory.adjoin_hom_extend_of_denominator <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem ker_retraction_fg : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  intro D T E _ _ _ _ _ ι F hF χ hχ
  have hχι : ∀ t, χ (ι t) = t := fun t => by simpa using DFunLike.congr_fun hχ t
  set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ
  have key : ∀ x, x - ι (χ x) ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E)) := by rw [hF]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | hx
      · simp [hχι]
      · exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp [AlgHom.commutes]
    | add x y _ _ hx hy =>
      have e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y)) := by
        simp only [map_add (f := _)]; ring
      rw [e]; exact J.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y)) := by
        simp only [map_mul]; ring
      rw [e]; exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  have hker : RingHom.ker χ = J := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simpa [hx] using key x
    · rw [hJ, Ideal.span_le]
      rintro _ ⟨f, _, rfl⟩
      simp [RingHom.mem_ker, hχι]
  rw [hker]
  classical
  exact ⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem finite_retractions_of_adjoin_finset_integral
    (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
    [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) :
    {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  classical
  choose p hpm hp0 using fun x : E => (Algebra.IsIntegral.isIntegral (R := D) x)
  have hfin : (Set.pi Set.univ fun f : F =>
      ((((p f.1).map (algebraMap D T)).roots.toFinset : Finset T) : Set T)).Finite :=
    Set.Finite.pi (fun f => Finset.finite_toSet _)
  refine Set.Finite.of_finite_image (f := fun χ : E →ₐ[D] T => fun f : F => χ f.1)
    (hfin.subset ?_) ?_
  · rintro _ ⟨χ, _, rfl⟩
    refine Set.mem_univ_pi.2 fun f => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm f.1).map (algebraMap D T)).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hp0, map_zero]
  · intro χ₁ h₁ χ₂ h₂ he
    apply AlgHom.ext_of_adjoin_eq_top hF
    rintro x (⟨t, rfl⟩ | hx)
    · have e₁ := AlgHom.congr_fun (show χ₁.comp ι = AlgHom.id D T from h₁) t
      have e₂ := AlgHom.congr_fun (show χ₂.comp ι = AlgHom.id D T from h₂) t
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
      rw [e₁, e₂]
    · exact congrFun he ⟨x, hx⟩

theorem finite_retractions_of_adjoin_finset_integral' :
    ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
      [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E),
      Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ →
        {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite :=
  fun D T E _ _ _ _ _ _ _ _ ι F hF => finite_retractions_of_adjoin_finset_integral D T E ι F hF

end GlobalTheory
end

section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_residue_idempotent' : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] [Nontrivial Λ], ∃ x : Λ, x * x - x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) ∧ (∀ y : Λ, ∃ c : A, x * y * x - c • x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) ∧ ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * x * b i - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (exact GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (intros; apply GlobalTheory.AzumayaResidue.exists_residue_idempotent  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finsum_orbitRel_fibred_equivariant : ∀ {H X B E : Type} [Group H] [MulAction H X] [MulAction H B] [MulAction H E] (π : X → B), (∀ (h : H) (x : X), π (h • x) = h • π x) → ∀ (S : B → Subgroup H), (∀ b : B, MulAction.stabilizer H b ≤ S b) → ∀ (j : B → E → X), (∀ b : B, Function.Injective (j b)) → (∀ (b : B) (e : E), π (j b e) = b) → (∀ (b : B) (x : X), π x = b → ∃ e : E, j b e = x) → (∀ (b : B), ∀ h ∈ S b, ∀ e : E, j b (h • e) = h • j b e) → ∀ (s : MulAction.orbitRel.Quotient H B → B), (∀ q, Quotient.mk (MulAction.orbitRel H B) (s q) = q) → ∀ (g : MulAction.orbitRel.Quotient H X → ℂ), (Function.support g).Finite → ∑ᶠ o, g o = ∑ᶠ q, ∑ᶠ o' : MulAction.orbitRel.Quotient (S (s q)) E, g (Quotient.mk (MulAction.orbitRel H X) (j (s q) (Quotient.out o'))) := by
  first | exact @GlobalTheory.finsum_orbitRel_fibred | exact GlobalTheory.finsum_orbitRel_fibred | (intros; apply GlobalTheory.finsum_orbitRel_fibred <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass : ∀ {K Z : Type} [Group K] [Finite K] [MulAction K Z] (f : Z → ℂ), (∀ (k : K) (z : Z), f (k • z) = f z) → (Function.support f).Finite → ∑ᶠ o : MulAction.orbitRel.Quotient K Z, ((Nat.card (MulAction.stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * f (Quotient.out o) = ((Nat.card K : ℕ) : ℂ)⁻¹ * ∑ᶠ z, f z := by
  first | exact @GlobalTheory.finsum_orbits_stabilizer_mass | exact GlobalTheory.finsum_orbits_stabilizer_mass | (intros; apply GlobalTheory.finsum_orbits_stabilizer_mass <;> assumption)
end

section


theorem _root_.GlobalTheory.T.dvd_of_period_of_dvd_sum_powersetCard' : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → (∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i)) → ∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l := by
  first | exact @GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | exact GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | (intros; apply GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.polynomial_system_eventually_solvable_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  first | (exact @GlobalTheory.TorsorColim.poly_eventually_solvable) | (exact GlobalTheory.TorsorColim.poly_eventually_solvable) | (intros; apply GlobalTheory.TorsorColim.poly_eventually_solvable  <;> assumption)
end
