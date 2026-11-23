module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle002
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle873
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianCompletionSupIdealSmulEq
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt (f g : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) =
      _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← add_smul, show (fun z ↦ f z + g z) = f + g from rfl,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, ContinuousMultilinearMap.add_apply, mul_add]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_const_fun (c : ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => ?_]
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_congr_germ (f g : (I → ℂ) → ℂ) (h : f =ᶠ[𝓝 0] g) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span (f : (I → ℂ) → ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t) := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ']
  have h0 : ∑ s : Fin 0 → I, ((↑(Nat.factorial 0))⁻¹ * (iteratedFDeriv ℂ 0 f 0)
      fun a ↦ Pi.single (s a) 1) • ∏ a, t (s a) = algebraMap ℂ D (f 0) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h0, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun s _ => ?_
  rw [Algebra.smul_def, Fin.prod_univ_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s 0, rfl⟩))

end


set_option autoImplicit false in
open Filter Topology in
theorem _root_.GlobalTheory.PeriodFamily.taylor_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • _root_.GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (_root_.GlobalTheory.PeriodFamily.taylor N t f) = _root_.GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  intro I _ _ D _ _ N t
  refine ⟨fun f g hf hg => _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t f g hf hg,
    fun c f hf => ?_, _root_.GlobalTheory.PeriodFamily.taylor_const_fun N t,
    _root_.GlobalTheory.PeriodFamily.taylor_congr_germ N t, fun D' _ _ ψ f => ?_,
    _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t⟩
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show (fun z ↦ c * f z) = fun z ↦ c • f z from rfl,
      iteratedFDeriv_const_smul_apply' hf.contDiffAt, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul, smul_smul, mul_left_comm]
  · unfold _root_.GlobalTheory.PeriodFamily.taylor

    simp [map_sum, map_prod]

end GlobalTheory.PeriodFamily
end

section

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem sum_words_eq_sum_multinomial {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [AddCommGroup D] [Module ℂ D] (k : ℕ) (G : (I →₀ ℕ) → D) :
    ∑ s : Fin k → I, G (∑ a, Finsupp.single (s a) 1) =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • G m := by
  let ℓ : MvPolynomial I ℂ →ₗ[ℂ] D := (MvPolynomial.basisMonomials I ℂ).constr ℂ G
  have hℓ : ∀ m, ℓ (MvPolynomial.monomial m 1) = G m := fun m => by
    have := (MvPolynomial.basisMonomials I ℂ).constr_basis ℂ G m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h1 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ s : Fin k → I, MvPolynomial.monomial (∑ a, Finsupp.single (s a) 1) 1 := by
    rw [Fintype.sum_pow]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.monomial_sum_one]
    rfl
  have h2 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • MvPolynomial.monomial m 1 := by
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    symm
    refine Finset.sum_nbij' (fun m => (m : I → ℕ)) (fun m => Finsupp.equivFunOnFinite.symm m)
      ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simpa using hm
    · intro m hm
      simpa using hm
    · intro m _
      simp
    · intro m _
      simp
    · intro m _
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Nat.cast_smul_eq_nsmul,
        nsmul_eq_mul]
      simp
  have h := congrArg ℓ (h1.symm.trans h2)

  simpa only [map_sum, map_smul, hℓ] using h

theorem iteratedFDeriv_word_eq_coeff {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (s : Fin k → I) :
    iteratedFDeriv ℂ k f 0 (fun a => Pi.single (s a) 1) =
      ((∏ i, ((∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i).factorial : ℕ) : ℂ) *
        MvPowerSeries.coeff (∑ a, Finsupp.single (s a) 1) (GlobalTheory.taylor f) := by
  have hl : ((List.ofFn s : List I) : Multiset I) =
      Finsupp.toMultiset (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) := by

    rw [map_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [← Fin.univ_val_map, Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Multiset.map s _),
      Multiset.map_map]
    rfl
  rw [GlobalTheory.taylor_eq_taylorDir, GlobalTheory.coeff_taylorDir_eq_lineDerivList _ hf hl, List.map_ofFn,
    GlobalTheory.lineDerivList_ofFn hf, mul_inv_cancel_left₀ (GlobalTheory.cast_prod_factorial_ne_zero _)]
  rfl

theorem taylor_eq_sum_coeff_taylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 →
    GlobalTheory.PeriodFamily.taylor N t f = ∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m (GlobalTheory.taylor f) • ∏ i, t i ^ m i := by
  intro I _ _ D _ _ N t f hf
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => ?_
  have hp : ∀ s : Fin k → I, ∏ a, t (s a) =
      ∏ i, t i ^ (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i := fun s => by
    simp only [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [Finsupp.single_apply]
  simp only [iteratedFDeriv_word_eq_coeff hf, hp]
  rw [sum_words_eq_sum_multinomial k fun m : I →₀ ℕ =>
    ((k.factorial : ℂ)⁻¹ * (((∏ i, (m i).factorial : ℕ) : ℂ) *
      MvPowerSeries.coeff m (GlobalTheory.taylor f))) • ∏ i, t i ^ m i]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hk : ∑ i, m i = k := (Finset.mem_finsuppAntidiag.1 hm).1
  have hs : ((∏ i, (m i).factorial : ℕ) : ℂ) * (Nat.multinomial Finset.univ m : ℂ) =
      (k.factorial : ℂ) := by
    rw [← Nat.cast_mul, Nat.multinomial_spec, hk]
  have h0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [smul_smul]
  congr 1
  rw [← mul_assoc, ← mul_assoc, mul_right_comm _ _ ((∏ i, (m i).factorial : ℕ) : ℂ),
    mul_comm (Nat.multinomial _ _ : ℂ), hs, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.PeriodFamily
end

section

noncomputable section

open Formalism.L2.DIV NumberField

namespace GlobalTheory.GoodFamilyOfChars

theorem nOf_eq_nS {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (P0 : Subgroup G)
    [Fintype P0] (ψ0 : P0 →* Kˣ) (s : T.S) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf (T.tau s) ⟨P0, ψ0⟩ = Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨P0, ψ0⟩ s := by
  classical
  have e : Formalism.IndefR.IndefiniteEpsilonOperator.epOp (T.tau s) ⟨P0, ψ0⟩ = (T.tau s).asAlgebraHom (Formalism.MainNotions.PrimeDegreeVariant.eps ⟨P0, ψ0⟩) := by

    rw [Formalism.MainNotions.PrimeDegreeVariant.eps, map_smul, map_sum, Formalism.IndefR.IndefiniteEpsilonOperator.epOp]
    congr 1
    have hsub : (Finset.univ.map (Function.Embedding.subtype (· ∈ P0))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have : x ∉ P0 := fun h => hx (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)
      simp [this]), Finset.sum_map]
    simp only [Function.Embedding.subtype_apply]
    refine Finset.sum_congr (by convert rfl) fun h _ => ?_
    simp [h.2, Representation.asAlgebraHom_of, map_inv]
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp Formalism.MainNotions.PrimeDegreeVariant.nS
  rw [e]

variable {K : Type} [Field K] {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module K W]

theorem asAlg_mem (τ : Representation K G W) (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U)
    (a : MonoidAlgebra K G) : ∀ w ∈ U, τ.asAlgebraHom a w ∈ U := by
  induction a using MonoidAlgebra.induction_on with
  | of g => intro w hw; simpa [Representation.asAlgebraHom_of] using hU g w hw
  | add a b ha hb => intro w hw; simpa using U.add_mem (ha w hw) (hb w hw)
  | smul r a ha => intro w hw; simpa using U.smul_mem r (ha w hw)

theorem asAlg_comm (τ : Representation K G W) (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f)
    (a : MonoidAlgebra K G) : f * τ.asAlgebraHom a = τ.asAlgebraHom a * f := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simpa [Representation.asAlgebraHom_of, Module.End.mul_eq_comp] using hf g
  | add a b ha hb => simp [map_add (f := _), mul_add, add_mul, ha, hb]
  | smul r a ha => simp [map_smul, ha]

theorem irr_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hc)
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha⟩ := hs ((φ w)⁻¹ • φ.smulRight v)
  have := asAlg_mem τ U hU a w hw
  rw [ha] at this
  simpa [hφ] using this

theorem scalar_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  have hc : f ∈ Set.center (Module.End K W) := by
    rw [Semigroup.mem_center_iff]
    intro e
    obtain ⟨a, rfl⟩ := hs e
    exact (asAlg_comm τ f hf a).symm
  obtain ⟨α, hα, rfl⟩ := Module.End.mem_center_iff.1 hc
  exact ⟨α, by ext x; simp⟩

theorem exists_goodFamily : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  intro K _ _ G _ _ X hX P0 _ ψ0 h1
  obtain ⟨T, hT, hM, -⟩ := GlobalTheory.GoodSetOfChars.exists_goodSet K G X hX ⟨P0, ψ0⟩ h1
  have hch : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) = fun g => LinearMap.trace K (T.W s) (T.tau s g) := fun s => rfl
  have hmem : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) ∈ X := fun s => (hT _).2 ⟨s, (hch s)⟩
  refine ⟨T.S, inferInstance, T.W, inferInstance, inferInstance, inferInstance, T.tau,
    ⟨fun s => inferInstance, fun s U hU => irr_of_surj (T.tau s) (T.irr s) U hU,
     fun s f hf => scalar_of_surj (T.tau s) (T.irr s) f hf, fun s t h => T.inj h⟩,
    fun χ => ⟨fun h => ?_, ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs⟩ := (hT χ).1 h
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hmem s
  · rw [nOf_eq_nS]
    exact hM s

end GlobalTheory.GoodFamilyOfChars
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.latticeIntertwiner_comap_linear_isometry : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (Φ : V ≃ₗ[ℂ] W), (∀ x y, H x y = H' (Φ x) (Φ y)) → IsHerm H' → ∀ (Λ₁ Λ₂ : AddSubgroup W) (α : W → ℂ) (F : W → ℂ), IsSemiChar H' Λ₂ α → F ∈ fixedBy H' α Λ₁ → relIdx Λ₁ Λ₂ ≠ 0 → ∀ z, inter H (fun v => α (Φ v)) (Λ₁.comap (Φ : V →ₗ[ℂ] W).toAddMonoidHom) (Λ₂.comap (Φ : V →ₗ[ℂ] W).toAddMonoidHom) (fun v => F (Φ v)) z = inter H' α Λ₁ Λ₂ F (Φ z) := by
  first | exact @GlobalTheory.inter_comap_isom | exact GlobalTheory.inter_comap_isom | (intros; apply GlobalTheory.inter_comap_isom <;> assumption)
end

section

open NumberField

namespace GlobalTheory.PrimesAboveExistence

theorem sup_eq_top_of_le_maximal {R : Type} [CommRing R] {A B I : Ideal R}
    (h : ∀ M : Ideal R, M.IsMaximal → B ≤ M → A ≤ M) (hA : I ⊔ A = ⊤) : I ⊔ B = ⊤ := by
  by_contra hne

  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hAM : A ≤ M := h M hM (le_sup_right.trans hle)
  exact hM.ne_top (top_le_iff.mp (hA ▸ sup_le (le_sup_left.trans hle) hAM))

theorem exists_primes_above {F : Type} [Field F] [NumberField F] (l : ℕ) (hl : Nat.Prime l) :
    ∃ P : Finset (Ideal (𝓞 F)),
      (∀ 𝔭 ∈ P, Ideal.IsMaximal 𝔭 ∧ 𝔭 ≠ ⊥ ∧ l ∣ (Ideal.absNorm : Ideal (𝓞 F) → ℕ) 𝔭) ∧
      ∀ I : Ideal (𝓞 F), Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔
        Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  classical
  set L : Ideal (𝓞 F) := Ideal.span {(l : 𝓞 F)} with hL
  have hL0 : L ≠ ⊥ := by
    rw [hL, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero

  refine ⟨(UniqueFactorizationMonoid.normalizedFactors L).toFinset, ?_, ?_⟩
  · intro 𝔭 h𝔭
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
    obtain ⟨hp, hle⟩ := h𝔭
    have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hle))
    have hmax : 𝔭.IsMaximal := hp.isMaximal hne
    refine ⟨hmax, hne, ?_⟩

    have hdvd : Ideal.absNorm 𝔭 ∣ l ^ Module.finrank ℤ (𝓞 F) := by
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rwa [hL, Ideal.absNorm_span_singleton,
        show (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hmax.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hk))
    change l ∣ Ideal.absNorm 𝔭
    rw [hk]
    exact dvd_pow_self l hk0
  · intro I
    unfold Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo
    refine and_congr_right fun _ =>
      ⟨fun h => sup_eq_top_of_le_maximal ?_ h, fun h => sup_eq_top_of_le_maximal ?_ h⟩
    ·
      intro M hM hLM
      have hmem : M ∈ (UniqueFactorizationMonoid.normalizedFactors L).toFinset := by
        rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0]
        exact ⟨hM.isPrime, hLM⟩
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun 𝔭 => 𝔭) hmem)
    ·
      intro M hM hPM
      obtain ⟨𝔭, h𝔭, hle⟩ := (Ideal.IsPrime.prod_le hM.isPrime).mp hPM
      rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
      have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ h𝔭.2))
      have h𝔭M : 𝔭 = M := (h𝔭.1.isMaximal hne).eq_of_le hM.ne_top hle
      exact h𝔭M ▸ h𝔭.2

end GlobalTheory.PrimesAboveExistence
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.FinConj

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem finEmb_eq_finGL (E : Type) [Field E] [NumberField E] (a : ℕ) (l : GL (Fin a) (Af E)) :
    finEmb E a l = finGL E a l := by
  have k1 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).1 = c.1 - 0 + 0 := fun _ _ _ => rfl
  have k2 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).2 = c.2 - y + x := fun _ _ _ => rfl
  apply (AdelicGLn.prodEquiv E a).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · rw [AdelicGLn.prodEquiv_apply_fst]
    change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).1
    rw [k1, sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  · rw [AdelicGLn.prodEquiv_apply_snd]
    change (l : Matrix (Fin a) (Fin a) (Af E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).2
    rw [k2, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [adele_one_snd, sub_self, zero_add]
    · rw [adele_zero_snd, sub_self, zero_add]

theorem unip_eq_unipGL (E : Type) [Field E] [NumberField E] (a r : ℕ) (z : BlockIx a r → Ad E) :
    (unip z : GA E a) = unipGL z := Units.ext rfl

theorem exists_conj_unip_mem :
    ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := by
  intro E _ _ a r L hL ω hω
  set U : Subgroup (AdelicGLn.integralFiniteGL E a) := L.comap (AdelicGLn.integralFiniteGL E a).subtype
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) := hL.preimage continuous_subtype_val
  obtain ⟨M, hM, h⟩ := exists_natCast_conj_unipGL_mem (K := E) (n := a) U hU hω r
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  obtain ⟨u, hu⟩ := h b hb ρ hρ k hk z hz1 hz2
  refine ⟨((u : AdelicGLn.integralFiniteGL E a) : GL (Fin a) (Af E)), u.2, ?_⟩
  rw [unip_eq_unipGL, ← finEmb_eq_finGL]
  exact hu

end GlobalTheory.FinConj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lagrangianCompletion_sup_ideal_smul_eq : ∀ (C : Type) [CommRing C] (I : Ideal C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (O : Type) [Ring O] (ρ : O →+* Module.End C H) (bar : O → O) (φ : LinearMap.BilinForm C H) (e : Module.End C H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ x y, φ x y = -φ y x) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∀ x ∈ F, e x ∈ F) → ∀ G M : Submodule C H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e → ∃ E : Submodule C H, (∃ N : Submodule C H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ E ⊔ I • ⊤ = F ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ a, ∀ x ∈ E, ρ a x ∈ E) ∧ ∀ x ∈ E, e x ∈ E := by
  first | (exact @GlobalTheory.lagrangian_completion_sup_smul_eq) | (exact GlobalTheory.lagrangian_completion_sup_smul_eq) | (intros; apply GlobalTheory.lagrangian_completion_sup_smul_eq  <;> assumption)
end
