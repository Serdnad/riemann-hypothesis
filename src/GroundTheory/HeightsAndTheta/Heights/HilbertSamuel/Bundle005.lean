module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle036
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Algebra.Order.Polynomial

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

theorem isReduced_tensor_domain_of_formallyEtale (E L D : Type*) [Field E] [Field L] [Algebra E L]
    [Algebra.FormallyEtale E L] [Algebra.EssFiniteType E L] [CommRing D] [IsDomain D]
    [Algebra E D] : IsReduced (L ⊗[E] D) := by
  have : IsReduced (FractionRing D ⊗[E] L) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) (FractionRing D ⊗[E] L)
  have : IsReduced (L ⊗[E] FractionRing D) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E L (FractionRing D))
      (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id E L) (IsScalarTower.toAlgHom E D (FractionRing D)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective D _))


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isReduced_tensor_field_of_perfectField (K L F : Type*) [Field K] [PerfectField K]
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L] [Field F] [Algebra K F] :
    IsReduced (L ⊗[K] F) := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  let R := Algebra.adjoin K (s : Set L)
  let E := IntermediateField.adjoin K (s : Set L)
  letI : Algebra R E :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K (s : Set L))).toAlgebra
  have : IsScalarTower K R E := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul R E :=
    Subalgebra.inclusion.faithfulSMul (IntermediateField.algebra_adjoin_le_adjoin K (s : Set L))
  have : IsFractionRing R E := IsFractionRing.of_field _ _ fun ⟨_, h⟩ => by
    obtain ⟨x, hx, y, hy, eq⟩ := IntermediateField.mem_adjoin_iff_div.mp h
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩

  have eR : R ≃ₐ[K] MvPolynomial s K :=
    (Subalgebra.equivOfEq R (Algebra.adjoin K (Set.range ((↑) : s → L))) (by simp [R])).trans hs.1.aevalEquiv.symm
  have hRF : IsDomain (R ⊗[K] F) :=
    ((Algebra.TensorProduct.comm K R F).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[K] F) eR).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv (σ := s) K F).toRingEquiv)).toMulEquiv.isDomain

  have hT : IsDomain (E ⊗[R] (R ⊗[K] F)) := by
    letI : Algebra (R ⊗[K] F) (E ⊗[R] (R ⊗[K] F)) := Algebra.TensorProduct.rightAlgebra
    have := IsLocalization.tensorRight (R := R) (S := R ⊗[K] F) (A := E) (nonZeroDivisors R)
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := R ⊗[K] F)
      (M := Algebra.algebraMapSubmonoid (R ⊗[K] F) (nonZeroDivisors R)) (E ⊗[R] (R ⊗[K] F)) ?_
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have hinj : Function.Injective (algebraMap R (R ⊗[K] F)) :=
      Algebra.TensorProduct.includeLeft_injective (S := R) (RingHom.injective (algebraMap K F))
    exact nonZeroDivisors.ne_zero hr (hinj (by simpa using h0))

  have : IsDomain (E ⊗[K] F) :=
    (Algebra.TensorProduct.cancelBaseChange K R R E F).symm.toMulEquiv.isDomain

  have : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  have : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  have := isReduced_tensor_domain_of_formallyEtale E L (E ⊗[K] F)
  exact isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange K E E L F).symm
    (AlgEquiv.injective _)

theorem isReduced_tensor_domain_of_perfectField (K A F : Type*) [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra K F] :
    IsReduced (F ⊗[K] A) := by
  have : Algebra.EssFiniteType A (FractionRing A) :=
    .of_isLocalization _ (nonZeroDivisors A)
  have : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
  have := isReduced_tensor_field_of_perfectField K (FractionRing A) F
  have : IsReduced (F ⊗[K] FractionRing A) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K F (FractionRing A)) (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K A (FractionRing A)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective A _))

theorem isRadical_map_of_isPrime_of_perfectField (K F : Type*) [Field K] [PerfectField K]
    [Field F] [Algebra K F] (σ : Type*) [Fintype σ] (Q : Ideal (MvPolynomial σ K))
    [Q.IsPrime] : (Q.map (MvPolynomial.map (algebraMap K F))).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  let e₀ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) K F
  have hJ : Q.map (MvPolynomial.map (algebraMap K F)) =
      (Q.map (Algebra.TensorProduct.includeRight (R := K) (A := F)).toRingHom).map
        e₀.toRingEquiv.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    simp [e₀, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e : F ⊗[K] (MvPolynomial σ K ⧸ Q) ≃+*
      MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap K F)) :=
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K (MvPolynomial σ K) F Q).toRingEquiv.trans
      (Ideal.quotientEquiv _ _ e₀.toRingEquiv (hJ.trans rfl))
  have := isReduced_tensor_domain_of_perfectField K (MvPolynomial σ K ⧸ Q) F
  exact isReduced_of_injective e.symm e.symm.injective

theorem PrimeComplexRadical.proof : PrimeComplexRadical.Statement := by
  intro σ _ P hP
  by_cases hZ : ∃ n : ℤ, n ≠ 0 ∧ C n ∈ P
  · obtain ⟨n, hn, hnP⟩ := hZ
    have htop : P.map (MvPolynomial.map (Int.castRingHom ℂ)) = ⊤ := by
      apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hnP)
      rw [MvPolynomial.map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using hn)).map C
    rw [htop]
    exact fun x _ => Submodule.mem_top
  · push Not at hZ
    let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
    let M := (nonZeroDivisors ℤ).map (C (σ := σ) (R := ℤ))
    have : IsLocalization M (MvPolynomial σ ℚ) := MvPolynomial.isLocalization _ _
    let Q := P.map (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ))
    have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hP (by
      rw [Set.disjoint_left]
      rintro _ ⟨n, hn, rfl⟩ hnP
      exact hZ n (nonZeroDivisors.ne_zero hn) hnP)
    have hmap : P.map (MvPolynomial.map (Int.castRingHom ℂ)) =
        Q.map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
      rw [Ideal.map_map]
      congr 1
      refine RingHom.ext fun p => ?_
      change _ = MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (algebraMap ℤ ℚ) p)
      rw [MvPolynomial.map_map,
        show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    rw [hmap]
    exact isRadical_map_of_isPrime_of_perfectField ℚ ℂ σ Q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem RootsLiftToZeros.exists_extend {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ) (hker : RingHom.ker (algebraMap R A) ≤ RingHom.ker ev) :
    ∃ χ : A →+* ℂ, χ.comp (algebraMap R A) = ev :=
  _root_.UpperTheory.Reformulated.B.Qi28.exists_extend ev hker

theorem RootsLiftToZeros.proof : RootsLiftToZeros.Statement := by
  intro σ P e ℓ u G hint hG y t ht
  classical
  let A := MvPolynomial σ ℚ ⧸ P
  let α : Polynomial (MvPolynomial (Fin e) ℚ) →+* A :=
    (Ideal.Quotient.mk P).comp (Polynomial.eval₂RingHom (aeval ℓ).toRingHom u)
  letI : Algebra (Polynomial (MvPolynomial (Fin e) ℚ)) A := α.toAlgebra
  have hα : ∀ Q, algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A Q =
      Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) := fun _ => rfl
  have _ : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin e) ℚ)) A := by
    constructor
    intro a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hpm, hp⟩ := hint g
    refine ⟨p.map Polynomial.C, hpm.map _, ?_⟩
    have hc : (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A).comp Polynomial.C =
        (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom :=
      RingHom.ext fun r => by simp [hα]
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  let ev : Polynomial (MvPolynomial (Fin e) ℚ) →+* ℂ := Polynomial.eval₂RingHom (aeval y).toRingHom t
  have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A) ≤ RingHom.ker ev := by
    intro Q hQ
    rw [RingHom.mem_ker, hα, Ideal.Quotient.eq_zero_iff_mem] at hQ
    obtain ⟨H, rfl⟩ := hG Q hQ
    rw [RingHom.mem_ker, map_mul]
    change Polynomial.eval₂ (aeval y).toRingHom t G * ev H = 0
    rw [ht, zero_mul]
  obtain ⟨ψ, hψ⟩ := RootsLiftToZeros.exists_extend ev hker
  let χ : MvPolynomial σ ℚ →+* ℂ := ψ.comp (Ideal.Quotient.mk P)
  have hχ : χ = (aeval fun i => χ (X i)).toRingHom :=
    MvPolynomial.ringHom_ext
      (fun r => RingHom.congr_fun (Subsingleton.elim (χ.comp C) ((aeval fun i => χ (X i)).toRingHom.comp C)) r)
      (fun i => by simp)
  have key : ∀ Q, χ (Q.eval₂ (aeval ℓ).toRingHom u) = ev Q := fun Q => RingHom.congr_fun hψ Q
  have hz : ∀ g, aeval (fun i => χ (X i)) g = χ g := fun g => (RingHom.congr_fun hχ g).symm
  refine ⟨fun i => χ (X i), fun g hg => ?_, funext fun j => ?_, ?_⟩
  · rw [hz]
    change ψ (Ideal.Quotient.mk P g) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  · have := key (Polynomial.C (X j))
    simp only [Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at this
    rw [hz, this]
    simp [ev]
  · have := key Polynomial.X
    simp only [Polynomial.eval₂_X] at this
    rw [hz, this]
    simp [ev]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Finset

theorem RootGridLower.sum_fin_pow {M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    {a b : ℕ} (ha : a < M) (hb : b < M) :
    ∑ t : Fin M, (ω ^ a * (ω ^ b)⁻¹) ^ (t : ℕ) = if a = b then (M : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero hM.ne'
  rw [Fin.sum_univ_eq_sum_range (fun t => (ω ^ a * (ω ^ b)⁻¹) ^ t)]
  split_ifs with hab
  · subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero _ hω0)]
  · have hz : ω ^ a * (ω ^ b)⁻¹ ≠ 1 := by
      intro h
      apply hab
      apply hω.pow_inj ha hb
      have := congrArg (· * ω ^ b) h
      simpa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hω0)] using this
    rw [geom_sum_eq hz]
    have h1 : (ω ^ a * (ω ^ b)⁻¹) ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    simp [h1]

theorem RootGridLower.average {e M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    (Q : MvPolynomial (Fin e) ℤ) (hdeg : ∀ i, Q.degreeOf i < M) (j : Fin e →₀ ℕ)
    (hj : ∀ i, j i < M) :
    ∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = (M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ) := by
  classical
  simp_rw [eval_map, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ d ∈ Q.support, ∑ k : Fin e → Fin M,
      (Int.castRingHom ℂ) (Q.coeff d) * (∏ i, (ω ^ (k i : ℕ)) ^ d i) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) =
      ((Q.coeff d : ℤ) : ℂ) * if d = j then (M : ℂ) ^ e else 0 := by
    intro d hd
    have hdM : ∀ i, d i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hd) (hdeg i)
    have hprod : ∀ k : Fin e → Fin M, (∏ i, (ω ^ (k i : ℕ)) ^ d i) * ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)
        = ∏ i, (ω ^ d i * (ω ^ j i)⁻¹) ^ (k i : ℕ) := by
      intro k
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k i : ℕ)]
    simp_rw [mul_assoc, hprod, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun i (t : Fin M) => (ω ^ d i * (ω ^ j i)⁻¹) ^ (t : ℕ))]
    simp_rw [RootGridLower.sum_fin_pow hM hω (hdM _) (hj _)]
    split_ifs with hdj
    · subst hdj; simp
    · obtain ⟨i, hi⟩ : ∃ i, d i ≠ j i := by
        by_contra h
        push Not at h
        exact hdj (Finsupp.ext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [Finset.sum_congr rfl key]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hjs
  · simp [mul_comm]
  · rw [MvPolynomial.notMem_support_iff.mp hjs]; simp

theorem RootGridLower.of_pos {e M : ℕ} (hM : 0 < M) (Q : MvPolynomial (Fin e) ℤ) (hQ : Q ≠ 0)
    (hdeg : ∀ i, Q.degreeOf i < M) :
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ M = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖ := by
  classical
  have hω := Complex.isPrimitiveRoot_exp M hM.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / M)
  obtain ⟨j, hj⟩ : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hQ
  have hjM : ∀ i, j i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hj) (hdeg i)
  have hc : (1 : ℝ) ≤ ‖((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (MvPolynomial.mem_support_iff.mp hj)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one hM.ne'
  by_contra hne
  push Not at hne
  have hlt : ∀ k : Fin e → Fin M,
      ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ < 1 := by
    intro k
    refine hne _ fun i => ?_
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hne' : (Finset.univ : Finset (Fin e → Fin M)).Nonempty :=
    ⟨fun i => ⟨j i, hjM i⟩, Finset.mem_univ _⟩
  have hupper : ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ < (M : ℝ) ^ e := by
    rw [← RootGridLower.average hM hω Q hdeg j hjM]
    calc ‖∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖
        ≤ ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [norm_prod, hω1]
      _ < ∑ _k : Fin e → Fin M, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne' fun k _ => hlt k
      _ = (M : ℝ) ^ e := by simp
  have hlower : (M : ℝ) ^ e ≤ ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact le_mul_of_one_le_right (by positivity) hc
  linarith

theorem RootGridLower.proof : RootGridLower.Statement := by
  intro e m Q hQ hdeg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨ζ, -, hζ⟩ := RootGridLower.of_pos Nat.one_pos Q hQ
      (fun i => lt_trans (hdeg i) Nat.one_pos)
    exact ⟨ζ, fun i => pow_zero _, hζ⟩
  · exact RootGridLower.of_pos hm Q hQ hdeg

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial Filter

theorem PolySandwich.leadingCoeff_nonneg_of_eventually (f : ℚ[X])
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.leadingCoeff := by
  by_contra h
  push Not at h
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · obtain ⟨n, hn⟩ := hf.exists
    rw [eq_C_of_natDegree_eq_zero h0, eval_C] at hn
    have : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, h0]
    linarith
  · have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
    have ht := (f.tendsto_atBot_of_leadingCoeff_nonpos hdeg h.le).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn1, hn2⟩ := (hf.and (ht.eventually (eventually_lt_atBot 0))).exists
    simp only [Function.comp] at hn2
    linarith

theorem PolySandwich.coeff_nonneg_of_eventually (f : ℚ[X]) (E : ℕ) (hE : f.natDegree ≤ E)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq]
    exact PolySandwich.leadingCoeff_nonneg_of_eventually f hf

theorem PolySandwich.natDegree_shift (p : ℚ[X]) (c : ℚ) : (p.comp (X + C c)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem PolySandwich.coeff_shift (p : ℚ[X]) (c : ℚ) (E : ℕ) (hE : p.natDegree ≤ E) :
    (p.comp (X + C c)).coeff E = p.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (by rwa [PolySandwich.natDegree_shift])]
  · subst heq
    have h1 : (p.comp (X + C c)).leadingCoeff = p.leadingCoeff := by
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C, one_pow,
        mul_one]
    rw [leadingCoeff, PolySandwich.natDegree_shift] at h1
    exact h1

theorem PolySandwich.proof : PolySandwich.Statement := by
  intro D c p q hq hev
  set g : ℚ[X] := p.comp (X + C (c : ℚ)) with hg
  have h1 : ∀ᶠ n : ℕ in atTop, 0 ≤ (q - p).eval (n : ℚ) :=
    hev.mono fun n hn => by rw [eval_sub]; linarith [hn.1]
  have h2 : ∀ᶠ n : ℕ in atTop, 0 ≤ (g - q).eval (n : ℚ) :=
    hev.mono fun n hn => by
      rw [eval_sub, hg, eval_comp, eval_add, eval_X, eval_C]; linarith [hn.2]
  have hgdeg : g.natDegree = p.natDegree := PolySandwich.natDegree_shift p c

  have key : ∀ E : ℕ, p.natDegree ≤ E → q.natDegree ≤ E → p.coeff E = q.coeff E := by
    intro E hp hqE
    have a := PolySandwich.coeff_nonneg_of_eventually (q - p) E
      ((natDegree_sub_le _ _).trans (max_le hqE hp)) h1
    have b := PolySandwich.coeff_nonneg_of_eventually (g - q) E
      ((natDegree_sub_le _ _).trans (max_le (hgdeg ▸ hp) hqE)) h2
    rw [coeff_sub] at a b
    rw [hg, PolySandwich.coeff_shift p c E hp] at b
    linarith
  have hpD : p.natDegree ≤ D := by
    by_contra hlt
    push Not at hlt
    have e := key p.natDegree le_rfl (hq.trans hlt.le)
    rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt)] at e
    have hp0 : p = 0 := leadingCoeff_eq_zero.mp e
    rw [hp0, natDegree_zero] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  exact ⟨hpD, key D hpD hq⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix

noncomputable section

def ComplexTaylorTwo.Statement : Prop :=
  ∀ (D : ℕ) (ψ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), ContDiffAt ℝ 2 ψ y₀ →
    ∃ (a : Fin D → ℂ) (b : Matrix (Fin D) (Fin D) ℂ),
      (fun z : Fin D → ℂ => ψ (y₀ + z) - ψ y₀ - (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re -
          (z ⬝ᵥ (hessC ψ y₀ *ᵥ star z)).re) =o[𝓝 0] fun z => ‖z‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
