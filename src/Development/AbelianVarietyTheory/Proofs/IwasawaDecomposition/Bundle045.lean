module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle040
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
public import Mathlib.Topology.Algebra.Valued.NormedValued
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.automorphism_congr_one_on_adjoin_root_uniformiser : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra W F] [IsScalarTower W (FractionRing W) F]
    (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ (ϖ : W), Irreducible ϖ → ∀ (l : ℕ), l ≠ 0 → ∀ (x : F), x ^ l = algebraMap W F ϖ →
    ∀ (g : F ≃ₐ[FractionRing W] F) (b : F), b ∈ IntermediateField.adjoin (FractionRing W) {x} →
    O.valuation b ≤ 1 → O.valuation (g b - b) < 1 := by
  first | exact @GlobalTheory.RootOfUniformiserDVR.cong_on_adjoin | exact GlobalTheory.RootOfUniformiserDVR.cong_on_adjoin | (intros; apply GlobalTheory.RootOfUniformiserDVR.cong_on_adjoin <;> assumption)
end

section

open NumberField Module

namespace GlobalTheory.Mem.ImagQuad

open QuadraticZeta

theorem exists_field_sq_eq_neg (d : ℕ) (hd : 0 < d) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (r : K),
      finrank ℚ K = 2 ∧ r ^ 2 = -(d : K) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ) with hp
  have hpdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hpmon : p.Monic := by
    rw [hp]; monicity!
  have hroot : ∀ x : ℚ, ¬ p.IsRoot x := by
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot p) := pb.finite
  have : NumberField (AdjoinRoot p) := ⟨⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, hpdeg]
  · have h := AdjoinRoot.eval₂_root p
    simp only [hp, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [eq_neg_iff_add_eq_zero, ← h]
    simp

theorem exists_imagQuad_integers : ∀ d : ℕ, d.Prime → d % 4 = 3 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ω : 𝓞 K), IsTotallyComplex K ∧
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ (2 * ω - 1) ^ 2 = -(d : 𝓞 K) ∧
      (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  intro d hdp hd4
  obtain ⟨K, _, _, r, h2, hr⟩ := exists_field_sq_eq_neg d hdp.pos
  have hsq : Squarefree d := hdp.squarefree
  obtain ⟨w, bar, hw, -, hspan, hemb, -⟩ :=
    GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d hsq hd4 K h2 r hr
  have hwr : 2 * (w : K) - 1 = r := by rw [hw]; ring
  have hcoe : algebraMap (𝓞 K) K (2 * w - 1) = r := by
    rw [← hwr]
    simp only [map_sub, map_mul, map_one, map_ofNat]
  have hw2 : (2 * w - 1) ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hcoe, hr, map_neg, map_natCast]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hwsq : w * w = w - (k : 𝓞 K) := by
    have h4 : (4 : 𝓞 K) * (w * w - w + k) = 0 := by
      have : ((d : ℕ) : 𝓞 K) + 1 = 4 * (k : 𝓞 K) := by exact_mod_cast hk
      linear_combination hw2 - this
    have h4ne : (4 : 𝓞 K) ≠ 0 := by
      intro h
      have : ((4 : 𝓞 K) : K) = 0 := by rw [h]; simp
      norm_num at this
    have := (mul_eq_zero.mp h4).resolve_left h4ne
    linear_combination this
  have hli : LinearIndependent ℤ ![(1 : 𝓞 K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hK : (s : K) + t * (w : K) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hst
      simpa [zsmul_eq_mul] using this
    have ht : t = 0 := by
      by_contra ht
      have htK : (t : K) ≠ 0 := by exact_mod_cast ht
      set q : ℚ := -(2 * s + t) / t with hqdef
      have hrq : r = algebraMap ℚ K q := by
        simp only [hqdef, map_div₀, map_neg, map_add (f := _), map_mul, map_ofNat, map_intCast]
        field_simp
        linear_combination (2 : K) * hK + (-(t : K)) * hwr
      have hq : q ^ 2 = -(d : ℚ) := by
        apply (algebraMap ℚ K).injective
        rw [map_pow, ← hrq, hr]
        simp
      have hdpos : (0 : ℚ) < d := by exact_mod_cast hdp.pos
      nlinarith [sq_nonneg q]
    subst ht
    refine ⟨?_, rfl⟩
    have : (s : K) = 0 := by simpa using hK
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspan z
    have hr' : Set.range ![(1 : 𝓞 K), w] = {1, w} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]; rfl
    rw [hr', Submodule.mem_span_pair]
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  let B := Basis.mk hli hsp
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = w := by simp [B]
  have hrepr : ∀ s t : ℤ, B.repr ((s : 𝓞 K) + t * w) = Finsupp.single 0 s + Finsupp.single 1 t := by
    intro s t
    have : (s : 𝓞 K) + t * w = s • B 0 + t • B 1 := by
      rw [hB0, hB1]; simp [zsmul_eq_mul]
    rw [this, map_add (f := _), map_zsmul, map_zsmul, B.repr_self, B.repr_self]
    simp
  refine ⟨K, inferInstance, inferInstance, w, ?_, h2, ?_, hw2, hspan, ?_⟩
  · refine ⟨fun v => ?_⟩
    rw [InfinitePlace.isComplex_iff]
    exact (hemb v.embedding).1
  · exact GlobalTheory.discr_eq_neg_of_sq_eq h2 hsq hd4 hr
  · intro a b
    rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
    have e00 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 0 = a := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have e10 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 0 = b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have hx1 : ((a : 𝓞 K) + b * w) * w = ((-(b * k) : ℤ) : 𝓞 K) + ((a + b : ℤ) : 𝓞 K) * w := by
      push_cast
      linear_combination (b : 𝓞 K) * hwsq
    have e01 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 1 = -(b * k) := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    have e11 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 1 = a + b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    rw [e00, e10, e01, e11]
    have hk' : (d : ℤ) + 1 = 4 * k := by exact_mod_cast hk
    linear_combination (-(b ^ 2) : ℤ) * hk'

end GlobalTheory.Mem.ImagQuad
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.exists_integral_quotient_dominating_valuationSubring : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra.IsAlgebraic (FractionRing W) F] [Algebra W F]
    [IsScalarTower W (FractionRing W) F] (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ x ∈ O, ∃ s t : F, IsIntegral W s ∧ IsIntegral W t ∧ O.valuation s = 1 ∧ s * x = t := by
  first | exact @GlobalTheory.DomValInt.exists_integral_quotient | exact GlobalTheory.DomValInt.exists_integral_quotient | (intros; apply GlobalTheory.DomValInt.exists_integral_quotient <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B) (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime), Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  first | exact @GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | exact GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | (intros; apply GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial <;> assumption)
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor : ∀ (T U C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T] [CommRing U] [IsDomain U] [IsIntegrallyClosed U] [Algebra T U] [Module.Flat T U] [CommRing C] [IsDomain C] [Algebra T C] [Module.Finite T C], Function.Injective (algebraMap T U) → Function.Injective (algebraMap T C) → ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c → ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s = algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  first | exact @GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | exact GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | (intros; apply GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.SplitComplHomeo


open scoped WithZeroTopology in
theorem exists_complEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L,
      Continuous i ∧ Continuous i.symm ∧ ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro E _ _ _ s
  have : s.w.asIdeal.LiesOver s.v.asIdeal := ⟨s.w_under.symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (maximalRealSubfield E) E s.v s.w).continuous
  let φ : s.v.adicCompletion (maximalRealSubfield E) →+* s.w.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E s.w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv (maximalRealSubfield E) s.v).toRingHom
  have hφ : ∀ x : maximalRealSubfield E, φ (algebraMap (maximalRealSubfield E) _ x) =
      algebraMap E _ (algebraMap (maximalRealSubfield E) E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E s.w).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion (maximalRealSubfield E) s.v))
  have hi : ∀ x : E, φ (s.i x) = algebraMap E (s.w.adicCompletion E) x := fun x => by
    have key : ∀ y, Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x) := fun y =>
      (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).induction_on
        (p := fun y => Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x)) y
        (isClosed_eq
          ((Valued.continuous_valuation_of_surjective (s.w.valuedAdicCompletion_surjective E)).comp
            (hcont.sub continuous_const))
          ((Valued.continuous_valuation_of_surjective (s.v.valuedAdicCompletion_surjective _)).comp
            (continuous_id.sub continuous_const))) fun k => by
        rw [hφ, ← map_sub, ← PI.CompAtExist.stepA s, map_sub, AlgHom.commutes]
    have h0 := key (s.i x)
    rw [sub_self, map_zero, map_eq_zero, sub_eq_zero] at h0
    exact h0
  letI : Algebra (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hcont
  letI : NontriviallyNormedField (s.v.adicCompletion (maximalRealSubfield E)) :=
    Valued.toNontriviallyNormedField _ _
  have hs : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E)) := Submodule.closed_of_finiteDimensional _
    intro y
    exact (HeightOneSpectrum.denseRange_algebraMap E s.w).induction_on
      (p := fun y => y ∈ (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E))) y hcl fun x => ⟨s.i x, hi x⟩
  let e : s.v.adicCompletion (maximalRealSubfield E) ≃ₗ[s.v.adicCompletion (maximalRealSubfield E)]
      s.w.adicCompletion E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) ⟨φ.injective, hs⟩
  haveI : FiniteDimensional (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    e.finiteDimensional
  have hinv : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, hs⟩, hcont, hinv.congr fun y => ?_, hi⟩
  exact (RingEquiv.symm_apply_eq _).2 (e.apply_symm_apply y).symm |>.symm

end GlobalTheory.SplitComplHomeo
end

section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow : ∀ (p q : ℕ), constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | exact GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | (intros; apply GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow <;> assumption)
end

section

open scoped Pointwise

namespace GlobalTheory.ValuationOfMemIff

theorem le_iff_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (x y : Ω) :
    A.valuation (σ x) ≤ A.valuation (σ y) ↔ A.valuation x ≤ A.valuation y := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hσy : σ y ≠ 0 := by simpa using hy
    have key : ∀ a b : Ω, b ≠ 0 → (A.valuation a ≤ A.valuation b ↔ a / b ∈ A) := by
      intro a b hb
      rw [← A.valuation_le_one_iff, map_div₀,
        div_le_one₀ (by simpa [pos_iff_ne_zero] using hb)]
    rw [key _ _ hσy, key _ _ hy, ← map_div₀, h]

theorem not_injective_pow {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (t : Ω) (ht : IsIntegral E t) :
    ¬ Function.Injective (fun k : ℕ => (σ ^ k) t) := by
  intro hinj

  have hsub : Set.range (fun k : ℕ => (σ ^ k) t) ⊆ (minpoly E t).rootSet Ω := by
    rintro _ ⟨k, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero ht, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    simpa [minpoly.aeval] using this
  exact Set.infinite_range_of_injective hinj (((minpoly E t).rootSet_finite Ω).subset hsub)

theorem valuation_eq_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (t : Ω)
    (ht : IsIntegral E t) : A.valuation (σ t) = A.valuation t := by
  have hsucc : ∀ k : ℕ, (σ ^ (k + 1)) t = σ ((σ ^ k) t) := fun k => by
    rw [pow_succ', AlgEquiv.mul_apply]

  have hlt : ∀ x y : Ω, A.valuation (σ x) < A.valuation (σ y) ↔ A.valuation x < A.valuation y := by
    intro x y
    rw [lt_iff_not_ge, lt_iff_not_ge, le_iff_of_mem_iff A σ h]
  have hinj : ∀ w : ℕ → _, (StrictMono w ∨ StrictAnti w) →
      (∀ k, w k = A.valuation ((σ ^ k) t)) → False := by
    intro w hw hwk
    apply not_injective_pow σ t ht
    intro a b hab
    have : w a = w b := by rw [hwk, hwk]; exact congrArg A.valuation hab
    rcases hw with hw | hw
    · exact hw.injective this
    · exact hw.injective this
  rcases lt_trichotomy (A.valuation (σ t)) (A.valuation t) with hc | hc | hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inr (strictAnti_nat_of_succ_lt ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih
  · exact hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inl (strictMono_nat_of_lt_succ ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih

theorem valuation_apply_eq : ∀ (E Ω : Type) [inst : Field E] [NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : Formalism.ConjugateSelfDual.G E Ω), Membership.mem (ReciprocityTheory.Gal.Dec A) σ → ∀ (t : Ω), Eq ((ValuationSubring.valuation A) (σ t)) ((ValuationSubring.valuation A) t) := by
  intro E Ω _ _ _ _ _ A σ hσ t
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact valuation_eq_of_mem_iff A σ (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hσ) t
    (Algebra.IsIntegral.isIntegral t)

end GlobalTheory.ValuationOfMemIff
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameTau

theorem root_eq_of_close {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω}
    (h : ζ ^ m = 1) (h' : ζ' ^ m = 1) (hm : ¬ A.valuation (m : Ω) < 1)
    (hc : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  first
  | exact @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | (apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one ..)

theorem ine_fix_root {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  refine root_eq_of_close A m (by rw [← map_pow, hζ, map_one]) hζ hm ?_
  exact hσ.2 ζ (valuation_eq_one_of_pow_eq_one A hm0 hζ).le

theorem quot_mul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ τ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {π : Ω} (hπ : π ≠ 0)
    {e : E} (he : π ^ m = algebraMap E Ω e) :
    (σ * τ) π / π = (σ π / π) * (τ π / π) := by
  have hτ : (τ π / π) ^ m = 1 := by
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hfix := ine_fix_root hσ m hm hτ
  have e1 : τ π = (τ π / π) * π := by field_simp
  have e2 : (σ * τ) π = σ (τ π / π) * σ π := by
    rw [AlgEquiv.mul_apply, ← map_mul, div_mul_cancel₀ _ hπ]
  rw [e2, hfix]
  field_simp

end GlobalTheory.TameTau
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_specTensor_to_pullback_sections_compat : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens) (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), letI := (ρ.appLE U W hW).hom.toAlgebra; letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra; ∃ (κ : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ pullback ξ ρ) (hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens)), (∀ c : Γ(Y', W), (Scheme.ΓSpecIso _).hom.hom (((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom c) = c ⊗ₜ[Γ(X, U)] (1 : R)) ∧ ∀ r : R, (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] r := by
  first | exact @GlobalTheory.specTensor_to_pullback | exact GlobalTheory.specTensor_to_pullback | (intros; apply GlobalTheory.specTensor_to_pullback <;> assumption)
end

section

open NumberField

namespace GlobalTheory.HermSignature

theorem exists_le_gram_eq_sgn : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → ∀ τ : E →+* ℂ, ∃ p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ReciprocityTheory.ChartRestriction.G.FD.gram τ G P = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  intro E _ _ _ r G hG hd τ
  obtain ⟨p, Q, hQ, h⟩ := GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn hG hd τ
  refine ⟨min p r, min_le_right _ _, Q, hQ, ?_⟩
  rw [h]
  congr 1
  funext a
  have ha := a.2
  simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, lt_min_iff, ha, and_true]

end GlobalTheory.HermSignature
end
