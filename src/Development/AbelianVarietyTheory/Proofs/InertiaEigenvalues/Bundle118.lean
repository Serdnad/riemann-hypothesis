module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.WittVector.Frobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle092
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalB
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Mathlib.RingTheory.PowerSeries.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open ReciprocityTheory.Gal Pointwise NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_frob_at_place_over_prime : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω),
    A.valuation (p : Ω) < 1 → ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧
      ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  intro F Ω _ _ _ _ _ p hp A hpA
  set f : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F) with hf
  have fA : ∀ r : 𝓞 F, f r ∈ A := fun r =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe r).map (algebraMap F Ω).toIntAlgHom)
  let I : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal A).comap (f.codRestrict A fA)
  have memI : ∀ r, r ∈ I ↔ A.valuation (algebraMap F Ω (r : F)) < 1 := fun r => by
    simp only [I, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have hIp : I.IsPrime := Ideal.comap_isPrime _ _
  have hpI : (p : 𝓞 F) ∈ I := by
    rw [memI]; simpa using hpA
  have hIne : I ≠ ⊥ := fun h => by
    have h' := hpI
    rw [h, Ideal.mem_bot] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  let v : HeightOneSpectrum (𝓞 F) := ⟨I, hIp, hIne⟩
  obtain ⟨σ, hσA, hσ⟩ := exists_frob_over (F := F) (A := A) (v := v) (fun x => (memI x).symm)
  refine ⟨σ, hσA, Nat.card (𝓞 F ⧸ v.asIdeal), fun h1 => ?_, hσ⟩
  have hss : Subsingleton (𝓞 F ⧸ v.asIdeal) := by
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finite.card_le_one_iff_subsingleton.mp h1.le
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
  exact hIp.ne_top ((Ideal.eq_top_iff_one _).2 this)

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.trace_eq_sum_of_algEquiv_pi : ∀ {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ) (e : K ≃ₐ[F] (Fin r → F)) (k : K), Algebra.trace F K k = ∑ i, e k i := by
  first | exact @GlobalTheory.trace_eq_sum_coords_of_algEquiv | exact GlobalTheory.trace_eq_sum_coords_of_algEquiv | (intros; apply GlobalTheory.trace_eq_sum_coords_of_algEquiv <;> assumption)
end

section

open scoped NNReal

namespace GlobalTheory.DworkLift

theorem exists_frobenius_compatible_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
    ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O,
      (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  intro l _ A _ φ hφ htor O _ _ f
  have hex := GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate l A φ hφ
  have inj := GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion l A htor
  let s : A → WittVector l A := fun a => Classical.choose (hex a)
  have hs : ∀ a n, WittVector.ghostComponent n (s a) = φ^[n] a := fun a => Classical.choose_spec (hex a)
  have hit : ∀ (n : ℕ) (a : A), φ^[n] a = (φ ^ n) a := fun n a => by rw [RingHom.coe_pow]
  let S : A →+* WittVector l A :=
    { toFun := s
      map_one' := inj _ _ fun n => by rw [hs, map_one, hit, map_one]
      map_mul' := fun a b => inj _ _ fun n => by rw [map_mul, hs, hs, hs, hit, hit, hit, map_mul]
      map_zero' := inj _ _ fun n => by rw [hs, map_zero, hit, map_zero]
      map_add' := fun a b => inj _ _ fun n => by rw [map_add (f := _), hs, hs, hs, hit, hit, hit, map_add (f := _)] }
  have hS0 : ∀ a, (S a).coeff 0 = a := fun a => by
    change (s a).coeff 0 = a
    have h := hs a 0
    rw [WittVector.ghostComponent_apply, wittPolynomial_zero] at h
    simpa using h
  have hSφ : ∀ a, S (φ a) = WittVector.frobenius (S a) := fun a => inj _ _ fun n => by
    change WittVector.ghostComponent n (s (φ a)) = WittVector.ghostComponent n (WittVector.frobenius (s a))
    rw [WittVector.ghostComponent_frobenius, hs, hs, Function.iterate_succ_apply]
  refine ⟨(WittVector.map f).comp S, fun a => ?_, fun a => ?_⟩
  · simp only [RingHom.comp_apply, WittVector.map_coeff, hS0]
  · simp only [RingHom.comp_apply, hSφ]
    exact WittVector.IsPoly.map (WittVector.frobenius_isPoly l) f (S a)

end GlobalTheory.DworkLift
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.continuousCohomology_vanishes_of_primeToL_normal_no_invariants : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (l : ℕ) (J : Subgroup Γ), l.Prime → J.Normal → IsClosed (J : Set Γ) → (∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∀ j ∈ J, ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U) → ContAction ρ → (∀ m : M, ∃ n, l ^ n • m = 0) → (∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) → H0 ρ = ⊥ ∧ Subsingleton (H1 ρ) ∧ Subsingleton (H2 ρ) := by
  first | exact @GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | exact GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | (intros; apply GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  first | exact @GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | exact GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | (intros; apply GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv <;> assumption)
end

section

open PowerSeries GlobalTheory.BK Filter Topology

theorem _root_.GlobalTheory.T.tendsto_const_pow_mul_pow_pow_zero' : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l → Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.tendsto_const_pow_mul_pow_pow_zero | exact GlobalTheory.tendsto_const_pow_mul_pow_pow_zero | (intros; apply GlobalTheory.tendsto_const_pow_mul_pow_pow_zero <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary : ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G] (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), Topology.IsEmbedding (fun m : M => ϖ • m) → ∀ (s : Finset (Z1 ρ)), (∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ)) → ∀ c : Z1 ρ, ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M), (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  first | exact @GlobalTheory.cocycle_lift_mod_uniformizer | exact GlobalTheory.cocycle_lift_mod_uniformizer | (intros; apply GlobalTheory.cocycle_lift_mod_uniformizer <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

theorem _root_.GlobalTheory.T.galoisAddHom_vanishes_complexConjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  first | exact @GlobalTheory.addHom_complexConjugation_eq_zero | exact GlobalTheory.addHom_complexConjugation_eq_zero | (intros; apply GlobalTheory.addHom_complexConjugation_eq_zero <;> assumption)
end
