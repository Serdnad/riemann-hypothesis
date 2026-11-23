module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle006
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle007
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle008
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle010
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle009
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ScaledCasimir

section General

variable {J A : Type*} [Fintype J] [DecidableEq J] [CommRing A] (a : Module.Basis J ℤ A)

noncomputable def dualScaled (m : J) : A :=
  ∑ n, (Algebra.traceMatrix ℤ a).adjugate m n • a n

theorem trace_dualScaled_mul_basis (m p : J) :
    Algebra.trace ℤ A (dualScaled a m * a p) =
      if m = p then (Algebra.traceMatrix ℤ a).det else 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul (Algebra.traceMatrix ℤ a)) m) p
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one,
    mul_zero] at h
  rw [← h]

  simp only [dualScaled, Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul,
  Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem trace_dualScaled_mul (m : J) (y : A) :
    Algebra.trace ℤ A (dualScaled a m * y) = a.repr y m * (Algebra.traceMatrix ℤ a).det := by
  conv_lhs => rw [← a.sum_repr y]

  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, trace_dualScaled_mul_basis,
  smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem eq_of_trace_mul_basis (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) {x y : A}
    (H : ∀ p, Algebra.trace ℤ A (x * a p) = Algebra.trace ℤ A (y * a p)) : x = y := by
  have hz : (fun q => a.repr (x - y) q) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hd
    funext p
    have h1 : Algebra.trace ℤ A ((x - y) * a p) = 0 := by
      rw [sub_mul, map_sub, H p, sub_self]
    conv at h1 => lhs; rw [← a.sum_repr (x - y)]

    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul] at h1
    simpa [Matrix.vecMul, dotProduct, Algebra.traceMatrix_apply, Algebra.traceForm_apply] using h1
  have : x - y = 0 := by
    apply a.repr.injective
    ext q
    simpa using congrFun hz q
  exact sub_eq_zero.mp this

theorem mul_dualScaled (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) (b : A) (n : J) :
    b * dualScaled a n = ∑ m, a.repr (b * a m) n • dualScaled a m := by
  apply eq_of_trace_mul_basis a hd
  intro p
  have h1 : b * dualScaled a n * a p = dualScaled a n * (b * a p) := by ring
  rw [h1, trace_dualScaled_mul]

  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, trace_dualScaled_mul,
  Module.Basis.repr_self, smul_eq_mul]
  simp [Finsupp.single_apply]

theorem sum_dualScaled_mul (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) :
    ∑ m, dualScaled a m * a m = (((Algebra.traceMatrix ℤ a).det : ℤ) : A) := by
  apply eq_of_trace_mul_basis a hd
  intro k
  have h1 : ∀ m, dualScaled a m * a m * a k = dualScaled a m * (a k * a m) := fun m => by ring
  have h2 : (((Algebra.traceMatrix ℤ a).det : ℤ) : A) * a k =
      (Algebra.traceMatrix ℤ a).det • a k := by rw [zsmul_eq_mul]

  rw [Finset.sum_mul, map_sum, h2, map_zsmul, Algebra.trace_eq_matrix_trace a (a k)]
  simp only [h1, trace_dualScaled_mul, Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem equivariant (hd : (Algebra.traceMatrix ℤ a).det ≠ 0)
    {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (ρ : A →+* Module.End Ω V) (σ : A →+* Ω) (b : A) (v : V) :
    ρ b (∑ m, σ (dualScaled a m) • ρ (a m) v) =
      σ b • ∑ m, σ (dualScaled a m) • ρ (a m) v := by
  have hmul : ∀ m, ρ b (ρ (a m) v) = ∑ n, ((a.repr (b * a m) n : ℤ) : Ω) • ρ (a n) v := by
    intro m
    have h0 : ρ b (ρ (a m) v) = ρ (b * a m) v := by simp [map_mul]
    rw [h0]
    conv_lhs => rw [← a.sum_repr (b * a m)]

    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have hc : ∀ n, σ b * σ (dualScaled a n) =
      ∑ m, σ (dualScaled a m) * ((a.repr (b * a m) n : ℤ) : Ω) := by
    intro n

    rw [← map_mul, mul_dualScaled a hd, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]

  simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc n, Finset.sum_smul]

end General

theorem exists_scaledCasimir :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (n : ℕ) (a c : Fin n → 𝓞 F), (∑ m, c m * a m = (((NumberField.discr F : ℤ) : 𝓞 F))) ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 F →+* Module.End Ω V) (σ : 𝓞 F →+* Ω) (b : 𝓞 F) (v : V), ρ b (∑ m, σ (c m) • ρ (a m) v) = σ b • ∑ m, σ (c m) • ρ (a m) v := by
  intro F _ _
  let a := Module.finBasis ℤ (𝓞 F)
  have hdet : (Algebra.traceMatrix ℤ a).det = NumberField.discr F := by
    rw [← Algebra.discr_def, NumberField.discr_eq_discr]
  have hd : (Algebra.traceMatrix ℤ a).det ≠ 0 := by
    rw [hdet]; exact NumberField.discr_ne_zero F
  refine ⟨_, a, dualScaled a, ?_, ?_⟩
  · rw [sum_dualScaled_mul a hd, hdet]
  · intro Ω _ V _ _ ρ σ b v
    exact equivariant a hd ρ σ b v

end GlobalTheory.CompanionTheory.Ar.ScaledCasimir
end

section

open Polynomial NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem map_charpoly_lmul_eq_prod_embeddings (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [Fintype (E →+* Ω)]
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom Ω) =
      ∏ s : E →+* Ω, (X - C (s (a : E))) := by
  classical
  let e := NumberField.RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* Ω) := by
    rw [← Module.finrank_eq_card_basis e, NumberField.RingOfIntegers.rank, ← hc,
      Nat.card_eq_fintype_card]
  let eqv := Fintype.equivOfCardEq hcard
  let P : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E →ₐ[ℤ] Ω :=
    fun j => ((eqv j).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  have hP : Function.Injective P := by
    intro i j hij
    apply eqv.injective
    apply IsFractionRing.injective_comp_algebraMap (A := 𝓞 E) (K := E) (L := Ω)
    show (eqv i).comp (algebraMap (𝓞 E) E) = (eqv j).comp (algebraMap (𝓞 E) E)
    ext x
    exact DFunLike.congr_fun hij x
  have h := GlobalTheory.map_charpoly_leftMulMatrix_eq_prod_algHom e hP a
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, algebraMap_int_eq] at h
  refine h.trans ?_
  exact Fintype.prod_equiv eqv _ _ fun j => rfl

theorem charpoly_lmul_splits_of_conjugates (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω]
    (K : Type) [Field K] (g : O →+* K) (hinj : Function.Injective (algebraMap O Ω))
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E)
    (hO : ∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) (a : 𝓞 E) :
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  classical
  haveI : Finite (E →+* Ω) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* Ω) := Fintype.ofFinite _
  have hO' : ∀ (s' : E →+* Ω) (a : 𝓞 E), ∃ y, algebraMap O Ω y = s' (a : E) :=
    fun s' a => RingHom.mem_range.mp (hO s' a)
  choose o ho using hO'
  have hΩ := GlobalTheory.CompanionTheory.Ar.Flat.DegZ.map_charpoly_lmul_eq_prod_embeddings E Ω hc a
  have hO2 : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom O) =
      ∏ s : E →+* Ω, (X - C (o s a)) := by
    apply Polynomial.map_injective (algebraMap O Ω) hinj
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap O Ω).comp (Int.castRingHom O)) (Int.castRingHom Ω), hΩ,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ho]
  have hK : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* Ω, (X - C (g (o s a))) := by
    rw [RingHom.ext_int (Int.castRingHom K) (g.comp (Int.castRingHom O)), ← Polynomial.map_map, hO2,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hK]
  exact Polynomial.Splits.prod fun s _ => Polynomial.Splits.X_sub_C _

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end

section


theorem _root_.GlobalTheory.T.prime_ideal_extension_local_domain : ∀ (R B : Type) [CommRing R] [IsDedekindDomain R] [CommRing B] [IsDomain B] [IsNoetherianRing B] (u : R →+* B), u.FiniteType → (∀ p : Ideal R, p.IsMaximal → ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u) → ∀ (f : B) (d : R), d ≠ 0 → (∀ m : Ideal B, m.IsMaximal → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O), (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧ Function.Injective (ψ.comp u) ∧ ∃ c, ψ f = ψ (u d) * c) → ∃ a, f = u d * a := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | exact GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | (intros; apply GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local <;> assumption)
end

section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem _root_.GlobalTheory.T.exists_element_same_prime_count : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I P : Ideal R), I ≠ ⊥ → P.IsPrime → P ≠ ⊥ → ∃ x ∈ I, x ≠ 0 ∧ (normalizedFactors (Ideal.span {x})).count P = (normalizedFactors I).count P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq | exact GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.maximal_ideal_membership_of_local : ∀ {K : Type} [Field K] (R : Subring K) [IsLocalRing R] (P : Ideal (integralClosure R K).toSubring), P.IsMaximal → ∀ (t : (integralClosure R K).toSubring), (t : K) ∈ R → (t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R)) := by
  first | exact @GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem <;> assumption)
end

section


theorem _root_.GlobalTheory.T.local_subring_integral_closure_max : ∀ {K : Type} [Field K] (R D B : Subring K) [IsLocalRing R] [IsLocalRing D], R ≤ D → (∀ r ∈ R, r ≠ 0 → r⁻¹ ∈ D → r⁻¹ ∈ R) → (integralClosure R K).toSubring ≤ D → B ≤ (integralClosure R K).toSubring → (∀ a ∈ D, ∃ u ∈ B, ∃ v ∈ B, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) → ∃ (P : Ideal (integralClosure R K).toSubring) (_ : P.IsMaximal), D = (LocalSubring.ofPrime _ P).toSubring ∧ ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
  first | exact @GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure | exact GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure | (intros; apply GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kaehler_finrank_fraction_field : ∀ (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T),
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = m := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | exact GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis <;> assumption)
end

section


theorem _root_.GlobalTheory.T.prime_mem_iff_not_unit_localization : ∀ {K : Type} [Field K] (T : Subring K) (P : Ideal T) (_ : P.IsPrime) (t : T), t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ (LocalSubring.ofPrime T P).toSubring) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem <;> assumption)
end

section


theorem _root_.GlobalTheory.T.smooth_map_localization_compat : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (A₀ : Subalgebra ℤ Ω₀)
    (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁), (∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) → φ.Smooth →
    ∀ h : Ω₀, h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀) → h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
      S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)) →
      T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω)) →
      ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | exact GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorsionChars

theorem exists_units_map_eq {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') (n : ℕ) [NeZero n]
    (v : Ω'ˣ) (hv : v ^ Nat.card (rootsOfUnity n Ω) = 1) :
    ∃ u : Ωˣ, Units.map (i : Ω →* Ω') u = v := by
  classical
  set m := Nat.card (rootsOfUnity n Ω) with hm
  haveI : NeZero m := ⟨Nat.card_pos.ne'⟩
  have hinj : Function.Injective (Units.map (i : Ω →* Ω')) :=
    Units.map_injective i.injective
  let f : rootsOfUnity n Ω → rootsOfUnity m Ω' := fun u =>
    ⟨Units.map (i : Ω →* Ω') u.1, by
      have h1 : (u : Ωˣ) ^ m = 1 := by
        have := congrArg Subtype.val (pow_card_eq_one' (x := u))
        rw [Subgroup.coe_pow, Subgroup.coe_one] at this
        exact this
      rw [mem_rootsOfUnity, ← map_pow, h1, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (hinj (congrArg Subtype.val hab))
  have hbij := hf.bijective_of_nat_card_le (card_rootsOfUnity Ω' m)
  obtain ⟨u, hu⟩ := hbij.2 ⟨v, by rw [mem_rootsOfUnity]; exact hv⟩
  exact ⟨u.1, congrArg Subtype.val hu⟩

theorem pow_right_of_mul {G M : Type} [CommGroup G] [CommGroup M] (n : ℕ) (χ : G → M)
    (hχ : ∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g')
    (g : G) (hg : g ^ n = 1) (k : ℕ) : χ (g ^ k) = χ g ^ k := by
  have h1 : χ 1 = 1 := by
    have := hχ 1 1 (one_pow n) (one_pow n)
    simpa using this
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hk : (g ^ k) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]
    rw [pow_succ, hχ _ _ hk hg, ih, pow_succ]

theorem chars_descend : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (C A : Type) [CommGroup C] [CommGroup A] (rel : A → C → Prop) (n : ℕ), 1 ≤ n →
  (∀ c : C, c ^ n = 1 → ∃ a : A, a ^ n = 1 ∧ rel a c) →
  (∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c) →
  (∀ a a' c c', rel a c → rel a' c' → rel (a * a') (c * c')) →
  (∀ a a' c, rel a c → rel a' c → a = a') →
  (∀ a c c', rel a c → rel a c' → c = c') →
  ∀ (e : C → C → Ωˣ) (e' : A → A → Ω'ˣ),
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g') →
  (∀ χ : C → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g) →
  (∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1) →
  (∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e' x (g * g') = e' x g * e' x g') →
  (∀ χ : A → Ω'ˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') → ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e' x g) →
  (∀ y' : A, y' ^ n = 1 → ∃ y : C, y ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) ∧
  (∀ y : C, y ^ n = 1 → ∃ y' : A, y' ^ n = 1 ∧ ∀ g g', g ^ n = 1 → g' ^ n = 1 → rel g' g → (e' y' g' : Ω') = i (e y g)) := by
  classical
  intro Ω Ω' _ _ i C A _ _ rel n hn hCA hAC hmul hinjA hinjC e e' emul eperf enondeg e'mul e'perf
  haveI : NeZero n := ⟨by omega⟩
  have hinj : Function.Injective (Units.map (i : Ω →* Ω')) :=
    Units.map_injective i.injective
  have hrel11 : rel 1 1 := by
    obtain ⟨a₀, -, h₀⟩ := hCA 1 (one_pow n)
    have h := hmul _ _ _ _ h₀ h₀
    rw [_root_.mul_one] at h
    have : a₀ * a₀ = a₀ := hinjA _ _ _ h h₀
    have h1 : a₀ = 1 := by simpa using this
    rwa [h1] at h₀
  have hrelpow : ∀ a c, rel a c → ∀ k : ℕ, rel (a ^ k) (c ^ k) := by
    intro a c h k
    induction k with
    | zero => simpa using hrel11
    | succ k ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
  refine ⟨?_, ?_⟩
  · intro y' hy'
    set m := Nat.card (rootsOfUnity n Ω) with hm
    have hCm : ∀ g : C, g ^ n = 1 → g ^ m = 1 := by
      intro g hg
      refine enondeg _ (by rw [← pow_mul, mul_comm, pow_mul, hg, one_pow]) ?_
      intro x hx
      rw [pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg m]
      have hmem : e x g ∈ rootsOfUnity n Ω := by
        rw [mem_rootsOfUnity, ← pow_right_of_mul n (e x) (fun g g' => emul x g g' hx) g hg n, hg]
        have := emul x 1 1 hx (one_pow n) (one_pow n)
        simpa using this
      have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨e x g, hmem⟩ : rootsOfUnity n Ω)))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    have hAm : ∀ a : A, a ^ n = 1 → a ^ m = 1 := by
      intro a ha
      obtain ⟨c, hc, hac⟩ := hAC a ha
      have h := hrelpow a c hac m
      rw [hCm c hc] at h
      exact hinjA _ _ _ h hrel11
    have hval : ∀ a : A, a ^ n = 1 → ∃ u : Ωˣ, Units.map (i : Ω →* Ω') u = e' y' a := by
      intro a ha
      apply exists_units_map_eq i n
      rw [← pow_right_of_mul n (e' y') (fun g g' => e'mul y' g g' hy') a ha m, hAm a ha]
      have := e'mul y' 1 1 hy' (one_pow n) (one_pow n)
      simpa using this
    have hpart : ∀ c : C, c ^ n = 1 → ∃ u : Ωˣ, ∃ a : A, a ^ n = 1 ∧ rel a c ∧
        Units.map (i : Ω →* Ω') u = e' y' a := by
      intro c hc
      obtain ⟨a, ha, hac⟩ := hCA c hc
      obtain ⟨u, hu⟩ := hval a ha
      exact ⟨u, a, ha, hac, hu⟩
    let χ : C → Ωˣ := fun c => if h : c ^ n = 1 then (hpart c h).choose else 1
    have hχ : ∀ c : C, c ^ n = 1 → ∀ a : A, a ^ n = 1 → rel a c →
        Units.map (i : Ω →* Ω') (χ c) = e' y' a := by
      intro c hc a ha hac
      obtain ⟨a₁, -, hrel, hu⟩ := (hpart c hc).choose_spec
      have : χ c = (hpart c hc).choose := dif_pos hc
      rw [this, hu, hinjA _ _ _ hrel hac]
    obtain ⟨y, hy, hye⟩ := eperf χ (by
      intro g g' hg hg'
      obtain ⟨a, ha, hag⟩ := hCA g hg
      obtain ⟨a', ha', hag'⟩ := hCA g' hg'
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      have haa : (a * a') ^ n = 1 := by rw [mul_pow, ha, ha', _root_.one_mul]
      apply hinj
      rw [map_mul, hχ _ hgg _ haa (hmul _ _ _ _ hag hag'), hχ _ hg _ ha hag, hχ _ hg' _ ha' hag',
        e'mul y' _ _ hy' ha ha'])
    refine ⟨y, hy, ?_⟩
    intro g g' hg hg' hrel
    rw [← hχ g hg g' hg' hrel, hye g hg]
    rfl
  · intro y hy
    have hpart : ∀ a : A, a ^ n = 1 → ∃ c : C, c ^ n = 1 ∧ rel a c := hAC
    let χ : A → Ω'ˣ := fun a =>
      if h : a ^ n = 1 then Units.map (i : Ω →* Ω') (e y (hpart a h).choose) else 1
    have hχ : ∀ a : A, a ^ n = 1 → ∀ c : C, rel a c →
        χ a = Units.map (i : Ω →* Ω') (e y c) := by
      intro a ha c hac
      have : χ a = Units.map (i : Ω →* Ω') (e y (hpart a ha).choose) := dif_pos ha
      rw [this, hinjC _ _ _ (hpart a ha).choose_spec.2 hac]
    obtain ⟨y', hy', hye⟩ := e'perf χ (by
      intro g g' hg hg'
      obtain ⟨c, hc, hgc⟩ := hAC g hg
      obtain ⟨c', hc', hgc'⟩ := hAC g' hg'
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      rw [hχ _ hgg _ (hmul _ _ _ _ hgc hgc'), hχ _ hg _ hgc, hχ _ hg' _ hgc',
        emul y _ _ hy hc hc', map_mul])
    refine ⟨y', hy', ?_⟩
    intro g g' hg hg' hrel
    rw [← hye g' hg', hχ g' hg' g hrel]
    rfl

end GlobalTheory.CompanionTheory.Ar.TorsionChars
end

section


theorem _root_.GlobalTheory.T.kaehler_basis_tower_alt : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] (e m : ℕ) (z : Fin e → S) (w : Fin m → T),
    LinearIndependent S (fun i => KaehlerDifferential.D R S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D R S (z i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) ∧
    Submodule.span T (Set.range fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | exact GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | (intros; apply GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower <;> assumption)
end
