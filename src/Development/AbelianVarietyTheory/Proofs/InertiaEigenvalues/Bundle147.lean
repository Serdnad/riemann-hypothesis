module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle131
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleInvolutiveAlgebraSplittingSmaller
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle132
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Field.ProperSpace
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem intO_lift_of_val_nonneg (K : UQ) (x : K.E) (h : 0 ≤ val K.O x) : ∃ a : K.O, algebraMap K.O K.E a = x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  unfold val at h
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem intO_val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  have h1 := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem intO_val_ne_zero_of_mem (K : UQ) (a : K.O) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal K.O) :
    val K.O (algebraMap K.O K.E a) ≠ 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha0
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

theorem intO : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O,
    @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  intro K K' d φ hU hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfr : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure K.O K'.E
  haveI : Module.Finite K.O S := IsIntegralClosure.finite K.O K.E K'.E S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain K.O K.E K'.E S
  haveI : IsFractionRing S K'.E := IsIntegralClosure.isFractionRing_of_finite_extension K.O K.E K'.E S
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := K.O) S
  have hinj : Function.Injective (algebraMap K.O S) :=
    algebraMap_injective_of_field_isFractionRing K.O S K.E K'.E
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField K.O (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).1
    (inferInstance : IsDedekindDomain S)

  have hv : ∀ a : K.O, 0 ≤ val K'.O (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hU.2.2.1]; exact intO_val_algebraMap_nonneg K a
  choose ψf hψf using fun a : K.O => intO_lift_of_val_nonneg K' _ (hv a)
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let ψ : K.O →+* K'.O :=
    { toFun := ψf
      map_one' := hinj' (by rw [hψf]; simp)
      map_mul' := fun a b => hinj' (by simp [hψf])
      map_zero' := hinj' (by rw [hψf]; simp)
      map_add' := fun a b => hinj' (by simp [hψf]) }
  have hψ : ∀ a, algebraMap K'.O K'.E (ψ a) = algebraMap K.O K'.E a := fun a => hψf a

  have hS : ∀ t : K'.E, IsIntegral K.O t → ∃ z : K'.O, algebraMap K'.O K'.E z = t := by
    intro t ht
    have : IsIntegral K'.O t :=
      IsIntegral.map_of_comp_eq (T := K'.O) (U := K'.E) ψ (RingHom.id K'.E) (by ext a; exact hψ a) ht
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  set x := algebraMap K'.O K'.E y with hx
  rcases ValuationRing.isInteger_or_isInteger S x with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]; exact s.2
  by_cases hx0 : x = 0
  · rw [hx0]; exact isIntegral_zero
  by_cases hsu : IsUnit s
  · have hu1 : ((hsu.unit⁻¹ : Sˣ) : S) * s = 1 := by
      have := hsu.unit.inv_mul; rwa [IsUnit.unit_spec] at this
    have e : algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) * algebraMap S K'.E s = 1 := by
      rw [← map_mul, hu1, map_one]
    have : x = algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) := by
      rw [eq_inv_of_mul_eq_one_left e, hs, inv_inv]
    rw [this]; exact ((hsu.unit⁻¹ : Sˣ) : S).2
  exfalso
  have hall : ∀ n : Ideal S, n.IsMaximal → s ∈ n := fun n hn => by
    rw [IsLocalRing.eq_maximalIdeal hn]; exact (mem_maximalIdeal s).2 hsu
  obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := K.O) S s hall
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hN
  obtain ⟨t, ht⟩ := hN
  obtain ⟨z, hz⟩ := hS _ t.2
  have h1 : algebraMap K'.O K'.E (y ^ N * (ψ π * z)) = 1 := by
    have := congrArg (algebraMap S K'.E) ht
    rw [map_mul, map_pow, hs, ← IsScalarTower.algebraMap_apply] at this
    have h' : (t : K'.E) * algebraMap K.O K'.E π = x⁻¹ ^ N := this
    rw [map_mul, map_pow, map_mul, hψ, hz, ← hx, mul_comm (algebraMap K.O K'.E π), h', ← mul_pow,
      mul_inv_cancel₀ hx0, one_pow]
  have hu : IsUnit (ψ π) := by
    have : y ^ N * (ψ π * z) = 1 := hinj' (by rw [h1, map_one])
    exact IsUnit.of_mul_eq_one (z * y ^ N) (by rw [← this]; ring)
  have h2 := GlobalTheory.UnitLemma.Orbit.val_unit (K := K') _ hu
  rw [hψ] at h2
  have h3 := hU.2.2.1 (algebraMap K.O K.E π)
  change val K'.O (φ (algebraMap K.O K.E π)) = 0 at h2
  rw [h3] at h2
  exact intO_val_ne_zero_of_mem K π hπ.ne_zero hπ.not_isUnit h2

end GlobalTheory.UnitLemma.Unr
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.NormVal

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

section Gen

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]

theorem val_mul' {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : val O (x * y) = val O x + val O y := by
  unfold val
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation E y ≠ 0 := by simpa using hy
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

theorem val_one' : val O (1 : E) = 0 := by simp [val]

theorem val_pow' {x : E} (hx : x ≠ 0) (k : ℕ) : val O (x ^ k) = k * val O x := by
  induction k with
  | zero => simp [val_one']
  | succ k ih =>
    rw [pow_succ, val_mul' O (pow_ne_zero _ hx) hx, ih]
    push_cast; ring

theorem val_inv' {x : E} (hx : x ≠ 0) : val O x⁻¹ = -val O x := by
  have := val_mul' O hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, val_one'] at this
  omega

theorem exists_lift_of_val_eq_zero {x : E} (hx : x ≠ 0) (h : val O x = 0) : ∃ a : O, algebraMap O E a = x := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation E x = 1 := by
    unfold val at h
    rw [← WithZero.exp_log hx']
    have : WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x) = 0 := by omega
    rw [this, WithZero.exp_zero]
  exact IsDiscreteValuationRing.exists_lift_of_le_one h1.le

theorem val_algebraMap_unit (a : O) (ha : IsUnit a) : val O (algebraMap O E a) = 0 := by
  unfold val
  have : (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (IsLocalRing.mem_maximalIdeal a).1 h ha
  rw [this]; simp

theorem exists_val_eq_one : ∃ π : E, val O π = 1 := by
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal O).valuation_exists_uniformizer E
  exact ⟨π, by simp [val, hπ]⟩

end Gen

theorem norm_integral (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hφ : IsUnrExt K K' d φ) (hd : 0 < d) (z : K'.O) :
    ∃ a : K.O, algebraMap K.O K.E a = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt K K' d φ hφ hd
  have hwj : ∀ j, ∃ c : K'.O, algebraMap K'.O K'.E c = w j := by
    intro j
    refine (hw (w j)).2 fun k => ?_
    rw [w.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  have hM : ∀ i j, ∃ m : K.O, algebraMap K.O K.E m = Algebra.leftMulMatrix w (algebraMap K'.O K'.E z) i j := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    obtain ⟨c, hc⟩ := hwj j
    refine (hw _).1 ⟨z * c, ?_⟩ i
    rw [map_mul, hc]
  choose M hM using hM
  refine ⟨(Matrix.of M).det, ?_⟩
  rw [Algebra.norm_eq_matrix_det w, RingHom.map_det]
  congr 1
  ext i j
  simp [hM]

theorem normval : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by
  intro K K' d φ hφ hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hfr : Module.finrank K.E K'.E = d := hφ.2.2.2.2
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (hfr ▸ hd)
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero]
    simp [val]
  obtain ⟨π, hπ⟩ := exists_val_eq_one K.O (E := K.E)
  have hπ0 : π ≠ 0 := by rintro rfl; simp [val] at hπ
  have hφπ : val K'.O (φ π) = 1 := by rw [hφ.2.2.1, hπ]
  have hφπ0 : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
  set n := val K'.O y with hn
  set a := (-n).toNat
  set b := n.toNat
  have hab : (b : ℤ) - a = n := Int.toNat_sub_toNat_neg n
  set u := y * φ π ^ a * (φ π ^ b)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0))
  have hvu : val K'.O u = 0 := by
    rw [hu, val_mul' _ (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0)),
      val_mul' _ hy (pow_ne_zero _ hφπ0), val_inv' _ (pow_ne_zero _ hφπ0), val_pow' _ hφπ0, val_pow' _ hφπ0, hφπ, ← hn]
    omega
  have hvu' : val K'.O u⁻¹ = 0 := by rw [val_inv' _ hu0, hvu]; rfl
  obtain ⟨u₁, hu₁⟩ := exists_lift_of_val_eq_zero K'.O hu0 hvu
  obtain ⟨u₂, hu₂⟩ := exists_lift_of_val_eq_zero K'.O (inv_ne_zero hu0) hvu'
  obtain ⟨m₁, hm₁⟩ := norm_integral K K' d φ hφ hd u₁
  obtain ⟨m₂, hm₂⟩ := norm_integral K K' d φ hφ hd u₂
  have hunit : IsUnit m₁ := by
    have h12 : m₁ * m₂ = 1 := by
      apply IsFractionRing.injective K.O K.E
      rw [map_mul, hm₁, hm₂, hu₁, hu₂, ← map_mul, mul_inv_cancel₀ hu0, map_one, map_one]
    exact IsUnit.of_mul_eq_one m₂ h12
  have hNu : val K.O (Algebra.norm K.E u) = 0 := by
    rw [← hu₁, ← hm₁]; exact val_algebraMap_unit K.O m₁ hunit
  have hNu0 : Algebra.norm K.E u ≠ 0 := Algebra.norm_ne_zero_iff.2 hu0
  have hNy0 : Algebra.norm K.E y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have hNφ : Algebra.norm K.E (φ π) = π ^ d := by
    rw [← hfr]; exact Algebra.norm_algebraMap π
  have key : y * φ π ^ a = u * φ π ^ b := by
    rw [hu, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hφπ0), mul_one]
  have key2 := congrArg (fun x => val K.O (Algebra.norm K.E x)) key
  simp only [map_mul, map_pow, hNφ] at key2
  rw [val_mul' _ hNy0 (pow_ne_zero _ (pow_ne_zero _ hπ0)), val_mul' _ hNu0 (pow_ne_zero _ (pow_ne_zero _ hπ0)),
    val_pow' _ (pow_ne_zero _ hπ0), val_pow' _ (pow_ne_zero _ hπ0), val_pow' _ hπ0, hNu, hπ] at key2
  rw [← hab]
  push_cast at key2 ⊢
  linarith

end GlobalTheory.UnitLemma.Unr.NormVal
end
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  first | exact @GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum | exact GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum | (intros; apply GlobalTheory.UnitLemma.latPair_orbit_finite_and_sum <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  first | exact @GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | exact GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | (intros; apply GlobalTheory.JR.LinDesc.tm_isClosedEmbedding <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_descendedFunction : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  first | exact @GlobalTheory.JR.descFn_isTest | exact GlobalTheory.JR.descFn_isTest | (intros; apply GlobalTheory.JR.descFn_isTest <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_unit_leftMulMatrix_of_commute_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by
  first | exact @GlobalTheory.JR.LinDesc.centr | exact GlobalTheory.JR.LinDesc.centr | (intros; apply GlobalTheory.JR.LinDesc.centr <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Subsingleton A.K → WeilAt A := by
  first | exact @GlobalTheory.JR.weilAt_of_subsingleton | exact GlobalTheory.JR.weilAt_of_subsingleton | (intros; apply GlobalTheory.JR.weilAt_of_subsingleton <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K → ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧ Module.finrank F A₂.K < Module.finrank F A.K := by
  first | exact @GlobalTheory.JR.EtQuot.exists_splitting | exact GlobalTheory.JR.EtQuot.exists_splitting | (intros; apply GlobalTheory.JR.EtQuot.exists_splitting <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

namespace GlobalTheory.JR.WeilQuad.GaussTrans

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  intro F E _ _ _ _ U A ψ x μ ω hH t s ⟨ℓ, hℓ⟩ G ⟨Λ₀, ho₀, hc₀, hG⟩
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hs' : algebraMap A.K A.L (s : A.K) = ℓ * star ℓ := by rw [← hℓ, hN]
  have hu : IsUnit ℓ := isUnit_of_mul_isUnit_left (hs' ▸ (s.isUnit.map (algebraMap A.K A.L)))
  set u : A.Lˣ := hu.unit with hu_def
  have hul : (u : A.L) = ℓ := hu.unit_spec
  have hmod : distribHaarChar A.L u = distribHaarChar A.K s :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) u s
      (by rw [hul]; exact hs')
  have hmap : μ.map (fun y => u • y) = (distribHaarChar A.L u⁻¹ : ℝ≥0∞) • μ := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul u) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul]
  have hemb : MeasurableEmbedding (fun y : A.L => u • y) :=
    (Homeomorph.smul u).measurableEmbedding
  have key : ∀ Λ : AddSubgroup A.L, gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
      ((A.absK s : ℂ))⁻¹ * gaussInt A ψ x μ t (u • Λ : AddSubgroup A.L) := by
    intro Λ
    have h1 : gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
        ∫ y in (Λ : Set A.L), A.psiK ψ ((t : A.K) * x * A.NL (u • y)) ∂μ := by
      unfold gaussInt
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hNm : A.NL (u • y) = s * A.NL y := by
        rw [Units.smul_def, hul, smul_eq_mul]
        unfold Et.NL
        rw [map_mul]
        exact congrArg (· * _) hℓ
      simp only
      rw [hNm]
      push_cast; ring_nf
    have h2 := hemb.setIntegral_map (μ := μ) (fun z => A.psiK ψ ((t : A.K) * x * A.NL z)) ((u • Λ : AddSubgroup A.L) : Set A.L)
    have hpre : (fun y => u • y) ⁻¹' ((u • Λ : AddSubgroup A.L) : Set A.L) = Λ := by
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using (AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.1 h),
        fun h => AddSubgroup.smul_mem_pointwise_smul _ _ _ h⟩
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure] at h2
    rw [h1, ← h2]
    unfold gaussInt
    rw [Complex.real_smul, EtMeas.absK_unit, ENNReal.coe_toReal, map_inv, hmod]
    congr 1
    push_cast
    rfl
  have hcoe : ∀ (v : A.Lˣ) (M : AddSubgroup A.L), ((v • M : AddSubgroup A.L) : Set A.L) = v • (M : Set A.L) :=
    fun v M => AddSubgroup.coe_pointwise_smul v M
  refine ⟨u⁻¹ • Λ₀, ?_, ?_, fun Λ hoΛ hcΛ hle => ?_⟩
  · rw [hcoe]; exact ho₀.smul _
  · rw [hcoe]; exact hc₀.smul _
  · rw [key, hG (u • Λ) (by rw [hcoe]; exact hoΛ.smul _) (by rw [hcoe]; exact hcΛ.smul _) ?_, mul_comm]
    intro z hz
    have : u⁻¹ • z ∈ Λ := hle (AddSubgroup.smul_mem_pointwise_smul _ _ _ hz)
    exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 this

end GlobalTheory.JR.WeilQuad.GaussTrans
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaleTraceAddChar_norm_eq_one_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  first | exact @GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | exact GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | (intros; apply GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_linear_on_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  first | exact @GlobalTheory.JR.Hyp.pt_linear | exact GlobalTheory.JR.Hyp.pt_linear | (intros; apply GlobalTheory.JR.Hyp.pt_linear <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  first | exact @GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | exact GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | (intros; apply GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS <;> assumption)
end
