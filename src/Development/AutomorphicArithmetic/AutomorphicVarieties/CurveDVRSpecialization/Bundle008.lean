module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.NumberTheory.NumberField.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem val_of_even {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {M : ℕ} (hM : Even M)
    (h : B.valuation ((4 : ℕ) : Ω) < 1) : B.valuation (M : Ω) < 1 := by
  have h2 : B.valuation (2 : Ω) < 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (1 : _) ≤ B.valuation (2 : Ω) * B.valuation (2 : Ω) := one_le_mul hc hc
    rw [← map_mul] at h4
    have : ((4 : ℕ) : Ω) = 2 * 2 := by norm_num
    rw [this] at h
    exact absurd h (not_lt.mpr h4)
  obtain ⟨k, rfl⟩ := hM
  have hk : B.valuation (k : Ω) ≤ 1 := by
    exact B.valuation_le_one (k : B)
  have : ((k + k : ℕ) : Ω) = 2 * (k : Ω) := by push_cast; ring
  rw [this, map_mul]
  exact mul_lt_one_of_lt_of_le h2 hk
end

section

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem norm_le_one_of_integral_padic (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l x hx

set_option linter.overlappingInstances false in
private theorem small_norm_on_maximal_ideal_power {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal A ^ n, ‖y z‖ < ε := by
  have hl0 : ((l : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : A) ≠ 0 := fun h => hl0 (by simpa using congrArg y h)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
  refine ⟨e * n, fun z hz => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  have hd : (l : A) ^ n ∣ z := by
    refine Dvd.dvd.trans ?_ hz
    rw [pow_mul, hu]
    exact pow_dvd_pow_of_dvd (Units.mul_left_dvd.2 dvd_rfl) n
  obtain ⟨w, rfl⟩ := hd
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle w)) hn

set_option linter.overlappingInstances false in
private theorem continuous_padic_embedding_rep {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {D : Type} [Group D] [TopologicalSpace D]
    (r : D →* GG (m := 3) (R := A))
    (h : UnitaryThreeInertia.AdicCont (maximalIdeal A) r) : Continuous fun g => (r g).mat.map y := by
  refine continuous_matrix fun a b => continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := small_norm_on_maximal_ideal_power y hle hε
  filter_upwards [(h n).eventually_eq g] with g' hg'
  rw [dist_eq_norm, Matrix.map_apply, Matrix.map_apply, ← map_sub]
  exact hn _ (Ideal.Quotient.eq.1 (congrFun (congrFun hg' a) b))

private theorem continuous_units_of_continuous_coe {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem orthogonal_pairing_from_intertwiner {R : Type} [CommRing R]
    {x y j : GG (m := 3) (R := R)} (hj : j.mat = 1) (hj' : j.right = -1)
    (hy : y.right = 1) (h : y * j = j * x) : x.mat.transpose * Jmat R 3 * y.mat = Jmat R 3 := by
  have h1 : j.left = 1 := Units.ext hj
  have h2 := congrArg SemidirectProduct.left h
  simp only [SemidirectProduct.mul_left, h1, hj', map_one, mul_one, one_mul, sgnAct_neg_one] at h2
  rw [GG.mat, GG.mat, h2, theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R 3) (Jmat R 3),
    Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
  simp

private theorem irreducible_of_scalar_multiples {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (U : Subgroup Γ) (a : Γ → Matrix (Fin 3) (Fin 3) k)
    (h : MatIrr U a) (r : Γ' →* GL (Fin 3) k) (hr : ∀ g ∈ U, ∃ s, ∃ t : k, a g = t • (r s).val) : Af.IsIrr r := by
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hi => h W fun g hg v hv => ?_⟩
  obtain ⟨s, t, e⟩ := hr g hg
  rw [e, Matrix.smul_mulVec]
  exact W.smul_mem t (hi s v hv)
end

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem fix_iff {K Ω : Type} [Field K] [NumberField K] [Field Ω] [CharZero Ω] (hK : Module.finrank ℚ K = 2)
    (f g : K →+* Ω) (s : Ω ≃ₐ[ℚ] Ω) (h : ∀ x, s (f x) = f x) (x : K) : s (g x) = g x := by
  by_cases hq : ∃ q : ℚ, (q : K) = x
  · obtain ⟨q, rfl⟩ := hq
    simp only [map_ratCast]
  · have hli : LinearIndependent ℚ ![(1 : K), x] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      by_cases hb : b = 0
      · subst hb
        simp at hab
        exact ⟨hab, rfl⟩
      · exfalso
        apply hq
        refine ⟨-a / b, ?_⟩
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
        have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
        push_cast
        rw [div_eq_iff hb']
        linear_combination -hab
    have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hK])
    have hmem : x * x ∈ Submodule.span ℚ (Set.range ![(1 : K), x]) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair] at hmem
    obtain ⟨a, b, hab⟩ := hmem
    rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
    have hg : g x * g x = a + b * g x := by
      rw [← map_mul, ← hab, map_add (f := _), map_mul, map_ratCast, map_ratCast]
    have hf : f x * f x = a + b * f x := by
      rw [← map_mul, ← hab, map_add (f := _), map_mul, map_ratCast, map_ratCast]
    have hprod : (g x - f x) * (g x - ((b : Ω) - f x)) = 0 := by
      linear_combination hg - hf
    rcases mul_eq_zero.mp hprod with h1 | h1
    · rw [sub_eq_zero.mp h1, h x]
    · have h2 : g x = f ((b : K) - x) := by
        rw [sub_eq_zero.mp h1, map_sub, map_ratCast]
      rw [h2, h]
end
