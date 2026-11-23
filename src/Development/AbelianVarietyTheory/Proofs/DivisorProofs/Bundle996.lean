module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.HomExtendsOverDVR
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory

theorem card_embeddings_restrict_eq_finrank (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    [Algebra k k'] (τ : k →+* ℂ) :
    Nat.card {σ : k' →+* ℂ // σ.comp (algebraMap k k') = τ} = Module.finrank k k' := by
  letI : Algebra k ℂ := τ.toAlgebra
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  rw [← AlgHom.card k k' ℂ, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun σ => { σ.1 with commutes' := fun x => RingHom.congr_fun σ.2 x },
    fun φ => ⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩, fun σ => rfl, fun φ => rfl⟩

theorem finrank_mul_sum_embeddings_comp (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    (i : k →+* k') (f : (k →+* ℂ) → ℝ) :
    (Module.finrank ℚ k : ℝ) * ∑ σ : k' →+* ℂ, f (σ.comp i)
      = (Module.finrank ℚ k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
  classical
  letI : Algebra k k' := i.toAlgebra
  have h1 : ∑ σ : k' →+* ℂ, f (σ.comp i) = (Module.finrank k k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : k' →+* ℂ => σ.comp i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f τ) (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
      Finset.sum_const, nsmul_eq_mul, ← card_embeddings_restrict_eq_finrank k k' τ,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [h1, ← _root_.mul_assoc, ← Module.finrank_mul_finrank ℚ k k', Nat.cast_mul]

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM Polynomial

theorem dvd_of_smul_end_eq_smul {R M : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] (f : Module.End R M) {a b : R} (ha : a ≠ 0)
    (h : ∀ x, a • f x = b • x) {x₀ : M} (hx₀ : x₀ ≠ 0) : a ∣ b := by
  obtain ⟨P, hP, hf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (i : ℕ) (x : M), a ^ i • (f ^ i) x = b ^ i • x := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      intro x
      rw [pow_succ f, Module.End.mul_apply, pow_succ' a, mul_smul, ih, smul_comm, h, pow_succ, mul_smul]
  have h0 : (P.scaleRoots a).eval b = 0 := by
    have h1 : (P.scaleRoots a).eval b • x₀ = a ^ P.natDegree • (aeval f P) x₀ := by
      rw [eval_eq_sum_range, aeval_eq_sum_range, natDegree_scaleRoots, Finset.sum_smul, LinearMap.sum_apply,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [coeff_scaleRoots, mul_smul, ← hpow, LinearMap.smul_apply, smul_smul, smul_smul, mul_assoc,
        pow_sub_mul_pow a hi', mul_comm]
    rw [hf, LinearMap.zero_apply, smul_zero, smul_eq_zero] at h1
    exact h1.resolve_right hx₀
  let K := FractionRing R
  have ha' : algebraMap R K a ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hc : algebraMap R K a * (algebraMap R K b / algebraMap R K a) = algebraMap R K b :=
    mul_div_cancel₀ _ ha'
  have hint : _root_.IsIntegral R (algebraMap R K b / algebraMap R K a) := by
    refine ⟨P, hP, ?_⟩
    have h2 := scaleRoots_eval₂_mul (p := P) (algebraMap R K) (algebraMap R K b / algebraMap R K a) a
    rw [hc, eval₂_at_apply, h0, map_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (pow_ne_zero _ ha')
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨g, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hg, hc]

theorem exists_smul_of_rank_one (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (h : D.p + D.q = 1) (γ : D.La →+ D.La) (hγ : ∀ (s : 𝓞 E) (x : D.La), γ (s • x) = s • γ x) :
    ∃ g : 𝓞 E, ∀ x, γ x = g • x := by
  have := D.fin
  have := D.proj
  have hr : Module.finrank (𝓞 E) D.La = 1 := D.rank.trans h
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : D.La)
  obtain ⟨a, b, ha, hab⟩ := CMLat.exists_smul_eq_smul hr hx₀ (γ x₀)
  have key : ∀ x, a • γ x = b • x := fun x => by
    obtain ⟨r, s, hr0, e⟩ := CMLat.exists_smul_eq_smul hr hx₀ x
    have h1 : r • (a • γ x - b • x) = 0 := by
      rw [smul_sub, smul_comm r a, ← hγ, e, hγ, smul_comm a s, hab, smul_comm r b, e, smul_comm s b, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left hr0)
  let f : Module.End (𝓞 E) D.La := { toFun := γ, map_add' := γ.map_add, map_smul' := hγ }
  obtain ⟨g, rfl⟩ := dvd_of_smul_end_eq_smul f ha key hx₀
  refine ⟨g, fun x => ?_⟩
  have h1 : a • (γ x - g • x) = 0 := by rw [smul_sub, key, mul_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left ha)

end GlobalTheory.FlatCM

end
end
