module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle124
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle163
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem coneval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  intro V _ _ _ r m N n hn ε s₁ s₂ ga h1m h1u h2m h2u hprod
  classical
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  let ℓ : FractionRing V → ℤ := fun x => WithZero.log (v x)
  have hinj := IsFractionRing.injective V (FractionRing V)
  have hne : ∀ x : V, x ≠ 0 → algebraMap V (FractionRing V) x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ hinj).2 hx
  have hv0 : ∀ x : FractionRing V, x ≠ 0 → v x ≠ 0 := fun x hx => (Valuation.ne_zero_iff v).2 hx
  have ℓmul : ∀ x y : FractionRing V, x ≠ 0 → y ≠ 0 → ℓ (x * y) = ℓ x + ℓ y := fun x y hx hy => by
    simp only [ℓ, map_mul, WithZero.log_mul (hv0 x hx) (hv0 y hy)]
  have ℓzpow : ∀ (x : FractionRing V) (z : ℤ), ℓ (x ^ z) = z * ℓ x := fun x z => by
    simp only [ℓ, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  have ℓprod : ∀ (J : Type) (t : Finset J) (g : J → FractionRing V), (∀ i, g i ≠ 0) →
      ℓ (∏ i ∈ t, g i) = ∑ i ∈ t, ℓ (g i) := by
    intro J t g hg
    induction t using Finset.induction_on with
    | empty => simp [ℓ]
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ℓmul _ _ (hg j)
        (Finset.prod_ne_zero_iff.2 fun i _ => hg i), ih]
  have hunit : ∀ x : V, IsUnit x → ℓ (algebraMap V (FractionRing V) x) = 0 := by
    intro x hx
    have h1 : v (algebraMap V (FractionRing V) x) = 1 := by
      refine le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ x) ?_
      by_contra hlt
      have := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).1 (lt_of_not_ge hlt)
      exact (IsLocalRing.mem_maximalIdeal x).1 this hx
    simp only [ℓ, h1, WithZero.log_one]
  have hneg : ∀ x : V, x ∈ maximalIdeal V → x ≠ 0 → ℓ (algebraMap V (FractionRing V) x) < 0 := by
    intro x hm hx
    have h1 : v (algebraMap V (FractionRing V) x) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).2 hm
    have := (WithZero.log_lt_log (hv0 _ (hne x hx)) one_ne_zero).2 h1
    simpa [ℓ, WithZero.log_one] using this
  have hs0 : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ i, algebraMap V (FractionRing V) (s i) ≠ 0 := by
    intro s hm hu i
    rcases i with k | k
    · exact hne _ (hm k).2
    · exact hne _ (hu k).ne_zero
  have hsum : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ z : (Fin m ⊕ Fin N) → ℤ,
      ℓ (∏ i, algebraMap V (FractionRing V) (s i) ^ z i) =
        ∑ k, z (.inl k) * ℓ (algebraMap V (FractionRing V) (s (.inl k))) := by
    intro s hm hu z
    rw [ℓprod _ _ _ (fun i => zpow_ne_zero _ (hs0 s hm hu i)), Fintype.sum_sum_type]
    simp only [ℓzpow, hunit _ (hu _), mul_zero, Finset.sum_const_zero, add_zero]
  let c₁ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))).toNat
  let c₂ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))).toNat
  have hc₁ : ∀ k, (c₁ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₁ (.inl k))) := fun k => by
    have := hneg _ (h1m k).1 (h1m k).2
    simp only [c₁]; omega
  have hc₂ : ∀ k, (c₂ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₂ (.inl k))) := fun k => by
    have := hneg _ (h2m k).1 (h2m k).2
    simp only [c₂]; omega
  refine ⟨c₁, c₂, fun k => ?_, fun k => ?_, ?_⟩
  · have := hc₁ k; have := hneg _ (h1m k).1 (h1m k).2; omega
  · have := hc₂ k; have := hneg _ (h2m k).1 (h2m k).2; omega
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  obtain ⟨u, hu⟩ := hprod a b
  have key := congrArg ℓ hu
  rw [ℓmul _ _ (hne _ u.ne_zero) (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs0 s₁ h1m h1u i)),
    hunit _ u.isUnit, zero_add, hsum s₂ h2m h2u, hsum s₁ h1m h1u] at key
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul]
  beta_reduce at key
  have key' : (n:ℤ) * ∑ k, ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = (n:ℤ) * ∑ k, ((c₁ k:ℤ) * ε (.inl k) a b) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = -((n:ℤ) * ε (.inl k) (ga a) (ga b) * ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))) by rw [hc₂]; ring),
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₁ k : ℤ) * ε (.inl k) a b) = -((n:ℤ) * ε (.inl k) a b * ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))) by rw [hc₁]; ring),
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, key]
  have := (mul_left_cancel₀ hn' key').symm
  exact this

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

open GlobalTheory.Poinc

theorem cone_gen_mem_of_common {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {r r' : ℕ} {ζ : Fin r → LinearMap.BilinForm ℤ X}
    {ζ' : Fin r' → LinearMap.BilinForm ℤ X} (hζ : IsCone bar φ ζ) (hζ' : IsCone bar φ ζ') (c : Fin r → ℕ)
    (c' : Fin r' → ℕ) (hc : ∀ j, 0 < c j) (he : ∑ j, c j • ζ j = ∑ j, c' j • ζ' j) (j : Fin r) :
    ∃ j', ζ j = ζ' j' := by
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hζ.mem hζ.nonneg hζ.linear hζ' c c' he j (hc j)
  have hd' : ∑ i, d i • ζ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • ζ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • ζ' i = ∑ l, e l • ζ l :=
    fun i hi => intCone_absorb hζ'.mem hζ'.nonneg hζ'.linear hζ d _ hd' i hi
  obtain ⟨f, hf⟩ := hζ.basis.exists_dual
  obtain ⟨g, hg⟩ := hζ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨ζ l, hζ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨ζ' i, hζ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0

    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • ζ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hζ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG

    rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE

    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, _root_.mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← _root_.mul_assoc, ← h2, _root_.mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, _root_.mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

theorem coneSum_eq : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' →
    ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) →
    ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  intro φ X _ _ m m' δ δ' hδ hδ' c c' hc hc' he
  classical
  have h1 : ∀ k, ∃ j, δ k = δ' j := cone_gen_mem_of_common hδ hδ' c c' hc he
  have h2 : ∀ j, ∃ k, δ' j = δ k := cone_gen_mem_of_common hδ' hδ c' c hc' he.symm
  have himg : Finset.univ.image δ = Finset.univ.image δ' := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨j, hj⟩ := h1 k
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := h2 j
      exact ⟨k, hk.symm⟩
  have e1 : ∑ x ∈ Finset.univ.image δ, x = ∑ k, δ k :=
    Finset.sum_image fun a _ b _ h => hδ.injective h
  have e2 : ∑ x ∈ Finset.univ.image δ', x = ∑ k, δ' k :=
    Finset.sum_image fun a _ b _ h => hδ'.injective h
  rw [← e1, ← e2, himg]

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_integral_gauge_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)), ∃ (N' : GlobalTheory.Ex.NumD (Kb R)) (ν' : GlobalTheory.Ex.NumOf D.toPre (Kb R) N') (q' : N'.QT (m ^ 2)) (S : Subalgebra R (Kb R)), ν'.th = ν.th ∧ ν'.QPt p q' ∧ Module.Finite R S ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x'' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.θ x x' x'' : Kb R) ∈ S ∧ (((N'.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.σ x : Kb R) ∈ S ∧ (((N'.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ χ, N'.th (N'.c χ * (q'.1.2 ^ m).b) ∈ S) ∧ (∀ χ, (N'.ψ χ : Kb R) ∈ S) ∧ ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N'.ψ χ}.Finite := by
  first | exact @GlobalTheory.FinGauge.gauge | exact GlobalTheory.FinGauge.gauge | (intros; apply GlobalTheory.FinGauge.gauge <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OneTraitTheta

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso GlobalTheory.LabTrans
open GlobalTheory.PsiEvenPull (proj)

theorem exists_values_iso (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (hF : Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') : ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨th', h₁, h₂⟩ := GeneratorPull.exists_generator_pull hL R R' φ D.P D'.P _ hD.w (pull_grp hD) hD.w_gen ν.th ν.th_gen
  obtain ⟨c, hc⟩ := ν'.th_gen th'
  obtain ⟨c', hc'⟩ := h₁ ν'.th
  have key : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) th' x.left z ν'.J := fun x =>
    h₂ (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  have k₁ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc (show Sp F ⟶ _ from x.left) z (good ν' z)
  have k₂ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc' (show Sp F ⟶ _ from x.left) z (good ν' z)
  by_cases h : c = 0
  · subst h
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z 1 fun x => ?_
    have e₁ := k₁ x
    rw [GenSecField.cst_zero', zero_mul] at e₁
    have e₂ := k₂ x
    rw [e₁, mul_zero] at e₂
    exact ((key x).trans ((congrArg _ e₁).trans (mul_zero _))).trans ((congrArg _ e₂).trans (mul_zero _)).symm
  · let u : (FractionRing R')ˣ := Units.mk0 (algebraMap R' _ c) fun e =>
      h (IsFractionRing.injective R' (FractionRing R') (e.trans (map_zero _).symm))
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z (TauTwist.unitAt (Z := Sp F) (jFK (R := R') F) z u) fun x => ?_
    refine ((key x).trans (congrArg _ (k₁ x))).trans ((_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (· * ·) ?_ rfl))
    rw [Units.val_mul, TauTwist.unitAt_val]
    refine (_root_.mul_comm _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    exact (congrArg (fun q => cst (Z := Sp F) q z c) (Over.w x)).trans
      (cst_comp (Z := Sp F) (jFK (R := R') F) (algebraMap R' (FractionRing R')) z c)

theorem exists_scalar {K C I : Type} [Field K] [Field C] (f : K →+* C) {v t : I → K} (s : Cˣ)
    (h : ∀ i, f (v i) = s * f (t i)) : ∃ c : K, c ≠ 0 ∧ ∀ i, v i = c * t i := by
  by_cases h₀ : ∀ i, t i = 0
  · exact ⟨1, one_ne_zero, fun i => f.injective (by rw [h, h₀]; simp)⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h₀
    have hi' : f (t i) ≠ 0 := (map_ne_zero f).2 hi
    have e : f (v i / t i) = s := by rw [map_div₀, h, mul_div_cancel_right₀ _ hi']
    exact ⟨v i / t i, fun h₁ => s.ne_zero (by rw [← e, h₁, map_zero]), fun l => f.injective (by rw [map_mul, e, h])⟩

theorem isThetaPt_descend (hL : Laws) (hL₂ : Laws2) {S S' : Scheme.{0}} [IsLocallyNoetherian S] [IsLocallyNoetherian S']
    {P : PolAV S} {P' : PolAV S'} {f : S' ⟶ S} {a : P'.A.left ⟶ P.A.left} (hp : IsGrpPullback P'.A P.A f a)
    (hw : LBIso P'.L (P.L.pull a)) {K C : Type} [Field K] [Field C] [IsAlgClosed C] (em : K →+* C) (s : Sp K ⟶ S)
    (s' : Sp C ⟶ S') (hs : spMap em ≫ s = s' ≫ f) {m : ℕ} (hm : Odd m) (hmK : (m : K) ≠ 0) {I : Type}
    (x : I → (Over.mk s ⟶ P.A)) (x' : I → (Over.mk s' ⟶ P'.A)) (hx : ∀ i, (x' i).left ≫ a = spMap em ≫ (x i).left)
    (hk : ∀ i, x' i ^ m ^ 2 = 1) {w : I → C} (hw' : IsThetaPt P' m x' fun i => fnOf (w i)) {v : I → K} (c : Cˣ)
    (hv : ∀ i, em (v i) = c * w i) : IsThetaPt P m x fun i => fnOf (v i) := by
  have hmC : (m : C) ≠ 0 := by rw [← map_natCast em]; exact (map_ne_zero em).2 hmK
  let U : Over.mk (s' ≫ f) ⟶ Over.mk s := Over.homMk (spMap em) hs
  obtain ⟨e, he⟩ : ∃ e : (Over.mk s' ⟶ P'.A) ≃* (Over.mk (s' ≫ f) ⟶ P.A), ∀ y, (e y).left = y.left ≫ a :=
    LiePull.exists_pushEquiv hp (Over.mk s') _ rfl
  have hU : ∀ i, U ≫ x i = e (x' i) := fun i => Over.OverMorphism.ext ((hx i).symm.trans (he _).symm)
  have hkU : ∀ i, (U ≫ x i) ^ m ^ 2 = 1 := fun i => by rw [hU, ← map_pow, hk, map_one]
  have hkx : ∀ i, x i ^ m ^ 2 = 1 := fun i => by
    letI := em.toAlgebra
    haveI : Flat (spMap em) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K C)
    haveI : Surjective (spMap em) := ⟨fun p => ⟨(⊥ : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap em) := Flat.epi_of_flat_of_surjective (spMap em)
    have E : U ≫ (x i ^ m ^ 2) = U ≫ 1 := by rw [MonObj.comp_pow, hkU, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi (spMap em)).1 (congrArg (fun q => q.left) E))
  obtain ⟨t, ht⟩ := Specialise.exists_isThetaPt_local hL hL₂ P s hm (IsUnit.mk0 _ hmK) x hkx
  have T₁ := Specialise.isThetaPt_map hL₂ P em hs ht
  have T₂ := ((CoordSep.coord_exists_unique_separate hL C _ P (s' ≫ f) m hm hmC I (fun i => U ≫ x i) hkU).2.2.1
    fun i => em (t i)).1 T₁
  let τ : (Over.mk s').left ⟶ (Over.mk (s' ≫ f)).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have T₃ : IsCoordPt P' m x' 1 fun i => fnOf (em (t i)) :=
    FullExtend.isCoordPt_move τ hp hw τ (𝟙 _) (Category.comp_id _) (Category.id_comp _) (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id P.A P.isLB 1 (SecM.ofSec P.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (hx i).symm) hk (z := 1)
      ((Category.id_comp _).trans (by rw [← he, map_one])) T₂
  obtain ⟨-, h₂, h₃, -⟩ := CoordSep.coord_exists_unique_separate hL C _ P' s' m hm hmC I x' hk
  obtain ⟨d, hd⟩ := (h₂ 1 _ w T₃).1 ((h₃ w).1 hw')
  obtain ⟨c', hc', hv'⟩ := exists_scalar em (v := v) (t := t) (c * d) fun i => by
    rw [hv, hd, Units.val_mul, _root_.mul_assoc]; rfl
  rw [show v = fun i => c' * t i from funext hv']
  exact Specialise.isThetaPt_mul P ht hc'

theorem isThetaPt_of_series : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → ∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) := by
  intro R _ _ _ hR D A lab n hn ho _ hT j v hv
  obtain ⟨W, _, _, _, φ, G, _, _, D', A', U', hD, a, _, em₀, hW, iφ, lφ, hG, ⟨ga, hga, gp, lb⟩, c₀, H₀⟩ := hT
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have b₀ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hm : Odd (n ^ j) := ho.pow
  have hk : 1 ≤ (n ^ j) ^ 2 := pow_pos hm.pos 2
  generalize n ^ j = m at *
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp ga).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (hga r)
  have a₀K : algebraMap (FractionRing R) (Kb W) = (algebraMap (FractionRing W) (Kb W)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (hga r).symm))
  let jW : Kb W →ₐ[FractionRing W] C := ⟨gam, hgam⟩
  let jR : Kb W →ₐ[FractionRing R] C := ⟨gam, fun t => by rw [a₀K]; exact hgam (ga t)⟩
  have hCR : CExt R (maximalIdeal R) C :=
    ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
  obtain ⟨N', ν', -⟩ := ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial
  obtain ⟨J, hJX, hJ⟩ := exists_values_iso hL hD cC ν ν'
  obtain ⟨f, hf, hf'⟩ := GlobalTheory.TorsionIso.torsion_clause W _ b₀ D' A' G hG U' C (m ^ 2) hk
  have ex : ∀ i : QkPt D.toPre (Kb R) (m ^ 2), ∃ (p₁ : QkPt D.toPre C (m ^ 2)) (p' : QkPt D'.toPre C (m ^ 2))
      (x' : TFK (R := W) C ⟶ A'.A), QkExt (jR.comp em₀).toRingHom i p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
      IsPullGtF φ hD C p₁.g p'.g ∧ x'.left ≫ a = spMap (jR.comp em₀).toRingHom ≫ (lab _ i).left ∧
      QkToAkU U'.toUnifPre C (m ^ 2) p' x' := fun i => by
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ i
    obtain ⟨r, hr⟩ := exists_ext hB jR q₁
    let q₀ := pullQk hD hGF c₀ hB D'.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab _ i)
    have t₀ := H₀ _ hk i q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt hD hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ b₀ D' A' G hG U' _ C jW _ hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    refine ⟨r, q₀', x₀', qkExt_trans hq₁ hr, ?_,
      isPullGtF_ext hD cC jW.toRingHom jW.comp_algebraMap (isPullGtF_pullGt hD hGF c₀ _) hr hq₀', ?_,
      (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀⟩
    · rw [hq₀'.1, hr.1]; rfl
    · rw [hx₀', Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp]; rfl
  choose p₁ p' x' e₁ e₂ e₃ e₄ e₅ using ex
  have hGt := GlobalTheory.T.torus_torsion_points_correspond_values
  choose q hq using fun i => (((hGt R D.toPre D.psi_even hB C N ν).2.2.2.2 _).1 (p₁ i)).exists
  choose q' hq' using fun i => (((hGt W D'.toPre D'.psi_even D'.tau_bimult C N' ν').2.2.2.2 _).1 (p' i)).exists
  obtain ⟨s, hs⟩ := hv C hCR (jR.comp em₀) N ν p₁ q e₁ hq
  have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV hGt (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G hG U' C hC N' ν' m hm _ p' q' x' e₅ hq'
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  refine isThetaPt_descend hL hL₂ gp lb (jR.comp em₀).toRingHom (jFK (R := R) (Kb R)) (jFK (R := W) C) ?_ hm
    (Nat.cast_ne_zero.2 hm.pos.ne') (lab _) x' e₄ (fun i => ?_) Q (s * J.lam) fun i => ?_
  · exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap (jR.comp em₀).comp_algebraMap).trans (Geo.Tor.spMap_comp _ _))
  · rw [(hf.1 _ _).1 (e₅ i)]; exact hf' _
  · have e := (RelabelCoords.series_iso J hm (p := q' i) (p' := q i) (ν.eX.injective (by
      rw [hJX, (hq i).1, (hq' i).1, e₂, AddEquiv.apply_symm_apply])) (hJ _ _ _ _ (hq i).2 (hq' i).2 (e₃ i))).1
    rw [e, Units.val_mul, _root_.mul_assoc, Units.mul_inv_cancel_left]
    exact hs i

end GlobalTheory.Mum.OneTraitTheta

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_product_coordinate_independent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  first | exact @GlobalTheory.Mum.Near.closed_product_unique | exact GlobalTheory.Mum.Near.closed_product_unique | (intros; apply GlobalTheory.Mum.Near.closed_product_unique <;> assumption)
end
