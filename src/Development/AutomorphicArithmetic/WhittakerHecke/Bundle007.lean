module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.GaloisValuations.Global
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.AddChar
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.exists_addChar_invariant_iff_finiteField_aut_eq_one :
    ∀ (K : Type) [Field K] [Finite K] (f : RingAut K), ∃ ψ : Multiplicative K →* ℂˣ, ∀ m : ℤ,
        (∀ x : K, ψ (Multiplicative.ofAdd ((f ^ m) x)) = ψ (Multiplicative.ofAdd x)) ↔ f ^ m = 1 := by
  intro K _ _ f
  classical
  haveI hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  haveI : NeZero (ringChar K) := ⟨hp.out.ne_zero⟩
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := Kˣ)
  let T : K →ₗ[ZMod (ringChar K)] ZMod (ringChar K) := Algebra.trace (ZMod (ringChar K)) K
  let χ : AddChar K ℂ :=
    ((ZMod.stdAddChar (N := ringChar K)).compAddMonoidHom T.toAddMonoidHom).mulShift (b : K)
  have hχ : ∀ x : K, χ x = ZMod.stdAddChar (T ((b : K) * x)) := fun x => rfl
  refine ⟨χ.toMonoidHom.toHomUnits, fun m => ⟨fun h => ?_, fun h x => by rw [h]; rfl⟩⟩
  generalize f ^ m = g at h ⊢
  have h1 : ∀ x : K, T ((b : K) * g x) = T ((b : K) * x) := by
    intro x
    apply ZMod.injective_stdAddChar
    rw [← hχ, ← hχ]
    exact congrArg Units.val (h x)
  have hT : ∀ y : K, T (g y) = T y := by
    intro y
    let e : K ≃ₐ[ZMod (ringChar K)] K := AlgEquiv.ofRingEquiv (f := g) (fun c => by
      have := RingHom.ext_zmod ((g : K →+* K).comp (algebraMap (ZMod (ringChar K)) K))
        (algebraMap (ZMod (ringChar K)) K)
      exact DFunLike.congr_fun this c)
    exact Algebra.trace_eq_of_algEquiv e y
  have h2 : g (b : K) = (b : K) := by
    by_contra hne
    have hne' : (b : K) - g (b : K) ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0).symm
    obtain ⟨y, hy⟩ := FiniteField.trace_to_zmod_nondegenerate K hne'
    apply hy
    obtain ⟨x, rfl⟩ := g.surjective y
    change T (((b : K) - g b) * g x) = 0
    rw [sub_mul, map_sub, h1, ← map_mul, hT, sub_self]
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hb (Units.mk0 x hx))
    have hxn : x = (b : K) ^ n := by
      rw [← Units.val_zpow_eq_zpow_val, hn]; rfl
    rw [hxn, map_zpow₀, h2]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

private theorem one_add_pow_expansion' {R : Type} [CommRing R] (z : R) (N : ℕ) :
    ∃ r : R, (1 + z) ^ N = 1 + N * z + z ^ 2 * r := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨n + r + z * r, ?_⟩
    rw [pow_succ, hr]; push_cast; ring

theorem UpperTheory.exists_unit_residue_logarithm_of_roots_of_unity :
    ∀ {C Γ K : Type} [Field C] [LinearOrderedCommGroupWithZero Γ] [Field K] (v : Valuation C Γ) (ϖ : C),
        ϖ ≠ 0 → v ϖ < 1 → (∀ x, v x < 1 → v x ≤ v ϖ) → ∀ (ρ : v.valuationSubring →+* K), Function.Surjective ρ →
        (∀ x : v.valuationSubring, ρ x = 0 ↔ v (x : C) < 1) → ∀ N : ℕ, 0 < N → (∀ z : K, z ≠ 0 → z ^ N = 1) → (N : K) = -1 →
        ∃ abelian₂ : Cˣ → K,
          (∀ a b : Cˣ, v (a : C) = 1 → v (b : C) = 1 → abelian₂ (a * b) = abelian₂ a + abelian₂ b) ∧
          (∀ y : K, ∃ a : Cˣ, v (a : C) = 1 ∧ abelian₂ a = y) ∧
          (∀ a : Cˣ, v ((a : C) - 1) < v ϖ → abelian₂ a = 0) ∧
          ∀ (i : C ≃+* C) (f : K ≃+* K), i ϖ = ϖ → (∀ x, v (i x) = v x) →
            (∀ (x y : v.valuationSubring), (y : C) = i x → ρ y = f (ρ x)) →
            ∀ a : Cˣ, v (a : C) = 1 → abelian₂ (Units.map i.toRingHom.toMonoidHom a) = f (abelian₂ a) := by
  intro C Γ K _ _ _ v ϖ h0 h1 hmax ρ hsurj hker N hN hpow hNK
  classical
  have hv0 : v ϖ ≠ 0 := by simpa using h0
  have hvpos : 0 < v ϖ := zero_lt_iff.mpr hv0
  let abelian₂ : Cˣ → K := fun a =>
    if hy : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring then ρ ⟨_, hy⟩ else 0
  have hlt : ∀ a : C, v a = 1 → v (a ^ N - 1) < 1 := by
    intro a ha
    have hm : a ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact ha.le
    have hne : ρ ⟨a, hm⟩ ≠ 0 := by
      intro h
      have := (hker _).1 h
      simp [ha] at this
    have h2 : ρ ((⟨a, hm⟩ : v.valuationSubring) ^ N - 1) = 0 := by
      rw [map_sub, map_pow, hpow _ hne, map_one, sub_self]
    have := (hker _).1 h2
    simpa using this
  have hint : ∀ a : C, v a = 1 → (a ^ N - 1) / ϖ ∈ v.valuationSubring := by
    intro a ha
    rw [Valuation.mem_valuationSubring_iff, map_div₀, div_le_one₀ hvpos]
    exact hmax _ (hlt a ha)
  have key : ∀ (a : Cˣ) (y : v.valuationSubring), (y : C) = ((a : C) ^ N - 1) / ϖ → abelian₂ a = ρ y := by
    intro a y hy
    have hm : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring := hy ▸ y.2
    simp only [abelian₂, dif_pos hm]
    congr 1
    exact Subtype.ext hy.symm
  have hϖm : ϖ ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact h1.le
  have hρϖ : ρ ⟨ϖ, hϖm⟩ = 0 := (hker _).2 h1
  refine ⟨abelian₂, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    have hbm : (b : C) ^ N - 1 ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact (hlt _ hb).le
    have hb0 : ρ ⟨_, hbm⟩ = 0 := (hker _).2 (hlt _ hb)
    rw [key a ⟨_, hint _ ha⟩ rfl, key b ⟨_, hint _ hb⟩ rfl,
      key (a * b) (⟨_, hint _ ha⟩ + ⟨_, hint _ hb⟩ + ⟨_, hint _ ha⟩ * ⟨_, hbm⟩) ?_]
    · rw [map_add (f := _), map_add (f := _), map_mul, hb0, mul_zero, add_zero]
    · push_cast
      field_simp
      ring
  · intro y
    obtain ⟨x, hx⟩ := hsurj (-y)
    have hx1 : v (x : C) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 x.2
    have hz : v (ϖ * x) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hx1) h1
    have ha : v (1 + ϖ * x) = 1 := v.map_one_add_of_lt hz
    have hne : (1 + ϖ * x : C) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    obtain ⟨r, hr⟩ := one_add_pow_expansion' ((⟨ϖ, hϖm⟩ : v.valuationSubring) * x) N
    have hr' : (1 + ϖ * x : C) ^ N = 1 + N * (ϖ * x) + (ϖ * x) ^ 2 * r := by
      have := congrArg (fun t : v.valuationSubring => (t : C)) hr
      simpa using this
    refine ⟨Units.mk0 _ hne, ha, ?_⟩
    rw [key _ ((N : v.valuationSubring) * x + ⟨ϖ, hϖm⟩ * (x ^ 2 * r)) ?_]
    · rw [map_add (f := _), map_mul, map_mul, hρϖ, map_natCast, hNK, hx]; ring
    · rw [Units.val_mk0, hr']
      push_cast
      field_simp
      ring
  · intro a ha
    have ha1 : v (a : C) = 1 := by
      have := v.map_one_add_of_lt (lt_trans ha h1)
      simpa using this
    rw [key a ⟨_, hint _ ha1⟩ rfl, hker]
    have ham : (a : C) ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact ha1.le
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one (⟨_, ham⟩ : v.valuationSubring) N
    have hs' : (a : C) ^ N - 1 = ((a : C) - 1) * s := by
      have := congrArg (fun t : v.valuationSubring => (t : C)) hs
      simpa using this
    have hs1 : v (s : C) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 s.2
    show v (((a : C) ^ N - 1) / ϖ) < 1
    rw [map_div₀, div_lt_one₀ hvpos, hs', map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hs1) ha
  · intro i f hi hv hf a ha
    have hia : v ((Units.map i.toRingHom.toMonoidHom a : Cˣ) : C) = 1 := by
      show v (i a) = 1
      rw [hv, ha]
    rw [key a ⟨_, hint _ ha⟩ rfl, key _ ⟨_, hint _ hia⟩ rfl]
    apply hf
    show ((i a) ^ N - 1) / ϖ = i (((a : C) ^ N - 1) / ϖ)
    rw [map_div₀, map_sub, map_pow, map_one, hi]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.continuous_inertia_restriction_of_compat :
    ∀ {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E L] [Algebra E Ω] [Algebra L Ω]
        [IsScalarTower E L Ω] (A : ValuationSubring Ω) (ι : Ine (F := E) A →* Ine (F := L) A),
        (∀ (t : Ine (F := E) A) (x : Ω), (ι t : G L Ω) x = (t : G E Ω) x) → Continuous ι := by
  intro E L Ω _ _ _ _ _ _ _ _ _ A ι hι
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  apply continuous_of_continuousAt_one ι
  rw [ContinuousAt, map_one, tendsto_subtype_rng, Filter.tendsto_def]
  intro s hs
  rw [OneMemClass.coe_one] at hs
  obtain ⟨K, hK, hKs⟩ := (krullTopology_mem_nhds_one_iff L Ω s).mp hs
  haveI : FiniteDimensional E K := Module.Finite.trans L K
  haveI : FiniteDimensional E (K.restrictScalars E) := inferInstanceAs (FiniteDimensional E K)
  have hopen := (K.restrictScalars E).fixingSubgroup_isOpen
  refine Filter.mem_of_superset ((hopen.preimage continuous_subtype_val).mem_nhds ?_) ?_
  · exact (K.restrictScalars E).fixingSubgroup.one_mem
  · intro t ht
    apply hKs
    rw [Set.mem_preimage, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at ht
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hι]
    exact ht x ((IntermediateField.mem_restrictScalars E).mpr hx)
end
