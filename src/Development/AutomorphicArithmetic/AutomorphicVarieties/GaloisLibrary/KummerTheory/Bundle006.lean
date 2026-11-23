module

public import Formalism.GaloisCohomology.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem qzB_smul_mk (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzB_mk_eq_zero (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzB_mk_surj (l : ℕ) [Fact l.Prime] (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

theorem UpperTheory.V.Kum.qzBasic :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l], u ≠ 0 → Function.Surjective fun x : QZ l => u • x) ∧ (∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0) ∧ (l ≠ 2 → ∀ x : QZ l, 2 • x = 0 → x = 0) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have tors : ∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ := qzB_mk_surj l x
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hl1
    refine ⟨k, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], qzB_smul_mk, qzB_mk_eq_zero]
    have hpos : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (by linarith) k
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [PadicInt.mem_subring_iff]
    push_cast
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpos, mul_one]
    exact hk.le
  refine ⟨?_, tors, ?_⟩
  · intro u hu a
    obtain ⟨q, rfl⟩ := qzB_mk_surj l a
    have hu' : (u : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 hu
    refine ⟨QZ.mk l (q / u), ?_⟩
    show u • QZ.mk l (q / u) = QZ.mk l q
    rw [qzB_smul_mk, mul_div_cancel₀ q hu']
  · intro h2 x hx
    obtain ⟨k, hk⟩ := tors x
    have hc : IsCoprime (2 : ℤ) ((l ^ k : ℕ) : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm h2))
    obtain ⟨a, b, hab⟩ := hc
    calc x = (1 : ℤ) • x := (one_smul ℤ x).symm
      _ = (a * 2 + b * ((l ^ k : ℕ) : ℤ)) • x := by rw [hab]
      _ = a • ((2 : ℕ) • x) + b • ((l ^ k) • x) := by
        rw [add_smul, mul_smul, mul_smul]
        norm_cast
      _ = 0 := by rw [hx, hk, smul_zero, smul_zero, add_zero]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
  by_contra hx
  have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
  exact lt_irrefl _ h2

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
      ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
  have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
    (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
  rw [eq_top_iff]
  intro x _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
  have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
  obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
  have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
    rw [hP, h0, Ideal.mem_bot]
    exact Int.cast_ne_zero.2 hn
  have h4 : A.valuation (n : Ω) = 1 :=
    le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
  have h5 := int_le A hi
  rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
  exact (A.valuation_le_one_iff x).1 h5

theorem UpperTheory.V.Kum.placeDict :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Ine (F := K) (⊤ : ValuationSubring Ω) = ⊥ ∧ (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v) ∧
    (∀ (A : ValuationSubring Ω) (N : ℕ), N ≠ 0 → A.valuation (N : Ω) < 1 → A ≠ ⊤) ∧
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (N : ℕ), IsPlaceOver A v →
      (A.valuation (N : Ω) < 1 ↔ v ∈ Formalism.GaloisCohomology.Above (F := K) N) := by
  intro K Ω _ _ _ _ _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  · intro A hA
    exact exists_place K Ω A hA
  · rintro A N hN h rfl
    exact hN (Nat.cast_eq_zero.1 (val_top h))
  · intro A v N hv
    have h := hv (N : 𝓞 K)
    have e : algebraMap K Ω ((N : 𝓞 K) : K) = (N : Ω) := by simp
    rw [← e]
    exact h
end
