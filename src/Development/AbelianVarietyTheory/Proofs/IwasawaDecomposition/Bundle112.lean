module

public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle001
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.FrobeniusOrbits.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.AlgebraicWeights.IsAlgWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.ResidueBar

theorem residueField_ringEquiv_fbar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first
  | exact @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | (apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv ..)

end GlobalTheory.ResidueBar
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MaxIdealPow

variable {Ω : Type} [Field Ω]

theorem aeval_eq_coeff_zero_add (A : ValuationSubring Ω) (g : ℤ[X]) {y : Ω} (hy : y ∈ A) :
    ∃ w ∈ A, aeval y g = ((g.coeff 0 : ℤ) : Ω) + y * w := by
  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := g)
  have hg : g = C (g.coeff 0) + X * r := by rw [← hr]; ring
  refine ⟨((aeval (⟨y, hy⟩ : A) r : A) : Ω), SetLike.coe_mem _, ?_⟩
  have h1 : aeval y r = ((aeval (⟨y, hy⟩ : A) r : A) : Ω) :=
    aeval_algebraMap_apply Ω (⟨y, hy⟩ : A) r
  conv_lhs => rw [hg]
  rw [map_add (f := _), map_mul, aeval_C, aeval_X, h1]
  simp

theorem exists_nat_of_isPlaceOver (E : Type) [Field E] [NumberField E] [Algebra E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (hP : IsPlaceOver (F := E) A P) :
    ∃ p : ℕ, p ≠ 0 ∧ p ≠ 1 ∧ ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  let I : Ideal ℤ := P.asIdeal.comap (Int.castRingHom (𝓞 E))
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ a ∣ n := by
    intro n
    have h1 := hP (n : 𝓞 E)
    have h2 : (algebraMap E Ω) (((n : 𝓞 E)) : E) = (n : Ω) := by simp
    rw [h2] at h1
    rw [h1]
    have h3 : (n : 𝓞 E) ∈ P.asIdeal ↔ n ∈ I := by simp [I]
    rw [h3, ha, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨k, rfl⟩; exact Dvd.intro_left k rfl
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩
  refine ⟨a.natAbs, ?_, ?_, fun n => by rw [hmem n, Int.natAbs_dvd]⟩
  · intro h0
    have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
    have hN := Ideal.absNorm_mem P.asIdeal
    have hNv : A.valuation (((Ideal.absNorm P.asIdeal : ℕ) : ℤ) : Ω) < 1 := by
      have h1 := (hP ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)).mpr hN
      simpa using h1
    rw [hmem, ha0, zero_dvd_iff] at hNv
    have : Ideal.absNorm P.asIdeal = 0 := by exact_mod_cast hNv
    exact P.ne_bot (Ideal.absNorm_eq_zero_iff.mp this)
  · intro h1
    have : A.valuation ((1 : ℤ) : Ω) < 1 := by
      rw [hmem, ← Int.natAbs_dvd, h1]; simp
    simp at this

end GlobalTheory.MaxIdealPow

namespace GlobalTheory.MaxIdealPow

theorem exists_pow_lt_valuation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  intro E Ω _ _ _ _ _ A P hP x c hx hc hc0 hvx
  obtain ⟨p, hp0, hp1, hpv⟩ := exists_nat_of_isPlaceOver E A P hP
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvp : A.valuation (p : Ω) < 1 := by
    have := (hpv p).2 dvd_rfl
    simpa using this
  have hvp0 : A.valuation (p : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hp0
  have hunit : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → A.valuation (n : Ω) = 1 := fun n hn =>
    le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A n))
      (not_lt.1 (fun h => hn ((hpv n).1 h)))
  have hxA : x ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hx
  have hcA : c ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hc

  have hstep2 : ∃ s : ℕ, A.valuation x ^ s ≤ A.valuation (p : Ω) := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    let f := minpoly ℤ x
    have hfm : f.Monic := minpoly.monic hx
    let fb := f.map (Int.castRingHom (ZMod p))
    have hfb0 : fb ≠ 0 := (hfm.map _).ne_zero
    obtain ⟨q, hq, hqX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd fb hfb0 0
    simp only [map_zero, sub_zero] at hq hqX
    set s := rootMultiplicity 0 fb
    have hq0 : q.coeff 0 ≠ 0 := fun h => hqX (X_dvd_iff.mpr h)
    obtain ⟨g, hg⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
    have hker : f - X ^ s * g ∈ RingHom.ker (mapRingHom (Int.castRingHom (ZMod p))) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, hg]
      exact sub_eq_zero.mpr hq
    rw [ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hker
    obtain ⟨h, hh⟩ := hker
    have hev := congrArg (aeval x) hh
    rw [map_sub, map_mul, map_pow, aeval_X, minpoly.aeval, map_mul, aeval_C] at hev
    have hg0 : ¬ (p : ℤ) ∣ g.coeff 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h0; apply hq0; rw [← hg, coeff_map]; simpa using h0
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A g hxA
    have hvg : A.valuation (aeval x g) = 1 := by
      rw [hw, Valuation.map_add_eq_of_lt_left, hunit _ hg0]
      rw [hunit _ hg0, Valuation.map_mul]
      calc A.valuation x * A.valuation w ≤ A.valuation x * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation x := mul_one _
        _ < 1 := hvx
    have hhA : aeval x h ∈ A := by
      obtain ⟨w', hw'A, hw'⟩ := aeval_eq_coeff_zero_add A h hxA
      rw [hw']; exact add_mem (intCast_mem A _) (mul_mem hxA hw'A)
    refine ⟨s, ?_⟩
    have hev2 : x ^ s * aeval x g = -((algebraMap ℤ Ω p) * aeval x h) := by
      rw [← hev]; ring
    have := congrArg A.valuation hev2
    rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hvg,
      mul_one] at this
    rw [this]
    have hp' : (algebraMap ℤ Ω (p : ℤ)) = (p : Ω) := by simp
    rw [hp']
    calc A.valuation (p : Ω) * A.valuation (aeval x h) ≤ A.valuation (p : Ω) * 1 :=
          mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hhA) |>.trans_eq (mul_one _).symm
      _ = A.valuation (p : Ω) := mul_one _

  have hstep3 : ∃ t : ℕ, A.valuation (p : Ω) ^ t ≤ A.valuation c := by
    let f := minpoly ℤ c
    have hf0 : f ≠ 0 := (minpoly.monic hc).ne_zero
    obtain ⟨f₁, hf, hfX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
    simp only [map_zero, sub_zero] at hf hfX
    have ha0 : f₁.coeff 0 ≠ 0 := fun h => hfX (X_dvd_iff.mpr h)
    have hev : aeval c f₁ = 0 := by
      have h1 := minpoly.aeval ℤ c
      change aeval c f = 0 at h1
      rw [hf, map_mul, map_pow, aeval_X] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc0)
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A f₁ hcA
    rw [hev] at hw
    have hle : A.valuation ((f₁.coeff 0 : ℤ) : Ω) ≤ A.valuation c := by
      have he : ((f₁.coeff 0 : ℤ) : Ω) = -(c * w) := by linear_combination -hw
      rw [he, Valuation.map_neg, Valuation.map_mul]
      calc A.valuation c * A.valuation w ≤ A.valuation c * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation c := mul_one _
    have hn0 : (f₁.coeff 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
    obtain ⟨t, u, hu, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp1
    refine ⟨t, le_trans (le_of_eq ?_) hle⟩
    have habs : A.valuation ((f₁.coeff 0 : ℤ) : Ω) = A.valuation (((f₁.coeff 0).natAbs : ℤ) : Ω) := by
      rcases Int.natAbs_eq (f₁.coeff 0) with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, Valuation.map_neg]
    rw [habs, hfac]
    have hu1 : A.valuation ((u : ℤ) : Ω) = 1 := hunit u (by exact_mod_cast hu)
    push_cast
    rw [Valuation.map_mul, Valuation.map_pow]
    push_cast at hu1
    rw [hu1, mul_one]
  obtain ⟨s, hs⟩ := hstep2
  obtain ⟨t, ht⟩ := hstep3
  refine ⟨s * (t + 1), ?_⟩
  calc A.valuation x ^ (s * (t + 1)) = (A.valuation x ^ s) ^ (t + 1) := pow_mul _ _ _
    _ ≤ A.valuation (p : Ω) ^ (t + 1) := pow_le_pow_left₀ zero_le' hs _
    _ = A.valuation (p : Ω) ^ t * A.valuation (p : Ω) := pow_succ _ _
    _ < A.valuation (p : Ω) ^ t * 1 :=
        mul_lt_mul_of_pos_left hvp (zero_lt_iff.mpr (pow_ne_zero _ hvp0))
    _ = A.valuation (p : Ω) ^ t := mul_one _
    _ ≤ A.valuation c := ht

end GlobalTheory.MaxIdealPow
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem galAlgClosure_exists_pos_pow_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (σ : G E Ω) (t : Ω), ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
  intro E Ω _ _ _ _ _ σ t
  have hint : IsIntegral E t :=
    ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic t).isIntegral
  have hmem : ∀ i : ℕ, (σ ^ i) t ∈ (minpoly E t).rootSet Ω := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ i : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    rw [minpoly.aeval, map_zero] at h
    exact h
  haveI : Finite ((minpoly E t).rootSet Ω) := ((minpoly E t).rootSet_finite Ω).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨(σ ^ i) t, hmem i⟩ : (minpoly E t).rootSet Ω))
  have heq' : (σ ^ i) t = (σ ^ j) t := congrArg Subtype.val heq
  have key : ∀ a b : ℕ, a < b → (σ ^ a) t = (σ ^ b) t → ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
    intro a b hab h
    refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
    apply (σ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact h.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq'
  · exact key j i h heq'.symm

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV

namespace GlobalTheory

theorem reduction_blockTri_detDD : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  intro L _ _ _ s φ n r h g hφ hg
  have key : ∀ a b, (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = 0 ↔
      Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
    intro a b
    obtain ⟨hab, e⟩ := hg a b
    rw [e, hφ]
  refine ⟨?_, ?_⟩
  · rw [mem_blockTri]
    constructor
    · intro H a b ha hb
      rw [← key]
      apply H
      simp [blk2, hb, Nat.not_lt.mpr ha]
    · intro H i j hij
      rw [key]
      unfold blk2 at hij
      by_cases hj : j.val < r
      · by_cases hi : i.val < r
        · simp [hj, hi] at hij
        · exact H i j (Nat.not_lt.mp hi) hj
      · by_cases hi : i.val < r <;> simp [hj, hi] at hij
  · intro hT
    let M : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s.v.adicCompletionIntegers (maximalRealSubfield L)) :=
      fun a b => ⟨(h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1, (hg a.1 b.1).1⟩
    have hdet : NG.detDD s r h = (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype M.det := by
      rw [RingHom.map_det]
      rfl
    refine ⟨hdet ▸ (M.det).2, ?_⟩
    have e1 : (⟨NG.detDD s r h, hdet ▸ (M.det).2⟩ : s.v.adicCompletionIntegers (maximalRealSubfield L)) = M.det :=
      Subtype.ext hdet
    rw [e1, RingHom.map_det, diag_block_det_val 1 hT]
    let e : {a : Fin n // blk2 r a = 1} ≃ {x : Fin n // r ≤ x.val} :=
      Equiv.subtypeEquivRight (fun a => by
        unfold blk2
        split_ifs with h'
        · exact ⟨fun h0 => absurd h0 (by decide), fun h0 => absurd h' (Nat.not_lt.mpr h0)⟩
        · exact ⟨fun _ => Nat.not_lt.mp h', fun _ => rfl⟩)
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply, M]
    exact (hg (e a).1 (e b).1).2

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatIso

theorem heckeFunI_eq_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)) (h : GU Dv.σw n → ℂ)
    (hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0}) :
    ∃ (C : Finset (GAf L n ⧸ U)) (a : GAf L n ⧸ U → ℂ) (x : GAf L n ⧸ U → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n U Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ := by
  classical
  refine ⟨hfin.toFinset,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      Dv.hval h (Dv.loc hc.choose) else 0,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      hc.choose else 1, fun W _ _ φ => ?_⟩
  funext g
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · simp only [dif_pos hc]
      rfl
    · simp only [dif_neg hc, zero_smul]
      rfl
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · rw [dif_pos hc] at hc0
      rw [Set.Finite.coe_toFinset]
      refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
      rw [h0, zero_smul]
    · exact absurd (dif_neg hc) hc0

theorem satAt_of_iso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n)
    (hiso : π.Iso π') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0})
    (hs : NG.SatAt π Dv α) : NG.SatAt π' Dv α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  obtain ⟨T, hT⟩ := hiso.2
  refine ⟨(T ⟨f, hfS⟩ : π'.S), (T ⟨f, hfS⟩).2, ?_, U, ?_, hUv, ?_⟩
  · intro h0
    have h1 : T ⟨f, hfS⟩ = 0 := Subtype.ext h0
    have h2 : (⟨f, hfS⟩ : π.S) = 0 := T.map_eq_zero_iff.mp h1
    exact hf0 (congrArg Subtype.val h2)
  · intro κ hκ
    exact (hT κ ⟨f, hfS⟩ ⟨f, hfS⟩ (hU κ hκ).symm).symm
  · intro h hh
    obtain ⟨C, a, x, hC⟩ := heckeFunI_eq_sum Dv U h (hfin U hUv h hh)
    have e := hH h hh
    rw [hC] at e
    rw [hC]
    have e1 : (∑ c ∈ C, a c • (⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ : π.S)) =
        SatU Dv.ϖ (qV (maximalRealSubfield L) v) h α • (⟨f, hfS⟩ : π.S) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact e
    have e2 := congrArg (fun y => ((T y : π'.S) : GAf L n → π'.W)) e1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hT (x c) ⟨f, hfS⟩ ⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ rfl]

end GlobalTheory.SatIso
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem omFrame_exists_with_jE (D : D7) (jE : D.host.E →+* Qb) : ∃ fr : OmFrame D, fr.jE = jE := by
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Qb := inferInstance
  haveI : IsScalarTower ℚ D.host.E Qb := .of_algebraMap_eq fun x => (map_ratCast jE x).symm
  haveI : Algebra.IsAlgebraic D.host.E Qb := .tower_top (K := ℚ) D.host.E
  haveI : IsAlgClosure D.host.E Qb := ⟨inferInstance, inferInstance⟩
  let e : D.nd.Om ≃ₐ[D.host.E] Qb := IsAlgClosure.equiv D.host.E D.nd.Om Qb
  exact ⟨⟨jE, e.toRingEquiv, fun x => e.commutes x⟩, rfl⟩

end GlobalTheory.HeightCounting
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocLevel

theorem mem_placesOver_of_overPl' {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem overPl_of_isConjPl {D : D7} {w : PlE D.host} {s : SplitPlace D.host.E} (hc : IsConjPl D.host w s.w) :
    NG.OverPl w s.v := by
  unfold NG.OverPl
  rw [← s.w_under]
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  apply hc
  have hy := GlobalTheory.SplitConjPlace.cO_algebraMap a
  set y := algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a
  have e1 : (y : D.host.E) = IsCMField.complexConj D.host.E (y : D.host.E) := by
    conv_lhs => rw [← hy]
    rw [IsCMField.coe_ringOfIntegersComplexConj]
  rw [e1]
  conv_rhs => rw [← e1]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])


end GlobalTheory.LocLevel
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.witt_theorem_adelic_one_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ y : (Fin 1 → Fin M → AF F ⊗[F] E), qR (AF F) σ J (y 0) = algebraMap F (AF F) β → ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  first | exact @GlobalTheory.AdelicWitt.witt_adelic | exact GlobalTheory.AdelicWitt.witt_adelic | (intros; apply GlobalTheory.AdelicWitt.witt_adelic <;> assumption)
end
