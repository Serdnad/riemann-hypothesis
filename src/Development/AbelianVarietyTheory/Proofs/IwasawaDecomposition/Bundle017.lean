module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

section

namespace GlobalTheory.SmulMemSpanIntegers

theorem exists_smul_mem_span_integers {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type}
    [AddCommGroup WL] [Module Ks WL] [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {T : Set WL} {g : WL}
    (hg : g ∈ Submodule.span Ks T) :
    ∃ d : NumberField.RingOfIntegers Ks, d ≠ 0 ∧
      d • g ∈ Submodule.span (NumberField.RingOfIntegers Ks) T := by

  induction hg using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d₁, hd₁, h₁⟩ := ihx
    obtain ⟨d₂, hd₂, h₂⟩ := ihy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm d₁ d₂ x]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul c x _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (NumberField.RingOfIntegers Ks) Ks b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ Ks)).2 hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have e : b • ((algebraMap (NumberField.RingOfIntegers Ks) Ks a /
        algebraMap (NumberField.RingOfIntegers Ks) Ks b) • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hbK, algebraMap_smul]
    rw [mul_comm, mul_smul, e, smul_comm]
    exact Submodule.smul_mem _ _ h

end GlobalTheory.SmulMemSpanIntegers
end

section

open Polynomial

namespace GlobalTheory.IsIntegralDetLattice

theorem isIntegral_of_isRoot_charpoly {R K : Type} [CommRing R] [Field K] [Algebra R K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (hA : IsIntegral R A) (x : K) (hx : A.charpoly.IsRoot x) :
    IsIntegral R x := by
  obtain ⟨p, hp, hpA⟩ := hA

  have hmem : x ∈ spectrum K A := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hx
  have h2 := spectrum.subset_polynomial_aeval A (p.map (algebraMap R K)) ⟨x, hmem, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hpA, spectrum.mem_iff, sub_zero] at h2
  refine ⟨p, hp, ?_⟩
  rw [eval₂_eq_eval_map]
  by_contra hne
  exact h2 ((Ne.isUnit hne).map (algebraMap K (Matrix (Fin N) (Fin N) K)))

theorem isIntegral_det {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) E) (hA : IsIntegral R A) : IsIntegral R A.det := by

  let φ : E →ₐ[R] AlgebraicClosure E := IsScalarTower.toAlgHom R E (AlgebraicClosure E)
  have hA' : IsIntegral R (A.map (algebraMap E (AlgebraicClosure E))) := by
    exact hA.map (φ.mapMatrix (m := Fin N))
  have hdet : (A.map (algebraMap E (AlgebraicClosure E))).det = algebraMap E (AlgebraicClosure E) A.det := by
    rw [RingHom.map_det]; rfl
  rw [← isIntegral_algHom_iff φ (algebraMap E (AlgebraicClosure E)).injective]
  show IsIntegral R (algebraMap E (AlgebraicClosure E) A.det)
  rw [← hdet, Matrix.det_eq_prod_roots_charpoly]
  exact multiset_prod_mem (S := integralClosure R (AlgebraicClosure E)) _
    fun r hr => isIntegral_of_isRoot_charpoly _ hA' r (Polynomial.isRoot_of_mem_roots hr)

theorem isIntegral_of_preserves {R E : Type} [CommRing R] [Field E] [Algebra R E] {N : ℕ}
    (L : Submodule R (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ := by
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hL

  let f : Module.End R L := ((Matrix.mulVecLin γ).restrictScalars R).restrict hγ
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (n : ℕ) (v : Fin N → E) (hv : v ∈ L),
      (γ ^ n).mulVec v = ((f ^ n) ⟨v, hv⟩ : Fin N → E) := by
    intro n
    induction n with
    | zero => intro v hv; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih v hv, Module.End.mul_apply]
      rfl
  have key : ∀ (q : R[X]) (v : Fin N → E) (hv : v ∈ L),
      (aeval γ q).mulVec v = ((aeval f q) ⟨v, hv⟩ : Fin N → E) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v hv; simp [Matrix.add_mulVec, hp v hv, hq v hv]
    | monomial n a =>
      intro v hv
      simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hpow n v hv]
  have hz : Matrix.toLin' (aeval γ p) = 0 := by
    refine LinearMap.ext_on hs fun v hv => ?_
    simp [Matrix.toLin'_apply, key p v hv, hpf]
  exact ⟨p, hp, by rw [← aeval_def]; exact Matrix.toLin'.map_eq_zero_iff.mp hz⟩

theorem isIntegral_det_of_preserves_lattice {E : Type} [Field E] [NumberField E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : L.FG)
    (hs : Submodule.span E (↑L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det := by
  exact isIntegral_trans _ (isIntegral_det γ (isIntegral_of_preserves L hL hs γ hγ))

end GlobalTheory.IsIntegralDetLattice
end

section

namespace GlobalTheory.SpanValuationBound

open IsDedekindDomain

theorem span_valuation_le {L : Type} [Field L] [NumberField L] {S : Set L}
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}
    (hS : ∀ x ∈ S, (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) :
    ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S,
      (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => simp
  | add y z _ _ hy hz =>
    exact le_trans (Valuation.map_add _ y z) (max_le hy hz)
  | smul a y _ hy =>
    rw [Algebra.smul_def, map_mul]
    calc (HeightOneSpectrum.valuation L w) (algebraMap _ L a) * (HeightOneSpectrum.valuation L w) y
        ≤ 1 * γ := mul_le_mul' (HeightOneSpectrum.valuation_le_one w a) hy
      _ = γ := one_mul γ

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {S : Set L} (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}, (∀ x ∈ S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) → ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ :=
  @fun _ _ _ _ w _ h => span_valuation_le w h

end GlobalTheory.SpanValuationBound
end

section

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem selfDual_standard_at_rational_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)) (t : 𝓞 K), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → t ∉ 𝔭.asIdeal → (∀ x ∈ L, ∀ i, (t : K) * x i ∈ (algebraMap (𝓞 K) K).range) → (∀ j, (Pi.single j (t : K) : n → K) ∈ L) → ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • v ∈ L := by
  intro K _ _ σ n _ _ p 𝔭 α β L t hσ hN hp hp𝔭 hα hβ hβα hL ht h1 h2
  have hint : ∀ x ∈ (algebraMap (𝓞 K) K).range, σ x ∈ (algebraMap (𝓞 K) K).range := by
    rintro _ ⟨x, rfl⟩
    have : IsIntegral ℤ (σ (algebraMap (𝓞 K) K x)) :=
      (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
    exact ⟨⟨_, this⟩, rfl⟩
  obtain ⟨t', ht'⟩ := hint (t : K) ⟨t, rfl⟩
  have ht'' : (t' : K) = σ t := ht'
  have h1' : ∀ x ∈ L, ∀ j, (t' : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have := (hL x).1 hx _ (h2 j)
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)] at this
    rw [ht'', mul_comm]
    simpa only [Pi.single_eq_same] using this
  have h2' : ∀ j, (Pi.single j (t' : K) : n → K) ∈ L := by
    intro j
    rw [hL]
    intro y hy
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)]
    rw [Pi.single_eq_same, ht'', ← map_mul]
    exact hint _ (h1 y hy j)
  set a : 𝓞 K := β * t + α * t' with ha
  have haK : (a : K) = β * t + α * t' := by simp [ha]
  have ha𝔭 : a ∉ 𝔭.asIdeal := by
    intro h
    have h' : β * t ∈ 𝔭.asIdeal := by
      have := 𝔭.asIdeal.sub_mem h (𝔭.asIdeal.mul_mem_right t' hα)
      simpa [ha] using this
    rcases 𝔭.isPrime.mem_or_mem h' with h | h
    · exact hβ h
    · exact ht h
  have hσa : σ a = a := by
    rw [haK, map_add (f := _), map_mul, map_mul, hβα, ht'', hσ, hσ]
    ring
  have ha1 : ∀ x ∈ L, ∀ j, (a : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have : (a : K) * x j = β * (t * x j) + α * (t' * x j) := by rw [haK]; ring
    rw [this]
    exact add_mem (mul_mem ⟨β, rfl⟩ (h1 x hx j)) (mul_mem ⟨α, rfl⟩ (h1' x hx j))
  have ha2 : ∀ j, (Pi.single j (a : K) : n → K) ∈ L := by
    intro j
    have : (Pi.single j (a : K) : n → K)
        = β • (Pi.single j (t : K) : n → K) + α • (Pi.single j (t' : K) : n → K) := by
      ext i
      by_cases h : i = j
      · subst h
        simp [haK, Algebra.smul_def]
      · simp [Pi.single_eq_of_ne h]
    rw [this]
    exact add_mem (L.smul_mem _ (h2 j)) (L.smul_mem _ (h2' j))
  obtain ⟨m, hm⟩ := hN a
  rw [hσa] at hm
  have hmO : a * a = (m : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    simpa using hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, ((m.natAbs : ℕ) : ℤ) = e * m := by
    rcases Int.natAbs_eq m with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨-1, by omega⟩
  have hs : ((m.natAbs : ℕ) : K) = (e : K) * (a * a) := by
    rw [hm]
    have := congrArg (Int.cast : ℤ → K) he
    rwa [Int.cast_natCast, Int.cast_mul] at this
  refine ⟨m.natAbs, ?_, ?_, ?_⟩
  · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h
    have : a * a ∈ 𝔭.asIdeal := by
      rw [hmO, hc]
      push_cast
      exact 𝔭.asIdeal.mul_mem_right _ hp𝔭
    rcases 𝔭.isPrime.mem_or_mem this with h | h <;> exact ha𝔭 h
  · intro x hx i
    have : ((m.natAbs : ℕ) : K) * x i = (e : K) * a * (a * x i) := by rw [hs]; ring
    rw [this]
    exact mul_mem (mul_mem (intCast_mem _ e) ⟨a, rfl⟩) (ha1 x hx i)
  · intro v hv
    choose w hw using hv
    have : ((m.natAbs : ℕ) : K) • v
        = ∑ j, ((e : 𝓞 K) * w j * a) • (Pi.single j (a : K) : n → K) := by
      ext i
      rw [Finset.sum_apply, Finset.sum_eq_single i
        (by intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, hs, ← hw i, Algebra.smul_def (_ : 𝓞 K),
        smul_eq_mul]
      simp only [map_mul, map_intCast]
      change _ = (e : K) * _ * (a : K) * (a : K)
      ring
    rw [this]
    exact L.sum_mem fun j _ => L.smul_mem _ (ha2 j)

end GlobalTheory
end

section

namespace GlobalTheory.DenominatorExists

open NumberField

theorem exists_mul_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) [hP : P.IsPrime]
    (a b : R) (hb : b ≠ 0) :
    ∃ s t : R, s ∉ P ∧ (a * t = b * s ∨ b * t = a * s) := by
  by_cases h0 : P = ⊥
  · refine ⟨b, a, ?_, Or.inr (mul_comm _ _)⟩
    rw [h0]; simpa using hb
  · haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 _
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
      IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime P) a)
      (algebraMap R (Localization.AtPrime P) b)
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.surj P.primeCompl c
    simp only at hts
    refine ⟨s, t, s.2, ?_⟩
    rcases hc with hc | hc
    · left
      apply hinj
      rw [map_mul, map_mul, ← hts, ← mul_assoc, hc]
    · right
      apply hinj
      rw [map_mul, map_mul, ← hts, ← mul_assoc, hc]

theorem mem_of_integer {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (s : 𝓞 L) : algebraMap L Ω (s : L) ∈ A := by
  have hz : IsIntegral ℤ (algebraMap L Ω (s : L)) := s.2.map (algebraMap L Ω).toIntAlgHom
  have hA : IsIntegral A (algebraMap L Ω (s : L)) := hz.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [← hy]
  exact y.2

theorem exists_denominator {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : L) (hx : A.valuation (algebraMap L Ω x) ≤ 1) :
    ∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧ (s : L) * x = (t : L) := by
  let f : 𝓞 L →+* A :=
    ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (fun s => mem_of_integer A s)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  have hle : ∀ s : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) ≤ 1 :=
    fun s => (A.valuation_le_one_iff _).mpr (mem_of_integer A s)
  have hP : ∀ s : 𝓞 L, s ∉ P → A.valuation (algebraMap L Ω (s : L)) = 1 := by
    intro s hs
    refine le_antisymm (hle s) (not_lt.mp fun h => hs ?_)
    exact Ideal.mem_comap.mpr ((A.valuation_lt_one_iff (f s)).mpr h)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : (b : L) ≠ 0 := by exact_mod_cast hb0
  change A.valuation (algebraMap L Ω ((a : L) / (b : L))) ≤ 1 at hx
  change ∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧
    (s : L) * ((a : L) / (b : L)) = (t : L)
  obtain ⟨s, t, hs, h | h⟩ := exists_mul_eq P a b hb0
  · have h' : (a : L) * t = b * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h
    have e : (t : L) * ((a : L) / (b : L)) = s := by
      field_simp
      linear_combination h'
    refine ⟨t, s, le_antisymm (hle t) ?_, e⟩
    have h1 := hP s hs
    rw [← e, map_mul, map_mul] at h1
    rw [← h1]
    exact mul_le_of_le_one_right' hx
  · have h' : (b : L) * t = a * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h
    refine ⟨s, t, hP s hs, ?_⟩
    field_simp
    linear_combination -h'

end GlobalTheory.DenominatorExists
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem sum_log_embedding_add_finsum_log_adicAbv_eq_zero
    (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite ∧
      (∑ σ : F →+* ℂ, Real.log ‖σ N‖) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 F),
          Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) = 0 := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => NumberField.HeightOneSpectrum.adicAbv F v N) =
      (fun w : FinitePlace F => w N) ∘ (FinitePlace.equivHeightOneSpectrum (K := F)).symm := by
    funext v
    simp only [Function.comp, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      NumberField.HeightOneSpectrum.adicAbv F v N).Finite := by
    rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
      (FinitePlace.hasFiniteMulSupport hN)
  have hpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < NumberField.HeightOneSpectrum.adicAbv F v N :=
    fun v => (NumberField.HeightOneSpectrum.adicAbv F v).pos hN
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v N =
      ((|Algebra.norm ℚ N|⁻¹ : ℚ) : ℝ) := by
    rw [← FinitePlace.prod_eq_inv_abs_norm hN,
      ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    exact congrArg finprod hfun
  have hsub : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)) ⊆ hfin.toFinset := by
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact hv (by simp only [h, Real.log_one])
  refine ⟨hfin.toFinset.finite_toSet.subset hsub, ?_⟩
  have h1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) =
      - Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun v _ => (hpos v).ne'),
      ← finprod_eq_prod_of_mulSupport_subset _ (by simp), hprod, Rat.cast_inv, Real.log_inv]
  have h2 : ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
    simp only [norm_prod] at h
    rw [← Real.log_prod (fun σ _ => by simpa using hN)]
    congr 1
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
      (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
    simp [← Complex.norm_ratCast]
  rw [h1, h2, add_neg_cancel]

end GlobalTheory
end

section

namespace GlobalTheory.AlgebraMapToZMod

theorem algebraMap_toZMod_eq {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type} [inst_1 : Field R]
    [inst_2 : Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  have h := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  set z : ZMod l := PadicInt.toZMod x with hz
  have hc : (ZMod.cast z : ℤ_[l]) = ((z.val : ℕ) : ℤ_[l]) := (ZMod.natCast_val z).symm
  have hx : x = y * (l : ℤ_[l]) + ((z.val : ℕ) : ℤ_[l]) := by
    rw [hy, hc]; ring
  have h1 : f x = ((z.val : ℕ) : R) := by
    conv_lhs => rw [hx]
    rw [map_add (f := _), map_mul, hf, mul_zero, zero_add, map_natCast]
  have h2 : algebraMap (ZMod l) R z = ((z.val : ℕ) : R) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [h1, h2]

end GlobalTheory.AlgebraMapToZMod
end

section

namespace GlobalTheory.LimitSeriesPowSmul

theorem mem_pow_smul_top_iff {R : Type} [CommRing R] (p : R) (n : ℕ) (x : R) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R R)) ↔ p ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R) : ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p})
    (fun k => ∑ i ∈ Finset.range k, p ^ i * f i) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← Finset.sum_range_add_sum_Ico _ hmn,
        sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow p (Finset.mem_Ico.mp hi).1) _)
  exact ⟨L, fun k => (mem_pow_smul_top_iff p k _).mp ((SModEq.sub_mem).mp (hL k))⟩

theorem target : ∀ {R : Type} [inst : CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R), ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L :=
  by
  intro R _ p _ f
  exact exists_limit_series p f

end GlobalTheory.LimitSeriesPowSmul
end
