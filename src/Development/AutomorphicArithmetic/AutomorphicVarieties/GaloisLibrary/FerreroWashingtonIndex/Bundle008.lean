module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.CMField
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement
public import Mathlib.Algebra.Algebra.Hom.Rat
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem iC_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem iC_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem iC_eta {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => iC_pow A (iC_one A hm hη) h i

private theorem iC_ine (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) (g : G F Ω)
    (hg : g ∈ Ine (F := F) A) (k : ℕ) (ζ : Ω) (hζ : ζ ^ l ^ k = 1) : g ζ = ζ := by
  have hm : l ^ k ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  have hv := iC_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A l)) (not_lt.1 hA)
  have hA' : ¬ A.valuation ((l ^ k : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hl1, one_pow]; exact lt_irrefl _
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine iC_eta A hm hA' (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, hv, div_one]; exact hg.2 ζ hv.le
  exact (div_eq_one_iff_eq h0).1 this

theorem UpperTheory.V.FW.ineCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) [IsCyclotomicExtension {l ^ n} F K] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ galOf F K Ω := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ n hc A hA g hg x
  have hx := IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := F) (B := K) x
  show g (algebraMap K Ω x) = algebraMap K Ω x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨m, hm, -, hy⟩ := hy
    obtain rfl : m = l ^ n := hm
    exact iC_ine F Ω l A hA g hg n _ (by rw [← map_pow, hy, map_one])
  | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact g.commutes r
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.embCyc :
    ∀ (N m M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {m} K K'] (L : Type) [Field L] [NumberField L] [Algebra K' L] [IsCyclotomicExtension {M} K' L], N ∣ M → m ∣ M → Nonempty (K →ₐ[ℚ] CyclotomicField N ℚ) → IsCyclotomicExtension {M} ℚ L := by
  intro N m M _ K _ _ _ K' _ _ _ _ L _ _ _ _ hNM hmM hφ
  obtain ⟨φ⟩ := hφ
  have hM0 : M ≠ 0 := NeZero.ne M
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM0 (zero_dvd_iff.mp hNM)
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K' L (Set.mem_singleton M) hM0
  let F : Subalgebra ℚ L := Algebra.adjoin ℚ {ζ}
  have hroot : ∀ x : L, ∀ k : ℕ, k ∣ M → x ^ k = 1 → x ∈ F := by
    intro x k hk hx
    have hxM : x ^ M = 1 := by
      obtain ⟨j, hj⟩ := hk
      rw [hj, pow_mul, hx, one_pow]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hxM
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
  have hpN : IsPrimitiveRoot (ζ ^ (M / N)) N := by
    have := hζ.pow_of_dvd (p := M / N) ?_ (Nat.div_dvd_of_dvd hNM)
    · rwa [Nat.div_div_self hNM hM0] at this
    · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hNM) (Nat.pos_of_ne_zero hN0)).ne'
  have hsp : Polynomial.Splits ((Polynomial.X ^ N - 1 : Polynomial ℚ).map (algebraMap ℚ L)) := by
    simpa using Polynomial.X_pow_sub_one_splits hpN
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ (CyclotomicField N ℚ)
  let ψ : CyclotomicField N ℚ →ₐ[ℚ] L :=
    Polynomial.IsSplittingField.lift (CyclotomicField N ℚ) (Polynomial.X ^ N - 1) hsp
  have h1 : ∀ y, ψ y ∈ F := by
    intro y
    have hy := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) y
    have hle : Algebra.adjoin ℚ {b : CyclotomicField N ℚ | ∃ n : ℕ, n ∈ ({N} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1}
        ≤ F.comap ψ := by
      rw [Algebra.adjoin_le_iff]
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hb
      exact hroot (ψ b) N hNM (by rw [← map_pow, hb, map_one])
    exact hle hy
  have h2 : ∀ k : K, algebraMap K' L (algebraMap K K' k) ∈ F := by
    intro k
    let e1 : K →ₐ[ℚ] L := ((algebraMap K' L).comp (algebraMap K K')).toRatAlgHom
    let e2 : K →ₐ[ℚ] L := ψ.comp φ
    let g := e2.equivFieldRange
    haveI := Normal.of_algEquiv g
    have hr := AlgHom.fieldRange_of_normal (e1.comp g.symm.toAlgHom)
    have hk : e1 k ∈ e2.fieldRange := by
      rw [← hr]
      exact AlgHom.mem_fieldRange.mpr ⟨g k, by simp⟩
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hk
    show e1 k ∈ F
    rw [← hy]
    exact h1 (φ y)
  have h3 : ∀ x : K', algebraMap K' L x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {m}) (A := K) x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ m hmM (by rw [← map_pow, hbn, map_one])
    | algebraMap k => exact h2 k
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  have h4 : ∀ x : L, x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {M}) (A := K') x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ M dvd_rfl hbn
    | algebraMap k => exact h3 k
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨ζ, hζ⟩, fun x => Algebra.adjoin_mono ?_ (h4 x)⟩
  rintro _ rfl
  exact hζ.pow_eq_one
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem isUnit_one_sub {R : Type} [CommRing R] [IsDomain R] {M : ℕ} (hM : 0 < M) {z : R}
    (hz : IsPrimitiveRoot z M) (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ M) : IsUnit (1 - z) := by
  have hroot := hz.isRoot_cyclotomic hM
  have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
  have h1 := congrArg (Polynomial.eval 1) hfac
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one_cyclotomic_not_prime_pow h] at h1
  exact IsUnit.of_mul_eq_one _ h1

private theorem exists_finset_adjoin_laurent_preimage (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {M} ℚ L] [IsCMField L] (h4 : 4 ∣ M)
    (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ M) :
    Function.Surjective (IsCMField.unitsMulComplexConjInv L) := by
  have hM : 0 < M := NeZero.pos M
  obtain ⟨k, hk⟩ := h4
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ L
  set ζ := IsCyclotomicExtension.zeta M ℚ L
  have hη := hζ.toInteger_isPrimitiveRoot
  have hu : IsUnit (1 - hζ.toInteger) := isUnit_one_sub hM hη h
  have hm1 : ζ ^ (2 * k) = -1 := by
    have hsq : ζ ^ (2 * k) * ζ ^ (2 * k) = 1 := by
      rw [← pow_add, show 2 * k + 2 * k = M by omega]
      exact hζ.pow_eq_one
    have hne : ζ ^ (2 * k) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    exact (mul_self_eq_one_iff.mp hsq).resolve_left hne
  have hneg : IsPrimitiveRoot (-ζ) M := by
    have hpow : -ζ = ζ ^ (2 * k + 1) := by
      rw [pow_succ, hm1, neg_one_mul]
    rw [hpow]
    apply hζ.pow_of_coprime
    rw [hk, Nat.coprime_comm, show 4 * k = 2 * (2 * k) by ring]
    refine Nat.Coprime.mul_left ?_ ?_
    · exact Nat.coprime_two_left.mpr (odd_two_mul_add_one k)
    · exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hζne : ζ ≠ 1 := hζ.ne_one (by omega)
  set g := IsCMField.unitsMulComplexConjInv L hu.unit with hgdef
  have hg : algebraMap (𝓞 L) L ((g : (𝓞 L)ˣ) : 𝓞 L) = -ζ := by
    have hc : IsCMField.complexConj L ζ = ζ⁻¹ := by
      obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
      refine eq_inv_of_mul_eq_one_left ?_
      apply φ.injective
      have hz : ‖φ ζ‖ = 1 := (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)
      rw [map_mul, map_one, IsCMField.complexEmbedding_complexConj, Complex.conj_mul', hz]
      simp
    rw [hgdef, IsCMField.unitsMulComplexConjInv_apply, Units.coe_mul, map_units_inv]
    simp
    have e1 : (algebraMap (𝓞 L) L) hζ.toInteger = ζ := rfl
    have e2 : ((hζ.toInteger : 𝓞 L) : L) = ζ := rfl
    rw [e1, e2, hc]
    have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
    have h1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζne
    have h2 : (1 : L) - ζ⁻¹ = (ζ - 1) / ζ := by
      field_simp
    rw [h2, inv_div]
    field_simp
    ring
  have hgp : IsPrimitiveRoot g M := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff,
      ← IsPrimitiveRoot.map_iff_of_injective (f := algebraMap (𝓞 L) L)
        (FaithfulSMul.algebraMap_injective _ _), hg]
    exact hneg
  have htop : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ← hgp.eq_orderOf]
    have ht := IsCyclotomicExtension.Rat.torsionOrder_eq (n := M) (K := L)
    rw [if_pos ⟨2 * k, by omega⟩] at ht
    exact ht.symm
  intro y
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top y)
  exact ⟨hu.unit ^ j, by rw [map_zpow, hj]⟩

theorem UpperTheory.V.FW.unitSurj :
    ∀ (f n : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L], Odd f → 1 < f → 2 ≤ n → Function.Surjective (IsCMField.unitsMulComplexConjInv L) := by
  intro f n _ L _ _ _ _ hf hf1 hn
  apply exists_finset_adjoin_laurent_preimage (f * 2 ^ n) L
  · have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hn) f
  · intro p hp k hk
    have h2 : 2 ∣ p ^ k := hk ▸ Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) f
    have hp2 : p = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    subst hp2
    have hfd : f ∣ 2 ^ k := hk ▸ Dvd.intro _ rfl
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hfd
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp at hf1
    · have hev : Even (2 ^ i) := (Nat.even_pow).mpr ⟨even_two, hi.ne'⟩
      exact (Nat.not_even_iff_odd.mpr hf) hev
end
