module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ShortLatticeVectorBoundedSizeOfOrthogonalFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in
private lemma natAbs_discr_pow_finrank_le_natAbs_discr (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    (discr K).natAbs ^ Module.finrank K L ≤ (discr L).natAbs := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  refine Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) ?_
  rw [h]
  exact Dvd.intro_left _ rfl


set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in
theorem _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    Real.log (Module.finrank ℚ K) ≤ Real.log (Module.finrank ℚ L) ∧
      Real.log |((NumberField.discr K : ℤ) : ℝ)| / Module.finrank ℚ K ≤
        Real.log |((NumberField.discr L : ℤ) : ℝ)| / Module.finrank ℚ L := by
  have hmul := Module.finrank_mul_finrank ℚ K L
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hm : 0 < Module.finrank K L := Module.finrank_pos
  have hnR : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast hn
  have hmR : (0 : ℝ) < Module.finrank K L := by exact_mod_cast hm
  have hNR : ((Module.finrank ℚ L : ℕ) : ℝ) = Module.finrank ℚ K * Module.finrank K L := by
    rw [← hmul]; push_cast; ring
  constructor
  · apply Real.log_le_log hnR
    rw [hNR]
    have : (1 : ℝ) ≤ Module.finrank K L := by exact_mod_cast hm
    nlinarith
  · have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := by
      have := discr_ne_zero K
      positivity
    have hle : |((discr K : ℤ) : ℝ)| ^ Module.finrank K L ≤ |((discr L : ℤ) : ℝ)| := by
      have h := natAbs_discr_pow_finrank_le_natAbs_discr K L
      have h' : (((discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) ≤ ((discr L).natAbs : ℝ) := by
        exact_mod_cast h
      simpa [Nat.cast_natAbs, Int.cast_abs] using h'
    have hlog : (Module.finrank K L : ℝ) * Real.log |((discr K : ℤ) : ℝ)| ≤
        Real.log |((discr L : ℤ) : ℝ)| := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hK _) hle
    rw [hNR, div_le_div_iff₀ hnR (mul_pos hnR hmR)]
    nlinarith


set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in
theorem _root_.GlobalTheory.FieldSize.sz_mono_and_of_le :
    (∀ (F : IntermediateField ℚ ℂ) (a b a' b' : ℝ), _root_.GlobalTheory.FieldSize.Sz F a b →
        a ≤ a' → b ≤ b' → _root_.GlobalTheory.FieldSize.Sz F a' b') ∧
      ∀ (F F' : IntermediateField ℚ ℂ) (a b : ℝ), F ≤ F' →
        _root_.GlobalTheory.FieldSize.Sz F' a b → _root_.GlobalTheory.FieldSize.Sz F a b := by
  constructor
  · rintro F a b a' b' ⟨hF, h1, h2⟩ ha hb
    exact ⟨hF, h1.trans ha, h2.trans hb⟩
  · rintro F F' a b hFF' ⟨hF', h1, h2⟩
    haveI : FiniteDimensional ℚ F' := hF'
    haveI hF : FiniteDimensional ℚ F :=
      FiniteDimensional.of_injective (IntermediateField.inclusion hFF').toLinearMap
        (IntermediateField.inclusion hFF').injective
    haveI : NumberField F := ⟨⟩
    haveI : NumberField F' := ⟨⟩
    letI : Algebra F F' := (IntermediateField.inclusion hFF').toRingHom.toAlgebra
    obtain ⟨g1, g2⟩ := _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower F F'
    exact ⟨hF, g1.trans h1, g2.trans h2⟩

end GlobalTheory.FieldSize
end

section

set_option autoImplicit false

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

theorem sz_adjoin_rootOfUnity :
    ∀ n : ℕ, 0 < n → Sz ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ (Real.log n) (Real.log n) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  set F := ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ with hF
  haveI hc : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ F.toSubalgebra
    rw [hF, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral hn).tower_top (A := ℚ)).isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hfd : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {n} ℚ F
  refine ⟨hfd, ?_⟩
  letI : NumberField F := NumberField.mk
  have hrk : Module.finrank ℚ F = Nat.totient n :=
    IsCyclotomicExtension.finrank F (Polynomial.cyclotomic.irreducible_rat hn)
  have ht : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have htR : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast ht
  have hd : (NumberField.discr F).natAbs ≤ n ^ Nat.totient n := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr n F]
    exact Nat.div_le_self _ _
  refine ⟨?_, ?_⟩
  · rw [hrk]
    exact Real.log_le_log htR (by exact_mod_cast Nat.totient_le n)
  · rw [hrk, div_le_iff₀ htR, mul_comm, ← Real.log_pow]
    have h0 : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
    refine Real.log_le_log (abs_pos.2 (by exact_mod_cast h0)) ?_
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hd

end GlobalTheory.FieldSize
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

theorem sz_fieldRange_embedding (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) :
    Sz φ.toRatAlgHom.fieldRange (Real.log (Module.finrank ℚ K))
      (Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K) := by
  let e : K ≃ₐ[ℚ] φ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField φ.toRatAlgHom
  have hfd : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange := e.toLinearEquiv.finiteDimensional
  refine ⟨hfd, ?_⟩
  let _ : NumberField φ.toRatAlgHom.fieldRange := NumberField.mk
  have h1 : Module.finrank ℚ φ.toRatAlgHom.fieldRange = Module.finrank ℚ K := e.toLinearEquiv.finrank_eq.symm
  have h2 : discr φ.toRatAlgHom.fieldRange = discr K := (NumberField.discr_eq_discr_of_algEquiv K e).symm
  rw [h1, h2]
  exact ⟨le_rfl, le_rfl⟩

end GlobalTheory.FieldSize
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.NT
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize.RayDegree

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] {m : Ideal R}

theorem isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m :=
  Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩

theorem exists_mem_sub_one {I : Ideal R} (hI0 : I ≠ ⊥) (h : IsCoprime I m) : ∃ a ∈ I, a ≠ 0 ∧ a - 1 ∈ m := by
  by_cases ht : m = ⊤
  · obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    exact ⟨a, haI, ha0, by simp [ht]⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  have h1 : a - 1 ∈ m := by
    have : a - 1 = -b := by rw [← hab]; ring
    rw [this]
    exact m.neg_mem hb
  refine ⟨a, ha, ?_, h1⟩
  rintro rfl
  apply ht
  rw [Ideal.eq_top_iff_one]
  simpa using m.neg_mem h1

theorem exists_good {I J : Ideal R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI : IsCoprime I m) (hJ : IsCoprime J m)
    {x y : R} (hy : y ≠ 0) (h : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ m ∧ IsCoprime (Ideal.span {b}) m ∧
      Ideal.span {a} * I = Ideal.span {b} * J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have h1 : y * a ∈ Ideal.span {x} * I := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) haJ
  obtain ⟨b, -, hb⟩ := Ideal.mem_span_singleton_mul.mp h1
  have h2 : Ideal.span {a} * I = Ideal.span {b} * J := by
    have hy' : (Ideal.span {y} : Ideal R) ≠ 0 := by simpa using hy
    apply mul_left_cancel₀ hy'
    rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← hb, mul_left_comm, ← h, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, mul_comm b x]
  refine ⟨a, b, ha0, ?_, ha, ?_, h2⟩
  · rintro rfl
    simp [ha0, hI0] at h2
  · have := (isCoprime_span ha).mul_left hI
    rw [h2] at this
    exact this.of_mul_left_left

end General

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {𝔮 : Ideal (𝓞 K)}

theorem emb_ne_zero (φ : K →+* ℝ) {a : 𝓞 K} (ha : a ≠ 0) : φ (a : K) ≠ 0 := by
  simpa using ha

theorem heckeIdeal_eq_of_ray (hR : IsRay L 𝔮) {I J : Ideal (𝓞 K)} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    (hI : IsCoprime I 𝔮) (hJ : IsCoprime J 𝔮) {α β : 𝓞 K} (hp : RayPair 𝔮 α β)
    (h : I * Ideal.span {β} = J * Ideal.span {α}) (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    heckeIdeal L χ I = heckeIdeal L χ J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have ha2 : a * a - 1 ∈ 𝔮 := by
    have : a * a - 1 = (a + 1) * (a - 1) := by ring
    rw [this]; exact 𝔮.mul_mem_left _ ha
  obtain ⟨M, hM⟩ : J ∣ Ideal.span {a * a} := Ideal.dvd_span_singleton.mpr (J.mul_mem_left _ haJ)
  have hM' : IsCoprime M 𝔮 := by
    have := isCoprime_span ha2
    rw [hM] at this
    exact this.of_mul_left_right
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    simp [ha0] at hM
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  have e1 : heckeIdeal L χ (J * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hJ0 hM0) (hJ.mul_left hM')).2 ⟨a * a, 1, ⟨mul_ne_zero ha0 ha0, one_ne_zero,
      isCoprime_span ha2, isCoprime_span (by simp), ha2, fun φ => ?_⟩, by simp [hM]⟩ χ
    have := mul_self_pos.2 (emb_ne_zero φ ha0)
    simpa using this
  have e2 : heckeIdeal L χ (I * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hI0 hM0) (hI.mul_left hM')).2 ⟨a * a * α, β,
      ⟨mul_ne_zero (mul_ne_zero ha0 ha0) h1, h2, ?_, h4, ?_, fun φ => ?_⟩, ?_⟩ χ
    · rw [← Ideal.span_singleton_mul_span_singleton]
      exact (isCoprime_span ha2).mul_left h3
    · have : a * a * α - β = α * (a * a - 1) + (α - β) := by ring
      rw [this]
      exact 𝔮.add_mem (𝔮.mul_mem_left _ ha2) h5
    · have := mul_pos (mul_self_pos.2 (emb_ne_zero φ ha0)) (h6 φ)
      simpa [mul_assoc] using this
    · rw [mul_right_comm, h, mul_right_comm, ← hM, Ideal.span_singleton_mul_span_singleton]
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hJ0 hM0] at e1
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hM0] at e2
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one e1) (e2.trans e1.symm)

theorem exists_ideal [IsGalois K L] (hR : IsRay L 𝔮) (σ : L ≃ₐ[K] L) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧ ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ) := by
  let S : Submonoid (L ≃ₐ[K] L) :=
    { carrier := {σ | ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧
        ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ)}
      one_mem' := ⟨1, one_ne_zero, isCoprime_one_left, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
      mul_mem' := by
        rintro x y ⟨I, hI0, hI, hx⟩ ⟨J, hJ0, hJ, hy⟩
        refine ⟨I * J, mul_ne_zero hI0 hJ0, hI.mul_left hJ, fun χ => ?_⟩
        rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hJ0, hx, hy]; simp }
  have hσ : σ ∈ Subgroup.closure
      {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ GlobalTheory.NT.IsFrob L 𝔭 σ} := by
    rw [hR.2.1]; trivial
  change σ ∈ S
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, hx⟩ := hx
    refine ⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hv (Ideal.dvd_iff_le.2 (le_sup_right.trans (v.isMaximal.eq_of_le hne le_sup_left).ge))
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hR.1 v hv) hx]
  | one => exact S.one_mem
  | mul x y _ _ hx hy => exact S.mul_mem hx hy
  | inv x _ hx =>
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [this]
    exact S.pow_mem hx _

theorem finrank_le : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRay L 𝔮 →
    Module.finrank K L ≤ classNumber K * Ideal.absNorm 𝔮 * 2 ^ Fintype.card (K →+* ℝ) := by
  intro K L _ _ _ _ _ _ 𝔮 h𝔮 hR
  classical
  choose s hs0 hs hsx using exists_ideal hR
  let cl : (L ≃ₐ[K] L) → ClassGroup (𝓞 K) := fun x =>
    ClassGroup.mk0 ⟨s x, mem_nonZeroDivisors_of_ne_zero (hs0 x)⟩
  have key : ∀ x, ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ 𝔮 ∧ IsCoprime (Ideal.span {b}) 𝔮 ∧
      Ideal.span {a} * s x = Ideal.span {b} * s (Function.invFun cl (cl x)) := by
    intro x
    have h : cl x = cl (Function.invFun cl (cl x)) := (Function.invFun_eq ⟨x, rfl⟩).symm
    obtain ⟨a, b, -, hb, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    exact exists_good (hs0 x) (hs0 _) (hs x) (hs _) hb hxy
  choose a b ha0 hb0 ha hb hab using key
  let F : (L ≃ₐ[K] L) → (ClassGroup (𝓞 K) × (𝓞 K ⧸ 𝔮)) × ((K →+* ℝ) → Prop) := fun x =>
    ((cl x, Ideal.Quotient.mk 𝔮 (b x)), fun φ => 0 < φ (a x : K) * φ (b x : K))
  have hF : Function.Injective F := by
    intro x y hxy
    obtain ⟨h12, h3⟩ := Prod.mk.inj hxy
    obtain ⟨h1, h2⟩ := Prod.mk.inj h12
    rw [Ideal.Quotient.eq] at h2
    have hp : RayPair 𝔮 (b x * a y) (a x * b y) := by
      refine ⟨mul_ne_zero (hb0 x) (ha0 y), mul_ne_zero (ha0 x) (hb0 y), ?_, ?_, ?_, fun φ => ?_⟩
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (hb x).mul_left (isCoprime_span (ha y))
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (isCoprime_span (ha x)).mul_left (hb y)
      · have : b x * a y - a x * b y = b x * (a y - 1) - b y * (a x - 1) + (b x - b y) := by ring
        rw [this]
        exact 𝔮.add_mem (𝔮.sub_mem (𝔮.mul_mem_left _ (ha y)) (𝔮.mul_mem_left _ (ha x))) h2
      · have h4 : 0 < φ (a x : K) * φ (b x : K) ↔ 0 < φ (a y : K) * φ (b y : K) := (congrFun h3 φ).to_iff
        have h5 := mul_ne_zero (emb_ne_zero φ (ha0 x)) (emb_ne_zero φ (hb0 x))
        have h6 := mul_ne_zero (emb_ne_zero φ (ha0 y)) (emb_ne_zero φ (hb0 y))
        have h7 : 0 < (φ (a x : K) * φ (b x : K)) * (φ (a y : K) * φ (b y : K)) := by
          by_cases h : 0 < φ (a x : K) * φ (b x : K)
          · exact mul_pos h (h4.1 h)
          · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 h) h5)
              (lt_of_le_of_ne (not_lt.1 fun h' => h (h4.2 h')) h6)
        convert h7 using 1
        push_cast
        simp only [map_mul]
        ring
    have he : s x * Ideal.span {a x * b y} = s y * Ideal.span {b x * a y} := by
      have e1 := hab x
      have e2 := hab y
      rw [← h1] at e2
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        ← mul_assoc, mul_comm (s x), e1, mul_comm (s y), mul_assoc _ _ (s y), e2]
      ring
    have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, χ x = χ y := fun χ => by
      apply Units.ext
      rw [← hsx, ← hsx]
      exact heckeIdeal_eq_of_ray hR (hs0 x) (hs0 y) (hs x) (hs y) hp he χ
    by_contra hne
    letI : CommGroup (L ≃ₐ[K] L) := IsMulCommutative.instCommGroup
    obtain ⟨χ, h⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ
      (a := x * y⁻¹) (by rwa [ne_eq, mul_inv_eq_one])
    apply h
    rw [map_mul, map_inv, hχ χ, mul_inv_cancel]
  haveI : Finite (𝓞 K ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h𝔮
  rw [← IsGalois.card_aut_eq_finrank]
  refine (Nat.card_le_card_of_injective F hF).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_prod, Ideal.absNorm_apply, Submodule.cardQuot_apply, classNumber,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := _ → Prop)]
  simp

end GlobalTheory.FieldSize.RayDegree
end
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], AnisoSmall E → OrthoSmall E := by
  first | exact @GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | exact GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | (intros; apply GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E → ShortSmall E := by
  first | exact @GlobalTheory.SmoothForms.Short.shortSmall | exact GlobalTheory.SmoothForms.Short.shortSmall | (intros; apply GlobalTheory.SmoothForms.Short.shortSmall <;> assumption)
end
