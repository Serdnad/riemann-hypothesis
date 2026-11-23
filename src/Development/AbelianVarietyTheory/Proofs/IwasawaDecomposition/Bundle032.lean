module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle022
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle020
public import Mathlib.Algebra.Module.SpanRankOperations
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Mathlib.RingTheory.FractionalIdeal.Operations

@[expose] public section

section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_injective_tensor_into_tensor_fractionFields : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U], ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧ ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  first | exact @GlobalTheory.flat_tensor_embeds_tensor_fractionFields | exact GlobalTheory.flat_tensor_embeds_tensor_fractionFields | (intros; apply GlobalTheory.flat_tensor_embeds_tensor_fractionFields <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

theorem isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes
    (R : Type) [CommRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ nonZeroDivisors R)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P))
    (hcond : ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) :
    IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro c hc
  obtain ⟨s, hs⟩ := hcond c hc

  suffices hmem : Ideal.Quotient.mk (Ideal.span {x}) s = 0 by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hmem
    obtain ⟨w, rfl⟩ := hmem
    refine ⟨w, ?_⟩
    have hu : IsUnit (algebraMap R (FractionRing R) x) :=
      IsLocalization.map_units (FractionRing R) ⟨x, hx⟩
    apply hu.mul_left_cancel
    rw [← hs, map_mul, mul_comm]
  have key := eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
    (A := R) (M := R ⧸ Ideal.span {x}) (x := Ideal.Quotient.mk (Ideal.span {x}) s)
  apply key
  intro P hP
  haveI hPp : P.IsPrime := hP.isPrime
  obtain ⟨hdom, hic⟩ := hloc P hP
  let RP := Localization.AtPrime P
  let K := FractionRing RP

  have hreg : ∀ b ∈ nonZeroDivisors R, IsUnit (algebraMap R K b) := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R RP K]
    refine IsLocalization.map_units K (⟨algebraMap R RP b, ?_⟩ : nonZeroDivisors RP)
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl RP b).1 h0
    have : (t : R) = 0 := (mem_nonZeroDivisors_iff_right.1 hb) t ht
    exact t.2 (this ▸ P.zero_mem)
  let φ : FractionRing R →+* K :=
    IsLocalization.lift (M := nonZeroDivisors R) (g := algebraMap R K) fun b ↦ hreg b b.2
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap RP K (algebraMap R RP r) :=
    fun r ↦ by
      rw [IsLocalization.lift_eq, IsScalarTower.algebraMap_apply R RP K]
  have hint : IsIntegral RP (φ c) := by
    refine IsIntegral.map_of_comp_eq (algebraMap R RP) φ ?_ hc
    ext r
    simp only [RingHom.comp_apply]
    rw [hφ]
  obtain ⟨u, hu⟩ := (isIntegrallyClosed_iff K).1 hic hint
  have hxu : algebraMap R RP x * u = algebraMap R RP s := by
    apply IsFractionRing.injective RP K
    rw [map_mul, hu, ← hφ, ← hφ, hs, map_mul]
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj P.primeCompl u
  have h2 : algebraMap R RP (x * r) = algebraMap R RP (s * t) := by
    simp only at hrt
    rw [map_mul, map_mul, ← hxu, ← hrt]
    ring
  obtain ⟨t', ht'⟩ := (IsLocalization.eq_iff_exists P.primeCompl RP).1 h2
  refine ⟨t' * t, P.primeCompl.mul_mem t'.2 t.2, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  refine ⟨t' * r, ?_⟩
  linear_combination ht'

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → x ∈ Ideal.jacobson (⊥ : Ideal R) → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → IsDomain (Localization.AtPrime P)) → IsReduced R := by
  first | exact @GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes | exact GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes | (intros; apply GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R], IsIntegrallyClosed R → IsDomain R := by
  first | exact @GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | exact GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | (intros; apply GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_basis_of_integral_with_trace_in_base : ∀ (T C F K : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C], ∃ (n : ℕ) (b : Module.Basis (Fin n) F K), (∀ i, ∃ c : C, algebraMap C K c = b i) ∧ ∀ i j, ∃ t : T, algebraMap T F t = Algebra.trace F K (b i * b j) := by
  first | exact @GlobalTheory.exists_basis_in_finite_domain_trace_mem | exact GlobalTheory.exists_basis_in_finite_domain_trace_mem | (intros; apply GlobalTheory.exists_basis_in_finite_domain_trace_mem <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor : ∀ (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S] (e : S ≃+* R × S') (d : S), (∀ c : FractionRing S, IsIntegral S c → ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) → ∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  first | exact @GlobalTheory.conductor_prod_fst | exact GlobalTheory.conductor_prod_fst | (intros; apply GlobalTheory.conductor_prod_fst <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero : ∀ (k : Type) [Field k] [Infinite k] (σ τ : Type) (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k), D ≠ 0 → ∀ P : MvPolynomial σ (MvPolynomial τ k), (∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) → P ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  first | exact @GlobalTheory.mem_span_map_of_eval_mem | exact GlobalTheory.mem_span_map_of_eval_mem | (intros; apply GlobalTheory.mem_span_map_of_eval_mem <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

namespace RegularNormal

def StableDvd (A : Type*) [CommRing A] : Prop :=
  ∀ (a b : A) (I : Ideal A), b ≠ 0 → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a

theorem StableDvd.isIntegrallyClosed {A : Type*} [CommRing A] [IsDomain A] (h : StableDvd A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) y
  set K := FractionRing A
  set y : K := algebraMap A K a / algebraMap A K b with hydef
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := by
    simpa using hb0
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  obtain ⟨d, hd, hdN⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A)
    hy.fg_adjoin_singleton
  let I : Ideal A :=
    { carrier := {r | ∀ z ∈ Algebra.adjoin A {y}, ∃ s : A, algebraMap A K s = r • z}
      zero_mem' := fun z _ => ⟨0, by simp⟩
      add_mem' := by
        intro r r' hr hr' z hz
        obtain ⟨s, hs⟩ := hr z hz
        obtain ⟨s', hs'⟩ := hr' z hz
        exact ⟨s + s', by rw [map_add (f := _), hs, hs', add_smul]⟩
      smul_mem' := by
        intro c r hr z hz
        obtain ⟨s, hs⟩ := hr z hz
        exact ⟨c * s, by rw [map_mul, hs, smul_eq_mul, mul_smul, Algebra.smul_def c]⟩ }
  have hyN : y ∈ Algebra.adjoin A {y} := Algebra.self_mem_adjoin_singleton A y
  have hdI : d ∈ I := fun z hz => hdN z hz
  have hI : I ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero hd (by simpa [h0] using hdI)
  obtain ⟨c, hc⟩ := h a b I hb0 hI (by
    intro r hr
    obtain ⟨s, hs⟩ := hr y hyN
    refine ⟨s, fun z hz => ?_, hinj ?_⟩
    · obtain ⟨t, ht⟩ := hr (y * z) (mul_mem hyN hz)
      refine ⟨t, ?_⟩
      rw [ht, Algebra.smul_def s, hs, smul_mul_assoc]
    · rw [map_mul, map_mul, hs, Algebra.smul_def, hydef, mul_left_comm, mul_div_cancel₀ _ hbK, mul_comm])
  refine ⟨c, ?_⟩
  rw [hydef, hc, map_mul, mul_div_cancel_left₀ _ hbK]

section Step

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}

theorem dvd_of_not_dvd (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) {a b : A}
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) : b ∣ a := by
  first
  | exact @_root_.GlobalTheory.SaturatedNotDvd.main
  | exact _root_.GlobalTheory.SaturatedNotDvd.main
  | (apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedNotDvd.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedNotDvd.main ..)


omit [IsLocalRing A] in
theorem prime_dvd_of_stable (hx : Prime x) {a b : A} {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = x * b * s) : x ∣ a := by
  by_contra ha
  have key : ∀ k : ℕ, ∀ r ∈ I, x ^ k ∣ r := by
    intro k
    induction k with
    | zero => intro r _; simp
    | succ k ih =>
      intro r hr
      obtain ⟨s, hs, e⟩ := hst r hr
      obtain ⟨v, rfl⟩ := ih s hs
      exact hx.pow_dvd_of_dvd_mul_left (k + 1) ha ⟨b * v, by linear_combination e⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨n, c, hc, e⟩ := WfDvdMonoid.max_power_factor' hr0 hx.not_unit
  obtain ⟨v, hv⟩ := key (n + 1) r hr
  refine hc ⟨v, mul_left_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩
  linear_combination hv - e

theorem StableDvd.of_quotient (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) :
    StableDvd A := by
  intro a b I hb hI hst
  obtain ⟨n, c, hc, rfl⟩ := WfDvdMonoid.max_power_factor' hb hx.not_unit
  clear hb
  induction n generalizing a with
  | zero =>
    rw [pow_zero, one_mul] at hst ⊢
    exact dvd_of_not_dvd hx h hc hI hst
  | succ n ih =>
    obtain ⟨a, rfl⟩ := prime_dvd_of_stable hx (a := a) (b := x ^ n * c) hI (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, by linear_combination e⟩)
    obtain ⟨v, hv⟩ := ih a (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, mul_left_cancel₀ hx.ne_zero (by linear_combination e)⟩)
    exact ⟨v, by rw [hv]; ring⟩

end Step

open ReciprocityTheory.CA.AB.RegA in
theorem stableDvd_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) = n → StableDvd R := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R _ _ hn
  have : IsDomain R := IsRegularLocalRing.isDomain R
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · have h0 := IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R hsq
    intro a b I hb _ _
    refine IsUnit.dvd ?_
    by_contra hu
    have : b ∈ maximalIdeal R := hu
    rw [h0] at this
    exact hb this
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (zero_mem _)
  have hquot := IsRegularLocalRing.quotient_span_singleton hx hx2
  have hxp : Prime x := by
    rw [← Ideal.span_singleton_prime hx0, ← Ideal.Quotient.isDomain_iff_prime]
    exact IsRegularLocalRing.isDomain _
  refine StableDvd.of_quotient hxp (IH _ ?_ _ rfl)
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have h2 : Submodule.spanFinrank (maximalIdeal R)
      = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  omega

end RegularNormal

theorem isDomain_and_isIntegrallyClosed_of_isRegularLocalRing :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  intro T _ _
  have hd : IsDomain T := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain T
  exact ⟨hd, (RegularNormal.stableDvd_of_spanFinrank_eq _ T rfl).isIntegrallyClosed⟩

end GlobalTheory
end
