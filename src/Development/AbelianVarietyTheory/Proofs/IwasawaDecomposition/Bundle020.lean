module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory

open IsLocalRing Polynomial in
private lemma residue_eval_map_eq {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    residue R ((P.map φ).eval x) =
      (P.map (residue A)).eval₂ (ResidueField.map φ) (residue R x) := by
  rw [eval_map, hom_eval₂, eval₂_map]
  congr 1


open IsLocalRing Polynomial in
theorem _root_.GlobalTheory.exists_hensel_generator_of_residue_finite_unramified : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], ((residue R).comp φ).Finite → ((residue R).comp φ).FormallyUnramified → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hunr
  have hcomp : (residue R).comp φ = (ResidueField.map φ).comp (residue A) :=
    RingHom.ext fun a => (ResidueField.map_residue φ a).symm
  rw [hcomp] at hfin hunr
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hfin.of_comp_finite
  haveI : Algebra.FormallyUnramified (ResidueField A) (ResidueField R) := hunr.of_comp
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) :=
    Algebra.FormallyUnramified.isSeparable _ _
  set pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) (ResidueField R)
  set f := minpoly (ResidueField A) pb.gen with hf
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hfroot : aeval pb.gen f = 0 := minpoly.aeval _ _
  have hfder : aeval pb.gen (derivative f) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ pb.gen).aeval_derivative_ne_zero hfroot
  obtain ⟨q, hqf, hqdeg, hqmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts f).2 (map_surjective (residue A) residue_surjective f)) hfmonic
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective pb.gen
  have key : ∀ (P : A[X]) (x : R), residue R x = pb.gen →
      residue R ((P.map φ).eval x) = aeval pb.gen (P.map (residue A)) := by
    intro P x hx
    rw [residue_eval_map_eq, hx]
    rfl
  obtain ⟨θ, hroot, hθ⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (q.map φ)
    (hqmonic.map φ) θ₀
    (by rw [← residue_eq_zero_iff, key _ _ hθ₀, hqf, hfroot])
    (by
      rw [derivative_map]
      change IsUnit (residue R _)
      rw [key _ _ hθ₀, ← derivative_map, hqf]
      exact isUnit_iff_ne_zero.2 hfder)
  have hθres : residue R θ = pb.gen := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hθ
  refine ⟨θ, q, hqmonic, hroot, ?_, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, key _ _ hθres, ← derivative_map, hqf]
    exact hfder
  · intro r
    obtain ⟨g, hg⟩ := pb.exists_eq_aeval' (residue R r)
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective g
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, key _ _ hθres, hP, hg, sub_self]
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, key _ _ hθres] at hmem
    have hzero : P.map (residue A) = 0 := by
      by_contra hne
      have h1 := minpoly.degree_le_of_ne_zero (ResidueField A) pb.gen hne hmem
      have h2 := natDegree_le_natDegree h1
      have h3 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hf, ← hqdeg] at h2
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hzero, coeff_zero]

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

private theorem exp_neg_le_of_natAbs_log_le {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) {n : ℕ}
    (h : (WithZero.log x).natAbs ≤ n) : WithZero.exp (-(n : ℤ)) ≤ x := by
  rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
  omega

theorem exists_approx_finite_places :
    ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)),
      Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 →
      ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
        Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  intro F _ _ ι _ w hw y c hc
  classical
  have hb : ∀ i, ∃ b : F, Valued.v (algebraMap F ((w i).adicCompletion F) b - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
    intro i
    let c' : (w i).adicCompletion F := algebraMap F ((w i).adicCompletion F) c⁻¹
    have hcc : c' * algebraMap F ((w i).adicCompletion F) c = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have ho : IsOpen ((fun z => (z - y i) * c') ⁻¹'
        ((Valued.v : Valuation ((w i).adicCompletion F) (WithZero (Multiplicative ℤ))).integer : Set ((w i).adicCompletion F))) :=
      (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
    obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w i)).exists_mem_open ho ⟨y i, by
      simp only [Set.mem_preimage, sub_self, zero_mul, SetLike.mem_coe]
      exact zero_mem _⟩
    refine ⟨b, ?_⟩
    have h1 : Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') ≤ 1 :=
      (Valuation.mem_integer_iff _ _).1 hb
    calc Valued.v (algebraMap F ((w i).adicCompletion F) b - y i)
        = Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') *
            Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
          rw [← map_mul, mul_assoc, hcc, mul_one]
      _ ≤ 1 * Valued.v (algebraMap F ((w i).adicCompletion F) c) := by gcongr
      _ = _ := one_mul _
  choose b hbv using hb
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 F))
    (Finset.univ : Finset ι) b
  have hd' : ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (d : 𝓞 F) • b i :=
    fun i => hd i (Finset.mem_univ i)
  choose r hr using hd'
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have ht : algebraMap (𝓞 F) F d * c ≠ 0 := mul_ne_zero hd0 hc
  obtain ⟨s0, hs0⟩ := exists_forall_sub_mem_ideal (s := Finset.univ) (fun i => (w i).asIdeal)
    (fun i => (WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs)
    (fun i _ => (w i).prime) (fun i _ j _ hij h => hij (hw (HeightOneSpectrum.ext h)))
    (fun i => r i.1)
  refine ⟨algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d, fun i => ?_⟩
  have hloc : (w i).valuation F (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i) ≤
      (w i).valuation F c := by
    have e1 : algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i =
        algebraMap (𝓞 F) F (s0 - r i) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hr i, Algebra.smul_def]
      field_simp
    have e2 : c = algebraMap (𝓞 F) F d * c / algebraMap (𝓞 F) F d := by
      field_simp
    have hint : (w i).intValuation (s0 - r i) ≤ WithZero.exp
        (-((WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs : ℤ)) :=
      ((w i).intValuation_le_pow_iff_mem _ _).2 (hs0 i (Finset.mem_univ i))
    have hv : (w i).valuation F (algebraMap (𝓞 F) F (s0 - r i)) ≤
        (w i).valuation F (algebraMap (𝓞 F) F d * c) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact hint.trans (exp_neg_le_of_natAbs_log_le ((Valuation.ne_zero_iff _).2 ht) le_rfl)
    rw [e1]
    conv_rhs => rw [e2]
    rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
    gcongr
  have e3 : ∀ x : F, Valued.v (algebraMap F ((w i).adicCompletion F) x) = (w i).valuation F x :=
    fun x => (w i).valuedAdicCompletion_eq_valuation' x
  calc Valued.v (algebraMap F ((w i).adicCompletion F)
        (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) - y i)
      = Valued.v ((algebraMap F ((w i).adicCompletion F)
          (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) -
            algebraMap F ((w i).adicCompletion F) (b i)) +
          (algebraMap F ((w i).adicCompletion F) (b i) - y i)) := by
        rw [sub_add_sub_cancel]
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ _ := max_le (by rw [← map_sub, e3, e3]; exact hloc) (hbv i)

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem mem_span_singleton_of_isNilpotent_of_associatedPrimes {R : Type} [CommRing R]
    [IsNoetherianRing R] (x : R)
    (hP : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      IsDomain (Localization.AtPrime P))
    {n : R} (hn : IsNilpotent n) : n ∈ Ideal.span {x} := by
  by_contra hnx
  have h0 : (Ideal.Quotient.mk (Ideal.span {x}) n) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hPa, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {x}) n) h0
  haveI : P.IsPrime := hPa.isPrime
  haveI := hP P hPa
  have hz : algebraMap R (Localization.AtPrime P) n = 0 :=
    (hn.map (algebraMap R (Localization.AtPrime P))).eq_zero
  obtain ⟨⟨s, hs⟩, hsn⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ n).1 hz
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk (Ideal.span {x}) s * Ideal.Quotient.mk (Ideal.span {x}) n = 0
  rw [← map_mul, hsn, map_zero]

theorem isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R →
      x ∈ Ideal.jacobson (⊥ : Ideal R) →
      (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
        IsDomain (Localization.AtPrime P)) → IsReduced R := by
  intro R _ _ x hx hj hP
  refine ⟨fun n hn => ?_⟩
  have key : ∀ k : ℕ, ∀ m : R, IsNilpotent m → m ∈ Ideal.span {x} ^ k := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      obtain ⟨m', rfl⟩ := Ideal.mem_span_singleton'.1
        (mem_span_singleton_of_isNilpotent_of_associatedPrimes x hP hm)
      have hm' : IsNilpotent m' := by
        obtain ⟨e, he⟩ := hm
        refine ⟨e, ?_⟩
        rw [mul_pow] at he
        exact (mem_nonZeroDivisors_iff_right.1 (pow_mem hx e)) _ he
      rw [pow_succ', mul_comm m' x]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (ih m' hm')
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ideal.span {x})
    ((Ideal.span_singleton_le_iff_mem _).2 (by simpa only [Ideal.jacobson_bot] using hj))
  have : n ∈ (⨅ i : ℕ, (Ideal.span {x}) ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    simpa [smul_eq_mul, Ideal.mul_top] using key i n hn
  rw [hK] at this
  simpa using this

end GlobalTheory
end

section

universe u_1

namespace GlobalTheory.SaturatedNotDvd

theorem exists_saturated {A : Type u_1} [CommRing A] [IsDomain A] {x a b : A} (hx : Prime x)
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥) (h : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) :
    ∃ K : Ideal A, K ≠ ⊥ ∧ (∀ u, x * u ∈ K → u ∈ K) ∧ ∀ r ∈ K, ∃ s ∈ K, a * r = b * s := by
  let K : Ideal A :=
    { carrier := {u | ∃ k : ℕ, x ^ k * u ∈ I}
      add_mem' := by
        rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        refine ⟨k + l, ?_⟩
        have e : x ^ (k + l) * (u + v) = x ^ l * (x ^ k * u) + x ^ k * (x ^ l * v) := by ring
        rw [e]
        exact I.add_mem (I.mul_mem_left _ hk) (I.mul_mem_left _ hl)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have e : x ^ k * (c • u) = c * (x ^ k * u) := by rw [smul_eq_mul]; ring
        rw [e]
        exact I.mul_mem_left _ hk }
  refine ⟨K, ?_, ?_, ?_⟩
  · intro hK
    apply hI
    rw [eq_bot_iff] at hK ⊢
    intro r hr
    exact hK (show ∃ k : ℕ, x ^ k * r ∈ I from ⟨0, by simpa using hr⟩)
  · rintro u ⟨k, hk⟩
    exact ⟨k + 1, by rw [pow_succ, mul_assoc]; exact hk⟩
  · rintro r ⟨k, hk⟩
    obtain ⟨s, hs, hrs⟩ := h _ hk
    have hdvd : x ^ k ∣ b * s := ⟨a * r, by rw [← hrs]; ring⟩
    obtain ⟨s', hs'⟩ := hx.pow_dvd_of_dvd_mul_left k hb hdvd
    refine ⟨s', ⟨k, by rw [← hs']; exact hs⟩, ?_⟩
    have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx.ne_zero
    apply mul_left_cancel₀ hxk
    calc x ^ k * (a * r) = a * (x ^ k * r) := by ring
      _ = b * s := hrs
      _ = b * (x ^ k * s') := by rw [hs']
      _ = x ^ k * (b * s') := by ring

theorem exists_not_dvd {A : Type u_1} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : ¬ IsUnit x) {K : Ideal A} (hK : K ≠ ⊥) (hs : ∀ u, x * u ∈ K → u ∈ K) :
    ∃ u ∈ K, ¬ x ∣ u := by
  by_contra hall
  push_neg at hall
  apply hK
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) K (IsNoetherian.noetherian K)
  · intro u hu
    obtain ⟨u', rfl⟩ := hall u hu
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) (hs u' hu)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)

theorem main : (let d1 : (A : Type u_1) → [CommRing A] → Prop := @(fun (A : Type u_1) [CommRing A] ↦ ∀ (a b : A) (I : Ideal A), b ≠ (0 : A) → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a); ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}, Prime x → d1 (A ⧸ Ideal.span {x}) → ∀ {a b : A}, ¬x ∣ b → ∀ {I : Ideal A}, I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a) := by
  intro d1 A _ _ _ _ x hx hd a b hb I hI h
  have hd' : ∀ (a b : A ⧸ Ideal.span {x}) (I : Ideal (A ⧸ Ideal.span {x})), b ≠ 0 → I ≠ ⊥ →
      (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a := hd
  obtain ⟨K, hK, hsat, hKa⟩ := exists_saturated hx hb hI h
  obtain ⟨u₀, hu₀, hxu⟩ := exists_not_dvd hx.not_unit hK hsat
  have hz : ∀ y : A, Ideal.Quotient.mk (Ideal.span {x}) y = 0 ↔ x ∣ y := fun y => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have step : ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c d : A, a = b * c + x * d ∧ ∀ r ∈ K, ∃ s ∈ K, d * r = b * s := by
    intro a ha
    have hdiv : Ideal.Quotient.mk (Ideal.span {x}) b ∣ Ideal.Quotient.mk (Ideal.span {x}) a := by
      refine hd' _ _ (K.map (Ideal.Quotient.mk (Ideal.span {x}))) (fun h0 => hb ((hz b).1 h0)) ?_ ?_
      · intro hbot
        have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {x})) hu₀
        rw [hbot, Ideal.mem_bot] at hm
        exact hxu ((hz _).1 hm)
      · intro r hr
        obtain ⟨r', hr', rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hr
        obtain ⟨s, hs, hrs⟩ := ha r' hr'
        exact ⟨_, Ideal.mem_map_of_mem _ hs, by rw [← map_mul, ← map_mul, hrs]⟩
    obtain ⟨c', hc'⟩ := hdiv
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
    have hxd : x ∣ a - b * c := (hz _).1 (by rw [map_sub, map_mul, hc', sub_self])
    obtain ⟨d, hdd⟩ := hxd
    refine ⟨c, d, by linear_combination hdd, ?_⟩
    intro r hr
    obtain ⟨s, hs, hrs⟩ := ha r hr
    have h1 : b * (s - c * r) = x * (d * r) := by linear_combination r * hdd - hrs
    have h2 : x ∣ s - c * r := (hx.dvd_or_dvd ⟨_, h1⟩).resolve_left hb
    obtain ⟨w, hw⟩ := h2
    have hwK : w ∈ K := hsat w (hw ▸ K.sub_mem hs (K.mul_mem_left c hr))
    refine ⟨w, hwK, ?_⟩
    apply mul_left_cancel₀ hx.ne_zero
    rw [← h1, hw]; ring
  have iter : ∀ n : ℕ, ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c y : A, a = b * c + x ^ n * y := by
    intro n
    induction n with
    | zero => intro a _; exact ⟨0, a, by simp⟩
    | succ n ih =>
      intro a ha
      obtain ⟨c, d, rfl, hd2⟩ := step a ha
      obtain ⟨c', y, rfl⟩ := ih d hd2
      exact ⟨c + x * c', y, by ring⟩
  have hne : Ideal.span {x} ≠ ⊤ := fun h => hx.not_unit (Ideal.span_singleton_eq_top.1 h)
  have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ Ideal.span {b})
    (Ideal.span {x}) hne
  have hmem : Ideal.Quotient.mk (Ideal.span {b}) a ∈
      (⨅ i : ℕ, Ideal.span {x} ^ i • ⊤ : Submodule A (A ⧸ Ideal.span {b})) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨c, y, hcy⟩ := iter n a hKa
    have : Ideal.Quotient.mk (Ideal.span {b}) a
        = x ^ n • Ideal.Quotient.mk (Ideal.span {b}) y := by
      change _ = Ideal.Quotient.mk (Ideal.span {b}) (x ^ n * y)
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨c, by rw [hcy]; ring⟩
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n)
      Submodule.mem_top
  rw [hk, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem

end GlobalTheory.SaturatedNotDvd
end

section

open MvPolynomial

namespace GlobalTheory

theorem mem_span_map_of_eval_mem (k : Type) [Field k] [Infinite k] (σ τ : Type)
    (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k) (hD : D ≠ 0)
    (P : MvPolynomial σ (MvPolynomial τ k))
    (hP : ∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) :
    P ∈ Submodule.span (MvPolynomial τ k)
      (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  classical
  let Γ : Finset (τ →₀ ℕ) := P.support.biUnion (fun m => (AddMonoidAlgebra.coeff P m).support)
  let Q : (τ →₀ ℕ) → MvPolynomial σ k := fun γ =>
    ∑ m ∈ P.support, monomial m (AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ)
  have hQ : ∀ γ m, AddMonoidAlgebra.coeff (Q γ) m = AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ := by
    intro γ m
    simp only [Q, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [notMem_support_iff.mp h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hdec : P = ∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ) := by
    ext m : 1
    rw [coeff_sum]
    simp only [MvPolynomial.coeff_smul, coeff_map, hQ, smul_eq_mul, MvPolynomial.algebraMap_eq]
    have : ∀ γ, (monomial γ (1 : k) : MvPolynomial τ k) * C (AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ) = monomial γ (AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff P m) γ) := by
      intro γ; rw [mul_comm, C_mul_monomial, mul_one]
    simp only [this]
    by_cases hm : m ∈ P.support
    · conv_lhs => rw [as_sum (AddMonoidAlgebra.coeff P m)]
      apply Finset.sum_subset
      · intro γ hγ; exact Finset.mem_biUnion.mpr ⟨m, hm, hγ⟩
      · intro γ _ hγ; rw [notMem_support_iff.mp hγ, monomial_zero]
    · rw [notMem_support_iff.mp hm]
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, monomial_zero,
        Finset.sum_const_zero]
  have hevid : ∀ y : τ → k, (eval y).comp (algebraMap k (MvPolynomial τ k)) = RingHom.id k := by
    intro y; ext c; simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, eval_C, RingHom.id_apply]
  have hevP : ∀ y : τ → k, map (eval y) P =
      ∑ γ ∈ Γ, (eval y (monomial γ (1 : k) : MvPolynomial τ k)) • Q γ := by
    intro y
    conv_lhs => rw [hdec]

    rw [map_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [smul_eq_C_mul, map_mul, map_C, map_map, hevid, map_id, smul_eq_C_mul]
  have hQM : ∀ γ ∈ Γ, Q γ ∈ M := by
    intro β hβ
    by_contra hnot
    obtain ⟨L, hLβ, hLM⟩ := Submodule.exists_le_ker_of_notMem hnot
    let R : MvPolynomial τ k := ∑ γ ∈ Γ, monomial γ (L (Q γ))
    have hR : ∀ y : τ → k, eval y R = L (map (eval y) P) := by
      intro y

      rw [hevP, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun γ _ => ?_)
      rw [map_smul, smul_eq_mul, eval_monomial, eval_monomial, mul_comm, one_mul]
    have hRD : R * D = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_mul, map_zero]
      by_cases hy : eval y D = 0
      · rw [hy, mul_zero]
      · rw [hR, LinearMap.mem_ker.mp (hLM (hP y hy)), zero_mul]
    have hR0 : R = 0 := (mul_eq_zero.mp hRD).resolve_right hD
    have hcoef : AddMonoidAlgebra.coeff R β = L (Q β) := by
      simp only [R, coeff_sum, coeff_monomial]
      rw [Finset.sum_ite_eq', ite_eq_left hβ]
    exact hLβ (by simp only [← hcoef, hR0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply])
  suffices h : (∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ)) ∈
      Submodule.span (MvPolynomial τ k)
        (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) by
    rwa [← hdec] at h
  refine Submodule.sum_mem _ (fun γ hγ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨Q γ, hQM γ hγ, rfl⟩

end GlobalTheory
end
