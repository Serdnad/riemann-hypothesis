module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh24.Fv :
    (F : Type) →
      [inst : Field F] → [NumberField F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → Type :=
    fun (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

noncomputable def UpperTheory.Reformulated.B.Qh24.inclR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] → (R : Type) → [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] ↦
      Algebra.TensorProduct.includeRight.toRingHom

noncomputable def UpperTheory.Reformulated.B.Qh24.OEv :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
                Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E) :=
    fun {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      (↑(Submodule.span (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
            ((fun (x : NumberField.RingOfIntegers E) ↦
                (UpperTheory.Reformulated.B.Qh24.inclR (UpperTheory.Reformulated.B.Qh24.Fv F v) : E → TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E)
                  (↑x : E)) ''
              Set.univ)) :
        Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E))

theorem UpperTheory.Reformulated.B.Qh24.oev_mul :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      {s t : TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E},
      s ∈ UpperTheory.Reformulated.B.Qh24.OEv v → t ∈ UpperTheory.Reformulated.B.Qh24.OEv v → s * t ∈ UpperTheory.Reformulated.B.Qh24.OEv v := by
  intro F E _ _ _ _ _ v s t hs ht
  unfold UpperTheory.Reformulated.B.Qh24.OEv at *
  simp only [SetLike.mem_coe] at *
  induction hs using Submodule.span_induction with
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  | mem a ha =>
    induction ht using Submodule.span_induction with
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
    | mem b hb =>
      obtain ⟨x, -, rfl⟩ := ha
      obtain ⟨y, -, rfl⟩ := hb
      refine Submodule.subset_span ⟨x * y, Set.mem_univ _, ?_⟩
      beta_reduce
      rw [← map_mul]
      rfl
end

section

theorem UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K],
    Module.finrank ℚ K ≤ (2 : ℕ) →
      ∀ (P Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        P ≠ Q →
          Ideal.under ℤ P.asIdeal = Ideal.under ℤ Q.asIdeal →
            (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion K P → WithZero (Multiplicative ℤ))
                (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) P.asIdeal) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion K P) =
              WithZero.exp (-1 : ℤ) := by
  intro K _ _ hn P Q hPQ hunder
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have hQm : Q.asIdeal.IsMaximal := Q.isMaximal
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (IsDedekindDomain.HeightOneSpectrum.ext h)
  have hIprime : (Ideal.under ℤ P.asIdeal).IsPrime := Ideal.IsPrime.under ℤ P.asIdeal
  have hNP0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have hNmem : ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    simpa [Ideal.under_def, Ideal.mem_comap] using this
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.under ℤ P.asIdeal)).principal
  have hg' : Ideal.under ℤ P.asIdeal = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [hg', Ideal.mem_span_singleton] at hNmem
    exact hNP0 (by simpa using hNmem)
  have hgprime : Prime g := by
    rw [hg'] at hIprime
    exact (Ideal.span_singleton_prime hg0).1 hIprime
  set p : ℕ := g.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hgprime
  have hpI : (p : ℤ) ∈ Ideal.under ℤ P.asIdeal := by
    rw [hg', Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.2 dvd_rfl
  have hpP : (p : NumberField.RingOfIntegers K) ∈ P.asIdeal := by
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hpQ : (p : NumberField.RingOfIntegers K) ∈ Q.asIdeal := by
    rw [hunder] at hpI
    simpa [Ideal.under_def, Ideal.mem_comap] using hpI
  have hnorm : Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers K)}) =
      p ^ Module.finrank ℚ K := by
    have h : (p : NumberField.RingOfIntegers K) =
        algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) := by simp
    rw [Ideal.absNorm_span_singleton, h, Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast, NumberField.RingOfIntegers.rank]
  have hdvd : P.asIdeal * Q.asIdeal ∣ Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.dvd_iff_le, Ideal.mul_eq_inf_of_coprime (hPm.coprime_of_ne hQm hne)]
    exact le_inf ((Ideal.span_singleton_le_iff_mem _).2 hpP)
      ((Ideal.span_singleton_le_iff_mem _).2 hpQ)
  obtain ⟨J, hJ⟩ := hdvd
  have hprod : p ^ Module.finrank ℚ K =
      Ideal.absNorm P.asIdeal * Ideal.absNorm Q.asIdeal * Ideal.absNorm J := by
    rw [← hnorm, hJ, map_mul, map_mul]
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_assoc]) : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro _ (by rw [hprod, mul_comm (Ideal.absNorm P.asIdeal), mul_assoc]) :
      Ideal.absNorm Q.asIdeal ∣ p ^ Module.finrank ℚ K)
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1
    (Dvd.intro_left _ hprod.symm : Ideal.absNorm J ∣ p ^ Module.finrank ℚ K)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at ha
    exact hPm.ne_top ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hb
    exact hQm.ne_top hb
  have hexp : Module.finrank ℚ K = a + b + c := by
    apply Nat.pow_right_injective hp.two_le
    simp only
    rw [hprod, ha, hb, hc, pow_add, pow_add]
  have ha1 : a = 1 := by omega
  have hc0 : c = 0 := by omega
  have hNP : Ideal.absNorm P.asIdeal = p := by rw [ha, ha1, pow_one]
  have hJtop : J = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, hc, hc0, pow_zero]
  have hspan : Ideal.span {(p : NumberField.RingOfIntegers K)} = P.asIdeal * Q.asIdeal := by
    rw [hJ, hJtop, Ideal.mul_top]
  have hp0 : (p : NumberField.RingOfIntegers K) ≠ 0 := by
    intro h
    rw [h] at hnorm
    rw [Set.singleton_zero, Ideal.span_zero, Ideal.absNorm_bot] at hnorm
    exact pow_ne_zero _ hp.ne_zero hnorm.symm
  have h1 : P.intValuation (p : NumberField.RingOfIntegers K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_one]
    exact Dvd.intro _ rfl
  have h2 : ¬ P.intValuation (p : NumberField.RingOfIntegers K) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, hspan, pow_two]
    intro h
    have h3 : P.asIdeal ∣ Q.asIdeal := (mul_dvd_mul_iff_left P.ne_bot).1 h
    exact hne (hQm.eq_of_le hPm.ne_top (Ideal.dvd_iff_le.1 h3)).symm
  have hval : P.intValuation (p : NumberField.RingOfIntegers K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hp0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    omega
  rw [hNP]
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) P
    (p : NumberField.RingOfIntegers K)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval] at key
  simpa using key
end

section

theorem UpperTheory.Reformulated.B.ExistsValuationSubLeOne.exists_valuation_sub_le_one.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Type u_2} [inst_2 : Field K]
    [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K] (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (x : IsDedekindDomain.HeightOneSpectrum R → K),
    ∃ (k : K),
      (∀ v ∈ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) (k - x v) ≤
            (1 : WithZero (Multiplicative ℤ))) ∧
        ∀ v ∉ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) k ≤
            (1 : WithZero (Multiplicative ℤ)) := by
  classical
  intro R _ _ K _ _ _ S x
  obtain ⟨⟨d, hdm⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) S x
  simp only at hd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdm
  have hdK : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdm
  have hr : ∀ v, ∃ r : R, v ∈ S → algebraMap R K r = algebraMap R K d * x v := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hd v hv
      exact ⟨r, fun _ => by rw [hr, Algebra.smul_def]⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose r hr using hr
  have hI : Ideal.span {d} ≠ (0 : Ideal R) := by
    simpa using hd0
  let T : Finset (IsDedekindDomain.HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  have he : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      v.intValuation d = WithZero.exp (-(e v : ℤ)) := fun v => v.intValuation_if_neg hd0
  have he0 : ∀ v, v ∉ T → e v = 0 := by
    intro v hv
    have hmem : d ∉ v.asIdeal := by
      intro h
      apply hv
      simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact Or.inr (Ideal.dvd_span_singleton.2 h)
    have h1 := IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hmem
    rw [he, ← WithZero.exp_zero, WithZero.exp_inj] at h1
    omega
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : IsDedekindDomain.HeightOneSpectrum R => v.asIdeal) e
    (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then r v.1 else 0)
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (a : R), a ∈ v.asIdeal ^ e v →
      v.valuation K (algebraMap R K a / algebraMap R K d) ≤ 1 := by
    intro v a ha
    rw [map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, he]
    exact div_le_one_of_le₀ ((v.intValuation_le_pow_iff_mem a (e v)).2 ha) zero_le'
  refine ⟨algebraMap R K y / algebraMap R K d, fun v hv => ?_, fun v hv => ?_⟩
  · have hvT : v ∈ T := Finset.mem_union_left _ hv
    have h1 := hy v hvT
    simp only [hv, if_true] at h1
    have h2 := key v _ h1
    have h3 : algebraMap R K (y - r v) / algebraMap R K d =
        algebraMap R K y / algebraMap R K d - x v := by
      rw [map_sub, hr v hv]
      field_simp
    rwa [h3] at h2
  · apply key
    by_cases hvT : v ∈ T
    · have h1 := hy v hvT
      simpa [hv] using h1
    · simp [he0 v hvT]
end

section

namespace DedekindLocalUniformizer
end DedekindLocalUniformizer

theorem UpperTheory.Reformulated.B.Yde5.main :
    ∀ {R : Type} [inst : CommRing R] [IsDedekindDomain R] (P : Ideal R),
      P.IsMaximal → P ≠ ⊥ → ∃ (π : R), π ≠ (0 : R) ∧ π ∈ P ∧ ∃ s ∉ P, ∀ y ∈ P, ∃ (c : R), s * y = π * c := by
  intro R _ _ P hmax hbot
  haveI : P.IsPrime := hmax.isPrime
  have hlt : P ^ (1 + 1) < P ^ 1 := Ideal.pow_succ_lt_pow hbot 1
  rw [pow_one] at hlt
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hπ2 (Ideal.zero_mem _)
  refine ⟨π, hπ0, hπP, ?_⟩
  have hle : Ideal.span {π} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 hπP
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hπ2
    have : Ideal.span {π} ≤ P ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun y hy => ?_⟩
  have hmem : s * y ∈ Ideal.span {π} := by
    rw [hJ, mul_comm s y]; exact Ideal.mul_mem_mul hy hsJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨c, by rw [← hc, mul_comm]⟩
end

section

open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi11.Af :
    (F : Type) → [inst : Field F] → [NumberField F] → Type :=
    fun (F : Type) [Field F] [NumberField F] ↦ IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

theorem UpperTheory.Reformulated.B.Qi11.aux2 :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v),
      ∀ᶠ (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
        Pi.single v a x ∈
          (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F x) :
            Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F x)) := by
  intro F _ _ v a
  refine (Set.finite_singleton v).subset fun x hx => ?_
  by_contra h
  apply hx
  have hne : x ≠ v := h
  simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hne]
  exact zero_mem _

noncomputable def UpperTheory.Reformulated.B.Qi11.sglV :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
        (a : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ↦
      (⟨Pi.single v a, UpperTheory.Reformulated.B.Qi11.aux2 v a⟩ :
        { x :
          (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
            (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
              i //
          ∀ᶠ (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) in Filter.cofinite,
            x i ∈
              (fun (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
                  (↑(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) :
                    Set (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)))
                i })

noncomputable def UpperTheory.Reformulated.B.Qi11.sglS :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → UpperTheory.Reformulated.B.Qi11.Af F :=
    fun {F : Type} [Field F] [NumberField F]
        (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
      ∑ v ∈ A, UpperTheory.Reformulated.B.Qi11.sglV v (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)

private theorem UpperTheory.Reformulated.B.Qi11.tendsto_cut {ι : Type*} {R : ι → Type*} [∀ i, Zero (R i)]
    [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)} (h0 : ∀ i, (0 : R i) ∈ A i)
    (y z : RestrictedProduct R A Filter.cofinite) (hz : ∀ i, z i = 0)
    (f : Finset ι → RestrictedProduct R A Filter.cofinite)
    (hf : ∀ B i, f B i = if i ∈ B then 0 else y i) :
    Filter.Tendsto f Filter.atTop (nhds z) := by
  have hS : Filter.cofinite ≤ Filter.principal {i | y i ∈ A i} := Filter.le_principal_iff.2 y.2
  let g : Finset ι → RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := fun B =>
    ⟨fun i => if i ∈ B then 0 else y i, fun i hi => by
      show (if i ∈ B then 0 else y i) ∈ A i
      split_ifs
      · exact h0 i
      · exact hi⟩
  let o : RestrictedProduct R A (Filter.principal {i | y i ∈ A i}) := ⟨fun _ => 0, fun i _ => h0 i⟩
  have hg : Filter.Tendsto g Filter.atTop (nhds o) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with B hB
    have hi : i ∈ B := hB (Finset.mem_singleton_self i)
    show (0 : R i) = if i ∈ B then 0 else y i
    rw [if_pos hi]
  have h1 : f = RestrictedProduct.inclusion R A hS ∘ g :=
    funext fun B => RestrictedProduct.ext _ _ fun i => hf B i
  have h2 : z = RestrictedProduct.inclusion R A hS o := RestrictedProduct.ext _ _ fun i => hz i
  rw [h1, h2]
  exact ((RestrictedProduct.continuous_inclusion hS).tendsto o).comp hg

private theorem UpperTheory.Reformulated.B.Qi11.sglS_apply {F : Type} [Field F] [NumberField F]
    (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    UpperTheory.Reformulated.B.Qi11.sglS A w = if w ∈ A then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => rfl
  | insert v A hv ih =>
    have h : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) =
        UpperTheory.Reformulated.B.Qi11.sglV v 1 + UpperTheory.Reformulated.B.Qi11.sglS A := Finset.sum_insert hv
    have h' : UpperTheory.Reformulated.B.Qi11.sglS (insert v A) w =
        (Pi.single v 1 : ∀ u, IsDedekindDomain.HeightOneSpectrum.adicCompletion F u) w +
          UpperTheory.Reformulated.B.Qi11.sglS A w := by
      rw [h]
      rfl
    rw [h', ih]
    by_cases hw : w = v
    · subst hw
      simp [hv]
    · simp [hw]

theorem UpperTheory.Reformulated.B.Qi11.tendsto_fin :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : UpperTheory.Reformulated.B.Qi11.Af F),
      Filter.Tendsto
        (fun (A : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) ↦
          ((1 : UpperTheory.Reformulated.B.Qi11.Af F) - UpperTheory.Reformulated.B.Qi11.sglS A) * y)
        Filter.atTop (nhds (0 : UpperTheory.Reformulated.B.Qi11.Af F)) := by
  intro F _ _ y
  have key := UpperTheory.Reformulated.B.Qi11.tendsto_cut
    (R := fun v => IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)
    (A := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      SetLike.coe (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
    (fun v => zero_mem _)
  refine key y (0 : UpperTheory.Reformulated.B.Qi11.Af F) (fun w => ?_)
    (fun B => ((1 - UpperTheory.Reformulated.B.Qi11.sglS B) * y : UpperTheory.Reformulated.B.Qi11.Af F)) fun B w => ?_
  · rfl
  · show (1 - UpperTheory.Reformulated.B.Qi11.sglS B w) * y w = if w ∈ B then 0 else y w
    rw [UpperTheory.Reformulated.B.Qi11.sglS_apply]
    split_ifs <;> simp
end

section

theorem UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ :
    ∀ {R : Type} [inst : CommRing R]
    (I : Ideal R) (D : Derivation ℤ R R) {n : ℕ} {r : R}, r ∈ I ^ (n + (1 : ℕ)) → (D : R → R) r ∈ I ^ n := by
  intro R _ I D n
  induction n with
  | zero =>
    intro r _
    simp
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (ih ha) hb
    · intro x y hx hy
      rw [map_add (f := _)]
      exact Ideal.add_mem _ hx hy
end

section

noncomputable def UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers.{u_1} :
    {A : Type u_1} → [inst : CommRing A] → Ideal A → A → Ideal A :=
  fun {A} _ J a =>
    { carrier := {x : A | ∃ n : ℕ, a ^ n * x ∈ J}
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : a ^ (m + n) * (x + y) = a ^ n * (a ^ m * x) + a ^ m * (a ^ n * y) := by ring
        rw [h]
        exact J.add_mem (J.mul_mem_left _ hm) (J.mul_mem_left _ hn)
      zero_mem' := ⟨0, by rw [mul_zero]; exact J.zero_mem⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : a ^ n * (c • x) = c * (a ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact J.mul_mem_left _ hn }
end
