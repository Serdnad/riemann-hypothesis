module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza3.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

noncomputable def UpperTheory.Reformulated.B.Yza3.normV.{u_1} :
    {F : Type u_1} → [inst : Field F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ :=
    fun {F : Type u_1} [Field F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      Nat.card (NumberField.RingOfIntegers F ⧸ v.asIdeal)

namespace UpperTheory.Reformulated.B.Yza3

open NumberField in
private lemma exists_prime_gen (v : Pl) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  classical
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hprime : v.asIdeal.IsPrime := v.isPrime
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 ℚ, v.asIdeal = Ideal.span {g} :=
    haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
    (IsPrincipalIdealRing.principal v.asIdeal).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by simpa using hg)
  have hgp : Prime g := by
    rw [← Ideal.span_singleton_prime hg0, ← hg]
    exact hprime
  have hep : Prime (e g) := (MulEquiv.prime_iff e.toMulEquiv).2 hgp
  refine ⟨(e g).natAbs, Int.prime_iff_natAbs_prime.1 hep, ?_⟩
  rw [hg]
  have hassoc : Associated (e g) (((e g).natAbs : ℕ) : ℤ) := (Int.associated_natAbs _)
  have : Associated g (((e g).natAbs : ℕ) : 𝓞 ℚ) := by
    have h2 := hassoc.map e.symm.toMonoidHom
    generalize (e g).natAbs = n at h2 ⊢
    have h3 : e.symm.toMonoidHom (e g) = g := e.symm_apply_apply g
    have h4 : e.symm.toMonoidHom ((n : ℕ) : ℤ) = (n : 𝓞 ℚ) := map_natCast e.symm n
    rwa [h3, h4] at h2
  exact Ideal.span_singleton_eq_span_singleton.2 this

open NumberField in
private lemma eq_of_natCast_mem {p : ℕ} (hp : p.Prime) (v v' : Pl)
    (h : (p : 𝓞 ℚ) ∈ v.asIdeal) (h' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have key : ∀ u : Pl, (p : 𝓞 ℚ) ∈ u.asIdeal → u.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    intro u hu
    obtain ⟨q, hq, huq⟩ := exists_prime_gen u
    rw [huq] at hu ⊢
    have hd : (q : 𝓞 ℚ) ∣ (p : 𝓞 ℚ) := Ideal.mem_span_singleton.1 hu
    have hd' : (q : ℤ) ∣ (p : ℤ) := by
      have := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hd
      simpa using this
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd')
    rw [this]
  exact IsDedekindDomain.HeightOneSpectrum.ext ((key v h).trans (key v' h').symm)

open NumberField in
theorem htc_places :
    ∀ (w : UpperTheory.Reformulated.B.Yza3.Pl),
      UpperTheory.Reformulated.B.Yza3.normV w ≠ (0 : ℕ) ∧
        (∀ (v : UpperTheory.Reformulated.B.Yza3.Pl), v ≠ w → (↑(UpperTheory.Reformulated.B.Yza3.normV w) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal) ∧
          ∀ (p : ℕ),
            Nat.Prime p →
              ∀ (v v' : UpperTheory.Reformulated.B.Yza3.Pl),
                (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → (↑p : NumberField.RingOfIntegers ℚ) ∈ v'.asIdeal → v = v' := by
  intro w
  obtain ⟨p, hp, hw⟩ := exists_prime_gen w
  have hnorm : normV w = p := by
    have h1 : normV w = Ideal.absNorm w.asIdeal := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h1, hw, Ideal.absNorm_span_singleton]
    have : ((p : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  refine ⟨by rw [hnorm]; exact hp.ne_zero, ?_, fun q hq v v' => eq_of_natCast_mem hq v v'⟩
  intro v hvw hmem
  rw [hnorm] at hmem
  refine hvw (eq_of_natCast_mem hp v w hmem ?_)
  rw [hw]
  exact Ideal.mem_span_singleton_self _

end UpperTheory.Reformulated.B.Yza3
end

section

theorem UpperTheory.Reformulated.B.Qk5.dz_exists_prime :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers F) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers F) ∈ v.asIdeal := by
  intro F _ _ v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with ha | hb
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨p, hp, hd.mul_left a, hm⟩
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj17.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

theorem UpperTheory.Reformulated.B.Qj17.ho_exists_prime :
    ∀ (v : UpperTheory.Reformulated.B.Qj17.Pl) (n : ℕ),
      n ≠ (0 : ℕ) →
        (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
          ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_left a, hm⟩
end

section

theorem UpperTheory.Reformulated.B.Qk8.exists_place :
    ∀ {F : Type} [inst : Field F] [NumberField F] (p : ℕ),
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        (↑p : NumberField.RingOfIntegers F) ∈ w.asIdeal := by
  intro F _ _ p hp
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hinj : Function.Injective (algebraMap ℤ (NumberField.RingOfIntegers F)) :=
    (algebraMap ℤ (NumberField.RingOfIntegers F)).injective_int
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := NumberField.RingOfIntegers F) (Ideal.span {(p : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := hinj (by rw [hx, map_zero])
      rw [hx0]
      exact Ideal.zero_mem _)
  have hmem : (p : NumberField.RingOfIntegers F) ∈ Q := by
    have h : (p : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQP]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h
    exact h
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
end

section

theorem UpperTheory.Reformulated.B.Qi54.card_pow :
    ∀ {E : Type} [inst : Field E] [NumberField E]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (q : ℕ),
    Nat.Prime q →
      (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal →
        ∃ (f : ℕ), Nat.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) = q ^ f := by
  intro E _ _ w q hq hmem
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have h0 : (q : NumberField.RingOfIntegers E ⧸ w.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_natCast] at this
  haveI : CharP (NumberField.RingOfIntegers E ⧸ w.asIdeal) q :=
    (CharP.charP_iff_prime_eq_zero (p := q) (hp := hq)).mpr h0
  obtain ⟨n, -, hn⟩ := FiniteField.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) q
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe49.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.Qe49.exists_prime_mem :
    ∀ {E : Type} [inst : Field E] [NumberField E] (w : UpperTheory.Reformulated.B.Qe49.Plc E),
      ∃ (q : ℕ), Nat.Prime q ∧ (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ w
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  refine ⟨ringChar (NumberField.RingOfIntegers E ⧸ w.asIdeal),
    CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar
end

section

theorem UpperTheory.Reformulated.B.Qo8.exists_supported :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
    ∃ (π : NumberField.RingOfIntegers F),
      π ≠ (0 : NumberField.RingOfIntegers F) ∧
        π ∈ p.asIdeal ∧
          ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), v ≠ p → π ∉ v.asIdeal := by
  intro F _ _ p
  have hp : p.asIdeal ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) :=
    mem_nonZeroDivisors_of_ne_zero p.ne_bot
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite (ClassGroup.mk0 ⟨p.asIdeal, hp⟩)).exists_pow_eq_one
  rw [← map_pow] at hpow
  have hprin : (p.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (pow_mem hp n)).1 hpow
  obtain ⟨π, hπ⟩ := hprin
  have hπ' : p.asIdeal ^ n = Ideal.span {π} := hπ
  have hmem : π ∈ p.asIdeal ^ n := hπ' ▸ Ideal.mem_span_singleton_self π
  refine ⟨π, ?_, Ideal.pow_le_self hn.ne' hmem, ?_⟩
  · rintro rfl
    rw [Ideal.span_singleton_zero] at hπ'
    exact pow_ne_zero n p.ne_bot hπ'
  · intro v hv hπv
    have hle : p.asIdeal ^ n ≤ v.asIdeal := by
      rw [hπ', Ideal.span_le, Set.singleton_subset_iff]
      exact hπv
    have hle' : p.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
    exact hv (IsDedekindDomain.HeightOneSpectrum.ext
      (p.isMaximal.eq_of_le v.isPrime.ne_top hle').symm)
end

section

open NumberField

theorem UpperTheory.unramified_anti_invariant_local :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      Module.finrank F E = 2 →
      Algebra.Unramified (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E) →
      ∀ (ξ : E), ξ ≠ 0 → σ ξ = -ξ →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        ∃ (a b : NumberField.RingOfIntegers E) (n : NumberField.RingOfIntegers F),
          n ∉ v.asIdeal ∧ σ (a : E) = -(a : E) ∧ (a : E) * (b : E) = algebraMap F E (n : F) := by
  intro F E _ _ _ _ _ σ hr hU ξ hξ hσ v
  have hne : σ ξ ≠ ξ := by
    intro h
    rw [hσ] at h
    exact hξ (by linear_combination (-1 / 2 : E) * h)
  have hfix : ∀ y : E, σ y = y → ∃ c : F, algebraMap F E c = y := by
    intro y hy
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := hy
      rw [h] at this
      exact Algebra.mem_bot.mp this
    · have : ξ ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      exact absurd this hne
  have hinv : ∀ y : E, σ (σ y) = y := by
    intro y
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)) with h | h
    · have : ξ ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by
        show σ (σ ξ) = ξ
        rw [hσ, map_neg, hσ, neg_neg]
      rw [h] at this
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp this
      exact absurd (by rw [← hc, AlgHom.commutes]) hne
    · have : y ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by rw [h]; trivial
      exact this
  let τ : 𝓞 E →ₐ[𝓞 F] 𝓞 E := RingOfIntegers.mapAlgHom σ
  have hτ : ∀ x : 𝓞 E, ((τ x : 𝓞 E) : E) = σ x := fun _ => rfl
  have := v.isMaximal
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hx : ∃ x : 𝓞 E, x - τ x ∉ w := by
    by_contra hcon
    push Not at hcon
    have heq : AlgHom.id (𝓞 F) (𝓞 E) = τ :=
      Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw.ne_top)
        (fun x => Ideal.Quotient.eq.mpr (hcon x))
    have hall : ∀ x : 𝓞 E, σ x = x := fun x => by rw [← hτ, ← heq]; rfl
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ξ
    apply hne
    rw [← hpq, map_div₀]
    exact congrArg₂ (· / ·) (hall p) (hall q)
  obtain ⟨x, hx⟩ := hx
  set a : 𝓞 E := x - τ x with ha
  have hσa : σ (a : E) = -(a : E) := by
    have : (a : E) = x - σ x := by rw [← hτ]; rfl
    rw [this, map_sub, hinv, neg_sub]
  obtain ⟨c, hc⟩ := hfix ((a : E) * a) (by rw [map_mul, hσa, neg_mul_neg])
  have hci : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (B := E) , hc]
    exact a.isIntegral_coe.mul a.isIntegral_coe
  refine ⟨a, a, ⟨c, hci⟩, ?_, hσa, hc.symm⟩
  intro hn
  have h1 := (Ideal.mem_of_liesOver w v.asIdeal _).mp hn
  have h2 : algebraMap (𝓞 F) (𝓞 E) ⟨c, hci⟩ = a * a := by
    apply RingOfIntegers.ext
    exact hc
  rw [h2] at h1
  exact hx ((hw.isPrime.mem_or_mem h1).elim id id)
end

section

theorem UpperTheory.Reformulated.B.SpanDenominator.den_of_span :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {i : ℕ} (P : Ideal (NumberField.RingOfIntegers K))
      [inst_2 : P.IsPrime] (M : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      ∀
        x ∈
          Submodule.span ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
            (↑M : Set (Fin i → K)),
        ∃ s ∈ P.primeCompl, s • x ∈ M := by
  intro K _ _ i P _ M x hx
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span P.primeCompl
    ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
    (↑M : Set (Fin i → K)) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, t.2, ht⟩
end

section

noncomputable def UpperTheory.Reformulated.B.SpanTopFamily.Mι :
    {E K : Type} →
      [inst : Field E] →
        [inst_1 : Field K] →
          (O : ValuationSubring K) →
            (E →+* K) → {n : Type} → Submodule (NumberField.RingOfIntegers E) (n → E) → Submodule (↥O) (n → K) :=
    fun {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
        (L : Submodule (NumberField.RingOfIntegers E) (n → E)) ↦
      Submodule.span (↥O) ((fun (l : n → E) (j : n) ↦ (ι : E → K) (l j)) '' (↑L : Set (n → E)))

theorem UpperTheory.Reformulated.B.SpanTopFamily.span_top :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by
  intro E K _ _ _ O ι n _ _ L hL
  have key : ∀ v : n → E, v ∈ Submodule.span E (↑L : Set (n → E)) →
      (fun j => ι (v j)) ∈ Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero =>
      have : (fun j : n => ι ((0 : n → E) j)) = 0 := by
        funext j; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun j : n => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
        funext j; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun j : n => ι ((a • x) j)) = ι a • (fun j => ι (x j)) := by
        funext j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ' w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := key (Pi.single i 1) (by rw [hL]; trivial)
  have e : (fun j : n => ι ((Pi.single i 1 : n → E) j)) = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e] at h
  exact h
end

section

namespace UpperTheory.Reformulated.B.Yva3.Helpers

private lemma key {α ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) (u : Finset (ι → α)) :
    ∑ ξ ∈ u, ∏ i, f (ξ i) ≤ ∏ _i : ι, ∑' x, f x := by
  have h1 : ∑ ξ ∈ u, ∏ i, f (ξ i)
      ≤ ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ξ hξ
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ hξ
    · intro ξ _ _
      exact Finset.prod_nonneg fun i _ => h0 (ξ i)
  have h2 : ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i)
      = ∏ i, ∑ x ∈ u.image (fun η => η i), f x :=
    by rw [Finset.prod_univ_sum]
  have h3 : ∏ i, ∑ x ∈ u.image (fun η => η i), f x ≤ ∏ _i : ι, ∑' x, f x := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.sum_nonneg fun x _ => h0 x
    · intro i _
      exact hf.sum_le_tsum _ (fun x _ => h0 x)
  exact h1.trans (h2.le.trans h3)

private lemma summ {α ι : Type} [Fintype ι] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) : Summable fun (ξ : ι → α) ↦ ∏ i : ι, f (ξ i) := by
  classical
  exact summable_of_sum_le (fun ξ => Finset.prod_nonneg fun i _ => h0 (ξ i)) (key hf h0)

end UpperTheory.Reformulated.B.Yva3.Helpers

theorem UpperTheory.Reformulated.B.Yva3.main :
    ∀ {k : Type} [inst : Field k] [NumberField k] {ι : Type} [inst : Fintype ι] {f : k → ℝ},
      Summable f → (∀ (a : k), (0 : ℝ) ≤ f a) → Summable fun (ξ : ι → k) ↦ ∏ i : ι, f (ξ i) := by
  intro k _ _ ι _ f hf h0
  exact UpperTheory.Reformulated.B.Yva3.Helpers.summ hf h0
end
