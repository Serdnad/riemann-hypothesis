module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace KrullColonIdeal

variable {R : Type*} [CommRing R]

def colonI (s c : R) : Ideal R where
  carrier := {r | r * c ∈ Ideal.span {s}}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul]
    exact Ideal.add_mem _ hx hy
  zero_mem' := by simp
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ hx

theorem mem_colonI {s c r : R} : r ∈ colonI s c ↔ r * c ∈ Ideal.span {s} := Iff.rfl

theorem exists_prime_colon [IsNoetherianRing R] (s a : R) (ha : a ∉ Ideal.span {s}) :
    ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      ∀ q1 q2 : R, q1 * q2 ∈ colonI s b → q1 ∈ colonI s b ∨ q2 ∈ colonI s b := by
  classical
  have hS : ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      colonI s b = J} : Set (Ideal R)).Nonempty := ⟨colonI s a, a, ha, le_rfl, rfl⟩
  obtain ⟨M, hM, hmax⟩ : ∃ M ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)),
      ∀ I ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)), ¬ M < I := by
    first
    | exact set_has_maximal_iff_noetherian.mpr inferInstance _ hS
    | exact WellFounded.has_min (wellFounded_submodule_gt R R) _ hS
  obtain ⟨b, hb, hab, rfl⟩ := hM
  refine ⟨b, hb, hab, fun q1 q2 h => ?_⟩
  by_cases h1 : q1 ∈ colonI s b
  · exact Or.inl h1
  · right

    have hle : colonI s b ≤ colonI s (q1 * b) := by
      intro r hr
      rw [mem_colonI] at hr ⊢
      have e : r * (q1 * b) = q1 * (r * b) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ q1 hr
    have hnot : q1 * b ∉ Ideal.span {s} := fun h' => h1 (mem_colonI.2 h')
    have heq : colonI s b = colonI s (q1 * b) := by
      by_contra hne
      exact hmax _ ⟨q1 * b, hnot, hab.trans hle, rfl⟩ (lt_of_le_of_ne hle hne)
    rw [heq, mem_colonI]
    have h' := mem_colonI.1 h
    have e : q2 * (q1 * b) = q1 * q2 * b := by ring
    rw [e]
    exact h'

end KrullColonIdeal


open KrullColonIdeal in
theorem mem_of_mem_heightOne_localizations {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = x := open KrullColonIdeal in by
  classical

  obtain ⟨a, b, hb0, hxab⟩ : ∃ a b : R, b ≠ 0 ∧ x * algebraMap R K b = algebraMap R K a := by
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hx'⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    refine ⟨a, b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← hx']
    exact IsLocalization.mk'_spec K a ⟨b, hb⟩
  have hbK : algebraMap R K b ≠ 0 := by
    intro h
    apply hb0
    apply IsFractionRing.injective R K
    rw [h, map_zero]
  by_contra hne
  have ha : a ∉ Ideal.span {b} := by
    intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    apply hne
    refine ⟨r, ?_⟩
    apply mul_right_cancel₀ hbK
    rw [hxab, ← hr, map_mul]
  obtain ⟨c, hc, hac, hprime⟩ := exists_prime_colon b a ha
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (Ideal.zero_mem _)
  have hbP : b ∈ colonI b c := mem_colonI.2 (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self b))
  have hPne : colonI b c ≠ ⊥ := by
    intro h
    have hb' := hbP
    rw [h, Ideal.mem_bot] at hb'
    exact hb0 hb'
  have hPprime : (colonI b c).IsPrime := by
    refine ⟨?_, fun h => hprime _ _ h⟩
    refine (Ideal.ne_top_iff_one _).2 (fun h1 => hc ?_)
    have h1' := mem_colonI.1 h1
    rwa [one_mul] at h1'

  have key : ∃ q0 ∈ colonI b c, ∃ u : R, u ∉ colonI b c ∧ u * b = q0 * c := by
    by_contra hcon
    push_neg at hcon
    apply hc
    have hint : IsIntegral R (algebraMap R K c / algebraMap R K b) := by
      refine isIntegral_of_smul_mem_submodule
        (Submodule.map (Algebra.linearMap R K) (colonI b c)) ?_ ?_ _ ?_
      · intro hbot
        have hmem : algebraMap R K b ∈ Submodule.map (Algebra.linearMap R K) (colonI b c) :=
          Submodule.mem_map_of_mem hbP
        rw [hbot, Submodule.mem_bot] at hmem
        exact hbK hmem
      · exact (IsNoetherian.noetherian (colonI b c)).map _
      · intro n hn
        obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hn
        obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
        have hvP : v ∈ colonI b c := by
          by_contra hv'
          exact hcon q hq v hv' hv
        refine Submodule.mem_map.2 ⟨v, hvP, ?_⟩
        have hv2 : algebraMap R K v * algebraMap R K b = algebraMap R K q * algebraMap R K c := by
          rw [← map_mul, ← map_mul, hv]
        simp only [Algebra.linearMap_apply, smul_eq_mul]
        first
        | (rw [div_mul_eq_mul_div, eq_div_iff hbK]; linear_combination hv2)
        | (field_simp; linear_combination hv2)
        | (field_simp; linear_combination -hv2)
    obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R K r = algebraMap R K c / algebraMap R K b := by
      first
      | exact IsIntegrallyClosed.isIntegral_iff.1 hint
      | exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hrc : r * b = c := by
      apply IsFractionRing.injective R K
      rw [map_mul, hr]
      first
      | exact div_mul_cancel₀ _ hbK
      | field_simp
    exact Ideal.mem_span_singleton'.2 ⟨r, hrc⟩
  obtain ⟨q0, hq0, u, hu, huq⟩ := key
  have huP : ∀ q ∈ colonI b c, u * q ∈ Ideal.span {q0} := by
    intro q hq
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
    refine Ideal.mem_span_singleton'.2 ⟨v, ?_⟩
    apply mul_right_cancel₀ hc0
    linear_combination (-v) * huq + u * hv

  have hmin : colonI b c ∈ (Ideal.span {q0}).minimalPrimes := by
    refine ⟨⟨hPprime, ?_⟩, fun Q hQ hQP => ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hq0
    · intro q hq
      have huq' : u * q ∈ Q := hQ.2 (huP q hq)
      rcases hQ.1.mem_or_mem huq' with h | h
      · exact absurd (hQP h) hu
      · exact h
  haveI : Submodule.IsPrincipal (Ideal.span {q0}) := ⟨⟨q0, rfl⟩⟩
  have hle1 : (colonI b c).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {q0}) _ hmin
  have hge1 : (1 : ℕ∞) ≤ (colonI b c).height := by
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hPne
  have hheight : (colonI b c).height = 1 := le_antisymm hle1 hge1
  obtain ⟨a', s', hs', hs'x⟩ := hx (colonI b c) hPprime hheight
  apply hs'
  apply hac
  rw [mem_colonI]
  refine Ideal.mem_span_singleton'.2 ⟨a', ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_mul, ← hs'x, ← hxab]
  ring

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem regVert_eq_of_le_height_one {A : Type*} [CommRing A] [IsDomain A] {Q P : Ideal A} [Q.IsPrime]
    [P.IsPrime] (hQ : Q ≠ ⊥) (hQP : Q ≤ P) (hP : P.height = 1) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP hne
  have hbot : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.mpr hQ
  have hQle : Q.height ≤ 1 := hP ▸ Ideal.height_mono hQP
  have hQfin : Q.height ≠ ⊤ := ne_top_of_le_ne_top (by simp) hQle
  haveI : Q.FiniteHeight := ⟨Or.inr hQfin⟩
  haveI : (⊥ : Ideal A).FiniteHeight := ⟨Or.inr (by simp)⟩
  have h1 : (⊥ : Ideal A).height + 1 ≤ Q.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
  have h2 : Q.height + 1 ≤ P.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
  rw [hP] at h2
  have h3 : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal A).height + 1 + 1 := by gcongr; simp
      _ ≤ Q.height + 1 := by gcongr
      _ ≤ 1 := h2
  exact absurd h3 (by norm_num)

theorem regVert_valuationRing {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ValuationRing (Localization.AtPrime P) := by
  have hPne : P ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal A).height = 0 := by
      first
      | exact Ideal.height_bot
    rw [h0] at hP
    exact zero_ne_one hP
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have hmax : Ideal.map (algebraMap A (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hcm : Ideal.comap (algebraMap A (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = P := by
    first
    | exact Localization.AtPrime.under_maximalIdeal
  have hmne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥ := by
    rw [← hmax]
    intro h
    exact hPne ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hmne
  haveI : IsDomain (Localization.AtPrime P) := by
    first
    | infer_instance
  haveI hic : IsIntegrallyClosed (Localization.AtPrime P) := by
    first
    | exact isIntegrallyClosed_of_isLocalization P.primeCompl P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
  have huniq : ∃! Q' : Ideal (Localization.AtPrime P), Q' ≠ ⊥ ∧ Q'.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal _, ⟨hmne, inferInstance⟩, ?_⟩
    rintro Q' ⟨hQ'ne, hQ'p⟩
    haveI := hQ'p
    have hc : Q'.under A ≤ P := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'p.ne_top)).trans hcm.le
    have hcne : Q'.under A ≠ ⊥ := by
      intro h
      apply hQ'ne
      rw [← IsLocalization.map_under P.primeCompl (Localization.AtPrime P) Q', h, Ideal.map_bot]
    have heq := regVert_eq_of_le_height_one hcne hc hP
    rw [← IsLocalization.map_under P.primeCompl (Localization.AtPrime P) Q', heq, hmax]
  first
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 2).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq)
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 6).mpr (And.intro hic huniq))
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 4).mpr (And.intro hic huniq)

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

theorem ufd_mem_of_forall_prime {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (x : FractionRing R)
    (h : ∀ p : R, Prime p → ∃ a b : R, ¬ p ∣ b ∧ x * algebraMap R (FractionRing R) b =
      algebraMap R (FractionRing R) a) :
    ∃ a : R, x = algebraMap R (FractionRing R) a := by
  classical
  have key : ∀ c : R, c ≠ 0 → ∀ a0 : R, x * algebraMap R (FractionRing R) c =
      algebraMap R (FractionRing R) a0 → ∃ a : R, x = algebraMap R (FractionRing R) a := by
    intro c
    induction c using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h0; exact absurd rfl h0
    | h₂ u hu =>
      intro _ a0 hx
      refine ⟨a0 * ↑(hu.unit⁻¹), ?_⟩
      have hu' : algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹) = 1 := by
        rw [← map_mul]; simp
      calc x = x * (algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) ↑(hu.unit⁻¹)) := by
              rw [hu', mul_one]
        _ = algebraMap R (FractionRing R) (a0 * ↑(hu.unit⁻¹)) := by rw [← mul_assoc, hx, map_mul]
    | h₃ c p hc hp ih =>
      intro _ a0 hx
      obtain ⟨a, b, hpb, hab⟩ := h p hp
      have hinj := IsFractionRing.injective R (FractionRing R)
      have e1 : a * (p * c) = a0 * b := by
        apply hinj
        simp only [map_mul] at hx hab ⊢
        linear_combination (-(algebraMap R (FractionRing R) p * algebraMap R (FractionRing R) c)) * hab +
          algebraMap R (FractionRing R) b * hx
      have hpa0 : p ∣ a0 := by
        have : p ∣ a0 * b := ⟨a * c, by rw [← e1]; ring⟩
        rcases hp.dvd_or_dvd this with h1 | h1
        · exact h1
        · exact absurd h1 hpb
      obtain ⟨a1, rfl⟩ := hpa0
      have hp0 : algebraMap R (FractionRing R) p ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
        exact fun h' => hp.ne_zero (hinj h')
      refine ih hc a1 ?_
      apply mul_left_cancel₀ hp0
      simp only [map_mul] at hx ⊢
      linear_combination hx
  obtain ⟨a0, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine key c hc0 a0 ?_
  rw [div_mul_cancel₀]
  rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
  exact fun h' => hc0 (IsFractionRing.injective R (FractionRing R) h')

end ReciprocityTheory.ChartRestriction.G.T0
end
