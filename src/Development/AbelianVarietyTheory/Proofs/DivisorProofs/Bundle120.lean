module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.DomDVR



theorem exists_dominating_dvr : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  intro F _ _ T' hT s h1 hmul
  classical
  haveI := hT
  set A := Submodule.span T' (s : Set F) with hA
  have hAmul : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A := by
    intro x y hx hy
    have : A * A ≤ A := by
      rw [hA, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
    exact this (Submodule.mul_mem_mul hx hy)
  have hsm : ∀ d ∈ T', ∀ a ∈ A, d * a ∈ A := fun d hd a ha => A.smul_mem ⟨d, hd⟩ ha
  let Asub : Subalgebra T' F := A.toSubalgebra h1 hAmul
  have hint : ∀ x ∈ s, IsIntegral T' x := fun x hx =>
    IsIntegral.of_mem_of_fg Asub (Submodule.fg_span s.finite_toSet) x (Submodule.subset_span hx)
  let K := FractionRing T'
  have hι : Function.Injective (T'.subtype) := Subtype.val_injective
  letI : Algebra K F := (IsFractionRing.lift (K := K) hι).toAlgebra
  haveI : IsScalarTower T' K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap (K := K) hι x).symm)
  have hintK : ∀ x ∈ (s : Set F), IsIntegral K x := fun x hx => (hint x hx).tower_top
  let L := IntermediateField.adjoin K (s : Set F)
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin hintK
  haveI : CharZero K := (algebraMap K F).charZero
  haveI : Algebra.IsSeparable K L := inferInstance
  let C := integralClosure T' L
  haveI : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain T' K L C

  have hLF : ∀ a : T', ((algebraMap T' L a : L) : F) = a := by
    intro a
    rw [IsScalarTower.algebraMap_apply T' K L]
    show algebraMap K F (algebraMap T' K a) = a
    exact IsFractionRing.lift_algebraMap (K := K) hι a
  have hcoe : ∀ a : T', (((algebraMap T' C a : C) : L) : F) = a := by
    intro a
    rw [← hLF a, IsScalarTower.algebraMap_apply T' C L]
    rfl
  have hinjC : Function.Injective (algebraMap T' C) := fun a b h => Subtype.val_injective (by
    have := congrArg (fun c : C => ((c : L) : F)) h
    simpa only [hcoe] using this)
  obtain ⟨P, hPmax, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (maximalIdeal T')
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinjC]; exact bot_le)
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field T'
    rw [← hPm, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinjC)]
  let Loc := Localization.AtPrime P
  haveI : IsDiscreteValuationRing Loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot Loc
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap C L y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (by
      rw [show (y : C) = 0 from Subtype.ext (by simpa using h)]; exact P.zero_mem)
  let ψ : Loc →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hψ : Function.Injective ψ := (IsLocalization.lift_injective_iff hunit).2 fun x y =>
    ⟨fun h => by rw [IsLocalization.injective Loc P.primeCompl_le_nonZeroDivisors h], fun h => by rw [Subtype.val_injective h]⟩
  let φ : Loc →+* F := (algebraMap L F).comp ψ
  have hφ : Function.Injective φ := fun a b h => hψ ((algebraMap L F).injective h)
  have hφc : ∀ c : C, φ (algebraMap C Loc c) = ((c : L) : F) := by
    intro c
    show ((ψ (algebraMap C Loc c) : L) : F) = _
    rw [IsLocalization.lift_eq]
    rfl
  let T'' := φ.range
  let e : Loc ≃+* T'' := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => hφ (by simpa only [RingHom.coe_rangeRestrict] using congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  refine ⟨T'', IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact RingHom.mem_range.2 ⟨algebraMap C Loc (algebraMap T' C ⟨x, hx⟩), by rw [hφc, hcoe]⟩
  · intro x hx
    have hxL : x ∈ L := IntermediateField.subset_adjoin K _ hx
    have hxC : (⟨x, hxL⟩ : L) ∈ C := by
      rw [mem_integralClosure_iff]
      let f : L →ₐ[T'] F := { toRingHom := algebraMap L F, commutes' := fun a => hLF a }
      exact (isIntegral_algHom_iff f (algebraMap L F).injective).1 (hint x hx)
    exact RingHom.mem_range.2 ⟨algebraMap C Loc ⟨⟨x, hxL⟩, hxC⟩, by rw [hφc]⟩
  · rintro x hx ⟨y, hy, hxy⟩
    by_contra hne
    have hnu : (⟨x, hx⟩ : T') ∈ maximalIdeal T' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      exact hne ⟨b, b.2, congrArg Subtype.val hb⟩
    have hP : algebraMap T' C ⟨x, hx⟩ ∈ P := by
      rw [← hPm] at hnu; exact hnu
    have hmax : algebraMap C Loc (algebraMap T' C ⟨x, hx⟩) ∈ maximalIdeal Loc :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff Loc P _).2 hP
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    apply (IsLocalRing.mem_maximalIdeal _).1 hmax
    refine isUnit_iff_exists_inv.2 ⟨z, hφ ?_⟩
    rw [map_mul, map_one, hφc, hcoe]; exact hxy
  · let M : Subalgebra K F :=
      { carrier := {y | ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ A}
        mul_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a * b) = (d1 * a) * (d2 * b) by ring]; exact hAmul _ _ ha hb⟩
        add_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a + b) = d2 * (d1 * a) + d1 * (d2 * b) by ring]
            exact A.add_mem (hsm _ hd2 _ ha) (hsm _ hd1 _ hb)⟩
        algebraMap_mem' := by
          intro k
          obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T') k
          have hb : ((b : T') : F) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
          refine ⟨(b : T'), (b : T').2, hb, ?_⟩
          have e1 : algebraMap K F (IsLocalization.mk' K a b) = (a : F) / ((b : T') : F) :=
            IsFractionRing.lift_mk' hι a b
          have e2 : ((b : T') : F) * ((a : F) / ((b : T') : F)) = a := by field_simp
          rw [e1, e2]
          simpa using hsm _ a.2 _ h1 }
    have hLM : ∀ y ∈ L, y ∈ M := by
      intro y hy
      have e := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := K) (S := (s : Set F))
        (fun x hx => (hintK x hx).isAlgebraic)
      have hy' : y ∈ Algebra.adjoin K (s : Set F) := by rw [← e]; exact hy
      refine (Algebra.adjoin_le ?_ : Algebra.adjoin K (s : Set F) ≤ M) hy'
      intro x hx
      exact ⟨1, T'.one_mem, one_ne_zero, by rw [one_mul]; exact Submodule.subset_span hx⟩
    intro y hy
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    exact hLM _ (ψ z).2
end GlobalTheory.DomDVR
end

section

namespace GlobalTheory

theorem eq_zero_of_sum_eq_zero_of_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R] {ϖ : R}
    (hϖ : Irreducible ϖ) {e : ℕ} (c : Fin e → R)
    (hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : R), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n))
    (hsum : ∑ i, c i = 0) : ∀ i, c i = 0 := by
  classical
  by_contra hne
  push_neg at hne
  choose! n w hw hcw using hc
  set S := Finset.univ.filter (fun i => c i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => i.val + e * n i) hSne
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0S).2
  have hdvd : ∀ i ∈ Finset.univ.erase i0, ϖ ^ (i0.val + e * n i0 + 1) ∣ c i := by
    intro i hi
    have hii0 : i ≠ i0 := Finset.ne_of_mem_erase hi
    by_cases hci : c i = 0
    · rw [hci]; exact dvd_zero _
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩
      have hle : i0.val + e * n i0 ≤ i.val + e * n i := hmin i hiS
      have hne' : i.val + e * n i ≠ i0.val + e * n i0 := by
        intro heq
        apply hii0
        apply Fin.ext
        have h1 : (i.val + e * n i) % e = i.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
        have h2 : (i0.val + e * n i0) % e = i0.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.isLt]
        rw [← h1, ← h2, heq]
      rw [hcw i hci]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  obtain ⟨X, hX⟩ := Finset.dvd_sum hdvd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hX, hcw i0 hi0] at hsum
  have h0 : ϖ ^ (i0.val + e * n i0) * (w i0 + ϖ * X) = 0 := by rw [← hsum]; ring
  have h1 : w i0 + ϖ * X = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ.ne_zero)
  have h2 : ϖ ∣ w i0 := ⟨-X, by linear_combination h1⟩
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h2 (hw i0 hi0))

theorem ramification_le_card_of_span :
    ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' →
      IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''),
      (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F),
      (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) →
      ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧
        Associated (Subring.inclusion h π) (ϖ ^ e) := by
  intro F _ T' T'' h1 h2 h hdom s hspan π hπ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T''
  have hπ0 : Subring.inclusion h π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ
  refine ⟨ϖ, hϖ, e, ?_, ?_, he⟩
  · rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exfalso
      rw [pow_zero] at he
      have hu : IsUnit (Subring.inclusion h π) := he.isUnit_iff.2 isUnit_one
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      obtain ⟨z, hzT', hz⟩ := hdom (π : F) π.2
        ⟨(y : F), y.2, by simpa using congrArg Subtype.val hy⟩
      exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨⟨z, hzT'⟩, Subtype.ext hz⟩)
    · exact hpos
  ·
    choose d hdT hd0 hdspan using
      fun i : Fin e => hspan ((ϖ ^ (i : ℕ) : T'') : F) (ϖ ^ (i : ℕ)).2
    set D : F := ∏ i, d i with hDdef
    have hDT : D ∈ T' := Subring.prod_mem _ (fun i _ => hdT i)
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
    let f : Fin e → F := fun i => D * ((ϖ ^ (i : ℕ) : T'') : F)
    have hfspan : ∀ i, f i ∈ Submodule.span T' (s : Set F) := by
      intro i
      have hmem : (∏ j ∈ Finset.univ.erase i, d j) ∈ T' :=
        Subring.prod_mem _ (fun j _ => hdT j)
      have := Submodule.smul_mem (Submodule.span T' (s : Set F))
        (⟨∏ j ∈ Finset.univ.erase i, d j, hmem⟩ : T') (hdspan i)
      rw [Subring.smul_def] at this
      have heq : f i = (∏ j ∈ Finset.univ.erase i, d j) * (d i * ((ϖ ^ (i : ℕ) : T'') : F)) := by
        simp only [f, hDdef]
        rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
        ring
      rw [heq]
      exact this
    have hli : LinearIndependent T' f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      obtain ⟨v, hv⟩ := he.symm
      let c : Fin e → T'' := fun i =>
        Subring.inclusion h (g i * ⟨D, hDT⟩) * ϖ ^ (i : ℕ)
      have hcsum : ∑ i, c i = 0 := by
        apply Subtype.ext
        have hcs : ((∑ i, c i : T'') : F) = ∑ i, g i • f i := by
          simp [c, f, Subring.smul_def, mul_assoc]
        rw [hcs, hg]
        rfl
      have hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : T''), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n) := by
        intro i hci
        have ha : g i * ⟨D, hDT⟩ ≠ 0 := by
          intro h0; apply hci; simp only [c, h0, map_zero, zero_mul]
        obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
        refine ⟨m, Subring.inclusion h (u : T') * (v : T'') ^ m,
          (u.isUnit.map (Subring.inclusion h)).mul (v.isUnit.pow m), ?_⟩
        simp only [c]
        rw [hu, map_mul, map_pow, ← hv]
        ring
      have hc0 := eq_zero_of_sum_eq_zero_of_unit_mul_pow hϖ c hc hcsum
      intro i
      have := hc0 i
      simp only [c, mul_eq_zero, pow_eq_zero_iff', hϖ.ne_zero, false_and, or_false] at this
      have h3 : g i * ⟨D, hDT⟩ = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val this
        simpa using this
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h4
      · exact absurd (congrArg Subtype.val h4) hD0
    let f' : Fin e → Submodule.span T' (s : Set F) := fun i => ⟨f i, hfspan i⟩
    have hli' : LinearIndependent T' f' :=
      LinearIndependent.of_comp (Submodule.span T' (s : Set F)).subtype hli
    have hcard := hli'.cardinal_le_rank.trans (rank_span_finset_le s)
    simpa using hcard

end GlobalTheory
end

section

namespace GlobalTheory

def UnramSub {V F : Type} [CommRing V] [Field F] (i : V →+* F) (T : Subring F) : Prop :=
  ∃ (_ : IsDiscreteValuationRing T) (f : V →+* T), (∀ v, (f v : F) = i v) ∧ ∀ π : V, Irreducible π → Irreducible (f π)

namespace UnramSub

variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}

theorem mem {T : Subring F} (h : UnramSub i T) (v : V) : i v ∈ T := by
  obtain ⟨_, f, hf, -⟩ := h
  exact hf v ▸ (f v).2

theorem isDVR {T : Subring F} (h : UnramSub i T) : IsDiscreteValuationRing T := h.1

theorem trans {T₁ T₂ : Subring F} (h₁ : UnramSub i T₁) (h₂ : UnramSub T₁.subtype T₂) : UnramSub i T₂ := by
  obtain ⟨_, f₁, hf₁, hi₁⟩ := h₁
  obtain ⟨_, f₂, hf₂, hi₂⟩ := h₂
  refine ⟨‹_›, f₂.comp f₁, fun v => ?_, fun π hπ => hi₂ _ (hi₁ π hπ)⟩
  rw [RingHom.comp_apply, hf₂, Subring.coe_subtype, hf₁]

theorem le {T₁ T₂ : Subring F} (h₂ : UnramSub T₁.subtype T₂) : T₁ ≤ T₂ := fun z hz => h₂.mem ⟨z, hz⟩

theorem range [IsDomain V] [IsDiscreteValuationRing V] (hi : Function.Injective i) : UnramSub i i.range := by
  let e : V ≃+* i.range := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hi)
  exact ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, e.toRingHom, fun v => rfl,
    fun π hπ => hπ.map e⟩

end UnramSub

end GlobalTheory
end

section

set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.WeilIntegral


set_option autoImplicit false in
open scoped TensorProduct in
theorem _root_.GlobalTheory.WeilIntegral.isAlgebraic_of_etale (S B : Type) [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.Etale S B] (f : B) : IsAlgebraic S f := by
  classical
  let K := FractionRing S
  haveI : Algebra.Etale K (TensorProduct S K B) := Algebra.Etale.baseChange S B K
  haveI : Module.Finite K (TensorProduct S K B) :=
    Algebra.FormallyUnramified.finite_of_free K (TensorProduct S K B)
  haveI hal : Algebra.IsAlgebraic K (TensorProduct S K B) := Algebra.IsAlgebraic.of_finite K _
  obtain ⟨p, hp0, hp⟩ := hal.isAlgebraic ((1 : K) ⊗ₜ[S] f)
  set q := IsLocalization.integerNormalization (nonZeroDivisors S) p
  have hq0 : q ≠ 0 := fun h0 =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h0)
  have hq : Polynomial.aeval ((1 : K) ⊗ₜ[S] f) q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ p hp
  have hmap : (1 : K) ⊗ₜ[S] Polynomial.aeval f q = 0 := by
    rw [← hq, ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply]
    rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).2 (TensorProduct.isBaseChange S B K)
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) (TensorProduct.mk S K B 1)).1 hmap
  refine ⟨Polynomial.C (s : S) * q, ?_, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.2 (nonZeroDivisors.coe_ne_zero s)) hq0
  · rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def]
    exact hs

end GlobalTheory.WeilIntegral
end

section

namespace GlobalTheory.EtaleProd

abbrev fam (A₁ A₂ : Type) : Fin 2 → Type := ![A₁, A₂]

instance instCommRing (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] : ∀ i, CommRing (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (CommRing A₁)) (Fin.cases (inferInstanceAs (CommRing A₂)) finZeroElim)

instance instAlgebra (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] :
    ∀ i, Algebra B (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (Algebra B A₁)) (Fin.cases (inferInstanceAs (Algebra B A₂)) finZeroElim)

theorem etale_fam (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂]
    (h₁ : Algebra.Etale B A₁) (h₂ : Algebra.Etale B A₂) : ∀ i, Algebra.Etale B (fam A₁ A₂ i) :=
  Fin.cases h₁ (Fin.cases h₂ finZeroElim)

end GlobalTheory.EtaleProd


open GlobalTheory.EtaleProd in
theorem GlobalTheory.etale_prod : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  intro B A₁ A₂ _ _ _ _ _ h₁ h₂
  haveI := etale_fam B A₁ A₂ h₁ h₂
  exact Algebra.Etale.of_equiv
    (AlgEquiv.ofRingEquiv (R := B) (f := RingEquiv.piFinTwo (fam A₁ A₂)) fun _ => rfl)
end

section

namespace GlobalTheory.EtC

def IsExcisionNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  Algebra.Etale A A' ∧ (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
    ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}

theorem isExcisionNbhd_self (A : Type) [CommRing A] (f : A) : IsExcisionNbhd A A f :=
  ⟨inferInstance, fun a' => ⟨a', by simp⟩, fun a h => by simpa using h⟩

end GlobalTheory.EtC
end

section

namespace GlobalTheory

theorem etale_prime_le_map_of_unique (B A : Type) [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.Etale B A] (P : Ideal B) (hP : P.IsMaximal) (Q : Ideal A)
    (hQ : ∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) :
    Q ≤ P.map (algebraMap B A) := by
  set I := P.map (algebraMap B A) with hI
  by_cases htop : I = ⊤
  · rw [htop]; exact le_top

  have hrad : I.radical = Q := by
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    have hMQ : M = Q := hQ M hM.isPrime hIM
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hMQ ▸ hIM, hMQ ▸ hM.isPrime⟩
    · refine le_sInf ?_
      rintro J ⟨hJ1, hJ2⟩
      exact (hQ J hJ2 hJ1).ge

  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FormallyUnramified B (A ⧸ I) :=
    Algebra.FormallyUnramified.comp B A (A ⧸ I)
  haveI : Algebra.FormallyUnramified (B ⧸ P) (A ⧸ I) :=
    Algebra.FormallyUnramified.of_restrictScalars B (B ⧸ P) (A ⧸ I)
  haveI : Algebra.EssFiniteType B (A ⧸ I) := Algebra.EssFiniteType.comp B A (A ⧸ I)
  haveI : Algebra.EssFiniteType (B ⧸ P) (A ⧸ I) := Algebra.EssFiniteType.of_comp B (B ⧸ P) (A ⧸ I)
  haveI : IsReduced (A ⧸ I) := Algebra.FormallyUnramified.isReduced_of_field (B ⧸ P) (A ⧸ I)
  intro x hx
  rw [← hrad] at hx
  obtain ⟨n, hn⟩ := hx
  have h0 : (Ideal.Quotient.mk I x) ^ n = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn
  have : Ideal.Quotient.mk I x = 0 := IsReduced.eq_zero _ ⟨n, h0⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory
end
