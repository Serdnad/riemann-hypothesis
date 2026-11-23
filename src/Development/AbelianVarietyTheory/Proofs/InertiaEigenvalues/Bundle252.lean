module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharValueLength

variable {l : ℕ} [Fact l.Prime] in
private theorem isUnit_of_toZMod_ne_zero' {x : ℤ_[l]} (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hx

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_prime_eq_one_add_pow_succ {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (h2 : l = 2 → 2 ≤ r) (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ l = 1 + (l : ℤ_[l]) ^ (r + 1) * w' := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
  set x := (l : ℤ_[l]) ^ r * w with hx
  have hexp : u ^ l = (∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l])) + x * l + 1 := by
    rw [hu, add_comm, add_pow, show l + 1 = n + 1 + 1 + 1 by omega, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, zero_add]
  have hdvd : (l : ℤ_[l]) ^ (r + 2) ∣ ∑ j ∈ Finset.range (n + 1),
      x ^ (j + 1 + 1) * ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj' : j + 2 ≤ l := by rw [Finset.mem_range] at hj; omega
    have hxp : x ^ (j + 1 + 1) = (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * w ^ (j + 1 + 1) := by
      rw [hx, mul_pow, ← pow_mul]
    rcases Nat.lt_or_ge (j + 2) l with hlt | hge
    · have hc : (l : ℤ_[l]) ∣ ((l.choose (j + 1 + 1) : ℕ) : ℤ_[l]) :=
        Nat.cast_dvd_cast ((Fact.out : l.Prime).dvd_choose_self (by omega) (by omega))
      have h1 : (l : ℤ_[l]) ^ (r + 2) ∣ (l : ℤ_[l]) ^ (r * (j + 1 + 1)) * l := by
        rw [← pow_succ]; exact pow_dvd_pow _ (by nlinarith)
      exact h1.trans (mul_dvd_mul (Dvd.intro _ hxp.symm) hc)
    · have hle : r + 2 ≤ r * (j + 1 + 1) := by
        rcases Nat.lt_or_ge l 3 with h | h
        · have := h2 (by omega); nlinarith
        · nlinarith
      exact ((pow_dvd_pow _ hle).trans (Dvd.intro _ hxp.symm)).mul_right _
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨w + l * c, isUnit_of_toZMod_ne_zero' ?_, ?_⟩
  · simpa [ZMod.natCast_self] using (hw.map PadicInt.toZMod).ne_zero
  · rw [hexp, hc, hx]; ring

variable {l : ℕ} [Fact l.Prime] in
private theorem toZMod_principalUnit_eq_one {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r)
    (hu : u = 1 + (l : ℤ_[l]) ^ r * w) : PadicInt.toZMod u = 1 := by
  rw [hu]
  simp [ZMod.natCast_self, zero_pow (Nat.one_le_iff_ne_zero.1 hr)]

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_of_not_dvd {u w : ℤ_[l]} {r m : ℕ} (hr : 1 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) (hm : ¬ l ∣ m) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ m = 1 + (l : ℤ_[l]) ^ r * w' := by
  refine ⟨w * ∑ i ∈ Finset.range m, u ^ i, hw.mul (isUnit_of_toZMod_ne_zero' ?_), ?_⟩

  · rw [map_sum]
    simp only [map_pow, toZMod_principalUnit_eq_one hr hu, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    exact fun h => hm ((ZMod.natCast_eq_zero_iff m l).1 h)
  · have hg := geom_sum_mul u m
    have hu1 : u - 1 = (l : ℤ_[l]) ^ r * w := by rw [hu]; ring
    rw [hu1] at hg
    linear_combination -hg

variable {l : ℕ} [Fact l.Prime] in
private theorem principalUnit_pow_eq_one_add_pow_add_padicValNat {u w : ℤ_[l]} {r : ℕ} (hr : 1 ≤ r) (h2 : l = 2 → 2 ≤ r)
    (hw : IsUnit w) (hu : u = 1 + (l : ℤ_[l]) ^ r * w) {k : ℕ} (hk : k ≠ 0) :
    ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ k = 1 + (l : ℤ_[l]) ^ (r + padicValNat l k) * w' := by
  have hpow : ∀ a : ℕ, ∃ w' : ℤ_[l], IsUnit w' ∧ u ^ (l ^ a) = 1 + (l : ℤ_[l]) ^ (r + a) * w' := by
    intro a
    induction a with
    | zero => exact ⟨w, hw, by simpa using hu⟩
    | succ a ih =>
      obtain ⟨w', hw', h'⟩ := ih
      obtain ⟨w'', hw'', h''⟩ :=
        principalUnit_pow_prime_eq_one_add_pow_succ (by omega) (fun h => by have := h2 h; omega) hw' h'
      exact ⟨w'', hw'', by rw [pow_succ, pow_mul, h'', ← add_assoc]⟩
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk l (Fact.out : l.Prime).one_lt.ne'
  obtain ⟨w', hw', h'⟩ := hpow a
  obtain ⟨w'', hw'', h''⟩ := principalUnit_pow_of_not_dvd (by omega) hw' h' hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  refine ⟨w'', hw'', ?_⟩
  rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hm0,
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero, pow_mul, h'']

private theorem length_quotient_span_unit_mul_pow_eq {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (w : Oˣ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {(w : O) * ϖ ^ n}) = n := by
  rw [Ideal.span_singleton_mul_left_unit w.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n

theorem _root_.GlobalTheory.CharValueLength.injOn_and_lenUnit : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ _root_.Formalism.BasicNotions.lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  intro l _ O _ _ _ _ _ _ s t u v χ hs hs2 huv hχ
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hD : ∀ k : ℕ, k ≠ 0 → ∃ ε : Oˣ,
      algebraMap ℤ_[l] O u ^ k - 1 = ε * (l : O) ^ (s + padicValNat l k) := by
    intro k hk
    obtain ⟨w', hw', h'⟩ := principalUnit_pow_eq_one_add_pow_add_padicValNat hs hs2 v.isUnit huv hk
    refine ⟨(hw'.map (algebraMap ℤ_[l] O)).unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_pow, h', map_add (f := _), map_one, map_mul, map_pow, map_natCast]
    ring
  have hrel : ∀ c, 1 ≤ c → c ≤ t → (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) = χ 1 := by
    intro c h1 h2
    have h : χ c * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (c - 1) = χ 1 := by
      rw [hχ c h1 h2, mul_assoc, ← zpow_natCast, ← zpow_add, Nat.cast_sub h1, Nat.cast_one,
        neg_add_cancel, zpow_zero, mul_one]
    have h' := congrArg (fun z : Oˣ => (z : O)) h
    simpa using h'
  have hφu : IsUnit (algebraMap ℤ_[l] O u) := u.isUnit.map _
  constructor
  · intro c hc c' hc' heq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hc hc'
    simp only at heq
    have key : ∀ a b : ℕ, 1 ≤ a ∧ a ≤ t → 1 ≤ b ∧ b ≤ t → (χ a : O) = χ b → a ≤ b → a = b := by
      intro c c' hc hc' heq hle
      by_contra hne
      obtain ⟨ε, hε⟩ := hD (c' - c) (by omega)
      have e1 := hrel c hc.1 hc.2
      have e2 := hrel c' hc'.1 hc'.2
      rw [← heq, show c' - 1 = (c - 1) + (c' - c) by omega, pow_add] at e2
      have h0 : (χ c : O) * algebraMap ℤ_[l] O u ^ (c - 1) *
          (algebraMap ℤ_[l] O u ^ (c' - c) - 1) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.1 h0 with h | h
      · exact ((χ c).isUnit.mul (hφu.pow _)).ne_zero h
      · rw [hε] at h
        exact mul_ne_zero ε.ne_zero (pow_ne_zero _ hl0) h
    rcases le_total c c' with hle | hle
    · exact key c c' hc hc' heq hle
    · exact (key c' c hc' hc heq.symm hle).symm
  · have hterm : ∀ c ∈ Finset.Ioc 1 t, ∃ ε : Oˣ,
        (χ 1 : O) - χ c = ε * (l : O) ^ (s + padicValNat l (c - 1)) := by
      intro c hc
      rw [Finset.mem_Ioc] at hc
      obtain ⟨ε, hε⟩ := hD (c - 1) (by omega)
      refine ⟨χ c * ε, ?_⟩
      rw [← hrel c (by omega) hc.2, Units.val_mul, mul_assoc, ← hε]
      ring
    choose! ε hε using hterm
    have hprod : ∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - χ c) =
        ((∏ c ∈ Finset.Ioc 1 t, ε c : Oˣ) : O) *
          (l : O) ^ (∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1))) := by
      rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Units.coe_prod]
    have hsum : ∑ c ∈ Finset.Ioc 1 t, (s + padicValNat l (c - 1)) =
        ∑ k ∈ Finset.Ioo 0 t, (s + padicValNat l k) := by
      refine Finset.sum_nbij' (fun c => c - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;>
        simp only [Finset.mem_Ioc, Finset.mem_Ioo] at ha ⊢ <;> omega
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨e, η, hη⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    have he : e ≠ 0 := by
      rintro rfl
      have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
        Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal O)
      have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
        rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
        exact Ideal.subset_span rfl
      rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
      exact hl (by rw [hη, pow_zero, mul_one]; exact η.isUnit)
    unfold _root_.Formalism.BasicNotions.lenUnit
    rw [hprod, hsum, hη, mul_pow, ← pow_mul, ← mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, length_quotient_span_unit_mul_pow_eq hϖ, length_quotient_span_unit_mul_pow_eq hϖ,
      ENat.toNat_natCast, ENat.toNat_natCast, Nat.cast_mul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 he)]
    push_cast
    rfl

end GlobalTheory.CharValueLength
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.CoeffEmbedding

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem exists_norm_le : ∃ C : ℝ, ∀ b : N.O i, ‖iotaOQ N A i b‖ ≤ C := by

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[N.l i] (N.O i)).FG)
  refine ⟨∑ a ∈ s, ‖iotaOQ N A i a‖, fun b => ?_⟩
  have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
  obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb

  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hz : iotaOQ N A i (algebraMap ℤ_[N.l i] (N.O i) (c a)) =
      algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i]) := A.iotaQ_alg i (c a)
  rw [Algebra.smul_def, map_mul, norm_mul, hz]
  have h1 : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ ≤ 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ = ‖(c a : ℚ_[N.l i])‖ :=
      PadicAlgCl.norm_extends (p := N.l i) _
    rw [he, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  exact mul_le_of_le_one_left (norm_nonneg _) h1


include A in
theorem exists_pow_le_span : ∃ e : ℕ, IsLocalRing.maximalIdeal (N.O i) ^ e ≤
    Ideal.span {((N.l i : ℕ) : N.O i)} := by

  have hl : ((N.l i : ℕ) : N.O i) ≠ 0 := by
    intro h
    have h' := congrArg (iotaOQ N A i) h
    rw [map_natCast, map_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : (N.l i).Prime).ne_zero) h'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {((N.l i : ℕ) : N.O i)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨n, ?_⟩
  rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem continuous_iotaOQ : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  intro R H what₂ N A i

  obtain ⟨C, hC⟩ := exists_norm_le N A i
  obtain ⟨e, he⟩ := exists_pow_le_span N A i
  refine continuous_of_continuousAt_zero (iotaOQ N A i) ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  set q : ℝ := ‖((N.l i : ℕ) : Qbar (N.l i))‖ with hq
  have hq1 : q < 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) ((N.l i : ℕ) : ℚ_[N.l i])‖ =
        ‖((N.l i : ℕ) : ℚ_[N.l i])‖ := PadicAlgCl.norm_extends (p := N.l i) _
    rw [map_natCast] at he
    rw [hq, he]
    exact Padic.norm_p_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hC1) hq1
  obtain ⟨hopen, -⟩ := isAdic_iff.mp (N.O_adic i)
  filter_upwards [(hopen (e * k)).mem_nhds (Ideal.zero_mem _)] with x hx
  have hx' : x ∈ Ideal.span {((N.l i : ℕ) : N.O i) ^ k} := by
    rw [← Ideal.span_singleton_pow, pow_mul] at *
    exact Ideal.pow_right_mono he k hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  rw [Metric.mem_ball, dist_zero_right, map_mul, map_pow, map_natCast, norm_mul, norm_pow, ← hq]
  calc ‖iotaOQ N A i b‖ * q ^ k ≤ (|C| + 1) * q ^ k :=
        mul_le_mul_of_nonneg_right ((hC b).trans (by linarith [le_abs_self C])) (pow_nonneg hq0 k)
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left hk hC1
    _ = ε := by field_simp

end GlobalTheory.CoeffEmbedding
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Proof.ConjugatePlaces

open GlobalTheory.IndefiniteRowSideFullHecke

section Host

variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem exists_conj_int (x : 𝓞 H.E) : ∃ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) :=
  ⟨⟨H.conj (x : H.E), (x.isIntegral_coe).map (H.conj.toAlgHom.restrictScalars ℤ)⟩, rfl⟩

variable {H}

theorem isConjPl_symm {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') : IsConjPl H w' w :=
  fun x y hy => (h y x (by rw [hy, conj_conj])).symm

theorem isConjPl_unique {w w₁ w₂ : HeightOneSpectrum (𝓞 H.E)} (h₁ : IsConjPl H w w₁)
    (h₂ : IsConjPl H w w₂) : w₁ = w₂ := by
  ext y
  obtain ⟨x, hx⟩ := exists_conj_int H y
  have hy : (y : H.E) = H.conj (x : H.E) := by rw [hx, conj_conj]
  exact (h₁ x y hy).symm.trans (h₂ x y hy)

variable (H)

end Host

section Loc

variable (D : D7) (i : D.nd.Loc)

section Pl

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Pl

end Loc

end GlobalTheory.Proof.ConjugatePlaces

end
end

section

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem act_root_eq_pow_of_chi_nat {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (u : ℕ)
    (hg : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    g ζ = ζ ^ u := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ
  rw [hg] at ha
  have h2 : ‖((((u : ℤ) - (a : ℤ) : ℤ)) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    push_cast; exact ha
  have h3 : ((l : ℤ) ^ m) ∣ ((u : ℤ) - (a : ℤ)) := (Padic.norm_int_le_pow_iff_dvd _ _).mp h2
  have h4 : a ≡ u [MOD l ^ m] := by
    rw [Nat.modEq_iff_dvd]
    push_cast
    exact h3
  rw [hga, pow_eq_pow_mod a hζ, pow_eq_pow_mod u hζ, h4]

theorem actT_εroot_eq_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l)
    (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) →
      ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  intro l _ P AI g u hg j
  have hz : ∀ m, P.ζQ m ^ l ^ m = 1 := by
    intro m
    induction m with
    | zero => simpa using P.ζQ_zero
    | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  refine Perfection.ext fun n => ?_
  have hc : PreTilt.coeff n (AI.εroot j) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (n + j)) := by
    rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g _ n _ hc
  have h3 : y' = AI.ζ (n + j) ^ u := by
    apply Subtype.ext
    rw [h1, SubmonoidClass.coe_pow, AI.ζ_eq, AI.actC_ext,
      act_root_eq_pow_of_chi_nat P g u hg (n + j) _ (hz _)]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [h2, map_pow, hc, h3]
  exact map_pow _ _ _

end GlobalTheory.ExpImage
end
end

section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.CompanionTheory.InertiaEigenvalues.LPow


end GlobalTheory.CompanionTheory.InertiaEigenvalues.LPow

end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

private theorem xi_eq_sum_choose_mul_pi_pow_lemma_2 {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l}
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) :
    AI.ξ = ∑ i ∈ Finset.range l, ((l.choose (i + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i := by
  have h := congrArg (Polynomial.eval AI.π₁)
    (Polynomial.geom_sum_X_comp_X_add_one_eq_sum (R := _root_.Formalism.BasicNotions.Loc.Ainf l) l)
  simp only [Polynomial.eval_comp, Polynomial.eval_finsetSum, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_natCast] at h
  rw [← h]
  unfold _root_.Formalism.BasicNotions.LocAinf.ξ _root_.Formalism.BasicNotions.LocAinf.π₁
  simp

private theorem xi_eq_pi_pow_add_prime_mul_lemma {l : ℕ} [hl : Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l}
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) :
    ∃ w, AI.ξ = AI.π₁ ^ (l - 1) + (l : _root_.Formalism.BasicNotions.Loc.Ainf l) * (1 + AI.π₁ * w) := by
  have hp := hl.out
  obtain ⟨m, hm⟩ : ∃ m, l = m + 2 := ⟨l - 2, by have := hp.two_le; omega⟩
  refine ⟨∑ i ∈ Finset.range m, ((l.choose (i + 2) / l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i, ?_⟩
  rw [xi_eq_sum_choose_mul_pi_pow_lemma_2, show Finset.range l = Finset.range (m + 1 + 1) by rw [hm],
    Finset.sum_range_succ, Finset.sum_range_succ',
    show l.choose (m + 1 + 1) = 1 by rw [show m + 1 + 1 = l by omega]; simp]
  have hd : ∀ i ∈ Finset.range m, ((l.choose (i + 1 + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ (i + 1) =
      (l : _root_.Formalism.BasicNotions.Loc.Ainf l) * (AI.π₁ * (((l.choose (i + 2) / l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) * AI.π₁ ^ i)) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hdvd : l ∣ l.choose (i + 2) := hp.dvd_choose_self (by omega) (by omega)
    rw [show ((l.choose (i + 1 + 1) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) =
        ((l * (l.choose (i + 2) / l) : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) by rw [Nat.mul_div_cancel' hdvd]]
    push_cast
    ring
  rw [Finset.sum_congr rfl hd, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [zero_add, Nat.choose_one_right, pow_zero, mul_one, Nat.cast_one, one_mul]
  rw [show m + 1 = l - 1 by omega]
  ring

theorem _root_.GlobalTheory.Adopt.ainf_invPi_mod_xi_pow_bounded_denominator : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l)
    (AI : _root_.Formalism.BasicNotions.LocAinf l P) (k n M : ℕ), 1 ≤ M → k ≤ (l - 1) * n →
    ((l : ℕ) : _root_.Formalism.BasicNotions.Loc.Ainf l) ^ (n + M - 1) ∈ Ideal.span {AI.π₁ ^ k, AI.ξ ^ M} := by
  intro l _ P AI k n M hM hk
  obtain ⟨w, hw⟩ := xi_eq_pi_pow_add_prime_mul_lemma AI
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  set q := Ideal.Quotient.mk (Ideal.span {AI.π₁ ^ k, AI.ξ ^ M})
  have hπ : q AI.π₁ ^ k = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hξ : q AI.ξ ^ M = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have hu : IsUnit (q (1 + AI.π₁ * w)) := by
    rw [map_add (f := _), map_one, map_mul]
    exact IsNilpotent.isUnit_one_add ⟨k, by rw [mul_pow, hπ, zero_mul]⟩
  have hneg : (-(q AI.π₁ ^ (l - 1))) ^ n = 0 := by
    rw [neg_pow, ← pow_mul, pow_eq_zero_of_le hk hπ, mul_zero]
  have hsum := (Commute.all (q AI.ξ) (-(q AI.π₁ ^ (l - 1)))).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
    hξ hneg (k := n + M - 1) (by omega)
  rw [← sub_eq_add_neg, congrArg q hw, map_add (f := _), map_pow, add_sub_cancel_left, map_mul,
    mul_pow] at hsum
  rw [map_pow, map_natCast]
  exact ((hu.pow _).mul_left_eq_zero).1 hsum

end
end
