module

public import Formalism.MirabolicMackeyTheory.Bundle001
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Mirabolic
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem isMackey_pi_upper_unipotent_prod_character (K : Type) [Field K] [NumberField K]
    (ι : Type) [Fintype ι] [DecidableEq ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, Finite (k v)] (n : ℕ)
    (χ : ∀ v, AddChar (k v) (𝓞 K)) (hχ : ∀ v, χ v ≠ 1)
    (P : ∀ v, Subgroup (GL (Fin (n + 1)) (k v))) (U : ∀ v, Subgroup (P v))
    (hP : ∀ v, ∀ h : GL (Fin (n + 1)) (k v), h ∈ P v ↔ IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))
    (hU : ∀ v, ∀ h : P v, h ∈ U v ↔
      IsUniU ((h : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v))) :
    IsMackey (Subgroup.pi Set.univ U) (fun h : (∀ v, P v) =>
      ∏ v, χ v (supd (((h v : P v) : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))) := mackey_product ι (𝓞 K) (fun v => ↥(P v)) U
    (fun v (h : P v) => χ v (supd (((h : GL (Fin (n + 1)) (k v)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (k v)))))
    (fun v => mirabolic_is_mackey (k v) (𝓞 K) n (χ v) (hχ v) (P v) (U v) (hP v) (hU v))

end Formalism.EigenvalueLevelCeiling
end

section

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem mem_sc {K : Type} [Field K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ sc a A ↔ ∃ y ∈ A, a • y = x := by
  unfold sc
  rw [Submodule.mem_map]
  rfl

theorem idxPsiGood_of (hMono : IdxMono) (hSc : IdxScaleIn) (hCut : IdxCutLe) (hInt : LatInter) :
    IdxPsiGood := by
  unfold IdxPsiGood
  intro K _ _ _ Z _ _ _ _ _ w Zψ V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0Z σ hσ hThσ u hu
    hucut a E r ha hE hr δ hδ hδi
  have hcc : ∀ (W W' : Submodule K Z) (A : Submodule (𝓞 K) Z), W' ≤ W →
      cut W' (cut W A) = cut W' A := by
    intro W W' A hWW
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, hWW h3⟩, h3⟩
  set L : Submodule K Z := Zψ ⊓ V₀ with hL
  have hLZ : L ≤ Zψ := inf_le_left
  set N : Submodule (𝓞 K) Z := M ⊓ sc a⁻¹ Th with hN
  have hNl : IsLatIn ⊤ N := hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)
  have hNM : N ≤ M := inf_le_left
  have hX : IsLatIn L (cut L M) := (hCut K Z w ⊤ L M M hM hM le_rfl le_top).1
  have hB0 : IsLatIn L (cut L N) := (hCut K Z w ⊤ L N N hNl hNl le_rfl le_top).1
  have hMψ : IsLatIn Zψ (cut Zψ M) := (hCut K Z w ⊤ Zψ M M hM hM le_rfl le_top).1
  have hNψ : IsLatIn Zψ (cut Zψ N) := (hCut K Z w ⊤ Zψ N N hNl hNl le_rfl le_top).1
  have hThKψ : IsLatIn Zψ (cut Zψ ThK) := (hCut K Z w ⊤ Zψ ThK ThK hThK hThK le_rfl le_top).1
  have hu' : (u : K) ≠ 0 := by exact_mod_cast hu
  have hc : a * σ⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hσ)

  have hTh0 : IsLatIn Zψ Th0 := by
    show Th0.FG ∧ Submodule.span K (Th0 : Set Z) = Zψ
    refine ⟨hTh0fg, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.mpr (fun x hx => hTh0Z hx)
    · have h1 := (hSc K Z w Zψ (cut Zψ ThK) (cut Zψ ThK) hThKψ hThKψ (u : K) hu').1
      have h2 : Submodule.span K ((sc (u : K) (cut Zψ ThK) : Submodule (𝓞 K) Z) : Set Z) = Zψ :=
        h1.2
      rw [← h2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr hucut)
  have hcutTh0 : cut V₀ Th0 = cut L Th0 := by
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hL]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hTh0Z h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  have hT : IsLatIn L (cut V₀ Th0) := by
    rw [hcutTh0]
    exact (hCut K Z w Zψ L Th0 Th0 hTh0 hTh0 le_rfl hLZ).1
  refine ⟨hT, ?_⟩
  have hB1 := hSc K Z w L (cut L M) (cut L N) hX hB0 (a * σ⁻¹) hc
  have hB2 := hSc K Z w L (cut L M) (sc (a * σ⁻¹) (cut L N)) hX hB1.1 (u : K) hu'

  have hle2 : sc (u : K) (sc (a * σ⁻¹) (cut L N)) ≤ cut V₀ Th0 := by
    intro x hx
    rw [mem_sc] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_sc] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hN, hL] at hz ⊢
    obtain ⟨⟨_, hz2⟩, hzψ, hzV⟩ := hz
    rw [mem_sc] at hz2
    obtain ⟨t, ht, rfl⟩ := hz2
    obtain ⟨k, hk, rfl⟩ := (mem_sc σ ThK t).1 (hThσ ht)
    have hkey : (a * σ⁻¹) • a⁻¹ • σ • k = k := by
      rw [smul_smul, smul_smul]
      have h1 : a * σ⁻¹ * a⁻¹ * σ = 1 := by field_simp
      rw [h1, one_smul]
    have hkψ : k ∈ Zψ := by
      have h1 := Zψ.smul_mem (a * σ⁻¹) hzψ
      rwa [hkey] at h1
    have hkV : k ∈ V₀ := by
      have h1 := V₀.smul_mem (a * σ⁻¹) hzV
      rwa [hkey] at h1
    rw [hkey]
    have hkc : k ∈ cut Zψ ThK := by
      simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact ⟨hk, hkψ⟩
    exact ⟨hucut ((mem_sc _ _ _).2 ⟨k, hkc, rfl⟩), V₀.smul_mem _ hkV⟩
  have hmono := hMono K Z w L (cut L M) (sc (u : K) (sc (a * σ⁻¹) (cut L N))) (cut V₀ Th0)
    hX hB2.1 hT hle2
  have hNMψ : cut Zψ N ≤ cut Zψ M := by
    unfold cut
    exact inf_le_inf_right _ hNM
  have hcut2 := (hCut K Z w Zψ L (cut Zψ M) (cut Zψ N) hMψ hNψ hNMψ hLZ).2.2
  rw [hcc Zψ L M hLZ, hcc Zψ L N hLZ] at hcut2
  have hv : vw w (a * σ⁻¹) = (E : ℤ) - vw w σ := by
    rw [ValuationRepresentative.vw_mul w a σ⁻¹ ha (inv_ne_zero hσ),
      ValuationRepresentative.vw_inv w σ, hE, sub_eq_add_neg]
  rw [hB2.2, hB1.2, hv] at hmono
  have h1 : (δ : ℝ) * (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (lix w M N : ℝ) + (finrank K Z : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hδi
  have hJ : (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (r + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)) / (δ : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hδ)]
    linarith
  have hm : (lix w (cut L M) (cut V₀ Th0) : ℝ) ≤ (lix w (cut L M) (cut L N) : ℝ) +
      (finrank K L : ℝ) * ((E : ℝ) - (vw w σ : ℝ)) + (finrank K L : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hmono
  have hc2 : (lix w (cut L M) (cut L N) : ℝ) ≤ lix w (cut Zψ M) (cut Zψ N) := by
    exact_mod_cast hcut2
  nlinarith

end Formalism.EigenvalueLevelCeiling
end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem plc_prime (w : HeightOneSpectrum (𝓞 K)) : (plc w).Prime := by
  haveI := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  unfold plc
  exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 K ⧸ w.asIdeal) _)

theorem plc_mem (w : HeightOneSpectrum (𝓞 K)) : ((plc w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  unfold plc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

private theorem vw_coe_eq_count_factors_span_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    vw w (x : K) = ((Associates.mk w.asIdeal).count
      (Associates.mk (Ideal.span {x} : Ideal (𝓞 K))).factors : ℤ) := by
  have hspan : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.count_coe K w hspan, FractionalIdeal.coeIdeal_span_singleton]

theorem intValuation_eq_exp' (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.intValuation x = WithZero.exp (-(vw w (x : K))) := by
  rw [vw_coe_eq_count_factors_span_of_ne_zero w x hx, IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hx]

theorem one_le_ramw (w : HeightOneSpectrum (𝓞 K)) : 1 ≤ ramw w := by
  have hm := plc_mem w
  have hne : ((plc w : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (plc_prime w).ne_zero
  have h1 := (w.intValuation_lt_one_iff_mem _).mpr hm
  rw [intValuation_eq_exp' w _ hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold ramw
  push_cast at h1
  omega

theorem plc_conjPl (w : HeightOneSpectrum (𝓞 K)) : plc (conjPl w) = plc w := by
  unfold plc
  let e := Ideal.quotientEquiv w.asIdeal (conjPl w).asIdeal (cO K) rfl
  haveI := ringChar.charP (𝓞 K ⧸ w.asIdeal)
  haveI : CharP (𝓞 K ⧸ (conjPl w).asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) :=
    charP_of_injective_ringHom (f := (e : 𝓞 K ⧸ w.asIdeal →+* 𝓞 K ⧸ (conjPl w).asIdeal))
      e.injective _
  exact ringChar.eq _ _

theorem ramw_conjPl (w : HeightOneSpectrum (𝓞 K)) : ramw (conjPl w) = ramw w := by
  unfold ramw
  rw [plc_conjPl, ← (valuation_basic_properties K w).2.1 ((plc w : ℕ) : K), star_natCast]

theorem sum_lw_vw_natCast_le (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ) := by
  classical
  have hd0 : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hn0 : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn
  have hI0 : (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hn0

  obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (𝓞 K) → ℕ, ∀ w, e w =
      (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {((n : ℕ) : 𝓞 K)})).factors :=
    ⟨_, fun _ => rfl⟩
  have hv : ∀ w, vw w (n : K) = (e w : ℤ) := by
    intro w
    have h := vw_coe_eq_count_factors_span_of_ne_zero w _ hn0
    rw [he w]
    have hc : (((n : ℕ) : 𝓞 K) : K) = (n : K) := by
      first
        | (push_cast; rfl)
        | push_cast
        | simp
    rw [hc] at h
    exact h

  have hdiv : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    intro w
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hn0, he w]
  have hdvd : ∏ w ∈ T, w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      show IsCoprime (a.asIdeal ^ e a) (b.asIdeal ^ e b)
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne a.isMaximal b.isMaximal
        (fun h => hab (HeightOneSpectrum.ext h))
    · intro w _
      exact hdiv w
  have hP0 : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
    intro h
    rw [h, zero_dvd_iff] at hdvd
    exact hI0 hdvd
  have hle : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≤
      Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) := by
    apply Nat.le_of_dvd
    · apply Nat.pos_of_ne_zero
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
      exact hI0
    · exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  have hnormI : Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) =
      n ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)) n,
      Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hNw : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    intro w
    have : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast this
  have hlog : Real.log (Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) : ℝ) =
      ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    rw [map_prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [map_pow, Nat.cast_pow, Real.log_pow]
    · intro w _
      rw [map_pow, Nat.cast_pow]
      exact pow_ne_zero _ (hNw w)
  have hlogle : ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) ≤
      (finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
    rw [← hlog, ← Real.log_pow, ← Nat.cast_pow, ← hnormI]
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hP0
    · exact_mod_cast hle
  have hsum : ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) =
      (∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ)) / (finrank ℚ K : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hv w]
    unfold lw
    push_cast
    ring
  rw [hsum, div_le_iff₀ hd0, mul_comm (Real.log (n : ℝ))]
  exact hlogle

end SlopeTestRemainingChoices

theorem ramified_basic_bound : RamBasic := by
  unfold RamBasic
  intro K _ _ _ w
  refine ⟨plc_prime w, one_le_ramw w, plc_conjPl w, ramw_conjPl w, ?_⟩
  have h1 : (1:ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast one_le_ramw w
  have hp : (0:ℝ) < (plc w : ℝ) := by exact_mod_cast (plc_prime w).pos
  unfold ellw
  rw [div_pow, Real.sq_sqrt (by linarith)]
  have h2 : (ramw w : ℝ) ≠ 0 := by linarith
  have h3 : (plc w : ℝ) ≠ 0 := hp.ne'
  first
    | (field_simp; ring)
    | field_simp

theorem place_sum : PlaceSum := by
  unfold PlaceSum
  intro K _ _ _ S X hX
  rw [← Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem plc hw)]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : p ≠ 0 := by
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hp
    rw [← hw]
    exact (plc_prime w).ne_zero
  have e : ∑ w ∈ S with plc w = p, lw w * ((ramw w : ℝ) * X (plc w)) =
      (∑ w ∈ S with plc w = p, lw w * (vw w (p : K) : ℝ)) * X p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h4 : plc w = p := (Finset.mem_filter.mp hw).2
    unfold ramw
    rw [h4]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (sum_lw_vw_natCast_le _ p hp0) (hX p)

end Formalism.EigenvalueLevelCeiling
end
end
