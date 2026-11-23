module

public import Formalism.DistinguishedUnitIdeals.Bundle003
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ArcLiftOfLocalizationData
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.DescentEstimateDownUp
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bundle003
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfDownDown
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bundle002
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LinExtEqZeroOfMemExt
public import Formalism.DistinguishedUnitIdeals.Bundle004
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GoodOf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.ExponentWindows.E.Full

open PowerSeries

theorem constLift_of_word {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {ℓ ell r₁ r₂ a₀ rr : ℕ} {p : ℕ → PowerSeries O} {H b : ℕ → ℕ}
    {kind : ℕ → Kind} {U₁ : ℕ → Submodule O (Fin r₁ → O)} {U₂ : ℕ → Submodule O (Fin r₂ → O)}
    {prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)}
    (hS : LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂) (hL : LLift ℓ rr prL) (hr : rr ≤ 2 * a₀)
    (hW : ArcWord ϖ ℓ ell a₀ p b kind U₁ U₂ prL) :
    ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL := by
  obtain ⟨cN, cD, cDU, cDD, cUD⟩ := CL.lifts_mod_const_of_words
  rcases hW with hW | hW | hW | hW | hW
  · exact cN levels_mod_const_iff_of_no_down O ϖ hϖ ℓ ell r₁ r₂ a₀ p H b kind U₁ U₂ prL hS hW
  · obtain ⟨s₁, h1, h2, h3⟩ := hW
    exact cD descent_estimate_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₁ h1 h2 h3
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, h5⟩ := hW
    exact cDU descent_estimate_down_up O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 h5
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, ρ, fρ, h5, h6, h7, h8⟩ := hW
    exact cDD levels_mod_const_iff_of_down_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 ρ fρ h5 h6 h7 h8
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, hC, c, α, β, h5, h6⟩ := hW
    exact cUD descent_estimate_up_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 hC c α β h5 h6

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem pow_mem_pair {ϖ : O} {p₁ p₀ : PowerSeries O} (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) :
    ∃ N : ℕ, C (ϖ ^ N) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} := by
  unfold CoprimeRat at h
  obtain ⟨N, a, a', hN⟩ := h
  refine ⟨N * (b₁ + b₀), ?_⟩
  have hmem : C (ϖ ^ N) ∈ Ideal.span {p₁} ⊔ Ideal.span {p₀} := by
    rw [← hN]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  have h2 : C (ϖ ^ N) ^ (b₁ + b₀) ∈ (Ideal.span {p₁} ⊔ Ideal.span {p₀}) ^ (b₁ + b₀) :=
    Ideal.pow_mem_pow hmem _
  have h3 := Ideal.sup_pow_add_le_pow_sup_pow h2
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h3
  rw [pow_mul, map_pow, Ideal.span_insert]
  exact h3

theorem consts_DD {ϖ : O} {p₁ p₀ : PowerSeries O} (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) :
    ∃ (ρ : ℕ) (fρ : PowerSeries O),
      C (ϖ ^ ρ) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} ∧
      (∀ k : ℕ, C (ϖ ^ k) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} → ρ ≤ k) ∧
      fρ ∈ Ideal.span {p₁ ^ b₁} ∧ fρ - C (ϖ ^ ρ) ∈ Ideal.span {p₀ ^ b₀} := by
  classical
  have hex := pow_mem_pair h b₁ b₀
  have hρ : C (ϖ ^ Nat.find hex) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} := Nat.find_spec hex
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hρ
  refine ⟨Nat.find hex, x * p₁ ^ b₁, hρ, fun k hk => Nat.find_min' hex hk,
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  rw [← hxy]
  have e : x * p₁ ^ b₁ - (x * p₁ ^ b₁ + y * p₀ ^ b₀) = (-y) * p₀ ^ b₀ := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem consts_UD {ϖ : O} (hϖ : Irreducible ϖ) {d : ℕ} (hd : 1 ≤ d) {p₁ p₀ : PowerSeries O}
    (hp₀ : UnitDist ϖ d p₀) (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) (hb : 1 ≤ b₀) :
    ∃ (c : ℕ) (α β : PowerSeries O),
      p₁ ^ b₁ = C (ϖ ^ c) * α + p₀ ^ b₀ * β ∧
      p₁ ^ b₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p₀ ^ b₀} := by
  classical
  obtain ⟨N, hN⟩ := pow_mem_pair h b₁ b₀
  have hex : ∃ c : ℕ, p₁ ^ b₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p₀ ^ b₀} := by
    refine ⟨N, fun hmem => ?_⟩
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hmem
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hN
    have h1 : C (ϖ ^ N) * (1 - C ϖ * (x * u)) ∈ Ideal.span {p₀ ^ b₀} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨x * v + y, ?_⟩
      have e : C (ϖ ^ (N + 1)) = C (ϖ ^ N) * C ϖ := by rw [pow_succ, map_mul]
      rw [e] at huv
      calc C (ϖ ^ N) * (1 - C ϖ * (x * u))
          = C (ϖ ^ N) - x * (u * (C (ϖ ^ N) * C ϖ)) := by ring
        _ = (x * p₁ ^ b₁ + y * p₀ ^ b₀) - x * (u * (C (ϖ ^ N) * C ϖ)) := by rw [hxy]
        _ = (x * (u * (C (ϖ ^ N) * C ϖ) + v * p₀ ^ b₀) + y * p₀ ^ b₀)
              - x * (u * (C (ϖ ^ N) * C ϖ)) := by rw [huv]
        _ = p₀ ^ b₀ * (x * v + y) := by ring
    have h2 := mem_span_pow_of_uniformizer_mul O ϖ hϖ d p₀ hp₀ b₀ N _ h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h2
    have h3 := congrArg (coeff 0) hw
    have h0 := constantCoeff_mem_of_unitDist ϖ d p₀ hp₀ hd
    obtain ⟨e0, he0⟩ := Ideal.mem_span_singleton.1 h0
    obtain ⟨b', rfl⟩ : ∃ b', b₀ = b' + 1 := ⟨b₀ - 1, by omega⟩
    simp only [coeff_zero_eq_constantCoeff, map_sub, map_one, map_mul, map_pow,
      constantCoeff_C] at h3 he0
    have : ϖ ∣ 1 := by
      refine ⟨constantCoeff x * constantCoeff u +
        e0 * (constantCoeff p₀) ^ b' * constantCoeff w, ?_⟩
      have h4 : (1 : O) = ϖ * (constantCoeff x * constantCoeff u) +
          (constantCoeff p₀) ^ (b' + 1) * constantCoeff w := by rw [← h3]; ring
      have h5 : (constantCoeff p₀) ^ (b' + 1) = (constantCoeff p₀) ^ b' * (ϖ * e0) := by
        rw [← he0, pow_succ]
      rw [h5] at h4
      rw [h4]
      ring
    exact hϖ.not_isUnit (isUnit_of_dvd_one this)
  have hs := Nat.find_spec hex
  have hmem : p₁ ^ b₁ ∈ Ideal.span {C (ϖ ^ (Nat.find hex)), p₀ ^ b₀} := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0, pow_zero, map_one]
      have : Ideal.span {(1 : PowerSeries O), p₀ ^ b₀} = ⊤ :=
        Ideal.eq_top_of_unit_mem _ 1 1 (Ideal.subset_span (by simp)) (one_mul 1)
      rw [this]; trivial
    · obtain ⟨c', hc'⟩ : ∃ c', Nat.find hex = c' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (m := c') (by omega)
      rw [hc']
      exact not_not.1 this
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hmem
  exact ⟨Nat.find hex, u, v, huv.symm.trans (by ring), hs⟩

end

end Formalism.ExponentWindows.E.Full

namespace Formalism.ExponentWindows.E

open PowerSeries

theorem word_constants_holds : WordConsts := by
  unfold WordConsts
  intro O _ _ _ ϖ hϖ ℓ ell p b hℓ hP s₀ s₁ h01 h1e
  unfold DistinguishedFamily at hP
  have hs₀ : s₀ < ell := lt_trans h01 h1e
  have hc : CoprimeRat ϖ (p s₁) (p s₀) := hP.2 s₁ h1e s₀ hs₀ (ne_of_gt h01)
  refine ⟨Full.consts_DD hc _ _, fun hb => Full.consts_UD hϖ ?_ (hP.1 s₀ hs₀) hc _ _ hb⟩
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))

theorem theorem_E_full_form : ThmEFull := by
  intro O _ _ _ ϖ hϖ B n _ Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂
    hM hB hL₁ hL₂ h1 h2 h3 h4 h5 h6 hr hA
  refine theorem_E_assembled O B n Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hM hB
    hL₁ hL₂ h1 h2 h3 h4 h5 h6 ?_
  intro c hc
  obtain ⟨r₁, r₂, S₁, S₂, m, H, b, kind, U₁, U₂, PP, PP', a1, a2, a3, a4, a5, a6, a7, a8, a9,
    a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27⟩ :=
    hA c hc
  exact arc_lift_of_localization_data O B n Cu abelian₂ g sig rr a₀ kap V₁ V₂ L₁ L₂ h c r₁ r₂ S₁ S₂ m ϖ H b kind U₁ U₂
    PP PP' a1 hB.1 (hL₂.1 c) a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
    a21 a22 a23 (Full.constLift_of_word hϖ a25 a26 hr a27) a24

end Formalism.ExponentWindows.E
end

section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace PolynomialValuationLemmas

theorem factV {O : Type} [CommRing O] [IsLocalRing O] {ℓ : ℕ} {u x : Oˣ} (hp : ℓ.Prime)
    (h3 : 3 ≤ ℓ) (hl : ¬ IsUnit (ℓ : O)) (hu : (u : O) = 1 + (ℓ : O) * (x : O)) :
    FactVval u ℓ := by
  have key : ∀ r : ℕ, 1 ≤ r →
      ∃ ε : Oˣ, (u : O) ^ r - 1 = (ε : O) * (ℓ : O) ^ (1 + padicValNat ℓ r) := by
    intro r hr
    rw [hu]
    exact GoodPlacesAlt.one_add_pow_sub_one_valuation hp h3 hl x.isUnit r hr
  intro m hm
  obtain ⟨r, rfl | rfl⟩ := m.eq_nat_or_neg
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd rfl hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨-ε, ?_⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val, padicValInt.of_nat, Units.val_neg]
    rw [← Nat.padicValNat_def]
    linear_combination -hε
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd (by simp) hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨(u ^ r)⁻¹ * ε, ?_⟩
    have hv : padicValInt ℓ (-(r : ℤ)) = padicValNat ℓ r := by
      simp [padicValInt, Nat.padicValNat_def]
    have hinv : (((u ^ r)⁻¹ : Oˣ) : O) * (u : O) ^ r = 1 := by
      rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
    rw [zpow_neg, zpow_natCast, hv, Units.val_mul]
    linear_combination (((u ^ r)⁻¹ : Oˣ) : O) * hε - hinv

theorem val_mul_pow (ℓ E : ℕ) [Fact ℓ.Prime] {i : ℤ} (hi : i ≠ 0) :
    padicValInt ℓ (i * ((ℓ ^ E : ℕ) : ℤ)) = E + padicValInt ℓ i := by
  have h2 : ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  rw [padicValInt.mul hi h2, padicValInt.of_nat, padicValNat.prime_pow, add_comm]

theorem ppevalVal {O : Type} [CommRing O] (u : Oˣ) (ℓ E : ℕ) (JS : Finset ℤ) (hp : ℓ.Prime)
    (hV : FactVval u ℓ) :
    ∃ ε : Oˣ, (G.PPoly u ℓ E JS).eval 1 = (ε : O) * (ℓ : O) ^ kapExp ℓ E JS := by
  haveI := Fact.mk hp
  have hf : ∀ i ∈ JS.erase 0, ∃ ε : Oˣ, (1 : O) - ((u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : Oˣ) : O) =
      (ε : O) * (ℓ : O) ^ (1 + E + padicValInt ℓ i) := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hm : i * ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := mul_ne_zero hi0 (by exact_mod_cast pow_ne_zero _ hp.ne_zero)
    obtain ⟨ε, hε⟩ := hV _ hm
    refine ⟨ε, ?_⟩
    rw [hε, val_mul_pow ℓ E hi0, add_assoc]
  choose! ε hε using hf
  refine ⟨∏ i ∈ JS.erase 0, ε i, ?_⟩
  unfold kapExp
  rw [G.PPoly, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Units.coe_prod]
  push_cast
  rw [pow_add]
  ring

theorem ppval_of_le {O : Type} [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ)
    (hp : ℓ.Prime) (hV : FactVval u ℓ) (hk : kapExp ℓ E JS + kapExp ℓ E JS' ≤ 2 * kap) :
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS') := by
  obtain ⟨ε, h1⟩ := ppevalVal u ℓ E JS hp hV
  obtain ⟨ε', h2⟩ := ppevalVal u ℓ E JS' hp hV
  exact ⟨kapExp ℓ E JS + kapExp ℓ E JS', ε * ε', hk, by rw [h1, h2, Units.val_mul, pow_add]; ring⟩

section free
variable {O : Type} [CommRing O]

variable {B : Base O} {n : ℕ} {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀]

end free

end PolynomialValuationLemmas

open PolynomialValuationLemmas

theorem factorial_valuation_holds : FactVvalOf := by
  intro O _ _ ℓ u x hp h3 hl hu
  exact factV hp h3 hl hu

theorem factorial_bound_holds : FactVOf := by
  intro O LL Ks Δ _ _ _ _ _ Lev u ℓ hu hl hV m hm h1
  obtain ⟨ε, hε⟩ := hV m hm
  have hU : Lev.u = Units.map (algebraMap O LL : O →* LL) u := Units.ext hu
  have h2 : algebraMap O LL ((u ^ m : Oˣ) : O) = 1 := by
    have : ((Lev.u ^ m : LLˣ) : LL) = algebraMap O LL ((u ^ m : Oˣ) : O) := by
      rw [hU, ← map_zpow]
      rfl
    rw [← this, h1, Units.val_one]
  have h3 := congrArg (algebraMap O LL) hε
  rw [RingHom.map_sub, map_one, h2, sub_self, map_mul, map_pow, map_natCast] at h3
  exact mul_ne_zero ((ε.isUnit.map (algebraMap O LL)).ne_zero) (pow_ne_zero _ hl) h3.symm

theorem polynomial_valuation_holds : PPvalOf := by
  intro O _ u ℓ E kap JS JS' hp hV h
  exact ppval_of_le u ℓ E kap JS JS' hp hV (by unfold kapExp; omega)

end Formalism.ExponentWindows.E
end
