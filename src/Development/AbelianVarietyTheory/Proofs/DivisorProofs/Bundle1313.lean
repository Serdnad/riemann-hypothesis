module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_kltAt_of_isNkltCentre (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ) (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) (Γ : X → ℚ) (z x : X) (h : IsNkltCentre p n Γ z)
    (hz : z ⤳ x) : ¬ KltAt p n Γ x := by
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  rintro ⟨η', m', g', h₁, h₂, h₃, h₄⟩
  obtain ⟨E, η, m, g, hη, hm, hg, hE, hd⟩ := h
  have h₅ : IsLogEqn p Γ η' z m' g' := fun w hw => h₃ w (hw.trans hz)
  have h₆ := h₄ E (hE.1.of_specializes hz)
  rw [discrep_eq hn h₁ hη h₂ hm h₅ hg hE.1] at h₆
  exact h₆.not_ge hd

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefAsymp

theorem tendsto_log_nat_div : Tendsto (fun m : ℕ => Real.log m / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun m => ?_)
  simp

theorem tendsto_log_sq_div {X : ℕ → ℝ} {D : ℕ} {L : ℝ} (h1 : ∀ m, 1 ≤ X m)
    (hX : Tendsto (fun m : ℕ => X m / (m : ℝ) ^ (D + 1)) atTop (𝓝 L)) :
    Tendsto (fun m : ℕ => Real.log (X m ^ 2) / m) atTop (𝓝 0) := by
  set C : ℝ := max (L + 1) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hev : ∀ᶠ m : ℕ in atTop, X m / (m : ℝ) ^ (D + 1) < C :=
    hX.eventually (gt_mem_nhds (lt_of_lt_of_le (lt_add_one L) (le_max_left _ _)))
  have hup : Tendsto (fun m : ℕ => 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 2 * Real.log C * (m : ℝ)⁻¹) atTop (𝓝 (2 * Real.log C * 0)) :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _
    have h2 := tendsto_log_nat_div.const_mul (2 * ((D : ℝ) + 1))
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun m => ?_)
    simp [div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · refine Eventually.of_forall fun m => ?_
    exact div_nonneg (Real.log_nonneg (by nlinarith [h1 m])) (Nat.cast_nonneg m)
  · filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    have hXle : X m ≤ C * (m : ℝ) ^ (D + 1) := by
      rw [div_lt_iff₀ hP] at hm; exact hm.le
    have hX0 : 0 < X m := lt_of_lt_of_le one_pos (h1 m)
    have hlog : Real.log (X m) ≤ Real.log C + ((D : ℝ) + 1) * Real.log m := by
      have := Real.log_le_log hX0 hXle
      rw [Real.log_mul (by positivity) hP.ne', Real.log_pow] at this
      push_cast at this
      linarith
    rw [Real.log_pow]
    rw [show 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)
        = (2 * (Real.log C + ((D : ℝ) + 1) * Real.log m)) / m by ring]
    apply div_le_div_of_nonneg_right _ hm0.le
    push_cast
    linarith

theorem tendsto_bound_div (D q : ℕ) (hq : 3 ≤ q) {β g : ℕ → ℝ} {a γ : ℝ} (hβ0 : ∀ m, 0 ≤ β m)
    (hg0 : ∀ m, 0 ≤ g m) (hβ : Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a))
    (hg : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ)) :
    Tendsto (fun m : ℕ => bound D q (β m) (g m) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (Real.log q * (a / (((D + 1).factorial : ℝ) * Real.log ((q : ℝ) / 2))))) := by
  set Δ : ℝ := Real.log ((q : ℝ) / 2) with hΔdef
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hΔ : 0 < Δ := Real.log_pos (by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have hFΔ : 0 < F * Δ := mul_pos hF hΔ
  set c1 : ℝ := ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2) with hc1
  have hc1p : 0 ≤ c1 := mul_nonneg (by positivity)
    (add_nonneg hΔ.le (div_nonneg (mul_nonneg (Nat.cast_nonneg D) (Real.log_nonneg one_le_two)) zero_le_two))
  set A : ℕ → ℝ := fun m => (β m + c1 * g m) / (F * Δ) with hA
  set B : ℕ → ℝ := fun m => ((D : ℝ) + 1) * g m / (2 * (F * Δ)) with hB
  have hunf : ∀ m, bound D q (β m) (g m) = Real.log q * (A m + B m * Real.log ((A m + 2 * B m + 1) ^ 2)) :=
    fun m => rfl
  have hinv := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgP : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hg.mul hinv
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hAP : Tendsto (fun m : ℕ => A m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (a / (F * Δ))) := by
    have := (hβ.add (hgP.const_mul c1)).div_const (F * Δ)
    rw [mul_zero, add_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hA]; ring)
  have hBP : Tendsto (fun m : ℕ => B m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hgP.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have hA0 : ∀ m, 0 ≤ A m := fun m => div_nonneg (add_nonneg (hβ0 m) (mul_nonneg hc1p (hg0 m))) hFΔ.le
  have hB0 : ∀ m, 0 ≤ B m := fun m => div_nonneg (mul_nonneg (by positivity) (hg0 m)) (by positivity)
  have hX1 : ∀ m, 1 ≤ A m + 2 * B m + 1 := fun m => by linarith [hA0 m, hB0 m]
  have hXP : Tendsto (fun m : ℕ => (A m + 2 * B m + 1) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (a / (F * Δ) + 2 * 0 + 0 ^ (D + 1))) := by
    have := (hAP.add (hBP.const_mul 2)).add (hinv.pow (D + 1))
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hlog := tendsto_log_sq_div hX1 hXP
  have h2 : Tendsto (fun m : ℕ => B m * Real.log ((A m + 2 * B m + 1) ^ 2) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := ((hg.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))).mul hlog)
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have := (hAP.add h2).const_mul (Real.log q)
  rw [add_zero] at this
  exact this.congr' (Eventually.of_forall fun m => by show _ = bound D q (β m) (g m) / _; rw [hunf]; ring)

theorem eventually_le_of_bound : ∀ (D : ℕ) (u β g : ℕ → ℝ) (a γ : ℝ), (∀ m, 0 ≤ β m) → (∀ m, 0 ≤ g m) →
    Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a) →
    Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ) →
    (∀ m q, 3 ≤ q → u m ≤ bound D q (β m) (g m)) → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop, u m ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro D u β g a γ hβ0 hg0 hβ hg hu ε hε
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have ha : 0 ≤ a := ge_of_tendsto' hβ (fun m => div_nonneg (hβ0 m) (by positivity))
  set K : ℝ := Real.log 2 * a / (F * ε) with hK
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.exp K)
  set q : ℕ := max n 3 with hqdef
  have hq3 : 3 ≤ q := le_max_right _ _
  have hqn : (n : ℝ) ≤ q := by exact_mod_cast le_max_left n 3
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hKΔ : K < Real.log ((q : ℝ) / 2) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hΔ : 0 < Real.log ((q : ℝ) / 2) := Real.log_pos (by linarith)
  have hlogq : Real.log q = Real.log ((q : ℝ) / 2) + Real.log 2 := by
    rw [Real.log_div hq0.ne' two_ne_zero]; ring
  have hL : Real.log q * (a / (F * Real.log ((q : ℝ) / 2))) < a / F + ε := by
    have e : Real.log q * (a / (F * Real.log ((q : ℝ) / 2)))
        = a / F + Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) := by
      rw [hlogq]; field_simp
    rw [e]
    have h1 : Real.log 2 * a < Real.log ((q : ℝ) / 2) * (F * ε) := by
      rw [hK, div_lt_iff₀ (mul_pos hF hε)] at hKΔ; exact hKΔ
    have h2 : Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) < ε := by
      rw [div_lt_iff₀ (mul_pos hF hΔ)]; nlinarith
    linarith
  have ht := tendsto_bound_div D q hq3 hβ0 hg0 hβ hg
  filter_upwards [ht.eventually (gt_mem_nhds hL), eventually_ge_atTop 1] with m hm hm1
  have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm1) _
  rw [div_lt_iff₀ hP] at hm
  exact (hu m q hq3).trans hm.le

end GlobalTheory.HSNefAsymp
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
private lemma exists_coheight_one_generalization_not_unitAt {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} {f : X.functionField} (hf : f ≠ 0)
    (hreg : _root_.GlobalTheory.Cartier.RegAt z f) (hnu : ¬ _root_.GlobalTheory.Cartier.UnitAt z f) :
    ∃ w : X, w ⤳ z ∧ Order.coheight w = 1 ∧ ¬ _root_.GlobalTheory.Cartier.UnitAt w f := by
  obtain ⟨U, hzU, a, rfl⟩ := hreg.exists_fnOf
  obtain ⟨V, hV, hzV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU
  have hV' : IsAffineOpen V := hV
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨z, trivial, hzV⟩
  rw [← _root_.GlobalTheory.Cartier.fnOf_resG hVU hgV a] at hf hnu ⊢
  generalize _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hVU a = b at hf hnu ⊢
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hmem : ∀ q : PrimeSpectrum Γ(X, V), hV'.fromSpec q ∈ V := fun q => by
    have : hV'.fromSpec q ∈ Set.range hV'.fromSpec := Set.mem_range_self q
    rwa [hV'.range_fromSpec] at this
  have key : ∀ q : PrimeSpectrum Γ(X, V),
      _root_.GlobalTheory.Cartier.UnitAt (hV'.fromSpec q) (_root_.GlobalTheory.Cartier.fnOf V hgV b) ↔
        b ∉ q.asIdeal := by
    intro q
    rw [_root_.GlobalTheory.Cartier.unitAt_fnOf_iff (hmem q) hgV b]
    have : hV'.fromSpec q ∈ X.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b := by
      rw [← hV'.fromSpec_preimage_basicOpen]; rfl
    rw [this, PrimeSpectrum.mem_basicOpen]
  set p := hV'.primeIdealOf ⟨z, hzV⟩
  have hpz : hV'.fromSpec p = z := hV'.fromSpec_primeIdealOf ⟨z, hzV⟩
  have hbp : b ∈ p.asIdeal := by
    by_contra h
    exact hnu (hpz ▸ (key p).mpr h)
  obtain ⟨P, hPmin, hPp⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hbp)
  haveI hPprime : P.IsPrime := hPmin.1.1
  set q : PrimeSpectrum Γ(X, V) := ⟨P, hPprime⟩
  have hbP : b ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  refine ⟨hV'.fromSpec q, ?_, ?_, fun h => (key q).mp h hbP⟩
  · rw [← hpz]
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hPp).map hV'.fromSpec.continuous
  · letI := X.presheaf.algebra_section_stalk ⟨hV'.fromSpec q, hmem q⟩
    haveI hloc := hV'.isLocalization_stalk' q (hmem q)
    have hdim : ringKrullDim (X.presheaf.stalk (hV'.fromSpec q)) = (P.height : WithBot ℕ∞) :=
      @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q.asIdeal q.2 _ _ _ hloc
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    haveI : (Ideal.span {b}).IsPrincipal := ⟨⟨b, rfl⟩⟩
    have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin
    have hne : P.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff]
      intro hmin
      have hbot : P ≤ ⊥ := hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
      have hb0 : b = 0 := (Submodule.eq_bot_iff _).mp (le_bot_iff.mp hbot) b hbP
      exact hf (by rw [hb0, map_zero])
    have h1 : P.height = 1 := le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)
    rw [h1] at hdim
    exact_mod_cast hdim


open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
theorem _root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] (D₀ : _root_.GlobalTheory.Cartier.CartierDiv X) (m : ℕ) (z : X),
    D₀.Eff → 0 < m →
      (_root_.GlobalTheory.PairStep.Off (_root_.GlobalTheory.Discrepancy.qWeil D₀ m) z ↔
        z ∉ D₀.supp) := by
  intro X _ _ D m z hD hm
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  obtain ⟨U, hzU, hU⟩ := hg.exists_nhds
  have hgen : ∀ w : X, w ⤳ z → D.IsEqn w g := fun w hwz =>
    hU w (hwz.mem_open U.isOpen hzU)
  unfold _root_.GlobalTheory.PairStep.Off _root_.GlobalTheory.Discrepancy.qWeil
  simp only [div_eq_zero_iff, hm', or_false, Int.cast_eq_zero]
  rw [hg.mem_supp_iff, not_not]
  constructor
  · intro h
    by_contra hnu
    have hreg := (_root_.GlobalTheory.Cartier.CartierDiv.eff_iff.mp hD) z g hg
    obtain ⟨w, hwz, hw1, hwnu⟩ := exists_coheight_one_generalization_not_unitAt (Units.ne_zero g) hreg hnu
    have hmult := h w hwz
    rw [(hgen w hwz).mult_eq] at hmult
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.Discrepancy.regAt_of_specializes hwz hreg
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact Units.ne_zero g (by rw [← ha, map_zero])
    rw [← ha, _root_.GlobalTheory.Cartier.ord_algebraMap hw1 ha0] at hmult
    have hdim : ringKrullDim (X.presheaf.stalk w) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, hw1]; rfl
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := by
      rw [Ring.krullDimLE_iff, hdim]
      exact_mod_cast le_rfl
    have hfin := isFiniteLength_quotient_span_singleton (X.presheaf.stalk w)
      (mem_nonZeroDivisors_of_ne_zero ha0)
    have htop := Module.length_ne_top_iff.mpr hfin
    have hzero : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a}) ≠ 0 := by
      rw [Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
        Ideal.span_singleton_eq_top]
      exact fun hunit => hwnu ⟨a, hunit, ha⟩
    have : (Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a})).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]
      tauto
    exact this (by exact_mod_cast hmult)
  · intro hunit w hwz
    rw [(hgen w hwz).mult_eq]
    obtain ⟨V, hzV, hV⟩ := hunit.exists_nhds
    exact (hV w (hwz.mem_open V.isOpen hzV)).ord_eq_zero

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_apply_of_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    {σ : ι} (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i k
  simp only [shear, Matrix.add_apply, Matrix.of_apply]
  rw [if_neg, add_zero]
  rintro ⟨h1, -⟩
  exact h (congrArg Sigma.fst h1)

theorem shear_self_mul_apply {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    (A : Matrix (Fin (m τ)) (Fin (m τ)) K) (i c : Fin (m τ)) :
    (shear τ a b t τ * A) i c = A i c + if i = a then t * A b c else 0 := by
  have e : ∀ k, shear τ a b t τ i k = (1 : Matrix (Fin (m τ)) (Fin (m τ)) K) i k + if i = a ∧ k = b then t else 0 := by
    intro k
    simp only [shear, Matrix.add_apply, Matrix.of_apply]
    congr 1
    by_cases h1 : i = a <;> by_cases h2 : k = b <;> simp [h1, h2]
  rw [Matrix.mul_apply]
  simp only [e, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h1 : i = a <;> simp [h1]

theorem almostLow_of_shear : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L,
      Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  intro ι m τ a b hab L K _ _ j t ht C hP
  have hmap : ∀ σ i c, (C.map j) σ i c = j (C σ i c) := fun _ _ _ => rfl
  have hL : ∀ σ, shear τ a b t σ * (C.map j) σ = (shear τ a b t * C.map j) σ := fun _ => rfl
  have hz : ∀ σ (i c : Fin (m σ)), i < c → (shear τ a b t σ * (C.map j) σ) i c = 0 := fun σ i c h => by
    rw [hL]; exact (hP σ).2.2.2 i c i.isLt h
  have hd : ∀ σ, (shear τ a b t σ * (C.map j) σ).det ≠ 0 := fun σ => by rw [hL]; exact (hP σ).2.1
  have hdiag : ∀ σ (i : Fin (m σ)), (shear τ a b t σ * (C.map j) σ) i i ≠ 0 := fun σ i => by
    have hbt : (shear τ a b t σ * (C.map j) σ).BlockTriangular OrderDual.toDual := fun p q hpq =>
      hz σ p q (OrderDual.toDual_lt_toDual.1 hpq)
    have := hd σ
    rw [Matrix.det_of_lowerTriangular _ hbt] at this
    exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have hba : b ≠ a := ne_of_gt hab'
  refine ⟨fun σ hσ => hd σ ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Mat.det_map, hσ, map_zero, mul_zero]
  · intro h0
    have h1 := hz τ a b hab'
    have h2 := hdiag τ b
    rw [shear_self_mul_apply] at h1 h2
    rw [if_pos rfl, hmap, h0, map_zero, zero_add] at h1
    rw [if_neg hba, add_zero] at h2
    exact h2 ((mul_eq_zero.1 h1).resolve_left ht)
  · intro σ i c hic hn
    refine (map_eq_zero j).1 ?_
    rw [← hmap]
    by_cases hσ : σ = τ
    · subst hσ
      have hn' : ¬ (i = a ∧ c = b) := fun h => hn ⟨by rw [h.1], by rw [h.2]⟩
      have h1 := hz σ i c hic
      rw [shear_self_mul_apply] at h1
      by_cases hi : i = a
      · subst hi
        have hcb : c ≠ b := fun h => hn' ⟨rfl, h⟩
        have hbc : b < c := by
          rw [Fin.lt_def] at hic ⊢
          have : (c : ℕ) ≠ b := fun h => hcb (Fin.ext h)
          omega
        have h2 := hz σ b c hbc
        rw [shear_self_mul_apply, if_neg hba, add_zero] at h2
        rw [if_pos rfl, h2, mul_zero, add_zero] at h1
        exact h1
      · rw [if_neg hi, add_zero] at h1
        exact h1
    · have h1 := hz σ i c hic
      rw [shear_apply_of_ne τ a b t hσ, one_mul] at h1
      exact h1

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_self {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) :
    shear τ a b t τ = Matrix.transvection a b t := by
  ext i j
  simp only [shear, Matrix.transvection, Matrix.add_apply, Matrix.of_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  rw [Matrix.single_apply]
  simp only [@eq_comm _ a i, @eq_comm _ b j]

theorem shear_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) (σ : ι)
    (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i j
  simp [shear, Sigma.mk.inj_iff, h]

theorem shear_props : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), a < b → ∀ (R : Type) [CommRing R] (t : R), (∀ σ, (shear τ a b t σ).det = 1) ∧ shear τ a b t * shear τ a b (-t) = 1 ∧ shear τ a b (0 : R) = 1 ∧ ∀ (S : Type) [CommRing S] (g : R →+* S), (shear τ a b t).map g = shear τ a b (g t) := by
  intro ι m τ a b hab R _ t
  have hne : a ≠ b := hab.ne
  refine ⟨fun σ => ?_, ?_, ?_, fun S _ g => ?_⟩
  · by_cases h : σ = τ
    · subst h; rw [shear_self]; exact Matrix.det_transvection_of_ne a b hne t
    · rw [shear_ne τ a b t σ h, Matrix.det_one]
  · funext σ
    rw [Pi.mul_apply, Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, shear_self, Matrix.transvection_mul_transvection_same (h := hne), add_neg_cancel,
        Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h, shear_ne τ a b _ σ h, mul_one]
  · funext σ
    rw [Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h]
  · funext σ i j
    simp only [Mat.map, shear, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem model_regAt_unitAt_values : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → (∀ (y : Y) (f : X.functionField), RegAt (π y) f → RegAt y (φ f)) ∧ (∀ (y : Y) (f : X.functionField), UnitAt (π y) f → UnitAt y (φ f)) ∧ (∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)), φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a)) ∧ ∀ (σ : k →+* ℂ) (z : CxPts q σ) (f : X.functionField), RegAt (π (under z)) f → ratVal (φ f) z = ratVal f (GlobalTheory.Points.PtsOver.map π hπ _ z) := by
  intro k _ X Y _ _ p q π hπ φ hM
  have h3 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)),
      φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a) := by
    intro U h h' a
    have e1 := algebraMap_germ (X := X) (show π (genericPoint Y) ∈ U from h') a
    have e2 := algebraMap_germ (X := Y) h' (π.app U a)
    rw [← e1, hM.compat, ← e2]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply π U (genericPoint Y) h' a
  refine ⟨?_, ?_, h3, ?_⟩
  · rintro y f ⟨a, rfl⟩
    exact ⟨π.stalkMap y a, (hM.compat y a).symm⟩
  · rintro y f ⟨a, ha, rfl⟩
    exact ⟨π.stalkMap y a, ha.map _, (hM.compat y a).symm⟩
  · intro σ z f hf
    obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
    have hz : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := mem_ptsIn.2 hU
    have hz' : GlobalTheory.Points.PtsOver.map π hπ _ z ∈ ptsIn p σ U := mem_ptsIn.2 (by first | exact hU | simpa [Function.comp_apply] using hU)
    rw [h3 U _ (gen_mem (show under z ∈ π ⁻¹ᵁ U from hU)) a, ratVal_fnOf hz, ratVal_fnOf hz',
      ev_app π hπ]

end GlobalTheory.HSNef
end
end
