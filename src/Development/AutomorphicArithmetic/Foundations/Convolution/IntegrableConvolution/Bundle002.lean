module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.L1

section QuotAnyAux

variable {X T : Type} [Group X] [MeasurableSpace X] [MeasurableMul₂ X] [Group T] [MeasurableSpace T]
  [MeasurableInv T]

private theorem lint_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {F : X → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ t x, F (i t * x) = F x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) :
    ∫⁻ x, F x * ρ x ∂μ = ∫⁻ x, F x * ρ' x ∂μ := by
  have hmul : Measurable fun p : T × X => i p.1 * p.2 := (hi.comp measurable_fst).mul measurable_snd
  have e1 : ∫⁻ x, F x * ρ x ∂μ = ∫⁻ t, ∫⁻ x, F x * ρ x * ρ' (i t * x) ∂μ ∂ν := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun x => ?_
      rw [lintegral_const_mul, hρ'1 x, mul_one]
      exact hρ'.comp (hi.mul_const x)
    · exact (((hF.comp measurable_snd).mul (hρ.comp measurable_snd)).mul (hρ'.comp hmul)).aemeasurable
  have e2 : ∀ t : T, ∫⁻ x, F x * ρ x * ρ' (i t * x) ∂μ = ∫⁻ x, F x * ρ' x * ρ (i t⁻¹ * x) ∂μ := by
    intro t
    rw [← lintegral_mul_left_eq_self (fun x => F x * ρ x * ρ' (i t * x)) (i t)⁻¹]
    refine lintegral_congr fun x => ?_
    simp only [mul_inv_cancel_left]
    rw [← map_inv, hFi]
    ring
  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun x => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun t : T => ρ (i t * x)), hρ1 x, mul_one]
    · exact hρ.comp ((hi.comp measurable_inv).mul_const x)

  · have hm : Measurable fun p : X × T => i p.2⁻¹ * p.1 :=
      (hi.comp (measurable_snd.inv)).mul measurable_fst
    exact (((hF.comp measurable_fst).mul (hρ'.comp measurable_fst)).mul (hρ.comp hm)).aemeasurable

end QuotAnyAux

section QuotAnyReal

variable {X : Type} [MeasurableSpace X]

private theorem nn_int {μ : Measure X} {g : X → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x)
    {ρ : X → ℝ≥0∞} (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, g x * (ρ x).toReal ∂μ = (∫⁻ x, ‖g x‖ₑ * ρ x ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => mul_nonneg (h0 x) ENNReal.toReal_nonneg)
    (hg.mul hρ.ennreal_toReal).aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  have hae := ae_lt_top (hg.enorm.mul hρ) hfin.ne
  filter_upwards [hae] with x hx
  rw [ENNReal.ofReal_mul (h0 x), ← Real.enorm_of_nonneg (h0 x)]
  by_cases h : ρ x = ⊤
  · have hz : ‖g x‖ₑ = 0 := by
      by_contra hne
      simp only [Pi.mul_apply] at hx
      rw [h, ENNReal.mul_top hne] at hx
      exact lt_irrefl _ hx
    simp [hz]
  · rw [ENNReal.ofReal_toReal h]

private theorem int_of {μ : Measure X} {g : X → ℝ} (hg : Measurable g) {ρ : X → ℝ≥0∞}
    (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    Integrable (fun x => g x * (ρ x).toReal) μ := by
  refine ⟨(hg.mul hρ.ennreal_toReal).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  rw [enorm_mul, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  gcongr
  exact ENNReal.ofReal_toReal_le

end QuotAnyReal

section QuotAnyMain

variable {X T : Type} [Group X] [MeasurableSpace X] [MeasurableMul₂ X] [Group T] [MeasurableSpace T]
  [MeasurableInv T]

private theorem real_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {g : X → ℝ} (hg : Measurable g)
    (hgi : ∀ t x, g (i t * x) = g x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) (hfin : ∫⁻ x, ‖g x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, g x * (ρ x).toReal ∂μ = ∫ x, g x * (ρ' x).toReal ∂μ := by
  have hpm : Measurable fun x => max (g x) 0 := hg.max measurable_const
  have hnm : Measurable fun x => max (-g x) 0 := hg.neg.max measurable_const
  have hpi : ∀ t x, max (g (i t * x)) 0 = max (g x) 0 := fun t x => by rw [hgi]
  have hni : ∀ t x, max (-g (i t * x)) 0 = max (-g x) 0 := fun t x => by rw [hgi]
  have hple : ∀ x, ‖max (g x) 0‖ₑ ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hnle : ∀ x, ‖max (-g x) 0‖ₑ ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _))
  have hfin' : ∫⁻ x, ‖g x‖ₑ * ρ' x ∂μ < ⊤ := by
    rw [← lint_eq hi hg.enorm (fun t x => by rw [hgi]) hρ hρ1 hρ' hρ'1]
    exact hfin
  have split : ∀ r : X → ℝ≥0∞, Measurable r → ∫⁻ x, ‖g x‖ₑ * r x ∂μ < ⊤ →
      ∫ x, g x * (r x).toReal ∂μ =
        (∫⁻ x, ‖max (g x) 0‖ₑ * r x ∂μ).toReal - (∫⁻ x, ‖max (-g x) 0‖ₑ * r x ∂μ).toReal := by
    intro r hr hf
    have fp : ∫⁻ x, ‖max (g x) 0‖ₑ * r x ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun x => by gcongr; exact hple x) hf
    have fn : ∫⁻ x, ‖max (-g x) 0‖ₑ * r x ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun x => by gcongr; exact hnle x) hf
    rw [← nn_int hpm (fun x => le_max_right _ _) hr fp, ← nn_int hnm (fun x => le_max_right _ _) hr fn,
      ← integral_sub (int_of hpm hr fp) (int_of hnm hr fn)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show g x * (r x).toReal = max (g x) 0 * (r x).toReal - max (-g x) 0 * (r x).toReal
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  rw [split ρ hρ hfin, split ρ' hρ' hfin',
    lint_eq hi hpm.enorm (fun t x => by rw [hpi]) hρ hρ1 hρ' hρ'1,
    lint_eq hi hnm.enorm (fun t x => by rw [hni]) hρ hρ1 hρ' hρ'1]

private theorem cpx_int {μ : Measure X} {Φ : X → ℂ} (hΦ : Measurable Φ) {ρ : X → ℝ≥0∞}
    (hρ : Measurable ρ) (hfin : ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) :
    Integrable (fun x => Φ x * ((ρ x).toReal : ℂ)) μ := by
  have h := int_of (μ := μ) (g := fun x => ‖Φ x‖) hΦ.norm hρ (by simpa [enorm_norm] using hfin)
  refine h.mono (hΦ.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp [abs_of_nonneg ENNReal.toReal_nonneg]

private theorem cpx_eq {μ : Measure X} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν]
    [ν.IsInvInvariant] {i : T →* X} (hi : Measurable i) {Φ : X → ℂ} (hΦ : Measurable Φ)
    (hΦi : ∀ t x, Φ (i t * x) = Φ x) {ρ ρ' : X → ℝ≥0∞} (hρ : Measurable ρ)
    (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1) (hρ' : Measurable ρ')
    (hρ'1 : ∀ x, ∫⁻ t, ρ' (i t * x) ∂ν = 1) (hfin : ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) :
    ∫ x, Φ x * ((ρ x).toReal : ℂ) ∂μ = ∫ x, Φ x * ((ρ' x).toReal : ℂ) ∂μ := by
  have hfin' : ∫⁻ x, ‖Φ x‖ₑ * ρ' x ∂μ < ⊤ := by
    rw [← lint_eq hi hΦ.enorm (fun t x => by rw [hΦi]) hρ hρ1 hρ' hρ'1]
    exact hfin
  have h1 := cpx_int hΦ hρ hfin
  have h2 := cpx_int hΦ hρ' hfin'
  have bre : ∫⁻ x, ‖(Φ x).re‖ₑ * ρ x ∂μ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun x => by
      gcongr
      exact enorm_le_iff_norm_le.2 (Complex.abs_re_le_norm _)) hfin
  have bim : ∫⁻ x, ‖(Φ x).im‖ₑ * ρ x ∂μ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun x => by
      gcongr
      exact enorm_le_iff_norm_le.2 (Complex.abs_im_le_norm _)) hfin
  apply Complex.ext
  · have a := Complex.reCLM.integral_comp_comm h1
    have b := Complex.reCLM.integral_comp_comm h2
    simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at a b
    rw [← a, ← b]
    exact real_eq hi (Complex.measurable_re.comp hΦ) (fun t x => by simp [hΦi]) hρ hρ1 hρ' hρ'1 bre
  · have a := Complex.imCLM.integral_comp_comm h1
    have b := Complex.imCLM.integral_comp_comm h2
    simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at a b
    rw [← a, ← b]
    exact real_eq hi (Complex.measurable_im.comp hΦ) (fun t x => by simp [hΦi]) hρ hρ1 hρ' hρ'1 bim

end QuotAnyMain

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.quotAny :
    UpperTheory.ConvolutionTheory.L1.QuotAny := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi Φ ρ hΦ hinv hρ hfin
  have hex : ∃ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id i ν ρ := ⟨ρ, hρ⟩
  rw [PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_left hex]
  have hc := hex.choose_spec
  exact (UpperTheory.ConvolutionTheory.L1.cpx_eq hi hΦ hinv hρ.1 hρ.2 hc.1 hc.2 hfin).symm
end

section

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

private theorem cont_prodFn {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun y : Fin m → G => (List.ofFn y).prod := by
  simp only [List.ofFn_eq_map]
  exact continuous_list_prod (f := fun i (y : Fin m → G) => y i) _ fun i _ => continuous_apply i

private theorem cont_fib {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) :
    Continuous fun p : G × (Fin m → G) => fib p.2 p.1 := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact ((cont_prodFn m).comp continuous_snd).inv.mul continuous_fst
  · simp only [fib, Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_snd

private theorem prod_fib {G : Type} [Group G] [MeasurableSpace G] {m : ℕ} (y : Fin m → G) (x : G) :
    (List.ofFn (fib y x)).prod = x := by
  rw [List.ofFn_succ']
  simp [fib]

private theorem integrable_fib {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (Φ : (Fin (m + 1) → G) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    ∃ K : Set (Fin m → G), IsCompact K ∧ (∀ x y, y ∉ K → Φ (fib y x) = 0) ∧
      ∀ x, Integrable (fun y : Fin m → G => Φ (fib y x)) (Measure.pi fun _ => μ) := by
  have hK : IsCompact ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) :=
    hs.isCompact.image (continuous_pi fun i => continuous_apply _)
  have h0 : ∀ x y, y ∉ ((fun g : Fin (m + 1) → G => fun i : Fin m => g i.castSucc) '' tsupport Φ) →
      Φ (fib y x) = 0 := by
    intro x y hy
    by_contra h
    exact hy ⟨fib y x, subset_tsupport _ h, funext fun i => by simp [fib]⟩
  refine ⟨_, hK, h0, fun x => ?_⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK (h0 x))
  exact hc.comp ((cont_fib m).comp (Continuous.prodMk_right x))

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.pushTest :
    UpperTheory.ConvolutionTheory.L1.PushTest := by
  intro G _ _ _ _ _ _ _ _ μ _ m Φ hc hs
  obtain ⟨K, hK, h0, hint⟩ := integrable_fib μ m Φ hc hs
  have hsup : ∀ x, push μ m Φ x ≠ 0 → ∃ g, Φ g ≠ 0 ∧ (List.ofFn g).prod = x := by
    intro x hx
    by_contra h
    apply hx
    have : ∀ y : Fin m → G, Φ (fib y x) = 0 := fun y => by
      by_contra h'
      exact h ⟨_, h', prod_fib y x⟩
    simp [push, this]
  refine ⟨?_, ?_, hsup, hint, ?_, ?_⟩
  · have e : push μ m Φ = fun x => ∫ y in K, Φ (fib y x) ∂(Measure.pi fun _ => μ) := by
      funext x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
    rw [e]
    exact continuous_parametric_integral_of_continuous (f := fun x y => Φ (fib y x)) (hc.comp (cont_fib m)) hK
  · refine HasCompactSupport.intro (hs.isCompact.image (cont_prodFn (m + 1))) fun x hx => ?_
    by_contra h
    obtain ⟨g, hg, rfl⟩ := hsup x h
    exact hx ⟨g, subset_tsupport _ hg, rfl⟩
  · intro c
    funext x
    simp [push, integral_const_mul]
  · intro Ψ hc' hs'
    obtain ⟨_, _, _, hint'⟩ := integrable_fib μ m Ψ hc' hs'
    funext x
    simp only [push, Pi.add_apply]
    exact integral_add (hint x) (hint' x)
end

section

open MeasureTheory

private theorem measurePreserving_chainCoords {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] (m : ℕ) :
    ∀ δ : Fin m → G,
    MeasurePreserving (fun x : Fin (m + 1) → G => (x 0, fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) := by
  induction m with
  | zero =>
    intro δ
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin 1 => μ) 0
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    exact i.elim0
  | succ m ih =>
    intro δ
    have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 2) => μ) 0
    have h2 := (MeasurePreserving.id μ).prod (ih (Fin.tail δ))
    have h3 : MeasurePreserving
        (fun p : G × (G × (Fin m → G)) => (id p.1, (p.1⁻¹ * δ 0 * p.2.1, p.2.2)))
        (μ.prod (μ.prod (Measure.pi fun _ => μ))) (μ.prod (μ.prod (Measure.pi fun _ => μ))) := by
      refine MeasurePreserving.skew_product (g := fun (a : G) (q : G × (Fin m → G)) => (a⁻¹ * δ 0 * q.1, q.2))
        (MeasurePreserving.id μ) ?_ (Filter.Eventually.of_forall fun a => ?_)
      · unfold Function.uncurry
        fun_prop
      · exact ((measurePreserving_mul_left μ (a⁻¹ * δ 0)).prod (MeasurePreserving.id _)).map_eq
    have h4 := (MeasurePreserving.id μ).prod
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
    have h := h4.comp (h3.comp (h2.comp h1))
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]

private theorem tele {G : Type} [Group G] (m : ℕ) : ∀ (δ : Fin m → G) (x : Fin (m + 1) → G),
    (List.ofFn fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ).prod =
      (x 0)⁻¹ * (List.ofFn δ).prod * x (Fin.last m) := by
  induction m with
  | zero => intro δ x; simp
  | succ m ih =>
    intro δ x
    have h := ih (fun i => δ i.succ) (fun i => x i.succ)
    simp only [List.ofFn_succ, List.prod_cons, ← Fin.succ_castSucc]
    rw [h]
    simp [mul_assoc]

theorem UpperTheory.ConvolutionTheory.L1.changeVar :
    UpperTheory.ConvolutionTheory.L1.ChangeVar := by
  intro G _ _ _ _ _ _ _ _ μ _ m δ
  refine ⟨measurePreserving_chainCoords μ m (fun i => δ i.castSucc), fun x => ?_⟩
  funext i
  unfold UpperTheory.ConvolutionTheory.L1.fib
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, tele m (fun i => δ i.castSucc) x, List.ofFn_succ' δ]
    simp [mul_assoc]
  · rw [Fin.snoc_castSucc, Fin.coeSucc_eq_succ]
end

section

open Topology

private theorem UpperTheory.ConvolutionTheory.L1.compact_lift {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f) (hs : Function.Surjective f) {D : Set Y}
    (hD : IsCompact D) : ∃ K : Set X, IsCompact K ∧ D ⊆ f '' K := by
  have h : ∀ z : Y, ∃ K : Set X, IsCompact K ∧ f '' K ∈ 𝓝 z := by
    intro z
    obtain ⟨g, rfl⟩ := hs z
    obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
    exact ⟨K, hK, hf.image_mem_nhds hg⟩
  choose K hK hK' using h
  obtain ⟨t, -, ht⟩ := hD.elim_nhds_subcover (fun z => f '' K z) (fun z _ => hK' z)
  refine ⟨⋃ z ∈ t, K z, t.isCompact_biUnion fun z _ => hK z, ?_⟩
  intro y hy
  obtain ⟨z, hz, g, hg, rfl⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact ⟨g, Set.mem_iUnion₂.2 ⟨z, hz, hg⟩, rfl⟩

theorem UpperTheory.ConvolutionTheory.L1.closedProper :
    UpperTheory.ConvolutionTheory.L1.ClosedProper := by
  intro G _ _ _ _ _ _ γ hO D hD
  set O : Set G := {y | ∃ x, y = x⁻¹ * γ * x} with hOdef
  let : MulAction G O :=
    { smul := fun g y => ⟨g * y.1 * g⁻¹, by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x * g⁻¹, by rw [hx]; group⟩⟩
      one_smul := fun y => Subtype.ext (by change 1 * y.1 * 1⁻¹ = y.1; group)
      mul_smul := fun a b y => Subtype.ext (by
        change a * b * y.1 * (a * b)⁻¹ = a * (b * y.1 * b⁻¹) * a⁻¹; group) }
  have hsm : ∀ (g : G) (y : O), ((g • y : O) : G) = g * y.1 * g⁻¹ := fun _ _ => rfl
  have : ContinuousSMul G O := ⟨by
    refine continuous_induced_rng.2 ?_
    change Continuous fun p : G × O => p.1 * p.2.1 * p.1⁻¹
    fun_prop⟩
  have : MulAction.IsPretransitive G O := ⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact ⟨b⁻¹ * a, Subtype.ext (by rw [hsm]; group)⟩⟩
  have : LocallyCompactSpace O := hO.locallyCompactSpace
  let γ₀ : O := ⟨γ, 1, by group⟩
  have hopen : IsOpenMap (fun g : G => g • γ₀) := isOpenMap_smul_of_sigmaCompact γ₀
  have hsurj : Function.Surjective (fun g : G => g • γ₀) := fun y => MulAction.exists_smul_eq G γ₀ y
  have hD' : IsCompact (Subtype.val ⁻¹' D : Set O) := hO.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  obtain ⟨K, hK, hDK⟩ := UpperTheory.ConvolutionTheory.L1.compact_lift hopen hsurj hD'
  refine ⟨(·⁻¹) '' K, hK.image continuous_inv, fun x hx => ?_⟩
  obtain ⟨g, hg, hgx⟩ := hDK (a := ⟨x⁻¹ * γ * x, x, rfl⟩) hx
  have h1 : g * γ * g⁻¹ = x⁻¹ * γ * x := congrArg Subtype.val hgx
  refine ⟨x * g, ?_, g⁻¹, ⟨g, hg, rfl⟩, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro h rfl
  calc h * (x * g) = x * (x⁻¹ * h * x) * g := by group
    _ = x * (g * h * g⁻¹) * g := by rw [h1]
    _ = x * g * h := by group
end
