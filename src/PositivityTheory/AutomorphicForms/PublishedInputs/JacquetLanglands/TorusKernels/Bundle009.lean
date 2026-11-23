module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk

theorem lint_prod {I : Type} [Fintype I] [SigmaFinite (volume : Measure P)]
    (f : I → P → ℝ) (hf0 : ∀ v x, 0 ≤ f v x) (hm : ∀ v, Measurable (f v))
    (C : I → ℝ≥0) (hC : ∀ v, ∫⁻ x, ENNReal.ofReal (f v x) ≤ C v) :
    ∫⁻ w : I → P, ENNReal.ofReal (∏ v, f v (w v)) ≤ ((∏ v, C v : ℝ≥0) : ℝ≥0∞) := by
  have hint : ∀ v, Integrable (f v) := by
    intro v
    refine ⟨(hm v).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hf0 v))]
    exact lt_of_le_of_lt (hC v) ENNReal.coe_lt_top
  have hnn : ∀ w : I → P, 0 ≤ ∏ v, f v (w v) :=
    fun w => Finset.prod_nonneg fun v _ => hf0 v (w v)
  have hP : Integrable (fun w : I → P => ∏ v, f v (w v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hP (ae_of_all _ hnn),
    integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg (hf0 v)), ENNReal.ofNNReal_finsetProd]
  refine Finset.prod_le_prod' fun v _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hint v) (ae_of_all _ (hf0 v))]
  exact hC v

theorem har1 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') (e : ℝ) (he : 0 ≤ e) :
    kap z w ^ e ≤ (8 : ℝ) ^ e * kap z w' ^ e := by
  unfold B1c at hB
  obtain ⟨h1, -, h3, -⟩ := hB
  have hzw := (h1 z w).1
  have hzw' := (h1 z w').1
  have key : kap z w ≤ 8 * kap z w' := by
    nlinarith [h3 z w w', mul_le_mul_of_nonneg_left h hzw]
  calc kap z w ^ e ≤ (8 * kap z w') ^ e := Real.rpow_le_rpow hzw key he
    _ = (8 : ℝ) ^ e * kap z w' ^ e := Real.mul_rpow (by norm_num) hzw'

theorem har2 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') :
    (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) := by
  unfold B1c at hB
  obtain ⟨-, -, -, h4, -⟩ := hB
  have hw : 0 < |w.1.im| := abs_pos.mpr w.2
  have hw' : 0 < |w'.1.im| := abs_pos.mpr w'.2
  have hz : 0 ≤ |z.1.im| := abs_nonneg _
  have hww : |w'.1.im| ≤ 8 * |w.1.im| := by
    nlinarith [h4 w w', mul_le_mul_of_nonneg_right h hw'.le]
  have key : |z.1.im| / |w.1.im| ≤ 8 * (|z.1.im| / |w'.1.im|) := by
    rw [mul_div_assoc', div_le_div_iff₀ hw hw']
    nlinarith [mul_le_mul_of_nonneg_left hww hz]
  calc (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 * (|z.1.im| / |w'.1.im|)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hz hw.le) key (by norm_num)
    _ = (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (div_nonneg hz hw'.le)

theorem meas_abs_im : Measurable fun x : P => |x.1.im| := by
  exact (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable

end UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk.KappaIntegralLemmas in
theorem UpperTheory.Esk.pf_KapInt : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B6 → UpperTheory.Esk.KapInt := by
  intro hA _ hB h6
  unfold KapInt
  intro I _ k hk
  have hσ : SigmaFinite (volume : Measure P) := by
    unfold B1a at hA
    exact hA.1
  haveI := hσ
  have hB' := hB
  unfold B1c at hB'
  obtain ⟨h1, -, -, -, h5, -⟩ := hB'
  unfold B6 at h6
  choose Cv hCv using fun v => h6 (k v) (hk v)
  have ha : ∀ v, 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := fun v => by positivity
  have hA' : ((∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) : ℝ≥0) : ℝ)
      = ∏ v, (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [NNReal.coe_prod]
    exact Finset.prod_congr rfl fun v _ => Real.coe_toNNReal _ (ha v)
  refine ⟨∏ v, Cv v, ∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)), fun z => ?_⟩
  have hkm : ∀ v, Measurable (fun t : P => kap (z v) t) := fun v =>
    h5.measurable.comp (measurable_const.prodMk measurable_id)
  have hsplit : ∀ w : X I, Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
      = ∏ v, (kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) := by
    intro w
    rw [Finset.prod_mul_distrib]
    rfl
  refine ⟨?_, ?_, ?_, fun w w' hn => ⟨?_, ?_⟩⟩
  · unfold Kap
    exact Finset.measurable_prod _ fun v _ => ((hkm v).comp (measurable_pi_apply v)).pow_const _
  · unfold Kap
    exact lint_prod (fun v t => kap (z v) t ^ ((k v : ℝ) / 2))
      (fun v t => Real.rpow_nonneg (h1 _ _).1 _) (fun v => (hkm v).pow_const _) Cv
      (fun v => (hCv v (z v)).1)
  · simp only [hsplit]
    exact lint_prod
      (fun v t => kap (z v) t ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |t.1.im|) ^ ((1 : ℝ) / 2))
      (fun v t => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
        (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _))
      (fun v => ((hkm v).pow_const _).mul ((measurable_const.div meas_abs_im).pow_const _)) Cv
      (fun v => (hCv v (z v)).2)
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    unfold Kap
    rw [hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => Real.rpow_nonneg (h1 _ _).1 _) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hp : 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2)
        ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := e1
      _ ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left h8 hp]
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    rw [hsplit w, hsplit w', hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
      (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have e2 := har2 hB (z v) (w v) (w' v) (hn' v)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
        ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2)) *
            ((8 : ℝ) ^ ((1 : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul e1 e2 (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)
            (mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _))
      _ = ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) *
            (kap (z v) (w' v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) := by
        ring
end
end

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UpperTheory.Esk.SummedOrbitIntegrals

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]

theorem meas_pair [Countable α] {E : Type*} [MeasurableSpace E] {f : α → β → E} (hf : ∀ a, Measurable (f a)) :
    Measurable (fun q : α × β => f q.1 q.2) := by
  intro s hs
  have e : (fun q : α × β => f q.1 q.2) ⁻¹' s = ⋃ a : α, ({a} : Set α) ×ˢ (f a ⁻¹' s) := by
    ext ⟨a, b⟩
    simp
  rw [e]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hs)

theorem lint_pair (μ : Measure β) [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂(Measure.count.prod μ) = ∑' a, ∫⁻ y, f (a, y) ∂μ := by
  rw [lintegral_prod f hf.aemeasurable, lintegral_count]

theorem count_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable A] [Countable B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count : Measure A).prod (Measure.count : Measure B) = Measure.count := by
  refine Measure.ext_iff_singleton.2 fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.count_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, Measure.count_singleton, one_mul]

end UpperTheory.Esk.SummedOrbitIntegrals

open UpperTheory.Esk.SummedOrbitIntegrals in
theorem UpperTheory.Esk.pf_Fsum : UpperTheory.Esk.E0a → UpperTheory.Esk.Fsum := by
  intro h0 F I Gf _ _ _ D hax
  obtain ⟨hcG, hsig, -⟩ := h0 F I Gf D hax
  haveI : Countable D.Cj := hcG
  haveI : Countable D.Om := hax.cO
  haveI : SigmaFinite (volume : Measure D.Xs) := hsig
  haveI : SFinite D.μY := by unfold UpperTheory.Esk.Dat.μY; infer_instance
  intro b hb
  refine ⟨⟨hb.meas.comp (measurable_fst.snd.prodMk measurable_snd), fun p => hb.nonneg _,
    fun p => hb.sum (p.1.2, p.2)⟩, ?_⟩
  intro u hu hfin
  have hgm : Measurable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) :=
    meas_pair (f := fun (c : D.Cj) (y : D.Y) => b y • u (D.el c) y) fun c => hb.meas.smul (hu (D.el c))
  have hlin : ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) =
      ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
    calc ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY)
        = ∑' c : D.Cj, ∫⁻ y, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          lint_pair D.μY (fun q : D.Cj × D.Y => ‖b q.2 • u (D.el q.1) q.2‖ₑ) hgm.enorm
      _ = ∫⁻ y, ∑' c : D.Cj, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          (lintegral_tsum fun c => ((hb.meas.smul (hu (D.el c))).enorm).aemeasurable).symm
      _ = ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
          refine lintegral_congr fun y => ?_
          simp only [enorm_smul, Real.enorm_of_nonneg (hb.nonneg y)]
          exact ENNReal.tsum_mul_left
  have hgi : Integrable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) (Measure.count.prod D.μY) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) < ⊤
    rw [hlin]
    exact hfin
  have hae : ∀ᵐ y ∂D.μY, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) = b y • ∑' γ, u γ y := by
    filter_upwards [hgi.prod_left_ae] with y hy
    have hy' : Integrable (fun c : D.Cj => b y • u (D.el c) y) Measure.count := hy
    rw [integral_countable hy']
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    exact tsum_const_smul'' (b y)
  have hP : Integrable (fun y => b y • ∑' γ, u γ y) D.μY := hgi.integral_prod_right.congr hae
  have hm1 : Measurable (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) :=
    meas_pair (α := D.Cj × D.Om) (β := D.Xs) (f := fun a z => u (D.el a.1) (a.2, z))
      fun a => (hu (D.el a.1)).comp measurable_prodMk_left
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc : (D.Cj × D.Om) × D.Xs ≃ᵐ D.Cj × D.Om × D.Xs)
      D.μC (Measure.count.prod D.μY) := by
    have e : D.μC = (Measure.count.prod Measure.count).prod volume := by
      unfold UpperTheory.Esk.Dat.μC
      rw [count_prod]
    rw [e]
    exact measurePreserving_prodAssoc _ _ _
  have hC : Integrable (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2)) D.μC :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi
  have hint : ∫ y, b y • ∑' γ, u γ y ∂D.μY =
      ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC := by
    calc ∫ y, b y • ∑' γ, u γ y ∂D.μY
        = ∫ y, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) ∂D.μY := (integral_congr_ae hae).symm
      _ = ∫ q, b q.2 • u (D.el q.1) q.2 ∂(Measure.count.prod D.μY) := (integral_prod_symm _ hgi).symm
      _ = ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC :=
          (hmp.integral_comp' (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2)).symm
  exact ⟨hm1, hC, hP, hint⟩
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk

def B1 (C c : ℝ) : Set {z : ℂ // z.im ≠ 0} := {w | |w.1.re| ≤ C ∧ c ≤ |w.1.im|}

theorem measurableSet_cusp_region (C c : ℝ) : MeasurableSet (B1 C c) := by
  have h1 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.re| :=
    (continuous_abs.comp (Complex.continuous_re.comp continuous_subtype_val)).measurable
  have h2 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.im| :=
    (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le measurable_const h2)

theorem pt_bound (C c : ℝ) (hc : 0 < c) (t : ℂ) (h1 : |t.re| ≤ C) (h2 : c ≤ |t.im|) :
    1 / t.im ^ 2 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hb : c ^ 2 ≤ t.im ^ 2 := by
    nlinarith [sq_abs t.im, mul_nonneg (sub_nonneg.2 h2) (add_nonneg (abs_nonneg t.im) hc.le)]
  have ha : t.re ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_abs t.re, mul_nonneg (sub_nonneg.2 h1) (by linarith [abs_nonneg t.re] : 0 ≤ C + |t.re|)]
  have hbpos : 0 < t.im ^ 2 := lt_of_lt_of_le hc2 hb
  have e1 : 1 ≤ (1 + C ^ 2) * (1 + t.re ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have e2 : 1 / t.im ^ 2 ≤ (1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹ := by
    have h3 : 1 ≤ t.im ^ 2 / c ^ 2 := by
      rw [le_div_iff₀ hc2]
      linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hbpos (by positivity), add_mul, one_mul, one_div, inv_mul_eq_div]
    linarith
  calc 1 / t.im ^ 2 = 1 * (1 / t.im ^ 2) := (one_mul _).symm
    _ ≤ ((1 + C ^ 2) * (1 + t.re ^ 2)⁻¹) * ((1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by ring

theorem integ_G : ∫⁻ t : ℂ, ENNReal.ofReal ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) < ⊤ := by
  have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun p : ℝ × ℝ => (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) :=
    h1.mul_prod h1
  have h3 : Integrable (fun t : ℂ => (1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) :=
    (Complex.volume_preserving_equiv_real_prod.integrable_comp h2.aestronglyMeasurable).2 h2
  exact h3.lintegral_lt_top

private theorem volume_eq_lintegral_inv_im_sq_comap (s : Set {z : ℂ // z.im ≠ 0}) (hs : MeasurableSet s) :
    (volume : Measure P) (show Set P from s) = ∫⁻ z in s, ENNReal.ofReal (1 / z.1.im ^ 2)
      ∂(Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume) :=
  withDensity_apply _ hs

private theorem lintegral_comap_im_ne_zero_le_lintegral (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume) ≤ ∫⁻ t, f t := by
  have hs : MeasurableSet {z : ℂ | z.im ≠ 0} :=
    (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet
  calc ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume)
      = ∫⁻ t in {z : ℂ | z.im ≠ 0}, f t := lintegral_subtype_comap hs f
    _ ≤ ∫⁻ t, f t := setLIntegral_le_lintegral _ _

private theorem lintegral_mul_inv_one_add_sq_lt_top (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ t : ℂ, ENNReal.ofReal (K * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹)) < ⊤ := by
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top integ_G

private theorem lintegral_B1_inv_im_sq_le_lintegral (C c : ℝ) (hc : 0 < c) :
    ∫⁻ z in B1 C c, ENNReal.ofReal (1 / z.1.im ^ 2) ∂(Measure.comap Subtype.val volume) ≤
      ∫⁻ z : {z : ℂ // z.im ≠ 0}, ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
          ((1 + z.1.re ^ 2)⁻¹ * (1 + z.1.im ^ 2)⁻¹)) ∂(Measure.comap Subtype.val volume) := by
  refine le_trans (setLIntegral_mono' (measurableSet_cusp_region C c) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
  exact ENNReal.ofReal_le_ofReal (pt_bound C c hc z.1 hz.1 hz.2)

theorem volume_cusp_region_lt_top (C c : ℝ) (hc : 0 < c) : (volume : Measure P) (show Set P from B1 C c) < ⊤ := by
  have hK0 : 0 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) := by positivity
  rw [volume_eq_lintegral_inv_im_sq_comap _ (measurableSet_cusp_region C c)]
  exact lt_of_le_of_lt ((lintegral_B1_inv_im_sq_le_lintegral C c hc).trans (lintegral_comap_im_ne_zero_le_lintegral
    (fun t : ℂ => ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
      ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹))))) (lintegral_mul_inv_one_add_sq_lt_top _ hK0)

end UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk.CuspRegionVolume in
theorem UpperTheory.Esk.cusp_region_volume_finite_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.E3 := by
  intro hB1a _ hC2 hE0a hE0d
  intro F I Gf _ _ _ D hD b hb
  obtain ⟨hcnt, hsf, -, hPY, -, -, -, -⟩ := hE0a F I Gf D hD
  obtain ⟨-, hsm, -, -, -, -, -, -, -, hsurj, -⟩ := hE0d F I Gf D hD
  haveI : Countable (PG F) := hcnt
  haveI : SigmaFinite (volume : Measure D.Xs) := hsf
  haveI : SigmaFinite (volume : Measure P) := hB1a.1
  haveI : Countable D.Om := hD.cO
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have h01 : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1
  let T : Set D.Om := (fun x : Gf => (show D.Om from ((x : Gf) : Gf ⧸ D.H))) '' (S : Set Gf)
  let U : Set D.Xs := Set.univ.pi fun _ : I => (show Set P from B1 C c)
  have hT : T.Finite := S.finite_toSet.image _
  have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => measurableSet_cusp_region C c
  have hS : MeasurableSet (T ×ˢ U) := (MeasurableSet.of_discrete).prod hU
  have hcover : ∀ y : D.Y, ∃ g : PG F, g • y ∈ T ×ˢ U := by
    intro y
    obtain ⟨s, hs0, hs⟩ := hmink y.2 (D.rep y.1)
    obtain ⟨γ, hγ⟩ := hsurj s hs0
    set y' : D.Y := (γ : PG F) • y with hy'
    have h1 : c₀ ≤ D.Ht ![0, 1] y'.2 (D.rep y'.1) := by
      change c₀ ≤ D.HtY ![0, 1] ((γ : PG F) • y)
      rw [hsm ![0, 1] h01 γ y, hγ]
      exact hs
    obtain ⟨bb, -, ⟨x', hx'S, h, hhH, hjx⟩, hSg⟩ := hnorm y'.2 (D.rep y'.1) h1
    refine ⟨(bb : PG F) * (γ : PG F), ?_⟩
    rw [mul_smul, ← hy']
    refine ⟨?_, ?_⟩
    · have hy1 : ((D.rep y'.1 : Gf) : Gf ⧸ D.H) = y'.1 := Quotient.out_eq _
      have hm := D.mk_smulO bb (D.rep y'.1)
      rw [hy1] at hm
      refine ⟨x', hx'S, ?_⟩
      show (show D.Om from ((x' : Gf) : Gf ⧸ D.H)) = (bb : PG F) • y'.1
      rw [hm, hjx]
      refine (QuotientGroup.eq.2 ?_).symm
      rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem hhH
    · show (bb : PG F) • y'.2 ∈ U
      rw [D.mk_smulX]
      intro v _
      exact ⟨(hSg v).1, (hSg v).2.1⟩
  have hfin : D.μY (T ×ˢ U) < ⊤ := by
    unfold Dat.μY
    rw [Measure.prod_prod]
    refine ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 hT) ?_
    change (Measure.pi fun _ : I => (volume : Measure P)) (Set.univ.pi fun _ : I => (show Set P from B1 C c)) < ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => volume_cusp_region_lt_top C c hc
  exact lt_of_le_of_lt ((hC2 (PG F) D.Y).2 D.μY hPY b hb _ hS hcover) hfin
end
end
