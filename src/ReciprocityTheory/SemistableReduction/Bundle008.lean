module

public import ReciprocityTheory.SemistableReduction.Bundle001
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Finsupp.MonomialOrder
public import Lemmata.GeneralBFactLeftExtra.Imports
public import ReciprocityTheory.SemistableReduction.Bundle003
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Polynomial

theorem integral_Ioc_log_eval_eq_logMahlerMeasure (q : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖q.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ =
      q.logMahlerMeasure := by
  rw [logMahlerMeasure_def, Real.circleAverage, ← intervalIntegral.integral_of_le zero_le_one]
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left
    (fun θ => Real.log ‖eval (circleMap 0 1 θ) q‖) (a := 0) (b := 1) h2
  simp only [mul_zero, mul_one] at this
  rw [← this]
  congr 1
  funext t
  congr 3
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring_nf

theorem logMahlerMeasure_comp_C_mul_X_le (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    (p.comp (C c * X)).logMahlerMeasure ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  have hq : p.comp (C c * X) ≠ 0 := by
    intro h
    apply hp
    have h' := congrArg (fun r => r.comp (C c⁻¹ * X)) h
    have hX : (C c * X).comp (C c⁻¹ * X) = (X : ℂ[X]) := by
      simp [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc]
    simpa [Polynomial.comp_assoc, hX] using h'
  have key : ∀ s : Multiset ℂ, (((s.map fun a => X - C a).prod).comp (C c * X)).mahlerMeasure ≤
      ((s.map fun a => X - C a).prod).mahlerMeasure := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, mahlerMeasure_mul]
      apply mul_le_mul _ ih (mahlerMeasure_nonneg _) (mahlerMeasure_nonneg _)
      have h1 : (X - C a).comp (C c * X) = C c * X + C (-a) := by
        simp [sub_eq_add_neg]
      rw [h1, mahlerMeasure_C_mul_X_add_C, mahlerMeasure_X_sub_C, norm_neg]
      exact max_le_max hc1 le_rfl
  rw [logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_eq_log_MahlerMeasure]
  apply Real.log_le_log (mahlerMeasure_pos_of_ne_zero hq)
  have hs := (IsAlgClosed.splits p).eq_prod_roots
  rw [hs, mul_comp, C_comp, mahlerMeasure_mul, mahlerMeasure_mul]
  exact mul_le_mul_of_nonneg_left (key _) (mahlerMeasure_nonneg _)

theorem integral_log_eval_mul_le (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
        Real.log ‖p.eval (c * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ ≤
      ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ := by
  have h := integral_Ioc_log_eval_eq_logMahlerMeasure (p.comp (C c * X))
  simp only [eval_comp, eval_mul, eval_C, eval_X] at h
  rw [h, integral_Ioc_log_eval_eq_logMahlerMeasure]
  exact logMahlerMeasure_comp_C_mul_X_le p hc hc1

instance isProbabilityMeasure_restrict_Ioc_zero_one :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩

instance isProbabilityMeasure_torusProb_sphere (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance

theorem measurePreserving_update_torus {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) (torusProb ι) := by
  have hm : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, torusProb, Measure.pi_pi,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (s := Finset.univ) (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem integral_torus_eq_iter {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {g : (ι → ℝ) → ℝ}
    (hg : Integrable g (torusProb ι)) :
    Integrable (fun x => ∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) (torusProb ι) ∧
    ∫ θ, g θ ∂(torusProb ι) =
      ∫ x, (∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) ∂(torusProb ι) := by
  have hU := measurePreserving_update_torus (ι := ι) i
  have hgU : Integrable (g ∘ fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (hU.integrable_comp hg.aestronglyMeasurable).mpr hg
  refine ⟨hgU.integral_prod_left, ?_⟩
  have h1 : ∫ θ, g θ ∂(torusProb ι) = ∫ p, g (Function.update p.1 i p.2)
      ∂((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    conv_lhs => rw [← hU.map_eq]
    exact integral_map hU.measurable.aemeasurable (by rw [hU.map_eq]; exact hg.aestronglyMeasurable)
  rw [h1]
  exact integral_prod _ hgU

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

section Gauss

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem coeff_le_gauss_abs (w : FinitePlace K) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    w (f.coeff s) ≤ gaussAbs w f := by
  unfold gaussAbs
  by_cases hs : s ∈ f.support
  · have h := Finset.le_sup (f := fun s => (w (f.coeff s)).toNNReal) hs
    have h2 : ((w (f.coeff s)).toNNReal : ℝ) ≤ _ := NNReal.coe_le_coe.2 h
    rwa [Real.coe_toNNReal _ (apply_nonneg w _)] at h2
  · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
    exact NNReal.coe_nonneg _

theorem gauss_abs_le_of_coeff_le (w : FinitePlace K) (f : MvPolynomial σ K) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s, w (f.coeff s) ≤ M) : gaussAbs w f ≤ M := by
  unfold gaussAbs
  have h1 : (f.support.sup fun s => (w (f.coeff s)).toNNReal) ≤ M.toNNReal :=
    Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [Real.coe_toNNReal _ hM] at h2

theorem gauss_abs_attained_at_coeff (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ s ∈ f.support, gaussAbs w f = w (f.coeff s) := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup f.support
    (MvPolynomial.support_nonempty.2 hf) (fun s => (w (f.coeff s)).toNNReal)
  refine ⟨s, hs, ?_⟩
  unfold gaussAbs
  rw [hsup, Real.coe_toNNReal _ (apply_nonneg w _)]

theorem gauss_abs_pos_of_ne_zero (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    0 < gaussAbs w f := by
  obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
  rw [h]
  exact FinitePlace.pos_iff.2 (MvPolynomial.mem_support_iff.1 hs)

theorem finite_place_sum_le {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  first | exact Bl.general_b_fact_left_extra.goal1 .. | (apply Bl.general_b_fact_left_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_extra.goal1 <;> assumption)

theorem finite_place_sum_lt {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ t, w (a i) < M) : w (∑ i ∈ t, a i) < M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans_lt (max_lt (h j (Finset.mem_insert_self j t)) ?_)
    exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

theorem finite_place_add_eq_of_lt (w : FinitePlace K) (x y : K) (h : w y < w x) : w (x + y) = w x := by
  apply le_antisymm
  · exact (FinitePlace.add_le w x y).trans (max_le le_rfl h.le)
  · have h1 : w x ≤ max (w (x + y)) (w (-y)) := by
      have := FinitePlace.add_le w (x + y) (-y)
      rwa [add_neg_cancel_right] at this
    rw [map_neg_eq_map] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem gauss_abs_mul_of_monomial_order (m : MonomialOrder σ) (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  classical
  have hGf := gauss_abs_pos_of_ne_zero w f hf
  have hGg := gauss_abs_pos_of_ne_zero w g hg
  apply le_antisymm
  · refine gauss_abs_le_of_coeff_le w _ (mul_nonneg hGf.le hGg.le) fun u => ?_
    rw [MvPolynomial.coeff_mul]
    refine finite_place_sum_le w _ _ (mul_nonneg hGf.le hGg.le) fun x _ => ?_
    rw [map_mul]
    exact mul_le_mul (coeff_le_gauss_abs w f _) (coeff_le_gauss_abs w g _) (apply_nonneg w _) hGf.le
  ·
    set Sf := f.support.filter (fun s => w (f.coeff s) = gaussAbs w f)
    set Sg := g.support.filter (fun s => w (g.coeff s) = gaussAbs w g)
    have hSf : Sf.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    have hSg : Sg.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w g hg
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    obtain ⟨s0, hs0, hs0max⟩ := Finset.exists_max_image Sf (fun s => m.toSyn s) hSf
    obtain ⟨t0, ht0, ht0max⟩ := Finset.exists_max_image Sg (fun s => m.toSyn s) hSg
    have hfs0 : w (f.coeff s0) = gaussAbs w f := (Finset.mem_filter.1 hs0).2
    have hgt0 : w (g.coeff t0) = gaussAbs w g := (Finset.mem_filter.1 ht0).2
    have hbigf : ∀ s, m.toSyn s0 < m.toSyn s → w (f.coeff s) < gaussAbs w f := by
      intro s hs
      refine lt_of_le_of_ne (coeff_le_gauss_abs w f s) fun heq => ?_
      have hmem : s ∈ Sf := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGf.ne heq
      exact absurd (hs0max s hmem) (not_le.2 hs)
    have hbigg : ∀ t, m.toSyn t0 < m.toSyn t → w (g.coeff t) < gaussAbs w g := by
      intro t ht
      refine lt_of_le_of_ne (coeff_le_gauss_abs w g t) fun heq => ?_
      have hmem : t ∈ Sg := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGg.ne heq
      exact absurd (ht0max t hmem) (not_le.2 ht)
    have hmemu : (s0, t0) ∈ Finset.HasAntidiagonal.antidiagonal (s0 + t0) := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    have hrest : w (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (s0 + t0)).erase (s0, t0),
        f.coeff x.1 * g.coeff x.2) < gaussAbs w f * gaussAbs w g := by
      refine finite_place_sum_lt w _ _ (mul_pos hGf hGg) fun x hx => ?_
      obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.1 hx
      have hsum : x.1 + x.2 = s0 + t0 := Finset.HasAntidiagonal.mem_antidiagonal.1 hxmem
      have hsyn : m.toSyn x.1 + m.toSyn x.2 = m.toSyn s0 + m.toSyn t0 := by
        rw [← map_add (f := _), ← map_add (f := _), hsum]
      rw [map_mul]
      rcases lt_trichotomy (m.toSyn x.1) (m.toSyn s0) with h1 | h1 | h1
      · have h2 : m.toSyn t0 < m.toSyn x.2 := by
          by_contra h2
          have := add_lt_add_of_lt_of_le h1 (not_lt.1 h2)
          rw [hsyn] at this
          exact lt_irrefl _ this
        calc w (f.coeff x.1) * w (g.coeff x.2) ≤ gaussAbs w f * w (g.coeff x.2) :=
              mul_le_mul_of_nonneg_right (coeff_le_gauss_abs w f _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_left (hbigg _ h2) hGf
      · exfalso
        have e1 : x.1 = s0 := m.toSyn.injective h1
        have e2 : x.2 = t0 := by
          rw [e1] at hsum
          exact add_left_cancel hsum
        exact hxne (Prod.ext e1 e2)
      · calc w (f.coeff x.1) * w (g.coeff x.2) ≤ w (f.coeff x.1) * gaussAbs w g :=
              mul_le_mul_of_nonneg_left (coeff_le_gauss_abs w g _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_right (hbigf _ h1) hGg
    have hcoeff : w ((f * g).coeff (s0 + t0)) = gaussAbs w f * gaussAbs w g := by
      rw [MvPolynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmemu]
      rw [finite_place_add_eq_of_lt w _ _ (by rwa [map_mul, hfs0, hgt0]), map_mul, hfs0, hgt0]
    rw [← hcoeff]
    exact coeff_le_gauss_abs w _ _

theorem gauss_abs_mul [Fintype σ] (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact gauss_abs_mul_of_monomial_order MonomialOrder.lex w f g hf hg

end Gauss

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance isProbabilityMeasure_torusProb (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance

def tmUpd (i : ι) : (ι → ℝ) × ℝ → (ι → ℝ) := fun p => update p.1 i p.2

lemma measurable_tmUpd (i : ι) : Measurable (tmUpd i) := by
  first
  | exact measurable_update' (a := i)
  | exact measurable_pi_iff.mpr fun j => by
      by_cases h : j = i
      · subst h; simpa [tmUpd] using measurable_snd
      · simpa [tmUpd, Function.update_of_ne h] using (measurable_pi_apply j).comp measurable_fst

lemma tmUpd_preimage_pi (i : ι) (s : ι → Set ℝ) :
    tmUpd i ⁻¹' (Set.univ.pi s) = (Set.univ.pi (update s i Set.univ)) ×ˢ s i := by
  ext ⟨θ, t⟩
  simp only [Set.mem_preimage, tmUpd, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
  constructor
  · intro h
    refine ⟨fun j => ?_, by simpa using h i⟩
    by_cases hj : j = i
    · subst hj; simp
    · simpa [hj] using h j
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i
    · subst hj; simpa using h2
    · simpa [hj] using h1 j

lemma measurePreserving_tmUpd (i : ι) :
    MeasurePreserving (tmUpd i) ((torusProb ι).prod unitIntervalMeasure) (torusProb ι) := by
  refine ⟨measurable_tmUpd i, ?_⟩
  have h1 : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1 := by simp
  unfold torusProb
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_tmUpd i) (MeasurableSet.univ_pi hs), tmUpd_preimage_pi,
    Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  have hp : ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (update s i Set.univ j) =
      ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (s j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hp, Function.update_self, h1, one_mul, mul_comm]

lemma tm_integrable_comp (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    Integrable (F ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) ↔ Integrable F (torusProb ι) := by
  exact (measurePreserving_tmUpd i).integrable_comp hF

lemma tm_integral_comp (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    ∫ θ, F θ ∂(torusProb ι) = ∫ p, F (tmUpd i p) ∂((torusProb ι).prod unitIntervalMeasure) := by
  have hmap := (measurePreserving_tmUpd i).map_eq
  conv_lhs => rw [← hmap]
  exact integral_map (measurable_tmUpd i).aemeasurable (by rwa [hmap])

lemma tm_measure_null (i : ι) {S : Set (ι → ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ θ ∂(torusProb ι), unitIntervalMeasure {t | update θ i t ∈ S} = 0) : torusProb ι S = 0 := by
  rw [← (measurePreserving_tmUpd i).measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply ((measurable_tmUpd i) hS)]
  have h2 : (fun θ => unitIntervalMeasure (Prod.mk θ ⁻¹' (tmUpd i ⁻¹' S))) =ᵐ[torusProb ι] 0 :=
    h.mono fun θ hθ => hθ
  rw [lintegral_congr_ae h2]
  simp

def tmSlice (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) : Polynomial ℂ :=
  ∑ s ∈ f.support, Polynomial.monomial (s i)
    (MvPolynomial.eval x (MvPolynomial.monomial (s.erase i) (f.coeff s)))

lemma tmSlice_coeff (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) (k : ℕ) :
    (tmSlice i x f).coeff k = MvPolynomial.eval x (coeffIn i k f) := by

  simp only [tmSlice, coeffIn, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, map_sum,
  Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

lemma tm_eval_update (i : ι) (x : ι → ℂ) (z : ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (update x i z) f = (tmSlice i x f).eval z := by
  conv_lhs => rw [f.as_sum]

  simp only [tmSlice, map_sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
  MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i, Function.update_self,
    Finsupp.erase_same, pow_zero, one_mul]
  have hp : ∏ j ∈ ({i}ᶜ : Finset ι), update x i z j ^ s j =
      ∏ j ∈ ({i}ᶜ : Finset ι), x j ^ (Finsupp.erase i s) j :=
    Finset.prod_congr rfl fun j hj => by
      have hji : j ≠ i := by simpa using hj
      rw [Function.update_of_ne hji, Finsupp.erase_ne hji]
  rw [hp]
  ring

lemma torusPoint_update (θ : ι → ℝ) (i : ι) (t : ℝ) :
    torusPoint (update θ i t) = update (torusPoint θ) i (circPt t) := by
  funext j
  by_cases h : j = i
  · subst h; simp [torusPoint, circPt]
  · simp [torusPoint, Function.update_of_ne h]

lemma norm_torusPoint (θ : ι → ℝ) (j : ι) : ‖torusPoint θ j‖ = 1 := by simp [torusPoint, Complex.norm_exp]

lemma norm_eval_torus_le (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
  rw [norm_mul, norm_prod]
  simp [norm_pow, norm_torusPoint]

lemma continuous_eval_torus (f : MvPolynomial ι ℂ) :
    Continuous fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f := by
  exact (MvPolynomial.continuous_eval f).comp (continuous_pi fun j => by unfold torusPoint; fun_prop)

lemma measurable_logEval (f : MvPolynomial ι ℂ) :
    Measurable fun θ : ι → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ := Real.measurable_log.comp (continuous_eval_torus f).norm.measurable

lemma vars_coeffIn_subset (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) :
    (coeffIn i k f).vars ⊆ f.vars.erase i := by
  intro j hj
  unfold coeffIn at hj
  have h1 := MvPolynomial.vars_sum_subset _ _ hj
  rw [Finset.mem_biUnion] at h1
  obtain ⟨s, hs, hjs⟩ := h1
  have hsf : s ∈ f.support := (Finset.mem_filter.mp hs).1
  rw [MvPolynomial.vars_monomial (MvPolynomial.mem_support_iff.mp hsf), Finsupp.support_erase,
    Finset.mem_erase] at hjs
  exact Finset.mem_erase.mpr ⟨hjs.1, (MvPolynomial.mem_vars_iff_mem_support j).mpr ⟨s, hsf, hjs.2⟩⟩

end ReciprocityTheory.MultiplicativeHeights
end
end
