module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P.Specmeas

variable {X : Type} [TopologicalSpace X]

def ofR (g : C(X, ℝ)) : C(X, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩

@[simp] lemma ofR_apply (g : C(X, ℝ)) (x : X) : ofR g x = (g x : ℂ) := rfl

lemma ofR_add (g h : C(X, ℝ)) : ofR (g + h) = ofR g + ofR h := by
  ext x; simp

lemma ofR_sub (g h : C(X, ℝ)) : ofR (g - h) = ofR g - ofR h := by
  ext x; simp

lemma ofR_smul (c : ℝ) (g : C(X, ℝ)) : ofR (c • g) = (c : ℂ) • ofR g := by
  ext x; simp

def reC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
def imC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩

lemma eq_ofR_re_add_im (f : C(X, ℂ)) : f = ofR (reC f) + Complex.I • ofR (imC f) := by
  ext x
  simp [reC, imC, mul_comm Complex.I, Complex.re_add_im]

section
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ

lemma nonneg_ofR {g : C(X, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ Λ (ofR g) := by
  let s : C(X, ℝ) := ⟨fun x => Real.sqrt (g x), by fun_prop⟩
  have : ofR g = star (ofR s) * ofR s := by
    ext x
    simp only [ofR_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply, s,
      ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hg x)]
  rw [this]; exact hΛ _

lemma im_ofR (g : C(X, ℝ)) : (Λ (ofR g)).im = 0 := by
  let p : C(X, ℝ) := ⟨fun x => max (g x) 0, by fun_prop⟩
  let n : C(X, ℝ) := ⟨fun x => max (-g x) 0, by fun_prop⟩
  have hg : g = p - n := by
    ext x
    simp only [p, n, ContinuousMap.sub_apply, ContinuousMap.coe_mk]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hp := nonneg_ofR Λ hΛ (g := p) (fun x => le_max_right _ _)
  have hn := nonneg_ofR Λ hΛ (g := n) (fun x => le_max_right _ _)
  rw [Complex.le_def] at hp hn
  rw [hg, ofR_sub, map_sub, Complex.sub_im, ← hp.2, ← hn.2]; simp

lemma ofR_eq_re (g : C(X, ℝ)) : Λ (ofR g) = ((Λ (ofR g)).re : ℂ) := by
  apply Complex.ext <;> simp [im_ofR Λ hΛ g]

end

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem exists_measure_of_positive (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ.Regular ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ := by
  let Λr : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { toFun g := (Λ (ofR g.toContinuousMap)).re
    map_add' g g' := by
      have : (g + g').toContinuousMap = g.toContinuousMap + g'.toContinuousMap := rfl
      rw [this, ofR_add, map_add (f := _), Complex.add_re]
    map_smul' c g := by
      have : (c • g).toContinuousMap = c • g.toContinuousMap := rfl
      rw [this, ofR_smul, map_smul]; simp
    monotone' g g' hgg' := by
      have h := nonneg_ofR Λ hΛ (g := g'.toContinuousMap - g.toContinuousMap)
        (fun x => sub_nonneg.2 (hgg' x))
      rw [ofR_sub, map_sub, Complex.le_def] at h
      have := h.1
      simp only [Complex.zero_re, Complex.sub_re] at this
      linarith }
  refine ⟨RealRMK.rieszMeasure Λr, inferInstance, inferInstance, fun f => ?_⟩
  have key : ∀ g : C(X, ℝ), Λ (ofR g) = ((∫ x, g x ∂(RealRMK.rieszMeasure Λr) : ℝ) : ℂ) := by
    intro g
    have := RealRMK.integral_rieszMeasure Λr (CompactlySupportedContinuousMap.continuousMapEquiv g)
    rw [ofR_eq_re Λ hΛ g]
    congr 1
    exact this.symm
  have hint : Integrable (fun x => f x) (RealRMK.rieszMeasure Λr) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  conv_lhs => rw [eq_ofR_re_add_im f]
  rw [map_add (f := _), map_smul, key, key, ← integral_re_add_im hint, smul_eq_mul, mul_comm]
  rfl

end PositivityTheory.Rg.BcB.E2.P.Specmeas

namespace PositivityTheory.Rg.BcB.E2.P

theorem specmeas : SpecMeas := by
  intro K _ _ _ S _ _ _ _ _ π v
  let Λ : C(S, ℂ) →ₗ[ℂ] ℂ :=
  { toFun f := inner ℂ v (π f v)
    map_add' f g := by simp [map_add (f := _)]
    map_smul' c f := by simp }
  have hΛ : ∀ f : C(S, ℂ), 0 ≤ Λ (star f * f) := by
    intro f
    show 0 ≤ inner ℂ v (π (star f * f) v)
    rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    exact pow_nonneg (Complex.zero_le_real.mpr (norm_nonneg (π f v))) 2
  obtain ⟨ν, h1, h2, h3⟩ := Specmeas.exists_measure_of_positive Λ hΛ
  exact ⟨ν, h1, h2, fun f => (h3 f).symm⟩

end PositivityTheory.Rg.BcB.E2.P

end
end

section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem gelf : Gelf := by
  intro K _ _ _ B _ _ _ _ R
  let A0 : StarSubalgebra ℂ (K →L[ℂ] K) := R.range
  have hc : ∀ x y : A0, x * y = y * x := by
    rintro ⟨x, b, rfl⟩ ⟨y, c, rfl⟩
    apply Subtype.ext
    change R b * R c = R c * R b
    rw [← map_mul, ← map_mul, mul_comm]
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := A0.topologicalClosure
  have : IsClosed (A : Set (K →L[ℂ] K)) := A0.isClosed_topologicalClosure
  let cr : CommRing A := A0.commRingTopologicalClosure hc
  let _ : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := cr.mul_comm }
  let G := gelfandStarTransform A
  have hmem : ∀ b, R b ∈ A := fun b => A0.le_topologicalClosure ⟨b, rfl⟩
  refine ⟨WeakDual.characterSpace ℂ A, inferInstance, inferInstance, inferInstance,
    A.subtype.comp G.symm.toStarAlgHom, G.toStarAlgHom.comp (R.codRestrict A hmem), ?_, ?_⟩
  · intro f
    have h1 : ‖G (G.symm f)‖ = ‖G.symm f‖ := (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) _
    rw [G.apply_symm_apply] at h1
    rw [h1]
    rfl
  · intro b
    change ((G.symm (G ⟨R b, hmem b⟩) : A) : K →L[ℂ] K) = R b
    rw [G.symm_apply_apply]

end PositivityTheory.Rg.BcB.E2.P
end

section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.E2.P

namespace Locint

theorem enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

end Locint

theorem locint : Tonelli → LocInt := by
  intro hT X S _ ν _ F f hF hrep
  let K := CompactExhaustion.choice X.G
  have hfin : ∀ n, ∀ᵐ s ∂ν, ∫⁻ y, (K n).indicator 1 y * ‖f y s‖ₑ ^ 2 ∂X.μ < ⊤ := by
    intro n
    have hK : IsCompact (K n) := K.isCompact n
    have hW : Measurable ((K n).indicator (1 : X.G → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    apply hT X.G S X.μ ν F f _ hrep hW
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
    refine ne_top_of_le_ne_top (b := ∫⁻ y, (K n).indicator (fun _ => ENNReal.ofReal C ^ 2) y ∂X.μ) ?_ ?_
    · rw [lintegral_indicator_const hK.measurableSet]
      exact ENNReal.mul_ne_top (by simp) hK.measure_lt_top.ne
    · refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ K n
      · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC y hy)
      · simp [Set.indicator_of_notMem hy]
  rw [← ae_all_iff] at hfin
  filter_upwards [hfin] with s hs
  have hm : Measurable fun y => f y s := hrep.1.of_uncurry_right
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hk
  refine IntegrableOn.mono_set ?_ hn
  have hKn : IsCompact (K n) := K.isCompact n
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have heq : (fun y => (K n).indicator 1 y * ‖f y s‖ₑ ^ 2) = (K n).indicator (fun y => ‖f y s‖ₑ ^ 2) := by
    ext y; by_cases hy : y ∈ K n <;> simp [hy]
  have h2 := hs n
  rw [heq, lintegral_indicator hKn.measurableSet] at h2
  show ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) < ⊤
  calc ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) ≤ ∫⁻ y, (1 + ‖f y s‖ₑ ^ 2) ∂(X.μ.restrict (K n)) :=
        lintegral_mono fun y => Locint.enorm_le_one_add_sq _
    _ = X.μ (K n) + ∫⁻ y, ‖f y s‖ₑ ^ 2 ∂(X.μ.restrict (K n)) := by
        rw [lintegral_add_left measurable_const]; simp
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hKn.measure_lt_top, h2⟩

end PositivityTheory.Rg.BcB.E2.P

end
end

section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem point : Point := by
  unfold PositivityTheory.Rg.BcB.E2.Point
  intro B _ _ _ _ S _ _ e p hp
  by_contra hne
  push Not at hne
  choose b hb using hne
  let c : S → B := fun s => b s - algebraMap ℂ B (p (b s))
  have hpc : ∀ s, p (c s) = 0 := fun s => by
    simp only [c, map_sub]
    rw [AlgHomClass.commutes]
    simp
  have hec : ∀ s, e (c s) s ≠ 0 := fun s => by
    have h1 : e (c s) s = e (b s) s - p (b s) := by
      simp only [c, map_sub, ContinuousMap.sub_apply]
      rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one]
    rw [h1]
    exact sub_ne_zero.2 (hb s)
  let g : S → B := fun s => star (c s) * c s
  have hpg : ∀ s, p (g s) = 0 := fun s => by simp [g, hpc]
  have heg : ∀ s t, e (g s) t = ((‖e (c s) t‖ ^ 2 : ℝ) : ℂ) := fun s t => by
    simp only [g, map_mul, map_star, ContinuousMap.mul_apply, ContinuousMap.star_apply]
    rw [Complex.ofReal_pow]
    exact Complex.conj_mul' _
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun s => {t : S | e (c s) t ≠ 0})
    (fun s => isOpen_compl_singleton.preimage (e (c s)).continuous)
    (fun t _ => Set.mem_iUnion.2 ⟨t, hec t⟩)
  let G : B := ∑ s ∈ F, g s
  let v : S → ℝ := fun t => ∑ s ∈ F, ‖e (c s) t‖ ^ 2
  have hpG : p G = 0 := by simp [G, hpg]
  have heG : ∀ t, e G t = (v t : ℂ) := fun t => by

    simp only [G, v, map_sum, ContinuousMap.sum_apply, heg]
    push_cast
    rfl
  have hv : ∀ t, 0 < v t := fun t => by
    obtain ⟨s, hsF, hs⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ t))
    have hs' : e (c s) t ≠ 0 := hs
    exact Finset.sum_pos' (fun i _ => by positivity) ⟨s, hsF, pow_pos (norm_pos_iff.2 hs') 2⟩
  have hvM : ∀ t, v t ≤ ‖e G‖ := fun t => by
    have h1 := ContinuousMap.norm_coe_le_norm (e G) t
    rw [heG, Complex.norm_real, Real.norm_of_nonneg (hv t).le] at h1
    exact h1
  have hM : 0 ≤ ‖e G‖ := norm_nonneg _
  have key := hp (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)
  have hp1 : p (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) = 1 := by simp [hpG]
  rw [hp1, norm_one] at key
  have hlt : ‖e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)‖ < 1 := by
    rw [ContinuousMap.norm_lt_iff _ one_pos]
    intro t
    have ht : e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) t = ((1 - v t / (‖e G‖ + 1) : ℝ) : ℂ) := by
      simp only [map_sub, map_one, map_smul, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.smul_apply, heG, smul_eq_mul]
      push_cast
      ring
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have h2 : v t / (‖e G‖ + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith [hvM t]
    have h3 : 0 < v t / (‖e G‖ + 1) := div_pos (hv t) (by linarith)
    constructor <;> linarith
  linarith

end PositivityTheory.Rg.BcB.E2.P
end

section

open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Fdata

lemma mul_le_weighted_squares (a b W : ℝ≥0∞) (h0 : W ≠ 0) (ht : W ≠ ⊤) : a * b ≤ W⁻¹ * a ^ 2 + W * b ^ 2 := by
  rcases le_or_gt a (W * b) with h | h
  · calc a * b ≤ W * b * b := by gcongr
      _ = W * b ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ _ := le_add_self
  · have hb : b ≤ W⁻¹ * a := by
      calc b = W⁻¹ * (W * b) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
        _ ≤ W⁻¹ * a := by gcongr
    calc a * b ≤ a * (W⁻¹ * a) := by gcongr
      _ = W⁻¹ * a ^ 2 := by ring
      _ ≤ _ := le_self_add

end Fdata

theorem fdata : RowsEx → RowsEig → FData := by
  intro hRx hRe X ι _ K _ _ _ J B _ _ _ _ R a₀ Φ g W S _ ν _ χ V hJ hΦ hT hS hne hW hW' hWc hg hg'
  obtain ⟨T₁, hT₁, hT₁J⟩ := hT 1
  obtain ⟨k, hk⟩ := hRx X ι (Φ 1) T₁ (hΦ 1) hT₁
  set L : Lp ℂ 2 ν →L[ℂ] X.Hs ι := J.comp V with hL
  have hLn : ∀ h, ‖L h‖ = ‖h‖ := fun h => (hJ _).trans (hS.iso h)
  have hL1 : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [hLn, one_mul]
  set A := ContinuousLinearMap.adjoint L with hA
  have hAn : ∀ v, ‖A v‖ ≤ ‖v‖ := fun v => by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ 1 * ‖v‖ := by
          gcongr
          rw [hA, LinearIsometryEquiv.norm_map]
          exact hL1
      _ = ‖v‖ := one_mul _
  have hAe : ∀ v, ‖A v‖ₑ ≤ ‖v‖ₑ := fun v => by
    rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hAn v)
  have hin : ∀ v h, inner ℂ (A v) h = inner ℂ v (L h) := fun v h =>
    ContinuousLinearMap.adjoint_inner_left L h v
  have hT1L : ∀ h, T₁ (L h) = J (R a₀ (V h)) := fun h => by
    show T₁ (J (V h)) = _
    rw [hT₁J, one_mul]
  have hmem : ∀ b (h : Lp ℂ 2 ν), MemLp (fun s => χ s b * h s) 2 ν := fun b h =>
    MemLp.of_le_mul (c := ‖R b‖) (Lp.memLp h)
      ((hS.meas b).aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
      (Filter.Eventually.of_forall fun s => by rw [norm_mul]; gcongr; exact hS.bdd b s)
  have hwt : ∀ i, ∫⁻ x, W x * ‖A (k i x)‖ₑ ^ 2 ∂X.ν ≠ ⊤ := by
    intro i
    obtain ⟨C, Ω, hC, hΩ, hkC⟩ := hk.norm
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (hWc Ω hΩ)) ?_
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_mono fun x => ?_
    calc W x * ‖A (k i x)‖ₑ ^ 2 ≤ W x * ‖k i x‖ₑ ^ 2 := by gcongr; exact hAe _
      _ ≤ W x * (C * cnt X.Γ Ω x) := by gcongr; exact hkC i x
      _ = C * (W x * cnt X.Γ Ω x) := by ring
  refine ⟨fun i x => A (k i x), ?_⟩
  refine ⟨fun i => A.continuous.comp (hk.cont i), fun i γ hγ x => by simp only [hk.inv i γ hγ x], ?_, hwt, ?_, ?_, ?_⟩
  ·
    intro hF0
    have hA0 : ∀ i x, A (k i x) = 0 := fun i x => congrFun (congrFun hF0 i) x
    have h0 : ∀ h, T₁ (L h) = 0 := fun h => by
      refine PiLp.ext fun i => ?_
      rw [PiLp.zero_apply]
      refine Lp.ext ?_
      filter_upwards [hk.rep (L h) i, Lp.coeFn_zero ℂ 2 X.ν] with x h1 h2
      rw [h1, h2, ← hin, hA0, inner_zero_left]
      rfl
    set h1 : Lp ℂ 2 ν := (memLp_const (1 : ℂ)).toLp _ with hh1
    set h' : Lp ℂ 2 ν := (hmem a₀ h1).toLp _ with hh'
    have hV : V h' = R a₀ (V h1) := hS.mul _ h1 _ (MemLp.coeFn_toLp _)
    have hJ0 : J (V h') = 0 := by rw [hV, ← hT1L, h0]
    have hn : ‖h'‖ = 0 := by rw [← hS.iso, ← hJ, hJ0, norm_zero]
    have hz : h' = 0 := norm_eq_zero.1 hn
    have hae : ∀ᵐ s ∂ν, False := by
      filter_upwards [hne, MemLp.coeFn_toLp (hmem a₀ h1), MemLp.coeFn_toLp (memLp_const (1 : ℂ) (μ := ν) (p := 2)),
        Lp.coeFn_zero ℂ 2 ν] with s hs e1 e2 e3
      apply hs
      have : (h' : S → ℂ) s = 0 := by rw [hz, e3]; rfl
      rw [hh', e1, hh1, e2] at this
      simpa using this
    exact hS.ne (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hae))
  ·
    intro c x i h
    set h' : Lp ℂ 2 ν := (hmem (c * a₀) h).toLp _ with hh'
    have hV : V h' = R (c * a₀) (V h) := hS.mul _ h _ (MemLp.coeFn_toLp _)
    obtain ⟨Tc, hTc, hTcJ⟩ := hT c
    have key : Tc (T₁ (L h)) = T₁ (L h') := by
      rw [hT1L, hT1L, hTcJ, hV]
      congr 1
      show (R (c * a₀) * R a₀) (V h) = (R a₀ * R (c * a₀)) (V h)
      rw [← map_mul, ← map_mul, mul_comm]
    have e := hRe X ι (Φ c) Tc T₁ k (L h) (L h') (hΦ c) hTc hk key x i
    simp only [hin]
    rw [e, ← hin, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hmem (c * a₀) h)] with s hs
    rw [hs, RCLike.inner_apply']
    ring
  ·
    intro n i
    have hgm : AEStronglyMeasurable (fun x => (g n i : X.G → ℂ) x) X.ν := Lp.aestronglyMeasurable _
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hgm, ?_⟩
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hg' n i, hwt i⟩) ?_
    have hm : AEMeasurable (fun x => (W x)⁻¹ * ‖(g n i : X.G → ℂ) x‖ₑ ^ 2) X.ν :=
      hW.inv.aemeasurable.mul (hgm.enorm.pow_const 2)
    rw [← lintegral_add_left' hm]
    refine lintegral_mono fun x => ?_
    rw [RCLike.enorm_conj]
    exact Fdata.mul_le_weighted_squares _ _ _ (hW' x).1 (hW' x).2
  ·
    intro n h
    have e : ∀ i, ∫ x, conj ((g n i : X.G → ℂ) x) * inner ℂ (A (k i x)) h ∂X.ν = inner ℂ (g n i) (T₁ (L h) i) := by
      intro i
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hk.rep (L h) i] with x hx
      rw [hx, hin, RCLike.inner_apply']
    simp only [e]
    rw [← PiLp.inner_apply, hT1L]
    exact inner_eq_zero_symm.1 (hg n _)

end PositivityTheory.Rg.BcB.E2.P
end

section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory

theorem hssep : HsSep := by
  intro X ι _
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  haveI : IsSeparable X.ν := inferInstance
  haveI : SecondCountableTopology (Lp ℂ 2 X.ν) := inferInstance
  infer_instance

end PositivityTheory.Rg.BcB.E2.P
end
