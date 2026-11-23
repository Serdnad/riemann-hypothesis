module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle008
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import GroundTheory.HeightsAndTheta.Heights.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]

theorem segreMap_monomial_isMultiHomog (d : ((_ : Unit) × ((k : K) → ι k)) →₀ ℕ) (a : F) :
    IsMultiHomog (segreMap F (monomial d a))
      (fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) := by
  unfold IsMultiHomog
  rw [segreMap, aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine IsWeightedHomogeneous.C_mul ?_ a
  have hX : ∀ v : (_ : Unit) × ((k : K) → ι k),
      IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
    intro v
    have := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => Pi.single k 1)
      (fun k _ => isWeightedHomogeneous_X F _ _)
    convert this using 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := IsWeightedHomogeneous.prod d.support
    (fun v => (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) ^ d v) (fun v => d v • (fun _ : K => (1 : ℕ)))
    (fun v _ => (hX v).pow _)
  have e : (fun _ : K => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) =
      ∑ v ∈ d.support, d v • (fun _ : K => (1 : ℕ)) := by
    ext j
    simp [Finsupp.weight_apply, Finsupp.sum, blockWeight, Finset.sum_apply]
  rw [e]
  exact this

theorem segreMap_weightedHomogeneousComponent [Nonempty K] (b : Unit → ℕ)
    (g : MRing (fun _ : Unit => ∀ k, ι k) F) :
    segreMap F (weightedHomogeneousComponent (blockWeight (fun _ : Unit => ∀ k, ι k)) b g) =
      weightedHomogeneousComponent (blockWeight ι) (fun _ => b ()) (segreMap F g) := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := isWeightedHomogeneous_monomial (blockWeight (fun _ : Unit => ∀ k, ι k)) d a rfl
    rw [weightedHomogeneousComponent_of_mem h1,
      weightedHomogeneousComponent_of_mem (segreMap_monomial_isMultiHomog F d a)]
    have key : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ↔
        (fun _ : K => b ()) = fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d () := by
      constructor
      · rintro rfl; rfl
      · intro h; funext u; cases u; exact congr_fun h (Classical.arbitrary K)
    by_cases h : b = Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d
    · rw [if_pos h, if_pos (key.mp h)]
    · rw [if_neg h, if_neg (mt key.mpr h), map_zero]
  | add p p' hp hp' => simp only [map_add (f := _), hp, hp']

theorem SegrePrime.proof : SegrePrime.Statement := by
  intro F _ K _ _ _ ι _ q hq
  have := hq.isPrime
  refine ⟨segrePrime.isPrime F q, ?_, ?_⟩
  · intro g hg b
    rw [segrePrime, Ideal.mem_comap] at hg ⊢
    rw [segreMap_weightedHomogeneousComponent]
    exact hq.multiHomog _ hg _
  · intro u
    cases u
    choose i hi using hq.relevant
    refine ⟨i, ?_⟩
    rw [segrePrime, Ideal.mem_comap, segreMap_X, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, _, hk⟩
    exact hi k hk

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Cardinal

noncomputable section

theorem SegreDimGe.proof : SegreDimGe.Statement := by
  intro F _ K _ _ _ ι _ q e hq hdim
  have := hq.isPrime
  let π : MRing ι F →ₐ[F] MRing ι F ⧸ q := Ideal.Quotient.mkₐ F q
  let φ : MRing (fun _ : Unit => ∀ k, ι k) F →ₐ[F] MRing ι F ⧸ q := π.comp (segreMap F)
  let R' : Subalgebra F (MRing ι F ⧸ q) := φ.range
  choose i hi using hq.relevant
  let x : K → MRing ι F ⧸ q := fun k => π (X ⟨k, i k⟩)
  have hx0 : ∀ k, x k ≠ 0 := fun k h =>
    hi k (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [x, π, Ideal.Quotient.mkₐ_eq_mk] using h))

  have hkey : ∀ k (j : ι k), (∏ l ∈ Finset.univ.erase k, x l) * π (X ⟨k, j⟩) =
      φ (X ⟨(), Function.update i k j⟩) := by
    intro k j
    rw [AlgHom.comp_apply, segreMap_X, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  let k0 : K := Classical.arbitrary K
  let s : Set (MRing ι F ⧸ q) := x '' ↑(Finset.univ.erase k0)
  let B : Subalgebra R' (MRing ι F ⧸ q) := Algebra.adjoin R' s
  have hR'B : ∀ a ∈ R', IsAlgebraic B a := fun a ha =>
    isAlgebraic_algebraMap (⟨a, Subalgebra.algebraMap_mem B (⟨a, ha⟩ : R')⟩ : B)
  have hsB : ∀ l, l ≠ k0 → IsAlgebraic B (x l) := fun l hl =>
    isAlgebraic_algebraMap (⟨x l, Algebra.subset_adjoin
      ⟨l, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩), rfl⟩⟩ : B)
  have hgen : ∀ k, (∀ l, l ≠ k → IsAlgebraic B (x l)) → ∀ j : ι k, IsAlgebraic B (π (X ⟨k, j⟩)) := by
    intro k hk j
    have hy : IsAlgebraic B (∏ l ∈ Finset.univ.erase k, x l) :=
      Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isAlgebraic_one
        fun l hl => hk l (Finset.ne_of_mem_erase hl)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ?_) hy ?_
    · exact Finset.prod_ne_zero_iff.mpr fun l _ => hx0 l
    · rw [hkey]
      exact hR'B _ ⟨_, rfl⟩
  have hall : ∀ l, IsAlgebraic B (x l) := by
    intro l
    by_cases hl : l = k0
    · subst hl
      exact hgen _ hsB (i _)
    · exact hsB l hl
  have hA : ∀ a : MRing ι F ⧸ q, IsAlgebraic B a := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective F q a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.algHom_C]
      exact hR'B _ (R'.algebraMap_mem c)
    | add p r hp hr => rw [map_add (f := _)]; exact hp.add hr
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hgen v.1 (fun l _ => hall l) v.2)
  have : Algebra.IsAlgebraic B (MRing ι F ⧸ q) := ⟨hA⟩
  have htop : Algebra.trdeg R' (MRing ι F ⧸ q) ≤ #s := Algebra.IsAlgebraic.trdeg_le_cardinalMk R' s
  have hs : #s ≤ (Fintype.card K - 1 : ℕ) := by
    refine Cardinal.mk_image_le.trans ?_
    simp
  have : FaithfulSMul F R' :=
    (faithfulSMul_iff_algebraMap_injective F R').mpr (algebraMap F R').injective
  have : FaithfulSMul R' (MRing ι F ⧸ q) :=
    ⟨fun {r₁ r₂} h => Subtype.ext (by simpa [Subalgebra.smul_def] using h 1)⟩
  have htower := trdeg_add_eq (A := MRing ι F ⧸ q) F R'

  let g : (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) →ₐ[F] R' :=
    Ideal.Quotient.liftₐ (segrePrime F q) φ.rangeRestrict fun p hp => by
      apply Subtype.ext
      simpa [φ, π, segrePrime, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hp
  have hg : Function.Surjective g := by
    rintro ⟨y, p, rfl⟩
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hR'le := trdeg_le_of_surjective g hg
  obtain ⟨n, hn, htn⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing ι F ⧸ q)
  obtain ⟨m, hm, htm⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q)
  have hne : n = e + Fintype.card K := by
    rw [hn] at hdim
    exact_mod_cast hdim
  have hcard : (n : Cardinal) ≤ (m + (Fintype.card K - 1) : ℕ) := by
    rw [← htn, ← htower, Nat.cast_add, ← htm]
    exact add_le_add hR'le (htop.trans hs)
  have hK : 0 < Fintype.card K := Fintype.card_pos
  have hnm : n ≤ m + (Fintype.card K - 1) := by exact_mod_cast hcard
  rw [hm]
  exact_mod_cast (show e + 1 ≤ m by omega)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem continuousOn_source_of_chart {E : Type*} [TopologicalSpace E] {f : X → E} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source)) :
    ContinuousOn f (A.chart j).source := by
  have h := hf.comp (A.chart j).continuousOn (fun y hy =>
    ⟨(A.chart j).map_source hy, by simpa [(A.chart j).left_inv hy] using hy⟩)
  exact h.congr (fun y hy => by simp [(A.chart j).left_inv hy])

theorem ptNormSq_eq_of_mem (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ptNormSq W n s x = ‖s j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) := by
  have hk : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hkj : x ∈ (A.chart (chartIdx A x)).source ∩ (A.chart j).source := ⟨hk, hx⟩
  have hg : 0 < ‖L.g (chartIdx A x) j x‖ ^ 2 := by
    have := L.ne_zero _ _ x hkj
    positivity
  have he : Real.exp ((n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hg n)]
  rw [ptNormSq, hs.2.1 _ j x hkj, W.compat _ j x hkj, norm_mul, norm_pow,
    show -(n : ℝ) * (W.φ j x + Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      -(n : ℝ) * W.φ j x - (n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2) by ring,
    Real.exp_sub, he]
  have hp : 0 < (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := pow_pos hg n
  field_simp
  ring

theorem ptNormSq_nonneg (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq; positivity

theorem continuous_ptNormSq (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hx⟩ := A.cover x
  have hsj : ContinuousOn (s j) (A.chart j).source :=
    continuousOn_source_of_chart j (hs.1 j j).continuousOn
  have hφj : ContinuousOn (W.φ j) (A.chart j).source :=
    continuousOn_source_of_chart j (W.smooth j j).continuousOn
  have hF : ContinuousOn (fun y => ‖s j y‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j y))
      (A.chart j).source :=
    ((hsj.norm.pow 2).mul ((continuousOn_const.mul hφj).rexp))
  have hopen := (A.chart j).open_source
  refine (hF.continuousAt (hopen.mem_nhds hx)).congr ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact (ptNormSq_eq_of_mem W hs j hy).symm

theorem ptNormSq_smul (W : Weight L) (n : ℕ) (c : ℂ) (s : Fin A.n → X → ℂ) (x : X) :
    ptNormSq W n (c • s) x = ‖c‖ ^ 2 * ptNormSq W n s x := by
  simp only [ptNormSq, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

variable [MeasurableSpace X] [BorelSpace X]

theorem SmoothVolume.isOpenPosMeasure (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU ⟨x, hxU⟩ hzero => ?_⟩
  obtain ⟨j, hx⟩ := A.cover x
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U with hOdef
  have hO : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hU
  have hxO : A.chart j x ∈ O :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hOt : O ⊆ (A.chart j).target := inter_subset_left
  have hmeas : Measurable (U.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have h1 := dV.chart_lintegral j _ hmeas
  have hL : ∫⁻ y in (A.chart j).source, U.indicator (1 : X → ℝ≥0∞) y ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left hzero
  rw [hL] at h1
  have h2 : ∫⁻ y in O, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in O, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in O, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := by
          refine setLIntegral_congr_fun hO.measurableSet fun y hy => ?_
          rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hOt
      _ = 0 := h1.symm
  have hae : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y)) (volume.restrict O) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((dV.smooth j).continuousOn).mono hOt).aemeasurable hO.measurableSet)
  have h3 := (lintegral_eq_zero_iff' hae).1 h2
  rw [EventuallyEq, ae_restrict_iff' hO.measurableSet] at h3
  have h4 : volume O = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h3] with y hy hyO
    exact (ENNReal.ofReal_pos.2 (dV.pos j y (hOt hyO))).ne' (hy hyO)
  exact hO.measure_ne_zero volume ⟨_, hxO⟩ h4

theorem integrable_ptNormSq (W : Weight L) (dV : SmoothVolume A) [CompactSpace X] {n : ℕ}
    {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) : Integrable (ptNormSq W n s) dV.μ := by
  have := dV.isProb
  exact (continuous_ptNormSq W hs).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [BorelSpace X] in
theorem sectionL2NormSq_nonneg (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) :
    0 ≤ sectionL2NormSq W dV n s :=
  integral_nonneg fun x => ptNormSq_nonneg W n s x


omit [BorelSpace X] in
theorem sectionL2NormSq_smul (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (c : ℂ)
    (s : Fin A.n → X → ℂ) : sectionL2NormSq W dV n (c • s) = ‖c‖ ^ 2 * sectionL2NormSq W dV n s := by
  simp only [sectionL2NormSq, ptNormSq_smul]
  exact integral_const_mul _ _

theorem ptNormSq_eq_zero_of_l2NormSq_eq_zero (W : Weight L) (dV : SmoothVolume A) [CompactSpace X]
    {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (h0 : sectionL2NormSq W dV n s = 0) (x : X) :
    ptNormSq W n s x = 0 := by
  have := dV.isOpenPosMeasure
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => ptNormSq_nonneg W n s y)
    (integrable_ptNormSq W dV hs)).1 h0
  have := (Continuous.ae_eq_iff_eq (μ := dV.μ) (continuous_ptNormSq W hs) continuous_const).1 hae
  exact congrFun this x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def GramChiDerivative.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → ∀ (e : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (t : ℝ),
      HasDerivAt (fun s : ℝ ↦ chiGram (W₀.lerp W₁ s) dV n (fun a ↦ (e a : Fin A.n → X → ℂ)))
        ((n : ℝ) / 2 * ∫ x, Weight.diff W₁ W₀ x * bergman (W₀.lerp W₁ t) dV V n x ∂dV.μ) t

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

def BergmanDensChartSum.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A)
    (P : ChartPartition A) (g : X → ℝ), Continuous g →
      ∫ x, g x * bergmanDens W dV x ∂dV.μ =
        (∑ j, ∫ y in (A.chart j).target,
          P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * chernTopDens W j y) / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def BergmanDensIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), Integrable (bergmanDens W dV) dV.μ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def BergmanIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → Integrable (bergman W dV V n) dV.μ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def ChartTaylorCover.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A),
    ∃ r : ℝ, 0 < r ∧ ∃ M c : ℝ, 0 < c ∧ ∀ x : X, ∃ j : Fin A.n, x ∈ (A.chart j).source ∧
      Metric.closedBall (A.chart j x) r ⊆ (A.chart j).target ∧
      (∀ y ∈ Metric.closedBall (A.chart j x) r, c ≤ dV.dens j y) ∧
      ∀ W ∈ [W₀, W₁], ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + M * ∑ i, ‖z i‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
