module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSpanStep

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  apply _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepHomog.mul_mem <;> assumption

theorem prod_pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {q : ℕ} {w : Fin q → Ω}
    (hw : ∀ j, w j ∈ chartLat y a 1) (ν : Fin q → ℕ) (S : Finset (Fin q)) :
    ∏ j ∈ S, w j ^ ν j ∈ chartLat y a (∑ j ∈ S, ν j) := by
  have hpow : ∀ (j : Fin q) (e : ℕ), w j ^ e ∈ chartLat y a e := by
    intro j e
    induction e with
    | zero => intro c _; simp
    | succ e ih => rw [pow_succ]; exact mul_mem ih (hw j)
  refine Finset.induction_on S ?_ ?_
  · intro c _
    simp
  · intro j S hj ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact mul_mem (hpow j (ν j)) ih

end SectionSpanStep


open SectionSpanStep in
theorem SectionSpanStep.proof (hH : SpanStepHomog.Statement) (hS : SerreGraded.Statement) :
    SectionSpanStep.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  obtain ⟨m, r, t, ht, hloc⟩ := hH K ι Ω y a q w hy hw hgen
  have hne : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    choose c hc using hy
    obtain ⟨u, -, hu⟩ := hgen c hc
    simp [h] at hu
  obtain ⟨n₀, hn₀⟩ := hS Ω q r w (fun _ => m) t hne
  refine ⟨max n₀ m, fun n hn s hs => ?_⟩
  have hs' : s ∈ gradedSpan w (fun _ => m) t (n + 1) :=
    hn₀ (n + 1) (by omega) s fun j hj => hloc (n + 1) s hs j hj
  refine (AddSubgroup.closure_le _).2 ?_ hs'
  rintro x ⟨l, μ, hdeg, rfl⟩
  have hdeg : m + ∑ i, μ i = n + 1 := hdeg
  obtain ⟨j, hj⟩ : ∃ j, 0 < μ j := by
    by_contra h
    push Not at h
    have h0 : ∑ i, μ i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)
    omega
  set μ' : Fin q → ℕ := μ - Pi.single j 1 with hμ'
  have hμ : μ = μ' + Pi.single j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp [hμ']
      omega
    · simp [hμ', hij]
  have hsum : ∑ i, μ i = ∑ i, μ' i + 1 := by
    rw [hμ]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
  have hprod : ∏ i, w i ^ μ i = (∏ i, w i ^ μ' i) * w j := by
    rw [hμ]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_eq_single j]
    · simp
    · intro i hi
      simp [hi]
  apply AddSubgroup.subset_closure
  refine ⟨t l * ∏ i, w i ^ μ' i, ?_, j, by rw [hprod, mul_assoc]⟩
  have hmem := mul_mem (ht l) (prod_pow_mem hw μ' Finset.univ)
  have hdeg' : m + ∑ i, μ' i = n := by omega
  rwa [hdeg'] at hmem

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

def intNumMultilinear {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRingOver ℚ ι)) (n : ℕ) (hI : NumbersDVR.IsMultiHomogIdeal I)
    (hr : NumbersDVR.IsRelevant I) (hd : FieldNumbers.relDim I = n) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => K → ℤ) ℤ where
  toFun bs := NumbersDVR.intNum ℚ I bs
  map_update_add' := by
    intro inst bs i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact FieldNumbers.IntNumAdd.full ℚ K ι I hI hr n hd bs i x y
  map_update_smul' := by
    intro inst bs i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    let g : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun x => NumbersDVR.intNum ℚ I (Function.update bs i x))
      fun x y => FieldNumbers.IntNumAdd.full ℚ K ι I hI hr n hd bs i x y
    exact map_zsmul g c x

theorem intNumMultilinear_apply {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRingOver ℚ ι)) (n : ℕ) (hI : NumbersDVR.IsMultiHomogIdeal I)
    (hr : NumbersDVR.IsRelevant I) (hd : FieldNumbers.relDim I = n) (bs : Fin n → K → ℤ) :
    intNumMultilinear I n hI hr hd bs = NumbersDVR.intNum ℚ I bs :=
  rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (L : Fin D → HermLine ι) (A₁ : HermLine ι),
    (∀ j, IsSmoothHerm (L j)) → A₁.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A₁ →
    ptsIntegral (mCoordIdeal d.y) (fun j z => Real.log ((L j).h z)) (fun z => Real.log (A₁.h z / d.A.h z)) =
      mInt d.R.A (fun j => AnResBridge.potOf d.R (L j))
        (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
  GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {N : ℕ}

namespace ProjFS

lemma isOpen_chartVec_ne (i j : Fin (N + 1)) : IsOpen {z : Fin N → ℂ | chartVec i z j ≠ 0} :=
  isOpen_ne_fun (contDiff_chartVec_apply ℂ i j).continuous continuous_const

lemma transition_transition {i j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    transition j i (transition i j z) = z := by
  change chartCoord i (chartInv j (chartCoord j (chartInv i z))) = z
  rw [chartInv_chartCoord j (show chartInv i z ∈ chartDomain j from hz), chartCoord_chartInv]

lemma chartVec_transition_apply {i j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0)
    (m : Fin (N + 1)) : chartVec j (transition i j z) m = (chartVec i z j)⁻¹ * chartVec i z m := by
  rw [chartVec_transition i j hz]; rfl

lemma image_transition (j : Fin (N + 1)) :
    transition 0 j '' {z : Fin N → ℂ | chartVec 0 z j ≠ 0} = {y | chartVec j y 0 ≠ 0} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change chartVec j (transition 0 j z) 0 ≠ 0
    rw [chartVec_transition_apply hz, chartVec_self, mul_one]
    exact inv_ne_zero hz
  · intro hy
    refine ⟨transition j 0 y, ?_, transition_transition hy⟩
    change chartVec 0 (transition j 0 y) j ≠ 0
    rw [chartVec_transition_apply hy, chartVec_self, mul_one]
    exact inv_ne_zero hy

lemma injOn_transition (i j : Fin (N + 1)) :
    Set.InjOn (transition i j) {z : Fin N → ℂ | chartVec i z j ≠ 0} := fun z hz z' hz' h => by
  rw [← transition_transition hz, h, transition_transition hz']

lemma ae_chartVec_ne (j : Fin (N + 1)) : ∀ᵐ y : Fin N → ℂ, chartVec j y 0 ≠ 0 := by
  obtain h | ⟨k, hk⟩ := Fin.eq_self_or_eq_succAbove j 0
  · exact Filter.Eventually.of_forall fun y => by rw [h, chartVec_self]; exact one_ne_zero
  · rw [ae_iff]
    have hset : {y : Fin N → ℂ | ¬ chartVec j y 0 ≠ 0} = Function.eval k ⁻¹' {0} := by
      ext y
      simp only [ne_eq, not_not, mem_setOf_eq, mem_preimage, Function.eval, mem_singleton_iff]
      rw [hk, chartVec_succAbove]
    rw [hset, volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem setLIntegral_fsMeasure_chartDomain (j : Fin (N + 1)) (g : CP N → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in chartDomain j, g x ∂fsMeasure N =
      ∫⁻ y, g (chartInv j y) * ENNReal.ofReal (fsVolumeDensity j y) := by
  have hD : MeasurableSet (chartDomain (N := N) j) := (isOpen_chartDomain j).measurableSet
  rw [fsMeasure, setLIntegral_map hD hg (measurable_chartInv 0), fsChartMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_fsVolumeDensity 0).ennreal_ofReal
      (show Measurable (fun x => g (chartInv 0 x)) from hg.comp (measurable_chartInv 0))
      (hD.preimage (measurable_chartInv 0))]
  have hW : chartInv 0 ⁻¹' chartDomain j = {z : Fin N → ℂ | chartVec 0 z j ≠ 0} := rfl
  rw [hW]
  have hae : (Set.univ : Set (Fin N → ℂ)) =ᵐ[volume]
      transition 0 j '' {z : Fin N → ℂ | chartVec 0 z j ≠ 0} := by
    rw [image_transition]
    filter_upwards [ae_chartVec_ne j] with y hy
    exact ⟨fun _ => hy, fun _ => trivial⟩
  conv_rhs => rw [← setLIntegral_univ]
  rw [setLIntegral_congr hae,
    lintegral_image_eq_lintegral_normSq_det_mul (transition 0 j) _ (isOpen_chartVec_ne 0 j)
      (fun z hz => analyticAt_transition 0 j hz) (injOn_transition 0 j)]
  refine setLIntegral_congr_fun (isOpen_chartVec_ne 0 j).measurableSet fun z hz => ?_
  have h1 : chartInv j (transition 0 j z) = chartInv 0 z :=
    chartInv_chartCoord j (show chartInv 0 z ∈ chartDomain j from hz)
  have h2 : fsVolumeDensity 0 z =
      Complex.normSq (jacC (transition 0 j) z).det * fsVolumeDensity j (transition 0 j z) := by
    rw [fsVolumeDensity_transition 0 j hz,
      det_fderiv_real_eq_normSq _ z (differentiableAt_transition 0 j hz),
      abs_of_nonneg (Complex.normSq_nonneg _)]
  simp only [Pi.mul_apply]
  rw [h1, h2, ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
  ring

end ProjFS

def fsVolume (N : ℕ) : SmoothVolume (projAtlas N) where
  μ := fsMeasure N
  isProb := inferInstance
  dens := fsVolumeDensity
  smooth (j : Fin (N + 1)) := by
    have h : fsVolumeDensity (N := N) j =
        fun z => (N.factorial : ℝ) / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) :=
      funext fun z => fsVolumeDensity_eq j z
    rw [h]
    have hs : ContDiff ℝ ∞ (normSqSum (N := N)) := by
      unfold normSqSum; exact contDiff_normSqSum
    refine (contDiff_const.div (contDiff_const.mul ((contDiff_const.add hs).pow _))
      fun z => ?_).contDiffOn
    have := one_add_normSqSum_pos z
    have := Real.pi_pos
    positivity
  pos (j : Fin (N + 1)) y _ := fsVolumeDensity_pos j y
  chart_lintegral (j : Fin (N + 1)) g hg := by
    change ∫⁻ x in chartDomain j, g x ∂fsMeasure N =
      ∫⁻ y in univ, g (chartInv j y) * ENNReal.ofReal (fsVolumeDensity j y)
    rw [setLIntegral_univ]
    exact ProjFS.setLIntegral_fsMeasure_chartDomain j g hg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem mixedDiff_zero {K : Type*} (h : (K → ℤ) → ℤ) (bs : Fin 0 → K → ℤ) :
    mixedDiff bs h = h := by
  simp [mixedDiff]

theorem relDim_eq_zero_of_ringKrullDim {F : Type*} [Field F] {K : Type} [Fintype K]
    {ι : K → Type} (q : Ideal (MRing ι F))
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  unfold GroundTheory.Heights₂.Heights.FieldNumbers.relDim
  rw [hd]
  simp
  change WithTop.map (fun e : ℕ => (e : ℤ) - (Fintype.card K : ℤ))
    ((Fintype.card K : ℕ) : WithTop ℕ) = 0
  exact congrArg WithTop.some (sub_self _)

theorem HilbertDimZero.proof : HilbertDimZero.Statement.{u} := by
  intro F _ K _ _ ι _ q hq hd
  have h0 := ((GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst.full.{u} F K ι q hq.multiHomog
    hq.relevant 0 (relDim_eq_zero_of_ringKrullDim q hd)).1 (![] : Fin 0 → K → ℤ))
  simp only [mixedDiff_zero] at h0
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h0
  refine ⟨Finset.univ.sup fun k => (b k).toNat, fun a ha => hb _ fun k => ?_⟩
  have h1 : (b k).toNat ≤ a k :=
    le_trans (Finset.le_sup (f := fun k => (b k).toNat) (Finset.mem_univ k)) (ha k)
  have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
  show b k ≤ (a k : ℤ)
  omega

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenFibreHomog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sum_block_eq_weight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, m ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) m k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isMultiHomog_of_weighted {f : MRing ι} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f b) : IsMultiHomog f b := by
  intro m hm k
  rw [sum_block_eq_weight, hf (mem_support_iff.mp hm)]

theorem coeff_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MRing ι) :
    AddMonoidAlgebra.coeff (mConeMap y f) (Finsupp.equivFunOnFinite.symm b) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) m = _)
    rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_of_weighted hm),
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) m)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]

theorem isMultiHomogIdeal_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := ℤ) (mCoordIdeal y) := by
  intro f hf b
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  change mConeMap y _ = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y
      (isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous b f)),
    ← coeff_mConeMap, hf']
  simp

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [∀ k, Fintype (ι k)] in
theorem isHomogeneous_of_isMultiHomogIdeal {R : Type} [CommRing R] {I : Ideal (MvPolynomial (Σ k, ι k) R)}
    (h : NumbersDVR.IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
  intro b f hf
  have key : (DirectSum.decompose (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) f b :
      MvPolynomial (Σ k, ι k) R) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f :=
    weightedDecomposition.decompose'_apply R (NumbersDVR.blockWeight ι) f b
  rw [key]
  exact h f hf b

end GenFibreHomog


open GenFibreHomog in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in
theorem GenFibreHomog.proof : GenFibreHomog.Statement := by
  intro K _ _ ι _ Ω _ y
  have hI := isHomogeneous_of_isMultiHomogIdeal (isMultiHomogIdeal_mCoordIdeal y)
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  have hJ : ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))).IsHomogeneous
      (weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι)) := by
    rw [hS, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := s.2
    refine ⟨b, ?_⟩
    rw [mem_weightedHomogeneousSubmodule] at hb ⊢
    intro d hd
    apply hb
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem ℚ _ hJ hf b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
