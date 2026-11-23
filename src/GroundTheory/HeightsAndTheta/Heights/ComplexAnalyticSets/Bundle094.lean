module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle076
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle082
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Matrix

noncomputable section

theorem PosPartIndep.proof (h : SheetOnlyNull.Statement) (hL : PosPartLocal.Statement)
    (hS : PosPartSplit.Statement) : PosPartIndep.Statement := by
  intro n d J A A' f φ hJ hd hA hA' hf hφ

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', IsSheetAt J A' x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A A' f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ k, x ∈ E k := by
    intro x hxZ h1 h2
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x h1 h2⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  have hae : ∀ B B' : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B → IsFiniteProjection J B' →
      (∀ x ∈ zeroSet J, (∃ s, IsSheetAt J B x s) → (∃ s', IsSheetAt J B' x s') → ∃ k, x ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B B' hB hB' hc
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h n d J B B' hJ hd hB hB')] with y hy
    refine hS n d J B f φ E y hB hEd fun x hx hs => hc x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  have hint : ∀ B : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B →
      (∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y)) →
      ∫⁻ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B hB hB2
    rw [lintegral_congr_ae hB2, lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hB (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  rw [hint A hA (hae A A' hA hA' hcov),
    hint A' hA' (hae A' A hA' hA fun x hx h1 h2 => hcov x hx h2 h1)]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

namespace DiscriminantSheetCover

theorem volume_zero_set {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0) :
    volume {y : Fin d → ℂ | eval y P = 0} = 0 := by
  set S := {y : Fin d → ℂ | eval y P = 0} with hSdef
  have hS : MeasurableSet S :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  have hnull : μH[((2 * d : ℕ) : ℝ)]
      (zeroSetEuc ((⊥ : Ideal (MvPolynomial (Fin d) ℂ)) ⊔ Ideal.span {P})) = 0 :=
    NullSmaller.proof d d _ (MassFinite.dim_sup_lt ⊥ Ideal.isPrime_bot (space_dim d) P
      (by simpa [Ideal.mem_bot] using hP))
  obtain ⟨c, hc⟩ := SheetAreaCompare.exists_lintegral_volume_eq d
  have h := hc (S.indicator 1)
  rw [lintegral_indicator_one hS] at h
  rw [h]
  have hae : (fun y : EuclideanSpace ℂ (Fin d) => S.indicator (1 : (Fin d → ℂ) → ENNReal) (WithLp.ofLp y))
      =ᵐ[(μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d)))] 0 := by
    refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
    have hyS : WithLp.ofLp y ∈ S := by
      by_contra h'
      exact hy (by simp [Set.indicator_of_notMem h'])
    intro q hq
    rw [bot_sup_eq] at hq
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    have : eval (WithLp.ofLp y) P = 0 := hyS
    simp only [map_mul]
    rw [show (fun i => y i) = WithLp.ofLp y from rfl, this, mul_zero]
  rw [lintegral_congr_ae hae]
  simp

theorem local_sheets {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {P : MvPolynomial (Fin d) ℂ} {N : ℕ}
    (hcov : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (fibre J A y).Finite ∧ (fibre J A y).ncard = N ∧
        ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A.mulVec (g w) = w) ∧
            zeroSet J ∩ V = g '' U)
    (y₀ : Fin d → ℂ) (hy₀ : eval y₀ P ≠ 0) :
    ∃ W : Set (Fin d → ℂ), IsOpen W ∧ y₀ ∈ W ∧ W ⊆ {y | eval y P ≠ 0} ∧
      ∃ s : Fin N → (Fin d → ℂ) → Fin n → ℂ, (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ y ∈ W, fibre J A y = Set.range (fun j => s j y) ∧ Function.Injective (fun j => s j y) ∧
          ∀ j, IsSheetAt J A (s j y) (s j) := by
  obtain ⟨hfin, hcard, hloc⟩ := hcov y₀ hy₀
  have : Finite (fibre J A y₀) := hfin
  let e : fibre J A y₀ ≃ Fin N := Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hcard])
  let x : Fin N → Fin n → ℂ := fun j => (e.symm j).1
  have hx : ∀ j, x j ∈ fibre J A y₀ := fun j => (e.symm j).2
  have hxinj : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  choose U V g hU hyU hV hxV hg hgy hAg hZ using fun j => hloc (x j) (hx j)
  have hcont : ∀ j, ContinuousAt (g j) y₀ := fun j =>
    (hg j).continuousOn.continuousAt ((hU j).mem_nhds (hyU j))
  have hev : ∀ᶠ w in 𝓝 y₀, (∀ j, w ∈ U j) ∧ eval w P ≠ 0 ∧ ∀ i j, i ≠ j → g i w ≠ g j w := by
    refine (eventually_all.2 fun j => (hU j).mem_nhds (hyU j)).and
      (((MvPolynomial.continuous_eval P).continuousAt.eventually_ne hy₀).and ?_)
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · have hne : g i y₀ - g j y₀ ≠ 0 := by
        rw [hgy, hgy]; exact sub_ne_zero.2 fun h => hij (hxinj h)
      filter_upwards [((hcont i).sub (hcont j)).eventually_ne hne] with w hw _
      exact sub_ne_zero.1 hw
  obtain ⟨W, hWsub, hWo, hyW⟩ := mem_nhds_iff.1 hev
  have hgZ : ∀ j, ∀ w ∈ U j, g j w ∈ zeroSet J ∩ V j := fun j w hw => (hZ j).symm ▸ ⟨w, hw, rfl⟩
  refine ⟨W, hWo, hyW, fun w hw => (hWsub hw).2.1, g,
    fun j => (hg j).mono fun w hw => (hWsub hw).1 j, fun w hw => ?_⟩
  obtain ⟨hwU, hwP, hwinj⟩ := hWsub hw
  have hinj : Function.Injective (fun j => g j w) := fun i j h => by_contra fun hij => hwinj i j hij h
  have hsub : Set.range (fun j => g j w) ⊆ fibre J A w := by
    rintro _ ⟨j, rfl⟩
    exact ⟨(hgZ j w (hwU j)).1, hAg j w (hwU j)⟩
  obtain ⟨hfinw, hcardw, -⟩ := hcov w hwP
  refine ⟨(Set.eq_of_subset_of_ncard_le hsub ?_ hfinw).symm, hinj, fun j => ?_⟩
  · rw [hcardw, Set.ncard_range_of_injective hinj, Nat.card_fin]
  · refine ⟨W, hWo, by rw [hAg j w (hwU j)]; exact hw, (hg j).mono fun v hv => (hWsub hv).1 j,
      by rw [hAg j w (hwU j)], fun v hv => ⟨hAg j v ((hWsub hv).1 j), (hgZ j v ((hWsub hv).1 j)).1⟩,
      V j, (hV j).mem_nhds (hgZ j w (hwU j)).2, fun x' hx' _ => ?_⟩
    obtain ⟨u, hu, rfl⟩ : x' ∈ g j '' U j := hZ j ▸ hx'
    rw [hAg j u hu]

end DiscriminantSheetCover

theorem DiscriminantSheetCover.proof (h₁ : ComplexSets.DiscriminantCover.Statement) :
    DiscriminantSheetCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨P, hP, hcov⟩ := h₁ n d J A hJ hdim hA
  have hall : ∀ y : Fin d → ℂ, ∃ W : Set (Fin d → ℂ), IsOpen W ∧ (eval y P ≠ 0 → y ∈ W) ∧
      W ⊆ {y | eval y P ≠ 0} ∧ ∃ s : Fin (projDegree J A) → (Fin d → ℂ) → Fin n → ℂ,
        (∀ j, DifferentiableOn ℂ (s j) W) ∧
        ∀ w ∈ W, fibre J A w = Set.range (fun j => s j w) ∧ Function.Injective (fun j => s j w) ∧
          ∀ j, IsSheetAt J A (s j w) (s j) := by
    intro y
    by_cases hy : eval y P = 0
    · exact ⟨∅, isOpen_empty, fun h => absurd hy h, Set.empty_subset _, fun _ _ => 0,
        fun _ => differentiableOn_empty, fun _ h => h.elim⟩
    · obtain ⟨W, hWo, hyW, hWP, s, hs, hsW⟩ := DiscriminantSheetCover.local_sheets hcov y hy
      exact ⟨W, hWo, fun _ => hyW, hWP, s, hs, hsW⟩
  choose W hWo hyW hWP s hs hsW using hall
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : {y | eval y P ≠ 0} ⊆ ⋃ k, W (e k) := by
    intro y hy
    have : y ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨y, hyW y hy⟩
    obtain ⟨i, hiT, hyi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact Set.mem_iUnion.2 ⟨k, hyi⟩
  have hcompl : (⋃ k, disjointed (fun k => W (e k)) k)ᶜ ⊆ {y | eval y P = 0} := by
    rw [iUnion_disjointed]
    intro y hy
    by_contra h
    exact hy (hcover h)
  exact ⟨P, fun k => W (e k), disjointed (fun k => W (e k)), fun _ => projDegree J A, fun k => s (e k), hP,
    fun k => ⟨hWo _, MeasurableSet.disjointed (fun i => (hWo _).measurableSet) k, disjointed_le _ k, hs _⟩,
    disjoint_disjointed _, hcompl, measure_mono_null hcompl (DiscriminantSheetCover.volume_zero_set P hP),
    fun k => hsW (e k)⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensLeibniz

variable {D : ℕ}

theorem exists_open_contDiffOn (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ 2 f U ∧ ContDiffOn ℝ 2 g U := by
  obtain ⟨U, hP, hU, hzU⟩ :=
    eventually_nhds_iff.mp ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  exact ⟨U, hU, hzU, fun y hy => (hP y hy).1.contDiffWithinAt,
    fun y hy => (hP y hy).2.contDiffWithinAt⟩

theorem contDiffAt_cplx {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 2 (cplx f) z := by
  have h : cplx f = fun y => Complex.ofRealCLM (f y) := by funext y; simp [cplx]
  rw [h]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hf

theorem dzb_cplx_mul (k : Fin D) (f g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx fun x => f x * g x) y = cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
  rw [dzb_cplx_eq_star, dz_cplx_mul k f g y hf hg, dzb_cplx_eq_star, dzb_cplx_eq_star]
  simp [cplx, star_add]

theorem dzb_cplx_sq_half (k : Fin D) (f : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) :
    dzb k (cplx fun x => f x ^ 2 / 2) y = cplx f y * dzb k (cplx f) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_sq_half f y hf]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, cplx]
  push_cast
  ring

theorem hessC_mul (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (fun y => f y * g y) z =
      (f z : ℂ) • hessC g z + (g z : ℂ) • hessC f z + gradMat f g z + gradMat g f z := by
  obtain ⟨U, hU, hzU, hfU, hgU⟩ := exists_open_contDiffOn f g z hf hg
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hfU.mul hgU) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k,
    hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx fun y => f y * g y) =ᶠ[𝓝 z]
      fun y => cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_mul k f g y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hG := (contDiffAt_cplx hg).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  have hG' := differentiableAt_dzb (j := k) (contDiffAt_cplx hg)
  rw [dz_congr hev, dz_add (hF.fun_mul hG') (hG.fun_mul hF'), dz_mul hF hG', dz_mul hG hF']
  simp only [gradMat, cplx]
  ring

theorem hessC_sq_half (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z) :
    hessC (fun y => f y ^ 2 / 2) z = (f z : ℂ) • hessC f z + gradMat f f z := by
  obtain ⟨U, hU, hzU, hfU, -⟩ := exists_open_contDiffOn f f z hf hf
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU ((hfU.pow 2).div_const 2) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k]
  have hev : dzb k (cplx fun y => f y ^ 2 / 2) =ᶠ[𝓝 z] fun y => cplx f y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_sq_half k f y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  rw [dz_congr hev, dz_mul hF hF']
  simp only [gradMat, cplx]
  ring

theorem mdisc_cons_add {n : ℕ} (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (A + A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  simpa using mdisc_cons_smul_add 1 1 A A' B

theorem proof : MaDensLeibniz.Statement := by
  intro D φ f g z hf hg
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, maDens_cons_eq, hessC_mul f g z hf hg]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_add, mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_sq_half f z hf]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_smul_fst]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring

end MaDensLeibniz

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimeGermCanonicalCover.proof (h₁ : PrimeGermPrimitivePresentation.Statement)
    (h₂ : PrimitivePresentationCover.Statement) : PrimeGermCanonicalCover.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, ℓ, N, c, δ, hpres, hδ⟩ := h₁ σ w k p hp hP
  have hδa : AnalyticAt ℂ δ (A w) := hpres.2.1
  have hdiv := hpres.2.2.2.2.2.1
  refine ⟨d, A, ℓ, N, δ, hδa, hδ, ?_, h₂ σ w k p d A ℓ N c δ hp hpres⟩
  intro g hg
  obtain ⟨M, a, ha, h, hh, hev⟩ := hdiv g hg
  exact ⟨M, a, h, ha, hh, hev⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitGoodPoints.proof (hBr : DivisorGeneralPointBranches.Statement)
    (hLim : LelongLimitAtBranches.Statement) (hOrd : LocalOrder.Statement) :
    LelongLimitGoodPoints.Statement := by
  classical
  intro n d J u φ hJ hdim hu hφ
  obtain ⟨I, hI, hIdim, hgood⟩ := hBr n d J u hJ hdim hu
  refine ⟨I, hI, hIdim, fun q hqJ hqu hqI => ?_⟩
  obtain ⟨W, hWm, hqW, hone, hWloc, m, γ, ord, π, hcov, hsl, hmeet, hvan, hbij⟩ :=
    hgood q hqJ hqu hqI
  obtain ⟨N, hN, hlim⟩ :=
    hLim n d J W u q m γ ord π φ hJ hdim hu hWm hqW hφ hWloc hcov hsl hmeet hvan hbij
  have hmult := hOrd n d J W u q m γ ord hJ hdim hu hWm hqW hcov hsl hmeet hvan
  have hclosed : ∀ W' : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet W') := fun W' => by
    have : zeroSet W' = ⋂ p ∈ W', {x : Fin n → ℂ | MvPolynomial.eval x p = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ => isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

  set O := ⋂ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hO : O ∈ 𝓝 q :=
    (Filter.biInter_mem
      ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).sdiff)).2 fun W' hW' =>
      (hclosed W').isOpen_compl.mem_nhds fun h => hW'.2 (hone W' hW'.1 h)
  refine ⟨N ∩ O, Filter.inter_mem hN hO, fun f hf hfc hfN => ?_⟩
  have hL : (∑ᶠ (W' : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W' : ℝ) * varInt W' d f φ) =
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    rw [finsum_eq_single _ W fun W' hne => ?_, finsum_eq_dif, dite_eq_left hWm]
    rw [finsum_eq_dif]
    split_ifs with hW'
    · rw [varInt_eq_zero_of_vanish W' f φ fun x hx => image_eq_zero_of_notMem_tsupport fun hxs =>
        Set.mem_iInter₂.1 (hfN hxs).2 W' ⟨hW', hne⟩ hx, mul_zero]
    · rfl
  rw [hL, hmult]
  exact hlim f hf hfc fun x hx => (hfN hx).1

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchNormalisation.proof (h₀ : BranchGermDimOne.Statement) (h₁ : BranchPlace.Statement)
    (h₂ : SameOrderBranchesMeet.Statement) (h₃ : PlaceHasBranch.Statement)
    (h₄ : OrdDeterminesPlace.Statement) (h₅ : CurveResidueDegree.Statement)
    (h₆ : OrdFiniteNonZeroDivisor.Statement) : BranchNormalisation.Statement := by
  intro n I q m c hrad hm hcov hdisj
  have hdim := h₀ n I q m c hm hcov
  refine ⟨hdim, fun f hf ↦ h₆ n I q f hrad hdim fun P ↦ ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj P
    rw [hb f]
    exact hf b
  choose P hP using fun b ↦ h₁ n I q (c b) hrad hdim

  have hcongr : ∀ Q Q' : MaximalSpectrum (curveNormalisation I q), Q = Q' → ∀ f : MvPolynomial (Fin n) ℂ,
      Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
      Ring.ord (Localization.AtPrime Q'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
    rintro Q _ rfl f
    rfl
  have hinj : Function.Injective P := by
    intro b b' hbb
    by_contra hne
    obtain ⟨x, hx, hxq⟩ := h₂ n I q (c b) (c b') hrad hdim fun f ↦
      (hP b f).symm.trans ((hcongr _ _ hbb f).trans (hP b' f))
    exact hxq (hdisj b b' hne hx)
  have hsurj : Function.Surjective P := by
    intro Q
    obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj Q
    exact ⟨b, h₄ n I q hrad hdim (P b) Q fun f ↦ (hP b f).trans (hb f).symm⟩
  exact ⟨Equiv.ofBijective P ⟨hinj, hsurj⟩, fun b ↦ ⟨h₅ n I q hrad hdim (P b), hP b⟩⟩

end GroundTheory.Heights₂.Heights
end
