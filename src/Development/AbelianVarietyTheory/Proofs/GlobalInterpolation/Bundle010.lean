module

import Lemmata.MiscLemmasM.Imports
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

section

namespace GlobalTheory.EqOneOfPowerClose

open Finset

theorem eq_one_of_pow_close {u : ℂ} (h : ∀ n : ℕ, ‖u ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    u = (1 : ℂ) := by
  apply Bl.SecondBlockLemmaN.goal1 <;> assumption

end GlobalTheory.EqOneOfPowerClose
end

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise

namespace GlobalTheory.QuotientHaar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem measurable_translate (g : G) : Measurable (fun h : H => g * (h : G)) :=
  (continuous_const.mul continuous_subtype_val).measurable

noncomputable def cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] : G ⧸ H → Measure G :=
  Quotient.lift (fun g : G => ν.map (fun h : H => g * (h : G))) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h1 := map_mul_left_eq_self ν (⟨a⁻¹ * b, hab'⟩ : H)
    beta_reduce
    conv_lhs => rw [← h1]
    rw [Measure.map_map (measurable_translate H a) (measurable_const_mul _)]
    congr 1
    funext h
    simp [← mul_assoc])

theorem cosetMeasure_mk (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) :
    cosetMeasure H ν (g : G ⧸ H) = ν.map (fun h : H => g * (h : G)) := rfl

theorem cosetMeasure_apply (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) {s : Set G}
    (hs : MeasurableSet s) :
    cosetMeasure H ν (g : G ⧸ H) s = ν ((fun h : H => g * (h : G)) ⁻¹' s) := by
  rw [cosetMeasure_mk, Measure.map_apply (measurable_translate H g) hs]

theorem lintegral_cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞}
    (hf : Measurable f) (q : G ⧸ H) :
    ∫⁻ x, f x ∂(cosetMeasure H ν q) = fibreIntegral H ν f q := by
  induction q using QuotientGroup.induction_on with
  | H g => rw [cosetMeasure_mk, lintegral_map hf (measurable_translate H g), fibreIntegral_mk]

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem cosetMeasure_lt_top (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure]
    (q : G ⧸ H) {K : Set G} (hK : IsCompact K) : cosetMeasure H ν q K < ⊤ := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cosetMeasure_apply H ν g hK.measurableSet]
    have h1 : IsCompact ((fun x : G => g * x) ⁻¹' K) :=
      (Homeomorph.mulLeft g).isCompact_preimage.mpr hK
    exact (hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1).measure_lt_top

theorem measurable_cosetMeasure_open (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {U : Set G}
    (hU : IsOpen U) : Measurable (fun q : G ⧸ H => cosetMeasure H ν q U) := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : ν.Regular := inferInstance
  refine measurable_of_Ioi fun c => IsOpen.measurableSet ?_
  rw [← (QuotientGroup.isQuotientMap_mk H).isOpen_preimage, isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν g hU.measurableSet] at hg
  have hO : IsOpen ((fun h : H => g * (h : G)) ⁻¹' U) :=
    hU.preimage (continuous_const.mul continuous_subtype_val)
  obtain ⟨K, hKU, hK, hc⟩ := hO.exists_lt_isCompact hg
  have hev : ∀ᶠ x in nhds g, ∀ h ∈ K, x * (h : G) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun h hh => ?_
    have hcont : Continuous (fun p : G × H => p.1 * (p.2 : G)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (hU.mem_nhds (hKU hh))
  filter_upwards [hev] with x hx
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν x hU.measurableSet]
  exact hc.trans_le (measure_mono fun h hh => hx h hh)

theorem measurable_cosetMeasure (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] :
    Measurable (cosetMeasure H ν) := by
  let K := CompactExhaustion.choice G
  have hres : ∀ n, Measurable (fun q => (cosetMeasure H ν q).restrict (interior (K n))) := by
    intro n
    haveI : ∀ q, IsFiniteMeasure ((cosetMeasure H ν q).restrict (interior (K n))) := fun q =>
      isFiniteMeasure_restrict.mpr ((measure_mono interior_subset).trans_lt
        (cosetMeasure_lt_top H hH ν q (K.isCompact n))).ne
    have key : ∀ s : Set G, IsOpen s →
        Measurable fun q => (cosetMeasure H ν q).restrict (interior (K n)) s := by
      intro s hs
      simp only [Measure.restrict_apply hs.measurableSet]
      exact measurable_cosetMeasure_open H hH ν (hs.inter isOpen_interior)
    exact Measurable.measure_of_isPiSystem (S := {s : Set G | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen key (key _ isOpen_univ)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hmono : Monotone fun n => s ∩ interior (K n) := fun a b hab =>
    Set.inter_subset_inter_right _ (interior_mono (K.subset hab))
  have hun : ⋃ n, s ∩ interior (K n) = s := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, h, K.subset_interior_succ n hn⟩
  have : (fun q => cosetMeasure H ν q s) =
      fun q => ⨆ n, (cosetMeasure H ν q).restrict (interior (K n)) s := by
    funext q
    simp only [Measure.restrict_apply hs]
    rw [← hmono.measure_iUnion, hun]
  rw [this]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hres n)

theorem measurable_fibreIntegral (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {f : G → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreIntegral H ν f) := by
  have : fibreIntegral H ν f = fun q => ∫⁻ x, f x ∂(cosetMeasure H ν q) :=
    funext fun q => (lintegral_cosetMeasure H ν hf q).symm
  rw [this]
  exact (Measure.measurable_lintegral hf).comp (measurable_cosetMeasure H hH ν)

theorem quotientFormula_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H)) :
    QuotientFormula H (μ.bind (cosetMeasure H ν)) ν μ := by
  intro f hf
  refine ⟨measurable_fibreIntegral H hH ν hf, ?_⟩
  rw [Measure.lintegral_bind (measurable_cosetMeasure H hH ν).aemeasurable hf.aemeasurable]
  exact lintegral_congr fun q => lintegral_cosetMeasure H ν hf q

theorem isHaarMeasure_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) : (μ.bind (cosetMeasure H ν)).IsHaarMeasure := by
  haveI := hμ.finiteOnCompacts
  haveI := hμ.invariant
  have hm := measurable_cosetMeasure H hH ν
  haveI hfin : IsFiniteMeasureOnCompacts (μ.bind (cosetMeasure H ν)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.bind_apply hK.measurableSet hm.aemeasurable]
    have hC : ν (Subtype.val ⁻¹' (K⁻¹ * K)) < ⊤ :=
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)).measure_lt_top
    have hπ : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K) :=
      hK.image QuotientGroup.continuous_mk
    have hle : ∀ q, cosetMeasure H ν q K ≤ ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
        (fun _ => ν (Subtype.val ⁻¹' (K⁻¹ * K))) q := by
      intro q
      by_cases hq : q ∈ (QuotientGroup.mk : G → G ⧸ H) '' K
      · rw [Set.indicator_of_mem hq]
        obtain ⟨k, hk, rfl⟩ := hq
        rw [cosetMeasure_apply H ν k hK.measurableSet]
        refine measure_mono fun h hh => ?_
        exact ⟨k⁻¹, Set.inv_mem_inv.mpr hk, k * h, hh, by simp⟩
      · induction q using QuotientGroup.induction_on with
        | H g =>
          rw [cosetMeasure_apply H ν g hK.measurableSet]
          have : (fun h : H => g * (h : G)) ⁻¹' K = ∅ :=
            Set.eq_empty_of_forall_notMem fun h hh => hq ⟨g * h, hh, by simp⟩
          simp [this]
    refine (lintegral_mono hle).trans_lt ((lintegral_indicator_const_le _ _).trans_lt ?_)
    exact ENNReal.mul_lt_top hC hπ.measure_lt_top
  haveI hinv : (μ.bind (cosetMeasure H ν)).IsMulLeftInvariant := by
    refine (forall_measure_preimage_mul_iff _).mp fun a s hs => ?_
    rw [Measure.bind_apply hs hm.aemeasurable,
      Measure.bind_apply (measurable_const_mul a hs) hm.aemeasurable]
    have h1 : Measurable fun q => cosetMeasure H ν q s := (Measure.measurable_coe hs).comp hm
    have h2 := (measurePreserving_smul a μ).lintegral_comp h1
    rw [← h2]
    refine lintegral_congr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      change _ = cosetMeasure H ν ((a * g : G) : G ⧸ H) s
      rw [cosetMeasure_apply H ν g (measurable_const_mul a hs), cosetMeasure_apply H ν _ hs]
      congr 1
      ext h
      simp [mul_assoc]
  have hne : μ.bind (cosetMeasure H ν) ≠ 0 := by
    intro h0
    have h1 : μ.bind (cosetMeasure H ν) Set.univ = ν Set.univ * μ Set.univ := by
      rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable, ← lintegral_const]
      refine lintegral_congr fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H g => rw [cosetMeasure_apply H ν g MeasurableSet.univ, Set.preimage_univ]
    rw [h0] at h1
    exact mul_ne_zero (isOpen_univ.measure_ne_zero ν Set.univ_nonempty)
      (Measure.measure_univ_ne_zero.mpr hμ.ne_zero) h1.symm
  haveI : IsLocallyFiniteMeasure (μ.bind (cosetMeasure H ν)) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : NeZero (μ.bind (cosetMeasure H ν)) := ⟨hne⟩
  haveI : (μ.bind (cosetMeasure H ν)).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_regular
  exact {}

end GlobalTheory.QuotientHaar

namespace GlobalTheory.QuotientHaar

theorem existsUnique_haar_of_invariantRadon : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH ν _ μ hμ
  refine ⟨μ.bind (cosetMeasure H ν),
    ⟨isHaarMeasure_bind H hH ν μ hμ, quotientFormula_bind H hH ν μ⟩, fun dg hdg => ?_⟩
  ext s hs
  have hf : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (hdg.2 _ hf).2,
    (quotientFormula_bind H hH ν μ _ hf).2]

end GlobalTheory.QuotientHaar
end

section

namespace GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation

open GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

theorem card_fiber_mul_card_stab {G : Type} [Group G] (Γ U K : Subgroup G) (hUK : U ≤ K)
    (hfree : ∀ x : G, stab Γ U x = ⊥) (y : G) :
    Nat.card {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y} * Nat.card (stab Γ K y) =
      U.relIndex K := by
  have hex : ∀ d : {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y},
      ∃ k : K, DoubleCoset.mk Γ U (y * k) = d.1 := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, k, hk, h⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 hd.symm
    refine ⟨⟨k, hk⟩, ?_⟩
    refine Eq.trans ?_ (DoubleCoset.out_eq' (H := Γ) (K := U) d)
    exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨a, ha, 1, U.one_mem, by rw [h]; group⟩
  choose κ hκ using hex
  rw [← Nat.card_prod, Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ((⟨y⁻¹ * p.2.1 * y, ((mem_stab Γ K y _).1 p.2.2).2⟩ * κ p.1 : K) :
      K ⧸ U.subgroupOf K)) ⟨?_, ?_⟩)
  · rintro ⟨d, s, hs⟩ ⟨e, t, ht⟩ h
    have hs' := ((mem_stab Γ K y _).1 hs).1
    have ht' := ((mem_stab Γ K y _).1 ht).1
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have hde : d = e := by
      apply Subtype.ext
      rw [← hκ d, ← hκ e]
      exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨t⁻¹ * s, Γ.mul_mem (Γ.inv_mem ht') hs', _, h1, by group⟩
    subst hde
    have h2 : s⁻¹ * t ∈ stab Γ U (y * κ d) := by
      refine (mem_stab Γ U _ _).2 ⟨Γ.mul_mem (Γ.inv_mem hs') ht', ?_⟩
      convert h1 using 1
      group
    rw [hfree, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hd : DoubleCoset.mk Γ K (DoubleCoset.mk Γ U (y * k)).out = DoubleCoset.mk Γ K y := by
        obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1
          (DoubleCoset.out_eq' (H := Γ) (K := U) (DoubleCoset.mk Γ U (y * k))).symm
        symm
        exact (@DoubleCoset.eq _ _ Γ K _ _).2
          ⟨a, ha, k * u, K.mul_mem k.2 (hUK hu), h.trans (by group)⟩
      obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1 (hκ ⟨_, hd⟩)
      have hk : y⁻¹ * a * y = k * u⁻¹ * (κ ⟨_, hd⟩ : G)⁻¹ := by
        generalize (κ ⟨_, hd⟩ : G) = m at h ⊢
        rw [show (k : G) = y⁻¹ * (y * k) by group, h]
        group
      have hs : a ∈ stab Γ K y := by
        refine (mem_stab Γ K y _).2 ⟨ha, ?_⟩
        rw [hk]
        exact K.mul_mem (K.mul_mem k.2 (K.inv_mem (hUK hu))) (K.inv_mem (κ _).2)
      refine ⟨⟨⟨_, hd⟩, ⟨a, hs⟩⟩, QuotientGroup.eq.2 ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hk]
      convert hu using 1
      group

theorem doubleCosetCount : DoubleCosetCount := by
  intro G _ Γ U K hUK hfi _ hfin hfree rep hrep
  have hne : U.relIndex K ≠ 0 := hfi.index_ne_zero
  let π : DoubleCoset.Quotient (Γ : Set G) (U : Set G) →
      DoubleCoset.Quotient (Γ : Set G) (K : Set G) := fun d => DoubleCoset.mk Γ K d.out
  have key : ∀ c, Nat.card {d // π d = c} * Nat.card (stab Γ K (rep c)) = U.relIndex K := by
    intro c
    have := card_fiber_mul_card_stab Γ U K hUK hfree (rep c)
    rw [hrep c] at this
    exact this
  have : ∀ c, Finite {d // π d = c} := fun c =>
    Nat.finite_of_card_ne_zero fun h => hne (by rw [← key c, h, zero_mul])
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv π), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : (Nat.card (stab Γ K (rep c)) : ℚ) ≠ 0 := by
    have := hfin (rep c)
    exact_mod_cast Nat.card_pos.ne'
  rw [← key c]
  push_cast
  field_simp

end GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
end

section

open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

theorem fibOf_compl_fibre : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  intro K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ q hq hh U s hs t
  obtain ⟨hUo, hUc, h1, hmul, hinv, hn, hsc, hsq⟩ := hs
  by_cases ht : t = 0
  · subst ht; rw [fibOf_zero]; rfl
  have hm : Measurable (fun x : V => s (t / q x) • x) := by
    have h1 : Measurable (fun x : V => s (t / q x)) :=
      hsc.measurable.comp (measurable_const.div hq.measurable)
    exact h1.smul measurable_id
  have hA : MeasurableSet (q ⁻¹' {t})ᶜ :=
    ((isClosed_singleton.preimage hq).measurableSet).compl
  rw [fibOf_ne _ _ _ _ _ ht, Measure.smul_apply, Measure.map_apply hm hA,
    Measure.restrict_apply (hm hA)]
  convert smul_zero _
  convert measure_empty (μ := μ)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, u, hu, hx2⟩
  apply hx1
  have hu0 : u ≠ 0 := by
    intro h
    have := hn u hu
    rw [h] at this
    simp at this
  have hx2' : q x = t * u := by simpa using hx2.symm
  have h3 : t / q x = u⁻¹ := by rw [hx2']; field_simp
  show q (s (t / q x) • x) = t
  rw [hh, h3, hsq _ (hinv u hu), hx2']
  field_simp

end GlobalTheory.QuadFibre
end

section

open MeasureTheory Topology

namespace GlobalTheory.QuadFibre

theorem exists_local_sqrt_near_one (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : ∃ (N : Set K) (g : K → K), IsOpen N ∧ (1 : K) ∈ N ∧ ContinuousOn g N ∧
      ∀ u ∈ N, g u ^ 2 = u := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  refine ⟨e.target, e.symm, e.open_target, ?_, e.continuousOn_symm, fun u hu => ?_⟩
  · simpa using hf.image_mem_toOpenPartialHomeomorph_target
  · have := e.right_inv hu
    rwa [he] at this

theorem exists_isSqrtOn (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] (h2 : (2 : K) ≠ 0) : ∃ (U : Set K) (s : K → K), IsSqrtOn U s := by
  classical
  obtain ⟨N, g, hN, h1, hg, hsq⟩ := exists_local_sqrt_near_one K h2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hN 1 h1
  set r : ℝ := min (ε / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : Metric.closedBall (1 : K) r ⊆ N :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hclopen : IsClopen (Metric.closedBall (1 : K) r) := ⟨Metric.isClosed_closedBall, hopen⟩
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  refine ⟨Metric.closedBall 1 r, (Metric.closedBall (1 : K) r).piecewise g (fun _ => 1), hopen,
    isCompact_closedBall _ _, Metric.mem_closedBall_self hr0.le, ?_, ?_, hnorm, ?_, ?_⟩
  · intro a ha b hb
    have hna := hnorm a ha
    rw [mem_closedBall_iff_norm] at ha hb ⊢
    have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rwa [norm_mul, hna, one_mul]
  · intro a ha
    have hna := hnorm a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hna
    rw [mem_closedBall_iff_norm] at ha ⊢
    have : a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by field_simp; ring
    rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul]
  · refine continuous_piecewise ?_ ?_ continuousOn_const
    · simp [hclopen.frontier_eq]
    · rw [Metric.isClosed_closedBall.closure_eq]
      exact hg.mono hsub
  · intro a ha
    rw [Set.piecewise_eq_of_mem _ _ _ ha]
    exact hsq a (hsub ha)

end GlobalTheory.QuadFibre
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  first | exact @GlobalTheory.weighted_fejer_positivity | exact GlobalTheory.weighted_fejer_positivity | (intros; apply GlobalTheory.weighted_fejer_positivity <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)), (∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) → ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧ LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) = f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  first | exact @GlobalTheory.linearEquiv_descends_of_preserves_image | exact GlobalTheory.linearEquiv_descends_of_preserves_image | (intros; apply GlobalTheory.linearEquiv_descends_of_preserves_image <;> assumption)
end
