module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle392
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle441
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle002
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle219

@[expose] public section

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.CutEnergy

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem wdb_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) : ∃ K : ℝ, 0 ≤ K ∧ ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K := by
  set e := A.chart (C.idx a)
  have hg : ContDiffOn ℝ ∞ (fun w => ((χ (e.symm w) : ℝ) : ℂ)) e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ (C.idx a))
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
    hg.fderiv_of_isOpen e.open_target (by simp)
  have hc : ContinuousOn (fun v => ∑ j, ‖wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ)) v‖ ^ 2)
      e.target := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    have : ContDiffOn ℝ ∞ (wdb n j (fun w => ((χ (e.symm w) : ℝ) : ℂ))) e.target :=
      ((hd.clm_apply contDiffOn_const).add
        (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2
    exact (this.continuousOn.norm).pow 2
  obtain ⟨K, hK⟩ := (isCompact_closedBall (C.c a) (C.r a)).exists_bound_of_continuousOn
    (hc.mono (C.sub a))
  refine ⟨max K 0, le_max_right _ _, fun v hv => ?_⟩
  have := hK v hv
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _))

theorem pt_bound (A : WeightedAtlas n Y ι La) (C : Cover A) (χ : Y → ℝ) (hχ : A.SmoothFn χ)
    (a : Fin C.m) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ v ∈ closedBall (C.c a) (C.r a),
      (∑ j, ‖wdb n j (fun w => ((χ ((A.chart (C.idx a)).symm w) : ℝ) : ℂ)) v‖ ^ 2) ≤ K)
    (la : La) (W Z : Set Y) (h : ι → Y → ℂ) (hW : IsOpen W) (hsupp : tsupport χ ⊆ W)
    (hsec : A.IsSecOn (A.kap + la) W h)
    (hZ : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) (v : V n) (hv : v ∈ ball (C.c a) (C.r a)) :
    ENNReal.ofReal ((∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) (C.idx a) ∘
        (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal K * ((Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y))
          ((A.chart (C.idx a)).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
  set i := C.idx a
  set e := A.chart i
  set y := e.symm v
  set g : V n → ℂ := fun w => ((χ (e.symm w) : ℝ) : ℂ)
  have hvt : v ∈ e.target := C.sub a (ball_subset_closedBall hv)
  have hys : y ∈ e.source := e.map_target hvt
  have hgs : ContDiffOn ℝ ∞ g e.target := Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ i)
  have hgd : DifferentiableAt ℝ g v :=
    (hgs.differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hvt)

  have hzero : y ∉ Z ∩ W → ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = 0 := by
    intro hy j
    by_cases hyW : y ∈ W
    · have hyZ : y ∉ Z := fun hz => hy ⟨hz, hyW⟩
      have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hyW⟩
      have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
        (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
      have hg0 : wdb n j g v = 0 := by
        have hev : g =ᶠ[𝓝 v] fun _ => ((χ y : ℝ) : ℂ) := by
          have := (e.continuousAt_symm hvt).eventually (hZ y hyZ)
          filter_upwards [this] with w hw
          simp only [g]; rw [hw]
        rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
        exact wdb_of_differentiableAt (differentiableAt_const _)
      have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
        rfl
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH, hg0]
      ring
    · have hyt : y ∉ tsupport χ := fun ht => hyW (hsupp ht)
      have h0 := (notMem_tsupport_iff_eventuallyEq.mp hyt)
      have hev : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        have := (e.continuousAt_symm hvt).eventually h0
        filter_upwards [this] with w hw
        simp only [Function.comp_apply, Pi.zero_apply] at hw ⊢
        rw [hw]; simp
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr hev]
      exact wdb_of_differentiableAt (differentiableAt_const _)
  by_cases hy : y ∈ Z ∩ W
  · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
    have hvU : v ∈ e.target ∩ e.symm ⁻¹' W := ⟨hvt, hy.2⟩
    have hH : DifferentiableAt ℂ (h i ∘ e.symm) v :=
      (hsec.1 i).differentiableAt (hU.mem_nhds hvU)
    have hfun : ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) = fun w => g w * (h i ∘ e.symm) w :=
      rfl
    have hw : ∀ j, wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v = wdb n j g v * h i y := by
      intro j
      rw [hfun, wdb_mul hgd (hH.restrictScalars ℝ), wdb_of_differentiableAt hH]
      simp [y]
    have hsum : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) =
        ‖h i y‖ ^ 2 * ∑ j, ‖wdb n j g v‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw j, norm_mul, mul_pow]; ring
    have hnsq := api_nsq_eq A hsec hys hy.2
    rw [A.ph_add _ _ i y hys] at hnsq
    have hexp : Real.exp (-A.ph la i y) =
        Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul (by unfold WeightedAtlas.nsq; positivity),
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hsum, ← hnsq, hexp]
    have hS := hK v (ball_subset_closedBall hv)
    have h1 : 0 ≤ ‖h i y‖ ^ 2 * (Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
        Real.exp (A.ph A.kap i y)) := by positivity
    calc ‖h i y‖ ^ 2 * (∑ j, ‖wdb n j g v‖ ^ 2) *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))
        = (∑ j, ‖wdb n j g v‖ ^ 2) * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) := by ring
      _ ≤ K * (‖h i y‖ ^ 2 *
          (Real.exp (-(A.ph A.kap i y + A.ph la i y)) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_right hS h1
      _ = K * (‖h i y‖ ^ 2 * Real.exp (-(A.ph A.kap i y + A.ph la i y)) *
          Real.exp (A.ph A.kap i y)) := by ring
  · have : (∑ j, ‖wdb n j ((fun i y => (χ y : ℂ) * h i y) i ∘ e.symm) v‖ ^ 2) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hzero hy j]; simp
    rw [this, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

end

end GlobalTheory.CutEnergy

namespace GlobalTheory.CutEnergy

theorem dbarEnergy_cutoff_mul_section_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  intro n Y _ _ _ _ _ ι La _ A C χ hχ
  choose K hK0 hK using fun a => wdb_bound A C χ hχ a
  refine ⟨∑ a, K a, Finset.sum_nonneg fun a _ => hK0 a, ?_⟩
  intro la W Z h hW hsupp hsec hZm hZ
  set G : Y → ℝ≥0∞ := (Z ∩ W).indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) with hGdef
  have hGm : Measurable G := by
    classical
    have h1 : Measurable (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) := by
      rw [← Set.piecewise_eq_indicator]
      exact ContinuousOn.measurable_piecewise
        (ENNReal.continuous_ofReal.comp_continuousOn (api_nsq_contOn A hW hsec))
        continuousOn_const hW.measurableSet
    have : G = Z.indicator (W.indicator fun y => ENNReal.ofReal (A.nsq (A.kap + la) h y)) :=
      (Set.indicator_indicator _ _ _).symm
    rw [this]; exact h1.indicator hZm
  have hint : ∫⁻ y, G y ∂A.mu = ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu :=
    lintegral_indicator (hZm.inter hW.measurableSet) _
  rw [← hint, ENNReal.ofReal_sum_of_nonneg (fun a _ => hK0 a), Finset.sum_mul]
  unfold n1
  refine Finset.sum_le_sum fun a _ => ?_
  calc _ ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (K a) *
          (G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
        setLIntegral_mono' measurableSet_ball fun v hv =>
          pt_bound A C χ hχ a (K a) (hK0 a) (hK a) la W Z h hW hsupp hsec hZ v hv
    _ = ENNReal.ofReal (K a) * ∫⁻ v in ball (C.c a) (C.r a), G ((A.chart (C.idx a)).symm v) *
            ENNReal.ofReal (Real.exp (A.ph A.kap (C.idx a) ((A.chart (C.idx a)).symm v))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
          gcongr
          exact A.aap_lintegral_chart_le _ G hGm _ (ball_subset_closedBall.trans (C.sub a))

end GlobalTheory.CutEnergy
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.tateIso_ev_eq_at_lcm_level : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
  (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
  (∀ a, J.ev l.A a = J'.ev l.A a) →
  (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
  ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  first | exact @GlobalTheory.LowDat.tateIso_ev_lcm_eq | exact GlobalTheory.LowDat.tateIso_ev_lcm_eq | (intros; apply GlobalTheory.LowDat.tateIso_ev_lcm_eq <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def GtPtAct {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O) (g g' : GtPtF D F) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (DegPre.cF D F χ) g.b).left)) (g'.s χ)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.range_genericPoint_stalk_subset_of_denseOpen : ∀ {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S] [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ s : S, Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆ Set.range j := by
  first | exact @GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range | exact GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range | (intros; apply GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_point_mem_translates' : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens), (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧ (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  first | exact @GlobalTheory.AlgClosedFibre.exists_point_mem_translates | exact GlobalTheory.AlgClosedFibre.exists_point_mem_translates | (intros; apply GlobalTheory.AlgClosedFibre.exists_point_mem_translates <;> assumption)
end

section

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_pow_eq_mul_of_quadraticBound_normalLocal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (X : Type) [AddCommGroup X] (h h' : X →+ X) (C : ℕ), (∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y) → ∀ N : ℕ, C + 1 ≤ N → ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  first | exact @GlobalTheory.exists_pow_eq_mul_of_quadratic_bound | exact GlobalTheory.exists_pow_eq_mul_of_quadratic_bound | (intros; apply GlobalTheory.exists_pow_eq_mul_of_quadratic_bound <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.fromSpecStalk_comp_eq_of_agree_on_closedThickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G), (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → ∀ x : G.left, G.hom x = closedPoint R → G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by
  first | exact @GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq | exact GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq | (intros; apply GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_glue_spec_complete_localRing_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  first | exact @GlobalTheory.LocalThickGlue.exists_glue | exact GlobalTheory.LocalThickGlue.exists_glue | (intros; apply GlobalTheory.LocalThickGlue.exists_glue <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
open scoped ComplexConjugate
open scoped Matrix

namespace GlobalTheory.MajCols

theorem hermC_comb_right {E : Type} [Field E] {r p : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) (k : Fin p → ℂ) (u : Fin p → Fin r → ℂ) :
    hermC τ G v (∑ c, k c • u c) = ∑ c, conj (k c) * hermC τ G v (u c) := by

  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
  Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem hermC_comb_left {E : Type} [Field E] {r p : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) (k : Fin p → ℂ) (u : Fin p → Fin r → ℂ) :
    hermC τ G (∑ c, k c • u c) v = ∑ c, k c * hermC τ G (u c) v := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem quad_change {p : ℕ} (A B D : Matrix (Fin p) (Fin p) ℂ) (hB : B.det ≠ 0) (hD : D.det ≠ 0)
    (w w' : Fin p → ℂ) :
    (w ᵥ* D) ⬝ᵥ ((B * A * D)⁻¹ *ᵥ (B *ᵥ w')) = w ⬝ᵥ (A⁻¹ *ᵥ w') := by
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hD' : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  congr 2
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hD', Matrix.nonsing_inv_mul_cancel_right _ _ hB']

theorem sum_eq_dot {p : ℕ} (M : Matrix (Fin p) (Fin p) ℂ) (w w' : Fin p → ℂ) :
    ∑ a, ∑ b, w a * M a b * w' b = w ⬝ᵥ (M *ᵥ w') := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem maj_eq_of_cols :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x' y : Frame X.Ψ r)
    (τ : X.Ψ) (C : Matrix (Fin X.p0) (Fin X.p0) ℂ), C.det ≠ 0 → (X.gramPos y τ).det ≠ 0 →
    (∀ a : Fin X.p0, col (mat x' τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, C c a • col (mat y τ) (Fin.castLE X.p0_le c)) →
    ∀ v : Fin r → ℂ, X.maj x' τ v = X.maj y τ v := by
  intro E _ _ _ r X x' y τ C hC _ hcol v
  set w : Fin X.p0 → ℂ := fun a => hermC τ.1 X.Gm v (col (mat y τ) (Fin.castLE X.p0_le a)) with hw
  have hD : (C.map (starRingEnd ℂ)).det ≠ 0 := by
    have := (starRingEnd ℂ).map_det C
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).mpr hC
  have hB : (Cᵀ).det ≠ 0 := by rwa [Matrix.det_transpose]
  have h1 : (fun a => hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a))) =
      w ᵥ* C.map (starRingEnd ℂ) := by
    funext a
    rw [hcol, hermC_comb_right]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hw]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have h2 : (fun a => conj (hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a)))) =
      Cᵀ *ᵥ fun a => conj (w a) := by
    funext a
    rw [hcol, hermC_comb_right]

    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hw, map_sum, map_mul,
    Complex.conj_conj]
  have h3 : X.gramPos x' τ = Cᵀ * X.gramPos y τ * C.map (starRingEnd ℂ) := by
    ext a b
    simp only [Data.gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply]
    rw [hcol a, hcol b, hermC_comb_right]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hermC_comb_left, mul_comm]
  have key : X.posPart x' τ v = X.posPart y τ v := by
    unfold Data.posPart
    congr 1
    rw [sum_eq_dot (X.gramPos x' τ)⁻¹
        (fun a => hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a)))
        (fun a => conj (hermC τ.1 X.Gm v (col (mat x' τ) (Fin.castLE X.p0_le a)))),
      sum_eq_dot (X.gramPos y τ)⁻¹ w (fun a => conj (w a)), h1, h2, h3,
      quad_change _ _ _ hB hD]
  unfold Data.maj
  rw [key]

end GlobalTheory.MajCols
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 → ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  first | exact @GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero | exact GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero | (intros; apply GlobalTheory.EqCovol.exists_data_of_le_relIndex_ne_zero <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory

theorem span_tangent_of_type : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p d h : ℕ) (ty : Fin d → ZMod h)
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), IsBasis G p ty γ →
    ∀ (t : ZMod h) (w : Fin d → C), (∀ c, ty c ≠ t → w c = 0) →
      w ∈ Submodule.span C (Set.range fun b : {b // ty b = t} => tangent (γ b.1)) := by
  intro C _ v p d h ty G γ hB t w hw
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0 := by
    intro b c hc
    rw [PTb.tangent_eq_lc_zero G p (fun e => (hγ b e).1)]
    exact (hγty b).2 0 c (by simpa using hc)
  set x : Fin d → C := Matrix.vecMul w (PTb.tmat γ)⁻¹ with hx
  have hxw : Matrix.vecMul x (PTb.tmat γ) = w := PTb.vecMul_inv_tmat hdet' w
  have hsupp : ∀ b, ty b ≠ t → x b = 0 :=
    PTb.vecMul_tmat_support ty hdet' ht x t (fun c hc => by rw [hxw]; exact hw c hc)
  have hsum : w = ∑ b, x b • tangent (γ b) := by rw [PTb.sum_smul_tangent, hxw]
  rw [hsum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : ty b = t
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩)
  · rw [hsupp b hb, zero_smul]; exact Submodule.zero_mem _

end GlobalTheory
end
