module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollA
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  integralWith)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

section Defs

variable {W : Type} [TopologicalSpace W]

def secNorm (L : LocPot W) (s : W → W → ℂ) (x : W) : ℝ := ‖s x x‖ * Real.exp (-L.φ x x)

def greenEp (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) (x : W) : ℝ :=
  Real.log (1 + ε / secNorm L s x ^ 2)

def kappaEp (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) : LocPot W :=
  LocPot.rsmul 2 L + LocPot.ofFun fun x => Real.log (secNorm L s x ^ 2 + ε)

def curForms {D : ℕ} (th : Fin (D + 1) → LocPot W) (u : Fin (D + 1) → ℝ → W → ℝ) (t : ℝ) :
    Fin (D + 1) → LocPot W :=
  fun i => potForm (th i) (u i t)

def mixedForms {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (b : ℕ) :
    Fin (D + 1) → LocPot W :=
  fun i => if (i : ℕ) < b then T i else Om

def restForms {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (b : ℕ) : Fin D → LocPot W :=
  fun i => if (i : ℕ) < b then T i.castSucc else Om

def restrictForms {D : ℕ} (S : Set W) (Φ : Fin D → LocPot W) : Fin D → LocPot S :=
  fun i => (Φ i).pullback Subtype.val continuous_subtype_val

end Defs

structure UIData (D : ℕ) (W : Type) [TopologicalSpace W] where

  A : FinHolAtlas (D + 1) W

  Om : KaehlerForm A

  L : LocPot W

  s : W → W → ℂ

  nc : ℕ

  mult : Fin nc → ℕ

  comp : Fin nc → Set W

  B : ∀ k, FinHolAtlas D (comp k)
  L_pot : IsPotential A L
  s_sec : IsSection A L s
  s_snc : IsSNC A L s mult comp
  B_holo : ∀ k, HoloMap (B k) A Subtype.val

  Yo : Set W
  Yo_open : IsOpen Yo
  bd_analytic : A.IsAnalyticSubset Yoᶜ
  bd_interior : interior Yoᶜ = ∅
  bdComp_analytic : ∀ k, (B k).IsAnalyticSubset (Subtype.val ⁻¹' Yo)ᶜ
  bdComp_interior : ∀ k, interior ((Subtype.val ⁻¹' Yo : Set (comp k))ᶜ) = ∅

  r : W → ℝ

  th : Fin (D + 1) → LocPot W

  u : Fin (D + 1) → ℝ → W → ℝ

  lim : Fin (D + 1) → W → ℝ

  C : ℝ

  C₁ : ℝ

  ell₀ : ℝ

  CE : ℝ
  form : ∀ a t, 0 < t → ell₀ ≤ ell t → IsSmoothPotForm A Yo r Om C₁ (th a) (u a t)
  lim_le : ∀ a t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ Yo, lim a x ≤ u a t x
  near : ∀ a t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ Yo, r x ≤ ell t →
    u a t x ≤ lim a x + t ^ (1 / 3 : ℝ) + errE C t
  mono : ∀ a t t₀, 0 < t → t ≤ t₀ → ell₀ ≤ ell t₀ → ∀ x, u a t x ≤ u a t₀ x + C * errE C t₀
  tail : ∀ b, b ≤ D → ∀ t, 0 < t → ell₀ ≤ ell t →
    TailLogBound A Yo r (mixedForms Om.pot (curForms th u t) b) CE
  tailComp : ∀ k b, b ≤ D → ∀ t, 0 < t → ell₀ ≤ ell t →
    TailLogBound (B k) (Subtype.val ⁻¹' Yo) (r ∘ Subtype.val)
      (restrictForms (comp k) (restForms Om.pot (curForms th u t) b)) CE

namespace UIData

variable {D : ℕ} {W : Type} [TopologicalSpace W] (S : UIData D W)

def T (t : ℝ) : Fin (D + 1) → LocPot W := curForms S.th S.u t

def green (ε : ℝ) : W → ℝ := greenEp S.L S.s ε

def J (a : ℕ) (ε t : ℝ) : ℝ := mInt S.A (mixedForms S.Om.pot (S.T t) a) (S.green ε)

def rest (a : ℕ) (t : ℝ) : Fin D → LocPot W := restForms S.Om.pot (S.T t) a

def divInt (Φ : Fin D → LocPot W) (g : W → ℝ) : ℝ :=
  ∑ k, (S.mult k : ℝ) * mInt (S.B k) (restrictForms (S.comp k) Φ) (g ∘ Subtype.val)

def plTerm (a : ℕ) (ha : a < D + 1) (ε t : ℝ) : ℝ :=
  mInt S.A (Fin.cons (kappaEp S.L S.s ε) (S.rest a t)) (S.u ⟨a, ha⟩ t) -
    2 * S.divInt (S.rest a t) (S.u ⟨a, ha⟩ t)

def gap (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : W → ℝ :=
  fun x => S.u ⟨a, ha⟩ t₀ x + S.C * errE S.C t₀ - S.u ⟨a, ha⟩ t x

def errW (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : ℝ :=
  mInt S.A (mixedForms S.Om.pot (S.T t) a) (S.gap a ha t₀ t)

def errDiv (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : ℝ :=
  S.divInt (S.rest a t) (S.gap a ha t₀ t)

end UIData

def UniformIntegrability.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∃ t₁, 0 < t₁ ∧ ∀ ε t, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ →
      S.ell₀ ≤ ell t → mInt S.A (S.T t) (S.green ε) ≤ η

section Inhabitant

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isPlurisubharmonic projLine_isHolomorphicSection projLine_isSimpleNormalCrossing ptAtlas)
open OnePoint

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax Mollifier)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errE errorWithLinear ell)

noncomputable section

section C2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendstoUniformlyOn_finset_biUnion {α β ι κ : Type*} [UniformSpace β] {F : κ → α → β}
    {f : α → β} {p : Filter κ} (T : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ T, TendstoUniformlyOn F f p (S i)) : TendstoUniformlyOn F f p (⋃ i ∈ T, S i) := by
  intro u hu
  filter_upwards [(eventually_all_finset T).2 fun i hi => h i hi u hu] with n hn x hx
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 hx
  exact hn i hi x hx

theorem TendstoC2On.congr_open {F G : ℝ → E → ℝ} {f : E → ℝ} {L U : Set E} (hU : IsOpen U)
    (hLU : L ⊆ U) (hFG : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ U, F t y = G t y) (h : TendstoC2On G f L) :
    TendstoC2On F f L := by
  have e0 : ∀ t, (∀ y ∈ U, F t y = G t y) → ∀ y ∈ U, F t =ᶠ[𝓝 y] G t :=
    fun t ht y hy => Filter.eventually_of_mem (hU.mem_nhds hy) ht
  refine ⟨h.1.congr ?_, h.2.1.congr ?_, h.2.2.congr ?_⟩
  · filter_upwards [hFG] with t ht y hy
    exact (ht y (hLU hy)).symm
  · filter_upwards [hFG] with t ht y hy
    exact (e0 t ht y (hLU hy)).fderiv_eq.symm
  · filter_upwards [hFG] with t ht y hy
    have h' : fderiv ℝ (F t) =ᶠ[𝓝 y] fderiv ℝ (G t) :=
      Filter.eventually_of_mem (hU.mem_nhds (hLU hy)) fun z hz => (e0 t ht z hz).fderiv_eq
    exact h'.fderiv_eq.symm

end C2

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

namespace ArgumentConvergenceLemmas

open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)

noncomputable section

theorem molli_contDiffAt {D : ℕ} (ρ : Mollifier D) {P : Set (Fin D → ℂ)} (hP : IsOpen P)
    {u : (Fin D → ℂ) → ℝ} (hu : ContinuousOn u P) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink P ε) : ContDiffAt ℝ ∞ (molli ρ ε u) z := by
  obtain ⟨δ, hδ, hδP⟩ := ReciprocityTheory.AnForm.A.exists_thick hP hε.le hz
  have hi : Integrable ((closedBall z (ε + δ)).indicator u) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).2
      ((hu.mono hδP).integrableOn_compact (isCompact_closedBall z (ε + δ)))
  have hg := (ReciprocityTheory.AnForm.A.scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (ReciprocityTheory.AnForm.A.scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ hε (C := closedBall z (ε + δ))
    (closedBall_subset_closedBall' (by linarith)), convolution_def]
  rfl

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_fderiv_eq (g : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ = ‖iteratedFDeriv ℝ 2 g y‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_sub_eq {a b : E → ℝ} {V : Set E} (hV : IsOpen V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiffOn ℝ 2 b V) {z : E} (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ 0 (fun y => a y - b y) z‖ = ‖a z - b z‖ ∧
      ‖iteratedFDeriv ℝ 1 (fun y => a y - b y) z‖ = ‖fderiv ℝ a z - fderiv ℝ b z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => a y - b y) z‖ =
        ‖fderiv ℝ (fderiv ℝ a) z - fderiv ℝ (fderiv ℝ b) z‖ := by
  have da : DifferentiableAt ℝ a z :=
    (ha.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  have db : DifferentiableAt ℝ b z :=
    (hb.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  refine ⟨norm_iteratedFDeriv_zero, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_one, fderiv_fun_sub da db]
  · rw [← norm_fderiv_fderiv_eq, fderiv2_sub_of_contDiffOn hV ha hb hz]

theorem norm_iteratedFDeriv_comp_le_of_isOpen {g : F → G} {f : E → F} {s : Set E} {t : Set F}
    (hs : IsOpen s) (ht : IsOpen t) (hg : ContDiffOn ℝ 2 g t) (hf : ContDiffOn ℝ 2 f s)
    (hst : MapsTo f s t) {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ 2) {C d : ℝ}
    (hC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ d ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * d ^ n := by
  have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  rw [← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le (hg.of_le hn') (hf.of_le hn') le_rfl ht.uniqueDiffOn
    hs.uniqueDiffOn hst hx (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx)]
    exact hC i (hi.trans hn)
  · rw [iteratedFDerivWithin_of_isOpen i hs hx]
    exact hD i hi1 (hi.trans hn)

theorem exists_bound_iteratedFDeriv {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ B : ℝ, ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
  have h : ∀ i : ℕ, i ≤ 2 → ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := fun i hi =>
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hs (by exact_mod_cast hi)).mono hKs)
  obtain ⟨B0, h0⟩ := h 0 (by norm_num)
  obtain ⟨B1, h1⟩ := h 1 (by norm_num)
  obtain ⟨B2, h2⟩ := h 2 le_rfl
  refine ⟨max B0 (max B1 B2), fun i hi y hy => ?_⟩
  interval_cases i
  · exact (h0 y hy).trans (le_max_left _ _)
  · exact (h1 y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y hy).trans ((le_max_right _ _).trans (le_max_right _ _))

end Calculus

theorem tendstoUniformlyOn_of_norm_le {Y α : Type*} [SeminormedAddCommGroup α] {F : ℝ → Y → α}
    {f : Y → α} {K : Set Y} {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ K, ‖F t y - f y‖ ≤ β t) :
    TendstoUniformlyOn F f (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [h, hβ.eventually (gt_mem_nhds he)] with t ht hβt y hy
  rw [dist_comm, dist_eq_norm]
  exact (ht y hy).trans_lt hβt

end

end ArgumentConvergenceLemmas

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable ChartPartition integralWith
  locDens chartPartMeasure integral_chartPartMeasure isFiniteMeasure_chartPartMeasure existsPartition
  locDensCont mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem tendsto_ell : Tendsto ell (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

section Signed

variable {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

def tvMeasure (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : Measure X :=
  ∑ j, (chartPartMeasure A (existsPartition A).some Φ 1 j +
    chartPartMeasure A (existsPartition A).some Φ (-1) j)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem chart_weight_continuousOn (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
  have h := (P.smooth j j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact continuousOn_const.mul (h.mul (locDensCont A Φ hΦ j))


omit [CompactSpace X] [T2Space X] in
theorem integrableOn_chart_of_part (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ)
    (hg : Measurable g) (hi : Integrable g (chartPartMeasure A P Φ s j)) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hwc := chart_weight_continuousOn A P Φ hΦ s j
  have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hd : AEMeasurable (fun y => ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hwc.aemeasurable hT)
  have hlt : ∀ᵐ y ∂(volume.restrict (A.chart j).target), ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hsymm' : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hfun : (fun y => (ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y))).toReal • (g ∘ (A.chart j).symm) y) = fun y => g ((A.chart j).symm y) *
        max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
    funext y
    rw [ENNReal.toReal_ofReal', smul_eq_mul, Function.comp_apply, mul_comm]
  unfold chartPartMeasure at hi
  rw [integrable_map_measure hg.aestronglyMeasurable hsymm',
    integrable_withDensity_iff_integrable_smul₀' hd hlt, hfun] at hi
  exact hi

theorem abs_mInt_le (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (f : X → ℝ) (hf : Measurable f) (hfi : MIntegrable A Φ f) :
    Integrable f (tvMeasure A Φ) ∧ |mInt A Φ f| ≤ ∫ x, |f x| ∂tvMeasure A Φ := by
  have h1 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ 1 j f hf hfi
  have h2 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ (-1) j f hf hfi
  have hI : ∀ j, Integrable f (chartPartMeasure A (existsPartition A).some Φ 1 j +
      chartPartMeasure A (existsPartition A).some Φ (-1) j) :=
    fun j => (h1 j).1.add_measure (h2 j).1
  have hm : mInt A Φ f = ∑ j, (∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ 1 j -
      ∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ (-1) j) := by
    rw [mInt, dite_eq_left (existsPartition A)]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(h1 j).2, (h2 j).2, ← integral_sub
      (integrableOn_chart_of_part A _ Φ hΦ 1 j f hf (h1 j).1)
      (integrableOn_chart_of_part A _ Φ hΦ (-1) j f hf (h2 j).1)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    ring
  refine ⟨integrable_finsetSum_measure.2 fun j _ => hI j, ?_⟩
  rw [hm, tvMeasure, integral_finsetSum_measure fun j _ => (hI j).abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [integral_add_measure (h1 j).1.abs (h2 j).1.abs]
  exact (abs_sub _ _).trans (add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs)

end Signed

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)

@[instance_reducible] def projectiveLineBorel : MeasurableSpace (OnePoint ℂ) := borel _

attribute [local instance] projectiveLineBorel

theorem projectiveLine_borelSpace : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

attribute [local instance] projectiveLine_borelSpace

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
