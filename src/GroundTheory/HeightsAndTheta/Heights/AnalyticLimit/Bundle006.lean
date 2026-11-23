module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem regChartData_continuousOn_r (R : RegChartData A) : ContinuousOn R.r R.Yo := by
  intro x hx
  obtain ⟨j, hxs, hxW⟩ := R.cover x
  have hW : R.ψ j x ∈ R.W j :=
    R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hxW)))
  have hnd : R.ψ j x ∉ coordDiv (R.S j) :=
    (R.mem_Yo_iff j _ hW).1 (by rw [(R.ψ j).left_inv hxs]; exact hx)
  have hne : ∀ i ∈ R.S j, R.ψ j x i ≠ 0 := fun i hi h0 => hnd ⟨i, hi, h0⟩
  let g : (Fin D → ℂ) → ℝ := fun z => Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have hg : ContinuousAt g (R.ψ j x) := by
    refine (continuousAt_const.add ((R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW))).sub
      (tendsto_finsetSum (R.S j) fun i hi => ?_)
    exact ((continuous_apply i).continuousAt.norm.pow 2).log (pow_pos (norm_pos_iff.2 (hne i hi)) 2).ne'
  have hz : ∀ᶠ z in 𝓝 (R.ψ j x), z ∈ R.W j ∧ z ∉ coordDiv (R.S j) := by
    refine (show ∀ᶠ z in 𝓝 (R.ψ j x), z ∈ R.W j from (R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW).and ?_
    have : ∀ᶠ z in 𝓝 (R.ψ j x), ∀ i ∈ R.S j, z i ≠ 0 := (eventually_all_finset _).2 fun i hi =>
      (continuous_apply i).continuousAt.eventually_ne (hne i hi)
    exact this.mono fun z hz ⟨i, hi, h0⟩ => hz i hi h0
  have hev : R.r =ᶠ[𝓝 x] g ∘ R.ψ j := by
    filter_upwards [((R.ψ j).continuousAt hxs).eventually hz, (R.ψ j).open_source.mem_nhds hxs]
      with y hy hys
    have := R.r_chart j (R.ψ j y) ⟨hy.1, hy.2⟩
    rw [(R.ψ j).left_inv hys] at this
    exact this
  exact ((hg.comp ((R.ψ j).continuousAt hxs)).congr hev.symm).continuousWithinAt

theorem regChartData_C_nonneg (R : RegChartData A) {x : X} (hx : x ∈ R.Yo) : 0 ≤ R.C := by
  by_contra h
  have h1 := R.le_φ x hx
  have h2 := R.φ_le x hx
  have h3 : 0 ≤ Real.log (R.r x) := Real.log_nonneg (R.one_le_r x hx)
  nlinarith

def regChartShift (R : RegChartData A) : RegChartData A :=
  { R with
    r := fun x => R.r x + (Real.exp 1 - 1)
    f := fun j z => R.f j z + (Real.exp 1 - 1)
    f_cont := fun j => (R.f_cont j).add continuousOn_const
    f_bdd := fun j => by
      obtain ⟨B, hB⟩ := R.f_bdd j
      exact ⟨B + |Real.exp 1 - 1|, fun z hz => (abs_add_le _ _).trans (by linarith [hB z hz])⟩
    r_chart := fun j z hz => by rw [R.r_chart j z hz]; ring
    one_le_r := fun x hx => by
      have := R.one_le_r x hx
      have := Real.add_one_le_exp (0 : ℝ)
      rw [Real.exp_zero] at this
      linarith [Real.add_one_le_exp (1 : ℝ)]
    le_φ := fun x hx => by
      have hC := regChartData_C_nonneg R hx
      have h1 := R.one_le_r x hx
      have : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      nlinarith [R.le_φ x hx]
    grad := fun j z hz => by
      have hx : (R.ψ j).symm z ∈ R.Yo := (R.mem_Yo_iff j z hz.1).2 hz.2
      have hC := regChartData_C_nonneg R hx
      have h1 := R.one_le_r _ hx
      have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      refine (R.grad j z hz).trans (mul_le_mul (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) (by linarith) hC) hC)
        (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)) }

theorem tailLogBound_of_le [CompactSpace X] [T2Space X] {Yo : Set X} (hYo : IsOpen Yo)
    {r r' : X → ℝ} (hr : ContinuousOn r Yo) (hle : ∀ x ∈ Yo, r x ≤ r' x) {T : Fin D → LocPot X}
    (hpot : ∀ i, IsPotential A (T i)) (hnn : ∀ i, FormNonneg A Yo (T i)) {CE : ℝ}
    (h : TailLogBound A Yo r' T CE) : TailLogBound A Yo r T CE := by
  intro R₀ hR₀
  obtain ⟨hI, hB⟩ := h R₀ hR₀
  have he : (1 : ℝ) ≤ R₀ := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hR₀
  set gs := (tail Yo r R₀).indicator fun x => Real.log (r x) with hgs
  set gb := (tail Yo r' R₀).indicator fun x => Real.log (r' x) with hgb
  have hg : ∀ x, 0 ≤ gs x ∧ gs x ≤ gb x := by
    intro x
    by_cases hx : x ∈ tail Yo r R₀
    · have hx' : x ∈ tail Yo r' R₀ := ⟨hx.1, hx.2.trans (hle x hx.1)⟩
      rw [hgs, hgb, indicator_of_mem hx, indicator_of_mem hx']
      exact ⟨Real.log_nonneg (he.trans hx.2),
        Real.log_le_log (by linarith [hx.2]) (hle x hx.1)⟩
    · rw [hgs, indicator_of_notMem hx]
      refine ⟨le_rfl, ?_⟩
      by_cases hx' : x ∈ tail Yo r' R₀
      · rw [hgb, indicator_of_mem hx']
        exact Real.log_nonneg (he.trans hx'.2)
      · rw [hgb, indicator_of_notMem hx']
  have hI' : MIntegrable A T gs := by
    intro k K hK hKc
    set U := (A.chart k).target ∩ (A.chart k).symm ⁻¹' Yo with hUdef
    have hU : IsOpen U := (A.chart k).isOpen_inter_preimage_symm hYo
    have hF : ContinuousOn (fun y => r ((A.chart k).symm y)) U :=
      hr.comp ((A.chart k).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2
    set Ms := U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Ici R₀ with hMs
    have hM : MeasurableSet Ms := by
      have ho := hF.isOpen_inter_preimage hU (isOpen_Iio (a := R₀))
      have e : Ms = U \ (U ∩ (fun y => r ((A.chart k).symm y)) ⁻¹' Iio R₀) := by
        ext y
        constructor
        · rintro ⟨hu, hge⟩
          exact ⟨hu, fun hm => (not_le.2 (show r ((A.chart k).symm y) < R₀ from hm.2)) (show R₀ ≤ r ((A.chart k).symm y) from hge)⟩
        · rintro ⟨hu, hn⟩
          exact ⟨hu, show R₀ ≤ r ((A.chart k).symm y) from not_lt.1 fun hlt => hn ⟨hu, hlt⟩⟩
      rw [e]
      exact hU.measurableSet.diff ho.measurableSet
    have hlog : ContinuousOn (fun y => Real.log (r ((A.chart k).symm y))) Ms :=
      (hF.mono inter_subset_left).log fun y hy => by
        have : R₀ ≤ r ((A.chart k).symm y) := hy.2
        exact (by linarith : (0 : ℝ) < _).ne'
    have hcongr : (fun y => gs ((A.chart k).symm y)) =ᵐ[volume.restrict K]
        Ms.indicator fun y => Real.log (r ((A.chart k).symm y)) := by
      refine ae_restrict_of_forall_mem hKc.measurableSet fun y hy => ?_
      have hyt := hK hy
      by_cases hc : (A.chart k).symm y ∈ tail Yo r R₀
      · show (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _
        rw [indicator_of_mem hc, indicator_of_mem (show y ∈ Ms from ⟨⟨hyt, hc.1⟩, hc.2⟩)]
      · show (tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart k).symm y) = _
        rw [indicator_of_notMem hc,
          indicator_of_notMem (show y ∉ Ms from fun hm => hc ⟨hm.1.2, hm.2⟩)]
    have hmeas : AEStronglyMeasurable
        (fun y => gs ((A.chart k).symm y) * ReciprocityTheory.AnForm.M.locDens A T k y) (volume.restrict K) :=
      (((aestronglyMeasurable_indicator_iff hM).2 (hlog.aestronglyMeasurable hM)).congr
        hcongr.symm).mul
        (((ReciprocityTheory.AnForm.M.locDensCont A T hpot k).mono hK).aestronglyMeasurable hKc.measurableSet)
    refine (hI k K hK hKc).norm.mono' hmeas (ae_of_all _ fun y => ?_)
    simp only [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Real.norm_of_nonneg (hg _).1, Real.norm_of_nonneg ((hg _).1.trans (hg _).2)]
    exact (hg _).2
  refine ⟨hI', ?_⟩
  have hlin := ReciprocityTheory.AnForm.M.mIntLinear A T hpot (-1) gs gb hI' hI
  have h0 := SystemIndependence.mInt_nonneg_on A Yo T hpot hnn (fun x => -1 * gs x + gb x)
    (fun x => by linarith [hg x]) (fun x hx => by
      rw [hgs, hgb, indicator_of_notMem (fun (h : x ∈ tail Yo r R₀) => hx h.1),
        indicator_of_notMem (fun (h : x ∈ tail Yo r' R₀) => hx h.1)]
      ring)
  linarith

theorem ListTailLogSmooth.proof (h : ListTailLog.Statement) : ListTailLogSmooth.Statement := by
  intro D X _ _ _ A R Om C₁
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨CE, hCE⟩ := h D A (regChartShift R) (fun x hx => by
    show Real.exp 1 ≤ R.r x + (Real.exp 1 - 1)
    linarith [R.one_le_r x hx]) Om (max C₁ 0)
  refine ⟨CE, fun th u hT => ?_⟩
  have hpot : ∀ i, IsPotential A (potForm (th i) (u i)) := fun i =>
    ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (hT i).1.th_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hT i).2)
  refine tailLogBound_of_le R.isOpen_Yo (regChartData_continuousOn_r R)
    (r' := (regChartShift R).r) (fun x _ => by show R.r x ≤ R.r x + (Real.exp 1 - 1); linarith)
    hpot (fun i => (hT i).1.nonneg) (hCE th u fun j => ?_)
  exact { (hT j).1 with
    le_u := fun x hx => by
      have h1 := R.one_le_r x hx
      have hl : Real.log (R.r x) ≤ Real.log (R.r x + (Real.exp 1 - 1)) :=
        Real.log_le_log (by linarith) (by linarith)
      have h0 := Real.log_nonneg h1
      have hu := (hT j).1.le_u x hx
      show -(max C₁ 0 * Real.log (R.r x + (Real.exp 1 - 1))) ≤ u j x
      nlinarith [le_max_left C₁ 0, le_max_right C₁ 0] }

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Topology
open scoped ComplexOrder Matrix
open ReciprocityTheory.AnForm (levi hessC maDens)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

theorem ListMonoDens.proof : ListMonoDens.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn j y hy hyY
  set p := (A.chart j).symm y with hp

  set f : Fin D → (Fin D → ℂ) → ℝ := fun i y' => (th i).φ p ((A.chart j).symm y') with hf
  set v : Fin D → (Fin D → ℂ) → ℝ := fun i y' => u i ((A.chart j).symm y') with hv
  set o : (Fin D → ℂ) → ℝ := fun y' => Om.φ p ((A.chart j).symm y') with ho
  have hfC : ∀ i, ContDiffAt ℝ 2 (f i) y := fun i =>
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two (hth i) p j hy ((th i).mem_U p)
  have hoC : ContDiffAt ℝ 2 o y :=
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two hOm p j hy (Om.mem_U p)
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    (A.chart j).isOpen_inter_preimage_symm hYo
  have hvC : ∀ i, ContDiffAt ℝ 2 (v i) y := fun i =>
    ((hu i j).contDiffAt (hopen.mem_nhds ⟨hy, hyY⟩)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  have hgC : ∀ i, ContDiffAt ℝ 2 (fun y' => o y' + (-1) * f i y') y := fun i =>
    hoC.add (contDiffAt_const.mul (hfC i))

  have hA : ∀ i, (hessC (fun y' => f i y' + v i y') y).PosSemidef := fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y ((hfC i).add (hvC i)) fun w =>
      hnn i p j y ⟨hy, hyY, (th i).mem_U p, Set.mem_univ _⟩ w

  have hB : ∀ i, (hessC (fun y' => o y' + (-1) * f i y') y).PosSemidef := fun i => by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y (hgC i)
      fun w => ?_
    rw [ReciprocityTheory.AnForm.levi_add_smul (-1) hoC (hfC i) w]
    have h := hle i p j y ⟨hy, ⟨⟨Set.mem_univ _, (th i).mem_U p⟩, Om.mem_U p⟩⟩ w
    have h' : 1 * levi (f i) y w ≤ 1 * levi o y w := h
    linarith

  have hsum : ∀ i, hessC (fun y' => o y' + v i y') y =
      hessC (fun y' => f i y' + v i y') y + hessC (fun y' => o y' + (-1) * f i y') y := fun i => by
    rw [← ReciprocityTheory.AnForm.A.hessC_add _ _ y ((hfC i).add (hvC i))
      (hgC i)]
    congr 1
    funext y'
    ring
  have e1 : locDens A (fun i => potForm (th i) (u i)) j y =
      maDens (fun i y' => f i y' + v i y') y := rfl
  have e2 : locDens A (fun i => potForm Om (u i)) j y = maDens (fun i y' => o y' + v i y') y := rfl
  rw [e1, e2]
  refine ⟨ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y hA, ?_⟩
  unfold maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _ hA fun i => ?_) (by positivity)
  simpa [hsum i] using hB i

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul levi_re_analytic)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential potSmoothAt)

theorem ListMonoRaise.proof : ListMonoRaise.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn x k y hy w
  set s := (A.chart k).symm with hs
  have hyt : y ∈ (A.chart k).target := hy.1
  have hyYo : s y ∈ Yo := hy.2.1
  have hyOx : s y ∈ Om.U x := hy.2.2.1

  have hadd : ∀ {f g : (Fin D → ℂ) → ℝ}, ContDiffAt ℝ 2 f y → ContDiffAt ℝ 2 g y →
      levi (fun v => f v + g v) y w = levi f y w + levi g y w := by
    intro f g hf hg
    simpa using levi_add_smul 1 hf hg w

  have hus : ContDiffAt ℝ 2 (u ∘ s) y :=
    ((hu k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm hYo).mem_nhds ⟨hyt, hyYo⟩)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hths : ContDiffAt ℝ 2 (th.φ (s y) ∘ s) y := potSmoothAt A th hth (s y) k ⟨hyt, th.mem_U _⟩
  have hOms : ContDiffAt ℝ 2 (Om.φ (s y) ∘ s) y := potSmoothAt A Om hOm (s y) k ⟨hyt, Om.mem_U _⟩

  obtain ⟨W, hWo, hpW, G, hG, hGeq⟩ := hOm.2 (s y) x (s y) ⟨Om.mem_U _, hyOx⟩
  have hGa : AnalyticAt ℂ (G ∘ s) y := hG k y ⟨hyt, hpW⟩
  have hGre : ContDiffAt ℝ 2 (fun v => ((G ∘ s) v).re) y :=
    (Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars.contDiffAt (n := 2)))
  have hVo : IsOpen ((A.chart k).target ∩ s ⁻¹' (W ∩ Om.U (s y) ∩ Om.U x)) :=
    (A.chart k).isOpen_inter_preimage_symm ((hWo.inter (Om.isOpen_U _)).inter (Om.isOpen_U x))
  have hgerm : (potForm Om u).φ x ∘ s =ᶠ[𝓝 y]
      fun v => ((Om.φ (s y) ∘ s) v + (u ∘ s) v) + (-1) * ((G ∘ s) v).re := by
    filter_upwards [hVo.mem_nhds ⟨hyt, ⟨hpW, Om.mem_U _⟩, hyOx⟩] with v hv
    have := hGeq (s v) hv.2
    show Om.φ x (s v) + u (s v) = (Om.φ (s y) (s v) + u (s v)) + (-1) * (G (s v)).re
    linarith
  have hΩ : levi ((potForm Om u).φ x ∘ s) y w = levi (Om.φ (s y) ∘ s) y w + levi (u ∘ s) y w := by
    rw [levi_congr hgerm, levi_add_smul (-1) (hOms.add hus) hGre, levi_re_analytic hGa,
      hadd hOms hus]
    ring

  have h1 := hle (s y) k y ⟨hyt, ⟨trivial, th.mem_U _⟩, Om.mem_U _⟩ w
  have h2 := hnn (s y) k y ⟨hyt, hyYo, th.mem_U _, trivial⟩ w
  have hT : levi ((potForm th u).φ (s y) ∘ s) y w = levi (th.φ (s y) ∘ s) y w + levi (u ∘ s) y w :=
    hadd hths hus
  rw [hT] at h2
  rw [hΩ]
  linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassError.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1), ∀ δ, 0 < δ → ∃ τ, 0 < τ ∧ ∀ t₀ t, 0 < t → t ≤ t₀ → t₀ ≤ τ →
      S.ell₀ ≤ ell t₀ → S.errW a ha t₀ t ≤ δ ∧ S.errDiv a ha t₀ t ≤ δ

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassReplace.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∃ Cκ, 0 ≤ Cκ ∧ ∀ (a : ℕ) (ha : a < D + 1) (t₀ : ℝ), 0 < t₀ → S.ell₀ ≤ ell t₀ →
      ∃ K, 0 ≤ K ∧ ∀ ε t, 0 < ε → ε ≤ 1 → 0 < t → t ≤ t₀ →
        S.plTerm a ha ε t ≤ K * S.J a ε t + Cκ * S.errW a ha t₀ t + 2 * S.errDiv a ha t₀ t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassStep.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1) (ε t : ℝ), 0 < ε → 0 < t → S.ell₀ ≤ ell t →
      S.J (a + 1) ε t ≤ S.J a ε t + S.plTerm a ha ε t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassZero.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ t, S.J 0 ε t ≤ η

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
