module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle091
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem continuousOn_of_holoOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨k, hk⟩ := A.cover y
  have hz : A.chart k y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k y) ∈ V
      rw [(A.chart k).left_inv hk]; exact hy⟩
  have h1 : ContinuousAt (g ∘ (A.chart k).symm) (A.chart k y) := (h k _ hz).continuousAt
  have h2 : ContinuousAt (A.chart k) y := (A.chart k).continuousAt hk
  have h3 : ContinuousAt ((g ∘ (A.chart k).symm) ∘ (A.chart k)) y := ContinuousAt.comp h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with u hu
  simp [(A.chart k).left_inv hu]

theorem holoOn_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y} {h : Y → X}
    (hh : HoloMap B A h) {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) fun y => g (h y) := by
  intro c z hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart c).symm z))
  have h1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart c).symm) z := hh.2 c k z ⟨hz.1, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart c).symm) z) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k (h ((B.chart c).symm z))) ∈ V
      rw [(A.chart k).left_inv hk]; exact hz.2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (h ∘ (B.chart c).symm) z :=
    hh.1.continuousAt.comp ((B.chart c).continuousAt_symm hz.1)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  have hu' : h ((B.chart c).symm u) ∈ (A.chart k).source := hu
  simp only [Function.comp]
  rw [(A.chart k).left_inv hu']

theorem holoOn_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_const (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_inv {V : Set X} {f : X → ℂ} (h : A.HoloOn V f) (h0 : ∀ y ∈ V, f y ≠ 0) :
    A.HoloOn V fun y => (f y)⁻¹ := fun k z hz => (h k z hz).inv (h0 _ hz.2)

theorem holoOn_det {σ : Type} [Fintype σ] [DecidableEq σ] {V : Set X} {m : X → Matrix σ σ ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => (m y).det := by
  simp only [Matrix.det_apply']
  exact holoOn_sum _ fun s => holoOn_mul (holoOn_const _ _) (holoOn_prod _ fun a => h _ _)

theorem holoOn_minorIJ {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e]
    exact holoOn_det fun a b => h _ _
  · simp only [dif_neg e]
    exact holoOn_const _ _

theorem holoOn_detFac {N j : ℕ} (i : Fin N) {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => detFac j i (m y) := by
  unfold detFac
  refine holoOn_mul ?_ ?_
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _

theorem exists_log {S : Set X} (hS : IsOpen S) {f : X → ℂ} (h : A.HoloOn S f) {y : X} (hy : y ∈ S)
    (h0 : f y ≠ 0) : ∃ W', IsOpen W' ∧ y ∈ W' ∧ W' ⊆ S ∧ ∃ G : X → ℂ, A.HoloOn W' G ∧
      ∀ z ∈ W', (G z).re = Real.log ‖f z‖ := by
  refine ⟨S ∩ (fun z => f z * (f y)⁻¹) ⁻¹' Complex.slitPlane,
    ((continuousOn_of_holoOn hS h).mul continuousOn_const).isOpen_inter_preimage hS Complex.isOpen_slitPlane,
    ⟨hy, ?_⟩, Set.inter_subset_left, fun z => Complex.log (f z * (f y)⁻¹) + Real.log ‖f y‖,
    fun k u hu => ?_, fun z hz => ?_⟩
  · simp [mul_inv_cancel₀ h0]
  · exact (AnalyticAt.clog ((h k u ⟨hu.1, hu.2.1⟩).mul analyticAt_const) hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.2)
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel]

end Holo

theorem minorIJ_one_self {N : ℕ} (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_ne_zero' {N j : ℕ} (hj : j ≤ N) (i : Fin N) {H : Matrix (Fin N) (Fin N) ℂ}
    (hb : IsBlockDiag j H) (hd : H.det ≠ 0) : detFac j i H ≠ 0 := by
  have hu : IsUnit H.det := hd.isUnit
  have h1 := ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.2 H H⁻¹ hb (hb.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu] at h1
  have h2 : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold detFac
    split_ifs <;> simp [minorIJ_one_self]
  intro h0
  rw [h2, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem isPshOn_stepPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS x c y₀ hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hU : (R.A.chart c).symm y₀ ∈ R.U x := hyU.1
  set y₁ := (R.A.chart c).symm y₀ with hy₁
  obtain ⟨W, l, H, D, hW, hyW, hWU, hWO, hHh, hHd, hDh, hDn, hEq⟩ := hS x y₁ hU
  have hb : pr y₁ ∉ bdry BM.s := hyb
  obtain ⟨V, Pi, hV, hVo, hPh, hPg⟩ := BM.period l (pr y₁) ⟨hWO y₁ hyW, hb⟩
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary _ _ _ _ _ BM.sec
  let V' : Set R.X := W ∩ pr ⁻¹' (V ∩ (bdry BM.s)ᶜ)
  have hV'o : IsOpen V' := hW.inter ((hVo.inter hcl.isOpen_compl).preimage hp.1)
  have hyV' : y₁ ∈ V' := ⟨hyW, hV, hb⟩
  let g : R.X → Matrix (Fin N) (Fin N) ℂ := fun y' => Pi p.1 (pr y') * H y'
  have hVW : V' ⊆ W := Set.inter_subset_left
  have hVP : V' ⊆ pr ⁻¹' V := fun y' h => h.2.1
  have hPh' : ∀ a b, R.A.HoloOn V' fun y' => Pi p.1 (pr y') a b := fun a b =>
    holoOn_mono (holoOn_comp hp (hPh p.1 a b)) hVP
  have hHh' : ∀ a b, R.A.HoloOn V' fun y' => H y' a b := fun a b =>
    holoOn_mono (hHh a b) hVW
  have hgh : ∀ a b, R.A.HoloOn V' fun y' => g y' a b := fun a b => by
    simp only [g, Matrix.mul_apply]
    exact holoOn_sum _ fun c' => holoOn_mul (hPh' a c') (hHh' c' b)
  have hstep : ∀ (i : Fin N), ∀ y' ∈ V', InFlagDomain N j (g y') ∧
      stepPot N j i (g y') = blockPot j i (BM.G l p.1 (pr y')) (H y') + Real.log ‖detFac j i (H y')‖ := by
    intro i y' hy'
    have hG := BM.G_pos l p.1 (pr y') ⟨hWO y' hy'.1, hy'.2.2⟩
    exact GlobalTheory.T.flag_potential_block_decomposition N j i _ _ _ M.j_le (hPg p.1 _ hy'.2.1) hG.1 hG.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  have hdn : ∀ y' ∈ V', detFac j p.2 (H y') ≠ 0 := fun y' hy' =>
    detFac_ne_zero' M.j_le p.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  let f : R.X → ℂ := fun y' => D y' * (detFac j p.2 (H y'))⁻¹
  have hfh : R.A.HoloOn V' f :=
    holoOn_mul (holoOn_mono hDh hVW) (holoOn_inv (holoOn_detFac p.2 hHh') hdn)
  have hf0 : ∀ y' ∈ V', f y' ≠ 0 := fun y' hy' =>
    mul_ne_zero (hDn y' hy'.1) (inv_ne_zero (hdn y' hy'))
  obtain ⟨V'', hV''o, hyV'', hV''s, Gh, hGh, hGre⟩ := exists_log hV'o hfh hyV' (hf0 _ hyV')
  let Φl : R.X → ℝ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)).φ x
  let pot : Unit × Fin N → LocPot R.X := fun q =>
    LocPot.ofFun (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y'))
  have hPC : IsPeriodChart R.A j pot y₁ V'' (fun _ => g) := by
    refine ⟨hV''o, hyV'', fun _ a b => holoOn_mono (hgh a b) hV''s,
      fun _ y' hy' => (hstep p.2 y' (hV''s hy')).1, fun q => ?_⟩
    by_cases hq : q.2 = p.2
    · refine ⟨Gh, hGh, fun y' hy' => ?_⟩
      have hy3 := hV''s hy'
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + (Gh y').re
      rw [if_pos hq, hq, hGre y' hy', (hstep p.2 y' hy3).2]
      have hE := hEq y' hy3.1 hy3.2.2
      have hl : Real.log ‖f y'‖ = Real.log ‖D y'‖ - Real.log ‖detFac j p.2 (H y')‖ := by
        simp only [f]
        rw [norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 (hDn y' hy3.1))
          (inv_ne_zero (norm_ne_zero_iff.2 (hdn y' hy3))), Real.log_inv, sub_eq_add_neg]
      rw [hl]
      show Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' = _
      rw [hE]
      ring
    · refine ⟨fun _ => 0, holoOn_const _ _, fun y' _ => ?_⟩
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + ((0 : ℂ)).re
      rw [if_neg hq]
      simp
  have hsrc : y₁ ∈ (R.A.chart c).source := (R.A.chart c).map_target hyt
  obtain ⟨Lm, -, hL, -⟩ := GlobalTheory.T.period_chart_potential_levi_form e R.X R.A Unit N j M.j_le pot y₁ V'' (fun _ => g) hPC c hsrc
  have hlev := hL ((), p.2) w
  have e1 : (R.A.chart c) y₁ = y₀ := (R.A.chart c).right_inv hyt
  have e2 : (pot ((), p.2)).φ y₁ = Φl := by
    show (if p.2 = p.2 then Φl else fun y' => stepPot N j p.2 (g y')) = Φl
    rw [if_pos rfl]
  rw [e2, e1] at hlev
  show 0 ≤ levi (Φl ∘ (R.A.chart c).symm) y₀ w
  rw [hlev]
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

end GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure OrbitChart (P : Ideal (MRing ι)) (e : ℕ) where

  D : Set (Fin e → ℂ)
  isOpen_D : IsOpen D

  φ : (Fin e → ℂ) → (Σ k, ι k) → ℂ
  holo : ∀ p, AnalyticOnNhd ℂ (fun w => φ w p) D
  mem : ∀ w ∈ D, φ w ∈ mcPts P

  O : Set ((Σ k, ι k) → ℂ)
  O_open : ∃ O' : Set ((Σ k, ι k) → ℂ), IsOpen O' ∧ O = O' ∩ mcPts P
  O_orbit : ∀ z ∈ O, ∀ z' ∈ mcPts P, SameOrbit z' z → z' ∈ O

  ρ : ((Σ k, ι k) → ℂ) → Fin e → ℂ
  ρ_cont : ContinuousOn ρ O
  ρ_orbit : ∀ z ∈ O, ∀ z' ∈ O, SameOrbit z' z → ρ z' = ρ z
  φ_mem_O : ∀ w ∈ D, φ w ∈ O
  ρ_φ : ∀ w ∈ D, ρ (φ w) = w
  ρ_mem : ∀ z ∈ O, ρ z ∈ D
  φ_ρ : ∀ z ∈ O, SameOrbit (φ (ρ z)) z
  immersion : ∀ w ∈ D, ∀ p : (k : K) → ι k, (∀ k, φ w ⟨k, p k⟩ ≠ 0) →
    (fderiv ℂ (fun w' => affCoord p (φ w')) w).ker = ⊥

end Orbit

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def stepOf (N j : ℕ) (c : Fin N) : Fin N :=
  ⟨if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j, by
    have := c.2
    split_ifs <;> omega⟩

def lowMat (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then c ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

def flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if e : ∃ p, M.blk p = some q.1 then
    ∑ I, valAt M.x (F.u q I) zb * minorIJ (h e.choose.1) I (stepCols N j e.choose.2)
  else zb ⟨⟨q.1, fun p hp => e ⟨p, hp⟩⟩, q.2⟩

def sqZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (k₀ : K) (τ : Ψ) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagZ M F zb h ⟨k, m⟩
  | ⟨none, m⟩ => flagZ M F zb (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩

def pluck (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (k : K)
    (z : (Σ k, ι k) → ℂ) (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * z ⟨k, m⟩

def twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (J : Finset (Fin N)) : ℂ :=
  ∑ I ∈ Finset.univ.filter (IsStepRows N j i), minorIJ g J I * pluck M F zb k z I

def lowRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ' : Ψ) (a' b' : Fin N) : ℂ :=
  (M.blk (τ', stepOf N j b')).elim 0 fun k =>
    twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (insert a' ((stepCols N j (stepOf N j b')).erase b')) /
      twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (stepCols N j (stepOf N j b'))

def baseOf (M : FlagModel y Ψ N j) (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (fstPt k₀ z)

abbrev wP (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) :
    Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (fun o : Option K => ι (o.getD k₀))) :=
  mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)

section Param

variable {n e : ℕ} {Λ : Type}

def wB (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def wL (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr (Sum.inl q)))

def wT (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : ℂ := w (ε (Sum.inr (Sum.inr ())))

def wD (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | wB ε w ∈ V}

end Param

variable {n e : ℕ}

def wH (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (w : Fin e → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := h τ' * lowMat (wL ε w) τ'

def wPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (k₀ : K) (τ : Ψ) (ca cb : Fin N)
    (w : Fin e → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ :=
  sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)

def IsBaseChart (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk)
    (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) : Prop :=
  IsOpen V ∧ V ⊆ (Rb.A.chart kb).target ∧ (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
    (∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl w)) V) ∧
    ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, bl w ⟨k, F.c k⟩ = 1) ∧ M.GoodAt F (mCoordIdeal (bl w)) ∧
      SameOrbit (Rb.lift ((Rb.A.chart kb).symm w) ((Rb.A.chart kb).symm w)) (bl w)

def IsWCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N)
    (d : ℕ) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (b : ℕ) = a + 1 ∧ ((b : ℕ) < j ∨ j ≤ (a : ℕ)) ∧ M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧
    (cb : ℕ) = ca + 1 ∧ IsArithVar (mCoordIdeal y) (d + 2) ∧ M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0

def wO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) :
    Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ) :=
  {z | z ∈ mcPts (wP M τ a k₀ ca cb) ∧ r (baseOf M k₀ z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (baseOf M k₀ z)) ∈ V ∧
    (∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0) ∧
    twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0}

def wRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (baseOf M k₀ z)) l
  | Sum.inr (Sum.inl q) => lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2
  | Sum.inr (Sum.inr _) =>
    lowRead M F (baseOf M k₀ z) h (sndPt k₀ z) τ cb ca - lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) τ cb ca

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem fsHerm_isSmoothHerm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) :=
  fun _ _ _ _ a => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm a

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | exact GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem varieties_over_rat_arith_contract : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P :=
  @PositivityTheory.Xgp.t_contract

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.points_integral_unique_embedding : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass | exact GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem _root_.GlobalTheory.T.weight_threshold_limit_coefficients : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.tower_seq | exact GlobalTheory.CompanionTheory.Ar.Small.tower_seq | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.tower_seq <;> assumption)
end
