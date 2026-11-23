module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle002
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.SymmetricChartsCutoffFamily
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def ReHolAt (A : FinHolAtlas e X) (f : X → ℝ) (y₀ : X) : Prop :=
  ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, f z = (G z).re

theorem holoOn_continuousOn {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  apply _root_.GlobalTheory.CompanionTheory.Ar.Giv.SecPot.holoOn_continuousOn' <;> assumption

theorem ReHolAt.congr {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hg : ReHolAt A g y₀)
    (h : f =ᶠ[𝓝 y₀] g) : ReHolAt A f y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hg
  obtain ⟨T, hT, hTo, hyT⟩ := mem_nhds_iff.1 h
  exact ⟨W ∩ T, hW.inter hTo, ⟨hy, hyT⟩, G, fun j u hu => hG j u ⟨hu.1, hu.2.1⟩,
    fun z hz => (hT hz.2).trans (hWG z hz.1)⟩

theorem ReHolAt.add {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y + g y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  obtain ⟨W', hW', hy', G', hG', hWG'⟩ := hg
  refine ⟨W ∩ W', hW.inter hW', ⟨hy, hy'⟩, fun z => G z + G' z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact (hG j u ⟨hu.1, hu.2.1⟩).add (hG' j u ⟨hu.1, hu.2.2⟩)
  · show f z + g z = (G z + G' z).re
    rw [hWG z hz.1, hWG' z hz.2, Complex.add_re]

theorem ReHolAt.const_mul {A : FinHolAtlas e X} {f : X → ℝ} {y₀ : X} (c : ℝ) (hf : ReHolAt A f y₀) :
    ReHolAt A (fun y => c * f y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  refine ⟨W, hW, hy, fun z => (c : ℂ) * G z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact analyticAt_const.mul (hG j u hu)
  · show c * f z = ((c : ℂ) * G z).re
    rw [hWG z hz, Complex.re_ofReal_mul]

theorem ReHolAt.sub {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y - g y) y₀ := by
  refine (hf.add (hg.const_mul (-1))).congr (Eventually.of_forall fun y => ?_)
  show f y - g y = f y + -1 * g y
  ring

theorem ReHolAt.sum {A : FinHolAtlas e X} {J : Type} (s : Finset J) {f : J → X → ℝ} {y₀ : X}
    (hf : ∀ i ∈ s, ReHolAt A (f i) y₀) : ReHolAt A (fun y => ∑ i ∈ s, f i y) y₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j u _ => analyticAt_const, ?_⟩
    intro z _
    simp
  | insert a s ha ih =>
    refine ((hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr (Eventually.of_forall fun y => ?_)
    show ∑ i ∈ insert a s, f i y = f a y + ∑ i ∈ s, f i y
    rw [Finset.sum_insert ha]

theorem reHolAt_log_norm {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} {y₀ : X} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hy : y₀ ∈ W) (h0 : f y₀ ≠ 0) :
    ReHolAt A (fun y => Real.log ‖f y‖) y₀ := by
  have hS : IsOpen {w : ℂ | w / f y₀ ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_id.div_const _)
  have hW' := (holoOn_continuousOn hf).isOpen_inter_preimage hW hS
  refine ⟨_, hW', ⟨hy, ?_⟩, fun z => Complex.log (f z / f y₀) + (Real.log ‖f y₀‖ : ℂ),
    fun j u hu => ?_, fun z hz => ?_⟩
  · show f y₀ / f y₀ ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) u := hf j u ⟨hu.1, hu.2.1⟩
    exact ((h1.div_const (c := f y₀)).clog hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := fun h => by
      have := Complex.slitPlane_ne_zero hz.2
      simp [h] at this
    rw [Complex.add_re, Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0),
      Complex.ofReal_re]
    ring

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsSecOn (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop :=
  (∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧ ∀ p, M.atlas.HoloOn U fun y => s y p

theorem reHolAt_log_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} (hU : IsOpen U) (hU' : IsOpen U') (hs : IsSecOn M U s)
    (hs' : IsSecOn M U' s')
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : ∀ z ∈ mcPts P, 0 < F z) {y₀ : M.Xc} (hy : y₀ ∈ U) (hy' : y₀ ∈ U') :
    ReHolAt M.atlas (fun y => Real.log (F (s' y)) - Real.log (F (s y))) y₀ := by
  classical
  have hz := (hs.1 y₀ hy).1
  have hz' := (hs'.1 y₀ hy').1
  choose i hi using hz.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz _ hz').1 (by rw [(hs.1 y₀ hy).2, (hs'.1 y₀ hy').2])
  have hi' : ∀ k, s' y₀ ⟨k, i k⟩ ≠ 0 := by
    intro k
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)
  have hR : ∀ k ∈ (Finset.univ : Finset K), ReHolAt M.atlas
      (fun y => (a k : ℝ) * (Real.log ‖s' y ⟨k, i k⟩‖ - Real.log ‖s y ⟨k, i k⟩‖)) y₀ := fun k _ =>
    ((reHolAt_log_norm hU' (hs'.2 _) hy' (hi' k)).sub
      (reHolAt_log_norm hU (hs.2 _) hy (hi k))).const_mul _
  refine (ReHolAt.sum Finset.univ hR).congr ?_
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k, s y ⟨k, i k⟩ ≠ 0 := eventually_all.2 fun k =>
    ((holoOn_continuousOn (hs.2 ⟨k, i k⟩)).continuousAt (hU.mem_nhds hy)).eventually_ne (hi k)
  filter_upwards [hU.mem_nhds hy, hU'.mem_nhds hy', hev] with y h1 h2 h3
  have hm := (hs.1 y h1).1
  have hm' := (hs'.1 y h2).1
  obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm _ hm').1 (by rw [(hs.1 y h1).2, (hs'.1 y h2).2])
  have hnc : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  rw [hcy, hF _ hm c hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hnc k))
    (hpos _ hm).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hnc k)), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h4 : torusSmul c (s y) ⟨k, i k⟩ = c k * s y ⟨k, i k⟩ := rfl
  rw [h4, Real.log_zpow, norm_mul, Real.log_mul (hnc k) (norm_ne_zero_iff.2 (h3 k)), add_sub_cancel_right]

theorem hessC_base_eq {M : CxModel P d} {Y : Set M.Xc} (c : ℝ) (B : HermLine ι) (Q : LocPot M.Xc)
    (j : Fin M.atlas.n)
    (hsm : ∀ x, M.atlas.SmoothOn (Q.U x ∩ Y) (Q.φ x)) (hY : IsOpen Y)
    (hsec : ∀ x, ∀ y₀ ∈ Q.U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Q.U x ∩ Y ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧
        (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, Q.φ x y' - (fun z => c * Real.log (B.h z)) (s y') = (G y').re)
    {y : Fin d → ℂ} (hy : y ∈ (M.atlas.chart j).target) (hyY : (M.atlas.chart j).symm y ∈ Y)
    {x₀ : M.Xc} (hx₀ : (M.atlas.chart j).symm y ∈ Q.U x₀) :
    hessC (fun y' => Q.φ ((M.atlas.chart j).symm y) ((M.atlas.chart j).symm y')) y =
      hessC (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) y := by
  set x := (M.atlas.chart j).symm y with hx
  obtain ⟨U₁, hU₁, hx₁, -, s₁, hs₁, hh₁, G₁, hG₁, he₁⟩ := hsec x x ⟨Q.mem_U x, hyY⟩
  obtain ⟨U₂, hU₂, hx₂, -, s₂, hs₂, hh₂, G₂, hG₂, he₂⟩ := hsec x₀ x ⟨hx₀, hyY⟩
  obtain ⟨W, hW, hxW, G₃, hG₃, he₃⟩ :=
    (reHolAt_log_sections (M := M) (F := B.h) (a := B.a) hU₂ hU₁ ⟨hs₂, hh₂⟩ ⟨hs₁, hh₁⟩
      (fun z _ c hc => B.smul c z hc) (fun z hz => B.pos z hz.1) hx₂ hx₁).const_mul c
  have hOo : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm ((hU₁.inter hU₂).inter hW)
  have hyO : y ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W) :=
    ⟨hy, ⟨⟨hx₁, hx₂⟩, hxW⟩⟩
  have h1 : (fun y' => Q.φ x ((M.atlas.chart j).symm y')) =ᶠ[nhds y]
      (fun w => (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) w +
        ((fun w' => G₁ ((M.atlas.chart j).symm w') - G₂ ((M.atlas.chart j).symm w') +
          G₃ ((M.atlas.chart j).symm w')) w).re) := by
    filter_upwards [hOo.mem_nhds hyO] with w hw
    have e1 := he₁ _ hw.2.1.1
    have e2 := he₂ _ hw.2.1.2
    have e3 := he₃ _ hw.2.2
    simp only [Complex.add_re, Complex.sub_re] at *
    linarith
  rw [hessCGerm _ _ _ h1]
  have hopen : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Q.U x₀ ∩ Y)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm ((Q.isOpen_U x₀).inter hY)
  have hsmooth : ContDiffAt ℝ 2 (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) y :=
    ((hsm x₀ j).contDiffAt (hopen.mem_nhds ⟨hy, ⟨hx₀, hyY⟩⟩)).of_le (WithTop.coe_le_coe.2 le_top)
  exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _ hsmooth
    (((hG₁ j y ⟨hy, hx₁⟩).sub (hG₂ j y ⟨hy, hx₂⟩)).add (hG₃ j y ⟨hy, hxW⟩))

end Model

theorem locDens_continuousOn_of_sections : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Y : Set M.Xc) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (j : Fin M.atlas.n), IsOpen Y → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → ContinuousOn (locDens M.atlas Φ j) ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Y) := by
  intro K _ ι _ P n M Y c B Φ j hY hΦs hsec y₀ hy₀
  apply ContinuousAt.continuousWithinAt
  set x₀ := (M.atlas.chart j).symm y₀ with hx₀
  have hVo : IsOpen ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm
      (hY.inter (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U _))
  have hy0V : y₀ ∈ (M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀) :=
    ⟨hy₀.1, hy₀.2, Set.mem_iInter.2 fun i => (Φ i).mem_U _⟩
  have heq : maDens (fun i y' => (Φ i).φ x₀ ((M.atlas.chart j).symm y')) =ᶠ[nhds y₀]
      locDens M.atlas Φ j := by
    filter_upwards [hVo.mem_nhds hy0V] with y hy
    unfold locDens
    refine maDens_congr_hessC _ _ _ fun i => ?_
    exact (hessC_base_eq (c i) (B i) (Φ i) j (hΦs i) hY (hsec i) hy.1 hy.2.1
      (Set.mem_iInter.1 hy.2.2 i)).symm
  refine ContinuousAt.congr ?_ heq
  refine (maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hy0V)
  exact ((hΦs i x₀ j).of_le (WithTop.coe_le_coe.2 le_top)).mono
    fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i, hy.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.intersection_family_defect_formula : RatRStatement → ResBridgeStatement → GoodProjExistsStatement → AvoidStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A B : HermLine ι) (f g : MRing ι) (w : ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → IsLineIso P A.a B.a f g → IsDefectOn P (mcPts P) f g A B w → I P (e + 1) (Fin.snoc L A) - I P (e + 1) (Fin.snoc L B) = -mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt | exact GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_cutoff_family_symmetric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (κ : Equiv.Perm (Fin P.N)), SymmCharts M P κ → ∃ (cut : Fin P.N → M.Xc → ℝ) (C : ℝ), P.IsCutoffFamily cut C ∧ ∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), cut (κ j) (M.proj (conjVec z)) = cut j (M.proj z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M P κ hS
  obtain ⟨hκ, -, hS3⟩ := hS
  choose g0 hg0s hg0b hg0one hg0c hg0t using fun j => LevelTowerAlt.exists_bumps P j
  have hstarMid : ∀ j t, t ∈ P.chartMid (κ j) → star t ∈ P.chartMid j := by
    intro j t ht
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨z, hz, hzx⟩ := M.surj ((P.chart (κ j)).symm t)
    obtain ⟨hsrc, hmid, -, hch⟩ := hS3 (κ j) z hz
    rw [hκ] at hsrc hmid hch
    have hx : M.proj z ∈ P.mid (κ j) := by
      rw [hzx]
      exact ht2
    have hx' : M.proj (conjVec z) ∈ P.mid j := hmid.2 hx
    have hxs : M.proj z ∈ (P.chart (κ j)).source := P.closure_mid _ (subset_closure hx)
    have hx's : M.proj (conjVec z) ∈ (P.chart j).source := P.closure_mid _ (subset_closure hx')
    have heq : P.chart j (M.proj (conjVec z)) = star t := by
      rw [hch hxs, hzx, (P.chart (κ j)).right_inv ht1]
    show star t ∈ (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
    refine ⟨?_, ?_⟩
    · rw [← heq]
      exact (P.chart j).map_source hx's
    · show (P.chart j).symm (star t) ∈ P.mid j
      rw [← heq, (P.chart j).left_inv hx's]
      exact hx'
  let g : Fin P.N → (Fin D.n → ℂ) → ℝ := fun j t => (g0 j t + g0 (κ j) (star t)) / 2
  have hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g j) := fun j =>
    ((hg0s j).add ((hg0s (κ j)).comp (LevelTowerAlt.contDiff_star _))).div_const 2
  have hbd : ∀ j y, 0 ≤ g j y ∧ g j y ≤ 1 := by
    intro j y
    have h1 := hg0b j y
    have h2 := hg0b (κ j) (star y)
    constructor
    · show 0 ≤ (g0 j y + g0 (κ j) (star y)) / 2
      linarith
    · show (g0 j y + g0 (κ j) (star y)) / 2 ≤ 1
      linarith
  have hone : ∀ j, ∀ x ∈ P.inner j, g j (P.chart j x) = 1 := by
    intro j x hx
    obtain ⟨z, hz, rfl⟩ := M.surj x
    obtain ⟨-, -, hinn, hch⟩ := hS3 j z hz
    have hmid : M.proj z ∈ P.mid j := P.closure_inner _ (subset_closure hx)
    have hsrc : M.proj z ∈ (P.chart j).source := P.closure_mid _ (subset_closure hmid)
    have h1 : g0 j (P.chart j (M.proj z)) = 1 := hg0one j _ ⟨_, subset_closure hx, rfl⟩
    have h2 : g0 (κ j) (star (P.chart j (M.proj z))) = 1 := by
      rw [← hch hsrc]
      exact hg0one (κ j) _ ⟨_, subset_closure (hinn.2 hx), rfl⟩
    show (g0 j (P.chart j (M.proj z)) + g0 (κ j) (star (P.chart j (M.proj z)))) / 2 = 1
    rw [h1, h2]
    norm_num
  have hK : ∀ j, tsupport (g j) ⊆ tsupport (g0 j) ∪ star '' tsupport (g0 (κ j)) := by
    intro j
    apply closure_minimal _ (((hg0c j).union ((hg0c (κ j)).image continuous_star)).isClosed)
    intro t ht
    rw [Function.mem_support] at ht
    by_cases h1 : g0 j t = 0
    · right
      refine ⟨star t, subset_tsupport _ ?_, star_star t⟩
      rw [Function.mem_support]
      intro h2
      apply ht
      show (g0 j t + g0 (κ j) (star t)) / 2 = 0
      rw [h1, h2]
      norm_num
    · left
      exact subset_tsupport _ h1
  have hcpt : ∀ j, IsCompact (tsupport (g j)) := fun j =>
    ((hg0c j).union ((hg0c (κ j)).image continuous_star)).of_isClosed_subset (isClosed_tsupport _) (hK j)
  have hsub : ∀ j, tsupport (g j) ⊆ P.chartMid j := by
    intro j t ht
    rcases hK j ht with h | ⟨u, hu, rfl⟩
    · exact hg0t j h
    · exact hstarMid j u (hg0t (κ j) hu)
  obtain ⟨C, hC⟩ := LevelTowerAlt.cutoff_of_bumps P g hsm hbd hone hcpt hsub
  refine ⟨_, C, hC, ?_⟩
  intro j z hz
  obtain ⟨hsrc, -, -, hch⟩ := hS3 j z hz
  simp only [ReciprocityTheory.AnForm.M.PLAux.chartPush]
  by_cases hx : M.proj z ∈ (P.chart j).source
  · rw [Set.indicator_of_mem (hsrc.2 hx), Set.indicator_of_mem hx]
    simp only [Function.comp]
    rw [hch hx]
    show (g0 (κ j) (star (P.chart j (M.proj z))) + g0 (κ (κ j)) (star (star (P.chart j (M.proj z))))) / 2 - 1
      = (g0 j (P.chart j (M.proj z)) + g0 (κ j) (star (P.chart j (M.proj z)))) / 2 - 1
    rw [hκ, star_star]
    ring
  · rw [Set.indicator_of_notMem (mt hsrc.1 hx), Set.indicator_of_notMem hx]
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

section Unit

variable {R : Type} [CommRing R] {N : ℕ}

def unitCols (I' C : Finset (Fin N)) (e : I'.card = C.card) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => ∑ s : Fin C.card,
    if a = I'.orderEmbOfFin e s ∧ b = C.orderEmbOfFin rfl s then 1 else 0

theorem unitCols_col (I' C : Finset (Fin N)) (e : I'.card = C.card) (a : Fin N) (t : Fin C.card) :
    (unitCols I' C e : Matrix (Fin N) (Fin N) R) a (C.orderEmbOfFin rfl t) =
      if a = I'.orderEmbOfFin e t then 1 else 0 := by
  simp only [unitCols, Matrix.of_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    rw [if_neg]
    rintro ⟨_, h⟩
    exact hs ((C.orderEmbOfFin rfl).injective h).symm
  · simp

theorem minor_unitCols (I' C J : Finset (Fin N)) (e : I'.card = C.card) :
    minorIJ (unitCols I' C e : Matrix (Fin N) (Fin N) R) J C = if J = I' then 1 else 0 := by
  by_cases hJ : J = I'
  · subst hJ
    rw [if_pos rfl, minorIJ, dite_eq_left e]
    have : (unitCols J C e : Matrix (Fin N) (Fin N) R).submatrix (J.orderEmbOfFin e) (C.orderEmbOfFin rfl) = 1 := by
      ext s t
      rw [Matrix.submatrix_apply, unitCols_col, Matrix.one_apply]
      simp
    rw [this, Matrix.det_one]
  · rw [if_neg hJ, minorIJ]
    split_ifs with e'
    · have hns : ¬ J ⊆ I' := fun hs => hJ (Finset.eq_of_subset_of_card_le hs (by rw [e, e']))
      obtain ⟨a, haJ, haI⟩ := Finset.not_subset.1 hns
      have hr : a ∈ Set.range (J.orderEmbOfFin e') := by
        rw [Finset.range_orderEmbOfFin]; exact haJ
      obtain ⟨s, rfl⟩ := hr
      refine Matrix.det_eq_zero_of_row_eq_zero s fun t => ?_
      rw [Matrix.submatrix_apply, unitCols_col, if_neg]
      intro h
      exact haI (h ▸ Finset.orderEmbOfFin_mem _ _ _)
    · rfl

theorem unitCols_blockDiag {j : ℕ} (I' C : Finset (Fin N)) (e : I'.card = C.card)
    (hs : ∀ a ∈ I', ∀ b ∈ C, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsBlockDiag j (unitCols I' C e : Matrix (Fin N) (Fin N) R) := fun a b h => by
  simp only [unitCols, Matrix.of_apply]
  refine Finset.sum_eq_zero fun s _ => if_neg ?_
  rintro ⟨rfl, rfl⟩
  exact h (hs _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _))

theorem stepRows_same_side {j : ℕ} {i : Fin N} {I' : Finset (Fin N)} (h : IsStepRows N j i I') :
    ∀ a ∈ I', ∀ b ∈ stepCols N j i, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  intro a ha b hb
  have h2 := h.2 ha
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  split_ifs at h2 hb with c
  · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega
  · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega

theorem minorIJ_one_self (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  rw [minorIJ, dite_eq_left rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp only [detFac, minorIJ_one_self, ite_self, mul_one]

end Unit

theorem detFac_ne_zero {Ω : Type} [Field Ω] {N j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) Ω}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  intro h0
  have hu : IsUnit T.det := hd.isUnit
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing Ω N j i hj).2.2.2 T T⁻¹ hT (hT.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu, detFac_one, h0, zero_mul] at h
  exact one_ne_zero h

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg


open FrameChange in
theorem plucker_change_of_frame : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ ρ : M.Ω, ρ ≠ 0 ∧ ∀ (m : ι k) (I' : Finset (Fin N)), IsStepRows N j p.2 I' → ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = ρ * F₂.u ⟨k, m⟩ I' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F₁ F₂ h₁ h₂ c₁ c₂ p k hp
  have hj := M.j_le
  have hT₁ := h₁.1 p.1
  have hT₂ := h₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hd₁ := detFac_ne_zero hj p.2 hT₁.1 hT₁.2
  have hd₂ := detFac_ne_zero hj p.2 hT₂.1 hT₂.2
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have hA₂ : (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₂ k')
  have hS : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  refine ⟨detFac j p.2 (F₁.T p.1) * (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') /
    (detFac j p.2 (F₂.T p.1) * ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k'),
    div_ne_zero (mul_ne_zero hd₁ hA₂) (mul_ne_zero hd₂ hA₁), fun m I' hI' => ?_⟩
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have e1 := h₁.2.1 p k hp m _ (hS.mul hE)
  have e2 := h₂.2.1 p k hp m _ hE
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
  have hm : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [(GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 hj).1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hm] at e1
  rw [hr] at e2
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hd₂ hA₁)]
  linear_combination (-detFac j p.2 (F₂.T p.1)) * e1 + detFac j p.2 (F₁.T p.1) * e2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end
