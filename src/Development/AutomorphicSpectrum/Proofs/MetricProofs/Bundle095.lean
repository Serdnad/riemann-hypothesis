module

import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCGradAtlas
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle043
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetCuspFramePlurisubharmonic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
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
public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.Transport

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isOpen_compl_bdry (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  apply PositivityTheory.Xgp.c_grad_atlas.isOpen_compl_bdry <;> assumption

theorem contDiffAt_two {A : FinHolAtlas e X} {U : Set X} {f : X → ℝ} (h : A.SmoothOn U f)
    (hU : IsOpen U) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hyU : (A.chart j).symm y ∈ U) : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y :=
  ((h j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hy, hyU⟩)).of_le
    ENat.LEInfty.out

theorem levi_eq_of_sub_re (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {W : Set X} (hW : IsOpen W) (hyW : (A.chart j).symm y ∈ W)
    {G : X → ℂ} (hG : A.HoloOn W G) {a b : X → ℝ} (hab : ∀ z ∈ W, a z - b z = (G z).re)
    (hb : ContDiffAt ℝ 2 (b ∘ (A.chart j).symm) y) (w : Fin e → ℂ) :
    levi (a ∘ (A.chart j).symm) y w = levi (b ∘ (A.chart j).symm) y w := by
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have hre : ContDiffAt ℝ 2 (fun z => ((G ∘ (A.chart j).symm) z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hGa.restrictScalars.contDiffAt
  have hev : (a ∘ (A.chart j).symm) =ᶠ[𝓝 y]
      fun z => (b ∘ (A.chart j).symm) z + 1 * ((G ∘ (A.chart j).symm) z).re := by
    have hmem : ∀ᶠ z in 𝓝 y, (A.chart j).symm z ∈ W :=
      ((A.chart j).continuousAt_symm hy).eventually_mem (hW.mem_nhds hyW)
    filter_upwards [hmem] with z hz
    have := hab _ hz
    simp only [Function.comp]
    linarith
  rw [levi_congr hev, levi_add_smul 1 hb hre, levi_re_analytic hGa]
  ring

theorem exists_re_base {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) {x u : X}
    (hu : u ∈ P.U x) : ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, P.φ x z - P.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G, hG, hW⟩ := hP.2 x u u ⟨hu, P.mem_U u⟩
  refine ⟨W ∩ P.U x ∩ P.U u, (oW.inter (P.isOpen_U x)).inter (P.isOpen_U u),
    ⟨⟨mW, hu⟩, P.mem_U u⟩, G, fun k => (hG k).mono fun y hy => ⟨hy.1, hy.2.1.1⟩, ?_⟩
  rintro z hz
  exact hW z hz

theorem exists_re_change {A : FinHolAtlas e X} {th th' : LocPot X} (hth : IsPotential A th)
    (hsame : SamePot A Set.univ th th') {x u : X} (hu : u ∈ th.U x) :
    ∃ W : Set X, IsOpen W ∧ u ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W, th.φ x z - th'.φ u z = (G z).re := by
  obtain ⟨W, oW, mW, G₁, h₁, e₁⟩ := exists_re_base hth hu
  obtain ⟨V, oV, mV, G₂, h₂, e₂⟩ := hsame u (Set.mem_univ _)
  refine ⟨W ∩ V, oW.inter oV, ⟨mW, mV⟩, fun z => G₁ z + G₂ z, fun k => ?_, ?_⟩
  · exact ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  · rintro z ⟨a, b⟩
    have h1 := e₁ z a
    have h2 := e₂ z b
    simp only [Complex.add_re]
    linarith

theorem isPshOn_transport {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} {th th' : LocPot X}
    {ph : X → ℝ} (hs : IsSection A L s) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hsm : A.SmoothOn (bdry s)ᶜ ph)
    (hpsh : IsPshOn A (bdry s)ᶜ (th' + LocPot.ofFun ph)) :
    IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun ph) := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1
  obtain ⟨W, oW, mW, G, hG, hW⟩ := exists_re_change hth hsame hyx
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨th'.mem_U _, Set.mem_univ _⟩, hyb⟩ w
  have hb : ContDiffAt ℝ 2 ((th' + LocPot.ofFun ph).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    (contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hsm (isOpen_compl_bdry A L s hs) j hyt hyb)
  rw [levi_eq_of_sub_re A j hyt oW mW hG (a := (th + LocPot.ofFun ph).φ x)
    (b := (th' + LocPot.ofFun ph).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := hW z hz
      show th.φ x z + ph z - (th'.φ _ z + ph z) = _
      linarith) hb w]
  exact h0

theorem isPsh_transport {A : FinHolAtlas e X} {Θ th th' : LocPot X} {f : X → ℝ} {c : ℝ}
    (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hth' : IsPotential A th')
    (hsame : SamePot A Set.univ th th') (hf : A.Smooth f)
    (hpsh : IsPsh A (th' + LocPot.ofFun f + Θ.rsmul c)) :
    IsPsh A (th + LocPot.ofFun f + Θ.rsmul c) := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hyx : (A.chart j).symm y ∈ th.U x := hyU.1.1
  have hyΘ : (A.chart j).symm y ∈ Θ.U x := hyU.2
  obtain ⟨W₁, o₁, m₁, G₁, h₁, e₁⟩ := exists_re_change hth hsame hyx
  obtain ⟨W₂, o₂, m₂, G₂, h₂, e₂⟩ := exists_re_base hΘ hyΘ
  have h0 := hpsh ((A.chart j).symm y) j y
    ⟨hyt, ⟨⟨th'.mem_U _, Set.mem_univ _⟩, Θ.mem_U _⟩⟩ w
  have hb : ContDiffAt ℝ 2
      ((th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((contDiffAt_two (hth'.1 _) (th'.isOpen_U _) j hyt (th'.mem_U _)).add
      (contDiffAt_two hf isOpen_univ j hyt (Set.mem_univ _))).add
      (contDiffAt_const.mul (contDiffAt_two (hΘ.1 _) (Θ.isOpen_U _) j hyt (Θ.mem_U _)))
  have hG : A.HoloOn (W₁ ∩ W₂) fun z => G₁ z + (c : ℂ) * G₂ z := fun k =>
    ((h₁ k).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add
      ((analyticOnNhd_const (v := (c : ℂ))).mul ((h₂ k).mono fun y hy => ⟨hy.1, hy.2.2⟩))
  rw [levi_eq_of_sub_re A j hyt (o₁.inter o₂) ⟨m₁, m₂⟩ hG
    (a := (th + LocPot.ofFun f + Θ.rsmul c).φ x)
    (b := (th' + LocPot.ofFun f + Θ.rsmul c).φ ((A.chart j).symm y)) (fun z hz => by
      have h1 := e₁ z hz.1
      have h2 := e₂ z hz.2
      show th.φ x z + f z + c * Θ.φ x z -
        (th'.φ _ z + f z + c * Θ.φ _ z) = _
      simp only [Complex.add_re, Complex.re_ofReal_mul]
      rw [← h1, ← h2]
      ring) hb w]
  exact h0

theorem singWeight_regFamily_transport : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (th th' : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ),
    IsPotential A Θ → IsSection A L s → IsPotential A th → IsPotential A th' → SamePot A Set.univ th th' →
    (IsSingWeight A L s th' ph C₅ → IsSingWeight A L s th ph C₅) ∧
      (IsRegFamily A Θ L s th' ph phT C t₀ → IsRegFamily A Θ L s th ph phT C t₀) := by
  intro e X _ A Θ L s th th' ph phT C₅ C t₀ hΘ hs hth hth' hsame
  constructor
  · rintro ⟨_, hsm, hpsh, hb⟩
    exact ⟨hth, hsm, isPshOn_transport hs hth hth' hsame hsm hpsh, hb⟩
  · rintro ⟨h0, h1, hreg⟩
    refine ⟨h0, h1, fun t ht ht' => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hreg t ht ht'
    exact ⟨a1, a2, a3, a4, isPsh_transport hΘ hth hth' hsame a1 a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.Ar.PB.Transport
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PshPull

open scoped ContDiff

theorem levi_pull_eq {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ)
    (hth : IsPotential A th) (hth' : IsPotential A' th') (hu : A'.Smooth u)
    (hs : SamePot A Set.univ th (th'.pullback h hh.1)) (c : ℝ) (x : X) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ th.U x) (w : Fin e → ℂ) :
    ∃ (j' : Fin A'.n) (y' v : Fin e' → ℂ), y' ∈ (A'.chart j').target ∧
      (A'.chart j').symm y' = h ((A.chart j).symm y) ∧
      levi (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) y w =
        levi (fun s => c * (th'.φ (h ((A.chart j).symm y)) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) y' v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  obtain ⟨p, hp⟩ : ∃ p, p = (A.chart j).symm y := ⟨_, rfl⟩
  rw [← hp] at hyU ⊢
  obtain ⟨j', hj'⟩ := A'.cover (h p)
  obtain ⟨W₁, hW₁o, hpW₁, G₁, hG₁, hE₁⟩ := hth.2 x p p ⟨hyU, th.mem_U p⟩
  obtain ⟨W₂, hW₂o, hpW₂, G₂, hG₂, hE₂⟩ := hs p (Set.mem_univ p)
  have hτ : AnalyticAt ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    hh.2 j j' y ⟨hy, by simpa [← hp] using hj'⟩
  have hGa : AnalyticAt ℂ (fun t => G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)) y :=
    AnalyticAt.add (hG₁ j y ⟨hy, by simpa [← hp] using hpW₁⟩) (hG₂ j y ⟨hy, by simpa [← hp] using hpW₂⟩)
  have hτy : (A'.chart j' ∘ h ∘ (A.chart j).symm) y = A'.chart j' (h p) := by simp [← hp]
  have hy' : A'.chart j' (h p) ∈ (A'.chart j').target := (A'.chart j').map_source hj'
  have hsy' : (A'.chart j').symm (A'.chart j' (h p)) = h p := (A'.chart j').left_inv hj'

  have hψ₁ : ContDiffAt ℝ 2 (th'.φ (h p) ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p)) :=
      (A'.chart j').isOpen_inter_preimage_symm (th'.isOpen_U _)
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p) :=
      ⟨hy', by simpa [hsy'] using th'.mem_U (h p)⟩
    exact (((hth'.1 (h p) j').contDiffAt (hO.mem_nhds hm))).of_le h2
  have hψ₂ : ContDiffAt ℝ 2 (u ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ) := by
      simpa using (A'.chart j').open_target
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ :=
      ⟨hy', Set.mem_univ _⟩
    exact ((hu j').contDiffAt (hO.mem_nhds hm)).of_le h2
  have hψ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      (A'.chart j' (h p)) :=
    contDiffAt_const.mul (hψ₁.add hψ₂)
  have hψτ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      ((A'.chart j' ∘ h ∘ (A.chart j).symm) y) := by rwa [hτy]
  have hτ2 : ContDiffAt ℝ 2 (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    (hτ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hf : ContDiffAt ℝ 2 ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
      (A'.chart j' ∘ h ∘ (A.chart j).symm)) y := hψτ.comp y hτ2
  have hg : ContDiffAt ℝ 2 (fun t => (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt

  have hev : (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) =ᶠ[𝓝 y]
      fun t => ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
        (A'.chart j' ∘ h ∘ (A.chart j).symm)) t + c * (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re := by
    have hcs : ContinuousAt (A.chart j).symm y := (A.chart j).continuousAt_symm hy
    have hOx : ∀ᶠ t in 𝓝 y, (A.chart j).symm t ∈ W₁ ∩ W₂ ∩ th.U x ∩ th.U p ∩ h ⁻¹' (A'.chart j').source := by
      apply hcs.eventually_mem
      rw [← hp]
      refine IsOpen.mem_nhds ?_ ⟨⟨⟨⟨hpW₁, hpW₂⟩, hyU⟩, th.mem_U p⟩, hj'⟩
      exact (((hW₁o.inter hW₂o).inter (th.isOpen_U x)).inter (th.isOpen_U p)).inter
        ((A'.chart j').open_source.preimage hh.1)
    filter_upwards [hOx] with t ht
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
    have e1 := hE₁ _ ⟨⟨h1, h3⟩, h4⟩
    have e2 : th.φ p ((A.chart j).symm t) - th'.φ (h p) (h ((A.chart j).symm t)) =
      (G₂ ((A.chart j).symm t)).re := hE₂ _ h2
    have e3 : (A'.chart j').symm (A'.chart j' (h ((A.chart j).symm t))) = h ((A.chart j).symm t) :=
      (A'.chart j').left_inv h5
    simp only [Function.comp_apply, e3, Complex.add_re]
    rw [← e1, ← e2]
    ring
  refine ⟨j', A'.chart j' (h p), fderiv ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y w, hy', hsy', ?_⟩
  rw [levi_congr hev w, levi_add_smul c hf hg w, levi_comp w hτ hψτ, levi_re_analytic hGa w, hτy]
  ring

theorem isPsh_pull : ∀ (e e' : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ),
    IsPotential A th → IsPotential A' th' → A'.Smooth u → SamePot A Set.univ th (th'.pullback h hh.1) →
    (IsPsh A' (th' + LocPot.ofFun u) → IsPsh A (th + LocPot.ofFun (u ∘ h))) ∧
      (IsPsh A' ((th' + LocPot.ofFun u).rsmul (-1)) → IsPsh A ((th + LocPot.ofFun (u ∘ h)).rsmul (-1))) := by
  intro e e' X Z _ _ A A' h hh th th' u hth hth' hu hs
  refine ⟨fun H x j y hy w => ?_, fun H x j y hy w => ?_⟩
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs 1 x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    simp only [one_mul] at hl
    exact hl ▸ hH
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs (-1) x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    exact hl ▸ hH

end GlobalTheory.CompanionTheory.Ar.PB.PshPull
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem frame_values :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  intro X Ω _ ξ E _ _ κ x L m r n V φ cb hG hV hli hsp p c hc
  obtain ⟨U, hU, b, hbsp, hb⟩ := hV p (Set.mem_univ p)
  have hf : L.IsFrameAt b p := hb p (Set.mem_univ p) hU
  have h1 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • cb a = b l := fun l => by
    have : b l ∈ Submodule.span Ω (Set.range cb) := by
      rw [hsp, ← hbsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  have h2 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • b a = cb l := fun l => by
    have : cb l ∈ Submodule.span Ω (Set.range b) := by
      rw [hbsp, ← hsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  choose t ht using h1
  choose t' ht' using h2
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t l a
  let T' : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t' l a
  have hT : colFrame cb T = b := by
    funext l; exact ht l
  have hT' : colFrame b T' = cb := by
    funext l; exact ht' l
  have hmul : T * T' = 1 := by
    have e : colFrame cb (T * T') = colFrame cb (1 : Matrix (Fin r) (Fin r) Ω) := by
      rw [colFrame_mul, hT, hT', colFrame_one]
    ext a l
    have h3 := congrFun e l
    simp only [colFrame] at h3
    have h0 := (Fintype.linearIndependent_iff.1 hli) (fun a => (T * T') a l - (1 : Matrix _ _ Ω) a l)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h3, sub_self]) a
    exact sub_eq_zero.1 h0
  have hdet : IsUnit T.det := Matrix.isUnit_det_of_right_inverse hmul
  have hval : ∀ a l, ((Matrix.of fun a b => φ a (cb b)) * T) a l = φ a (b l) := by
    intro a l
    rw [← hT]
    simp [Matrix.mul_apply, colFrame, mul_comm]
  have hmem : ∀ l, b l ∈ L p := fun l => by
    rw [hf.2]; exact Submodule.subset_span ⟨l, rfl⟩
  have hw : ∀ l, ∃ w : Module.Dual Ω E, ∀ k, w (b k) = if l = k then 1 else 0 := fun l => by
    obtain ⟨w, h1, h0⟩ := GlobalTheory.CompanionTheory.Ar.FlagGrGen.exists_coord hf.1 l
    refine ⟨w, fun k => ?_⟩
    split_ifs with h
    · rw [← h]; exact h1
    · exact h0 k (Ne.symm h)
  choose w hw using hw
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hf.2] at he
    induction he using Submodule.span_induction with
    | mem e h =>
      obtain ⟨k, rfl⟩ := h
      rw [hw]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a e _ he =>
      have h4 : w l (a • e) = (a : Ω) * w l e := by rw [Subring.smul_def, map_smul, smul_eq_mul]
      rw [h4]; exact mul_mem a.2 he
  choose g hg hg' using fun l => hG.2 p c hc (w l) (hwreg l)
  refine ⟨T, Matrix.of g, hdet, ?_, ?_, ?_, ?_⟩
  · rw [hT]; exact hf
  · intro a l; rw [hval]; exact hG.1 a p c hc _ (hmem l)
  · intro a j; exact hg a j
  · intro a l
    simp only [hval, Matrix.of_apply]
    rw [← hg' a (b l) (hmem l), hw]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.Parab

def IsParabolic {N : ℕ} (ca cb : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ a b, b < a → ¬ (a = cb ∧ b = ca) → M a b = 0

theorem IsParabolic.mul {N : ℕ} {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1)
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsParabolic ca cb A) (hB : IsParabolic ca cb B) :
    IsParabolic ca cb (A * B) := by
  intro a b hba hne
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : c < a ∧ ¬ (a = cb ∧ c = ca)
  · rw [hA a c h1.1 h1.2, zero_mul]
  by_cases h2 : b < c ∧ ¬ (c = cb ∧ b = ca)
  · rw [hB c b h2.1 h2.2, mul_zero]
  exfalso
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

theorem isParabolic_of_upper {N : ℕ} (ca cb : Fin N) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.BlockTriangular id) : IsParabolic ca cb M := fun _ _ h _ => hM h

theorem isParabolic_transvection {N : ℕ} (ca cb : Fin N) (t : ℂ) :
    IsParabolic ca cb (1 + Matrix.single cb ca t) := by
  intro a b hba hne
  rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne, add_zero]
  intro h
  exact hne ⟨h.1.symm, h.2.symm⟩

theorem eq_transvection {N : ℕ} {ca cb : Fin N} {Y : Matrix (Fin N) (Fin N) ℂ} (hne : cb ≠ ca)
    (hlt : ca < cb) (hY : IsLowerUni Y) (hP : IsParabolic ca cb Y) :
    Y = 1 + Matrix.single cb ca (Y cb ca) := by
  ext a b
  rw [Matrix.add_apply]
  by_cases e : a = cb ∧ b = ca
  · obtain ⟨rfl, rfl⟩ := e
    rw [Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
  · have hs : Matrix.single cb ca (Y cb ca) a b = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h => e ⟨h.1.symm, h.2.symm⟩)
    rw [hs, add_zero]
    rcases lt_trichotomy a b with h | h | h
    · rw [hY.2 a b h, Matrix.one_apply_ne h.ne]
    · subst h
      rw [hY.1 a, Matrix.one_apply_eq]
    · rw [hP a b h e, Matrix.one_apply_ne h.ne']

theorem mul_transvection_eq : ∀ (N : ℕ) (h B₀ B₁ : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ),
    (cb : ℕ) = ca + 1 → B₀.BlockTriangular id → B₁.BlockTriangular id → B₀.det ≠ 0 → B₁.det ≠ 0 →
    IsLowerUni (h * B₀) → IsLowerUni (h * (1 + Matrix.single cb ca t) * B₁) →
    ∃ y : ℂ, h * (1 + Matrix.single cb ca t) * B₁ = h * B₀ * (1 + Matrix.single cb ca y) := by
  intro N h B₀ B₁ ca cb t hc h0 h1 d0 _ L0 L1
  have hlt : ca < cb := by simp only [Fin.lt_def]; omega
  have hL0 : IsUnit (h * B₀).det := by rw [L0.det]; exact isUnit_one
  have hB0 : IsUnit B₀.det := isUnit_iff_ne_zero.mpr d0
  letI := Matrix.invertibleOfIsUnitDet (h * B₀) hL0
  letI := Matrix.invertibleOfIsUnitDet B₀ hB0
  set E : Matrix (Fin N) (Fin N) ℂ := 1 + Matrix.single cb ca t with hE
  set Y : Matrix (Fin N) (Fin N) ℂ := B₀⁻¹ * (E * B₁) with hYdef
  have hY : h * B₀ * Y = h * E * B₁ := by
    rw [hYdef, Matrix.mul_assoc h B₀, Matrix.mul_nonsing_inv_cancel_left _ _ hB0, Matrix.mul_assoc]
  have low : Y.BlockTriangular OrderDual.toDual := by
    have e1 : (h * B₀).BlockTriangular OrderDual.toDual := fun a b e => L0.2 _ _ e
    have e2 : (h * E * B₁).BlockTriangular OrderDual.toDual := fun a b e => L1.2 _ _ e
    have := (blockTriangular_inv_of_blockTriangular e1).mul e2
    rwa [← hY, Matrix.nonsing_inv_mul_cancel_left _ _ hL0] at this
  have hYl : IsLowerUni Y := by
    refine ⟨fun a => ?_, fun a b e => low e⟩
    have := L1.1 a
    rw [← hY, Matrix.mul_apply, Finset.sum_eq_single a
      (fun c _ hc' => by
        rcases lt_or_gt_of_ne hc' with e | e
        · rw [low e, mul_zero]
        · rw [L0.2 a c e, zero_mul]) (by simp), L0.1, one_mul] at this
    exact this
  have hP : IsParabolic ca cb Y :=
    (isParabolic_of_upper ca cb (blockTriangular_inv_of_blockTriangular h0)).mul hc
      ((isParabolic_transvection ca cb t).mul hc (isParabolic_of_upper ca cb h1))
  exact ⟨Y cb ca, by rw [← hY, ← eq_transvection hlt.ne' hlt hYl hP]⟩

end GlobalTheory.CompanionTheory.Ar.PB.Parab
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.log_det_cusp_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (I : Submodule (𝓞 E) Λ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → (∀ t ∈ U, (R t).IsCusp I) → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) - Real.log ((R t).nz σ I)) ∧ ContinuousOn (fun t => (R t).nz σ I) U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous | exact GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.isotropic_sublattice_gram_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → ∀ (m : ℕ) (b : Module.Basis (Fin m) ℤ I), m = 2 * Fintype.card Ψ * Module.finrank (𝓞 E) I ∧ (Matrix.of fun i j => (R.ip (R.P (b i : Λ)) (R.P (b j : Λ))).re).det = (R.nz σ I * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq <;> assumption)
end
