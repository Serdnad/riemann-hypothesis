module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle001
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

noncomputable section

section Objects

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def bdDom (R : RegChartData A) (j : Fin R.n) : Set X := (R.ψ j).source ∩ R.ψ j ⁻¹' R.W j

theorem isOpen_bdDom (R : RegChartData A) (j : Fin R.n) : IsOpen (bdDom R j) :=
  (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j)

def bdEq (R : RegChartData A) (j : Fin R.n) (y : X) : ℂ := ∏ i ∈ R.S j, R.ψ j y i

def bdIdx (R : RegChartData A) (x : X) : Fin R.n := (R.cover x).choose

theorem mem_V''_bdIdx (R : RegChartData A) (x : X) : x ∈ R.V'' (bdIdx R x) :=
  (R.cover x).choose_spec

theorem V''_subset_bdDom (R : RegChartData A) (j : Fin R.n) : R.V'' j ⊆ bdDom R j :=
  fun _ hx => ⟨hx.1, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hx.2)))⟩

theorem mem_bdDom_bdIdx (R : RegChartData A) (x : X) : x ∈ bdDom R (bdIdx R x) :=
  V''_subset_bdDom R _ (mem_V''_bdIdx R x)

def bdPot (R : RegChartData A) (φ : Fin R.n → X → ℝ) (c : ℝ) : LocPot X where
  U x := bdDom R (bdIdx R x)
  isOpen_U _ := isOpen_bdDom R _
  mem_U x := mem_bdDom_bdIdx R x
  φ x y := φ (bdIdx R x) y + c

def bdSec (R : RegChartData A) (x : X) : X → ℂ := bdEq R (bdIdx R x)

def IsBdMetric (R : RegChartData A) (φ : Fin R.n → X → ℝ) : Prop :=
  (∀ j, A.SmoothOn (bdDom R j) (φ j)) ∧
  (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
      A.HoloOn W G ∧ ∀ z ∈ W ∩ (bdDom R j ∩ bdDom R k), φ j z - φ k z = (G z).re) ∧
  ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
    ‖bdEq R j y‖ * Real.exp (-φ j y) = ‖bdEq R k y‖ * Real.exp (-φ k y)

def bdWeight (R : RegChartData A) (χ : Fin R.n → X → ℝ) (g : Fin R.n → Fin R.n → X → ℂ)
    (j : Fin R.n) (y : X) : ℝ :=
  ∑ l, (bdDom R l).indicator (fun z => χ l z * ‖g j l z‖ ^ 2) y

end Objects

def RegYoDense.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A), Dense R.Yo

def RegRCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A),
    ContinuousOn R.r R.Yo

def ChartCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X), IsOpen U →
    (∀ f : X → ℝ, A.SmoothOn U f → ContinuousOn f U) ∧
    ∀ g : X → ℂ, A.HoloOn U g → ContinuousOn g U

def BdEqHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n),
    A.HoloOn (bdDom R j) (bdEq R j) ∧ ∀ y ∈ bdDom R j, (bdEq R j y = 0 ↔ y ∉ R.Yo)

def HyperplaneDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (i : Fin D), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z i = 0 → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = z i * G z

def CoordDivDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (S : Finset (Fin D)), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z ∈ coordDiv S → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = (∏ i ∈ S, z i) * G z

def BdDivides.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ u : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) u ∧ ContinuousOn u (bdDom R j ∩ bdDom R k) ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R k y = u y * bdEq R j y

def BdTransition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ g : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) g ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, g y ≠ 0 ∧ bdEq R j y = g y * bdEq R k y

def BdCocycle.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (g : Fin R.n → Fin R.n → X → ℂ), (∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R j y = g j k y * bdEq R k y) →
    ∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y

def BdPartition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ χ : Fin R.n → X → ℝ, (∀ j, A.Smooth (χ j)) ∧ (∀ j y, 0 ≤ χ j y) ∧
      (∀ y, ∑ j, χ j y = 1) ∧ ∀ j, tsupport (χ j) ⊆ bdDom R j

def LogNormHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (W : Set X) (g : X → ℂ),
    IsOpen W → A.HoloOn W g → (∀ y ∈ W, g y ≠ 0) → ∀ y ∈ W, ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re

def IndicatorSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U O : Set X) (χ h : X → ℝ),
    IsOpen U → IsOpen O → A.Smooth χ → tsupport χ ⊆ O → A.SmoothOn (U ∩ O) h →
    A.SmoothOn U (O.indicator fun y => χ y * h y)

def NormSqSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X) (g : X → ℂ),
    A.HoloOn U g → A.SmoothOn U (fun y => ‖g y‖ ^ 2)

def BdWeight.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (g : Fin R.n → Fin R.n → X → ℂ),
    (∀ j k, A.HoloOn (bdDom R j ∩ bdDom R k) (g j k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, g j k y ≠ 0) →
    (∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y) →
    ∃ w : Fin R.n → X → ℝ, (∀ j, A.SmoothOn (bdDom R j) (w j)) ∧
      (∀ j, ∀ y ∈ bdDom R j, 0 < w j y) ∧
      ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, w j y = ‖g j k y‖ ^ 2 * w k y

def BdMetric.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ φ : Fin R.n → X → ℝ, IsBdMetric R φ

def BddOnInner.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n)
    (u : X → ℝ), ContinuousOn u (bdDom R j) → ∃ B : ℝ, ∀ y ∈ R.V'' j, |u y| ≤ B

def BdSectionProps.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    IsPotential A (bdPot R φ c) ∧ IsSection A (bdPot R φ c) (bdSec R) ∧ secOpen (bdSec R) = R.Yo

def BdNormCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    Continuous fun y => ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)

def BdComparison.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec (bdPot R φ c) (bdSec R) y| ≤ B

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 holoOn_const)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

def LemmaETailMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailMassBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh mInt)

def LemmaETruncTail.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, 1 ≤ M → ∀ v : Fin D → X → ℝ, (∀ i, A.Smooth (v i)) →
      (∀ i, IsPsh A (potForm Om.pot (v i))) → (∀ i x, -M ≤ v i x ∧ v i x ≤ 0) →
      ∀ ρ : ℝ, Real.exp 1 ≤ ρ →
        mInt A (fun i => potForm Om.pot (v i))
            ({x | x ∉ secOpen s ∨ ρ ≤ rSec L s x}.indicator 1) ≤ M ^ D * K / ρ

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh)

def LemmaEWeight.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ l : ℝ, 1 ≤ l → ∃ w : X → ℝ, A.Smooth w ∧ IsPsh A (potForm Om.pot w) ∧
      (∀ x ∈ secOpen s, min (c₀ * rSec L s x) l ≤ -w x ∧ -w x ≤ c₀ * rSec L s x + 1) ∧
      (∀ x, x ∉ secOpen s → l ≤ -w x)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection MIntegrable logNormSec)

def LogNormSecIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (L : LocPot X)
    (s : X → X → ℂ), IsPotential A L → IsSection A L s → Dense (secOpen s) →
    ∀ Φ : Fin D → LocPot X, (∀ i, IsPotential A (Φ i)) → MIntegrable A Φ (logNormSec L s)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def RegSection.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ (L : LocPot X) (s : X → X → ℂ), IsPotential A L ∧ IsSection A L s ∧
      (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) ∧ secOpen s = R.Yo ∧ Dense R.Yo ∧
      ContinuousOn R.r R.Yo ∧ ContinuousOn (rSec L s) R.Yo ∧
      ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec L s y| ≤ B

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi levi_zero levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_rsmul_chart (A : FinHolAtlas D X) (P : LocPot X) (hP : IsPotential A P) (a : ℝ)
    (x : X) (k : Fin A.n) (y : Fin D → ℂ)
    (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) (w : Fin D → ℂ) :
    levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w = a * levi (P.φ x ∘ (A.chart k).symm) y w := by
  have hs : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y :=
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hs w
  have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
      fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
    funext z
    simp [LocPot.rsmul]
  rw [he, h, levi_const, zero_add]

theorem BoundingKaehler.proof : BoundingKaehler.Statement := by
  intro X _ _ _ D A om m th hth
  have hX : IsCompact (Set.univ : Set X) := isCompact_univ
  choose M hM0 hM using fun i => levi_abs_le_global A hX (th i) om.pot (hth i) om.isPot om.pos
  set K : ℝ := 1 + ∑ i, M i with hKdef
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
  have hK : 0 < K := by linarith
  have hMK : ∀ i, M i ≤ K := fun i => by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hM0 j) (Finset.mem_univ i)
    linarith
  have hnn : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x, ∀ w : Fin D → ℂ,
      0 ≤ levi (om.pot.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (om.pos x k y hy w h0).le
  refine ⟨⟨om.pot.rsmul K, ReciprocityTheory.AnForm.M.isPotentialRsmul A K om.pot om.isPot,
    fun x k y hy w hw => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [levi_rsmul_chart A om.pot om.isPot K x k y hy w]
    exact mul_pos hK (om.pos x k y hy w hw)
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.1.2, hy.2.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.1.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.2, hy.2.1.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens potSmoothOn hessCGerm maDens_congr_hessC
  maDens_continuousOn)

theorem LocDensContOnOpen.proof : LocDensContOnOpen.Statement := by
  intro D X _ A Yo th u hYo hth hu j y0 hy0
  apply ContinuousAt.continuousWithinAt
  have hu2 : ∀ i, ContDiffOn ℝ 2 (u i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    fun i => (hu i j).of_le (WithTop.coe_le_coe.2 le_top)
  have hNo : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) :=
    (A.chart j).isOpen_inter_preimage_symm
      (hYo.inter (isOpen_iInter_of_finite fun i => (th i).isOpen_U _))
  have hy0N : y0 ∈ (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)) :=
    ⟨hy0.1, hy0.2, Set.mem_iInter.2 fun i => (th i).mem_U _⟩
  have hsm : ∀ i, ContDiffOn ℝ 2 (fun y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) ((A.chart j).target ∩
        (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) := fun i =>
    ((potSmoothOn A (th i) (hth i) _ j).mono (t := (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)))
      fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i⟩).add
      ((hu2 i).mono (t := (A.chart j).target ∩
        (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)))
        fun y hy => ⟨hy.1, hy.2.1⟩)
  have heq : ReciprocityTheory.AnForm.maDens (fun i y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) =ᶠ[nhds y0] locDens A (fun i => potForm (th i) (u i)) j := by
    filter_upwards [hNo.mem_nhds hy0N] with y hy
    unfold locDens
    apply maDens_congr_hessC
    intro i
    have hp0 : (A.chart j).symm y ∈ (th i).U ((A.chart j).symm y0) := Set.mem_iInter.1 hy.2.2 i
    obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ :=
      (hth i).2 ((A.chart j).symm y) ((A.chart j).symm y0) ((A.chart j).symm y) ⟨(th i).mem_U _, hp0⟩
    have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0))) :=
      (A.chart j).isOpen_inter_preimage_symm
        ((hWo.inter ((th i).isOpen_U _)).inter ((th i).isOpen_U _))
    have hyV : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0)) :=
      ⟨hy.1, ⟨hyW, (th i).mem_U _⟩, hp0⟩
    have h1 : (fun y' => (potForm (th i) (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
        (fun w => ((th i).φ ((A.chart j).symm y0) ((A.chart j).symm w) + u i ((A.chart j).symm w)) +
          ((G ∘ (A.chart j).symm) w).re) := by
      filter_upwards [hVo.mem_nhds hyV] with w hw
      have := hGeq ((A.chart j).symm w) hw.2
      show (th i).φ _ _ + u i _ = _
      simp only [Function.comp_apply]
      linarith
    exact ((hessCGerm _ _ _ h1).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
      ((hsm i).contDiffAt (hNo.mem_nhds hy)) (hG j y ⟨hy.1, hyW⟩))).symm
  refine ContinuousAt.congr ?_ heq
  exact (maDens_continuousOn _ _ hNo hsm).continuousAt (hNo.mem_nhds hy0N)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.proof (hRaise : ListMonoRaise.Statement) (hDens : ListMonoDens.Statement)
    (hCont : LocDensContOnOpen.Statement) (hInt : MIntegrableOfDensLe.Statement)
    (hMono : MIntMonoOfDensLe.Statement) : ListMono.Statement := by
  intro X _ _ _ D A Yo r Om C₁ th u hYo hT
  have hdens := hDens A Yo th Om.pot u hYo (fun i => (hT i).th_pot) Om.isPot
    (fun i => (hT i).u_smooth) (fun i => (hT i).th_le) (fun i => (hT i).nonneg)
  refine ⟨fun i => hRaise A Yo (th i) Om.pot (u i) hYo (hT i).th_pot Om.isPot (hT i).u_smooth
    (hT i).th_le (hT i).nonneg, fun j y hy hY => (hdens j y hy hY).1, fun g hg0 hgV hgA => ?_⟩
  have hcT := hCont A Yo th u hYo (fun i => (hT i).th_pot) (fun i => (hT i).u_smooth)
  have hcA := hCont A Yo (fun _ => Om.pot) u hYo (fun _ => Om.isPot) (fun i => (hT i).u_smooth)
  exact ⟨hInt A Yo _ _ hYo hcT hcA hdens g hgV hgA, hMono A Yo _ _ hdens g hg0 hgV hgA⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
