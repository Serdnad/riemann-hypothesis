module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

namespace SystemIndependence

section Integrals

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem mIntegrable_linComb (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (c : ℝ) {f f' : X → ℝ}
    (hf : MIntegrable A Φ f) (hf' : MIntegrable A Φ f') :
    MIntegrable A Φ (fun x => c * f x + f' x) := fun j K hK hKc =>
  IntegrableOn.congr_fun (((hf j K hK hKc).const_mul c).add (hf' j K hK hKc))
    (fun y _ => by simp only [Pi.add_apply]; ring) hKc.measurableSet

theorem mIntegrable_zero (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) :
    MIntegrable A Φ (fun _ => 0) := fun j K _ _ => by
  simp

theorem mInt_zero (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt ReciprocityTheory.AnForm.M.integralWith
  split_ifs <;> simp

theorem mInt_nonneg_on (A : FinHolAtlas D X) (V : Set X) (Φ : Fin D → LocPot X)
    (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i)) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf0 : ∀ x ∉ V, f x = 0) : 0 ≤ mInt A Φ f := by
  unfold mInt
  split_ifs with h
  · unfold ReciprocityTheory.AnForm.M.integralWith
    refine Finset.sum_nonneg fun j _ =>
      setIntegral_nonneg (A.chart j).open_target.measurableSet fun y hy => ?_
    by_cases hyV : (A.chart j).symm y ∈ V
    · have hd : 0 ≤ ReciprocityTheory.AnForm.M.locDens A Φ j y :=
        ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun i =>
          ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y
            (ReciprocityTheory.AnForm.M.pot_contDiffAt_two (hpot i) _ j hy ((Φ i).mem_U _))
            (fun w => hnn i _ j y ⟨hy, hyV, (Φ i).mem_U _⟩ w)
      exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf _)) hd
    · rw [hf0 _ hyV]
      simp
  · exact le_rfl

theorem abs_mInt_le [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (V : Set X)
    (Φ : Fin D → LocPot X) (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i))
    (hAn : A.IsAnalyticSubset Vᶜ) (hint : interior Vᶜ = ∅) {h b : X → ℝ}
    (hh : MIntegrable A Φ h) (hb : MIntegrable A Φ b) (hle : ∀ x ∈ V, |h x| ≤ b x) :
    |mInt A Φ h| ≤ mInt A Φ b := by
  have key : ∀ c : ℝ, |c| = 1 → 0 ≤ mInt A Φ (fun x => c * h x + b x) := by
    intro c hc
    have hcongr := ReciprocityTheory.AnForm.M.mIntCongrNull A Φ Vᶜ hAn hint (fun x => c * h x + b x)
      (V.indicator fun x => c * h x + b x) (fun x hx => by
        rw [Set.indicator_of_mem (Set.not_notMem.mp hx)])
    rw [hcongr]
    refine mInt_nonneg_on A V Φ hpot hnn _ (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _)
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx]
      have h1 := hle x hx
      have h2 : |c * h x| = |h x| := by rw [abs_mul, hc, one_mul]
      have h3 := neg_abs_le (c * h x)
      linarith
    · rw [Set.indicator_of_notMem hx]
  have l1 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot (-1) h b hh hb
  have l2 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot 1 h b hh hb
  have k1 := key (-1) (by norm_num)
  have k2 := key 1 (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end Integrals

end SystemIndependence

section Inhabitant

open ReciprocityTheory.AnForm.M (p1)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt)

def LemmaEEnergy.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (v : Fin D → X → ℝ) (w : X → ℝ), (∀ i, A.Smooth (v i)) →
    (∀ i, IsPsh A (potForm Om.pot (v i))) → (∀ i x, -1 ≤ v i x ∧ v i x ≤ 0) → A.Smooth w →
    IsPsh A (potForm Om.pot w) →
    mInt A (fun i => potForm Om.pot (v i)) (fun x => -w x) ≤
      mInt A (fun _ => Om.pot) (fun x => -w x) + D * Om.vol

section Inhabitants

open ReciprocityTheory.AnForm.M (p1)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt)

def LemmaEScale.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (M : ℝ) (v : Fin D → X → ℝ), 1 ≤ M → (∀ i, A.Smooth (v i)) →
    (∀ i, IsPsh A (potForm Om.pot (v i))) →
    (∀ i, IsPsh A (potForm Om.pot fun x => v i x / M)) ∧
    ∀ g : X → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      mInt A (fun i => potForm Om.pot (v i)) g ≤
        M ^ D * mInt A (fun i => potForm Om.pot fun x => v i x / M) g

section Inhabitants

open ReciprocityTheory.AnForm.M (p1)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh)

def LemmaETrunc.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Om : KaehlerForm A)
    (Yo : Set X) (r : X → ℝ) (C₁ : ℝ) (u : X → ℝ), IsOpen Yo → Dense Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → 0 ≤ C₁ → A.SmoothOn Yo u → FormNonneg A Yo (potForm Om.pot u) →
    (∀ x ∈ Yo, u x ≤ 0) → (∀ x ∈ Yo, -(C₁ * Real.log (r x)) ≤ u x) →
    (A.Smooth u ∨ ∀ y, y ∉ Yo → Tendsto u (𝓝[Yo] y) atBot) →
    ∀ R : ℝ, Real.exp 1 ≤ R → ∃ v : X → ℝ, A.Smooth v ∧ IsPsh A (potForm Om.pot v) ∧
      (∀ x, -(C₁ * Real.log R + 2) ≤ v x ∧ v x ≤ 0) ∧
      ∃ c : ℝ, ∀ x ∈ Yo, r x < R → v x = u x + c

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt MIntegrable)

def LemmaETruncMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (Yo : Set X) (r : X → ℝ) (u : Fin D → X → ℝ) (v : ℝ → Fin D → X → ℝ),
    IsOpen Yo → ContinuousOn r Yo → (∀ i, A.SmoothOn Yo (u i)) →
    (∀ i, FormNonneg A Yo (potForm Om.pot (u i))) →
    (∀ R : ℝ, Real.exp 1 ≤ R → ∀ i, A.Smooth (v R i) ∧ IsPsh A (potForm Om.pot (v R i)) ∧
      ∃ c : ℝ, ∀ x ∈ Yo, r x < R → v R i x = u i x + c) →
    ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
      MIntegrable A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1) ∧
      mInt A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1) ≤
        mInt A (fun i => potForm Om.pot (v R₀ i)) ({x | x ∉ Yo ∨ R₀ ≤ r x}.indicator 1)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def ListMono.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A) (C₁ : ℝ) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsBoundedPotForm A Yo r Om C₁ (th i) (u i)) →
    (∀ i, FormNonneg A Yo (potForm Om.pot (u i))) ∧
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y) ∧
    ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (∀ x, x ∉ Yo → g x = 0) →
      MIntegrable A (fun i => potForm Om.pot (u i)) g →
      MIntegrable A (fun i => potForm (th i) (u i)) g ∧
        mInt A (fun i => potForm (th i) (u i)) g ≤ mInt A (fun i => potForm Om.pot (u i)) g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def ListMonoDens.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (Om : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) →
    IsPotential A Om → (∀ i, A.SmoothOn Yo (u i)) → (∀ i, LeviLe A Set.univ 1 (th i) 1 Om) →
    (∀ i, FormNonneg A Yo (potForm (th i) (u i))) →
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y ∧
        locDens A (fun i => potForm (th i) (u i)) j y ≤ locDens A (fun i => potForm Om (u i)) j y

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def ListMonoRaise.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th Om : LocPot X)
    (u : X → ℝ), IsOpen Yo → IsPotential A th → IsPotential A Om → A.SmoothOn Yo u →
    LeviLe A Set.univ 1 th 1 Om → FormNonneg A Yo (potForm th u) → FormNonneg A Yo (potForm Om u)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListTailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), (∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) → ∀ (Om : KaehlerForm A) (C₁ : ℝ),
    ∃ CE : ℝ, ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ j, IsBoundedPotForm A R.Yo R.r Om C₁ (th j) (u j)) →
      TailLogBound A R.Yo R.r (fun j => potForm (th j) (u j)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListTailLogSmooth.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R : RegChartData A) (Om : KaehlerForm A) (C₁ : ℝ), ∃ CE : ℝ,
    ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th i) (u i)) →
        TailLogBound A R.Yo R.r (fun i => potForm (th i) (u i)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def LocDensContOnOpen.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn Yo (u i)) →
    ∀ j, ContinuousOn (locDens A (fun i => potForm (th i) (u i)) j)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def TailShift.Statement : Prop :=
  ∀ (D : ℕ) (B CE : ℝ), ∃ CE' : ℝ, ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas D X) (Yo : Set X) (r r' : X → ℝ) (T : Fin D → LocPot X),
    IsOpen Yo → ContinuousOn r Yo → ContinuousOn r' Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → (∀ x ∈ Yo, Real.exp 1 ≤ r' x) →
    (∀ x ∈ Yo, |r x - r' x| ≤ B) →
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A T j y) →
    TailLogBound A Yo r' T CE → TailLogBound A Yo r T CE'

section Inhabitants

open ReciprocityTheory.AnForm (fsDens fsDens_pos)
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLine_locDens_first_chart projectiveLine_locDens_second_chart projectiveLine_fubiniStudy_mass_one)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
