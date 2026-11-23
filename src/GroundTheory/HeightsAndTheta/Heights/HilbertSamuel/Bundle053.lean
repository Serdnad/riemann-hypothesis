module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem locDens_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y := by
  let x0 := (d.R.A.chart j).symm y
  let γ : (Fin D → ℂ) → Ix κ → ℂ := fun y' => d.R.lift x0 ((d.R.A.chart j).symm y')
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0 := by
    filter_upwards [hV.mem_nhds ⟨hy, d.R.mem_U x0⟩] with y' hy'
    exact ⟨differentiableAt_pi.2 fun p => (d.R.holo x0 p j y' hy').differentiableAt,
      gaamix_ne_zero_of_mcPts (d.R.mem x0 _ hy'.2)⟩
  have hL : locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      maDensity (fun k y' => purePot (interp d.m m₁ t) D k (γ y')) y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y =
      maDensity (fun k y' => mixPot d.m m₁ D i k (γ y')) y := by
    intro i
    have e : (fun (k : Fin D) (y' : Fin D → ℂ) =>
        (if k.val < i then resPot d m₁ else resPot d d.m).φ x0 ((d.R.A.chart j).symm y')) =
        fun k y' => mixPot d.m m₁ D i k (γ y') := by
      funext k y'
      by_cases hk : k.val < i
      · simp only [hk, if_true, mixPot]
        rfl
      · simp only [hk, if_false, mixPot]
        rfl
    show ReciprocityTheory.AnForm.maDens _ y = _
    rw [e]
    rfl
  rw [hL, gbamix_maDensity_interp d.smooth hm₁ t hγ]
  exact Finset.sum_congr rfl fun i _ => by rw [hR i]

theorem mInt_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) :
    mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) (fun y => logRatio d.m m₁ (resPt d y)) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y)) := by
  have hg : Continuous (fun y => logRatio d.m m₁ (resPt d y)) :=
    continuous_logRatio_resPt d d.smooth hm₁
  have hΦ : ∀ (i : ℕ) (k : Fin D),
      IsPotential d.R.A (if k.val < i then resPot d m₁ else resPot d d.m) := by
    intro i k
    split_ifs
    · exact isPotential_resPot d hm₁
    · exact isPotential_resPot d d.smooth
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) * logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
            locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
              locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_resPot_interp d hm₁ t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

namespace ResolutionInterpIntegral

theorem proof : ResolutionInterpIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  unfold resMetricInt
  simp only [mInt_resPot_interp d hm₁]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end ResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def NefOnGenericDeg (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ genDeg W 1 a

variable {Ω : Type} [Field Ω] [CharZero Ω]

def chartRingQ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)

def chartLatQ (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : Submodule ℚ Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingQ y c}
  zero_mem' := fun c _ => by simp
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  smul_mem' := fun r s hs c hc => by
    rw [smul_mul_assoc]
    exact Subalgebra.smul_mem _ (hs c hc) r

end Objects

def KodairaGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a →
    0 < genDeg (mCoordIdeal y) D a →
    ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • a - 1) 1

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockCGram (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun k l => ∫ x, pairValH d.A n (b k) (b l) (blockPt d x) ∂d.dV


open Classical in
def blockCChi (d : HSMBlockDatum D K ι Ω) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d.y d.k₀ n p.2 then
    -(1 / 2) * Real.log (blockCGram d n h.choose.2).det.re
  else 0

def blockInterpPot (d : HSMBlockDatum D K ι Ω) (A A' : HermLine ι) (t : ℝ) : LocPot d.R.X where
  U := d.R.U
  isOpen_U := d.R.isOpen_U
  mem_U := d.R.mem_U
  φ x y := (1 - t) * Real.log (A.h (d.R.lift x y)) + t * Real.log (A'.h (d.R.lift x y))

def blockMetricInt (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) : ℝ :=
  ∫ t in (0 : ℝ)..1, mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
    fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))

def blockMixPot (A A' : HermLine ι) (D i : ℕ) : Fin D → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (A'.h z) else Real.log (A.h z)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockMeasureChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d d' : HSMBlockDatum D K ι Ω),
    d'.y = d.y → d'.k₀ = d.k₀ → d'.A = d.A →
    (fun n => blockChi d' n - blockChi d n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d d' : HSMBlockDatum D K ι Ω),
    I.IsFamily → d'.y = d.y → d'.k₀ = d.k₀ →
    (fun n => hsDefect D (blockChi d') (I K ι (mCoordIdeal d'.y) (D + 1) fun _ => d'.A) n -
        hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n r : ℕ) (b : Fin r → MvPolynomial (Σ k, ι k) ℚ),
    IsSecBasisM d.y d.k₀ n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (blockPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockL2NormComplex (d : HSMBlockDatum D K ι Ω) (n : ℕ) (f : MRingOver ℂ ι) : ℝ :=
  Real.sqrt (∫ x, (‖eval (blockPt d x) f‖ / d.A.h (blockPt d x) ^ n) ^ 2 ∂d.dV)

def BlockResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRingOver ℂ ι, IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z f‖ / d.A.h z ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockSectionsRank.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ →
    ∃ C : ℝ, ∀ n : ℕ,
      |(Module.finrank ℤ (secM y (blockDeg k₀ n)) : ℝ) -
          (genDeg (mCoordIdeal y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def FSGeomDegPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → 0 < ptsIntegral P (pot fun _ : Fin e => fsH ι) (fun _ => 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def FrameChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ (B : Matrix (Ix κ) (Ix κ) ℚ) (d' : HSMDatum D Ω κ) (e : Fin (D + 1) → Ix κ),
      IsInvMat B ∧ d'.x = matAct B d.x ∧ (∀ z, d'.m.ρ (matActC B z) = d.m.ρ z) ∧ IsProjFrame d'.x e ∧
      (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenDegAmple.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ k, 1 ≤ d k) → 0 < genDeg (mCoordIdeal y) D d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GenDegGeomDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A →
    geomDeg (mCoordIdeal y) A D = (genDeg (mCoordIdeal y) D A.a : ℝ)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
