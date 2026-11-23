module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle045
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def SupBoundCount.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) (c : ℝ), 0 < c →
    (∀ f : MRing ι, IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f) →
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      blockChi d n - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PerturbSemipos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P0 P : Ideal (MRing ι)) (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (b a : ℤ),
    IsSemipositiveRel P0 P M → 0 ≤ b → 0 ≤ a → IsSemipositiveRel P0 P (HermLine.zcomb M (fsH ι) b a)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n j τ : ℕ) (s t : Ω),
    (τ : ℤ) • C.a = (n : ℤ) • A.a + (j : ℤ) • B.a →
    (∀ z ∈ mcPts (mCoordIdeal y), C.h z ^ τ = A.h z ^ n * B.h z ^ j) →
    s ∈ chartLat y A.a n → t ∈ chartLat y B.a 1 →
    s * t ^ j ∈ chartLat y C.a τ ∧
      ∀ c c' : ℝ, IsBoundedH (mCoordIdeal y) y A n c s → IsBoundedH (mCoordIdeal y) y B 1 c' t →
        IsBoundedH (mCoordIdeal y) y C τ (c * c' ^ j) (s * t ^ j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : Fin r → Ω), (∀ i, e i ∈ chartLat y a (d i)) ∧
      ∀ n : ℕ, chartLat y a n ≤ AddSubgroup.closure
        {s | ∃ (i : Fin r) (μ : Fin q → ℕ), d i + ∑ j, μ j = n ∧ s = e i * ∏ j, w j ^ μ j}

def SectionBounded.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) →
    ∀ (n : ℕ) (s : Ω), s ∈ chartLat y A.a n → ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A n C s

def SectionBoundedMul.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n m : ℕ) (C C' : ℝ) (s t : Ω),
    s ∈ chartLat y A.a n → t ∈ chartLat y A.a m →
    IsBoundedH (mCoordIdeal y) y A n C s → IsBoundedH (mCoordIdeal y) y A m C' t →
    IsBoundedH (mCoordIdeal y) y A (n + m) (C * C') (s * t)

section Inhabitants

open ProjLine

theorem isBoundedH_one_of_isSmallH {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {s : Ω}
    (h : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h' z hg hh hdeg he hz
  rw [one_mul]
  exact h dg dh g h' z hg hh hdeg he hz

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionSupBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (e : Ω),
    ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} → e ∈ chartLat y A.a τ →
    ∃ C : ℝ, 0 ≤ C ∧ IsBoundedH (mCoordIdeal y) y A τ (Real.exp C) e

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def TwistIntersectionAnyDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem)
    (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmoothHerm A → B.a = 0 → IsSmoothHerm B → (∀ sg, 0 < Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A.tensor B) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
          ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def TwistIntersectionInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem)
    (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmoothHerm A → B.a = 0 → IsSmoothHerm B → (∀ sg, 0 < Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A.tensor B) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
          ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZCombLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem) (k : ℕ),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → IsSmoothHerm B →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ℕ, 0 < p → 0 < q → (p : ℝ) / q < δ →
      |II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A B ((q : ℤ) - k * p) p) /
          (q : ℝ) ^ (D + 1) - II K ι (mCoordIdeal y) (D + 1) (fun _ => A)| < ε ∧
      |(genDeg (mCoordIdeal y) D (HermLine.zcomb A B ((q : ℤ) - k * p) p).a : ℝ) / (q : ℝ) ^ D -
          genDeg (mCoordIdeal y) D A.a| < ε

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace NefOnGenericOfSemipos

theorem hasFDerivAt_eval {σ : Type*} [Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i, eval z (pderiv i g) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i) z :=
  _root_.UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval g z

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem maDensity_nonneg {P P0 W : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hP0 : P0 ≤ P) (hPW : P ≤ W)
    (hs : IsSemipositiveRel P0 P A) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ)}
    {y : Fin 1 → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin 1 → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet W Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hz : γ y ∈ mcPts W := h.2.self_of_nhds.2.1
  have hne : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hz.1
  have hzP : γ y ∈ mcPts P := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) :=
    ((hs.1.contDiffAt (isOpen_blockNonzero.mem_nhds hne)).of_le
      (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hne).ne'
  have htan : IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y (Pi.single 0 1)) := by
    intro f hf
    have h0 : (fun y' => eval (γ y') (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [h.2] with y' hy'
      exact hy'.2.1.2 f (hPW (hP0 hf))
    have hd := (hasFDerivAt_eval (map (Int.castRingHom ℂ) f) (γ y)).comp y
      hA.differentiableAt.hasFDerivAt
    have h00 := (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) y).congr_of_eventuallyEq h0
    have := congrArg (fun L => L (Pi.single 0 1)) (hd.unique h00)
    simpa using this
  have hlevi : 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log (A.h z)) (γ y)
      (fderiv ℂ γ y (Pi.single 0 1)) := hs.2 (γ y) hzP _ htan
  have key := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) hA hφ
  rw [← key] at hlevi
  unfold ReciprocityTheory.AnForm.levi at hlevi
  simp only [Function.comp_def] at hlevi
  rw [maDensity_one]
  apply div_nonneg _ (by positivity)
  linarith

theorem geomDeg_one_nonneg {P P0 W : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hP0 : P0 ≤ P)
    (hs : IsSemipositiveRel P0 P A) (hPW : P ≤ W) : 0 ≤ geomDeg W A 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine MeasureTheory.integral_nonneg fun y => ?_
    refine finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · simpa only [one_mul] using maDensity_nonneg hP0 hPW hs hγ.choose_spec
    · exact le_rfl
  · exact le_rfl

end NefOnGenericOfSemipos

theorem NefOnGenericOfSemipos.proof : NefOnGenericOfSemipos.Statement :=
  fun _ _ _ _ _ _ _ hP0 hs _ _ hPW => NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hs hPW

theorem ArithmeticVolumeBig.of_moriwakiBig_only (hM : MoriwakiBigStatement) : ArithmeticVolumeBig.Statement :=
  ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hM

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionPullback.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A),
      A.Compatible d.R.A ∧ W.IsSemipositive ∧ dV.μ = d.dV ∧
      ∀ (n : ℕ) (f : MRing ι), IsMultiHomog f (blockDeg d.k₀ n) →
        ∃ s ∈ L.sections n, ∀ x : d.R.X,
          ptNormSq W n s x =
            (‖eval (blockPt d x) (map (Int.castRingHom ℂ) f)‖ / d.A.h (blockPt d x) ^ n) ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem G5.ptsIntegral_curve_const (W : Ideal (MRing ι)) (hW1 : IsArithVar W 1)
    (hfin : Finite (GroundTheory.Heights₂.Heights.projPts W)) (c : ℝ) :
    ptsIntegral W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) = c * degC W := by
  have : Nonempty K := hW1.1
  have hpot : pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.elim0 := Subsingleton.elim _ _
  have hpts := GroundTheory.Heights₂.Heights.PtsIntegralPoints.homogProof K ι W (fun _ => c) hW1.2.1.2.1 hfin
    (fun _ _ _ _ => rfl)
  rw [hpot, hpts]
  letI := Fintype.ofFinite (GroundTheory.Heights₂.Heights.projPts W)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    GroundTheory.Heights₂.Heights.degC_eq_card_projPts, Nat.card_eq_fintype_card]
  ring

theorem G5.proof' (hK : ArithKleiman.Statement) (hF : CurvePointsFinite.Statement) : G5.Statement := by
  intro K _ ι _ P P0 D A e II hII hP hP0 hsemi hnef hconj hW
  set A' := A.tensor (constLine (ι := ι) e) with hA'def
  have hA : IsSmoothHerm A := hsemi.1
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine e)
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hsemi' : IsSemipositiveRel P0 P A' := by
    refine ⟨hA', fun z hz w hw => ?_⟩
    have hev : ∀ᶠ z' in 𝓝 z, Real.log (A'.h z') = Real.log (A.h z') + -e :=
      (show ∀ᶠ z' in 𝓝 z, ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hU.mem_nhds hz.1).mono fun z' hz' =>
        G5.log_tensor_constLine A e z' hz'
    have : leviForm (fun z => Real.log (A'.h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
      unfold leviForm
      rw [G5.fderiv_fderiv_eq_of_add_const (-e) hev]
    rw [this]
    exact hsemi.2 z hz w hw
  have ha : A'.a = A.a := by
    show A.a + 0 = A.a
    rw [add_zero]
  have hnef' : NefOnFibres P A'.a := ha ▸ hnef
  have hconj' : IsConjInvariantH A' := fun z => by
    show A.h _ * Real.exp (-e) = A.h z * Real.exp (-e)
    rw [hconj z]
  have hW' : ∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A'] := by
    intro W hW1 hPW
    have hsn : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
        (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B] := by
      intro B
      funext j
      fin_cases j
      rfl
    have hmc := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => e) (fun _ _ _ => rfl) hW1
      (fun j => j.elim0) hA contDiffOn_const
    rw [hsn, hsn] at hmc
    have hA'W : II K ι W 1 ![A'] = II K ι W 1 ![A] - e * degC W := by
      rw [← G5.ptsIntegral_curve_const W hW1 (hF K ι W hW1) e]
      exact hmc
    rw [hA'W]
    linarith [hW W hW1 hPW]
  have hkl := hK K ι P P0 D A' II hII hP hP0 hsemi' hnef' hconj' hW'
  have htop := G5.top_tensor_constLine (II K ι) (hII K ι) P D A e hP hA
  rw [← hA'def] at htop
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
