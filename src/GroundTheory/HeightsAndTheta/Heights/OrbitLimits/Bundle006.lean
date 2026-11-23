module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.RingTheory.Nullstellensatz
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear linEval linForm euclPot logReg)

def LelongWeightDiff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (g k : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ g → HasCompactSupport g →
    (∀ j, SmoothNear (ComplexSets.zeroSet J) (φ j)) →
    SmoothNear (ComplexSets.zeroSet J) k → (∀ x ∈ ComplexSets.zeroSet J, 0 < k x) →
      Tendsto (fun ε : ℝ =>
          varInt J (d + 1) (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (vecCons g φ) -
            varInt J (d + 1) (logReg u ε) (vecCons g φ))
        (𝓝[>] 0) (𝓝 0)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)

section Chart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segreChartSet (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def segreChartIdeal (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (segreChartSet P σ i)

def segreChartComponents (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (segreChartIdeal P σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_segreChartComponents {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ segreChartComponents P σ i ↔ J ∈ (segreChartIdeal P σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _


omit [∀ k, Fintype (ι k)] in
theorem chart_coord_eq_one {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ ComplexSets.zeroSet J) : x (σ.symm i) = 1 := by
  have hle : segreChartIdeal P σ i ≤ J := (mem_segreChartComponents.1 hJ).1.2
  have hmem : (MvPolynomial.X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i := by
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    simp [hzi]
  have h := hx _ (hle hmem)
  simp only [map_sub, MvPolynomial.eval_X, map_one] at h
  exact sub_eq_zero.1 h

end Chart

section Lift

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ) :
    (Σ k, ι k) → ℂ :=
  fun p => x (σ.symm (Function.update i p.1 p.2))

theorem contDiff_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) {n : WithTop ℕ∞} :
    ContDiff ℝ n (chartLift σ i) :=
  contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (σ.symm (Function.update i p.1 p.2))


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartLift_blockNonzero {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0 :=
  fun k => ⟨i k, by simp [chartLift, hx]⟩


omit [∀ k, Fintype (ι k)] in
theorem chartLift_segre_apply {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) (k : K) (j : ι k) :
    chartLift σ i (fun a => segre z (σ a)) ⟨k, j⟩ = z ⟨k, j⟩ * (z ⟨k, i k⟩)⁻¹ := by
  have hne : z ⟨k, i k⟩ ≠ 0 := fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hz] at this
    exact one_ne_zero this
  have hupd : (fun k' => z ⟨k', Function.update i k j k'⟩) =
      Function.update (fun k' => z ⟨k', i k'⟩) k (z ⟨k, j⟩) := by
    funext k'
    by_cases h : k' = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hprod : segre z (Function.update i k j) = z ⟨k, j⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ := by
    simp only [segre]
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hall : z ⟨k, i k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i k'⟩ = 1 := by
    rw [Finset.mul_prod_erase _ (fun k' => z ⟨k', i k'⟩) (Finset.mem_univ k)]
    exact hz
  simp only [chartLift, Equiv.apply_symm_apply]
  rw [hprod]
  field_simp
  linear_combination z ⟨k, j⟩ * hall

theorem segre_chartLift {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) :
    segre (chartLift σ i (fun a => segre z (σ a))) = segre z := by
  funext i'
  show ∏ k, chartLift σ i (fun a => segre z (σ a)) ⟨k, i' k⟩ = ∏ k, z ⟨k, i' k⟩
  simp only [chartLift_segre_apply σ i z hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have : ∏ k, z ⟨k, i k⟩ = 1 := hz
  rw [this, inv_one, mul_one]

end Lift

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

def FnDegRelDeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hκv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (i' : ∀ k', ι' k'),
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsChart P' i' →
      haveI := hP'.isPrime
      ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg v P' i' = relDeg ⟨κ, hκv.1⟩ P'

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def SegreDivisor.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (n : ℕ), IsProjVarF V (n + 1) →
    ∃ f : MRingOver F ι, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => 1) ∧ f ∉ V ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f ≠ 0

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def ChartDimBound.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k), IsMultiProjPrime V → IsChart V i →
    ringKrullDim (MRingOver F ι ⧸ V) ≤
      ringKrullDim (MRingOver F ι ⧸ chartIdeal V i) + (Fintype.card K : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def ChartFiniteIrrel.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) (i : ∀ k, ι k),
    IsMultiHomogIdeal V → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => 1) →
    (∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, ¬ _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) →
    Module.Finite F (MRingOver F ι ⧸ chartIdeal V i)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def SegreComponent.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (n : ℕ) (f : MRingOver F ι), IsProjVarF V (n + 1) →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => 1) → (divSupp V f).Nonempty

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ChartLatFull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [NumberField Ω]
    (y : (Σ k, ι k) → Ω), Birational y →
    ∀ (a : K → ℤ) (τ : ℕ) (s : Ω), ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ chartLat y a τ

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo

def CurveCountLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y → IsSmoothHerm A →
    IsConjInvariantH A →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      (τ : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ

namespace CurveCountLower

end CurveCountLower

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveFieldNumber.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 → Birational y → NumberField Ω

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def IsSimpleSheetPt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSheet P Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)

def PtsSheetSimpleNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      volume {y : Fin e → ℂ | ∃ w ∈ fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) ∧ ¬ IsSimpleSheetPt P Ψ w} = 0

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)

def PtsGenericCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ d : ℕ, (∀ y, (fibre P Ψ y).encard ≤ d) ∧
        volume {y : Fin e → ℂ | ¬ ((fibre P Ψ y).encard = d ∧
          ∀ w ∈ fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ)} = 0

end GroundTheory.Heights₂.Heights
end
end
