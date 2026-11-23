module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Set Topology MvPolynomial ComplexSets
open scoped ContDiff Manifold

theorem exists_cutoff_near {n : ℕ} {S U : Set (Fin n → ℂ)} (hS : IsClosed S) (hU : IsOpen U)
    (hSU : S ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨V, hV, hSV, hVU⟩ := normal_exists_closure_subset hS hU hSU
  obtain ⟨f, hf1, hf0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, Fin n → ℂ) (n := ⊤) hS (t := closure V) (hSV.trans (interior_maximal subset_closure hV))
  refine ⟨f, f.contMDiff.contDiff, hf, ?_, ?_⟩
  · refine (closure_minimal (fun x hx => ?_) isClosed_closure).trans hVU
    by_contra h
    exact hx (hf0 x h)
  · obtain ⟨W, hW, hSW, hWf⟩ := mem_nhdsSet_iff_exists.1 hf1
    exact ⟨W, hW, hSW, fun x hx => hWf hx⟩

theorem exists_cutoff_near_zeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hIU : zeroSet I ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ zeroSet I ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  refine exists_cutoff_near ?_ hU hIU
  have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def PrimitiveElementFibres.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
        (Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ)),
        m.Monic ∧ m.natDegree = projDegree J A ∧ Δ ≠ 0 ∧
          ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
            (m.map (eval y)).Separable ∧
            (∀ x ∈ fibre J A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
              ∀ j, eval y Δ * x j = ((Q j).map (eval y)).eval (∑ j, c j * x j)) ∧
            ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ fibre J A y, ∑ j, c j * x j = τ

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamCritNull.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) → IsOpen N →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W) →
      volume {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} = 0

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def PrimeTubeVolume.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet J ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n : ℤ) - 2 * k))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def SmallSetTubeVolume.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet I ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

def ZeroSetOpenMass.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    ∀ (x : Fin n → ℂ) (O : Set (Fin n → ℂ)), IsOpen O → x ∈ O →
      x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
        0 < μH[((2 * d : ℕ) : ℝ)] (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

def leadForm (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent f.totalDegree f

def leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)))

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range X)

def linIdeal (A : Matrix (Fin d) (Fin n) ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range (linPoly A))

def ConeAvoids (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ) : Prop :=
  originIdeal n ^ N ≤ leadIdeal J ⊔ linIdeal A

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

variable {n d : ℕ}

def IsSheetAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin d → ℂ), IsOpen U ∧ A *ᵥ x ∈ U ∧ DifferentiableOn ℂ s U ∧ s (A *ᵥ x) = x ∧
    (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, A *ᵥ x' ∈ U → x' = s (A *ᵥ x')


open scoped Classical in
open Classical in
def sheetSum (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ∑ᶠ (x : Fin n → ℂ) (_ : x ∈ fibre J A y),
    if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0

def chartDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) y

def chartAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => |f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) y

def chartInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  ∫ y, chartDens J A f φ y


open scoped Classical in
open Classical in
def varInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  if h : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A then chartInt J h.choose f φ else 0

def SmoothNear (S : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U : Set (Fin n → ℂ), IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ ∞ φ U

def linEval (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j

def euclPot (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def energyInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (B : Set (Fin n → ℂ)) (χ : (Fin n → ℂ) → ℝ) : ℝ :=
  chartInt J A (B.indicator fun _ => 1) (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) -
    chartInt J A (B.indicator χ) (vecCons χ fun _ => euclPot)

structure VarBranch (J : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (p : Fin n → ℂ) where

  radius : ℝ
  radius_pos : 0 < radius

  toFun : (Fin k → ℂ) → Fin n → ℂ
  differentiableOn : DifferentiableOn ℂ toFun (Metric.ball 0 radius)
  injOn : Set.InjOn toFun (Metric.ball 0 radius)
  map_zero : toFun 0 = p
  mapsTo : Set.MapsTo toFun (Metric.ball 0 radius) (zeroSet J)

def VarBranch.image {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J k p) : Set (Fin n → ℂ) :=
  b.toFun '' Metric.ball 0 b.radius

def VarBranch.slice {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J (k + 1) p) : Set (Fin n → ℂ) :=
  b.toFun '' (Metric.ball 0 b.radius ∩ {t | t 0 = 0})

def VanishesToOrder {k : ℕ} (F : (Fin (k + 1) → ℂ) → ℂ) (r : ℝ) (m : ℕ) : Prop :=
  ∃ H : (Fin (k + 1) → ℂ) → ℂ, DifferentiableOn ℂ H (Metric.ball 0 r) ∧
    (∀ t ∈ Metric.ball 0 r, H t ≠ 0) ∧ ∀ t ∈ Metric.ball 0 r, F t = t 0 ^ m * H t

def IntegralIndep.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' → Measurable f →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → Integrable (chartAbsDens J A f φ) →
      Integrable (chartAbsDens J A' f φ) ∧ chartInt J A f φ = chartInt J A' f φ

def PointIntegral.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin 0 → (Fin n → ℂ) → ℝ),
    varInt (RingHom.ker (MvPolynomial.eval p)) 0 f φ = f p

def CutOff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ,
        (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
        (∀ R : ℝ, Tendsto (fun k => energyInt J A (Metric.closedBall 0 R) (χ k)) atTop (𝓝 0)) ∧
        (∀ (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), (∀ i, SmoothNear (zeroSet J) (φ i)) →
          Tendsto (fun k => ∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (χ k) φ) y) atTop (𝓝 0))

def StokesOnVariety.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → (HasCompactSupport f ∨ HasCompactSupport g) →
      varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ)

def LogIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Integrable (chartAbsDens J A
        ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖) φ)

def LocalOrder.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      localMult (J ⊔ Ideal.span {linForm u}) W = ∑ b, ord b

section Inhabitants

theorem linForm_single {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : ℂ)) = X i := by
  classical
  simp [linForm, Pi.single_apply]

theorem space_dim (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin n) ℂ))) = (n : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem smoothNear_of_contDiff {n : ℕ} {S : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ}
    (h : ContDiff ℝ ∞ φ) : SmoothNear S φ :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, h.contDiffOn⟩

theorem contDiff_euclPot (n : ℕ) : ContDiff ℝ ∞ (euclPot : (Fin n → ℂ) → ℝ) := by
  unfold euclPot
  exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) j)

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end
