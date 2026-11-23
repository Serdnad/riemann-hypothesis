module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Covering.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def RankDeficientFibreInfinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
    (∀ v ∈ U, ¬ Function.Injective (fderiv ℂ f v)) →
      ∃ y : Fin m → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

noncomputable section

def RiemannExtensionAnalytic.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g f : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U →
    (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0) →
    DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}) →
    (∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0}))) →
    ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U ∩ {t | g t ≠ 0})

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Matrix
open scoped ENNReal

noncomputable section

def pairPt {k m : ℕ} (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun j => y j))

def coordGraph {n : ℕ} (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | (fun i : P => z i) ∈ Ω ∧ ∀ j, j ∉ P → z j = F (fun i : P => z i) j}

def frameProj {n : ℕ} (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i : I => e.repr z i)

def ProjectionFormula.Statement : Prop :=
  ∀ (n d : ℕ) (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ),
    P.card = d → IsOpen Ω → DifferentiableOn ℂ F Ω →
    ∀ (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
      (B : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet B →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coordGraph P Ω F ∩ B) =
        ∑ I ∈ Finset.powersetCard d (Finset.univ : Finset (Fin n)),
          ∫⁻ x : EuclideanSpace ℂ I,
            (({z | z ∈ coordGraph P Ω F ∩ B ∧ frameProj e I z = x}.encard : ℕ∞) : ℝ≥0∞)
            ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ))


def PolySublevel.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 → ∀ R : ℝ, 0 < R →
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)
          {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 R ∧ ‖eval (fun i => x i) Q‖ ≤ η} ≤
        ENNReal.ofReal (C * η ^ α)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def RootSumHolomorphic.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (W : Set (Fin d → ℂ)) (Φ : (Fin d → ℂ) → ℂ → ℂ),
    m.Monic → IsOpen W → (∀ y ∈ W, (m.map (MvPolynomial.eval y)).Separable) →
    (∀ y ∈ W, ∀ τ : ℂ, (m.map (MvPolynomial.eval y)).IsRoot τ →
      ∃ O : Set ((Fin d → ℂ) × ℂ), IsOpen O ∧ (y, τ) ∈ O ∧ ∃ Ψ : (Fin d → ℂ) × ℂ → ℂ,
        DifferentiableOn ℂ Ψ O ∧
        ∀ p ∈ O, (m.map (MvPolynomial.eval p.1)).IsRoot p.2 → Φ p.1 p.2 = Ψ p) →
    DifferentiableOn ℂ (fun y => ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum) W

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def CriticalFlatNotInjective.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (a : Fin k → ℂ),
    2 ≤ k → IsOpen U → DifferentiableOn ℂ f U → a ∈ U →
    LinearMap.det (fderiv ℂ f a : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
    (∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 → fderiv ℂ f b = 0) →
    ¬ Set.InjOn f U

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicJacobianNeZero.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      ∀ x ∈ U, LinearMap.det (fderiv ℂ f x : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolomorphicKernelFibre.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (b : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → b ∈ U →
    ∀ d : ℕ, Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) = d →
      ∃ (V : Set (Fin d → ℂ)) (y : Fin d → ℂ) (γ : (Fin d → ℂ) → Fin k → ℂ)
        (ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ),
        IsOpen V ∧ y ∈ V ∧ DifferentiableOn ℂ γ V ∧ Set.MapsTo γ V U ∧ Set.InjOn γ V ∧
          (∀ s ∈ V, ∀ t ∈ V, ℓ (f (γ s)) = ℓ (f (γ t)) → f (γ s) = f (γ t)) ∧
          fderiv ℂ (fun t => ℓ (f (γ t))) y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory

noncomputable section

def CriticalImageNull.Statement : Prop :=
  ∀ (d n : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → Fin n → ℂ), IsOpen U →
    DifferentiableOn ℂ f U →
      μH[((2 * d : ℕ) : ℝ)] (f '' {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)}) = 0

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

noncomputable section

def FibreSectionsCovering.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (Ω : Set (Fin (e + 1) → ℂ))
    (X : Set (Fin n → ℂ)) (hX : Set.MapsTo (fun x => A *ᵥ x) X Ω),
    (∀ y ∈ Ω, {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    IsCoveringMap hX.restrict

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def SliceMatricesOpen.Statement : Prop :=
  ∀ (n k m : ℕ) (γ : Fin m → (Fin (k + 1) → ℂ) → Fin n → ℂ) (s : Fin m → Fin (k + 1) → ℂ),
    (∀ b, DifferentiableAt ℂ (γ b) (s b)) →
    (∀ b (v : Fin (k + 1) → ℂ), v 0 = 0 → fderiv ℂ (γ b) (s b) v = 0 → v = 0) →
      IsOpen {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} ∧
        {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))}.Nonempty

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Pointwise

variable {n d : ℕ}

def linPoly (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A (Pi.single j 1) i) * X j

def projAlgHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  aeval fun i => Ideal.Quotient.mk J (linPoly A i)

def IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) : Prop :=
  Function.Injective (projAlgHom J A) ∧ (projAlgHom J A).toRingHom.Finite

def unitaryRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {M | M * M.conjTranspose = 1}

def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    (∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
        (∃ M : Matrix (Fin d) (Fin n) ℂ, ∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) ∧
        ∀ M : Matrix (Fin d) (Fin n) ℂ,
          (∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) → IsFiniteProjection J M.mulVecLin) ∧
      (∃ M : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J M.mulVecLin) ∧
      (∀ D ⊆ unitaryRows d n, unitaryRows d n ⊆ closure D →
        ∃ M ∈ D, IsFiniteProjection J M.mulVecLin) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) ℂ),
        (∀ k, F k ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((U * F k).conjTranspose.submatrix s id).mulVecLin))

def lineMap : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval ![X 0, 0]

def lineIdeal : Ideal (MvPolynomial (Fin 2) ℂ) := RingHom.ker lineMap

theorem lineMap_surjective : Function.Surjective lineMap := by
  intro p
  refine ⟨rename (fun _ : Fin 1 => (0 : Fin 2)) p, ?_⟩
  have h : ((![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) ℂ) ∘ fun _ : Fin 1 => (0 : Fin 2)) = X := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  simp only [lineMap, aeval_rename, h, aeval_X_left_apply]

def lineEquiv : (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.quotientKerAlgEquivOfSurjective lineMap_surjective

theorem lineIdeal_dim : ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ lineIdeal) = (1 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv lineEquiv.toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

def lineProj : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.proj 0

theorem lineEquiv_projAlgHom (p : MvPolynomial (Fin 1) ℂ) :
    lineEquiv (projAlgHom lineIdeal lineProj p) = p := by
  have h : (lineEquiv.toAlgHom.comp (projAlgHom lineIdeal lineProj)) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [Fin.fin_one_eq_zero i]
    simp [projAlgHom, lineEquiv, linPoly, lineProj, lineMap, Fin.sum_univ_two]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk lineMap_surjective (X 0)).trans
      (by simp [lineMap])
  exact congrArg (fun f => f p) h

theorem lineProj_finite : IsFiniteProjection lineIdeal lineProj := by
  have hinj : Function.Injective (projAlgHom lineIdeal lineProj) :=
    Function.LeftInverse.injective lineEquiv_projAlgHom
  have hsurj : Function.Surjective (projAlgHom lineIdeal lineProj) := by
    intro q
    refine ⟨lineEquiv q, lineEquiv.injective ?_⟩
    rw [lineEquiv_projAlgHom]
  exact ⟨hinj, RingHom.Finite.of_surjective _ hsurj⟩

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval (0 : Fin n → ℂ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

def CircleArgumentPrinciple.Statement : Prop :=
  ∀ (h : ℂ → ℂ) (O : Set ℂ) (c : ℂ) (r : ℝ),
    0 < r → IsOpen O → closedBall c r ⊆ O → DifferentiableOn ℂ h O → (∀ s ∈ sphere c r, h s ≠ 0) →
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) ∧
      ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ O →
        (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv h s / h s) = (Z.map φ).sum

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
