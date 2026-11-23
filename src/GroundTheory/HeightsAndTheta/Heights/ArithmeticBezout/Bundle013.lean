module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeSlabBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖}) ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeHyperplaneNull.proof (hZ : ZeroLocusDimH.Statement) (hC : ChowFormDimLe.Statement) :
    ConeHyperplaneNull.Statement := by
  intro n e h W f u hW hf hu
  have := hW.isPrime
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {linForm u} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) := by
    have h1 := hC ℂ n (e + 1) W f hW hf
    have hr : Ideal.Quotient.mk W (linForm u) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left : W ≤ J))
      (Ideal.Quotient.factor_surjective _) hr
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have h3 := h2.trans h1
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = a at h3 ⊢
    induction a using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h3 (by norm_cast)
      | coe m =>
        have : m + 1 ≤ e + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : m ≤ e)

  let g : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hg : ∀ y, g y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective g := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz g).mp hinj

  have hsub : coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0} ⊆
      g ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, hyu⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]

      simpa [linForm, map_sum] using hyu
    intro q hq
    rw [hg]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) <
      (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealNeBotDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    incIdeal Q k ≠ ⊥ → ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((k : ℕ) : WithBot ℕ∞)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncidenceZeroLocus.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsHomogIdeal Q →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] (v : Fin k × Fin n → Ω),
      (∀ g ∈ incIdeal Q k, aeval v g = 0) →
        ∃ y : Fin n → Ω, y ≠ 0 ∧ (∀ q ∈ Q, aeval y q = 0) ∧ ∀ i, ∑ j, v (i, j) * y j = 0

section Inhabitants

attribute [local instance] MvPolynomial.gradedAlgebra

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ThroughPointIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)) (x c : Fin n → AlgebraicClosure F),
    ∑ j, c j * x j = 1 →
    (∀ u : Fin k × Fin n → AlgebraicClosure F, (∀ i, ∑ j, u (i, j) * x j = 0) → u ∈ incidence Q k) →
      ∀ g ∈ incIdeal Q k, aeval (genSubst (k := k) x c) g = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ThroughTwoPointsTrdeg.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] (n k : ℕ) [Algebra K Ω]
    [Algebra (MvPolynomial (Fin k × Fin n) K) Ω] [IsScalarTower K (MvPolynomial (Fin k × Fin n) K) Ω],
    Function.Injective (algebraMap (MvPolynomial (Fin k × Fin n) K) Ω) →
    ∀ x c : Fin n → K, ∑ j, c j * x j = 1 →
    ∀ (y : Fin n → Ω) (j : Fin n), y j ≠ 0 → (∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m)) →
      (∀ i, ∑ m, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (genSubst x c (i, m)) * y m = 0) →
        (k : Cardinal) ≤ Algebra.trdeg K (Algebra.adjoin K (Set.range fun m => y m * (y j)⁻¹))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def GraphAreaIntegral.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω → ∀ A ⊆ Ω, MeasurableSet A →
    ∀ h : EuclideanSpace ℂ (Fin n) → ℝ≥0∞,
      ∫⁻ y in graphPt e F '' A, h y ∂(μH[((2 * d : ℕ) : ℝ)]) =
        ∫⁻ x in A, h (graphPt e F x) * ENNReal.ofReal (areaJacobian
          (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)))
          ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def HolomorphicImplicitGraph.Statement : Prop :=
  ∀ (n m : ℕ) (f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ) (y : EuclideanSpace ℂ (Fin n))
    (V : Set (EuclideanSpace ℂ (Fin n))),
    (∀ i, ContDiff ℂ 1 (f i)) → IsOpen V → y ∈ V → (∀ i, f i y = 0) →
    finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m →
      ∃ (e : Fin n ≃ Fin m ⊕ Fin (n - m)) (Ω : Set (EuclideanSpace ℂ (Fin m)))
        (Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)))
        (U : Set (EuclideanSpace ℂ (Fin n))),
        IsOpen U ∧ y ∈ U ∧ U ⊆ V ∧ IsOpen Ω ∧ DifferentiableOn ℂ Φ Ω ∧
        graphPt e Φ '' Ω = {z | z ∈ U ∧ ∀ i, f i z = 0} ∧
        ∀ x ∈ Ω, LinearMap.range (fderiv ℂ (graphPt e Φ) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) =
          ⨅ i, LinearMap.ker (fderiv ℂ (f i) (graphPt e Φ x) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def projVar (e : ℕ) (i : Fin (e + 1)) : FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (X i)

def projPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) :
    Vertical.Par e n → FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
  | .inl (i, j) =>
      projVar e i.succ * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) -
        projVar e 0 * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A i.succ j)
  | .inr j => algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) / projVar e 0

def ProjSecDegree.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    ComplexSets.projDegree J A =
      Module.finrank (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
        (Vertical.SecAlg
          (J.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeGe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k E) g y) ≠ 0 →
        Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ∧
          δ ≤ Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeLe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      IsDomain (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Algebra.IsSeparable E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Vertical.specRest (algebraMap k E) g y ≠ 0 →
        Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ≤ δ

namespace SecDegreeLe

end SecDegreeLe

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecFiniteUnit.Statement : Prop :=
  ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R), IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      IsUnit (eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k R) g y)) →
        Module.Finite R (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k R))) y)

end

end GroundTheory.Heights₂.Heights
end
