module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitArchSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x) *
        ∑ σ : coordField x →+* ℂ,
          Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
            A.metric (fun k i ↦ σ (coordVec x k i)))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def ratioField (x : Cone n (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    (Set.range fun p : (k : ι) × Fin (n k + 1) × Fin (n k + 1) ↦ x p.1 p.2.1 / x p.1 p.2.2)

theorem ratioField_le_coordField (x : Cone n (AlgebraicClosure ℚ)) :
    ratioField x ≤ coordField x := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨p, rfl⟩
  exact div_mem (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.1⟩, rfl⟩)
    (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.2⟩, rfl⟩)

theorem div_mem_ratioField (x : Cone n (AlgebraicClosure ℚ)) (k : ι) (i j : Fin (n k + 1)) :
    x k i / x k j ∈ ratioField x :=
  IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i, j⟩, rfl⟩

variable [Fintype ι]

instance (x : Cone n (AlgebraicClosure ℚ)) : FiniteDimensional ℚ (ratioField x) :=
  IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral_algebraicClosure_rat y

instance (x : Cone n (AlgebraicClosure ℚ)) : NumberField (ratioField x) := {}

def orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x)) :
    Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span {F | ∃ d : ι → ℕ, Geo.IsMultiHomog (ι := blockIdx n) F d ∧
    v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k}

variable [DecidableEq ι]

theorem X_mem_orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x))
    (k : ι) (i : Fin (n k + 1)) (hi : v (coordVec x k i) < ⨆ j, v (coordVec x k j)) :
    (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∈ orbitCenter x v := by
  refine Ideal.subset_span ⟨coordDeg n ⟨k, i⟩, (geoMultiHomog_iff _ _).mpr
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, i⟩), ?_⟩
  simpa [evalCone, coordDeg, Pi.single_apply, pow_ite] using hi

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterLe.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) F d →
      v (evalCone (coordVec x) F) ≤ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartDehom.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1)).comap
            (C : ℤ →+* MvPolynomial (Coord n) ℤ) = V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) ∧
          Nonempty ((MvPolynomial (Coord n) ℤ ⧸
              (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1))) ≃+*
            (MvPolynomial (Coord n) ℤ ⧸
              (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) - 1))))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitCurve.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (x : Cone n (AlgebraicClosure ℚ)), BlockNonzero x →
    Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) 1

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitDegree.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → 0 < Geo.degC (ι := blockIdx n) (orbitIdeal x)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitDivVertical.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ¬ Geo.IsHorizontal (ι := blockIdx n) V

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitFiniteSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s,
        (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V)) =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x) *
        ∑ᶠ v : FinitePlace (coordField x),
          (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def HeightRecR.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (I : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) * height A x

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitConjSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (g : (Coord n → ℂ) → ℝ), BlockNonzero x →
    (∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) → g (fun p ↦ c p.1 * z p) = g z) →
    (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) *
        ∑ σ : coordField x →+* ℂ, g (fun p ↦ σ (coordVec x p.1 p.2)) =
      (Module.finrank ℚ (coordField x) : ℝ) *
        ∑ᶠ q : projPts (ι := blockIdx n) (orbitIdeal x),
          g (Quot.out q : Geo.mcPts (ι := blockIdx n) (orbitIdeal x))

end GroundTheory.Heights₂.Heights
end
