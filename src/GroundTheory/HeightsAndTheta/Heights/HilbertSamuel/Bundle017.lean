module

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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormMax.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ (n c : ℕ) (B : ℝ), 1 ≤ n ∧ 1 ≤ B ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) →
          ∀ S : Finset ((Σ k, ι k) → ℂ),
            (∀ z ∈ mcPts (mCoordIdeal y),
              (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
              ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ S, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * (HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) a).h z ^ τ *
                  ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n



end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormPullback.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ (n : ℕ) (M₀ : ℝ), 1 ≤ n ∧ 1 ≤ M₀ ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, s ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ F.IsHomogeneous (n * q * τ) ∧
          ∀ ζ : Fin (D + 1) → ℂ, ζ ≠ 0 →
          ∀ S : Finset ((Σ k, ι k) → ℂ),
            (∀ z ∈ mcPts (mCoordIdeal y),
              (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
              ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ S, z ∈ mcPts (mCoordIdeal y) →
              ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
                (∀ k, dg k = dh k + τ * (q * e k)) ∧ aeval y g = s * aeval y h ∧
                eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
                ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                  M * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
                    ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ M₀ ^ τ * ‖ζ‖ ^ (n * q * τ) * M ^ n


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreRepresentatives.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ ζ : Fin (D + 1) → ℂ, ∃ S : Finset ((Σ k, ι k) → ℂ),
      (∀ z ∈ S, z ∈ mcPts (mCoordIdeal y) ∧
        ∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) ∧
      ∀ z ∈ mcPts (mCoordIdeal y),
        (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
        ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def GridSeparation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ Z : Finset ((Σ k, ι k) → ℂ),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ s ∈ chartLatNm y A.a τ, ∀ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0) ∧
      ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 → ∃ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = u * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ ≤
          ‖eval z (map (Int.castRingHom ℂ) g)‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def NmSectionsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y → ∀ τ₂ : ℕ,
    ∃ (J : Type) (_ : Fintype J) (d : J → ℕ) (e : J → Ω) (τ₁ : ℕ),
      (∀ j, τ₂ ≤ d j ∧ d j ≤ τ₁ ∧ e j ∈ chartLatNm y (fun k => (a k : ℤ)) (d j)) ∧
      ∀ τ : ℕ, τ₁ ≤ τ → ∀ s ∈ chartLatNm y (fun k => (a k : ℤ)) τ,
        ∃ r : J → Ω, (∀ j, r j ∈ secM y (fun k => (τ - d j) * a k)) ∧ s = ∑ j, r j * e j

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NmSectionsRankBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ τ : ℕ, Module.Finite ℤ (chartLatNm y a τ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤ C * ((τ : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def NormalLocusRep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ (df : K → ℕ) (f : MRing ι), IsMultiHomog f df ∧ f ∉ mCoordIdeal y ∧
      ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ chartLatNm y a τ, ∀ z ∈ mcPts (mCoordIdeal y),
        eval z (map (Int.castRingHom ℂ) f) ≠ 0 →
        ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
          (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = s * aeval y h ∧
          eval z (map (Int.castRingHom ℂ) h) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ProjAvoidingForm.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (G : MvPolynomial (Fin (D + 1)) ℤ),
      (∀ k, 1 ≤ e k) ∧ (∀ j, IsMultiHomog (L j) e) ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) ∧ G ≠ 0 ∧
      ∀ ζ : Fin (D + 1) → ℂ, eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ mcPts (mCoordIdeal y),
          (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
          eval z (map (Int.castRingHom ℂ) f) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def coneNullIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : Ideal (MvPolynomial (Σ k, ι k) ℚ) :=
  Ideal.span (map (Int.castRingHom ℚ) '' (mCoordIdeal y : Set (MRing ι)) ∪
    Set.range fun j => map (Int.castRingHom ℚ) (L j))

def PullConeNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ N : ℕ, ∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∈ coneNullIdeal y L

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullFormsGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d →
      aeval (fun j => aeval y (L j)) F = 0 → F = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullSectionIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
        s / aeval y (L j) ^ (q * τ) ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))) Ω

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullSectionIntegralInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q N M : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) → (M : Ω) ≠ 0 →
    (∀ (d : K → ℕ) (g : MRing ι), IsMultiHomog g d → (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MRing ι, (∀ j, IsMultiHomog (a j) (d - e)) ∧
        (M : Ω) * aeval y g = ∑ j, aeval y (a j) * aeval y (L j)) →
    ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
      s / aeval y (L j) ^ (q * τ) ∈
        integralClosure
          (Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => aeval y (L i) / aeval y (L j)))) Ω

section Inhabitants

namespace PullSectionIntegralInt

end PullSectionIntegralInt

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
