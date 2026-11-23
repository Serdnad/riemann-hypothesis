module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearMap
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

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Polynomial
open scoped ComplexOrder

def QuotientLength : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (c : V →ₗ[K] (Fin n → K)) (N : Submodule K V),
    LinearMap.ker c ≤ N → ∀ (X : Submodule O V) (e be : ℕ) (th : Fin n → V),
    (∀ x ∈ X, ∀ i, ∃ a : O, c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a) →
    (∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X) →
    ∀ a a' : O, a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
      let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
      ∃ m : ℕ, Module.length O (↥X ⧸ ((X ⊓ N.restrictScalars O) ⊔ Tj).comap X.subtype) = m ∧
        (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)

def PoleOrderGood : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ) (e : ℤ), 1 ≤ ep → 0 ≤ c' → 0 ≤ vet →
    ν ≤ νs + c' * vet → (∃ n : ℤ, (ep : ℝ) * ν = n) → (T : ℝ) * νs ≤ e →
      ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def PoleOrderBad : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ), 1 ≤ ep → 1 ≤ T → 0 ≤ c' → 0 ≤ vet → ν ≤ νs + c' * vet →
    let e : ℤ := ⌈(T : ℝ) * (νs + 1)⌉
    ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def LevelsSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (mm : ι → ℤ) (v : ι → ℝ) (T : ℕ) (c' : ℝ),
    (∀ z, (mm z : ℝ) ≤ ep z * T * c' * v z) →
      ∑ z, (mm z : ℝ) * f z ≤ T * c' * ∑ z, ((ep z : ℝ) * f z) * v z

end Formalism.LatticeBaseChangeAlt
end
end

section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

def LevelsChain : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T : ℕ) (e : ℤ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
    (((T : ℝ) * νs ≤ e ∧ ∀ z, ∃ n : ℤ, (ep z : ℝ) * ν z = n) ∨ e = ⌈(T : ℝ) * (νs + 1)⌉) →
      ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z

def LengthBaseChangeLocal : Prop :=
  ∀ (O O₁ Q : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O₁]
    [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra O O₁] [AddCommGroup Q] [Module O Q]
    (ϖ : O) (ϖ₁ : O₁) (u : O₁ˣ) (ε : ℕ), Irreducible ϖ → Irreducible ϖ₁ →
    algebraMap O O₁ ϖ = u * ϖ₁ ^ ε → Module.length O Q ≠ ⊤ →
      Module.length O₁ (TensorProduct O O₁ Q) = ε * Module.length O Q

end Formalism.LatticeBaseChangeAlt
end
end

section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Matrix

def ComplexHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (A : ℝ), (∀ i j, ‖M i j‖ ≤ A) →
    ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2) ∧
      ‖M.det‖ ≤ (Real.sqrt n * A) ^ n

end Formalism.LatticeBaseChangeAlt
end
end

section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset Matrix
open scoped RealInnerProductSpace BigOperators

def CompletingSquare : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (q : ℝ), 0 < q → ∀ χ : V,
      (∀ u : V, -(B χ χ / 2) / q ≤ B χ u + q * (B u u / 2)) ∧
      B χ ((-(1 / q)) • χ) + q * (B ((-(1 / q)) • χ) ((-(1 / q)) • χ) / 2) = -(B χ χ / 2) / q

def PackingCount : Prop :=
  ∀ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin n))) (δ R : ℝ), 0 < δ → δ ≤ R →
    (∀ x ∈ P, ‖x‖ ≤ R) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) →
    (P.card : ℝ) ≤ (3 * R / δ) ^ n

def DetPerturbation : Prop :=
  ∀ (𝕜 : Type) [NormedField 𝕜] (i : ℕ) (κ : Type) [Fintype κ] (w : κ → Fin i → 𝕜)
    (σ₀ : Fin i → κ) (ε : Fin i → κ → 𝕜) (Δmax : ℝ),
    (∀ σ : Fin i → κ, ‖(Matrix.of fun a j => w (σ j) a).det‖ ≤ Δmax) →
    ‖(Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det -
        (Matrix.of fun a j => w (σ₀ j) a).det‖ ≤
      ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax

def DetPerturbNumeric : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ - 1 ≤ 1 / 2

def CauchyBinetMax : Prop :=
  ∀ (i N r : ℕ) (M : Matrix (Fin i) (Fin N) ℂ), M * Mᴴ = 1 → N ≤ r →
    ∃ s : Fin i → Fin N, StrictMono s ∧ (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(M.submatrix id s).det‖

end Formalism.LatticeBaseChangeAlt
end
end

section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset

def GammaL : Prop :=
  ∀ (T D r nW n' ap am : ℝ), 0 ≤ D → 0 ≤ r → r ≤ nW → 0 ≤ n' → n' ≤ nW →
    (D + 2) * nW + 2 * r ≤ T → 40 * (D + 2) ≤ T → 1.9 * T ≤ ap → 1.9 * T ≤ am →
      max T (2 * r + n' + 2 * (T + D + 2)) ≤ ap + am + nW - r + 1

def OrderSharp : Prop :=
  ∀ (lamQ lamQs lam1 lB d' rd f : ℝ), 0 < f → 0 < rd → 0 ≤ d' → 0 ≤ lB → 0 ≤ lamQs → 0 < lam1 →
    lamQ ^ 2 ≤ (1 / 2) * lB * lamQs ^ 2 → lamQs * lam1 ≤ d' → 2 * f / rd ^ 2 ≤ lam1 ^ 2 →
      lamQ ^ 2 ≤ lB * d' ^ 2 * rd ^ 2 / (4 * f)

def NearestPlane : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) (v : Fin n → V),
    LinearIndependent ℝ v → ∀ x ∈ Submodule.span ℝ (Set.range v),
      ∃ c : Fin n → ℤ, ‖x - ∑ i, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖v i‖ ^ 2

def GaussianTailBound : Prop :=
  ∀ (ι : Type) (h : ι → ℝ) (g : ℕ) (R0 : ℝ), 0 < R0 → 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2 →
    (∀ i, R0 ≤ h i) →
    (∀ R : ℝ, R0 ≤ R → ∀ S : Finset ι, (∀ i ∈ S, h i ≤ R) → (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g)) →
      Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) ∧
        ∑' i, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)

def BallVolume : Prop :=
  ∀ (D : ℕ) (rr : ℝ), 0 < rr →
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * D))) rr) =
      ENNReal.ofReal (Real.pi ^ D * rr ^ (2 * D) / (D.factorial : ℝ))

end Formalism.LatticeBaseChangeAlt
end
end

section

open scoped BigOperators
open Polynomial Finset

namespace Formalism.LatticeBaseChangeAlt

def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)

end Formalism.LatticeBaseChangeAlt
end

section

namespace Formalism.LatticeBaseChangeAlt

def FourTermSumBound : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ : ℝ), 0 ≤ d → 0 < T → 0 < ga → 0 ≤ PP → 0 ≤ D →
    0 ≤ RR ^ 2 * c + 1 / T → κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

def FourTermSumBoundOfParameters : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ q DF g₀ : ℝ), 0 ≤ d → 0 < T → T ≤ ga → 0 < PP → 1 ≤ D →
    1 ≤ RR → 0 < q → 0 ≤ C → 0 ≤ k → 0 ≤ f → 0 ≤ b → 0 < m → 0 < δ₂ →
    κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    4 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T →
    c = RR * PP * DF ^ 2 / q → 1 ≤ g₀ → T * c * g₀ ≤ 1 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → PP ^ 2 ≤ T → 2 ≤ PP ^ 2 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

end Formalism.LatticeBaseChangeAlt
end

section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Real

def TieBoundN : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (Γ : AddSubgroup V) (x : V),
      (∀ y ∈ Γ, B x x / 2 ≤ B (x + y) (x + y) / 2) →
      ∀ g ∈ Γ, ∀ N : ℕ, 2 ≤ N →
        B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 =
            (N : ℝ) * B x g + (N : ℝ) ^ 2 * (B g g / 2) ∧
        (N : ℝ) * ((N : ℝ) - 1) * (B g g / 2) ≤
            B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 ∧
        (0 < B g g → B x x / 2 < B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2)

def DetProductRest : Prop :=
  ∀ (i c : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    ((2 : ℝ) ^ c + ε) ^ i - (2 : ℝ) ^ (c * i) ≤ (i : ℝ) * ε * ((2 : ℝ) ^ c + 1) ^ i

end Formalism.LatticeBaseChangeAlt
end
end
