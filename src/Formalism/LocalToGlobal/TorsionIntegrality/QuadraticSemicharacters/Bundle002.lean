module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

section Objects

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def wt (H : Sesq V) (z : V) : ℝ := Real.exp (-Real.pi * (H z z).re)

def kerK (H : Sesq V) (w z : V) : ℂ := Complex.exp ((Real.pi : ℂ) * H z w)

def kerP (H : Sesq V) (α : V → ℂ) (Λ : AddSubgroup V) (z w : V) : ℂ :=
  ∑' x : Λ, α (x : V) * opU H (x : V) (kerK H w) z

def termT (H : Sesq V) (α : V → ℂ) (δ : V ≃ₗ[ℂ] V) (x z : V) : ℂ :=
  α x * opU H x (kerK H z) (δ.symm z) * (wt H z : ℂ)

def gq (H : Sesq V) (Ae : V ≃ₗ[ℂ] V) (z : V) : ℂ := Complex.exp (-(Real.pi : ℂ) * H (Ae z) z)

end Objects

def DiagTerm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ v z : V,
    opU H v (kerK H z) z * (wt H z : ℂ)
      = Complex.exp (-(Real.pi : ℂ) * H v v / 2) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ))

def TermShift : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V),
    IsIsom H H (δ : V →ₗ[ℂ] V) → (∀ x, Ae x = x - δ.symm x) →
    (∀ x z, termT H α δ x z = phiC H α Ae x * gq H Ae (z - Ae.symm x)) ∧
    ∀ z, ‖gq H Ae z‖ = Real.exp (-(Real.pi / 2) * (H (Ae z) (Ae z)).re)

def FormNorm : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsHerm H →
    IsPosDef H → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z, c * ‖z‖ ^ 2 ≤ (H z z).re ∧ (H z z).re ≤ C * ‖z‖ ^ 2

def LatGaussSummable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (Λ : AddSubgroup V),
    IsLat Λ → ∀ c r : ℝ, 0 < c → ∃ u : Λ → ℝ, Summable u ∧
      ∀ (x : Λ) (z₀ : V), ‖z₀‖ ≤ r → Real.exp (-c * ‖(x : V) - z₀‖ ^ 2) ≤ u x

def GaussIntegrable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ c : ℝ, 0 < c → Integrable (fun z => Real.exp (-c * (H z z).re)) μ ∧
      0 < ∫ z, Real.exp (-c * (H z z).re) ∂μ

def ExpSeriesEntire : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Type) (c : X → ℂ) (ℓ : X → V →L[ℂ] ℂ),
    (∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖ℓ x‖)) →
    AnalyticOnNhd ℂ (fun z => ∑' x, c x * Complex.exp (ℓ x z)) Set.univ

def KerPTh : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ), IsHerm H → IsPosDef H → IsLat Λ → IsSemiChar H Λ α →
    ∀ w : V, (∀ z, Summable fun x : Λ => α (x : V) * opU H (x : V) (kerK H w) z) ∧
      (fun z => kerP H α Λ z w) ∈ Th H α Λ

def FundDomain : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : AddSubgroup V), IsLat Λ →
    ∃ D : Set V, IsAddFundamentalDomain Λ D μ ∧ Bornology.IsBounded D ∧ 0 < (μ D).toReal ∧
      ∀ Λ' : AddSubgroup V, Λ' ≤ Λ → relIdx Λ' Λ ≠ 0 →
        ∃ D' : Set V, IsAddFundamentalDomain Λ' D' μ ∧ Bornology.IsBounded D' ∧
          (μ D').toReal = relIdx Λ' Λ * (μ D).toReal

def CharIntegral : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ (Λ' : AddSubgroup V) (D' : Set V), IsAddFundamentalDomain Λ' D' μ → ∀ v ∈ dualLat H Λ', v ≠ 0 →
      ∫ z in D', Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ)) ∂μ = 0

def GaussQuad : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsHerm H → IsPosDef H →
    ∀ δ Ae : V ≃ₗ[ℂ] V, IsIsom H H (δ : V →ₗ[ℂ] V) → (∀ x, Ae x = x - δ.symm x) →
    Integrable (gq H Ae) μ ∧
    ∫ z, gq H Ae z ∂μ = ((∫ z, wt H z ∂μ : ℝ) : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)

def DiagIntegral : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ Λ₂ : AddSubgroup V) (α : V → ℂ),
    IsHerm H → IsPosDef H → IsLat Λ → IsSelfDual H Λ → IsSelfDual H Λ₂ → IsSemiChar H Λ α →
    IsSemiChar H Λ₂ α → ∀ D' : Set V, IsAddFundamentalDomain (Λ ⊓ Λ₂ : AddSubgroup V) D' μ →
    Bornology.IsBounded D' → ∀ y ∈ Λ₂,
      ∫ z in D', α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) ∂μ
        = by classical exact if y ∈ Λ then ((μ D').toReal : ℂ) else 0

def UnfoldIntegral : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ)
    (δ Ae : V ≃ₗ[ℂ] V), IsLat Λ → UnitaryData H Λ α δ Ae → ∀ D' : Set V,
    IsAddFundamentalDomain (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ : AddSubgroup V) D' μ → Bornology.IsBounded D' →
    ∀ S : Finset V, IsReps (latA Λ δ Ae) Λ S →
      ∫ z in D', kerP H α Λ (δ.symm z) z * (wt H z : ℂ) ∂μ = (∑ x ∈ S, phiC H α Ae x) * ∫ z, gq H Ae z ∂μ

def SelfDualCovolume : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ),
    IsHerm H → IsPosDef H → IsLat Λ → IsSelfDual H Λ → IsSemiChar H Λ α → AtMostLine H α Λ →
    ∀ D : Set V, IsAddFundamentalDomain Λ D μ → Bornology.IsBounded D → (μ D).toReal = ∫ z, wt H z ∂μ

def KerPNonzero : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (Λ : AddSubgroup V) (α : V → ℂ), IsHerm H → IsPosDef H → IsLat Λ → IsSelfDual H Λ → IsSemiChar H Λ α →
    ∃ w z : V, kerP H α Λ z w ≠ 0

end Formalism.L2.Th1.H
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def F0 (L : PeriodPair) (ω₀ : ℂ) (n : Type*) [Fintype n] : (n → ℂ) → ℂ :=
  prodFn fun _ : n => Formalism.L2.Th1.F.th0 L (ω₀ / 2)

def stdChar (L : PeriodPair) (ω₀ : ℂ) {n : Type*} [Fintype n] (x : n → ℂ) : ℂ :=
  ∏ i, Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ (x i)

def qOf {V : Type*} [AddCommGroup V] [Module ℂ V] (c : ℝ) (H : Sesq V) (x : V) : ℝ := c * (H x x).re

def alphaQ {V : Type*} [AddCommGroup V] [Module ℂ V] (c : ℝ) (H : Sesq V) (x : V) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (qOf c H x : ℂ))

def StdSelfDual : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n], IsSelfDual (stdH L n) (stdLat L n)

def StdSemiChar : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n], ω₀ ∈ L.lattice →
    IsSemiChar (stdH L n) (stdLat L n) (stdChar L ω₀)

def ProductThetaMem : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n], ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ α : (n → ℂ) → ℂ, (∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) →
      F0 L ω₀ n ∈ Th (stdH L n) α (stdLat L n) ∧ F0 L ω₀ n 0 = 1

def ThStd : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n], ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ α : (n → ℂ) → ℂ, (∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) →
      ∀ F ∈ Th (stdH L n) α (stdLat L n), F = F 0 • F0 L ω₀ n

def Tens4Mem : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ)
    (θ : Fin 4 → (n → ℂ) → ℂ), (∀ a, θ a ∈ Th (matH h) α Λ) →
      (fun v => ∏ a, θ a (slice a v)) ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ)

def FourthRoot : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ), α 0 = 1 →
    ∀ P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ), P ≠ 0 →
    (∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ), ∃ c : ℂ, G = c • P) →
    (∃ θ ∈ Th (matH h) α Λ, tens4 θ = P) ∧
    ∀ θ ∈ Th (matH h) α Λ, tens4 θ = P →
      (∀ θ' ∈ Th (matH h) α Λ, tens4 θ' = P → ∃ ζ : ℂ, ζ ^ 4 = 1 ∧ θ' = ζ • θ) ∧
      ∀ F ∈ Th (matH h) α Λ, ∃ c : ℂ, F = c • θ

structure StdData (L : PeriodPair) (ω₀ : ℂ) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : Prop where
  per : ω₀ ∈ L.lattice
  half : ω₀ / 2 ∉ L.lattice
  isom : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
  alpha0 : α 0 = 1
  betaStd : ∀ x ∈ stdLat L (Fin 4 × n), β x = stdChar L ω₀ x
  betaSemi : IsSemiChar (stdH L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β
  betaAlpha : ∀ x, β (g x) = ∏ a, α (slice a x)
  selfDual : IsSelfDual (stdH L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
  idx₁ : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0
  idx₂ : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat L (Fin 4 × n)) ≠ 0

def kernel4 (L : PeriodPair) (ω₀ : ℂ) {n : Type} [Fintype n] [DecidableEq n] (Λ : AddSubgroup (n → ℂ))
    (β : (Fin 4 × n → ℂ) → ℂ) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (z : Fin 4 × n → ℂ) : ℂ :=
  inter (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (F0 L ω₀ (Fin 4 × n)) (g z)

def ThetaVector : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), StdData L ω₀ h Λ α β g → ∀ κ : ℂ, κ ≠ 0 →
    (∃ θ ∈ Th (matH h) α Λ, tens4 θ = κ • kernel4 L ω₀ Λ β g) ∧
    ∀ θ ∈ Th (matH h) α Λ, tens4 θ = κ • kernel4 L ω₀ Λ β g → θ ≠ 0 ∧
      (∀ θ' ∈ Th (matH h) α Λ, tens4 θ' = κ • kernel4 L ω₀ Λ β g → ∃ ζ : ℂ, ζ ^ 4 = 1 ∧ θ' = ζ • θ) ∧
      ∀ F ∈ Th (matH h) α Λ, ∃ c : ℂ, F = c • θ

def AlphaQSemi : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (b : ℤ) (d : ℕ), Odd b →
    ∀ Λ : AddSubgroup V, Λ ≤ dualLat H Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λ) →
    (∀ x ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H x = (m : ℝ)) ∧
    (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H (x + y) - qOf (Real.sqrt d / 2) H x
        - qOf (Real.sqrt d / 2) H y - altE H x y = 2 * (m : ℝ)) ∧
    IsSemiChar H Λ (alphaQ (Real.sqrt d / 2) H)

def AlphaQRules : Prop :=
  (∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W)
    (g : V →ₗ[ℂ] W), IsIsom H H' g → ∀ (c : ℝ) (x : V), alphaQ c H' (g x) = alphaQ c H x) ∧
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ) (c : ℝ) (x : Fin 4 × n → ℂ),
    alphaQ c (matH (blk4 h)) x = ∏ a, alphaQ c (matH h) (slice a x)

def CmStdChar : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d), 4 * (a : ℤ) * c = b ^ 2 + d → Odd a → d % 8 = 7 →
    ∀ (n : Type) [Fintype n] [DecidableEq n], ∀ x ∈ stdLat (Formalism.L2.Th1.F.cmPair a b d ha hd) n,
      alphaQ (Real.sqrt d / 2) (stdH (Formalism.L2.Th1.F.cmPair a b d ha hd) n) x
        = stdChar (Formalism.L2.Th1.F.cmPair a b d ha hd) (a : ℂ) x

end Formalism.L2.Th1.H
end
end
