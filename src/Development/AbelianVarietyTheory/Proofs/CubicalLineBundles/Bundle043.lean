module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdeal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegLatticeNumberFieldExtensionEq
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28

@[expose] public section

section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM

namespace GlobalTheory.LamF

theorem deg_eq_ndeg_of_line : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (Λ : Submodule (𝓞 K) V) (v : V) (ℓ : MLine K),
    v ≠ 0 → ℓ.Good → (∀ z, z ∈ Λ ↔ ∃ c ∈ ℓ.I, z = c • v) → (∀ s, ℓ.n s ^ 2 = (h.form s v v).re) →
    deg h Λ = ℓ.ndeg := by
  intro K _ _ V _ _ _ _ h Λ v ℓ hv hℓ hΛ hn
  rw [GlobalTheory.CM.deg_ideal_smul h Λ hv (m := fun s => ℓ.n s ^ 2) (fun s => pow_pos (hℓ.2 s) 2)
    (fun s => (hn s).symm) hℓ.1 (fun z => (hΛ z).trans ⟨fun ⟨c, a, b⟩ => ⟨c, b, a⟩, fun ⟨c, a, b⟩ => ⟨c, b, a⟩⟩),
    MLine.ndeg, MLine.deg, meanLog]
  simp only [Real.log_pow, ← Finset.mul_sum, Nat.cast_ofNat]
  ring

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.two_mul_deg_dual_line_cmIdeal : ∀ (E K V : Type) [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (Λ : Submodule (𝓞 K) V) (v : V) (τ : E →+* K) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (β : E) (n : (K →+* ℂ) → ℝ), 𝔞 ≠ 0 → v ≠ 0 → (∀ s, 0 < n s) → (∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) → (∀ s, (h.form s v v).re = (s (τ β)).re * n s) → (∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ ∀ b ∈ 𝔞, IsIntegral ℤ (t * τ (β * IsCMField.complexConj E b))) →
  2 * deg h Λ = (2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ β : ℚ)|) / Module.finrank ℚ E - meanLog K n := by
  first | exact @GlobalTheory.CM.two_mul_deg_dual_line | exact GlobalTheory.CM.two_mul_deg_dual_line | (intros; apply GlobalTheory.CM.two_mul_deg_dual_line <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.deg_lattice_numberField_extension_eq : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ) (h : HermFam K (Fin n → K)) (h' : HermFam K' (Fin n → K')) (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → (∀ s a b, h'.form s (Pi.single a 1) (Pi.single b 1) = h.form (s.comp j) (Pi.single a 1) (Pi.single b 1)) → deg h' (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Λ : Set (Fin n → K)))) = deg h Λ := by
  first | exact @GlobalTheory.deg_span_image_eq | exact GlobalTheory.deg_span_image_eq | (intros; apply GlobalTheory.deg_span_image_eq <;> assumption)
end
