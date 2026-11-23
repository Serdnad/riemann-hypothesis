module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle018
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CgSplit
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle007
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle019
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle020
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot


theorem _root_.GlobalTheory.T.mem_orbit_self' : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left), x ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | exact GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot


theorem _root_.GlobalTheory.T.mem_orbit_trans : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left), y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.locallyOfFinitePresentation_of_cancel : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q → LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) → LocallyOfFinitePresentation f := by
  first | exact @GlobalTheory.CompanionTheory.LfpDescent.descends | exact GlobalTheory.CompanionTheory.LfpDescent.descends | (intros; apply GlobalTheory.CompanionTheory.LfpDescent.descends <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Split

theorem isotropic_residue_injective_splits : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 :=
  @PositivityTheory.HtPt.Cg.split_local

end GlobalTheory.CompanionTheory.Ar.Split
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem addChar_mem_hopfOrder : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier :=
  @PositivityTheory.HtPt.Ra.charmem

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_pow_section_associated_global_element : ∀ (F Ω X : Type) [Field F] [NumberField F] [Field Ω] (φ : F →+* Ω) (R : X → Subring Ω) (s : X → Ω) (pl : X → Option (HeightOneSpectrum (𝓞 F))) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ x, ∀ z : Ω, IsIntegral (R x) z → z ∈ R x) → (∀ x, pl x = none → (∀ a : F, φ a ∈ R x) ∧ s x ∈ R x ∧ s x ≠ 0 ∧ (s x)⁻¹ ∈ R x) → (∀ x v, pl x = some v → (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ R x) ∧ ∃ (m : ℕ) (n : ℤ) (π : F), 0 < m ∧ (n : ℚ) = m * r v ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ s x ≠ 0 ∧ s x ^ m / φ π ^ n ∈ R x ∧ φ π ^ n / s x ^ m ∈ R x) → ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧ ∀ x, s x ^ M / φ α ∈ R x ∧ φ α / s x ^ M ∈ R x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_integral_posDef_perturbation : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places | exact GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem _root_.GlobalTheory.T.ideal_descending_one_dim_quotient : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A] (χ : A →ₐ[k] k) (e : A) (J : Ideal A), IsIdempotentElem e → χ e = 1 → (∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) → J ≤ Ideal.span {e} → J ≠ ⊥ → ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧ (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧ (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | exact GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one <;> assumption)
end
