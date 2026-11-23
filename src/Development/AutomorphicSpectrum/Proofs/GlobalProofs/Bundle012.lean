module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import GroundTheory.LocalFields.PadicLogSeries
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SphericalZetaCosets
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle001
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle011
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePower
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
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.ZetaSph

theorem zeta_spherical : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → ∀ (κ : Measure (GL (Fin c) F)), κ.IsMulLeftInvariant → κ (GLint O c : Set (GL (Fin c) F)) = 1 → ∀ σ : ℝ, (∀ i, ‖α i‖ * (q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) < 1) → IntegrableOn (fun g => φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ)) (Mint O c) κ ∧ ∫ g in Mint O c, φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ) ∂κ = ∏ i : Fin c, (1 - α i * (((q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) : ℝ) : ℂ))⁻¹ :=
  _root_.UpperTheory.Reformulated.B.SphericalZetaCosets.zeta_spherical

end GlobalTheory.CompanionTheory.ZetaSph
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.isClosed_cartier_locus_support : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt <;> assumption)
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.finitely_many_open_subgroups_bounded_index : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧ Module.finrank F E ≤ N}.Finite) → ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) | IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | exact GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite <;> assumption)
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.normal_subgroup_le_unramified_fixing : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), NS Ω S ≤ (maxUnramifiedOutside (F := F) (Ω := Ω) S).fixingSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | exact GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.NS_le_fixingSubgroup <;> assumption)
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.galois_unramified_outside_cohomology : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | exact GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS | (intros; apply GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.different_dvd_ramified_prime_power : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 → (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) → differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  first | exact @GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | exact GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | (intros; apply GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow <;> assumption)
end
