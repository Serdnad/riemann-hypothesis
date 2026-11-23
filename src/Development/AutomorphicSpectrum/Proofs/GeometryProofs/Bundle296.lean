module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle295
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpans
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalModelPowerFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle135
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.torsion_periods_finite_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period | exact GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

theorem _root_.GlobalTheory.T.hodge_cpt_multihomog_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c), A.ξ ≫ A.f = x ≫ Y.j → Mono (spMap β) → ∃ (b : MRing ι) (d : K → ℕ), IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w b ≠ 0 → ∃ z : Spec (CommRingCat.of ℂ) ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior | exact GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.period_lattice_spans : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Submodule.span ℂ (e.per b) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.span_per_eq_top | exact GlobalTheory.CompanionTheory.Ar.Flat.span_per_eq_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.span_per_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.global_model_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b) → PowFns Ygl.t ∧ ∀ (p : ℕ), p.Prime → ∀ z : Ygl.X, (p : Ygl.X.residueField z) = 0 → FibPF Ygl.t z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GlobalFib.global_fibPF | exact GlobalTheory.CompanionTheory.Ar.GlobalFib.global_fibPF | (intros; apply GlobalTheory.CompanionTheory.Ar.GlobalFib.global_fibPF <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hol_unif_period_matrix_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → (∀ y ∈ e.per b, ℓ y ∈ u.Λ) ∧ ∀ p ∈ u.Λ, ∃ y ∈ e.per b, ℓ y = p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.periods_map_onto_lattice <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem prop_snd_of_isPullback (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    {X Y S' S : Scheme.{0}} {φ : X ⟶ Y} {a : X ⟶ S'} {b : Y ⟶ S} {f : S' ⟶ S}
    (h : IsPullback φ a b f) (ha : P a) : P (pullback.snd b f) := by
  have sq : IsPullback h.isoPullback.inv (pullback.snd b f) a (𝟙 S') :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact P.of_isPullback sq ha

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

theorem abelianScheme_descends_to_fg_subring : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ :=
  GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring_anyDim

end GlobalTheory.CompanionTheory.Ar.Approx
end
end
