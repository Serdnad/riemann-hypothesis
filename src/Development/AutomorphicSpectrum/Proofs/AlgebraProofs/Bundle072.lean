module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle071
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAbelianVarietyPTorsion
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
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

open GlobalTheory.FiniteAmple

theorem exists_finFree_away_of_finitePresentation {A B : Type} [CommRing A] [CommRing B] {φ : A →+* B}
    (hf : φ.Finite) (hfl : φ.Flat) (hfp : φ.FinitePresentation) (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, ∀ {A' B' : Type} [CommRing A'] [CommRing B'] {α : A →+* A'} {β : B →+* B'}
      {φ' : A' →+* B'},
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β)
        (CommRingCat.ofHom φ') →
      IsUnit (α r) → FinFree φ' := by
  apply GlobalTheory.FiniteAmpleFP.exists_finFree_away_fp <;> assumption

theorem finiteFreeHom_comp_isIso {A B C : CommRingCat.{0}} (f : A ⟶ B) (e : B ⟶ C) [IsIso e]
    (h : FinFree f.hom) : FiniteFreeHom (f ≫ e).hom := by
  obtain ⟨hfin, hfree⟩ := h
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A C := (f ≫ e).hom.toAlgebra
  haveI : Module.Finite A B := hfin
  haveI : Module.Free A B := hfree
  let eR : B ≃+* C := (asIso e).commRingCatIsoToRingEquiv
  let eA : B ≃ₐ[A] C := AlgEquiv.ofRingEquiv (f := eR) (fun a => rfl)
  exact ⟨Module.Free.of_equiv eA.toLinearEquiv, Module.Finite.equiv eA.toLinearEquiv⟩

theorem exists_affine_finiteFreeHom {Y S : Scheme.{0}} (g : Y ⟶ S) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] (s : S) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧ FiniteFreeHom (g ∣_ W).appTop.hom := by
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  have hfin : (g.app V).hom.Finite := IsFinite.finite_app g V hV
  have hfl : (g.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @Flat g ‹_› ⟨V, hV⟩ ⟨_, hV.preimage g⟩ _
  have hfp : (g.app V).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @LocallyOfFinitePresentation g ‹_› ⟨V, hV⟩
      ⟨_, hV.preimage g⟩ _
  obtain ⟨r, hr, F⟩ := exists_finFree_away_of_finitePresentation hfin hfl hfp
    (PrimeSpectrum.comap (S.presheaf.germ V s hsV).hom (IsLocalRing.closedPoint _))
  have hsW : s ∈ S.basicOpen r := by
    rw [Scheme.mem_basicOpen _ _ _ hsV]
    by_contra hnu
    apply hr
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hWV : S.basicOpen r ≤ V := S.basicOpen_le r
  have hW : IsAffineOpen (S.basicOpen r) := hV.basicOpen r
  have hpush := GlobalTheory.FiniteAmple.isPushout_app g hV hW hWV
  have hu : IsUnit ((S.presheaf.map (homOfLE hWV).op).hom r) := by
    haveI := hV.isLocalization_basicOpen r
    exact IsLocalization.Away.algebraMap_isUnit r
  have key : FinFree (g.app (S.basicOpen r)).hom :=
    F (α := (S.presheaf.map (homOfLE hWV).op).hom) (φ' := (g.app (S.basicOpen r)).hom) hpush hu
  refine ⟨S.basicOpen r, hsW, hW, ?_⟩
  have key' : FinFree (g.app ((Scheme.Hom.opensFunctor (S.basicOpen r).ι).obj ⊤)).hom := by
    rw [Scheme.Opens.ι_image_top]
    exact key
  have aux : ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (p : B = C), FinFree f.hom →
      FiniteFreeHom (f ≫ eqToHom p).hom := by
    intro A B C f p hf
    subst p
    rw [eqToHom_refl]
    exact finiteFreeHom_comp_isIso f (𝟙 _) hf
  rw [morphismRestrict_appTop, eqToHom_op, eqToHom_map]
  exact aux _ _ key'

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem abFactor_prod_retract : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → (∀ (N₁ N₂ : Type) [AddCommGroup N₁] [AddCommGroup N₂] (M₁ : Submodule R (N₁ → C)) (M₂ : Submodule R (N₂ → C)), IsAbFactor p M₁ → IsAbFactor p M₂ → IsAbFactor p (tens M₁ M₂)) ∧ ∀ (N₁ N₂ : Type) [AddCommGroup N₁] [AddCommGroup N₂] (M : Submodule R (N₂ → C)) (i : N₁ →+ N₂) (π : N₂ →+ N₁), (∀ x, π (i x) = x) → (∀ g ∈ M, (fun x => g (i (π x))) ∈ M) → IsAbFactor p M → IsAbFactor p (M.map (LinearMap.funLeft R C (i : N₁ → N₂))) :=
  @PositivityTheory.HtPt.Rg.abfac_prod

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.pure_family_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (n : ℕ), IsPure hP x → (∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x)) → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) ∧ (∀ y ∈ PureType.lat hP (sgnRt H true), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))) ∧ ∀ y ∈ PureType.lat hP (sgnRt H false), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.pure_family_spans_pure_sublattice | exact GlobalTheory.CompanionTheory.Ar.Fl.pure_family_spans_pure_sublattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.pure_family_spans_pure_sublattice <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.pure_type_lattices_orthogonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (a b : D.La), a ∈ PureType.lat hP (sgnRt H true) → b ∈ PureType.lat hP (sgnRt H false) → sesq D a b = 0 ∧ sesq D b a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure | exact GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure | (intros; apply GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  first | exact @PositivityTheory.Xgf.exists_local_basis_cm_order | exact PositivityTheory.Xgf.exists_local_basis_cm_order
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | exact GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | (intros; apply GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_factor_tight_field_action : SubquotientStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, (∀ x : N, p • x = 0) → IsAbFactor p AA.carrier → IsTight v p AA.carrier → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw] (i : Nw →+ N) (π : N →+ Nw), (∀ y, π (i y) = y) → (∀ h ∈ AA.carrier, (fun x => h (i (π x))) ∈ AA.carrier) → FStable F (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) → ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ → FlagConcl v p (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) b σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flagConcl_directFactor_of_subquotient | exact GlobalTheory.CompanionTheory.Ar.GR.flagConcl_directFactor_of_subquotient | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flagConcl_directFactor_of_subquotient <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polarised_abelian_variety_p_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∃ (P : Out.PolAV (Spec (CommRingCat.of R))) (z : sp (R₀ := R) R ⟶ P.A), P.g = 1 ∧ z ^ p = 1 ∧ ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.exists_ord_point | exact GlobalTheory.CompanionTheory.Ar.GR.exists_ord_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.exists_ord_point <;> assumption)
end
