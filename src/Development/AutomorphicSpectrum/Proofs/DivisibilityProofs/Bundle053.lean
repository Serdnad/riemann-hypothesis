module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonThree
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle052
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle147
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootModelOriginCompatibility
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.good_tower_M2 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.M2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower | exact GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.root_origin_height_comparison_three : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ Rf : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (oR : RootOrigin Y ∅ Rf Fx) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (κR : Rf.K → K) (vR : (Σ k, Rf.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (iR : Rf.Ω →+* Ω), IsBlockMap κ₀ v₀ → IsBlockMap κ₁ v₁ → IsBlockMap κR vR → (∀ p, y (v₀ p) = i₀ (M₀.y p)) → (∀ p, y (v₁ p) = i₁ (M₁.y p)) → (∀ p, y (vR p) = iR (Rf.y p)) → i₀.comp o₀.g = iR.comp oR.g → i₁.comp o₁.g = iR.comp oR.g → o₀.Re.J = ⊤ → o₁.Re.J = ⊤ → oR.Re.J = ⊤ → oR.Fl.deg = 1 → IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) → ∀ (r : CMType H × Fin (D.p + D.q)) (f g : MvPolynomial (Σ k, J k) ℤ) (bf bg : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → (fun k => (bf k : ℤ) - bg k) = pullDeg κ₀ (M₀.xdeg r) - pullDeg κ₁ (M₁.xdeg r) → f ∉ mCoordIdeal y → g ∉ mCoordIdeal y → aeval y f = i₁ (o₁.e r) / i₀ (o₀.e r) * aeval y g → ∀ t, 0 < t → t ≤ Sys.t₀ → ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) f)‖ * (M₁.x t r).h (fun p => z (v₁ p)) = ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) g)‖ * (M₀.x t r).h (fun p => z (v₀ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrIso.root_isometric | exact GlobalTheory.CompanionTheory.Ar.OrIso.root_isometric | (intros; apply GlobalTheory.CompanionTheory.Ar.OrIso.root_isometric <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.extVan_section_has_cusp_form_match : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ TF.X (exOf (T.Q.Dw j) u 0), ∃ g ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ w ∈ framesOn (Y.U σ) Z, rdU (Y.U σ) f w.1 w.2 = rdU (Y.U σ) g w.1 w.2 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.extVan_section_has_cusp_form_match | exact GlobalTheory.CompanionTheory.Relay.extVan_section_has_cusp_form_match | (intros; apply GlobalTheory.CompanionTheory.Relay.extVan_section_has_cusp_form_match <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerPropA

theorem mono_spMap_ringOfIntegers (F : Type) [Field F] [NumberField F] :
    Mono (spMap (algebraMap (𝓞 F) F)) := by
  have := IsPreimmersion.of_isLocalization (S := F) (nonZeroDivisors (𝓞 F))
  exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 F) F))))

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem propA_of_origin : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : TowerOrigin Y T), IsGalois ℚ E → (∀ B a, (o.Or B a).𝔐.OmVB) → (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) → (∀ B a a', ∀ p ∈ o.S B, (o.Or B a').𝔐.R p = (o.Or B a).𝔐.R p) → T.Conv II → T.PropA II := by
  intro hpair htw II hII E _ _ _ H D l Xo c Y _ T o hgal hOm hhol hR hconv
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := mono_spMap_ringOfIntegers c.F
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hdisc : ∀ B, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.S B := by
    intro B p hp hd
    rw [o.S_iff]
    refine ⟨hp, Or.inr ?_⟩
    rw [o.bad_iff]
    exact ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  have hex : ∀ B a, ∃ t : HodgeTie Y (o.S B) (Module.finrank ℚ c.F) (T.M B a), t.A = (o.Or B a).𝔐 := by
    intro B a
    obtain ⟨-, ⟨x, hx⟩, -⟩ := HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 hinj
    exact GlobalTheory.T.prime_divisors_of_omega_bundle E H D l Xo c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) (hOm B a)
      (hdisc B) (GlobalTheory.T.root_model_origin_compatibility E H D l Xo c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx
        hmono (hhol a))
  choose tie htie using hex
  have hgen : ∀ B a, genPt (tie B a).A.ξ₀ = genPt (o.Fx a).ξf := by
    intro B a
    rw [htie B a]
    exact genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  refine GlobalTheory.T.hodge_tie_galois hpair htw II hII E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y T o.S
    (Module.finrank ℚ c.F) tie hgal hmono hconv ?_ ?_
  · intro B k k' p hp
    rw [htie B k', htie B k]
    exact hR B k k' p hp
  · intro B Φ hΦ
    refine GlobalTheory.T.hodge_ties_distinct_generic E H D l Xo c (𝓞 c.F) _ Y (o.S B) _ T.Comp (T.M B) (tie B) hmono ?_ ?_ Φ hΦ
    · intro k k' h
      apply o.comp_inj
      simpa only [hgen] using h
    · intro q hq
      obtain ⟨a, ha⟩ := o.comp_onto q hq
      exact ⟨a, (hgen B a).trans ha⟩

end GlobalTheory.CompanionTheory.Ar.TowerPropA
end
end
