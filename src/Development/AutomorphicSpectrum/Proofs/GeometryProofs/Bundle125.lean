module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramSmoothPunctured
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle119
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Mathlib.Algebra.AffineMonoid.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem _root_.GlobalTheory.T.component_specialization_tangent_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb | exact GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_sum_comb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exterior_coeff_base_change_compat : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | exact GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.exists_conjugate_log_periods : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) → ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1, HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u = (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram | exact GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.family_exponential_conjugate : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e' : Flat.FamExp G M (Metric.ball 0 ρ) (Flat.Conj.conjPts ψ)), ∃ e : Flat.FamExp G M (Metric.ball 0 ρ) ψ, ∀ b p, p ∈ e.per b ↔ star p ∈ e'.per (star b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.exists_famExp_of_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.period_gram_smooth_punctured : ∀ (n a₀ g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → ∀ (p q : Fin r), ∀ u ∈ Flat.punct n a₀ 1, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u' => HodgeMetric.periodGram L U u' p q) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

theorem app_fst_sc_eq_zero {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V) (J : Ideal V) (U : X.Opens)
    {r : V} (hr : r ∈ J) :
    ((pullback.fst π (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom (sc π U r) = 0 := by
  let j : Spec (CommRingCat.of (V ⧸ J)) ⟶ Spec (CommRingCat.of V) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let f := pullback.fst π j
  let g := pullback.snd π j
  have e1 := Scheme.Hom.appLE_comp_appLE f π ⊤ U (f ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e0 : ∀ e : ⊤ ≤ j ⁻¹ᵁ ⊤, (j.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0 := by
    intro e
    have a1 : j.appLE ⊤ ⊤ e = j.appTop := Scheme.Hom.appLE_eq_app (f := j) (U := ⊤)
    have a2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
    have a3 : j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J r) :=
      (congrArg (fun q => q.hom r) a2).symm
    rw [a1, a3, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  have key : ∀ (w : pullback π j ⟶ Spec (CommRingCat.of V)) (_ : w = g ≫ j) (e : f ⁻¹ᵁ U ≤ w ⁻¹ᵁ ⊤),
      (w.appLE ⊤ (f ⁻¹ᵁ U) e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0 := by
    rintro _ rfl e
    rw [← Scheme.Hom.appLE_comp_appLE g j ⊤ ⊤ (f ⁻¹ᵁ U) (fun _ _ => trivial) (fun _ _ => trivial),
      CommRingCat.comp_apply]
    exact (congrArg _ (e0 (fun _ _ => trivial))).trans (map_zero _)
  have h := key (f ≫ π) pullback.condition (fun _ _ => trivial)
  rw [← e1, CommRingCat.comp_apply] at h
  have e2 : f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U := Scheme.Hom.appLE_eq_app (f := f) (U := U)
  rw [e2] at h
  exact h

theorem semiAb_props : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsIntegral G.left ∧ ∀ W : G.left.Opens, IsAffineOpen W → IsNoetherianRing Γ(G.left, W) ∧ (sc G.hom W).FiniteType ∧ ∀ p : Ideal (𝓞 L), p.IsMaximal → ∀ a b : Γ(G.left, W), a * b ∈ p.map (sc G.hom W) → a ∈ p.map (sc G.hom W) ∨ b ∈ p.map (sc G.hom W) := by
  intro L _ _ G _ _ hG
  have := hG.smooth
  have := hG.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsNoetherianRing (𝓞 L) := inferInstance
  have : IsLocallyNoetherian (Sp (𝓞 L)) := inferInstance
  have hI : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have hN : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  refine ⟨hI, fun W hW => ⟨?_, ?_, ?_⟩⟩
  · exact IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  · have h1 : (G.hom.appLE ⊤ W (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) G.hom inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv).2
    exact h1.comp h2
  · intro p hp a b hab
    letI : Field (𝓞 L ⧸ p) := Ideal.Quotient.field p
    let j : Spec (CommRingCat.of (𝓞 L ⧸ p)) ⟶ Sp (𝓞 L) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
    have hY : IsIntegral (pullback G.hom j) :=
      GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom j)
    let f := pullback.fst G.hom j
    have hker : p.map (sc G.hom W) ≤ RingHom.ker (f.app W).hom :=
      Ideal.map_le_iff_le_comap.2 fun r hr => app_fst_sc_eq_zero G.hom p W hr
    have hz : (f.app W).hom a * (f.app W).hom b = 0 := by
      rw [← map_mul]
      exact hker hab
    have hab' : (f.app W).hom a = 0 ∨ (f.app W).hom b = 0 := by
      by_cases hne : Nonempty (f ⁻¹ᵁ W)
      · exact mul_eq_zero.1 hz
      · have hb : f ⁻¹ᵁ W = ⊥ := by
          ext x
          simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hne ⟨⟨x, hx⟩⟩
        have : Subsingleton Γ(pullback G.hom j, f ⁻¹ᵁ W) := by
          rw [hb]
          infer_instance
        exact Or.inl (Subsingleton.elim _ _)
    rcases hab' with h | h
    · exact Or.inl (DVR.mem_map_of_app_fst_eq_zero G.hom p hW a h)
    · exact Or.inr (DVR.mem_map_of_app_fst_eq_zero G.hom p hW b h)

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue

theorem sc_res {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (d : R) :
    (X.presheaf.map (homOfLE h).op).hom (sc π U d) = sc π V d := by
  have e := Scheme.Hom.appLE_map π (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op
  simp only [sc, RingHom.comp_apply]
  exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) e

theorem sc_ne_zero {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) {V : X.Opens}
    [Nonempty V] {d : R} (hd : sc π ⊤ d ≠ 0) : sc π V d ≠ 0 := by
  intro h
  apply hd
  have hi := map_injective_of_isIntegral X (homOfLE (le_top : V ≤ ⊤))
  apply hi
  have := sc_res π (le_top : V ≤ ⊤) d
  rw [map_zero]
  exact this.trans h

theorem sc_cancel {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) {a b : Γ(X, V)} (h : sc π V d * a = sc π V d * b) : a = b := by
  by_cases hV : Nonempty V
  · exact mul_left_cancel₀ (sc_ne_zero π hd) h
  · have : V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hV ⟨⟨x, hx⟩⟩
    subst this
    exact Subsingleton.elim _ _

theorem exists_div {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) (x : Γ(X, V))
    (h : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom x = sc π W d * a) :
    ∃ y : Γ(X, V), x = sc π V d * y := by
  let I := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : I → X.Opens := fun i => (i.1 : X.Opens)
  choose g hg using fun i : I => h (U i) i.2 i.1.2
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    apply sc_cancel π _ hd
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, sc_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (sc π V d * (show Γ(X, V) from s))
  rw [hg i, map_mul, sc_res]
  exact congrArg _ (hs i).symm

theorem exists_sec_of_local {X : Scheme.{0}} [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X)
    (s : LB.Sec M) (δ : R) (hδ : sc π ⊤ δ ≠ 0)
    (h : ∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) :
    ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  choose y hy using fun i => exists_div π (M.U i) hδ (s.f i) (h i)
  refine ⟨⟨y, fun i j => ?_⟩, hy⟩
  apply sc_cancel π _ hδ
  have e := s.compat i j
  rw [hy i, hy j, map_mul, map_mul, sc_res, sc_res] at e
  rw [e]
  ring

theorem sec_eq_smul_of_local : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X) (s : LB.Sec M) (δ : R), sc π ⊤ δ ≠ 0 → (∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W → ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) → ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  intro X _ R _ π M s δ hδ h
  exact exists_sec_of_local R π M s δ hδ h

end GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen

theorem exists_generic_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  intro R _ _ _ G _ _ _ M hM t ht b hb
  haveI hI : IsIntegral (Sp R) := by unfold Sp; infer_instance
  haveI hN : IsLocallyNoetherian (Sp R) := by unfold Sp; infer_instance
  haveI hGI : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  haveI hGR : GeometricallyReduced G.hom := inferInstance
  haveI hRed : AlgebraicGeometry.IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.hom
  have hgen : GeneralizingMap G.hom.base := Flat.generalizingMap G.hom
  have hne : ∃ y, y ∈ Out.nonzeroLocus (M := M) t := by
    by_contra hcon
    simp only [not_exists] at hcon
    apply ht
    apply SecMod.ext
    intro k
    rw [zero_f, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    exact absurd (by unfold Out.nonzeroLocus; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hy⟩) (hcon y)
  obtain ⟨y, hy⟩ := hne
  have hle : b.asIdeal ≤ (G.hom.base y).asIdeal := by rw [hb]; exact bot_le
  have hsp : b ⤳ G.hom.base y := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨y', hy'sp, hy'eq⟩ := hgen hsp
  exact ⟨y', hy'eq, hy'sp.mem_open (Out.nonzeroLocus (M := M) t).isOpen hy⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv

theorem mem_map_of_mem_primes {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    (m : Ideal R) [hm : m.IsMaximal] (a : A)
    (h : ∀ P : Ideal A, P.IsPrime → m.map (algebraMap R A) ≤ P → a ∈ P) : a ∈ m.map (algebraMap R A) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hr : _root_.IsReduced ((R ⧸ m) ⊗[R] A) := isReduced_of_smooth_alg (R ⧸ m) _
  have hr' : _root_.IsReduced (A ⊗[R] (R ⧸ m)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R A (R ⧸ m)).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm R A (R ⧸ m)).injective
  have hq : _root_.IsReduced (A ⧸ m.map (algebraMap R A)) :=
    isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).toRingEquiv.toRingHom
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).injective
  have hrad : (m.map (algebraMap R A)).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 hq
  refine hrad ?_
  rw [Ideal.radical_eq_sInf]
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨hP, hPp⟩
  exact h P hPp hP

theorem dvd_mul_of_mem_map {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (m : Ideal R) {c e : R}
    (h : ∀ π ∈ m, e ∣ c * π) {a : A} (ha : a ∈ m.map (algebraMap R A)) :
    algebraMap R A e ∣ algebraMap R A c * a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨π, hπ, rfl⟩ := hx
    rw [← map_mul]
    exact map_dvd _ (h π hπ)
  | zero => rw [MulZeroClass.mul_zero]; exact dvd_zero _
  | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
  | smul t x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left _

theorem mem_basicOpen_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem mem_basicOpen_top_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) :
    x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hmem : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    exact (congrArg (fun U : (Sp R).Opens => p x ∈ U) e).mpr hx
  rw [← Scheme.preimage_basicOpen]
  exact hmem

theorem isUnit_cst_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 (mem_basicOpen_top_of_notMem p x hx)
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp R).Opens) from trivial)]
  exact hu

theorem cst_mul (p : X ⟶ Sp R) (x : X) (a b : R) : cst p x (a * b) = cst p x a * cst p x b := by
  simp only [cst, map_mul]
  exact gs_mul p x ⊤ trivial _ _

theorem exists_smul_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Sp R) [Smooth p] (M : LB X) (b : Sp R), b.asIdeal.IsMaximal → ∀ u : SecMod p M, (∀ y : X, p y = b → y ∉ Out.nonzeroLocus (M := M) u) → ∀ c e : R, e ≠ 0 → (∀ π ∈ b.asIdeal, e ∣ c * π) → ∃ u' : SecMod p M, e • u' = c • u := by
  intro R _ _ X p _ M b hb u hu c e he hdiv
  have key : ∀ j, ∀ x ∈ M.U j, cst p x e ∣ gs (𝟙 X) x (M.U j) (LB.Sec.f (c • u : SecMod p M) j) := by
    intro j x hx
    rw [smul_f, gs_mul _ x _ hx, gs_constFn p _ _ x hx, Category.id_comp]
    by_cases hxb : b.asIdeal ≤ (p x).asIdeal
    ·
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := M.U j) (x := x) hx
      have hle : V ≤ M.U j := hVU
      have sm := HasRingHomProperty.appLE @Smooth p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
      have sm' : RingHom.Smooth ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
        RingHom.Smooth.comp
          (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) sm
      letI := ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
      have : Algebra.Smooth R Γ(X, V) := sm'
      have hconst : ∀ r : R, algebraMap R Γ(X, V) r = constFn p V r := fun _ => rfl
      have hmem : (X.presheaf.map (homOfLE hle).op).hom (LB.Sec.f u j) ∈ b.asIdeal.map (algebraMap R Γ(X, V)) := by
        have := hb
        refine mem_map_of_mem_primes b.asIdeal _ fun P hP hbP => ?_
        let y : X := hV.fromSpec (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))
        have hbo : ∀ f : Γ(X, V), y ∈ X.basicOpen f ↔ f ∉ P := fun f => by
          have e := hV.fromSpec_preimage_basicOpen f
          have e' := congrArg (fun O : (Spec Γ(X, V)).Opens => (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ O) e
          exact iff_of_eq e'
        have hyV : y ∈ V := by
          have h4 : y ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
          rw [hV.range_fromSpec] at h4
          exact h4
        have hcl : p y = b := by
          have hle' : b.asIdeal ≤ (p y).asIdeal := fun π hπ => by
            by_contra hn
            have h2 := mem_basicOpen_top_of_notMem p y hn
            have h3 : y ∈ X.basicOpen (constFn p V π) := by
              have e : constFn p V π = (X.presheaf.map (homOfLE le_top).op).hom
                  ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)) := rfl
              rw [e]
              exact (mem_basicOpen_map le_top _ y).2 ⟨hyV, h2⟩
            exact (hbo _).1 h3 (hbP (Ideal.mem_map_of_mem _ hπ))
          exact PrimeSpectrum.ext (hb.eq_of_le (p y).isPrime.ne_top hle').symm
        by_contra hn
        have h1 := (hbo _).2 hn
        exact hu y hcl (TopologicalSpace.Opens.mem_iSup.2 ⟨j, ((mem_basicOpen_map hle _ y).1 h1).2⟩)
      obtain ⟨t, ht⟩ := dvd_mul_of_mem_map b.asIdeal hdiv hmem
      refine ⟨gs (𝟙 X) x V t, ?_⟩
      have e' := congrArg (gs (𝟙 X) x V) ht
      rw [hconst, hconst, gs_mul _ x _ hxV, gs_mul _ x _ hxV, gs_constFn p _ _ x hxV, gs_constFn p _ _ x hxV,
        gs_res _ x _ hxV, Category.id_comp] at e'
      exact e'
    ·
      obtain ⟨π, hπ, hπx⟩ := Set.not_subset.1 hxb
      have hunit := isUnit_cst_of_notMem p x hπx
      obtain ⟨t, ht⟩ := hdiv π hπ
      have h1 : cst p x e ∣ cst p x c * cst p x π := by
        rw [← cst_mul, ht, cst_mul]
        exact dvd_mul_right _ _
      exact ((hunit.dvd_mul_right).1 h1).mul_right _
  obtain ⟨s', hs'⟩ := exists_div_sec p he (show LB.Sec M from (c • u : SecMod p M)) key
  exact ⟨s', SecMod.ext fun j => (hs' j).symm⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem mem_coordLat_iff_forall_om_mem_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' :=
  PositivityTheory.Xgn.sequence_coordinates_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chartPoint_inChart_dominated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (z : Spec (CommRingCat.of (CR O y c'))), InChart 𝔐.ξ (mseg y) c' ⟨P.x z, 𝔐.all _⟩ ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) ∧ ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r :=
  @PositivityTheory.Xgn.exists_function_at_point

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end
