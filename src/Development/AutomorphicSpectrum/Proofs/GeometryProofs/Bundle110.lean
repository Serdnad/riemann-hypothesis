module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle094
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.coord_valuation_bound_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L)
    (v : FinitePlace L) (A : Type) [CommRing A] [IsLocalRing A] [Algebra A L] (zA : Sp A ⟶ X),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ r : A, v (algebraMap A L r) ≤ 1) → (∀ r : A, v (algebraMap A L r) = 1 → IsUnit r) →
    CoordsAt ξ y (spMap (algebraMap A L) ≫ zA) w →
    ∃ (c : (k : K) → J k) (h : genPt ξ ⤳ centre zA), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
      (∀ k i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c k⟩)) ∧
      InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zA, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite | exact GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

theorem _root_.GlobalTheory.T.proper_pullback_line_bundle : ∀ (X₀ Xg X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξg : Spec (CommRingCat.of Ω) ⟶ Xg) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (L : Lat ξ Ω) (T : Set (Cpt ξ)) (t : Ω), IsPreimmersion e → IsProper f → IsLocallyNoetherian Xg → ξg ≫ e = ξ → ξ' ≫ f = ξg → IsCptGen ξ → NormalCpt ξ → (∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) → L.IsVBOn T 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' (f ≫ e) (AddMonoidHom.id _)).IsGenAt p' t) → ∀ x ∈ T, L.IsGenAt x t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends | exact GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.connected_special_fibre_constant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt | exact GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.unitAt_of_localLifts_of_unitAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.regular_sections_open_neighbourhood : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li),
    IsCptGen ξ → SmoothOfRelativeDimension g G.hom →
    ∀ (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li),
      (∀ j, S j ∈ M.lat p) → (∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) →
      ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
        (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem genPt_specializes_of_injective {Ω : Type} [Field Ω] {R : CommRingCat.{0}} [IsDomain R]
    (φ : R ⟶ CommRingCat.of Ω) (hφ : Function.Injective φ.hom) (q : Spec R) :
    genPt (Spec.map φ) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (genPt (Spec.map φ) : PrimeSpectrum R) q).1 ?_
  intro a ha
  have hm : φ.hom a ∈ IsLocalRing.maximalIdeal Ω := ha
  have h0 : φ.hom a = 0 := by
    by_contra hne
    exact hm (isUnit_iff_ne_zero.2 hne)
  have : a = 0 := hφ (h0.trans (map_zero φ.hom).symm)
  rw [this]
  exact zero_mem _

theorem lift_transfer {X X' W W' V : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    (e : X' ≅ X) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (hξ : ξ' ≫ e.hom = ξ)
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) (hdom : ∀ p : X', IsDomain (X'.presheaf.stalk p))
    (sW : W ⟶ Sp R) (hproj : IsProjOver sW)
    (f : X ⟶ W) (f' : X' ⟶ W') (j : V ⟶ W) (j' : V ⟶ W') [Mono j'] (Ψ : V ≅ V) (x x' : Sp Ω ⟶ V)
    (hx : x' ≫ Ψ.inv = x) (hf : ξ ≫ f = x ≫ j) (hf' : ξ' ≫ f' = x' ≫ j') (p : X')
    (hu : ∃ u' : Spec (X'.presheaf.stalk p) ⟶ V, u' ≫ j' = X'.fromSpecStalk p ≫ f') :
    ∃ u : Spec (X.presheaf.stalk (e.hom p)) ⟶ V, u ≫ j = X.fromSpecStalk (e.hom p) ≫ f := by
  obtain ⟨u', hu'⟩ := hu
  haveI := hdom p
  have h' : ξ' (IsLocalRing.closedPoint Ω) ⤳ p := hall p
  let φ : X'.presheaf.stalk p ⟶ CommRingCat.of Ω := X'.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ'
  let ξp : Sp Ω ⟶ Spec (X'.presheaf.stalk p) := Spec.map φ
  have hξp : ξp ≫ X'.fromSpecStalk p = ξ' := by
    simp only [ξp, φ]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have hgp : ∀ q, genPt ξp ⤳ q := genPt_specializes_of_injective φ (hgen.inj ⟨p, hall p⟩)
  have hxu : ξp ≫ u' = x' := by
    rw [← cancel_mono j', Category.assoc, hu', ← Category.assoc, hξp, hf']
  have heq : u' ≫ Ψ.inv ≫ j = X'.fromSpecStalk p ≫ e.hom ≫ f := by
    refine GlobalTheory.T.eq_of_eq_generic_projective R (Spec (X'.presheaf.stalk p)) W sW Ω ξp _ _ hproj hgp ?_
    have h1 : ξp ≫ u' ≫ Ψ.inv ≫ j = x ≫ j := by rw [reassoc_of% hxu, reassoc_of% hx]
    have h2 : ξp ≫ X'.fromSpecStalk p ≫ e.hom ≫ f = x ≫ j := by rw [reassoc_of% hξp, reassoc_of% hξ, hf]
    rw [h1, h2]
  haveI : IsIso (e.hom.stalkMap p) := inferInstance
  refine ⟨inv (Spec.map (e.hom.stalkMap p)) ≫ u' ≫ Ψ.inv, ?_⟩
  rw [Category.assoc, Category.assoc, heq, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, IsIso.inv_hom_id_assoc]

end GlobalTheory.CompanionTheory.Ar.TwistInterior

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem interior_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hf hf' hfst hsnd _ _ _ z
  have hΦ' : Φ.inv ≫ Xo.s = Xo.s := (Iso.inv_comp_eq Φ).2 hΦ.symm
  let ΦF : Xo.XF c ≅ Xo.XF c :=
    { hom := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.hom)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ, pullback.condition])
      inv := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.inv)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ', pullback.condition])
      hom_inv_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.hom_inv_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp])
      inv_hom_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp]) }
  have hxx : x ≫ ΦF.hom = x' := by
    apply pullback.hom_ext
    · simp only [ΦF, Category.assoc, pullback.lift_fst, hfst]
    · simp only [ΦF, Category.assoc, pullback.lift_snd, hsnd]
  obtain ⟨hjY, hA⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O β Y S Ω K J y A (z ≫ e.hom) hβ
  obtain ⟨hjY', hA'⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O' β' Y' S Ω K J y A' z hβ'
  have hc : centre (z ≫ e.hom) = e.hom (centre z) := rfl
  rw [hA, hA', hc]
  constructor
  · exact lift_transfer e A.ξ A'.ξ hξ A'.tie.gen A'.all (fun p => (A'.normal p).1) Y.s Y.proj A.f A'.f Y.j Y'.j
      ΦF x x' (by rw [← hxx, Category.assoc, Iso.hom_inv_id, Category.comp_id]) hf hf' (centre z)
  · intro hu
    have key := lift_transfer e.symm A'.ξ A.ξ (by rw [← hξ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      A.tie.gen A.all (fun p => (A.normal p).1) Y'.s Y'.proj A'.f A.f Y'.j Y.j ΦF.symm x' x
      (by rw [Iso.symm_inv, hxx]) hf' hf (e.hom (centre z)) hu
    have hp : e.symm.hom (e.hom (centre z)) = centre z := by
      rw [Iso.symm_hom, ← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    rwa [hp] at key

end GlobalTheory.CompanionTheory.Ar.TwistInterior
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)


theorem _root_.GlobalTheory.T.flag_basis_lin_indep_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (t : CMType H ⊕ CMType H),
    LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis.flag_b_basis | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis.flag_b_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis.flag_b_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem _root_.GlobalTheory.T.analytic_chart_unit_section : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U N : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T t : Ω) (v : Γ(X, N)) (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsCptGen ξ → IsChart s B Y → b₁ ∈ B → (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) → N ≤ U → (∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W) → IsUnit v → (∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N), genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T) → T ≠ 0 → ExtendsUnitAt s (RingHom.id ℂ) ξ W F t (Y b₁) → ∃ (B₂ : Set (Fin d → ℂ)) (H : (Fin d → ℂ) → ℂ), b₁ ∈ B₂ ∧ HChart s ξ W U F T B₂ Y H := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.cp_element_divides_prime_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A), IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | exact GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.log_denominator_bound_primes : ∀ (S : Finset ℕ) (m₀ : ℕ), (∀ p ∈ S, p.Prime) → 0 < m₀ → ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ Real.log m ≤ q * (Real.log m₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) (κ : Ω), (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) → ∀ t : Ω, ((m₀ : Ω) * κ) * t ∈ W → (m : Ω) * t ^ q ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ClearConstants.clear_constants | exact GlobalTheory.CompanionTheory.Ar.ClearConstants.clear_constants | (intros; apply GlobalTheory.CompanionTheory.Ar.ClearConstants.clear_constants <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

theorem _root_.GlobalTheory.T.flag_height_bound_arith_var : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (q : Cpt 𝔐.ξ), (∀ p ∈ S, p ∉ S₀ → ¬ InFibre 𝔐.ξ p q) → ∀ r, (Fl.shrink S₀ h hvb hsub).rootLat r q = Fl.rootLat r q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.rootLat_shrink_eq | exact GlobalTheory.CompanionTheory.Ar.Num.rootLat_shrink_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.rootLat_shrink_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.root_origin_point_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (x : o.Re.R.X) (x' : o₀.Re.R.X) (w₁ : (Σ k, M.ι k) → ℂ) (w₂ : (Σ k, R.ι k) → ℂ) (v : RootIx D → ℝ) (t : ℝ), 0 < t → t ≤ Sys.t₀ → w₁ ∈ mcPts M.P → w₂ ∈ mcPts R.P → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w₁ → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') w₂ → o.Re.π x = o₀.Re.π x' → o.Re.π x ∈ Sys.open' → (∀ r, 0 < v r ∧ v r * (o₀.sing r).h w₂ = (o.sing r).h w₁) → ∀ (τ : CMType H) (p : Fin (D.p + D.q)), -∑ k ∈ Finset.Iic p, (Real.log ((M.x t (τ, k)).h w₁) - Real.log ((R.x 1 (τ, k)).h w₂) - Real.log (v (τ, k))) = Sys.phT (some (τ, p)) t (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) + ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket | exact GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.component_open_stalks_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ U' : (Xo.XF c).Opens, (U' : Set (Xo.XF c)) = U ∧ ∀ p : Xo.XF c, p ∈ U → IsDomain ((Xo.XF c).presheaf.stalk p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain | exact GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain <;> assumption)
end
