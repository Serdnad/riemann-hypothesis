module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.RingTheory.Smooth.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.torsion_lift_is_closed_immersion : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom] (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left) (h : Γ.IsTorsionAlong G x N i), IsClosedImmersion (pullback.lift i Γ.G.hom h.isOver : Γ.G.left ⟶ pullback G.hom x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift | exact GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.finite_point_extends_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U → ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧ toUnit (genPt R) ≫ σ = Γ.pt t := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.Transl

theorem translates_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' _ g hg
  haveI := Γ.flat
  haveI := Γ.separated
  let p0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp0 : p0 ⤳ Γ.G.hom g := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨g', hg'g, hg'⟩ := Flat.generalizingMap Γ.G.hom hp0
  obtain ⟨s, x, hx⟩ := Γ.pt_onto g' (by rw [hg'])
  have hsU : (Γ.pt s).left x ∈ U := by
    rw [hx]; exact hg'g.mem_open U.isOpen hg
  have hsub : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z' := fun z z' =>
    PrimeSpectrum.ext (by
      haveI := z.isPrime
      haveI := z'.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.eq_bot_of_prime z'.asIdeal])
  have hsall : ∀ z, (Γ.pt s).left z ∈ U := fun z => hsub x z ▸ hsU
  have hinvU : ∀ z, (Γ.pt s⁻¹).left z ∈ U := by
    rw [map_inv]; exact hU.inv _ _ hsall
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point
    R T Γ U hU.finite s⁻¹ (fun z _ => hinvU z)
  refine ⟨σ, s⁻¹, hσ, ?_⟩
  set τ := (toUnit Γ.G ≫ σ) * 𝟙 Γ.G with hτ
  have hτpt : Γ.pt s ≫ τ = 1 := by
    rw [hτ, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc, comp_toUnit, hσ,
      Category.comp_id, ← Hom.mul_def, ← map_mul, inv_mul_cancel, map_one]
  have hτx : τ.left ((Γ.pt s).left x) = (η[Γ.G]).left ((toUnit (genPt R)).left x) := by
    have h1 : (Γ.pt s ≫ τ).left = (toUnit (genPt R) ≫ η[Γ.G]).left := by
      rw [hτpt, Hom.one_def]
    rw [Over.comp_left, Over.comp_left] at h1
    have h2 := congrArg (fun h => h x) h1
    simpa using h2
  have hw : (η[Γ.G]).left ≫ Γ.G.hom = 𝟙 _ := Over.w _
  haveI : UniversallyClosed ((η[Γ.G]).left ≫ Γ.G.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed (η[Γ.G]).left :=
    UniversallyClosed.of_comp_of_isSeparated _ Γ.G.hom
  have hcl : IsClosed (Set.range (η[Γ.G]).left) := by
    have h := (η[Γ.G]).left.isClosedMap _ isClosed_univ
    rwa [Set.image_univ] at h
  have hspec : τ.left ((Γ.pt s).left x) ⤳ τ.left g := by
    rw [hx]; exact hg'g.map τ.left.continuous
  have hsubset : ({τ.left ((Γ.pt s).left x)} : Set Γ.G.left) ⊆ Set.range (η[Γ.G]).left :=
    Set.singleton_subset_iff.2 ⟨_, hτx.symm⟩
  have hmem : τ.left g ∈ Set.range (η[Γ.G]).left :=
    closure_minimal hsubset hcl (specializes_iff_mem_closure.1 hspec)
  obtain ⟨z, hz⟩ := hmem
  rw [← hz]
  exact hU'.one z

end GlobalTheory.CompanionTheory.Ar.BT.Transl
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

theorem exists_germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) {y : X}
    (hs : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (a : Ω) :
    ∃ f g : X.presheaf.stalk y,
      (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g ≠ 0 ∧
      a * (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g =
        (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom f := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hzU : ξ (IsLocalRing.closedPoint Ω) ∈ U := hs.mem_open U.isOpen hyU
  let z : U := ⟨_, hzU⟩
  letI := X.presheaf.algebra_section_stalk z
  have hl := hU.isLocalization_stalk z
  obtain ⟨s, rfl⟩ := hb.2 a
  obtain ⟨⟨f, g⟩, e⟩ := IsLocalization.surj (S := X.presheaf.stalk z.1)
    (hU.primeIdealOf z).asIdeal.primeCompl s
  have hgerm : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes hs).hom (X.presheaf.germ U y hyU r) =
      X.presheaf.germ U _ hzU r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU hs) r
  refine ⟨X.presheaf.germ U y hyU f, X.presheaf.germ U y hyU g.1, ?_, ?_⟩
  · have hu : IsUnit (X.presheaf.germ U _ hzU g.1) :=
      IsLocalization.map_units (X.presheaf.stalk z.1) g
    have := hu.map (Scheme.stalkClosedPointTo ξ).hom
    simpa [hgerm] using this.ne_zero
  · have e' : s * X.presheaf.germ U _ hzU g.1 = X.presheaf.germ U _ hzU f := e
    have := congrArg (Scheme.stalkClosedPointTo ξ).hom e'
    simpa [hgerm] using this

theorem isFractionRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ →
    ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  intro X Ω _ ξ h p
  refine IsFractionRing.of_field (regAt ξ p) Ω fun a => ?_
  obtain ⟨f, g, hg, e⟩ := exists_germ_frac ξ h.bij (y := p.1) p.2 a
  refine ⟨⟨genMap ξ p f, f, rfl⟩, ⟨genMap ξ p g, g, rfl⟩, ?_⟩
  exact eq_div_of_mul_eq hg e

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torsion_along_order_divides : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one | exact GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled.pow_eq_one <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.tangent_vector_of_dual_hom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
     ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
  (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der | exact GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der | (intros; apply GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem comp_hom_apply_pointOfLocal {a b c d : CommRingCat.{0}} (A : a ⟶ b) (B : b ⟶ c) (D : a ⟶ c) (T : c ⟶ d)
    (e : A ≫ B = D) (s : a) : (B ≫ T).hom (A.hom s) = (D ≫ T).hom s := by
  subst e
  simp

theorem genMap_apply_of_specializes_pointOfLocal {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes p.2 =
      X.presheaf.stalkSpecializes q.2 := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  unfold genMap
  exact comp_hom_apply_pointOfLocal _ _ _ _ e s

theorem exists_unique_point_of_local (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R)
    (hφ : IsLocalHom φ) :
    ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  let e : X.presheaf.stalk p.1 →+* regAt ξ p := (genMap ξ p).rangeRestrict
  have he : ∀ s, ((e s : regAt ξ p) : Ω) = genMap ξ p s := fun s => rfl
  have einj : Function.Injective e := fun s t h => hξ.inj p (by rw [← he, ← he, h])
  have esurj : Function.Surjective e := (genMap ξ p).rangeRestrict_surjective
  let ψ : X.presheaf.stalk p.1 ⟶ CommRingCat.of R := CommRingCat.ofHom (φ.comp e)
  have hψ : ∀ s, ψ.hom s = φ (e s) := fun s => rfl
  have hloc : IsLocalHom ψ.hom := by
    refine ⟨fun s hs => ?_⟩
    have h1 : IsUnit (e s) := hφ.map_nonunit _ (by rwa [hψ] at hs)
    obtain ⟨b, hb⟩ := h1.exists_right_inv
    obtain ⟨t, rfl⟩ := esurj b
    have : s * t = 1 := einj (by rw [map_mul, hb, map_one])
    exact IsUnit.of_mul_eq_one t this
  let w : Σ x, { f : X.presheaf.stalk x ⟶ CommRingCat.of R // IsLocalHom f.hom } := ⟨p.1, ψ, hloc⟩
  let E := SpecToEquivOfLocalRing X (CommRingCat.of R)
  have key : ∀ y : Spec (CommRingCat.of R) ⟶ X, ∀ hc : centre y = p.1,
      (∀ s : X.presheaf.stalk (centre y),
        (Scheme.stalkClosedPointTo y).hom s =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s)) → y = E.symm w := by
    intro y hc h
    rw [Equiv.eq_symm_apply]
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨hc, ?_⟩
    ext s
    exact h s
  refine ⟨E.symm w, ?_, ?_⟩
  · have hs := E.apply_symm_apply w
    obtain ⟨hc, hT⟩ := SpecToEquivOfLocalRing_eq_iff.mp hs
    have hc' : centre (E.symm w) = p.1 := hc
    refine ⟨hc', fun a => ?_⟩
    obtain ⟨s, hsa⟩ := a.2
    have hsa' : e s = a := Subtype.ext hsa
    have hg : genPt ξ ⤳ centre (E.symm w) := hc'.symm ▸ p.2
    refine ⟨hg, (X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s, ?_, ?_⟩
    · exact (genMap_apply_of_specializes_pointOfLocal ξ ⟨_, hg⟩ p (specializes_of_eq hc') s).trans hsa
    · have h1 := congrArg (fun f => f.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) hT
      have h1' : (Scheme.stalkClosedPointTo (E.symm w)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
            ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) := h1
      have h2 : (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) = s := by
        have h3 : X.presheaf.stalkSpecializes (specializes_of_eq hc') ≫
            X.presheaf.stalkSpecializes (specializes_of_eq hc.symm) = 𝟙 _ := by
          rw [TopCat.Presheaf.stalkSpecializes_comp]
          exact TopCat.Presheaf.stalkSpecializes_refl _ _
        have h4 := congrArg (fun f => f.hom s) h3
        exact h4
      rw [h2, hψ, hsa'] at h1'
      exact h1'
  · rintro y ⟨hc, hv⟩
    refine key y hc fun s => ?_
    obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s := ⟨_, rfl⟩
    obtain ⟨hg, s1, hs1, hr⟩ := hv (e s0)
    have h1 : s1 = s := by
      apply hξ.inj ⟨_, hg⟩
      rw [hs1, he, hs0]
      exact genMap_apply_of_specializes_pointOfLocal ξ p ⟨_, hg⟩ (specializes_of_eq hc.symm) s
    rw [← hs0, hψ, ← hr, h1]

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory CptModel

namespace CoordInhab

variable {o K : Type} [CommRing o] [Field K] [Algebra o K]

theorem inv_mem_of_span_eq_top {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (S : Subring K) (h1 : ∀ a : o, algebraMap o K a ∈ S)
    (h2 : ∀ j, algebraMap o K (x j) / algebraMap o K (x c) ∈ S) : (algebraMap o K (x c))⁻¹ ∈ S := by
  have h1mem : (1 : o) ∈ Submodule.span o (Set.range x) := by
    have h : (1 : o) ∈ Ideal.span (Set.range x) := by
      rw [hx]
      exact Submodule.mem_top
    exact h
  have key : ∀ y ∈ Submodule.span o (Set.range x),
      algebraMap o K y / algebraMap o K (x c) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact h2 j
    | zero =>
      rw [map_zero, zero_div]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_div]
      exact S.add_mem hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact S.mul_mem (h1 r) hy
  have h := key 1 h1mem
  rwa [map_one, one_div] at h

theorem algebraMap_mem_regAt (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p :=
  RingHom.mem_range.2 ⟨tS p.1 a, genMap_toStalk _ p a⟩

variable [IsFractionRing o K]

theorem inChart_iff {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (p : Cpt (pt (algebraMap o K))) :
    InChart (pt (algebraMap o K)) (fun j => algebraMap o K (x j)) c p ↔ x c ∉ p.1.asIdeal := by
  have hinj := IsFractionRing.injective o K
  constructor
  · rintro ⟨hne, hrat⟩ hmem
    have hne' : algebraMap o K (x c) ≠ 0 := hne
    have hinv : (algebraMap o K (x c))⁻¹ ∈ regAt (pt (algebraMap o K)) p :=
      inv_mem_of_span_eq_top x hx c _ (algebraMap_mem_regAt p) hrat
    obtain ⟨b, s, hs, -, hbs⟩ := (mem_regAt_iff _ p _).1 hinv
    apply hs
    have hsb : algebraMap o K s = algebraMap o K (b * x c) := by
      rw [map_mul, ← hbs, mul_comm ((algebraMap o K (x c))⁻¹) (algebraMap o K s), mul_assoc,
        inv_mul_cancel₀ hne', mul_one]
    rw [hinj hsb]
    exact p.1.asIdeal.mul_mem_left b hmem
  · intro hnot
    have hne : algebraMap o K (x c) ≠ 0 := by
      intro h0
      apply hnot
      rw [(map_eq_zero_iff _ hinj).1 h0]
      exact p.1.asIdeal.zero_mem
    exact ⟨hne, fun c' => (mem_regAt_iff _ p _).2 ⟨x c', x c, hnot, hne, div_mul_cancel₀ _ hne⟩⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

end CoordInhab

open CoordInhab

theorem ValAt.unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (hξ : IsCptGen ξ) (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hs, s, hsa, rfl⟩ := h
  obtain ⟨hs', s', hsa', rfl⟩ := h'
  exact congrArg (Scheme.stalkClosedPointTo z).hom (hξ.inj ⟨centre z, hs⟩ (hsa.trans hsa'.symm))

namespace CoordInhab

end CoordInhab

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeRing

variable {X : Scheme.{0}} {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

theorem centre_specializes (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) ⤳ centre z := by
  have h := (IsLocalRing.specializes_closedPoint
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous
  exact h


set_option backward.isDefEq.respectTransparency false in
theorem stalkSpecializes_stalkClosedPointTo (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_change : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type)
    [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R')
    (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r →
    genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) →
    ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  intro X Ω _ ξ R R' _ _ _ _ ψ z a r h h'
  obtain ⟨h1, s, rfl, rfl⟩ := h
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalkSpecializes_stalkClosedPointTo ψ z)

end GlobalTheory.CompanionTheory.Ar.ChangeRing
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def Char0 (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Prop := ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p

def Pts (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Subring Ω) :=
  {R | ∃ p : Cpt ξ, Char0 ξ p ∧ R = regAt ξ p}

def IsLocAt [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (q : Ideal A) (R : Subring Ω) : Prop :=
  ∀ a : Ω, a ∈ R ↔ ∃ s : A, s ∉ q ∧ (s : Ω) * a ∈ A

structure IsSncPatch [Algebra ℚ Ω] (Pt Bd : Set (Subring Ω)) (e : ℕ) (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) :
    Prop where
  fg : A.FG
  smooth : Algebra.Smooth ℚ A
  le : n ≤ e
  li : LinearIndependent A fun i => KaehlerDifferential.D ℚ A (z i)
  span : Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤
  pts : ∀ q : Ideal A, q.IsPrime → ∃ R ∈ Pt, IsLocAt A q R ∧ (R ∈ Bd ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch

def TorusOver {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] (τ : TorusExtension G) (τ' : TorusExtension G') (φ : G'.left ⟶ G.left) : Prop :=
  letI := τ.addCommGroup
  letI := τ'.addCommGroup
  ∃ κ : τ.X ≃+ τ'.X, ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Sp L') (t' : Over.mk a ⟶ splitTorus (Sp L') τ'.X)
    (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) τ.X), (∀ χ, charVal t χ = charVal t' (κ χ)) →
      (t' ≫ τ'.i).left ≫ φ = (t ≫ τ.i).left

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch
end
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo

theorem multihomog_component_relation : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P :=
  @PositivityTheory.Xgn.homogeneous_pair_component

end GlobalTheory.CompanionTheory.Ggeo
end
