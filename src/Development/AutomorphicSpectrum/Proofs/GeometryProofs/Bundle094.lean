module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle083
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle017
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeTrivialMod
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c)
    (h' : genPt ξ ⤳ c') (s : X.presheaf.stalk c) :
    genMap ξ ⟨c', h'⟩ (X.presheaf.stalkSpecializes (specializes_of_eq hc) s) = genMap ξ ⟨c, h⟩ s := by
  subst hc
  simp [TopCat.Presheaf.stalkSpecializes_refl]

theorem closedPoint_specMap_fromSpecStalk {R : CommRingCat.{0}} [IsLocalRing R] (x : X)
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x ((Spec.map φ) (IsLocalRing.closedPoint R)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

private theorem stalkSpecializes_comp_comp_eq_of_eq {x y : X} (h1 : x ⤳ y) (h2 : y ⤳ x) (hxy : x = y)
    {R : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ R) :
    X.presheaf.stalkSpecializes h2 ≫ X.presheaf.stalkSpecializes h1 ≫ g = g := by
  subst hxy
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem stalkSpecializes_stalkClosedPointTo {K : Type} [Field K] (x : X)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom φ.hom]
    (hc : (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint (CommRingCat.of K)) = x) :
    X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = φ := by
  have key := (SpecToEquivOfLocalRing (X := X) (R := CommRingCat.of K)).apply_symm_apply ⟨x, ⟨φ, inferInstance⟩⟩
  obtain ⟨h, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp key
  rw [show Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = _ from h2,
    TopCat.Presheaf.stalkCongr_hom]
  exact stalkSpecializes_comp_comp_eq_of_eq _ _ hc.symm φ

private theorem isLocalHom_of_field' {K K' : Type} [Field K] [Field K'] (f : K →+* K') : IsLocalHom f :=
  ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩

theorem valAt_of_field_map {K K' : Type} [Field K] [Field K'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (w : Spec (CommRingCat.of K) ⟶ X) (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K')
    (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') {a : Ω} {u : K} (hv : ValAt ξ w a u) :
    ValAt ξ w' a (f u) := by
  obtain ⟨h, s, hs, hr⟩ := hv
  subst e
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X.presheaf.stalk (centre w) ⟶ CommRingCat.of K',
      ψ = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := ⟨_, rfl⟩
  haveI : IsLocalHom ψ.hom := by
    haveI := isLocalHom_of_field' f
    have hh : ψ.hom = f.comp (Scheme.stalkClosedPointTo w).hom := by
      subst hψ
      rfl
    rw [hh]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ f (Scheme.stalkClosedPointTo w).hom (isLocalHom_of_field' f)
      (Scheme.isLocalHom_stalkClosedPointTo w)
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk w
  have hw' : Spec.map (CommRingCat.ofHom f) ≫ w = Spec.map ψ ≫ X.fromSpecStalk (centre w) := by
    rw [hψ]
    erw [Spec.map_comp, Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom f) ≫ ·) hφ.symm
  rw [hw']
  have hc := closedPoint_specMap_fromSpecStalk (centre w) ψ
  have hc' : centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) = centre w := hc
  have h' : genPt ξ ⤳ centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) := by
    rw [hc']
    exact h
  refine ⟨h', X.presheaf.stalkSpecializes (specializes_of_eq hc') s, ?_, ?_⟩
  · exact (genMap_stalkSpecializes ξ hc' h h' s).trans hs
  · have H3 := stalkSpecializes_stalkClosedPointTo (centre w) ψ hc
    have H : (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
        Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk (centre w))).hom s = ψ.hom s :=
      congrArg (fun g => g.hom s) H3
    have hψs : ψ.hom s = f u := by
      rw [← hr]
      subst hψ
      rfl
    exact H.trans hψs

theorem valAt_complex : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  intro X Ω _ ξ L _ _ z σ a u hv
  exact valAt_of_field_map ξ _ _ σ (by rw [← Category.assoc]; congr 1; exact (Spec.map_comp _ _).symm) hv

end GlobalTheory.CompanionTheory.Ar.RootHt.PullVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.PushLoc

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξg : Spec (CommRingCat.of Ω) ⟶ Y} {e : Y ⟶ X}

theorem dominates_id (h : ξg ≫ e = ξ) : Dominates ξg ξ e (RingHom.id Ω) := by
  have h0 : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
  unfold Dominates
  rw [h0, Category.id_comp, h]

def emb (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) : Cpt ξ := ⟨e p.1, hD.specializes p⟩

theorem genMap_stalkMap (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) (s : X.presheaf.stalk (e p.1)) :
    genMap ξg p ((e.stalkMap p.1).hom s) = genMap ξ (emb hD p) s :=
  PullReg.stalkMap_comp_genMap hD p (hD.specializes p) s

theorem regAt_emb [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) :
    regAt ξg p = regAt ξ (emb hD p) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 s
    exact ⟨s', (genMap_stalkMap hD p s').symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, genMap_stalkMap hD p s⟩

theorem isCptGen_of [IsPreimmersion e] (h : ξg ≫ e = ξ) (hg : IsCptGen ξ) : IsCptGen ξg := by
  subst h
  have hD : Dominates ξg (ξg ≫ e) e (RingHom.id Ω) := dominates_id rfl
  refine ⟨?_, fun p => ?_⟩
  · have hb := hg.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb
    have hs := Scheme.Hom.stalkMap_surjective e (ξg (IsLocalRing.closedPoint Ω))
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      have : a' = b' := hb.1 hab
      rw [this]
    · intro c
      obtain ⟨a, rfl⟩ := hb.2 c
      exact ⟨_, rfl⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 a
    obtain ⟨b', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 b
    have h1 := genMap_stalkMap hD p a'
    have h2 := genMap_stalkMap hD p b'
    have : a' = b' := hg.inj (emb hD p) (h1.symm.trans (Eq.trans hab h2))
    rw [this]

theorem isIntegral_congr {R S : Subring Ω} (h : R = S) {a : Ω} (ha : IsIntegral R a) : IsIntegral S a := by
  subst h
  exact ha

theorem normalCpt_of [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (hn : NormalCpt ξ) :
    NormalCpt ξg := by
  intro p a ha
  rw [regAt_emb hD p]
  exact hn (emb hD p) a (isIntegral_congr (regAt_emb hD p) ha)

theorem coe_span_eq {R S : Subring Ω} (h : R = S) (M : Submodule S Ω) :
    ((Submodule.span R (M : Set Ω) : Submodule R Ω) : Set Ω) = M := by
  subst h
  rw [Submodule.span_eq]

theorem eq_span_of_coe {R S : Subring Ω} (h : R = S) {N : Submodule R Ω} {M : Submodule S Ω}
    (hNM : (N : Set Ω) = M) {A : Set Ω} (hM : M = Submodule.span S A) : N = Submodule.span R A := by
  subst h
  exact (SetLike.coe_injective hNM).trans hM

theorem coe_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) (p : Cpt ξg) :
    ((L.pull ξg e (AddMonoidHom.id Ω) p : Submodule (regAt ξg p) Ω) : Set Ω) = L (emb hD p) := by
  rw [Lat.pull_apply L hD]
  have h0 : (AddMonoidHom.id Ω) '' (L (emb hD p) : Set Ω) = (L (emb hD p) : Set Ω) := Set.image_id _
  exact (congrArg (fun A : Set Ω => ((Submodule.span (regAt ξg p) A : Submodule _ Ω) : Set Ω)) h0).trans
    (coe_span_eq (regAt_emb hD p) _)

theorem isVBOn_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) {T : Set (Cpt ξ)}
    (hT : ∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) (h : L.IsVBOn T 1 ⊤) :
    (L.pull ξg e (AddMonoidHom.id Ω)).IsVBOn Set.univ 1 ⊤ := by
  have hmem : ∀ p : Cpt ξg, emb hD p ∈ T := fun p => (hT _).2 ⟨p.1, rfl⟩
  intro p _
  obtain ⟨U, hU, b, hb, hq⟩ := h (emb hD p) (hmem p)
  refine ⟨e ⁻¹ᵁ U, hU, b, hb, fun q _ hqU => ?_⟩
  obtain ⟨h1, h2⟩ := hq (emb hD q) (hmem q) hqU
  exact ⟨h1, eq_span_of_coe (regAt_emb hD q) (coe_pull hD L q) h2⟩

theorem pull_pull_eq [IsPreimmersion e] {X' : Scheme.{0}} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ Y}
    (hD : Dominates ξg ξ e (RingHom.id Ω)) (hD' : Dominates ξ' ξg f (RingHom.id Ω))
    (hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω)) (L : Lat ξ Ω) (p' : Cpt ξ') :
    (L.pull ξg e (AddMonoidHom.id Ω)).pull ξ' f (RingHom.id Ω).toAddMonoidHom p' =
      L.pull ξ' (f ≫ e) (AddMonoidHom.id Ω) p' := by
  rw [Lat.pull_apply _ hD', Lat.pull_apply _ hD'']
  congr 1
  have h1 := coe_pull hD L ⟨f p'.1, hD'.specializes p'⟩
  have h2 : emb hD ⟨f p'.1, hD'.specializes p'⟩ = ⟨(f ≫ e) p'.1, hD''.specializes p'⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply f e p'.1).symm
  rw [h1, h2]
  rfl

theorem gen_descends : ∀ (X₀ Xg X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξg : Spec (CommRingCat.of Ω) ⟶ Xg) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (L : Lat ξ Ω) (T : Set (Cpt ξ)) (t : Ω), IsPreimmersion e → IsProper f → IsLocallyNoetherian Xg → ξg ≫ e = ξ → ξ' ≫ f = ξg → IsCptGen ξ → NormalCpt ξ → (∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) → L.IsVBOn T 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' (f ≫ e) (AddMonoidHom.id _)).IsGenAt p' t) → ∀ x ∈ T, L.IsGenAt x t := by
  intro X₀ Xg X' Ω _ ξ ξg ξ' e f L T t hpre hprop hloc h1 h2 hgen hnorm hT hVB hG x hx
  haveI := hpre
  haveI := hprop
  haveI := hloc
  have hD : Dominates ξg ξ e (RingHom.id Ω) := dominates_id h1
  have hD' : Dominates ξ' ξg f (RingHom.id Ω) := dominates_id h2
  have hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω) := dominates_id (by rw [← Category.assoc, h2, h1])
  obtain ⟨z, hz⟩ := (hT x).1 hx
  have hs : genPt ξg ⤳ z := by
    have h3 : e (genPt ξg) ⤳ e z := by
      rw [hD.map_genPt, hz]
      exact x.2
    exact (e.isEmbedding.isInducing.specializes_iff).1 h3
  have hp : (L.pull ξg e (AddMonoidHom.id Ω)).IsGenAt ⟨z, hs⟩ t :=
    GlobalTheory.T.line_bundle_normal_proper_pullback Xg Ω ξg X' Ω ξ' f (RingHom.id Ω) hD' Function.bijective_id (isCptGen_of h1 hgen)
      (normalCpt_of hD hnorm) (L.pull ξg e (AddMonoidHom.id Ω)) Set.univ ⟨z, hs⟩ t (isVBOn_pull hD L hT hVB)
      (fun _ _ => trivial) (fun p' _ => by
        have h4 := hG p'
        refine ⟨h4.1, ?_⟩
        rw [pull_pull_eq hD hD' hD'' L p']
        exact h4.2)
  have hx' : x = emb hD ⟨z, hs⟩ := Subtype.ext hz.symm
  rw [hx']
  exact ⟨hp.1, eq_span_of_coe (regAt_emb hD _).symm (coe_pull hD L _).symm hp.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PushLoc
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem unitAt_of_localLifts_of_unitAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) :=
  @PositivityTheory.Xgn.function_on_connected_fibre_unit

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ (W : X.Opens) (t : Γ(X, W)) (q : Cpt ξ) (hq : q.1 ∈ W) (hW : genPt ξ ∈ W) :
    genMap ξ q (X.presheaf.germ W q.1 hq t) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW t) := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hq q.2 t)

theorem regAt_near {p : Cpt ξ} {a : Ω} (h : a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → a ∈ regAt ξ q := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨W, hp, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  have hW : genPt ξ ∈ W := p.2.mem_open W.isOpen hp
  refine ⟨W, hp, fun q hq => ⟨X.presheaf.germ W q.1 hq t, ?_⟩⟩
  rw [genMap_germ W t q hq hW, genMap_germ W t p hp hW]

theorem regAt_near_finset {p : Cpt ξ} (A : Finset Ω) (h : ∀ a ∈ A, a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → ∀ a ∈ A, a ∈ regAt ξ q := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ ha => absurd ha (Finset.notMem_empty _)⟩
  | insert a A _ ih =>
    obtain ⟨W, hp, hW⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨W', hp', hW'⟩ := regAt_near (h a (Finset.mem_insert_self a A))
    refine ⟨W ⊓ W', ⟨hp, hp'⟩, fun q hq b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hW' q hq.2
    · exact hW q hq.1 b hb

theorem lie_near (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (g : ℕ) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) (hG : SmoothOfRelativeDimension g G.hom)
    (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li)
    (hS : ∀ j, S j ∈ M.lat p) (hΦ : ∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  classical
  obtain ⟨U, hpU, b, -, hb⟩ := (GlobalTheory.T.lie_lattice_vector_bundle_of_smooth X G g Ω ξ Li M hξ hG).1 p (Set.mem_univ p)
  have hbp := (hb p (Set.mem_univ p) hpU).2
  have hc : ∀ j, ∃ c : Fin g → regAt ξ p, ∑ s, c s • b s = S j := fun j => by
    have := hS j
    rw [hbp] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose c hc using hc
  have hΦb : ∀ j s, Φ j (b s) ∈ regAt ξ p := fun j s =>
    hΦ j _ (by rw [hbp]; exact Submodule.subset_span ⟨s, rfl⟩)
  obtain ⟨W, hpW, hW⟩ := regAt_near_finset (ξ := ξ) (p := p)
    (Finset.univ.image (fun js : Fin n × Fin g => (c js.1 js.2 : Ω)) ∪
      Finset.univ.image (fun js : Fin n × Fin g => Φ js.1 (b js.2))) (by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact (c js.1 js.2).2
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact hΦb js.1 js.2)
  refine ⟨U ⊓ W, ⟨hpU, hpW⟩, fun q hq => ?_⟩
  have hbq := (hb q (Set.mem_univ q) hq.1).2
  have hcq : ∀ j s, (c j s : Ω) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  have hΦq : ∀ j s, Φ j (b s) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  refine ⟨fun j => ?_, fun j e he => ?_⟩
  · rw [hbq, ← hc j]
    refine Submodule.sum_mem _ fun s _ => ?_
    have : (c j s) • b s = (⟨c j s, hcq j s⟩ : regAt ξ q) • b s := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · rw [hbq] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact hΦq j s
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul r x _ hx =>
      have : Φ j (r • x) = (r : Ω) * Φ j x := by
        show Φ j ((r : Ω) • x) = _
        simp
      rw [this]
      exact mul_mem r.2 hx

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.wedge_line_lattice_trivial_mod : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (ϖ : Ω), IsCptGen ξ → ϖ ≠ 0 → (∀ x, ϖ ∈ regAt ξ x) → A.IsVB p V → B.IsVB q V' → a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt A B p q a b x f) → ExactModLat A B ϖ (p + q) → TrivMod (lineLat A B p q a b) ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat | exact GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_regAt_genPt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
  obtain ⟨g, hg⟩ := h.bij.2 a
  refine ⟨g, ?_⟩
  rw [← hg]
  simp only [genMap, genPt, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rfl

theorem genPt_mem_genFibre_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (O : Type) [CommRing O] [Algebra O Ω]
    (hi : Function.Injective (algebraMap O Ω)) :
    (⟨genPt ξ, specializes_refl _⟩ : Cpt ξ) ∈ genFibre O ξ := fun o ho =>
  ⟨fun h0 => ho (hi (by rw [h0, map_zero])), mem_regAt_genPt_of_isCptGen h _,
    mem_regAt_genPt_of_isCptGen h _⟩

theorem mem_lat_genFibre_iff_const_mul : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t : Ω), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∀ u : Ω, (∀ p ∈ genFibre O ξ, u ∈ L p) ↔ ∃ x y : O, y ≠ 0 ∧ u * algebraMap O Ω y = algebraMap O Ω x * t := by
  intro X Ω _ ξ O _ _ _ s _ hs hi hξ hc L t ht u
  have ht0 : t ≠ 0 := (ht _ (genPt_mem_genFibre_of_isCptGen hξ O hi)).1
  constructor
  · intro hu
    have hreg : ∀ p ∈ genFibre O ξ, u / t ∈ regAt ξ p := by
      intro p hp
      have h1 := hu p hp
      rw [(ht p hp).2] at h1
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
      replace hc : (c : Ω) * t = u := hc
      rw [← hc, mul_div_cancel_right₀ _ ht0]
      exact c.2
    obtain ⟨x, y, hy, e⟩ := hc _ ((GlobalTheory.T.regular_everywhere_isIntegral X Ω ξ O s hs hi hξ (u / t)).2 hreg)
    refine ⟨x, y, hy, ?_⟩
    rw [← e]
    field_simp
  · rintro ⟨x, y, hy, e⟩ p hp
    rw [(ht p hp).2]
    have hx : algebraMap O Ω x ∈ regAt ξ p := by
      by_cases h0 : x = 0
      · rw [h0, map_zero]; exact zero_mem _
      · exact (hp x h0).2.1
    have hyu := hp y hy
    refine Submodule.mem_span_singleton.2 ⟨⟨_, mul_mem hx hyu.2.2⟩, ?_⟩
    change algebraMap O Ω x * (algebraMap O Ω y)⁻¹ * t = u
    have := hyu.1
    rw [mul_right_comm, ← e]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.weil_pairing_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (n : ℕ) (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ), GenWeil G L ξ n e → FullTorsion G ξ n → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → FullTorsion G' ξ' n → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (y : Over.mk ξ ⟶ G) (y' : Over.mk ξ' ⟶ G'), y ^ n = 1 → y' ^ n = 1 → (∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left → (e' y' g' : Ω') = i (e y g)) → (∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → (∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → ∀ (W : G.left.Opens) (s : Γ(G.left, W)),
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω →+* k) (xk g : Over.mk (spMap τ ≫ ξ) ⟶ G) (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap τ ≫ y.left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h s = c) →
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω' →+* k) (xk g : Over.mk (spMap τ ≫ ξ') ⟶ G') (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ (φ ⁻¹ᵁ W)), xk.left = spMap τ ≫ y'.left → g ^ n = 1 → Out.WeilIs G' L' n xk g (unitOn c) → secVal (B := k) g.left (φ ⁻¹ᵁ W) h (φ.app W s) = c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtTorPull.torsion_clause | exact GlobalTheory.CompanionTheory.Ar.HtTorPull.torsion_clause | (intros; apply GlobalTheory.CompanionTheory.Ar.HtTorPull.torsion_clause <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.dual_number_section_derivation : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (L : Type) [AddCommGroup L] [Module C L] (M : LieModel G y L) (W : G.left.Opens) (h : ∀ l, ⊤ ≤ (M.pt l).left ⁻¹ᵁ W) (s : Γ(G.left, W)), ∃ D : L →ₗ[C] C, ∀ l, D l = (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtPull.exists_linear_snd | exact GlobalTheory.CompanionTheory.Ar.HtPull.exists_linear_snd | (intros; apply GlobalTheory.CompanionTheory.Ar.HtPull.exists_linear_snd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.twist_iso_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty | exact GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty <;> assumption)
end
