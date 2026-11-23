module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.WeilBound.CoreStatements.SesquilinearFractions.LieNormSquareOfFamily
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle189
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle229
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle222
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle112
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle253
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeCmTypeWeight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle257
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle258
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle193
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  first | exact @PositivityTheory.Xgf.lie_norm_square_of_family | exact PositivityTheory.Xgf.lie_norm_square_of_family
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : R →+* S) (b : T →+* R) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  show Spec.map (CommRingCat.ofHom (a.comp b)) = Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have h' : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := h
  have := Spec.map_injective h'
  exact CommRingCat.hom_ext_iff.1 this |> fun e => by simpa using e

theorem spMap_dualMap_id (Ω : Type) [Field Ω] : spMap (dualMap (RingHom.id Ω)) = 𝟙 _ := by
  have : dualMap (RingHom.id Ω) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  rw [this]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
  simp

theorem cst_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] {a b : F →+* Ω}
    (h : a.comp (algebraMap (𝓞 F) F) = b.comp (algebraMap (𝓞 F) F)) : a = b :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem exists_cover : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 := by
  intro hG hW E _ _ _ H D l Xo c Y Sys Fx R o S hSp hSd hdeg
  have hRes : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have : CharZero R.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y o.𝔐.Ω₀ o.𝔐.ξ₀ o.𝔐.gen₀
  have hgen : GlobalTheory.CompanionTheory.Ar.genPt (o.𝔐.ξ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    have e : o.𝔐.ξ ≫ o.𝔐.f = Spec.map (CommRingCat.ofHom o.𝔐.fn) ≫ o.𝔐.ξ₀ := o.𝔐.fn_over
    rw [e, genPt_comp]; exact hgen₀
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y R.Ω (o.𝔐.ξ ≫ o.𝔐.f) S hgen hSp
  obtain ⟨K₁, _, J₁, _, y₁, bk₁, bx₁, M₁, h₁, hbk₁, hy₁, hdom₁, hnorm₁, hsm₁⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes R.K R.ι R.Ω Ω i R.y o.𝔐.X o.𝔐.ξ hfin o.𝔐.all o.𝔐.tie
  have hξ₁ : M₁.ξ ≫ h₁ ≫ o.𝔐.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
    have e : M₁.ξ ≫ h₁ = Spec.map (CommRingCat.ofHom i) ≫ o.𝔐.ξ := hdom₁
    rw [← Category.assoc, e, Category.assoc]
  have hgen₁ : GlobalTheory.CompanionTheory.Ar.genPt (M₁.ξ ≫ h₁ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    rw [hξ₁]; show GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom i) ≫ _) ∈ _
    rw [genPt_comp]; exact hgen
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω (M₁.ξ ≫ h₁ ≫ o.𝔐.f) hgen₁
  obtain ⟨K₂, _, J₂, _, y₂, bk₂, bx₂, B, g, hbk₂, hy₂, hdom₂, hf₂, hR₂, hfree₂, hiso₂⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S (fun _ => 4) Ω K₁ J₁ y₁ M₁ (h₁ ≫ o.𝔐.f) y₀ hnorm₁ hy₀ hgen₁ hSp hSd
      (fun _ _ => le_rfl) (fun p hp => by rw [hξ₁]; exact htors p hp) hroot
  have hgB : B.ξ ≫ g = M₁.ξ := by
    have e : B.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hdomB : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ o.𝔐.ξ (g ≫ h₁) i := by
    show B.ξ ≫ g ≫ h₁ = _
    rw [← Category.assoc, hgB]; exact hdom₁
  have hfB : B.f = (g ≫ h₁) ≫ o.𝔐.f := by rw [hf₂, Category.assoc]
  have hBξ : B.ξ ≫ B.f = y₀ ≫ Y.j := by
    rw [hf₂, ← Category.assoc, hgB]; exact hy₀
  have hcst : B.cst = i.comp o.𝔐.cst := by
    have h1 := B.cst_over
    have h2 := o.𝔐.cst_over
    have h3 : B.ξ ≫ B.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
      rw [hf₂, ← Category.assoc, hgB]; exact hξ₁
    have h4 : spMap (B.cst.comp (algebraMap (𝓞 c.F) c.F)) =
        spMap ((i.comp o.𝔐.cst).comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← Category.assoc, h3, RingHom.comp_assoc, spMap_comp', ← h2]
      simp
    have := c.fin
    have : NumberField c.F := {}
    exact cst_ext (spMap_inj h4)
  obtain ⟨jA, hext, hpt, hact, hlat⟩ :=
    GlobalTheory.T.hodge_comp_comparison_left E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 B i (g ≫ h₁) hdomB hfB
  obtain ⟨Li₀, _, _, M₀, j, V₀, hspan, hj, hV, hflag⟩ :=
    GlobalTheory.T.hodge_comp_comparison_middle E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hfin hdomB hfB hcst hext hpt hact
  have hvb := GlobalTheory.T.hodge_comp_comparison_right E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hdomB hfB hcst hext hpt hact hlat
  obtain ⟨K₃, _, J₃, _, y₃, bk₃, bx₃, 𝔐, g', Fl, xdeg, e, hbk₃, hy₃, hdom₃, hf₃, hR₃, hc₃, hfree₃, hFd, hFb, hlines, -, hiso₃⟩ :=
    GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω K₂ J₂ y₂ B y₀ (fun s a => jA (o.Fl.b s a)) Li₀ _ _ M₀ j V₀ _ hBξ hSd hfree₂
      (fun p hp => by rw [hR₂]; exact hroot p hp) hspan hj hV hflag
  have hsm₂ : SmoothGenericFibreM y₂ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₁ J₁ y₁ K₂ J₂ y₂ M₁.X B.X M₁.ξ B.ξ g M₁.all B.all M₁.tie B.tie hdom₂ hsm₁ hiso₂
  have hsm₃ : SmoothGenericFibreM y₃ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₂ J₂ y₂ K₃ J₃ y₃ B.X 𝔐.X B.ξ 𝔐.ξ g' B.all 𝔐.all B.tie 𝔐.tie hdom₃ hsm₂
      (fun q hq => hiso₃ q hq (hvb q hq))
  have hg' : 𝔐.ξ ≫ g' = B.ξ := by
    have e : 𝔐.ξ ≫ g' = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ B.ξ := hdom₃
    rw [e]; simp
  refine ⟨Ω, inferInstance, inferInstance, K₃, inferInstance, J₃, inferInstance, y₃, fun k => bk₃ (bk₂ (bk₁ k)),
    fun k => (bx₁ k).trans ((bx₂ _).trans (bx₃ _)), i, 𝔐, g' ≫ g ≫ h₁, Fl, xdeg, e,
    hbk₃.comp (hbk₂.comp hbk₁), ?_, ?_, ?_, ?_, ?_, ?_, hlines, ?_, hsm₃, ?_⟩
  · intro k a
    simp only [Equiv.trans_apply]
    rw [hy₃, hy₂, hy₁]
  · show 𝔐.ξ ≫ g' ≫ g ≫ h₁ = _
    rw [← Category.assoc, hg']; exact hdomB
  · rw [hf₃, hf₂]; simp
  · rw [hc₃, hcst]
  · intro s a
    rw [hFb, hpt, spMap_dualMap_id, Category.id_comp]
  · rw [hFd, hdeg, _root_.mul_one]
  · intro p hp
    have := hfree₃ p hp
    exact this
  · intro p hp
    rw [hR₃, hR₂]

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_tate_free_trivial_flag_mod : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), HTFree 𝔐 p → Fl.RootLines xdeg e → ∀ τ : CMType H, Num.TrivFlagMod o ((p : o) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => xdeg (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_rootLines_model | exact GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_rootLines_model | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_rootLines_model <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.hodge_tate_free_cm_type_weight : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → 0 < D.p + D.q → HTFree 𝔐 p → ∀ τ : CMType H, ExactModLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (p : Ω) (D.p + D.q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exactModLat_hodgeTate | exact GlobalTheory.CompanionTheory.Ar.Flat.exactModLat_hodgeTate | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exactModLat_hodgeTate <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.exists_sandwich_of_hodge_tate_free : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q), HTFree 𝔐 p → ∃ κ : Ω, IsCp p κ ∧ Sandwich 𝔐 p κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree | exact GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.boundary_chart_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), IsHolTo (punct n a 1) C.pt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt | exact GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameLen

theorem len_sq_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (g : ℕ) (u : HolUnif A (D.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsAbelianScheme A → IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → ∀ (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re := by
  intro E _ _ _ H L _ _ D σ A _ φ g u Hm χ hab hp h1 h2 hah a x c hvec
  obtain ⟨v, hlift, v', hv', hdiff⟩ := hvec
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  have hl₀ : (v₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := hlift
  obtain ⟨hL, hvt, -, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x x v₀ v₀ hl₀ hl₀
  have hp₀ : IsGrpPullback A D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ A := (HodgeLin.tanEquiv hp₀).symm v₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have lx₁ : x₁.left ≫ φ = v.left := congrArg (fun r => r.left) hx₁
  obtain ⟨w, hw, -⟩ := h1 x₁ tx₁
  have T1 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) A a.A φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB hab hp
    a.cart h1 h2 hah a.ah x₁ x₁ v' v' w w c c tx₁ tx₁ (hv'.trans lx₁.symm) (hv'.trans lx₁.symm) hw hw hdiff hdiff
  have T2 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) A A' φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB hab hp
    hpz h1 h2 hah hah' x₁ x₁ q p w w b' a' tx₁ tx₁ (eq'.trans lx₁.symm) (ep.trans lx₁.symm) hw hw dq dp
  have hH : a.herm c c = hermForm Hm' b' a' := T1.trans T2.symm
  have hin : ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ) =
      Real.pi * a.herm c c := by
    rw [hH]; exact hval
  have hnn : 0 ≤ ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ).re := (D.B.metric.form σ).re_inner_nonneg _
  unfold PPData.len
  rw [Real.sq_sqrt hnn, hin, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.Ar.Sl.FrameLen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.family_pure_periods_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ), 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.point_numberField_of_finiteIndex | exact GlobalTheory.CompanionTheory.Ggeo.point_numberField_of_finiteIndex | (intros; apply GlobalTheory.CompanionTheory.Ggeo.point_numberField_of_finiteIndex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PeriodConj

def conjEnd (g : ℕ) : Module.End ℂ (Fin g → ℂ) →+* Module.End ℂ (Fin g → ℂ) where
  toFun f :=
    { toFun := fun x => star (f (star x))
      map_add' := fun x y => by simp only [star_add, map_add (f := _)]
      map_smul' := fun c x => by simp only [star_smul, map_smul, star_star, RingHom.id_apply] }
  map_one' := by ext x; simp
  map_mul' f f' := by ext x; simp
  map_zero' := by ext x; simp
  map_add' f f' := by ext x; simp

theorem conjEnd_apply {g : ℕ} (f : Module.End ℂ (Fin g → ℂ)) (x : Fin g → ℂ) :
    conjEnd g f x = star (f (star x)) := rfl

theorem mem_eigSp_iff {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ)
    (x : Fin g → ℂ) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem finrank_eigSp_conj {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ) :
    Module.finrank ℂ (eigSp ((conjEnd g).comp ρ) σ) = Module.finrank ℂ (eigSp ρ ((starRingEnd ℂ).comp σ)) := by
  have h1 : ∀ x, x ∈ eigSp ((conjEnd g).comp ρ) σ → star x ∈ eigSp ρ ((starRingEnd ℂ).comp σ) := by
    intro x hx
    rw [mem_eigSp_iff] at hx ⊢
    intro a
    have := congrArg star (hx a)
    simpa [conjEnd_apply, star_smul] using this
  have h2 : ∀ y, y ∈ eigSp ρ ((starRingEnd ℂ).comp σ) → star y ∈ eigSp ((conjEnd g).comp ρ) σ := by
    intro y hy
    rw [mem_eigSp_iff] at hy ⊢
    intro a
    simp [conjEnd_apply, hy a, star_smul]
  let j : eigSp ((conjEnd g).comp ρ) σ ≃+ eigSp ρ ((starRingEnd ℂ).comp σ) :=
    { toFun := fun x => ⟨star x.1, h1 _ x.2⟩
      invFun := fun y => ⟨star y.1, h2 _ y.2⟩
      left_inv := fun x => Subtype.ext (star_star _)
      right_inv := fun y => Subtype.ext (star_star _)
      map_add' := fun x y => Subtype.ext (star_add _ _) }
  have hr := rank_eq_of_equiv_equiv (R := ℂ) (R' := ℂ) (starRingEnd ℂ) j
    (Function.Involutive.bijective (f := starRingEnd ℂ) (fun z => by simp)) (fun r m => by
      apply Subtype.ext
      change star (r • m.1) = star r • star m.1
      exact star_smul r m.1)
  exact congrArg Cardinal.toNat hr

theorem star_herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    star z ⬝ᵥ Hm.map (starRingEnd ℂ) *ᵥ star (star w) = star (z ⬝ᵥ Hm *ᵥ star w) := by
  simp [dotProduct, mulVec, star_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjLat {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) : RiemLat E g Λ where
  free := R.free
  fin := R.fin
  rank := R.rank
  form := -R.form
  alt x := by simp [R.alt x]
  unimod := by
    constructor
    · intro x y h
      exact R.unimod.1 (neg_injective (by simpa using h))
    · intro f
      obtain ⟨x, hx⟩ := R.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  adj a a' h x y := by simp [R.adj a a' h x y]
  P :=
    { toFun := fun x => star (R.P x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  Hm := R.Hm.map (starRingEnd ℂ)
  herm := by
    ext i j
    have := R.herm.apply i j
    simp [Matrix.conjTranspose_apply, ← this]
  pos z hz := by
    have h := R.pos (star z) (by simpa using hz)
    have h' := star_herm R.Hm (star z) (star z)
    simp only [star_star] at h'
    rw [h']
    simpa using h
  im x y := by
    have h := R.im x y
    have h' := star_herm R.Hm (R.P x) (R.P y)
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [h']
    simp [h]
  B := (conjEnd g).comp R.B
  act a x := by simp [conjEnd_apply, R.act]

theorem conj_rt_iff (H : Host E) (s : E →+* ℂ) :
    ((starRingEnd ℂ).comp s) (H.rt : E) = H.rt0 ↔ ¬ s (H.rt : E) = H.rt0 := by
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h2 : s (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => s (a : E)) H.rt_sq
    simpa using h
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have hi := congrArg Complex.im h0
    have hr := congrArg Complex.re h0
    simp [pow_two] at hi hr
    rcases (by
      have : H.rt0.re * H.rt0.im = 0 := by nlinarith
      exact mul_eq_zero.1 this) with h | h
    · exact h
    · exfalso; rw [h] at hr; nlinarith [mul_self_nonneg H.rt0.re]
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
    exact H.d_prime.ne_zero h0
  have hpm : s (H.rt : E) = H.rt0 ∨ s (H.rt : E) = -H.rt0 := by
    have : (s (H.rt : E) - H.rt0) * (s (H.rt : E) + H.rt0) = 0 := by
      linear_combination h2 - h0
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hneg : -H.rt0 ≠ H.rt0 := by
    intro h
    exact hne (by linear_combination -(1 / 2 : ℂ) * h)
  rcases hpm with h | h
  · simp only [RingHom.comp_apply, h, hconj]
    simpa using hneg
  · simp only [RingHom.comp_apply, h, map_neg, hconj, neg_neg]
    simpa using hneg

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PeriodConj

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

open PeriodConj

theorem period_lattice_fibre_and_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod (FU.Di i) ty P → (∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ FibreLat Xo.univ.t (FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) ∧ (∃ R : RiemLat E g (FU.Di i).La, R.form = -(FU.Di i).EF ∧ FibreLat Xo.univ.t (spMap (starRingEnd ℂ) ≫ FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.q else D.p) := by
  intro E _ _ _ H D l Xo σ g ty FU i P hty hP
  have hty' : IsTypeFn H (FU.Di i).p (FU.Di i).q ty := by
    rw [(FU.sig i).1, (FU.sig i).2]; exact hty
  obtain ⟨R, hRP, hRf, -, hrk⟩ := GlobalTheory.T.exists_riemann_lattice_of_period E H (FU.Di i) g ty P hty' hP
  have hF : FibreLat Xo.univ.t (FU.u i P) R :=
    GlobalTheory.T.family_period_riemann_lattice E H D l Xo σ g ty FU i R P 1 hP hRf (by simp) (fun x => by simp [hRP]) Empty
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
  refine ⟨⟨R, hRf, hF, fun s => ?_⟩, ⟨conjLat R, ?_, ?_, fun s => ?_⟩⟩
  · rw [hrk s, (FU.sig i).1, (FU.sig i).2]
  · show -R.form = _
    rw [hRf]
  · exact (GlobalTheory.T.fibre_lattice_base_change_conj E H Xo.X Xo.X Xo.univ.t Xo.univ.t (𝟙 _) g _ R (conjLat R) (FU.u i P)).2
      (fun _ => rfl) rfl (fun _ _ => rfl) hF
  · have h1 : Module.finrank ℂ (eigSp (conjLat R).B (s.comp (algebraMap (𝓞 E) E))) =
        Module.finrank ℂ (eigSp R.B (((starRingEnd ℂ).comp s).comp (algebraMap (𝓞 E) E))) :=
      finrank_eigSp_conj R.B (s.comp (algebraMap (𝓞 E) E))
    rw [h1, hrk, (FU.sig i).1, (FU.sig i).2]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg (fun h' => (conj_rt_iff H s).1 h' h)]
    · rw [if_neg h, if_pos ((conj_rt_iff H s).2 h)]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

theorem _root_.GlobalTheory.T.flag_variables_alg_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K L : Type) [Field K] [Field L] [Algebra K L] (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) L), AlgebraicIndependent K (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) → ∃ T : FlagVar Dw → L, AlgebraicIndependent K T ∧ Set.range T = Set.range (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ ∀ (s : CMType H ⊕ CMType H) (i j : Fin (Dw.mult (Small.labelC s))) (hij : i < j), T ⟨Small.labelC s, ⟨(i, j), hij⟩⟩ = v s (Fin.cast (Small.mult_labelC Dw s) j) (Fin.cast (Small.mult_labelC Dw s) i) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_variables_alg_indep | exact GlobalTheory.CompanionTheory.Relay.flag_variables_alg_indep | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_variables_alg_indep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.chowla_selberg_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (Z : Curve0 H ρ) (x : ℝ), Z.z ≠ 0 ∧ Z.C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_curve0_hasPeriod <;> assumption)
end
