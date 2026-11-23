module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle077
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle078
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrArch

theorem isLocalRing_of_value {Ω : Type} [Field Ω] (W : Subring Ω) (φ : W →+* ℂ)
    (hW : ∀ a : W, φ a ≠ 0 → IsUnit a) : IsLocalRing W := by
  haveI : Nontrivial W := φ.domain_nontrivial
  refine IsLocalRing.of_nonunits_add fun a b ha hb hu => ?_
  have h0 : ∀ c : W, c ∈ nonunits W → φ c = 0 := fun c hc => by_contra fun h => hc (hW c h)
  have := hu.map φ
  rw [map_add (f := _), h0 a ha, h0 b hb, add_zero] at this
  exact not_isUnit_zero this

theorem exists_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : genPt ξ ⤳ centre z)
    (hv : ∀ (a : Ω₁) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) :
    ∃ σ : X.presheaf.stalk (centre z) →+* W, (∀ s, (σ s : Ω) = i (genMap ξ ⟨centre z, hz⟩ s)) ∧
      ∀ s, φ (σ s) = (Scheme.stalkClosedPointTo z).hom s := by
  have hm : ∀ s, ValAt ξ z (genMap ξ ⟨centre z, hz⟩ s) ((Scheme.stalkClosedPointTo z).hom s) :=
    fun s => ⟨hz, s, rfl, rfl⟩
  exact ⟨(i.comp (genMap ξ ⟨centre z, hz⟩)).codRestrict W fun s => (hv _ _ (hm s)).1,
    fun _ => rfl, fun s => (hv _ _ (hm s)).2⟩

theorem isLocalHom_of_value {X : Scheme.{0}} {Ω : Type} [Field Ω] (W : Subring Ω) (φ : W →+* ℂ)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (σ : X.presheaf.stalk (centre z) →+* W)
    (hσ : ∀ s, φ (σ s) = (Scheme.stalkClosedPointTo z).hom s) : IsLocalHom σ :=
  ⟨fun s hs => GlobalTheory.CompanionTheory.Ar.CxVal.isUnit s (by rw [← hσ]; exact (hs.map φ).ne_zero)⟩

theorem domBy_of_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (q : Cpt ξ) (W : Subring Ω) (V : ValuationSubring Ω)
    (hWV : W ≤ V.toSubring) (hloc : IsLocalHom (Subring.inclusion hWV))
    (σ : X.presheaf.stalk q.1 →+* W) (hl : IsLocalHom σ) (hσ : ∀ s, (σ s : Ω) = i (genMap ξ q s)) :
    DomBy V.toSubring i ξ q := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← hσ]
    exact hWV (σ s).2
  · rintro _ ⟨s, rfl⟩ h0 hinv
    have hi : i (genMap ξ q s) ≠ 0 := (map_ne_zero i).2 h0
    have hu : IsUnit (Subring.inclusion hWV (σ s)) := by
      refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V.toSubring) (Subtype.ext ?_)
      change ((σ s : W) : Ω) * (i (genMap ξ q s))⁻¹ = 1
      rw [hσ, mul_inv_cancel₀ hi]
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit σ s (isUnit_of_map_unit (Subring.inclusion hWV) _ hu)
    exact ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).val, map_units_inv (genMap ξ q) u⟩

theorem point_closed {X Y : Scheme.{0}} (x : X) (f : X ⟶ Y) {R : Type} [CommRing R] [IsLocalRing R]
    (σ : X.presheaf.stalk x →+* R) (hl : IsLocalHom σ) :
    (spMap σ ≫ X.fromSpecStalk x ≫ f) (IsLocalRing.closedPoint R) = f x := by
  have : IsLocalHom (CommRingCat.ofHom σ).hom := hl
  change f (X.fromSpecStalk x (Spec.map (CommRingCat.ofHom σ) (IsLocalRing.closedPoint R))) = f x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem spec_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (q : Cpt ξ) (W : Subring Ω)
    (σ : X.presheaf.stalk q.1 →+* W) (hσ : ∀ s, (σ s : Ω) = i (genMap ξ q s)) :
    spMap W.subtype ≫ spMap σ ≫ X.fromSpecStalk q.1 = spMap i ≫ ξ := by
  have e : W.subtype.comp σ = i.comp (genMap ξ q) := RingHom.ext hσ
  have e2 : spMap W.subtype ≫ spMap σ = spMap i ≫ spMap (genMap ξ q) :=
    (LieTangent.spec_comp σ W.subtype).trans
      ((congrArg (fun g => Spec.map (CommRingCat.ofHom g)) e).trans (LieTangent.spec_comp _ _).symm)
  rw [← Category.assoc, e2, Category.assoc]
  exact congrArg (spMap i ≫ ·) (LieTangent.spec_genMap ξ q)

theorem exists_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (a : Ω) (r : ℂ), ValAt 𝔐.ξ z₁ a r → ∃ h : a ∈ W, φ ⟨a, h⟩ = r) → (∀ (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ z₂ a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) → ∃ (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) ∧ (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) ∧ (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) ∧ (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) ∧ spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i W φ z₁ z₂ hξ hW h₁ h₂
  haveI := isLocalRing_of_value W φ hW
  obtain ⟨σ₁, a₁, b₁⟩ := exists_stalkHom 𝔐.ξ (RingHom.id Ω) W φ z₁ (𝔐.all _) h₁
  obtain ⟨σ₂, a₂, b₂⟩ := exists_stalkHom 𝔐₀.ξ i W φ z₂ (𝔐₀.all _) h₂
  refine ⟨σ₁, σ₂, a₁, a₂, b₁, b₂, ?_⟩
  have e₁ := spec_stalkHom 𝔐.ξ (RingHom.id Ω) ⟨centre z₁, 𝔐.all _⟩ W σ₁ a₁
  have e₂ := spec_stalkHom 𝔐₀.ξ i ⟨centre z₂, 𝔐₀.all _⟩ W σ₂ a₂
  have hid : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
  rw [hid, Category.id_comp] at e₁
  have f₁ := congrArg (· ≫ 𝔐.f) e₁
  have f₂ := congrArg (· ≫ 𝔐₀.f) e₂
  simp only [Category.assoc] at f₁ f₂
  have hgen : spMap W.subtype ≫ (spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f) =
      spMap W.subtype ≫ (spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f) := by
    simpa only [Category.assoc] using f₁.trans (hξ.trans f₂.symm)
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 Subtype.val_injective]; exact bot_le)⟩
  have hbase : (spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f) ≫ Y.s =
      (spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have hsep : IsSeparated Y.s := by
    obtain ⟨N, j, hj, he⟩ := Y.proj
    letI : IsClosedImmersion j := hj
    rw [← he]
    have : IsSeparated (PSpace.str (𝓞 c.F) N) := by
      unfold PSpace.str
      infer_instance
    infer_instance
  exact ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen

end GlobalTheory.CompanionTheory.Ar.OrArch
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem grp_mul {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (a : T ⟶ S') (b : T ⟶ S) (hb : b = a ≫ f)
    (x y : Over.mk a ⟶ G') (x₀ y₀ : Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hb
  exact h.2 (Over.mk a) x y x₀ y₀ hx hy

theorem exists_lift {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} (a : T ⟶ S') (w : T ⟶ G.left) (hw : w ≫ G.hom = a ≫ f) :
    ∃ v : Over.mk a ⟶ G', v.left ≫ φ = w :=
  ⟨Over.homMk (h.lift w a hw) (by simp), by simp⟩

theorem lift_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {a : T ⟶ S'} (v v' : Over.mk a ⟶ G')
    (e : v.left ≫ φ = v'.left ≫ φ) : v = v' :=
  Over.OverMorphism.ext (h.hom_ext e (by rw [Over.w, Over.w]))

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun a => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

def scale {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) : epsAt a ⟶ Y :=
  Over.homMk (spMap (epsMul c) ≫ v.left) (by
    have h := Over.w v
    simp only [Over.mk_left, Over.mk_hom, Category.assoc] at h ⊢
    rw [h, ← Category.assoc, LieTangent.spec_eps_alg])

@[simp] theorem scale_left {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) :
    (scale a c v).left = spMap (epsMul c) ≫ v.left := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem abPart_mul {S : Scheme.{0}} {t : SAB H S} {K : Type} [Field K] {z : Sp K ⟶ S} (P : AbPart t z) {T : Over (Sp K)}
    (x y : T ⟶ P.tK.G) :
    (x * y) ≫ P.τ.q ≫ P.e.hom = (x ≫ P.τ.q ≫ P.e.hom) * (y ≫ P.τ.q ≫ P.e.hom) := by
  letI := P.τ.grpB
  haveI := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  rw [← Category.assoc, mul_comp, mul_comp, Category.assoc, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TanCompare

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem tan_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left)) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, ((Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t'.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt e).left)) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' V₁ V₂ _ _ _ _ MB MB' f hf σ Pσ mKσ mBσ
    d1 d2 Mσ hMσ Mσ' hMσ' x v u hv hu
  have spec_dual_alg {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap R' (DualNumber R')) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hbase : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, spMap_comp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb1 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) ≫ z₁ := by
    rw [hbase, Category.comp_id]
  have hb2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, Category.comp_id, Category.assoc]
  have hb3 : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    rw [spMap_comp e₂ σ, Category.comp_id, Category.assoc]
  have base : ∀ e : V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro e
    obtain ⟨vL, hvL⟩ := exists_lift P₂.m.cart.1 (spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _)
      (spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) (by
        have hMe : (MB.pt e).left ≫ t.G.hom = spMap (algebraMap (𝓞 L) (DualNumber (𝓞 L))) ≫ z := Over.w (MB.pt e)
        rw [Category.assoc, hMe, ← Category.assoc, spec_dual_alg, Category.assoc, hz, Category.comp_id])
    have hfe : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w ≫ m'.φ =
        spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left := hf e vL hvL
    obtain ⟨v, hv⟩ := exists_lift Pσ.m.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _)
      (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left
      ((Over.w (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).trans hb1)
    obtain ⟨u, hu⟩ := exists_lift m'.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ)
      (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left
      ((Over.w (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e))).trans hb2)
    refine ⟨v, u, hv, hu, ?_⟩
    have hde : spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap σ) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := spMap_dual_comp _ _
    have hd : spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := spec_dual_alg σ
    have h1 : (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left :=
      (Category.comp_id _).symm.trans (hMσ e)
    have h1' : (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt (f e)).left :=
      (Category.comp_id _).symm.trans (hMσ' (f e))
    have hvd : v.left ≫ Pσ.m.φ = spMap (dualMap σ) ≫ vL.left ≫ P₂.m.φ := by
      rw [hv, h1, hde, Category.assoc, hvL]
    have wv : v.left ≫ Pσ.tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _ := Over.w v
    have wvL : vL.left ≫ P₂.tK.G.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w vL
    have star : v.left ≫ mKσ.φ = spMap (dualMap σ) ≫ vL.left ≫ mK2.φ := by
      refine P₁.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, d1, hvd, Category.assoc, Category.assoc, c1]
      · rw [Category.assoc, mKσ.cart.1.w, ← Category.assoc, wv, hb3]
        simp only [Category.assoc]
        rw [mK2.cart.1.w, ← Category.assoc vL.left, wvL, Category.comp_id]
        have hd2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ ≫ spMap e₂ =
            spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) ≫ spMap e₂ := by
          rw [← Category.assoc, ← hd, Category.assoc]
        exact hd2
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    have wq : (vL ≫ P₂.τ.q).left ≫ P₂.τ.B.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w (vL ≫ P₂.τ.q)
    have we : P₂.e.hom.left ≫ P₂.tB.G.hom = P₂.τ.B.hom := Over.w P₂.e.hom
    have hu2 : u.left = spMap (dualMap σ) ≫ (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w := by
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [hu, h1', hde]
        simp only [Category.assoc]
        rw [hfe]
      · rw [wu]
        simp only [Category.assoc]
        rw [hw', we, wq, Category.comp_id, hd]
    have e1 : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ mB2.φ = vL.left ≫ (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ := by
      simp only [Over.comp_left, Category.assoc]
    have e2 : (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ = v.left ≫ (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
      rw [Over.comp_left, Category.assoc]
    rw [hu2, e2, ← d2, ← Category.assoc v.left, star]
    simp only [Category.assoc]
    rw [hw, e1, ← c2]
  have tm : ∀ (c : GroundTheory.Heights₂.Heights.ComplexAt σ) (e : V₁), ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt (c ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) (c ⊗ₜ[𝓞 L] e))).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro c e
    obtain ⟨v, u, h, k, l⟩ := base e
    let c' : ℂ := c
    have hs : c' • (1 : GroundTheory.Heights₂.Heights.ComplexAt σ) = c := by
      rw [GroundTheory.Heights₂.Heights.ComplexAt.complex_smul_def, _root_.mul_one]
      rfl
    have hc : ∀ (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (a : W),
        c ⊗ₜ[𝓞 L] a = c' • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] a) := by
      intro W _ _ a
      rw [TensorProduct.smul_tmul', hs]
    refine ⟨scale _ c' v, scale _ c' u, ?_, ?_, ?_⟩
    · rw [hc, Mσ.smul, scale_left, Category.assoc, h]
    · rw [LinearMap.lTensor_tmul, hc, Mσ'.smul, scale_left, Category.assoc, k]
    · rw [scale_left, Category.assoc, l]
      simp only [Over.comp_left, scale_left, Category.assoc]
  have hx0 : ∀ u : epsAt (spMap σ) ⟶ tK.G, (u.left ≫ mP.φ) ≫ P₁.tB.G.hom =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    intro u
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    rw [Category.assoc, mP.cart.1.w, ← Category.assoc, wu]
  have key : ∀ x : GroundTheory.Heights₂.Heights.Fibre σ V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt x).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      have h0 := tm 0 0
      rwa [TensorProduct.zero_tmul] at h0
    | tmul c e => exact tm c e
    | add x y hx hy =>
      obtain ⟨v₁, u₁, h₁, k₁, l₁⟩ := hx
      obtain ⟨v₂, u₂, h₂, k₂, l₂⟩ := hy
      refine ⟨v₁ * v₂, u₁ * u₂, ?_, ?_, ?_⟩
      · rw [Mσ.add]
        exact (grp_mul Pσ.m.cart _ _ hb1 v₁ v₂ (Mσ.pt x) (Mσ.pt y) h₁.symm h₂.symm).symm
      · rw [map_add (f := _), Mσ'.add]
        exact (grp_mul m'.cart _ _ hb2 u₁ u₂ _ _ k₁.symm k₂.symm).symm
      · rw [abPart_mul]
        let x₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₁.left ≫ mP.φ) (hx0 u₁)
        let y₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₂.left ≫ mP.φ) (hx0 u₂)
        rw [← grp_mul mP.cart _ _ rfl u₁ u₂ x₀ y₀ rfl rfl]
        exact grp_mul mBσ.cart _ _ hb3.symm _ _ x₀ y₀ l₁ l₂
  obtain ⟨v₀, u₀, h₀, k₀, l₀⟩ := key x
  have hv' : v = v₀ := lift_unique Pσ.m.cart.1 _ _ (hv.trans h₀.symm)
  have hu' : u = u₀ := lift_unique m'.cart.1 _ _ (hu.trans k₀.symm)
  rw [hv', hu']
  exact l₀

end GlobalTheory.CompanionTheory.Ar.TanCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameTri

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem comp_list_prod {B : Scheme.{0}} {G T T' : Over B} [GrpObj G] (f : T' ⟶ T) (L : List (T ⟶ G)) :
    f ≫ L.prod = (L.map fun a => f ≫ a).prod := by
  induction L with
  | nil => simpa using MonObj.comp_one f
  | cons a L ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem dualMap_comp_algebraMap {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap F (DualNumber F)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) =
      (GlobalTheory.CompanionTheory.Ar.epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, GlobalTheory.CompanionTheory.Ar.epsMul,
    TrivSqZeroExt.algebraMap_eq_inl]

theorem isComb_of_isCombAt {Xo : Moduli D l} {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m : ℕ}
    {vS : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {wS : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vS cf wS)
    {v : Fin m → (epsAt x' ⟶ Xo.univ.t.G)} {w : epsAt x' ⟶ Xo.univ.t.G}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ vS i)
    (hw : w.left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ wS) :
    Fl.IsComb (fun i => ψ (cf i)) v w := by
  subst hx
  obtain ⟨u, hu, hp⟩ := h
  have hf : spMap (Formalism.L2.Pj.dualMap ψ) ≫ (Formalism.L2.Pj.tEps x).hom = (epsAt (spMap ψ ≫ x)).hom := by
    show spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap]
  let f : epsAt (spMap ψ ≫ x) ⟶ Formalism.L2.Pj.tEps x := Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ)) hf
  refine ⟨fun i => f ≫ u i, fun i => ?_, ?_⟩
  · show spMap (Formalism.L2.Pj.dualMap ψ) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_epsMul']
  · have e : (List.ofFn fun i => f ≫ u i) = (List.ofFn u).map fun a => f ≫ a := by
      rw [List.map_ofFn]; rfl
    rw [e, ← comp_list_prod]
    apply Over.OverMorphism.ext
    rw [hw, ← hp]
    rfl

theorem exists_matrix {Xo : Moduli D l} {S F : Type} [CommRing S] [Field F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m n : ℕ} (hn : n = m)
    {u u' : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (d : Fin m → S)
    (h : ∀ i, ∃ cf : Fin m → S, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ Formalism.L2.Pj.IsCombAt x u cf (u' i))
    {v v' : Fin n → (epsAt x' ⟶ Xo.univ.t.G)}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u (i.cast hn))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u' (i.cast hn)) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, Fl.IsComb (A i) v (v' i)) ∧
      A.det = ∏ i : Fin n, ψ (d (i.cast hn)) := by
  subst hn
  choose cf h1 h2 h3 using h
  refine ⟨Matrix.of fun i j => ψ (cf i j), fun i => ?_, ?_⟩
  · exact isComb_of_isCombAt ψ hx (h3 i) hv (hv' i)
  · rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun i _ => by simp [h1]
    · intro i j hij
      have : i < j := hij
      simp [h2 i j this]

theorem exists_triangular_at_field (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S]
    (t : Formalism.L2.Pj.Ix D → Sˣ) (z z' : Formalism.L2.Pj.FrPt Xo c S) (hb : Formalism.L2.Pj.FrBor t z z')
    (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p)
    (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (hy : under y = spMap ψ ≫ z.x)
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm))
    (hw : ∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u τ (i.cast hp.symm))
    (hw' : ∀ j, (w' j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) :
    ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F),
      (∀ i, Fl.IsComb (A i) v (v' i)) ∧ (∀ j, Fl.IsComb (B j) w (w' j)) ∧
      A.det = ∏ i : Fin D.p, ψ (t (some ⟨τ, i.cast hp.symm⟩) : Sˣ) ∧
      B.det = ∏ j : Fin D.q, ψ (t (some ⟨ComplexEmbedding.conjugate τ, j.cast hq.symm⟩) : Sˣ) := by
  obtain ⟨-, hc, -⟩ := hb
  obtain ⟨A, hA, dA⟩ := exists_matrix ψ hy hp.symm (fun i => (t (some ⟨τ, i⟩) : S)) (hc τ) hv hv'
  obtain ⟨B, hB, dB⟩ := exists_matrix ψ hy hq.symm
    (fun i => (t (some ⟨ComplexEmbedding.conjugate τ, i⟩) : S)) (hc (ComplexEmbedding.conjugate τ)) hw hw'
  exact ⟨A, B, hA, hB, dA, dB⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrameTri
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.adapted_bases_change_by_block_matrices : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v v' : Fin p → W) (w w' : Fin q → W)
    (u u' : Fin (p + q) → W × Module.Dual K W) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K),
    IsAdapted ρH σ v w u → IsAdapted ρH σ v' w' u' → LinearIndependent K v →
    Submodule.span K (Set.range u) = HT.eigSp ρH σ →
    (∀ i, v' i = ∑ k, P i k • v k) → (∀ i, w' i = ∑ k, Q i k • w k) →
    ∃ B : Matrix (Fin (p + q)) (Fin (p + q)) K, (∀ i, u' i = ∑ k, B i k • u k) ∧ B.det * Q.det = P.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodge_lattice_transport_equiv : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport <;> assumption)
end
