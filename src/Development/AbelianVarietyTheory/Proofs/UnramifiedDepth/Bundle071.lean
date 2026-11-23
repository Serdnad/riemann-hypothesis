module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorExtPoints

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem exists_lift {X Y : Scheme.{0}} (q : X ⟶ Y) [Smooth q] {A : Type} [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω) (hn : IsNilpotent (RingHom.ker π)) (y : Sp A ⟶ Y) (x₀ : Sp Ω ⟶ X)
    (h : x₀ ≫ q = spMap (π : A →+* Ω) ≫ y) : ∃ x : Sp A ⟶ X, spMap (π : A →+* Ω) ≫ x = x₀ ∧ x ≫ q = y := by
  have hπ : Function.Surjective π := fun a => ⟨algebraMap Ω A a, π.commutes a⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ := exists_isAffineOpen_pair q (x₀ (closedPoint Ω)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen q hU hV hVU (CommRingCat.ofHom (π : A →+* Ω)) y x₀ h ?_
    (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · rintro _ ⟨p, rfl⟩
    obtain ⟨z, hz⟩ : p ∈ Set.range (PrimeSpectrum.comap (π : A →+* Ω)) := by
      refine (range_comap_of_surjective _ (π : A →+* Ω) hπ).ge ?_
      obtain ⟨n, hn⟩ := hn
      exact (Ideal.IsPrime.pow_le_iff (P := p.asIdeal) (hP := p.isPrime) n.succ_ne_zero).1 (by
        rw [pow_succ]
        exact Ideal.mul_le_left.trans (hn.le.trans bot_le))
    obtain rfl : z = closedPoint Ω := Subsingleton.elim _ _
    have e : q (x₀ (closedPoint Ω)) = y (spMap (π : A →+* Ω) (closedPoint Ω)) := congr($h (closedPoint Ω))
    rw [← hz]
    exact e ▸ hVU hxV
  · intro R C _ _ _ _ _ _ p hp φ
    have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
    have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
      convert hn using 1
      exact Ideal.ext fun b => Eq.congr_left (hp b)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
      Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩

def torPt (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra Ω A] :
    (overAt s A ⟶ splitTorus S X) ≃* (Multiplicative X →* Aˣ) :=
  (splitTorusPointsEquiv S X (overAt s A)).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv).monoidHomCongrRight

theorem torPt_nat (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] {A A' : Type} [CommRing A] [Algebra Ω A]
    [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (t : overAt s A ⟶ splitTorus S X) :
    torPt s X A' (homAt s f ≫ t) = (Units.map (f : A →* A')).comp (torPt s X A t) := by
  ext x
  change (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom
      (splitTorusPointsEquiv S X _ (homAt s f ≫ t) (Multiplicative.ofAdd x)).val =
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (splitTorusPointsEquiv S X _ t (Multiplicative.ofAdd x)).val)
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* A'))) _)

theorem isTorExt_of_kernel (s : Sp Ω ⟶ S) {G B : Over S} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Smooth q.left]
    (hk : IsPullback i (toUnit _) q η[B]) :
    IsTorExt s s G B X (fun A _ _ => IsMonHom.monoidHom q (overAt s A))
      (fun A _ _ => (IsMonHom.monoidHom i (overAt s A)).comp (torPt s X A).symm.toMonoidHom) := by
  refine ⟨fun A A' _ _ _ _ f x => Category.assoc _ x q, fun A A' _ _ _ _ f χ => ?_, fun A _ _ χ χ' h => ?_,
    fun A _ _ x => ⟨fun h => ?_, ?_⟩, fun A _ _ π hn y hy => ?_⟩
  · obtain ⟨t, rfl⟩ := (torPt s X A).surjective χ
    rw [← torPt_nat]
    change (torPt s X A').symm _ ≫ i = _ ≫ (torPt s X A).symm _ ≫ i
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Category.assoc]
  · exact (torPt s X A).symm.injective (hk.hom_ext h (toUnit_unique _ _))
  · refine ⟨torPt s X A (hk.lift x (toUnit _) h), ?_⟩
    change (torPt s X A).symm _ ≫ i = _
    rw [MulEquiv.symm_apply_apply]
    exact hk.lift_fst _ _ _
  · rintro ⟨χ, rfl⟩
    change (_ ≫ i) ≫ q = toUnit _ ≫ η[B]
    rw [Category.assoc, hk.w, ← Category.assoc, toUnit_unique (_ ≫ _) (toUnit _)]
  · have h1 : (1 : overAt s Ω ⟶ G) ≫ q = homAt s π ≫ y := (map_one (IsMonHom.monoidHom q _)).trans hy.symm
    obtain ⟨x, hx, hq⟩ := exists_lift q.left π hn y.left (1 : overAt s Ω ⟶ G).left (congrArg (·.left) h1)
    exact ⟨Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w y), Over.OverMorphism.ext hx,
      Over.OverMorphism.ext hq⟩

theorem exists_ptEquiv {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') {t : T.left ⟶ S} (ht : t = T.hom ≫ f) :
    ∃ E : (T ⟶ G') ≃* (Over.mk t ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  subst ht
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_isTorExt_of_pullback {G B : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj G'] [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φ)
    (hB : IsGrpPullback B' B f ψ) {s' : Sp Ω ⟶ S'} {s : Sp Ω ⟶ S} (hs : s' ≫ f = s) {X : Type} [AddCommGroup X]
    {τ' : PtHom s' s' G' B'} {io' : TorHom s' G' X} (h : IsTorExt s' s' G' B' X τ' io') :
    ∃ (τ : PtHom s s G B) (io : TorHom s G X), IsTorExt s s G B X τ io ∧
      ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), ∃ x' : overAt s' A ⟶ G',
        x'.left ≫ φ = x.left ∧ (τ A x).left = (τ' A x').left ≫ ψ := by
  have ht : ∀ (A : Type) [CommRing A] [Algebra Ω A], spMap (algebraMap Ω A) ≫ s = (overAt s' A).hom ≫ f :=
    fun A _ _ => by rw [← hs]; exact (Category.assoc _ _ _).symm
  choose E hE using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hG (overAt s' A) (ht A)
  choose F hF using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hB (overAt s' A) (ht A)
  have nE : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ G'), E A' (homAt s' g ≫ x) = homAt s g ≫ E A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hE A' _).trans ((Category.assoc _ x.left φ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hE A x).symm)))
  have nF : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ B'), F A' (homAt s' g ≫ x) = homAt s g ≫ F A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hF A' _).trans ((Category.assoc _ x.left ψ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hF A x).symm)))
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨fun A _ _ => ((F A).toMonoidHom.comp (τ' A)).comp (E A).symm.toMonoidHom,
    fun A _ _ => (E A).toMonoidHom.comp (io' A),
    ⟨fun A A' _ _ _ _ g x => ?_, fun A A' _ _ _ _ g χ => ?_, fun A _ _ => (E A).injective.comp (h₃ A),
      fun A _ _ x => ?_, fun A _ _ π hn y hy => ?_⟩, fun A _ _ x => ?_⟩
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A' (τ' A' ((E A').symm _)) = _ ≫ F A (τ' A ((E A).symm _))
    rw [← nE, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, h₁, nF]
  · change E A' (io' A' _) = _ ≫ E A (io' A χ)
    rw [h₂, nE]
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A (τ' A ((E A).symm _)) = 1 ↔ ∃ χ, E A (io' A χ) = _
    rw [MulEquiv.symm_apply_apply, MulEquiv.map_eq_one_iff, h₄]
    exact exists_congr fun χ => (E A).injective.eq_iff.symm
  · obtain ⟨y, rfl⟩ := (F A).surjective y
    rw [← nF, MulEquiv.map_eq_one_iff] at hy
    obtain ⟨x, hx, rfl⟩ := h₅ A π hn y hy
    refine ⟨E A x, by rw [← nE, hx, map_one], ?_⟩
    change F A (τ' A ((E A).symm _)) = _
    rw [MulEquiv.symm_apply_apply]
  · refine ⟨(E A).symm x, (hE A _).symm.trans ?_, hF A _⟩
    rw [MulEquiv.apply_symm_apply]

theorem exists_isTorExt : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  intro W _ _ I D G _ _ g Ω _ β hβ
  let β₀ : W ⧸ I ^ (0 + 1) →+* Ω := Ideal.Quotient.lift _ β (by simpa using hβ)
  have e : spMap β₀ ≫ Out.thick W I 0 = spMap β := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    rfl
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have := (H1.torus_dim (Sp (W ⧸ I ^ (0 + 1))) D.X).smooth
  have : Smooth g.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback g.i g.q g.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact g.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨τ, io, h, hτ⟩ := exists_isTorExt_of_pullback (isGrpPullback_pullback G (Out.thick W I 0))
    (isGrpPullback_pullback D.P.A (Out.thick W I 0)) e (isTorExt_of_kernel (spMap β₀) g.i g.q g.isKernel)
  refine ⟨τ, io, h, fun A _ _ x x₀ hx => ?_⟩
  obtain ⟨x', h₁, h₂⟩ := hτ A x
  have : IsClosedImmersion (Out.thick W I 0) := .spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain rfl : x₀ = x'.left := (cancel_mono (pullback.fst G.hom (Out.thick W I 0))).1 (hx.trans h₁.symm)
  exact h₂.trans (Category.assoc _ _ _)

end GlobalTheory.TorExtPoints
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair



theorem transfer_of_unif : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  intro W _ _ I D Av G _ _ U Ω _ β hβ τ hτ n A _ _ x y h
  let β₀ : W ⧸ I ^ (0 + 1) →+* A := Ideal.Quotient.lift _ ((algebraMap Ω A).comp β) fun a ha => by
    rw [zero_add, pow_one] at ha
    rw [RingHom.comp_apply, hβ a ha, map_zero]
  let T₀ : Over (Spec (CommRingCat.of (W ⧸ I ^ (0 + 1)))) := Over.mk (spMap β₀)
  have hT : T₀.hom ≫ Out.thick W I 0 = (overAt (spMap β) A).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let ρ : overAt (spMap β) A ⟶ Over.mk (T₀.hom ≫ Out.thick W I 0) :=
    Over.homMk (𝟙 (Sp A)) ((Category.id_comp _).trans hT)
  let φ : (T₀ ⟶ Out.thickObj W I 0 G) →* (overAt (spMap β) A ⟶ G) :=
    (preHom ρ).comp (UU.toBaseHom (UU.toBase_mul_pullback G (Out.thick W I 0)) T₀)
  have hφ : ∀ r, (φ r).left = r.left ≫ (Out.fstG I 0 G).left := fun r => Category.id_comp _
  have hψ : ∀ r, (τ A (φ r)).left = r.left ≫ (U.gt 0).pG.left := fun r => hτ A _ _ (hφ r).symm
  have inj : Function.Injective φ := fun r s e => Over.OverMorphism.ext (pullback.hom_ext
    ((hφ r).symm.trans ((congrArg (·.left) e).trans (hφ s))) ((Over.w r).trans (Over.w s).symm))
  have surj : Function.Surjective φ := fun v =>
    ⟨Over.homMk (pullback.lift v.left T₀.hom ((Over.w v).trans hT.symm)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  obtain ⟨x, rfl⟩ := surj x
  obtain ⟨y, rfl⟩ := surj y
  have hx : x ^ n = 1 := inj ((map_pow φ x n).trans (h.1.trans (map_one φ).symm))
  have hy : y ^ n = 1 := inj ((map_pow φ y n).trans (h.2.1.trans (map_one φ).symm))
  refine ⟨by rw [← map_pow, h.1, map_one], by rw [← map_pow, h.2.1, map_one], fun z J hJ => ?_⟩
  obtain ⟨N, hN⟩ := UU.exists_good_pt U.LG.isLB (Z := Sp A) z
  have key : ∀ a b d : T₀ ⟶ Out.thickObj W I 0 G,
      cubV D.toPre.cub z J (τ A (φ a)) (τ A (φ b)) (τ A (φ d)) *
        TorusInvariance.wVal U 0 z J N (a * b).left * TorusInvariance.wVal U 0 z J N (a * d).left *
        TorusInvariance.wVal U 0 z J N (b * d).left * TorusInvariance.wVal U 0 z J N (1 : T₀ ⟶ _).left =
      TorusInvariance.wVal U 0 z J N (a * b * d).left * TorusInvariance.wVal U 0 z J N a.left *
        TorusInvariance.wVal U 0 z J N b.left * TorusInvariance.wVal U 0 z J N d.left *
        cubV U.cubG z N (φ a) (φ b) (φ d) := by
    intro a b d
    have e := TorusInvariance.cube_val U (T := T₀) ![a, b, d] hJ hN
    have t₁ : WCub.tri (Out.thick W I 0) (U.gt 0).pG ![a, b, d] =
        (lift (τ A (φ a)) (lift (τ A (φ b)) (τ A (φ d)))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hψ] <;> rfl
    have t₂ : WCub.tri (Out.thick W I 0) (Out.fstG I 0 G) ![a, b, d] =
        (lift (φ a) (lift (φ b) (φ d))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hφ] <;> rfl
    have p : ∀ k : thK.{0}, (psum (Out.thickObj W I 0 G) ![a, b, d] k.down).left =
        (lift a (lift b d)).left ≫ thφ _ (x3 (Out.thickObj W I 0 G)) k := fun k =>
      congrArg (·.left) ((congrArg (fun q => psum _ q k.down) (funext fun i => by
        fin_cases i <;> simp [x3, preHom])).trans
        (psum_hom (preHom (lift a (lift b d))) (x3 (Out.thickObj W I 0 G)) k.down).symm)
    rw [t₁, t₂] at e
    simp only [p] at e
    exact UU.cub_alg (e.trans (congrArg₂ (· * ·) (prod_cub a b d (TorusInvariance.wVal U 0 z J N)) rfl))
  refine UU.cubN_ratio_twist ((τ A).comp φ) (fun r => TorusInvariance.wVal U 0 z J N r.left)
    (θ := cubV D.toPre.cub z J) (θ' := fun a b d => cubV U.cubG z N (φ a) (φ b) (φ d)) key hx hy ?_
  simpa only [cubN, map_mul, map_pow, map_one] using h.2.2 z N hN

end GlobalTheory.AlphaPair
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.Reduce

open Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def addDefect (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R) (i : Fin d) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.subst (fun q : Fin 2 × Fin d =>
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) (F i) -
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) (ga i)

def cob (F : Fin d → PS R 2 d) (b : PS R 1 d) : PS R 2 d :=
  ev (n := 2) ![addOf F (pt R d 0) (pt R d 1)] b - ev (n := 2) ![pt R d 0] b - ev (n := 2) ![pt R d 1] b

theorem map_addDefect (ψ : R →+* S) (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R)
    (h0 : ∀ i, PowerSeries.constantCoeff (ga i) = 0) (i : Fin d) :
    MvPowerSeries.map ψ (addDefect F ga i) =
      addDefect (fun i => MvPowerSeries.map ψ (F i)) (fun i => PowerSeries.map ψ (ga i)) i := by
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X k : MvPowerSeries (Fin 2) R)) := fun k =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hA : MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hq : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin d =>
      MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q =>
      MvPowerSeries.constantCoeff_subst_eq_zero (hX q.1) (fun _ => by simp) (h0 q.2))
  unfold addDefect
  rw [map_sub, MvPowerSeries.map_subst hq, MvPowerSeries.map_subst hA]
  simp only [MvPowerSeries.map_subst (hX _), map_add (f := _), MvPowerSeries.map_X]
  rfl

theorem map_cob (ψ : R →+* S) (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0)
    (b : PS R 1 d) :
    MvPowerSeries.map ψ (cob F b) = cob (fun i => MvPowerSeries.map ψ (F i)) (MvPowerSeries.map ψ b) := by
  unfold cob
  rw [map_sub, map_sub,
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_add F hF _ _ (cz_pt _) (cz_pt _) k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    mp_cons, mp_cons, mp_cons, mp_nil, mp_add ψ _ _ _ (cz_pt _) (cz_pt _), mp_pt, mp_pt]

theorem map_cubicalTermLinearAlongTangent (ψ : R →+* S) (ph2 : PS R 3 d) (u : Fin d → R) :
    MvPowerSeries.map ψ (c2 ph2 u) = c2 (MvPowerSeries.map ψ ph2) (fun i => ψ (u i)) := by
  ext mu
  rw [MvPowerSeries.coeff_map]
  change ψ (∑ i : Fin d, _) = ∑ i : Fin d, _

  simp only [map_sum, map_mul, MvPowerSeries.coeff_map]

theorem map_map {T σ : Type} [CommRing T] (ψ : R →+* S) (χ : S →+* T) (f : MvPowerSeries σ R) :
    MvPowerSeries.map (χ.comp ψ) f = MvPowerSeries.map χ (MvPowerSeries.map ψ f) := by
  ext mu
  simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]

end Ring

theorem exists_lift {C : Type} [Field C] (V : VF C) {σ : Type} (f : MvPowerSeries σ C)
    (hf : ∀ mu, V.Ge 0 (MvPowerSeries.coeff mu f)) :
    ∃ g : MvPowerSeries σ V.RR, MvPowerSeries.map V.RR.subtype g = f :=
  ⟨fun mu => ⟨MvPowerSeries.coeff mu f, hf mu⟩, by ext mu; rfl⟩

theorem degenerate_of_not_ndg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (d : ℕ) (Y : FBChart C V O d) (R₀ : Type) [CommRing R₀] (j : R₀ →+* V.RR) (F : Fin d → PS R₀ 2 d) (ph2 : PS R₀ 3 d), (∀ i, MvPowerSeries.constantCoeff (F i) = 0) → (∀ i, Y.B.G.F i = MvPowerSeries.map (V.RR.subtype.comp j) (F i)) → Y.B.ph2 = MvPowerSeries.map (V.RR.subtype.comp j) ph2 → ∀ (Ω : Type) [Field Ω] (ρ : V.RR →+* Ω), (∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C)) → ¬ NDG Y → Degenerate V.l (fun i => MvPowerSeries.map (ρ.comp j) (F i)) (MvPowerSeries.map (ρ.comp j) ph2) := by
  intro C _ _ V O _ _ d Y R₀ _ j F ph2 hF0 hF hph Ω _ ρ hρ hN
  unfold NDG at hN
  push Not at hN
  obtain ⟨ga, hcv, ⟨i₀, hi₀⟩, hadd, b, hb, hcob⟩ := hN
  have hlift : ∀ i, ∃ g : PowerSeries V.RR, PowerSeries.map V.RR.subtype g = ga i := fun i =>
    ⟨PowerSeries.mk fun n => ⟨PowerSeries.coeff n (ga i), (hcv i).2 n⟩, by ext n; simp⟩
  choose g hg using hlift
  obtain ⟨bR, rfl⟩ := exists_lift V b hb
  obtain rfl : ga = fun i => PowerSeries.map V.RR.subtype (g i) := funext fun i => (hg i).symm
  have hg0 : ∀ i, PowerSeries.constantCoeff (g i) = 0 := fun i => by
    have := (hcv i).1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    exact Subtype.ext this
  have hFR : Y.B.G.F = fun i => MvPowerSeries.map V.RR.subtype (MvPowerSeries.map j (F i)) :=
    funext fun i => by rw [hF i, map_map]
  have hFR0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.map j (F i)) = 0 := fun i => by
    rw [MvPowerSeries.constantCoeff_map, hF0 i, map_zero]
  rw [map_map] at hph
  simp only [map_map]
  refine ⟨fun i => PowerSeries.map ρ (g i), fun i => ?_, ⟨i₀, ?_⟩, fun i mu h0 h1 => ?_,
    MvPowerSeries.map ρ bR, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0 i, map_zero]
  · rw [PowerSeries.coeff_map] at hi₀ ⊢
    exact fun h => hi₀ ((hρ _).1 h)
  · have h : V.MM (MvPowerSeries.coeff mu (addDefect Y.B.G.F (fun i => PowerSeries.map V.RR.subtype (g i)) i)) :=
      hadd i mu h0 h1
    rw [hFR, ← map_addDefect V.RR.subtype _ g hg0 i, MvPowerSeries.coeff_map] at h
    change MvPowerSeries.coeff mu (addDefect (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i)))
      (fun i => PowerSeries.map ρ (g i)) i) = 0
    rw [← map_addDefect ρ _ g hg0 i, MvPowerSeries.coeff_map]
    exact (hρ _).2 h
  · change _ = cob (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i))) (MvPowerSeries.map ρ bR)
    simp only [PowerSeries.coeff_map]
    rw [← map_cob ρ _ hFR0, ← map_cubicalTermLinearAlongTangent, ← sub_eq_zero, ← map_sub]
    ext mu
    have h : V.MM (MvPowerSeries.coeff mu (c2 Y.B.ph2 (fun i => PowerSeries.coeff 1
        (PowerSeries.map V.RR.subtype (g i))) - cob Y.B.G.F (MvPowerSeries.map V.RR.subtype bR))) := hcob mu
    simp only [PowerSeries.coeff_map] at h
    rw [hFR, hph, ← map_cob V.RR.subtype _ hFR0, ← map_cubicalTermLinearAlongTangent, ← map_sub, MvPowerSeries.coeff_map] at h
    rw [MvPowerSeries.coeff_map, map_zero]
    exact (hρ _).2 h

end GlobalTheory.AlphaPair.Reduce
end
end
