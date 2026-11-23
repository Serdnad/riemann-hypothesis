module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle053
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_bijective_of_flat_preimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsPreimmersion f] [Flat f] (x : X) :
    Function.Bijective (f.stalkMap x).hom := by
  refine ⟨?_, f.stalkMap_surjective x⟩
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem spMap_flat_preimmersion {O F : Type} [CommRing O] [Field F] (β : O →+* F) (hi : Function.Injective β)
    (hq : ∀ x : F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) : IsPreimmersion (spMap β) ∧ Flat (spMap β) := by
  haveI : IsDomain O := hi.isDomain β
  letI : Algebra O F := β.toAlgebra
  have hal : ∀ a : O, algebraMap O F a = β a := fun _ => rfl
  have hfr : IsLocalization (nonZeroDivisors O) F :=
    { map_units := fun y => by
        refine IsUnit.mk0 _ ?_
        rw [hal]
        exact fun h => nonZeroDivisors.ne_zero y.2 (hi (h.trans (map_zero β).symm))
      surj := fun z => by
        obtain ⟨a, b, hb, e⟩ := hq z
        have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
        exact ⟨(a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩), e⟩
      exists_of_eq := fun {x y} e => ⟨1, by rw [hi e]⟩ }
  refine ⟨IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F), ?_⟩
  have hfl : Module.Flat O F := IsLocalization.flat F (nonZeroDivisors O)
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 hfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem j_flat_preimmersion {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hi : Function.Injective β) (hq : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) :
    IsPreimmersion Y.j ∧ Flat Y.j := by
  obtain ⟨h1, h2⟩ := spMap_flat_preimmersion β hi hq
  have h3 : IsPreimmersion (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h1
  have h4 : Flat (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip h2
  have := Y.jQ_open
  exact ⟨inferInstanceAs (IsPreimmersion (Y.jQ ≫ pullback.fst _ _)), inferInstanceAs (Flat (Y.jQ ≫ pullback.fst _ _))⟩

theorem cptOver_isOpen_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ U' : (Xo.XF c).Opens, (U' : Set (Xo.XF c)) = U ∧ ∀ p : Xo.XF c, p ∈ U → IsDomain ((Xo.XF c).presheaf.stalk p) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z ⟨hi, hN, hq⟩
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hi hq
  have hP : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hLN : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have ho := isOpen_closure_genPt (Z.ξ₀ ≫ Y.j) Z.gen
  have hU : U = Y.j ⁻¹' closure {genPt (Z.ξ₀ ≫ Y.j)} := by
    ext u
    rw [Z.closure u, Set.mem_preimage, ← specializes_iff_mem_closure]
    exact (Y.j.isEmbedding.isInducing.specializes_iff).symm
  refine ⟨⟨U, hU ▸ ho.preimage Y.j.continuous⟩, rfl, fun p _ => ?_⟩
  haveI := (Y.normal (Y.j p)).1
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j p
  exact ((RingEquiv.ofBijective _ hb).symm.injective.isDomain (RingEquiv.ofBijective _ hb).symm.toRingHom)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def baseFn {O : Type} [CommRing O] (s : X ⟶ Sp O) (o : O) : Γ(X, ⊤) :=
  s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)


set_option backward.isDefEq.respectTransparency false in
theorem baseFn_value {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (s : X ⟶ Sp O) (f : Sp R ⟶ X)
    (φ : O →+* R) (hf : f ≫ s = spMap φ) (o : O) :
    (Scheme.stalkClosedPointTo f).hom (X.presheaf.germ ⊤ (centre f) trivial (baseFn s o)) = φ o := by
  have e : X.presheaf.germ ⊤ (f (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo f =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    set_option backward.isDefEq.respectTransparency.types false in
      rw [Scheme.germ_stalkClosedPointTo]
      simp [Iso.trans_hom, Scheme.Hom.appTop]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ f.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom φ := by
    rw [← Category.assoc s.appTop, ← Scheme.Hom.comp_appTop, hf, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  rw [← e] at e2
  exact congrArg (fun q => q.hom o) e2


set_option backward.isDefEq.respectTransparency false in
theorem genMap_germ (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (g : Γ(X, ⊤)) :
    genMap ξ p (X.presheaf.germ ⊤ p.1 trivial g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ ⊤ (genPt ξ) trivial g) := by
  have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := ⊤) (x := genPt ξ) (y := p.1) trivial p.2
  have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom g) e
  exact e2


set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes (ξ : Sp Ω ⟶ X) (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf p.2 h
  have e2 := congrArg (fun r => (r ≫ Scheme.stalkClosedPointTo ξ).hom s) e
  exact e2

theorem exists_inv {A L₁ L₂ : Type} [CommRing A] [Field L₁] [Field L₂] (f₁ : A →+* L₁) (f₂ : A →+* L₂)
    (hl : ∀ b, IsUnit (f₂ b) → IsUnit b) (g : A) (a₁ : L₁) (a₂ : L₂) (ha : a₂ ≠ 0)
    (h₁ : f₁ g = a₁⁻¹) (h₂ : f₂ g = a₂⁻¹) : ∃ u, f₁ u = a₁ ∧ f₂ u = a₂ := by
  obtain ⟨g, rfl⟩ := hl g (by rw [h₂]; exact (inv_ne_zero ha).isUnit)
  refine ⟨(g⁻¹ : Aˣ), ?_, ?_⟩
  · have := map_units_inv f₁.toMonoidHom g
    refine this.trans ?_
    show (f₁ g)⁻¹ = _
    rw [h₁, inv_inv]
  · have := map_units_inv f₂.toMonoidHom g
    refine this.trans ?_
    show (f₂ g)⁻¹ = _
    rw [h₂, inv_inv]

def valMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) : regAt ξ p →+* R :=
  ev.comp (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm.toRingHom

theorem valMap_genMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) (s : X.presheaf.stalk p.1) (h : genMap ξ p s ∈ regAt ξ p) :
    valMap ξ p hi ev ⟨genMap ξ p s, h⟩ = ev s := by
  have : (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm
      ⟨genMap ξ p s, h⟩ = s := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show ev _ = ev s
  exact congrArg ev this

variable {O F V K : Type} [CommRing O] [Field F] [CommRing V] [IsLocalRing V] [Field K] [Algebra V K]

theorem exists_germ (ξ : Sp Ω ⟶ X) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K) (y : Sp K ⟶ X)
    (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β)) (h₁ : genPt ξ ⤳ centre y) (x : F)
    (hx : x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ u : X.presheaf.stalk (centre y), genMap ξ ⟨_, h₁⟩ u = inc x ∧ (Scheme.stalkClosedPointTo y).hom u = βK x := by
  have key : ∀ o : O, genMap ξ ⟨_, h₁⟩ (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = inc (β o) ∧
      (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = βK (β o) := by
    intro o
    refine ⟨?_, baseFn_value s y (βK.comp β) hy o⟩
    exact (genMap_germ ξ ⟨_, h₁⟩ (baseFn s o)).trans (baseFn_value s ξ (inc.comp β) hξ o)
  by_cases h0 : x = 0
  · subst h0
    exact ⟨0, (map_zero _).trans (map_zero inc).symm,
      (map_zero (Scheme.stalkClosedPointTo y).hom).trans (map_zero βK).symm⟩
  rcases hx with ⟨o, rfl⟩ | ⟨o, ho⟩
  · exact ⟨_, key o⟩
  obtain ⟨k1, k2⟩ := key o
  rw [ho] at k1 k2
  exact exists_inv (genMap ξ ⟨_, h₁⟩) (Scheme.stalkClosedPointTo y).hom
    (fun b hb => (Scheme.isLocalHom_stalkClosedPointTo' y).map_nonunit b hb) _ (inc x) (βK x) ((map_ne_zero βK).2 h0)
    (k1.trans (map_inv₀ inc x)) (k2.trans (map_inv₀ βK x))

theorem val_abs (ξ : Sp Ω ⟶ X) (hg : IsCptGen ξ) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K)
    (y : Sp K ⟶ X) (z : Sp V ⟶ X) (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β))
    (hz : spMap (algebraMap V K) ≫ z = y) (h₁ : genPt ξ ⤳ centre y)
    (hF : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K),
      centre y ⤳ centre z ∧ regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ ∧
      (∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a)) ∧
      (∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : F, ∃ h : inc x ∈ regAt ξ ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  have hsp : centre y ⤳ centre z := by
    subst hz
    exact (IsLocalRing.specializes_closedPoint _).map z.continuous
  have h₂ : genPt ξ ⤳ centre z := h₁.trans hsp
  let ψ : regAt ξ ⟨_, h₁⟩ →+* K := valMap ξ ⟨_, h₁⟩ (hg.inj _) (Scheme.stalkClosedPointTo y).hom
  have c3 : ∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a) := by
    rintro ⟨_, s', rfl⟩
    exact ⟨h₁, s', rfl, (valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _).symm⟩
  have c4 : ∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r := by
    rintro a r ⟨h, s', rfl, rfl⟩
    exact ⟨⟨s', rfl⟩, valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _⟩
  refine ⟨h₂, ψ, hsp, ?_, c3, c4, ?_, ?_⟩
  · rintro _ ⟨s', rfl⟩
    refine ⟨(X.presheaf.stalkSpecializes hsp).hom s', ?_⟩
    exact genMap_specializes ξ ⟨_, h₁⟩ ⟨_, h₂⟩ hsp s'
  · rintro a h ⟨s', rfl⟩
    have v : ValAt ξ z (genMap ξ ⟨_, h₂⟩ s') ((Scheme.stalkClosedPointTo z).hom s') := ⟨h₂, s', rfl, rfl⟩
    have v' := GlobalTheory.T.valAt_comp_local_hom X Ω ξ V K (algebraMap V K) z _ _ v (by rw [hz]; exact h₁)
    rw [hz] at v'
    obtain ⟨h', e⟩ := c4 _ _ v'
    exact ⟨_, e.symm⟩
  · intro x
    obtain ⟨u, e1, e2⟩ := exists_germ ξ s inc β βK y hξ hy h₁ x (hF x)
    obtain ⟨h, e⟩ := c4 _ _ (⟨h₁, u, e1, e2⟩ : ValAt ξ y (inc x) (βK x))
    exact ⟨h, e⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem point_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X),
    Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) →
    j.comp βK = κ → y ≫ pullback.snd _ _ = spMap βK → Set.range y ⊆ U → spMap (algebraMap V K) ≫ z = y ≫ Y.j →
    ∃ (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
      (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K),
      centre (y ≫ Y.j) ⤳ centre z ∧ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ ∧
      (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) ∧
      (∀ (a : Z.Ω) (r : K), ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ →
        ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : c.F, ∃ h : Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z p κ V K _ _ _ _ _ _ j βK y z hβ hκ hj hjk hy hU hz
  have hsj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hξ : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, Z.over_inc, ← Spec.map_comp]
    rfl
  have hy' : (y ≫ Y.j) ≫ Y.s = spMap (βK.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, hy, ← Spec.map_comp]
    rfl
  have h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) :=
    ((Z.closure _).1 (hU ⟨IsLocalRing.closedPoint K, rfl⟩)).map Y.j.continuous
  have hF : ∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range := by
    intro x
    by_cases h : ‖κ x‖ ≤ 1
    · exact Or.inl ((hκ x).1 h)
    · refine Or.inr ((hκ _).1 ?_)
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
  obtain ⟨h₂, ψ, r⟩ := PointVal.val_abs (Z.ξ₀ ≫ Y.j) Z.gen Y.s Z.inc β βK (y ≫ Y.j) z hξ hy' hz h₁ hF
  exact ⟨h₁, h₂, ψ, r⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstVal

def constGerm {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))

theorem genMap_constGerm {X : Scheme.{0}} {Ω O : Type} [Field Ω] [CommRing O] (f : O →+* Ω)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom f)) (p : Cpt ξ) (o : O) :
    genMap ξ p (constGerm s p.1 o) = f o := by
  letI : Algebra O Ω := f.toAlgebra
  exact ConstReg.genMap_germ_const ξ s hs p o

theorem genMap_self {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X)
    (x : X.presheaf.stalk (genPt z)) :
    genMap z ⟨genPt z, specializes_rfl⟩ x = (Scheme.stalkClosedPointTo z).hom x := by
  have e₀ : X.presheaf.stalkSpecializes (specializes_rfl (x := genPt z)) ≫ Scheme.stalkClosedPointTo z =
      Scheme.stalkClosedPointTo z := by
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Category.id_comp _
  exact congrArg (fun q => q.hom x) e₀

def closedMap {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X) :
    X.presheaf.stalk (centre z) →+* F :=
  (Scheme.stalkClosedPointTo z).hom

theorem closedPoint_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) :
    closedMap z (constGerm s (centre z) o) = f o :=
  (genMap_self z _).symm.trans (genMap_constGerm f z s hs ⟨genPt z, specializes_rfl⟩ o)

theorem isUnit_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) (ho : f o ≠ 0) :
    IsUnit (constGerm s (centre z) o) := by
  have h1 : IsUnit (closedMap z (constGerm s (centre z) o)) := by
    rw [closedPoint_constGerm f z s hs o]
    exact ho.isUnit
  haveI : IsLocalHom (closedMap z) := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  exact isUnit_of_map_unit (closedMap z) _ h1

theorem map_frac {A L K O : Type} [CommRing A] [CommRing L] [Field K] [CommRing O] (β : O →+* K) (g : O → A)
    (φ : A →+* L) (e : K →+* L) (h : ∀ o, φ (g o) = e (β o)) {a b : O} {k : K} (hk : k * β b = β a)
    (u : Aˣ) (hu : (u : A) = g b) : φ (g a * ↑u⁻¹) = e k := by
  have hw : e (β b) * φ ↑u⁻¹ = 1 := by
    rw [← h b, ← hu, ← map_mul, u.mul_inv, map_one]
  rw [map_mul, h a, ← hk, map_mul, _root_.mul_assoc, hw, _root_.mul_one]

theorem valAt_of_frac {X : Scheme.{0}} {K Ω F O : Type} [Field K] [Field Ω] [Field F] [CommRing O]
    (β : O →+* K) (inc : K →+* Ω) (βF : K →+* F)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of F) ⟶ X)
    (s : X ⟶ Spec (CommRingCat.of O))
    (hξ : ξ ≫ s = Spec.map (CommRingCat.ofHom (inc.comp β)))
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom (βF.comp β)))
    (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (h : genPt ξ ⤳ centre z) (k : K) : ValAt ξ z (inc k) (βF k) := by
  obtain ⟨a, b, hb, hk⟩ := hfr k
  obtain ⟨u, hu⟩ := isUnit_constGerm (βF.comp β) z s hz b ((map_ne_zero βF).2 hb)
  have e₁ : genMap ξ ⟨centre z, h⟩ (constGerm s (centre z) a * ↑u⁻¹) = inc k :=
    map_frac β (constGerm s (centre z)) (genMap ξ ⟨centre z, h⟩) inc
      (fun o => genMap_constGerm (inc.comp β) ξ s hξ ⟨centre z, h⟩ o) hk u hu
  have e₂ : closedMap z (constGerm s (centre z) a * ↑u⁻¹) = βF k :=
    map_frac β (constGerm s (centre z)) (closedMap z) βF
      (fun o => closedPoint_constGerm (βF.comp β) z s hz o) hk u hu
  exact ⟨h, _, e₁, e₂⟩

theorem constants_compose_structure {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {R : Type} [CommRing R] (w : Sp R ⟶ Xo.XF c) (f : c.F →+* R) (hw : w ≫ pullback.snd _ _ = spMap f) :
    (w ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom (f.comp β)) := by
  have h1 : (w ≫ Y.j) ≫ Y.s = (w ≫ pullback.snd _ _) ≫ spMap β := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  rw [h1, hw, CommRingCat.ofHom_comp, Spec.map_comp]

theorem valAt_inc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap βF → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → ∀ k : c.F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (Z.inc k) (βF k) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ βF y hfr hy hsp k
  exact valAt_of_frac β Z.inc βF (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) Y.s (constants_compose_structure Y _ _ Z.over_inc)
    (constants_compose_structure Y _ _ hy) hfr hsp k

end GlobalTheory.CompanionTheory.Ar.Flat.ConstVal
end
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_V_inr_iff_latOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inr τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hF hpS τ σ hσ s q hs hq e
  have hp : p.Prime := Fact.out
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p := by
    intro r hrS hrq
    by_contra hne
    have hloc : IsLocalRing (regAt 𝔐.ξ q) :=
      IsLocalRing.of_surjective' (genMap 𝔐.ξ q).rangeRestrict
        (genMap 𝔐.ξ q).rangeRestrict_surjective
    have key : ∀ m : ℕ, InFibre 𝔐.ξ m q → ¬ IsUnit ((m : regAt 𝔐.ξ q)) := by
      intro m hm hu
      apply hm
      obtain ⟨u, hu'⟩ := hu
      have h1 : (m : Ω) * (((u⁻¹ : (regAt 𝔐.ξ q)ˣ) : regAt 𝔐.ξ q) : Ω) = 1 := by
        have h2 := congrArg (fun x : regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
        simpa [hu'] using h2
      have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
      refine ⟨h0, natCast_mem _ m, ?_⟩
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    have hcop : Nat.Coprime r p := (Nat.coprime_primes (𝔐.S_prime r hrS) hp).2 hne
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (regAt 𝔐.ξ q))
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
    · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)
  have hV : 𝔐.V (Sum.inr τ) q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (Sum.inr τ)) q := by
    unfold HodgeCpt.V
    rw [Lat.patch_of_unique _ _ _ hpS hq hu]
    rfl
  have hσ' : ∀ a : 𝓞 E, 𝔐.emb (Sum.inr τ) a = (σ.comp (cmConj E).toRingHom) (a : E) := by
    intro a
    have h1 : 𝔐.emb (Sum.inr τ) a = 𝔐.emb (Sum.inl τ) (H.bar a) := rfl
    rw [h1, ← hσ, H.bar_eq]
    rfl
  have hom := hF.om'_loc s q hs hq
  rw [hV, LieModel.mem_htDual_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, fun w hw => ?_⟩
    · have := (Submodule.mem_iInf _).mp h1 a
      rw [← hσ' a]
      simpa [sub_eq_zero] using this
    · rw [one_mul]
      refine h2 w ?_
      have : w ∈ HT.omP 𝔐 p q := by
        rw [hom]
        exact Submodule.subset_span hw
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨(Submodule.mem_iInf _).mpr fun a => ?_, fun w hw => ?_⟩
    · have := HT.LatBasic.mem_eigSp.1 h1 a
      rw [← hσ' a] at this
      simpa [sub_eq_zero] using this
    · have hw' : w ∈ HT.omP 𝔐 p q := hw
      rw [hom] at hw'
      clear hw
      induction hw' using Submodule.span_induction with
      | mem x hx => simpa using h2 x hx
      | zero => simpa using (regAt 𝔐.ξ q).zero_mem
      | add x y _ _ hx hy => simpa using (regAt 𝔐.ξ q).add_mem hx hy
      | smul c x _ hx =>
        have : (c • x) e = (c : Ω) * x e := rfl
        rw [this]
        exact (regAt 𝔐.ξ q).mul_mem c.2 hx

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.centre_set_dominating_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Centre.exists_centre | exact GlobalTheory.CompanionTheory.Ar.Centre.exists_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Centre.exists_centre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.existsUnique_dominating_map : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω') (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) → ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates | exact GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates <;> assumption)
end
