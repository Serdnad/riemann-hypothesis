module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem isPushout_app_of_isPullback {X X₁ T T₁ : Scheme.{0}} {f : X₁ ⟶ X} {p₁ : X₁ ⟶ T₁} {p : X ⟶ T}
    {j : T₁ ⟶ T} (h : IsPullback f p₁ p j) [IsAffine T] [IsAffine T₁] {W : X.Opens}
    (hW : IsAffineOpen W) :
    IsAffineOpen (f ⁻¹ᵁ W) ∧
      IsPushout (p.appLE ⊤ W le_top) j.appTop (f.app W) (p₁.appLE ⊤ (f ⁻¹ᵁ W) le_top) := by
  have : IsAffine W.toScheme := hW
  have sq : IsPullback (f ∣_ W) ((f ⁻¹ᵁ W).ι ≫ p₁) (W.ι ≫ p) j :=
    (isPullback_morphismRestrict f W).paste_vert h
  have : IsAffine (f ⁻¹ᵁ W).toScheme := IsAffine.of_isPullback sq
  refine ⟨this, ?_⟩
  exact (ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip inferInstance (isAffineOpen_top T) hW le_top le_top).flip

theorem appLE_congr_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (e : a = b) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ a ⁻¹ᵁ U) (h' : V ≤ b ⁻¹ᵁ U) : a.appLE U V h = b.appLE U V h' := by
  subst e; rfl

theorem isPullback_app_of_affine {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W))
    (hV : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V) :
    IsPullback (f₁.app W) (f₂.app W) (g₁.appLE _ V hV₁) (g₂.appLE _ V hV₂) := by
  have := hM.aff; have := hM.aff₁; have := hM.aff₂; have := hM.closed
  obtain ⟨hT₀, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine k₂
  obtain ⟨hU₁, P₁⟩ := isPushout_app_of_isPullback h₁ hW
  obtain ⟨hU₂, P₂⟩ := isPushout_app_of_isPullback h₂ hW
  obtain ⟨-, P₀⟩ := isPushout_app_of_isPullback h₀ hU₂
  have hVe : V = g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := by
    refine le_antisymm hV₂ ?_
    have : g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
    exact this.le.trans hV
  subst hVe
  have e₂ : g₂.appLE (f₂ ⁻¹ᵁ W) (g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) hV₂ = g₂.app (f₂ ⁻¹ᵁ W) :=
    Scheme.Hom.appLE_eq_app ..
  rw [e₂]
  have hfl : (p.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  refine GlobalTheory.T.commRingCat_isPullback_flat_baseChange_surjective _ _ _ _ _ _ _ _ j₁.appTop j₂.appTop k₁.appTop k₂.appTop hM.cart hsurj _ _ _ _ _ _ _ _
    hfl P₁ P₂ P₀ ?_ ?_
  · rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_eq hg _ _ _ _
  · have : k₁.appTop = k₁.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app ..).symm
    rw [this]
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    exact appLE_congr_eq hp _ _ _ _

theorem app_restrict_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U W : Y.Opens} (h : U ≤ W) (a : Γ(Y, W)) :
    f.app U (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem appLE_restrict_eq {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (hU : U' ≤ U) (hV : V' ≤ V) (h : V ≤ g ⁻¹ᵁ U) (h' : V' ≤ g ⁻¹ᵁ U') (a : Γ(Y, U)) :
    g.appLE U' V' h' (Y.presheaf.map (homOfLE hU).op a) =
      X.presheaf.map (homOfLE hV).op (g.appLE U V h a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

theorem elem_of_isPullback_ring {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {i : C ⟶ D} (H : IsPullback f g h i) :
    (∀ x y, f x = f y → g x = g y → x = y) ∧ ∀ b c, h b = i c → ∃ a, f a = b ∧ g a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem sections_of_squares {X X₁ X₂ X₀ T T₁ T₂ T₀ : Scheme.{0}} {p : X ⟶ T} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {p₀ : X₀ ⟶ T₀} {j₁ : T₁ ⟶ T} {j₂ : T₂ ⟶ T} {k₁ : T₀ ⟶ T₁} {k₂ : T₀ ⟶ T₂}
    {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X} {g₁ : X₀ ⟶ X₁} {g₂ : X₀ ⟶ X₂} (hM : Milnor j₁ j₂ k₁ k₂)
    (h₁ : IsPullback f₁ p₁ p j₁) (h₂ : IsPullback f₂ p₂ p j₂) (h₀ : IsPullback g₂ p₀ p₂ k₂)
    (hg : g₁ ≫ f₁ = g₂ ≫ f₂) (hp : g₁ ≫ p₁ = p₀ ≫ k₁) [Flat p] (W : X.Opens) :
    (∀ a b : Γ(X, W), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b) ∧
    ∀ (V : X₀.Opens) (hV₁ : V ≤ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W)) (hV₂ : V ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)),
      g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)),
        g₁.appLE _ V hV₁ a₁ = g₂.appLE _ V hV₂ a₂ →
          ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂ := by
  have hpre : ∀ U : X.Opens, g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ U) = g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) := fun U ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg]
  have aff : ∀ U : X.Opens, IsAffineOpen U → IsPullback (f₁.app U) (f₂.app U)
      (g₁.appLE _ (g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U)) le_rfl) (g₂.appLE _ _ (hpre U).ge) :=
    fun U hU ↦ isPullback_app_of_affine hM h₁ h₂ h₀ hg hp hU _ le_rfl (hpre U).ge le_rfl
  have inj : ∀ (U : X.Opens) (a b : Γ(X, U)), f₁.app U a = f₁.app U b →
      f₂.app U a = f₂.app U b → a = b := by
    intro U a b ha hb
    refine TopCat.Presheaf.section_ext X.sheaf U a b fun x hx ↦ ?_
    change X.presheaf.germ U x hx a = X.presheaf.germ U x hx b
    obtain ⟨U', hU', hxU', hle⟩ := exists_isAffineOpen_mem_and_subset hx
    have hle' : U' ≤ U := hle
    rw [← X.presheaf.germ_res_apply (homOfLE hle') x hxU' a,
      ← X.presheaf.germ_res_apply (homOfLE hle') x hxU' b]
    congr 1
    refine (elem_of_isPullback_ring (aff U' hU')).1 _ _ ?_ ?_
    · rw [app_restrict_eq, app_restrict_eq, ha]
    · rw [app_restrict_eq, app_restrict_eq, hb]
  refine ⟨inj W, ?_⟩
  intro V hV₁ hV₂ hV a₁ a₂ he
  have loc : ∀ x : W, ∃ U : X.Opens, IsAffineOpen U ∧ x.1 ∈ U ∧ ∃ hUW : U ≤ W, ∃ c : Γ(X, U),
      f₁.app U c = X₁.presheaf.map (homOfLE (f₁.preimage_mono hUW)).op a₁ ∧
      f₂.app U c = X₂.presheaf.map (homOfLE (f₂.preimage_mono hUW)).op a₂ := by
    intro x
    obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset x.2
    have hUW : U ≤ W := hle
    refine ⟨U, hU, hxU, hUW, (elem_of_isPullback_ring (aff U hU)).2 _ _ ?_⟩
    have hVU : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ U) ≤ V := (g₁.preimage_mono (f₁.preimage_mono hUW)).trans hV
    rw [appLE_restrict_eq g₁ (f₁.preimage_mono hUW) hVU hV₁,
      appLE_restrict_eq g₂ (f₂.preimage_mono hUW) hVU hV₂, he]
  choose U hU hxU hUW c hc₁ hc₂ using loc
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 U c := by
    intro x y
    change X.presheaf.map (homOfLE (inf_le_left : U x ⊓ U y ≤ U x)).op (c x) =
      X.presheaf.map (homOfLE (inf_le_right : U x ⊓ U y ≤ U y)).op (c y)
    apply inj
    · rw [app_restrict_eq, app_restrict_eq, hc₁, hc₁, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [app_restrict_eq, app_restrict_eq, hc₂, hc₂, ← ConcreteCategory.comp_apply,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' U W (fun x ↦ homOfLE (hUW x))
    (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩) c compat
  have ha' : ∀ x, X.presheaf.map (homOfLE (hUW x)).op a = c x := ha
  refine ⟨a, ?_, ?_⟩
  · refine TopCat.Presheaf.section_ext X₁.sheaf _ _ _ fun y hy ↦ ?_
    change X₁.presheaf.germ _ y hy _ = X₁.presheaf.germ _ y hy _
    have hyU : y ∈ f₁ ⁻¹ᵁ U ⟨f₁ y, hy⟩ := hxU ⟨f₁ y, hy⟩
    rw [← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU,
      ← X₁.presheaf.germ_res_apply (homOfLE (f₁.preimage_mono (hUW ⟨f₁ y, hy⟩))) y hyU a₁,
      ← app_restrict_eq f₁ (hUW ⟨f₁ y, hy⟩) a, ha' ⟨f₁ y, hy⟩, hc₁]
  · refine TopCat.Presheaf.section_ext X₂.sheaf _ _ _ fun y hy ↦ ?_
    change X₂.presheaf.germ _ y hy _ = X₂.presheaf.germ _ y hy _
    have hyU : y ∈ f₂ ⁻¹ᵁ U ⟨f₂ y, hy⟩ := hxU ⟨f₂ y, hy⟩
    rw [← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU,
      ← X₂.presheaf.germ_res_apply (homOfLE (f₂.preimage_mono (hUW ⟨f₂ y, hy⟩))) y hyU a₂,
      ← app_restrict_eq f₂ (hUW ⟨f₂ y, hy⟩) a, ha' ⟨f₂ y, hy⟩, hc₂]

theorem sections_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → ∀ W : (A ⊗ T).left.Opens, (∀ a b : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = (A ◁ j₁).left.app W b → (A ◁ j₂).left.app W a = (A ◁ j₂).left.app W b → a = b) ∧ ∀ (V : (A ⊗ T₀).left.Opens) (h₁ : V ≤ (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W)) (h₂ : V ≤ (A ◁ k₂).left ⁻¹ᵁ ((A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ((A ⊗ T₁).left, (A ◁ j₁).left ⁻¹ᵁ W)) (a₂ : Γ((A ⊗ T₂).left, (A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left.appLE _ V h₁ a₁ = (A ◁ k₂).left.appLE _ V h₂ a₂ → ∃ a : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = a₁ ∧ (A ◁ j₂).left.app W a = a₂ := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ hM W
  have : Flat (snd A T).left := inferInstanceAs (Flat (pullback.snd A.hom T.hom))
  have hw : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext hM.w
  have hg : (A ◁ k₁).left ≫ (A ◁ j₁).left = (A ◁ k₂).left ≫ (A ◁ j₂).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hw]
  have hp : (A ◁ k₁).left ≫ (snd A T₁).left = (snd A T₀).left ≫ k₁.left := by
    rw [← Over.comp_left, ← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd]
  exact sections_of_squares hM (isPullback_whiskerLeft_snd_left A j₁)
    (isPullback_whiskerLeft_snd_left A j₂) (isPullback_whiskerLeft_snd_left A k₂) hg hp W

end GlobalTheory.DualOpen
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiNegFieldChange

theorem semiNeg_descends_baseChange : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (k' : Type) [Field k'] [Algebra k k'], ∃ (C' : Scheme.{0}) (_ : Algebra k' Γ(C', ⊤)) (π : C' ⟶ C), IsCurve k' C' ∧
      ∀ F : C.Modules, SemiNeg k' ((Scheme.Modules.pullback π).obj F) → SemiNeg k F := by
  intro k _ C _ hC k' _ _
  obtain ⟨h1, h2, h3⟩ := hC
  let t : Sp k' ⟶ Sp k := spMap (algebraMap k k')
  let f := strHom k C
  letI A' : Algebra k' Γ(pullback f t, ⊤) := algebraΓOfHom (pullback.snd f t)
  have hs : strHom k' (pullback f t) = pullback.snd f t := strHom_eq fun _ => rfl
  refine ⟨pullback f t, A', pullback.fst f t, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hs]; exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback (IsPullback.of_hasPullback f t) h1
  · rw [hs]; exact GlobalTheory.ProjSpace.isProjOver_pullback_snd _ h2
  · rw [hs]; haveI := h3; infer_instance
  · intro F hF W r hW i hi
    have : IsProper f := by
      obtain ⟨N, j, hj, e⟩ := h2
      have := isProper_str k N
      change IsProper (strHom k (X := C))
      rw [← e]
      infer_instance
    have hinst : (‹Algebra k Γ(C, ⊤)›) = algebraΓOfHom f :=
      Algebra.algebra_ext _ _ (algebraMap_eq_strHom k C)
    haveI : Flat (pullback.fst f t) := inferInstance
    have hm := GlobalTheory.T.mono_pullback_map_of_flat' _ _ (pullback.fst f t) W F i
    have h := hF _ r (hW.pullback _) _ hm
    rw [← interNum_congr_lbIso k' _ (isLB_vecOne (LB.isLB_pull hW.isLB_det _)) (isLB_vecOne (hW.pullback _).isLB_det)
      (fun j => by fin_cases j; exact hW.lbIso_det_pullback _)] at h
    have P := FieldChangeInter.interNum_pull (f := f) (f' := pullback.snd f t) (π := pullback.fst f t)
      (IsPullback.of_hasPullback f t) (L := ![det W r]) (isLB_vecOne hW.isLB_det)
    have e₃ : (fun j => ((![det W r] : Fin 1 → LB C) j).pull (pullback.fst f t)) = ![(det W r).pull (pullback.fst f t)] :=
      funext fun j => by fin_cases j; rfl
    rw [e₃] at P
    rw [hinst]
    exact P ▸ h

end GlobalTheory.SemiNegFieldChange
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.SumDual

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem sum_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ G *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

omit [NumberField E] [StarRing E] in
theorem antiDiagonalEpsilonGram_mulVec {c : ℕ} (ε : E) (u : Fin c → E) (p : Fin c) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) p = (if p = p.rev then ε else 1) * u p.rev := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single p.rev]
  · have := p.2
    simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
    rw [if_pos (by omega)]
  · intro q _ hq
    have := p.2
    simp only [antiDiagonalSignGramMatrix]
    rw [if_neg, zero_mul]
    intro h
    exact hq (Fin.ext (by rw [Fin.val_rev]; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gram_herm (S : HSpace E) : S.gramᴴ = S.gram := by
  ext i j
  exact S.herm.eq _ _

theorem hT_eq (S : HSpace E) (x y : S.V) :
    S.hT x y = star (S.frame.equivFun x) ⬝ᵥ S.gram *ᵥ S.frame.equivFun y := by
  rw [← sum_eq_dot]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
  starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, Module.Basis.equivFun_apply, HSpace.gram]
  ring

theorem gram_inj (S : HSpace E) (y : Fin S.rank → E) (h : S.gram *ᵥ y = 0) : y = 0 := by
  obtain ⟨y, rfl⟩ := S.frame.equivFun.surjective y
  rw [S.nondeg.2 y fun x => by rw [hT_eq, h, dotProduct_zero], map_zero]

theorem gram_isom (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (h : HSpace.IsIsomEmb A B ι) :
    (LinearMap.toMatrix A.frame B.frame ι)ᴴ * B.gram * LinearMap.toMatrix A.frame B.frame ι = A.gram := by
  ext i j
  rw [HSpace.gram, ← h, hT_eq, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, LinearMap.toMatrix_apply, Pi.star_apply,
    Module.Basis.equivFun_apply]

theorem selfDual_sum {n k c : ℕ} (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (G : Matrix (Fin n) (Fin n) E) (J : Matrix (Fin k) (Fin k) E) (M : Matrix (Fin n) (Fin k) E)
    (a : Matrix (Fin n) (Fin c) E) (ε : E) (hε : ε = 1 ∨ ε = -1) (hG : Gᴴ = G) (hJ : ∀ y, J *ᵥ y = 0 → y = 0)
    (h1 : Mᴴ * G * M = J) (h2 : Mᴴ * G * a = 0) (h3 : aᴴ * G * a = antiDiagonalSignGramMatrix c ε) (hr : k + c = n)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (𝔟 : Fin c → FractionalIdeal (𝓞 E)⁰ E)
    (hΛ : Submodule.IsLattice E Λ)
    (hΛd : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * J i j * y j)
    (hb : ∀ p, 𝔟 p ≠ 0) (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹)
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ ∃ y ∈ Λ, ∃ u : Fin c → E, (∀ p, u p ∈ 𝔟 p) ∧ x = M *ᵥ y + a *ᵥ u) :
    Submodule.IsLattice E L ∧
      ∀ y, y ∈ L ↔ ∀ x ∈ L, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j := by
  classical
  have h2' : aᴴ * G * M = 0 := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have eM : ∀ y u, Mᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = J *ᵥ y := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h1, h2, zero_mulVec, add_zero]
  have ea : ∀ y u, aᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = antiDiagonalSignGramMatrix c ε *ᵥ u := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h2', h3, zero_mulVec, zero_add]
  have key : ∀ x v y u, ∑ i, ∑ j, star ((M *ᵥ x + a *ᵥ v) i) * G i j * (M *ᵥ y + a *ᵥ u) j =
      (∑ i, ∑ j, star (x i) * J i j * y j) + ∑ p, (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := by
    intro x v y u
    rw [sum_eq_dot, sum_eq_dot, star_add, add_dotProduct, star_mulVec, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, eM, ea]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [antiDiagonalEpsilonGram_mulVec, Pi.star_apply]; ring
  have hsg : ∀ p : Fin c, ∃ e : 𝓞 E, (e : E) = (if p = p.rev then ε else 1) ∧ e * e = 1 := fun p => by
    split_ifs
    · rcases hε with rfl | rfl
      · exact ⟨1, rfl, by simp⟩
      · exact ⟨-1, by simp, by simp⟩
    · exact ⟨1, rfl, by simp⟩
  have hst : ∀ z : E, (∃ b : 𝓞 E, (b : E) = z) → ∃ b : 𝓞 E, (b : E) = star z := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨star (b : E), hs _ b.isIntegral_coe⟩, rfl⟩
  let f : ((Fin k → E) × (Fin c → E)) →ₗ[E] (Fin n → E) := M.mulVecLin.coprod a.mulVecLin
  have hf : ∀ y u, f (y, u) = M *ᵥ y + a *ᵥ u := fun _ _ => rfl
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    rintro ⟨y, u⟩ h
    rw [hf] at h
    have e1 := eM y u
    have e2 := ea y u
    rw [h, mulVec_zero, mulVec_zero] at e1 e2
    refine Prod.ext (hJ y e1.symm) (funext fun p => ?_)
    have e3 := congrFun e2 p.rev
    obtain ⟨e, he, hee⟩ := hsg p.rev
    rw [antiDiagonalEpsilonGram_mulVec, ← he, Fin.rev_rev] at e3
    have he0 : (e : E) ≠ 0 := by
      intro h0
      have : e = 0 := by exact_mod_cast h0
      rw [this] at hee; simp at hee
    exact (mul_eq_zero.1 e3.symm).resolve_left he0
  have fsur : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).1 finj
  refine ⟨⟨?_, ?_⟩, fun y' => ⟨?_, fun h => ?_⟩⟩
  · have : L = (Λ.prod (Submodule.pi Set.univ fun p => (𝔟 p : Submodule (𝓞 E) E))).map (f.restrictScalars (𝓞 E)) := by
      ext x
      rw [hL, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, u, hu, rfl⟩
        exact ⟨(y, u), ⟨hy, fun p _ => hu p⟩, rfl⟩
      · rintro ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
        exact ⟨y, hy, u, fun p => hu p trivial, rfl⟩
    rw [this]
    exact (hΛ.fg.prod (Submodule.fg_pi fun p => FractionalIdeal.fg_of_isNoetherianRing le_rfl _)).map _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro hy' x' hx'
    obtain ⟨y, hy, u, hu, rfl⟩ := (hL _).1 hy'
    obtain ⟨x, hx, v, hv, rfl⟩ := (hL _).1 hx'
    obtain ⟨b, hb1⟩ := (hΛd y).1 hy x hx
    have : ∀ p : Fin c, ∃ t : 𝓞 E, (t : E) = (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := fun p => by
      obtain ⟨e, he, -⟩ := hsg p
      have := (FractionalIdeal.mem_inv_iff (hb p)).1 ((hd p _).1 (hu p.rev)) _ (hv p)
      obtain ⟨t, ht⟩ := hst _ ((FractionalIdeal.mem_one_iff _).1 this)
      refine ⟨e * t, ?_⟩
      rw [← he, RingOfIntegers.coe_eq_algebraMap, map_mul]
      congr 1
      refine ht.trans ?_
      rw [star_mul, star_star]
    choose t ht using this
    refine ⟨b + ∑ p, t p, ?_⟩
    rw [key, ← hb1, ← Finset.sum_congr rfl fun p _ => ht p]
    simp
  · obtain ⟨⟨y, u⟩, rfl⟩ := fsur y'
    rw [hf] at h ⊢
    refine (hL _).2 ⟨y, (hΛd y).2 fun x hx => ?_, u, fun q => ?_, rfl⟩
    · have := h _ ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, rfl⟩)
      rw [key] at this
      simpa using this
    · obtain ⟨p, rfl⟩ := Fin.rev_surjective q
      refine (hd p _).2 ((FractionalIdeal.mem_inv_iff (hb p)).2 fun s hs => ?_)
      have := h _ ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p s, fun q => by
        by_cases hq : q = p
        · subst hq; simpa using hs
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem, rfl⟩)
      rw [key, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq]; simp)
        (fun h => absurd (Finset.mem_univ _) h)] at this
      obtain ⟨b, hb1⟩ := this
      obtain ⟨e, he, hee⟩ := hsg p
      rw [← he] at hb1
      have hee' : (e : E) * e = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hee
      obtain ⟨t, ht⟩ := hst (star s * u p.rev) ⟨e * b, by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul]
        change (e : E) * (b : E) = _
        rw [hb1]
        simp only [Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add, Pi.single_eq_same]
        rw [← mul_assoc, hee', one_mul]⟩
      refine (FractionalIdeal.mem_one_iff _).2 ⟨t, ht.trans ?_⟩
      rw [star_mul, star_star]

end General

theorem isSelfDualC_lat : ∀ (D : D7) (A B : HSp D) (c : ℕ) (ε : D.host.E) (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), (ε = 1 ∨ ε = -1) → IsSelfDualC A Λ → (∀ p, 𝔟 p ≠ 0) → (∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) → IsSelfDualC B (d.lat Λ 𝔟) := by
  intro D A B c ε d Λ 𝔟 hε hΛ hb hd
  exact selfDual_sum Formalism.BasicNotions.Examples₂.star_isIntegral B.gram A.gram (frameMat B A d.ι) d.a ε hε (gram_herm B) (gram_inj A)
    (gram_isom A B d.ι d.isom) d.perp d.gram d.rank Λ 𝔟 hΛ.1 hΛ.2 hb hd _ fun _ => Iff.rfl

end GlobalTheory.ChiGrid.SumDual
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.exists_finite_cosets_unitIdeles_completedOrder : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ → ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  first | exact @GlobalTheory.CMVal.Euler.exists_finset_cover_units | exact GlobalTheory.CMVal.Euler.exists_finset_cover_units | (intros; apply GlobalTheory.CMVal.Euler.exists_finset_cover_units <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

theorem _root_.GlobalTheory.T.exists_uniformiserIdele_multiplicative_on_ideals : ∀ (E : Type) [Field E] [NumberField E], ∃ t : Ideal (𝓞 E) → (Af E)ˣ, t ⊤ = 1 ∧ (∀ I J, I ≠ ⊥ → J ≠ ⊥ → t (I * J) = t I * t J) ∧ (∀ v : HeightOneSpectrum (𝓞 E), t v.asIdeal = unifAt v) ∧ (∀ I, I ≠ ⊥ → modF (t I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ∧ (∀ I, I ≠ ⊥ → ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((t I : Af E) w) ≤ 1 ∧ (w.asIdeal ∣ I → Valued.v ((t I : Af E) w) < 1) ∧ (¬ w.asIdeal ∣ I → (t I : Af E) w = 1)) ∧ (∀ I J, I ≠ ⊥ → J ≠ ⊥ → (∀ w, Valued.v ((t I : Af E) w) = Valued.v ((t J : Af E) w)) → I = J) ∧ ∀ z : (Af E)ˣ, (∀ w, Valued.v ((z : Af E) w) ≤ 1) → ∃ I, I ≠ ⊥ ∧ ∀ w, Valued.v ((t I : Af E) w) = Valued.v ((z : Af E) w) := by
  first | exact @GlobalTheory.CMVal.IdealIdele.main | exact GlobalTheory.CMVal.IdealIdele.main | (intros; apply GlobalTheory.CMVal.IdealIdele.main <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.mem_completedOrder_iff_placewise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E, z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), Valued.v (z w - a w) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  first | exact @GlobalTheory.CMVal.HatPlace.mem_hatO_iff | exact GlobalTheory.CMVal.HatPlace.mem_hatO_iff | (intros; apply GlobalTheory.CMVal.HatPlace.mem_hatO_iff <;> assumption)
end
