import Formalism.LocalToGlobal.ProjectiveLattices.FrameBaseChange
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramedBaseChange

theorem spec_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem spec_algHom_id (K : Type) [Field K] (T : Type) [CommRing T] [Algebra K T] :
    spMap (AlgHom.id K T).toRingHom = 𝟙 _ := by
  simp [spMap]

alias dual_id := Formalism.L2.Pj.FrameBaseChange.dual_id

alias appLE_eq_of_eq := Formalism.L2.Pj.FrameBaseChange.appLE_eq_of_eq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

alias chart_le := Formalism.L2.Pj.FrameBaseChange.ppx_le_cov

theorem pulledGroup_hom_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {W : Scheme.{0}} (a b : W ⟶ Gx x)
    (hs : a ≫ (snd (Over.mk x) Xo.univ.t.G).left = b ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : a ≫ (fst (Over.mk x) Xo.univ.t.G).left = b ≫ (fst (Over.mk x) Xo.univ.t.G).left) : a = b :=
  FrameBaseChange.gx_ext hs hf

alias refl := Formalism.L2.Pj.FrameBaseChange.refl

alias trans := Formalism.L2.Pj.FrameBaseChange.trans

alias cancel := Formalism.L2.Pj.FrameBaseChange.cancel

alias unique := Formalism.L2.Pj.FrameBaseChange.unique

theorem isPullSec {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z)
    (h : ptO Xo z.x ⟶ ptO Xo y.x) (hh : h.left = spMap φ.toRingHom) :
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s := by
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := hm
  have hpm : pm = (h ▷ Xo.univ.t.G).left := by
    apply pulledGroup_hom_ext
    · rw [hs, ← Over.comp_left, whiskerRight_snd]
    · rw [hf, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hh]
  subst hpm
  intro j
  exact (ha j (chart_le _ hs j)).symm

end GlobalTheory.FramedBaseChange

namespace GlobalTheory

theorem framedPoint_baseChange_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMap (AlgHom.id c.F S) y y) ∧ (∀ (S T U : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U] [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) (y : FrPt Xo c S) (z : FrPt Xo c T) (w : FrPt Xo c U), FrMap φ y z → (FrMap ψ z w ↔ FrMap (ψ.comp φ) y w)) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMap φ y z' → z = z') ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → ∀ h : ptO Xo z.x ⟶ ptO Xo y.x, h.left = spMap φ.toRingHom → IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s z.s :=
  fun _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ y => FramedBaseChange.refl y,
     fun _ _ _ _ _ _ _ _ _ φ ψ _ _ _ h₁ =>
       ⟨fun h₂ => FramedBaseChange.trans φ ψ h₁ h₂, fun h₂ => FramedBaseChange.cancel φ ψ h₁ h₂⟩,
     fun _ _ _ _ _ _ φ _ _ _ h₁ h₂ => FramedBaseChange.unique φ h₁ h₂,
     fun _ _ _ _ _ _ φ _ _ hm h hh => FramedBaseChange.isPullSec φ hm h hh⟩

end GlobalTheory
