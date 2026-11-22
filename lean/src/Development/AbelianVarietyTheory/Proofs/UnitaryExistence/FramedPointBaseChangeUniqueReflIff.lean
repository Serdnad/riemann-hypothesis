import Formalism.LocalToGlobal.ProjectiveLattices.FrameBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frMapUniq_scal_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x (1 : S) i = 1 := by
  unfold scal ReciprocityTheory.ChartRestriction.G.Out.liftFun
  simp only [map_one]

alias frMapUniq_chart_le := Formalism.L2.Pj.FrameBaseChange.ppx_le_cov

alias frMapUniq_refl := Formalism.L2.Pj.FrameBaseChange.refl

theorem frMap_unique_refl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  refine ⟨fun _ _ => FrameBaseChange.unique φ, frMapUniq_refl y, fun z => ?_⟩
  have k : ∀ i : (PPx y.x).ι, scal y.x (1 : S) i * y.s.f i = y.s.f i := fun i => by
    rw [frMapUniq_scal_one, _root_.one_mul]
  constructor
  · rintro ⟨hx, hu, pm, hs, hf, ha⟩
    exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).trans (ha i h)⟩
  · rintro ⟨hx, hu, pm, hs, hf, ha⟩
    exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).symm.trans (ha i h)⟩

end GlobalTheory.Frames
