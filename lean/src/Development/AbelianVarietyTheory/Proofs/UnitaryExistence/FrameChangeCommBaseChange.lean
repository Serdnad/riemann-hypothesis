import Formalism.LocalToGlobal.ProjectiveLattices.FrameBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.ChgBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

alias spMap_comp_ring := Formalism.L2.Pj.FrameBaseChange.spMap_comp_ring

alias spMap_id := Formalism.L2.Pj.FrameBaseChange.spMap_id

alias dualMap_alg := Formalism.L2.Pj.FrameBaseChange.dualMap_alg

alias dualMap_eps := Formalism.L2.Pj.FrameBaseChange.dualMap_eps

alias isCombAt_pull := Formalism.L2.Pj.FrameBaseChange.isCombAt_pull

theorem isCombAt_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' := by
  obtain ⟨u, hu, hprod⟩ := h
  obtain ⟨u', hu', hprod'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← hprod, ← hprod', e]

alias ppx_le_cov := Formalism.L2.Pj.FrameBaseChange.ppx_le_cov

alias scal_pull := Formalism.L2.Pj.FrameBaseChange.scal_pull

alias can_exists := Formalism.L2.Pj.FrameBaseChange.can_exists

alias gx_ext := Formalism.L2.Pj.FrameBaseChange.gx_ext

theorem square {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {y y' : Sp S ⟶ Xo.X}
    {z z' : Sp T ⟶ Xo.X} (pmA : Gx z ⟶ Gx y) (pmB : Gx z' ⟶ Gx y') (pmC : Gx y' ⟶ Gx y) (pm : Gx z' ⟶ Gx z)
    (hsA : pmA ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk z) Xo.univ.t.G).left)
    (hfA : pmA ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk z) Xo.univ.t.G).left ≫ spMap φ)
    (hsB : pmB ≫ (snd (Over.mk y') Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hfB : pmB ≫ (fst (Over.mk y') Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap φ)
    (hsC : pmC ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk y') Xo.univ.t.G).left)
    (hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left ≫ spMap (RingHom.id S))
    (hs : pm ≫ (snd (Over.mk z) Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap (RingHom.id T))
    (sy : LB.Sec (PPx y)) (sy' : LB.Sec (PPx y')) (sz : LB.Sec (PPx z))
    (haA : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z).U i ≤ pmA ⁻¹ᵁ (PPx y).U i),
      (pmA.appLE _ _ h).hom (sy.f i) = sz.f i)
    (haC : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y').U i ≤ pmC ⁻¹ᵁ (PPx y).U i),
      (pmC.appLE _ _ h).hom (scal y a i * sy.f i) = sy'.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z').U i ≤ pm ⁻¹ᵁ (PPx z).U i)
    (hB : (PPx z').U i ≤ pmB ⁻¹ᵁ (PPx y').U i) :
    (pm.appLE _ _ h).hom (scal z (φ a) i * sz.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
  rw [spMap_id] at hfC hf
  replace hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left :=
    hfC.trans (Category.comp_id _)
  replace hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left :=
    hf.trans (Category.comp_id _)
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply gx_ext
    · rw [Category.assoc, hsA, hs, Category.assoc, hsC, hsB]
    · rw [Category.assoc, hfA, Category.assoc, hfC]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap φ) hf)).trans hfB.symm
  have hA := ppx_le_cov pmA hsA i
  have hC := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z' ⟶ Gx y), q = pmB ≫ pmC → ∀ hh : (PPx z').U i ≤ q ⁻¹ᵁ (PPx y).U i,
      (q.appLE _ _ hh).hom (scal y a i * sy.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC ≫ pmB.appLE _ _ hB :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC hB).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC]
  rw [← haA i hA, ← scal_pull φ pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y a i * sy.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frChg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y y' z z' g a hb hz
  obtain ⟨hx, hcomb, pmC, hsC, hfC, haC⟩ := hb
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  constructor
  · rintro ⟨hx2, hu2, pmB, hsB, hfB, haB⟩
    have hxz : z'.x = z.x := by rw [hx2, hx1, hx]
    refine ⟨hxz, fun τ i => isCombAt_pull φ.toRingHom hx1 (hu1 τ) (hu2 τ i) (hcomb τ i), ?_⟩
    obtain ⟨pm, hs, hf⟩ := can_exists (RingHom.id T) (x := z.x) (x' := z'.x)
      (by rw [spMap_id, Category.id_comp, hxz])
    refine ⟨pm, hs, hf, fun i h => ?_⟩
    have hB := ppx_le_cov pmB hsB i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).trans
      (haB i hB)
  · rintro ⟨hxz, hc2, pm, hs, hf, ha⟩
    have hx2 : z'.x = spMap φ.toRingHom ≫ y'.x := by rw [hxz, hx1, hx]
    refine ⟨hx2, fun τ i => isCombAt_unique (hc2 τ i)
      (isCombAt_pull φ.toRingHom hx1 (hu1 τ) rfl (hcomb τ i)), ?_⟩
    obtain ⟨pmB, hsB, hfB⟩ := can_exists φ.toRingHom hx2
    refine ⟨pmB, hsB, hfB, fun i hB => ?_⟩
    have h := ppx_le_cov pm hs i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).symm.trans
      (ha i h)

end GlobalTheory.Frames.ChgBC
