module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ThickPush

theorem hom_ext_appLE {Z X : Scheme.{0}} {f g : Z ⟶ X} (hb : f.base = g.base)
    (h : ∀ U e, f.appLE U (g ⁻¹ᵁ U) e = g.app U) : f = g := by
  refine Scheme.Hom.ext hb fun U => ?_
  rw [← h U (le_of_eq congr((TopologicalSpace.Opens.map $hb.symm).obj U))]
  rfl

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h; rfl

theorem isUnit_germ_of_eq {T : Scheme.{0}} {p q : T} (hpq : p = q) (W : T.Opens) (hp : p ∈ W) (hq : q ∈ W)
    (t : Γ(T, W)) (h : IsUnit (T.presheaf.germ W p hp t)) : IsUnit (T.presheaf.germ W q hq t) := by
  subst hpq; exact h

section Desc
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def bse : (Y : TopCat) ⟶ (T : TopCat) :=
  TopCat.ofHom ⟨fun y => g₁ ((hj.homeomorph _).symm y),
    g₁.base.hom.continuous.comp (hj.homeomorph _).symm.continuous⟩

theorem bse_j₁ (x : Y₁) : bse hj g₁ (j₁ x) = g₁ x := by
  show g₁ ((hj.homeomorph _).symm (hj.homeomorph _ x)) = g₁ x
  rw [Homeomorph.symm_apply_apply]

include hw hi₂ hg in
theorem bse_j₂ (x : Y₂) : bse hj g₁ (j₂ x) = g₂ x := by
  obtain ⟨y, rfl⟩ := hi₂ x
  have h1 : j₂ (i₂ y) = j₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  have h2 : g₂ (i₂ y) = g₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
  rw [h1, h2, bse_j₁]

theorem pre₁ (W : T.Opens) : j₁ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₁ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₁ x) ∈ W ↔ g₁ x ∈ W
  rw [bse_j₁]

include hw hi₂ hg in
theorem pre₂ (W : T.Opens) : j₂ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₂ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₂ x) ∈ W ↔ g₂ x ∈ W
  rw [bse_j₂ hw hi₂ hj g₁ g₂ hg]

end Desc

section Lift
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def liftApp (W : T.Opens) : Γ(T, W) ⟶ Γ(Y, (TopologicalSpace.Opens.map (bse hj g₁)).obj W) :=
  (hV _).lift (g₁.appLE W _ (pre₁ hj g₁ W).le) (g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le) (by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      ((appLE_eq_of_eq hg _ _ _ _).trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm))

@[reassoc]
theorem liftApp_fst (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₁.app _ = g₁.appLE W _ (pre₁ hj g₁ W).le :=
  (hV _).lift_fst _ _ _

@[reassoc]
theorem liftApp_snd (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₂.app _ =
    g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le :=
  (hV _).lift_snd _ _ _

def psh : Y.toPresheafedSpace ⟶ T.toPresheafedSpace where
  base := bse hj g₁
  c :=
    { app := fun W => liftApp hw hi₂ hj hV g₁ g₂ hg W.unop
      naturality := fun W W' i => by
        apply (hV _).hom_ext
        · simp only [Category.assoc]
          erw [liftApp_fst, Scheme.Hom.naturality, liftApp_fst_assoc]
          simp
        · simp only [Category.assoc]
          erw [liftApp_snd, Scheme.Hom.naturality, liftApp_snd_assoc]
          simp }

end Lift

section Hom
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def desc : Y ⟶ T :=
  ⟨⟨psh hw hi₂ hj hV g₁ g₂ hg, fun x => ⟨fun a ha => by
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    obtain ⟨W, hW, t, rfl⟩ := T.presheaf.germ_exist (x := (psh hw hi₂ hj hV g₁ g₂ hg).base (j₁ x₁)) a
    have h1 := PresheafedSpace.stalkMap_germ_apply (psh hw hi₂ hj hV g₁ g₂ hg) W (j₁ x₁) hW t
    erw [h1] at ha
    have h2 : IsUnit ((Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t))) := by
      erw [← Scheme.Hom.germ_stalkMap_apply]; exact ha.map (j₁.stalkMap x₁).hom
    have h3 : (j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t) =
        (g₁.appLE W _ (pre₁ hj g₁ W).le).hom t := by
      rw [← CommRingCat.comp_apply, liftApp_fst]
    erw [h3] at h2
    have hx₁ : g₁ x₁ ∈ W := by rw [← bse_j₁ hj g₁ x₁]; exact hW
    have h4 : (Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((g₁.appLE W _ (pre₁ hj g₁ W).le).hom t) = g₁.stalkMap x₁ (T.presheaf.germ W (g₁ x₁) hx₁ t) := by
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply]
    rw [h4] at h2
    exact isUnit_germ_of_eq (bse_j₁ hj g₁ x₁).symm W hx₁ hW t (isUnit_of_map_unit (g₁.stalkMap x₁).hom _ h2)⟩⟩⟩

theorem desc_app (W : T.Opens) : (desc hw hi₂ hj hV g₁ g₂ hg).app W = liftApp hw hi₂ hj hV g₁ g₂ hg W := rfl

end Hom

section Fac
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

theorem fac₁ : j₁ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₁ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₁ hj g₁ x
  · have hh : j₁.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₁ ⁻¹ᵁ W) e = j₁.app _ ≫ Y₁.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_fst_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem fac₂ : j₂ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₂ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₂ hw hi₂ hj g₁ g₂ hg x
  · have hh : j₂.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₂ ⁻¹ᵁ W) e = j₂.app _ ≫ Y₂.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_snd_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem uniq (m : Y ⟶ T) (h₁ : j₁ ≫ m = g₁) (h₂ : j₂ ≫ m = g₂) : m = desc hw hi₂ hj hV g₁ g₂ hg := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    show m (j₁ x₁) = bse hj g₁ (j₁ x₁)
    rw [bse_j₁, ← h₁, Scheme.Hom.comp_apply]
  · rw [desc_app]
    apply (hV _).hom_ext
    · refine Eq.trans ?_ (liftApp_fst hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₁]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₁ _ _ _ _)
    · refine Eq.trans ?_ (liftApp_snd hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₂]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₂ _ _ _ _)

end Fac

theorem isPushout_of_isPullback_sections : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ →
    ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂),
    IsClosedImmersion j₁ → IsClosedImmersion j₂ → Surjective j₁ → Surjective j₂ →
    (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
      (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) →
    IsPushout i₁ i₂ j₁ j₂ := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ hs₂ Y j₁ j₂ hw hc₁ _ hs₁ _ hV
  have hj : IsHomeomorph j₁ :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨j₁.isClosedEmbedding.isEmbedding, hs₁.surj⟩
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => desc hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₁ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₂ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s m h₁ h₂ => uniq hw hs₂.surj hj hV s.inl s.inr s.condition m h₁ h₂))

end GlobalTheory.ThickPush
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

section One
variable {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]

theorem isHomeomorph : IsHomeomorph i :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩

def upOpen (U : Y₀.Opens) : Y₁.Opens := ⟨i '' (U : Set Y₀), (isHomeomorph i).isOpenMap _ U.2⟩

theorem preimage_upOpen (U : Y₀.Opens) : i ⁻¹ᵁ upOpen i U = U := by
  ext x
  change i x ∈ i '' (U : Set Y₀) ↔ x ∈ U
  exact (isHomeomorph i).injective.mem_set_image

theorem upOpen_preimage (V : Y₁.Opens) : upOpen i (i ⁻¹ᵁ V) = V := by
  ext y
  change y ∈ i '' (i ⁻¹' (V : Set Y₁)) ↔ y ∈ V
  rw [Set.image_preimage_eq _ i.surjective]
  rfl

theorem upOpen_mono : Monotone (upOpen i) := fun _ _ h ↦ Set.image_mono h

def res (U : Y₀.Opens) : Γ(Y₁, upOpen i U) ⟶ Γ(Y₀, U) :=
  i.appLE (upOpen i U) U (preimage_upOpen i U).ge

theorem res_naturality {U V : Y₀.Opens} (h : U ≤ V) :
    Y₁.presheaf.map (homOfLE (upOpen_mono i h)).op ≫ res i U =
      res i V ≫ Y₀.presheaf.map (homOfLE h).op := by
  simp only [res, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end One

section Two
variable {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁]
  [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂]

abbrev cone (U : Y₀.Opens) : PullbackCone (res i₁ U) (res i₂ U) :=
  CommRingCat.pullbackCone (res i₁ U) (res i₂ U)

def coneIsLimit (U : Y₀.Opens) : IsLimit (cone i₁ i₂ U) :=
  CommRingCat.pullbackConeIsLimit _ _

def fibMap {U V : Y₀.Opens} (h : U ≤ V) : (cone i₁ i₂ V).pt ⟶ (cone i₁ i₂ U).pt :=
  PullbackCone.IsLimit.lift (coneIsLimit i₁ i₂ U)
    ((cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op)
    ((cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op)
    (by rw [Category.assoc, Category.assoc, res_naturality i₁ h, res_naturality i₂ h,
      (cone i₁ i₂ V).condition_assoc])

@[reassoc (attr := simp)]
theorem fibMap_fst {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).fst =
    (cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem fibMap_snd {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).snd =
    (cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

def fib : Y₀.Opensᵒᵖ ⥤ CommRingCat.{0} where
  obj U := (cone i₁ i₂ U.unop).pt
  map f := fibMap i₁ i₂ f.unop.le
  map_id U := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ U.unop)
    (by simp [homOfLE_refl]) (by simp [homOfLE_refl])
  map_comp f g := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ _)
    (by simp [← Functor.map_comp]; rfl) (by simp [← Functor.map_comp]; rfl)

def fibπ : fib i₁ i₂ ⟶ Y₀.presheaf where
  app U := (cone i₁ i₂ U.unop).fst ≫ res i₁ U.unop
  naturality U V f := by
    change fibMap i₁ i₂ f.unop.le ≫ _ ≫ _ = _
    rw [fibMap_fst_assoc, res_naturality]
    rfl

def good : Set Y₀.Opens :=
  {U | IsAffineOpen U ∧ IsAffineOpen (upOpen i₁ U) ∧ IsAffineOpen (upOpen i₂ U)}

end Two

end GlobalTheory.FerrandPush
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem exists_ideal_factor_closedImmersion_iff (A : Type) [CommRing A] (X Y : Scheme.{0})
    (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X) [IsClosedImmersion j] :
    ∃ I : Ideal A, ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔
        I ≤ RingHom.ker ψ := by
  obtain ⟨I, e, hf⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd j a)).mp inferInstance
  refine ⟨I, fun R _ ψ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    let z : Spec (CommRingCat.of R) ⟶ pullback j a := pullback.lift y (Spec.map (CommRingCat.ofHom ψ)) hy
    have hz : z ≫ pullback.snd j a = Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (z ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ χ) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [Spec.map_comp, hχ, Category.assoc, ← hf, hz]
    have h2 := Spec.map_injective h1
    intro x hx
    have := congrArg (fun g => g.hom x) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    rw [RingHom.mem_ker, ← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun x hx => h hx))) ≫ e.inv ≫ pullback.fst j a, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, hf, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc]
    congr 2

theorem factor_closedImmersion_iff_of_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (X Y : Scheme.{0}) (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X), IsClosedImmersion j → ∀ J : Ideal A, (∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ) → ∀ (R : Type) [CommRing R] (ψ : A →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔ J ≤ RingHom.ker ψ := by
  intro A _ _ X Y a j hj J H
  obtain ⟨I, hI⟩ := exists_ideal_factor_closedImmersion_iff A X Y a j
  have key : ∀ (K : Ideal A), K ≠ ⊤ → (I ≤ K ↔ J ≤ K) := by
    intro K hK
    haveI : Nontrivial (A ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
    haveI : IsLocalRing (A ⧸ K) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have := (hI (A ⧸ K) (Ideal.Quotient.mk K)).symm.trans (H (A ⧸ K) (Ideal.Quotient.mk K))
    simpa [Ideal.mk_ker] using this
  have hIJ : I = J := by
    apply le_antisymm
    · by_cases hJ : J = ⊤
      · rw [hJ]; exact le_top
      · exact (key J hJ).mpr le_rfl
    · by_cases hI' : I = ⊤
      · rw [hI']; exact le_top
      · exact (key I hI').mp le_rfl
  intro R _ ψ
  rw [← hIJ]
  exact hI R ψ

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem closedCover_affine_nbhd_maps_into_affine :
    ∀ (Y Y₁ Y₂ X : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) [IsClosedImmersion j₁]
      [IsClosedImmersion j₂] (a₁ : Y₁ ⟶ X) (a₂ : Y₂ ⟶ X),
      (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) →
      (∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂) →
      ∀ y : Y, ∃ (W : Y.Opens) (U : X.affineOpens), IsAffineOpen W ∧ y ∈ W ∧
        j₁ ⁻¹ᵁ W ≤ a₁ ⁻¹ᵁ U.1 ∧ j₂ ⁻¹ᵁ W ≤ a₂ ⁻¹ᵁ U.1 := by
  intro Y Y₁ Y₂ X j₁ j₂ _ _ a₁ a₂ hcov hagree y
  have hinj₁ := j₁.isClosedEmbedding.injective
  have hinj₂ := j₂.isClosedEmbedding.injective

  obtain ⟨x, hx₁, hx₂⟩ : ∃ x : X, (∀ w, j₁ w = y → a₁ w = x) ∧ (∀ w, j₂ w = y → a₂ w = x) := by
    rcases hcov y with ⟨y₁, h₁⟩ | ⟨y₂, h₂⟩
    · refine ⟨a₁ y₁, fun w hw => ?_, fun w hw => ?_⟩
      · rw [hinj₁ (hw.trans h₁.symm)]
      · exact (hagree y₁ w (h₁.trans hw.symm)).symm
    · refine ⟨a₂ y₂, fun w hw => hagree w y₂ (hw.trans h₂.symm), fun w hw => ?_⟩
      rw [hinj₂ (hw.trans h₂.symm)]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  set C : Set Y := j₁.base '' ((a₁ ⁻¹ᵁ U : Set Y₁)ᶜ) ∪ j₂.base '' ((a₂ ⁻¹ᵁ U : Set Y₂)ᶜ) with hCdef
  have hC : IsClosed C :=
    (j₁.isClosedEmbedding.isClosedMap _ (a₁ ⁻¹ᵁ U).isOpen.isClosed_compl).union
      (j₂.isClosedEmbedding.isClosedMap _ (a₂ ⁻¹ᵁ U).isOpen.isClosed_compl)
  have hyC : y ∉ C := by
    rintro (⟨w, hw, hwy⟩ | ⟨w, hw, hwy⟩)
    · exact hw (by simpa [hx₁ w hwy] using hxU)
    · exact hw (by simpa [hx₂ w hwy] using hxU)
  obtain ⟨W, hW, hyW, hWC⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨Cᶜ, hC.isOpen_compl⟩) (show y ∈ Cᶜ from hyC)
  refine ⟨W, ⟨U, hU⟩, hW, hyW, ?_, ?_⟩
  · intro w hw
    by_contra hn
    exact hWC hw (Or.inl ⟨w, hn, rfl⟩)
  · intro w hw
    by_contra hn
    exact hWC hw (Or.inr ⟨w, hn, rfl⟩)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.GlueColim


set_option backward.isDefEq.respectTransparency false in
theorem isClosedImmersion_surjective_preimage : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ U, IsClosedImmersion (e U)) → (∀ U, Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∀ j : X ⟶ colimit F, (∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U) → IsClosedImmersion j ∧ Surjective j ∧ ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
  intro B₀ 𝒰 F _ _ X G hG hc e he hs hnat j hj
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : (G U.1).toScheme),
      F.map f (e U x) = e V (X.homOfLE (hG (show U.1 ≤ V.1 from f.le)) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat (show U.1 ≤ V.1 from f.le)]
    rfl
  have hinj : ∀ U, Function.Injective (e U) := fun U ↦ (e U).isClosedEmbedding.injective
  have key2 : ∀ {U V : 𝒰} (x : (G U.1).toScheme) (y : (G V.1).toScheme),
      colimit.ι F U (e U x) = colimit.ι F V (e V y) → x.1 = y.1 := by
    intro U V x y h
    obtain ⟨W, f, g, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := (e W).surjective z
    rw [hnat'] at h1 h2
    have h1' := congrArg Subtype.val (hinj _ h1)
    have h2' := congrArg Subtype.val (hinj _ h2)
    simp only [Scheme.homOfLE_apply] at h1' h2'
    exact h1'.symm.trans h2'
  have hj' : ∀ (U : 𝒰) (x : (G U.1).toScheme), j x.1 = colimit.ι F U (e U x) := fun U x ↦
    congr($(hj U) x)
  have hpre : ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
    intro U
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e U).surjective y
      obtain ⟨V, hV, hxV⟩ := hc x
      have := key2 (V := ⟨V, hV⟩) y ⟨x, hxV⟩ (hy.trans (hj' ⟨V, hV⟩ ⟨x, hxV⟩))
      have h2 : y.1 = x := this
      exact h2 ▸ y.2
    · intro hx
      exact ⟨_, (hj' U ⟨x, hx⟩).symm⟩
  refine ⟨?_, ⟨?_⟩, hpre⟩
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
      (Scheme.IsLocallyDirected.openCover F)]
    intro U
    have H : IsPullback (e U) (G U.1).ι (colimit.ι F U) j :=
      IsOpenImmersion.isPullback _ _ _ _ (hj U) (by rw [hpre]; simp)
    have : pullback.snd j (colimit.ι F U) = H.flip.isoPullback.inv ≫ e U := by simp
    change IsClosedImmersion (pullback.snd j (colimit.ι F U))
    rw [this]
    infer_instance
  · intro b
    obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F b
    obtain ⟨x, rfl⟩ := (e U).surjective x
    exact ⟨_, hj' U x⟩

end GlobalTheory.GlueColim
end
