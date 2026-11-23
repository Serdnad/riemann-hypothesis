module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PinchUnits

open ReciprocityTheory.ChartRestriction.G.Out.TLinPf

theorem pushout_sec_exists {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s₁ : Γ(X₁, ⊤)) (s₂ : Γ(X₂, ⊤))
    (h : i₁.appTop.hom s₁ = i₂.appTop.hom s₂) :
    ∃ s : Γ(X, ⊤), j₁.appTop.hom s = s₁ ∧ j₂.appTop.hom s = s₂ := by
  have w : i₁ ≫ mOf s₁ = i₂ ≫ mOf s₂ := by rw [comp_mOf, comp_mOf, h]
  refine ⟨fnOf (H.desc (mOf s₁) (mOf s₂) w), ?_, ?_⟩
  · rw [← fnOf_comp, H.inl_desc, fnOf_mOf]
  · rw [← fnOf_comp, H.inr_desc, fnOf_mOf]

theorem pushout_sec_ext {X₀ X₁ X₂ X : Scheme.{0}} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (H : IsPushout i₁ i₂ j₁ j₂) (s s' : Γ(X, ⊤))
    (h₁ : j₁.appTop.hom s = j₁.appTop.hom s') (h₂ : j₂.appTop.hom s = j₂.appTop.hom s') : s = s' := by
  apply mOf_inj
  apply H.hom_ext
  · rw [comp_mOf, comp_mOf, h₁]
  · rw [comp_mOf, comp_mOf, h₂]

theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

theorem isPullback_resLE_self {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) (f ⁻¹ᵁ U).ι U.ι f := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict f U

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → (∀ (U : Y.left.Opens) (a₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ), (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) a₁ = gm i₂ x (j₂ ⁻¹ᵁ U) a₂) → ∃ d : Γ(Y.left, U)ˣ, pullU j₁ U d = a₁ ∧ pullU j₂ U d = a₂) ∧ (∀ (U : Y.left.Opens) (d d' : Γ(Y.left, U)ˣ), pullU j₁ U d = pullU j₁ U d' → pullU j₂ U d = pullU j₂ U d' → d = d') := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hfl h₁ h₂ h₀ hc hc₂
  have hle : ∀ U : Y.left.Opens, i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U) ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ U) := by
    intro U x hx
    have e : (i₁ ≫ j₁) x = (i₂ ≫ j₂) x := by rw [hc]
    show j₂ (i₂ x) ∈ U
    simp only [Scheme.Hom.comp_apply] at e
    rw [← e]; exact hx
  have key : ∀ U : Y.left.Opens,
      (∀ (s₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)) (s₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)),
        (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom s₁ =
          (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom s₂ →
        ∃ d : Γ(Y.left, U), (j₁.app U).hom d = s₁ ∧ (j₂.app U).hom d = s₂) ∧
      (∀ d d' : Γ(Y.left, U), (j₁.app U).hom d = (j₁.app U).hom d' →
        (j₂.app U).hom d = (j₂.app U).hom d' → d = d') := by
    intro U
    let V₁ := j₁ ⁻¹ᵁ U
    let V₂ := j₂ ⁻¹ᵁ U
    let V₀ := i₁ ⁻¹ᵁ V₁
    let k₁ := j₁.resLE U V₁ le_rfl
    let k₂ := j₂.resLE U V₂ le_rfl
    let l₁ := i₁.resLE V₁ V₀ le_rfl
    let l₂ := i₂.resLE V₂ V₀ (hle U)
    have pb1 : IsPullback k₁ (V₁.ι ≫ Y₁.hom) (U.ι ≫ Y.hom) (Spec.map f₁) :=
      (isPullback_resLE_self j₁ U).paste_vert h₁
    have pb2 : IsPullback k₂ (V₂.ι ≫ Y₂.hom) (U.ι ≫ Y.hom) (Spec.map f₂) :=
      (isPullback_resLE_self j₂ U).paste_vert h₂
    have pb0 : IsPullback l₁ (V₀.ι ≫ Y₀.hom) (V₁.ι ≫ Y₁.hom) (Spec.map g₁) :=
      (isPullback_resLE_self i₁ V₁).paste_vert h₀
    have e1 : l₁ ≫ k₁ = l₂ ≫ k₂ := by
      rw [← cancel_mono U.ι]
      simp only [k₁, k₂, l₁, l₂, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, hc]
    have e2 : l₂ ≫ (V₂.ι ≫ Y₂.hom) = (V₀.ι ≫ Y₀.hom) ≫ Spec.map g₂ := by
      simp only [l₂, Category.assoc, Scheme.Hom.resLE_comp_ι_assoc, hc₂]
    have hfl' : Flat (Over.mk (U.ι ≫ Y.hom)).hom := by
      haveI := hfl
      show Flat (U.ι ≫ Y.hom)
      infer_instance
    have H : IsPushout l₁ l₂ k₁ k₂ :=
      GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (Over.mk (U.ι ≫ Y.hom))
        (Over.mk (V₁.ι ≫ Y₁.hom)) (Over.mk (V₂.ι ≫ Y₂.hom)) (Over.mk (V₀.ι ≫ Y₀.hom)) k₁ k₂ l₁ l₂
        hfl' pb1 pb2 pb0 e1 e2
    have hj : ∀ d : Γ(Y.left, U), k₁.appTop.hom (U.topIso.inv.hom d) = V₁.topIso.inv.hom ((j₁.app U).hom d) ∧
        k₂.appTop.hom (U.topIso.inv.hom d) = V₂.topIso.inv.hom ((j₂.app U).hom d) := fun d =>
      ⟨(resLE_appTop_topIso_inv j₁ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE]),
       (resLE_appTop_topIso_inv j₂ le_rfl d).trans (by rw [Scheme.Hom.app_eq_appLE])⟩
    refine ⟨fun s₁ s₂ h => ?_, fun d d' e₁ e₂ => ?_⟩
    · obtain ⟨t, ht1, ht2⟩ := pushout_sec_exists H (V₁.topIso.inv.hom s₁) (V₂.topIso.inv.hom s₂)
        (by rw [resLE_appTop_topIso_inv, resLE_appTop_topIso_inv, h])
      refine ⟨U.topIso.hom.hom t, ?_, ?_⟩
      · have := congrArg V₁.topIso.hom.hom ((hj (U.topIso.hom.hom t)).1)
        rwa [Iso.hom_inv_id_apply, ht1, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
      · have := congrArg V₂.topIso.hom.hom ((hj (U.topIso.hom.hom t)).2)
        rwa [Iso.hom_inv_id_apply, ht2, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, eq_comm] at this
    · have := pushout_sec_ext H (U.topIso.inv.hom d) (U.topIso.inv.hom d')
        (by rw [(hj d).1, (hj d').1, e₁]) (by rw [(hj d).2, (hj d').2, e₂])
      have := congrArg U.topIso.hom.hom this
      rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  refine ⟨fun U a₁ a₂ hg => ?_, fun U d d' e₁ e₂ => Units.ext ((key U).2 d.val d'.val
    (congrArg Units.val e₁) (congrArg Units.val e₂))⟩
  have heq : ∀ (b₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (b₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ),
      (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) b₁ = gm i₂ x (j₂ ⁻¹ᵁ U) b₂) →
      (i₁.appLE (j₁ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) le_rfl).hom b₁.val =
        (i₂.appLE (j₂ ⁻¹ᵁ U) (i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ U)) (hle U)).hom b₂.val := by
    intro b₁ b₂ hb
    apply TopCat.Presheaf.section_ext Y₀.left.sheaf
    intro x hx
    have := congrArg Units.val (hb x hx)
    rw [gm_val i₁ x _ hx, gm_val i₂ x _ (hle U hx)] at this
    simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact this
  obtain ⟨d, hd1, hd2⟩ := (key U).1 a₁.val a₂.val (heq a₁ a₂ hg)
  obtain ⟨d', hd1', hd2'⟩ := (key U).1 (a₁⁻¹).val (a₂⁻¹).val (heq a₁⁻¹ a₂⁻¹ (fun x hx => by
    rw [map_inv, map_inv, hg x hx]))
  have hdd : d * d' = 1 := (key U).2 _ _ (by rw [map_mul, map_one, hd1, hd1', Units.mul_inv])
    (by rw [map_mul, map_one, hd2, hd2', Units.mul_inv])
  exact ⟨⟨d, d', hdd, by rw [mul_comm, hdd]⟩, Units.ext hd1, Units.ext hd2⟩

end GlobalTheory.PinchUnits
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RigLinUnique

theorem eq_pull_section {X S S' : Scheme.{0}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p = 𝟙 S) (j : S' ⟶ S)
    (hi : Function.Injective (pullback.fst p j).appTop.hom)
    (hs : Function.Surjective (pullback.snd p j).appTop.hom) (u : Γ(X, ⊤)) :
    u = p.appTop.hom (e.appTop.hom u) := by
  have cmp : ∀ {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Γ(C, ⊤)),
      a.appTop.hom (b.appTop.hom x) = (a ≫ b).appTop.hom x := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  obtain ⟨c, hc⟩ := hs ((pullback.fst p j).appTop.hom u)
  let e' : S' ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 S') (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have h2 : e' ≫ pullback.snd p j = 𝟙 S' := pullback.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom u) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h1, h2, ← cmp, Scheme.Hom.id_appTop] at this
    exact this
  apply hi
  rw [cmp, pullback.condition, ← cmp, ← hc', hc]

theorem exists_ratio {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (w₁ w₂ : LB.Iso L' (L.pull F)) (h₁ : PGen w₁) (h₂ : PGen w₂) :
    ∃ u : Γ(X', ⊤)ˣ, ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), F (g y) ∈ L.U j → g y ∈ L'.U k →
      gw w₂ g y j k = gm g y ⊤ u * gw w₁ g y j k := by
  have key : ∀ (Y : Scheme.{0}) (g : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι),
      gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w₂.s (fun _ => j, k) * (w₁.s (fun _ => j, k))⁻¹) =
        gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := fun Y g y j k =>
    (map_mul _ _ _).trans (congrArg (gw w₂ g y j k * ·) (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit (X := X') (J := L.ι × L'.ι) ⊤ (fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2)
    (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩)
    (fun p => w₂.s (fun _ => p.1, p.2) * (w₁.s (fun _ => p.1, p.2))⁻¹) (fun p q x hx => by
      have a := h₁ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      refine (key _ _ x p.1 p.2).trans (Eq.trans ?_ (key _ _ x q.1 q.2).symm)
      rw [a, b, ← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv])
  refine ⟨u, fun Y g y j k hj hk => ?_⟩
  have hm : g y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have : gm g y ⊤ u = gw w₂ g y j k * (gw w₁ g y j k)⁻¹ := (gm_res g y le_top hm u).symm.trans
    ((congrArg (gm g y ((L.pull F).U (fun _ => j) ⊓ L'.U k)) (hu (j, k))).trans (key Y g y j k))
  rw [this]
  exact (inv_mul_cancel_right _ _).symm

theorem gw_eq_of_rigidified : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  intro R' _ _ _ D' A' G' _ _ hS U' s f₁ f₂ hf he₁ he₂ w₁ w₂ g₁ g₂ m₁ m₂ z j k hk hj
  subst hf
  have hL := U'.LG.isLB
  obtain ⟨u, hu⟩ := exists_ratio hL hL w₁ w₂ ((isGen_iff w₁).1 g₁) ((isGen_iff w₂).1 g₂)
  have p₁ := (maps_iff w₁ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₁ U'.LG.L)
    (fun _ => rfl)).1 m₁
  have p₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig s _ (rigPull_le f₁ s he₂ U'.LG.L)
    (fun _ => rfl)).1 m₂
  have he1 : pullU (eSec G') ⊤ u = 1 := by
    apply unit_ext
    intro x _
    obtain ⟨a, ha⟩ := exists_chart hL (f₁ (eSec G' x))
    obtain ⟨b, hb⟩ := exists_chart hL (eSec G' x)
    have q₁ := p₁ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q₂ := p₂ _ (𝟙 _) x (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    have q := mul_right_cancel (q₂.symm.trans q₁)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hu _ (𝟙 _ ≫ eSec G') x a b ha hb] at q
    rw [map_one]
    exact (gm_pull (𝟙 _) (eSec G') x ⊤ trivial u).trans (mul_eq_right.1 q)
  have := U'.smooth
  have : Flat G'.hom := inferInstance
  have : IsDominant (jK R') := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (algebraMap R' (FractionRing R')))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R' (FractionRing R'))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R')
  have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R')) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G'.hom (jK R')).flip
  have hb := GlobalFunctionsDvrPowers.bijective_of_iso U'.gen (GlobalTheory.SemiRigid.globalFns _ A'.A A'.isAb)
  have hv := eq_pull_section G'.hom (eSec G') (Over.w η[G']) (jK R')
    ((pullback.fst G'.hom (jK R')).app_injective ⊤) hb.2 u.val
  have he2 : (eSec G').appTop.hom u.val = 1 := congrArg Units.val he1
  have hu1 : u = 1 := Units.ext (hv.trans ((congrArg G'.hom.appTop.hom he2).trans (map_one _)))
  rw [hu _ (𝟙 _) z j k hj hk, hu1, map_one, _root_.one_mul]

end GlobalTheory.Mum.RigLinUnique
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.RigScale

private theorem mem_pull_lemma {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : F (f y) ∈ L.U i) : f y ∈ (L.pull F).U (fun _ => i) := by
  simp only [LB.pull, LB.LinComb, LB.wchart]
  simpa using hi

private theorem mem_U_of_mem_pull_U {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : f y ∈ (L.pull F).U (fun _ => i)) : F (f y) ∈ L.U i := by
  simp only [LB.pull, LB.LinComb, LB.wchart] at hi
  simpa using hi


private theorem pgen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : LB.Gen.IsGen w) : PGen w := by
  intro Y f y j j' k k' h1 h2 h3 h4
  have m1 := mem_pull_lemma f y j h1
  have m2 := mem_pull_lemma f y j' h2
  have hy : f y ∈ ((L.pull F).div L').U (fun _ => j, k) ⊓ ((L.pull F).div L').U (fun _ => j', k') :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j, k) (fun _ => j', k'))
  rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy] at e
  unfold gw
  refine e.trans ?_
  congr 1
  refine (map_mul (gm f y _) _ _).trans ?_
  congr 1
  · refine (gm_res f y _ hy _).trans ?_
    simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    refine (gm_res f y _ (show f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') from ⟨m1, m2⟩) _).trans ?_
    exact gm_pull f F y (L.U j ⊓ L.U j') ⟨h1, h2⟩ _
  · refine (map_inv (gm f y _) _).trans ?_
    congr 1
    exact gm_res f y _ hy _


private theorem isGen_of_pgen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : PGen w) : LB.Gen.IsGen w := by
  rintro ⟨a, k⟩ ⟨a', k'⟩
  apply unit_ext
  intro x hx
  have m1 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) := hx.1.1
  have m2 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a' PUnit.unit) := hx.2.1
  have n1 := mem_U_of_mem_pull_U (𝟙 X') x (a PUnit.unit) m1
  have n2 := mem_U_of_mem_pull_U (𝟙 X') x (a' PUnit.unit) m2
  have h := hw X' (𝟙 X') x (a PUnit.unit) (a' PUnit.unit) k k' n1 n2 hx.1.2 hx.2.2
  unfold gw at h
  rw [map_mul, gm_res, gm_res]
  · refine h.trans ?_
    symm
    congr 1
    refine (map_mul (gm (𝟙 X') x _) _ _).trans ?_
    congr 1
    · refine (gm_res (𝟙 X') x _ hx _).trans ?_
      simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
      refine (gm_res (𝟙 X') x _ (show (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) ⊓ (L.pull F).U (fun _ => a' PUnit.unit) from ⟨m1, m2⟩) _).trans ?_
      exact gm_pull (𝟙 X') F x (L.U (a PUnit.unit) ⊓ L.U (a' PUnit.unit)) ⟨n1, n2⟩ _
    · refine (map_inv (gm (𝟙 X') x _) _).trans ?_
      congr 1
      exact gm_res (𝟙 X') x _ hx _
  all_goals first | exact hx | skip

theorem exists_rig_rescale : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₂ : DegPre R) (D₃ : DegPre R') (Φ : D₃.P.A.left ⟶ D₂.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → ∀ w₀ : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w₀ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) := by
  intro R R' _ _ _ _ ρ D₂ D₃ Φ hΦ w₀ hw₀
  have hσ : eSec D₃.P.A ≫ D₃.P.A.hom = 𝟙 _ := Over.w (η[D₃.P.A])
  obtain ⟨w, hw, hm⟩ := GlobalTheory.UnifPreCompare.exists_rigidified (F := Φ) D₂.P.isLB D₃.P.isLB D₃.P.A.hom
    (eSec D₃.P.A) hσ w₀ (isGen_of_pgen w₀ hw₀) D₃.rig D₃.rig_gen D₂.rig D₂.rig_gen (spMap ρ)
    (GlobalTheory.PolBaseChange.eSec_comm hΦ)
  exact ⟨w, pgen_of_isGen w hw, hm⟩

end GlobalTheory.Mum.RigScale
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.commutatorPairing_determined_at_genericPoint : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (c : Oˣ) (k₀ : Type) [Field k₀] (j : O →+* k₀), Function.Injective j → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap j)) ≫ u) (toUnit (Over.mk (spMap j)) ≫ v) (unitOn (Units.map j.toMonoidHom c)) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom c)) := by
  first | exact @GlobalTheory.WeilGeneric.weilIs_of_generic | exact GlobalTheory.WeilGeneric.weilIs_of_generic | (intros; apply GlobalTheory.WeilGeneric.weilIs_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPair

theorem weilIs_of_spread : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  intro Ω T _ _ _ _ jT hj A P φ hp hw k x x' y y' c hk hx hx' hy hy' hW
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsLocallyNoetherian (Sp T) := inferInstance
  haveI : IsLocallyNoetherian (Sp Ω) := inferInstance
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil (Sp T) P k (baseOver _)).1 y y' hy hy'
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have H1 := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h hc₀
  have H2 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp T) (Sp Ω) P.A A.A (spMap jT) φ P.L A.L P.isLB A.isLB hp hw
    (baseOver (Sp Ω)) k x x' (h ≫ y) (h ≫ y') _ hx.symm hx'.symm).2 H1
  have inj : ∀ a b : baseOver (Sp Ω) ⟶ A.A, a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext e
    rw [Over.w, Over.w]
  have tors : ∀ (a : baseOver (Sp Ω) ⟶ A.A) (b : baseOver (Sp T) ⟶ P.A), a.left ≫ φ = spMap jT ≫ b.left →
      b ^ k = 1 → a ^ k = 1 := by
    intro a b e hb
    apply inj
    have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) (a ^ k)) = (h ≫ b) ^ k := by
      rw [map_pow]
      congr 1
      exact Over.OverMorphism.ext e
    have e2 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) 1) = (h ≫ b) ^ k := by
      rw [map_one, ← MonObj.comp_pow, hb, MonObj.comp_one]
    exact (congrArg (fun z => z.left) e1).trans (congrArg (fun z => z.left) e2).symm
  have hxk := tors x y hx hy
  have hxk' := tors x' y' hx' hy'
  have U := (hL.weil (Sp Ω) A k (baseOver _)).1 x x' hxk hxk'
  have e3 := U.unique H2 hW
  have nat : ∀ a : T, (spMap jT).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (jT a) := by
    intro a
    have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jT))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  have ginj : Function.Injective (spMap jT).appTop.hom := by
    intro a b e
    have ea : a = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom a) := by
      simp
    have eb : b = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom b) := by
      simp
    rw [ea, eb, nat, nat] at e
    have e' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom e
    have key : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom z) = z :=
      fun z => by simp
    rw [key, key] at e'
    rw [ea, eb, hj e']
  have e4 : c₀ = unitOn c := by
    apply Units.ext
    apply ginj
    exact (congrArg Units.val e3).trans (nat (c : T)).symm
  rw [← e4]
  exact hc₀

end GlobalTheory.MumPair
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkExt_refl {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

section Lab

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {ρ : R →+* R₁}
  {D : DegPre R} {D₁ : DegPre R₁} [Algebra (FractionRing R) (Kb R₁)]

variable {A : PolAV (Sp (FractionRing R))} {A₁ : PolAV (Sp (FractionRing R₁))}

end Lab

end GlobalTheory.LabExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.Mum.exists_sec_nonzero_on_fibre | exact GlobalTheory.Mum.exists_sec_nonzero_on_fibre | (intros; apply GlobalTheory.Mum.exists_sec_nonzero_on_fibre <;> assumption)
end
