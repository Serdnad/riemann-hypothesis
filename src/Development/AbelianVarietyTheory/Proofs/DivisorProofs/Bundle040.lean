module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem isIso_specMap_restrict_basicOpen_of_bijective {R S : CommRingCat.{0}} (f : R ⟶ S) (r : R)
    (h : Function.Bijective (Localization.awayMap f.hom r)) :
    IsIso (Spec.map f ∣_ (PrimeSpectrum.basicOpen r : (Spec R).Opens)) := by
  set φ := Spec.map f with hφ
  set g : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r with hg
  have hbo : (PrimeSpectrum.basicOpen r : (Spec R).Opens) = (Spec R).basicOpen g :=
    (basicOpen_eq_of_affine (R := R) r).symm
  rw [hbo]
  have hU := isAffineOpen_top (Spec R)
  have hpre : IsAffineOpen (φ ⁻¹ᵁ (⊤ : (Spec R).Opens)) := by
    simpa using isAffineOpen_top (Spec S)
  have nat : ∀ x : R, (φ.app ⊤).hom ((Scheme.ΓSpecIso R).inv x) =
      (Scheme.ΓSpecIso S).inv (f x) := fun x =>
    (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality f)).symm
  have hi := (IsLocalization.Away.map_injective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.1
  have hs := (IsLocalization.Away.map_surjective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.2
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen g),
    hU.app_basicOpen_eq_away_map φ hpre g]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen g
  have := hpre.isLocalization_basicOpen ((φ.app ⊤).hom g)
  constructor
  · refine (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha => ?_
    obtain ⟨x, rfl⟩ : ∃ x, (Scheme.ΓSpecIso R).inv x = a :=
      ⟨(Scheme.ΓSpecIso R).hom a, Iso.hom_inv_id_apply _ _⟩
    rw [nat] at ha
    have hx : f x = 0 := by
      have := congrArg (Scheme.ΓSpecIso S).hom ha
      rw [Iso.inv_hom_id_apply] at this
      exact this.trans (map_zero _)
    obtain ⟨n, hn⟩ := hi x hx
    exact ⟨n, by rw [hg, ← map_pow, ← map_mul, hn, map_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso S).inv y = b :=
      ⟨(Scheme.ΓSpecIso S).hom b, Iso.hom_inv_id_apply _ _⟩
    obtain ⟨c, m, e⟩ := hs y
    exact ⟨(Scheme.ΓSpecIso R).inv c, m, by
      rw [nat, hg, nat]
      exact (congrArg (Scheme.ΓSpecIso S).inv.hom e).trans
        ((map_mul _ _ _).trans (congrArg (· * _) (map_pow _ _ _)))⟩


set_option backward.isDefEq.respectTransparency false in
theorem relSpec_map_isIso_over_basicOpen : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  intro X F F' α α' hα hα' ι hαι g hg hg' V b hb W hW
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI := (relativeGluingData hα).cover.map_prop V
  haveI := (relativeGluingData hα').cover.map_prop V
  set φ := Spec.map (ι.app (Opposite.op V)) with hφ
  have hnat : (relativeGluingData hα).natTrans.app V =
      φ ≫ (relativeGluingData hα').natTrans.app V := by
    subst hαι
    simp [relativeGluingData, hφ, Spec.map_comp]
  have H : IsPullback φ ((relativeGluingData hα).cover.f V) ((relativeGluingData hα').cover.f V) g := by
    refine IsPullback.of_right ?_ (hg' V).symm ((relativeGluingData hα').isPullback_natTrans_ι_toBase V)
    rw [← hnat, hg]
    exact (relativeGluingData hα).isPullback_natTrans_ι_toBase V
  have hW' : W = (relativeGluingData hα').cover.f V ''ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) := by
    ext1; exact hW
  subst hW'
  have h1 := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H
    (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens)
  have hpre : φ ⁻¹ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) =
      PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) := by
    ext x; rfl
  refine ⟨?_, ?_⟩
  · set D' : (Spec (F'.obj (Opposite.op V))).Opens := PrimeSpectrum.basicOpen b with hD'
    have H₂ := (isPullback_morphismRestrict φ D').paste_vert H
    haveI : IsIso (φ ∣_ D') := isIso_specMap_restrict_basicOpen_of_bijective _ b hb
    haveI : IsIso (pullback.snd g (D'.ι ≫ (relativeGluingData hα').cover.f V)) := by
      rw [← H₂.flip.isoPullback_inv_snd]
      infer_instance
    have hr : (D'.ι ≫ (relativeGluingData hα').cover.f V).opensRange =
        (relativeGluingData hα').cover.f V ''ᵁ D' := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      rfl
    have := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange g (D'.ι ≫ (relativeGluingData hα').cover.f V))).mpr
      (show IsIso _ from inferInstance)
    rw [hr] at this
    exact this
  · rw [← h1, hpre]
    rfl

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing

namespace GlobalTheory

theorem specializes_lift_closedFibre_stalkBaseChange : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  intro X Y π z R _ _ i _ hi v y hv hsp hy
  let e : IsLocalRing.ResidueField (Y.presheaf.stalk z) ≃+* IsLocalRing.ResidueField R :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map i) ⟨(IsLocalRing.ResidueField.map i).injective, hi⟩
  let β : R →+* IsLocalRing.ResidueField (Y.presheaf.stalk z) := e.symm.toRingHom.comp (IsLocalRing.residue R)
  have hβ : β.comp i = IsLocalRing.residue _ := by
    ext x
    simp only [β, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← IsLocalRing.ResidueField.map_residue]
    exact e.symm_apply_apply (IsLocalRing.residue _ x)
  have hcomp : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) ≫ Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z = Y.fromSpecResidueField z := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hβ]
    rfl
  have hβcl : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) (IsLocalRing.closedPoint (Y.residueField z)) = IsLocalRing.closedPoint R := by
    have : IsLocalHom β := inferInstance
    exact IsLocalRing.comap_closedPoint β
  let g : π.fiber z ⟶ pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π :=
    pullback.lift (π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (π.fiberι z)
      (by rw [Category.assoc]; exact (congrArg (π.fiberToSpecResidueField z ≫ ·) hcomp).trans (π.fiber_fac z).symm)
  have hgq : g ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberι z := pullback.lift_snd _ _ _
  let h : pullback (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ⟶ π.fiber z :=
    pullback.lift (pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) (pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π))
      (by
        rw [Category.assoc, ← pullback.condition (f := (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z)) (g := π), ← Category.assoc,
          ← pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), Category.assoc]; exact congrArg _ hcomp)
  have hgf : g ≫ pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) := pullback.lift_fst _ _ _
  have hhf : h ≫ π.fiberToSpecResidueField z = pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := pullback.lift_snd _ _ _
  have hhι : h ≫ π.fiberι z = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π := pullback.lift_fst _ _ _
  have hhg : h ≫ g = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgf, ← Category.assoc, hhf]
      exact pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    · rw [Category.assoc, hgq, hhι]
  obtain ⟨u, -, hu2⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    (IsLocalRing.closedPoint (Y.residueField z)) v (hβcl.trans hv.symm)
  have hga : g (h u) = v := by
    rw [← Scheme.Hom.comp_apply, hhg, hu2]
  have hfa : π.fiberι z (h u) = pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v := by
    rw [← hga, ← Scheme.Hom.comp_apply g, hgq]
  let b := (π.fiberHomeo z).symm ⟨y, hy⟩
  have hb : π.fiberι z b = y := π.fiberι_fiberHomeo_symm z ⟨y, hy⟩
  have hab : h u ⤳ b := by
    rw [← (π.fiberι z).isEmbedding.toIsInducing.specializes_iff, hfa, hb]
    exact hsp
  refine ⟨g b, ?_, ?_⟩
  · rw [← hga]
    exact hab.map g.continuous
  · rw [← Scheme.Hom.comp_apply, hgq, hb]

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

open Filter Topology in
private lemma iteratedFDeriv_slice_eq_compContinuousLinearMap_inl {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (H : E × F → ℂ) {w : F}
    (hH : AnalyticAt ℂ H (0, w)) (k : ℕ) :
    iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 =
      (iteratedFDeriv ℂ k H (0, w)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl ℂ E F) := by
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  set s : Set (E × F) := (fun q ↦ q + (0, w)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_id.add continuous_const)
  have h0s : (0 : E × F) ∈ s := by simpa [hs] using hwU
  have hf : AnalyticOnNhd ℂ (fun q : E × F ↦ H (q + (0, w))) s := fun q hq ↦
    (hU _ hq).comp (f := fun q : E × F ↦ q + (0, w)) (analyticAt_id.add analyticAt_const)
  have hslice : (fun z : E ↦ H (z, w)) =
      (fun q : E × F ↦ H (q + (0, w))) ∘ ContinuousLinearMap.inl ℂ E F := by
    ext z; simp
  have hpre : IsOpen (ContinuousLinearMap.inl ℂ E F ⁻¹' s) :=
    hso.preimage (ContinuousLinearMap.continuous _)
  have h0s' : ContinuousLinearMap.inl ℂ E F 0 ∈ s := by rw [map_zero]; exact h0s
  have h0pre : (0 : E) ∈ ContinuousLinearMap.inl ℂ E F ⁻¹' s := h0s'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen k hpre h0pre,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right _ (hf.contDiffOn (n := k) hso.uniqueDiffOn)
      hso.uniqueDiffOn hpre.uniqueDiffOn h0s' le_rfl,
    iteratedFDerivWithin_of_isOpen k hso h0s', iteratedFDeriv_comp_add_right]
  simp

open Filter Topology in
private lemma fin_snoc_eq_cons_comp_finRotate {X : Type} {k : ℕ} (u : Fin k → X) (a : X) :
    (Fin.snoc u a : Fin (k + 1) → X) = Fin.cons a u ∘ finRotate (k + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp
  · simp


open Filter Topology in
theorem _root_.GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  intro E F _ _ _ _ _ _ H w₀ k v hH
  set u : Fin k → E × F := fun i ↦ (v i, 0) with hu
  have hev : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ H (0, w) :=
    ((continuous_const.prodMk continuous_id).tendsto w₀).eventually hH.eventually_analyticAt
  have heq : (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) =ᶠ[𝓝 w₀]
      fun w ↦ iteratedFDeriv ℂ k H (0, w) u :=
    hev.mono fun w hw ↦ by dsimp only; rw [iteratedFDeriv_slice_eq_compContinuousLinearMap_inl H hw k]; rfl
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  have hiter : AnalyticAt ℂ (iteratedFDeriv ℂ k H) (0, w₀) :=
    (AnalyticOnNhd.iteratedFDeriv_of_isOpen hU hUo k) _ hwU
  have hA : AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k H (0, w) u) w₀ :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).analyticAt _).comp
      (hiter.comp (f := fun w : F ↦ ((0 : E), w)) (analyticAt_const.prod analyticAt_id))
  refine ⟨hA.congr heq.symm, fun e ↦ ?_⟩
  have hD : HasFDerivAt (fun w ↦ iteratedFDeriv ℂ k H (0, w) u)
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).comp
        ((fderiv ℂ (iteratedFDeriv ℂ k H) (0, w₀)).comp (ContinuousLinearMap.inr ℂ E F))) w₀ :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).hasFDerivAt.comp w₀
      (hiter.differentiableAt.hasFDerivAt.comp w₀ (hasFDerivAt_prodMk_right (0 : E) w₀))
  have hG : AnalyticAt ℂ (fun y ↦ fderiv ℂ H y (0, e)) (0, w₀) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)).analyticAt _).comp hH.fderiv
  rw [heq.fderiv_eq, hD.fderiv, iteratedFDeriv_slice_eq_compContinuousLinearMap_inl _ hG k]
  have hcomp : (fun y ↦ fderiv ℂ H y (0, e)) =
      (ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)) ∘ fderiv ℂ H := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hH.fderiv.contDiffAt (n := k)) le_rfl]
  have hperm := (hH.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (Fin.cons ((0 : E), e) u)
    (finRotate (k + 1))
  rw [← fin_snoc_eq_cons_comp_finRotate, iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_succ_apply_left] at hperm
  simpa [u] using hperm.symm

end GlobalTheory
end

section

open Set Filter Topology MeasureTheory

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_volume_image_eq_zero :
    ∀ (n : ℕ) (h : (Fin n → ℂ) → (Fin n → ℂ)) (W : Set (Fin n → ℂ)), IsOpen W → AnalyticOnNhd ℂ h W → volume (h '' W) = 0 → ∀ y ∈ W, Module.finrank ℂ (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) < n := by
  intro n h W hW ha h0 y hy
  by_contra hlt
  have hn : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  have hle := Submodule.finrank_le
    (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
  have htop : LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  have hs : HasStrictFDerivAt h (fderiv ℂ h y) y := (ha y hy).hasStrictFDerivAt
  have hmap := hs.map_nhds_eq_of_surj htop
  have hmem : h '' W ∈ 𝓝 (h y) := by
    rw [← hmap]
    exact image_mem_map (hW.mem_nhds hy)
  exact (Measure.measure_pos_of_mem_nhds volume hmem).ne' h0

end GlobalTheory
end

section

open Set

namespace GlobalTheory

private lemma eq_of_fderiv_fibre_zero_convex {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {g : ℕ}
    (F : P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (hC : IsOpen C)
    (hCc : Convex ℝ C) (hF : AnalyticOnNhd ℂ F (Z ×ˢ C))
    (hd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0)
    {z : P} (hz : z ∈ Z) {y y' : Fin g → ℂ} (hy : y ∈ C) (hy' : y' ∈ C) :
    F (z, y) = F (z, y') := by
  have hda : ∀ x ∈ C, HasFDerivAt (fun w => F (z, w))
      ((fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ))) x := by
    intro x hx
    exact (hF (z, x) ⟨hz, hx⟩).differentiableAt.hasFDerivAt.comp x (hasFDerivAt_prodMk_right z x)
  have hzero : ∀ x ∈ C,
      (fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ)) = 0 := by
    intro x hx
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.pi_ext
    intro a t
    have e : ((0 : P), (Pi.single a t : Fin g → ℂ)) = t • ((0 : P), (Pi.single a 1 : Fin g → ℂ)) := by
      refine Prod.ext (by simp) ?_
      funext j
      by_cases h : j = a
      · subst h; simp
      · simp [h]
    show fderiv ℂ F (z, x) ((0 : P), Pi.single a t) = 0
    rw [e, map_smul, hd a (z, x) ⟨hz, hx⟩, smul_zero]
  exact hCc.is_const_of_fderivWithin_eq_zero
    (fun x hx => (hda x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [fderivWithin_of_isOpen hC hx, (hda x hx).fderiv, hzero x hx]) hy hy'

theorem exists_analytic_param_of_primitives_on_box : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (G G' : K → P × (Fin g → ℂ) → ℂ), (∀ k, IsOpen (W k)) → IsOpen Z → IsOpen C → Convex ℝ C → C.Nonempty → (∀ p ∈ Z ×ˢ C, ∃ k, p ∈ W k) → ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) → ((∀ k, AnalyticOnNhd ℂ (G' k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G' k p - G' l p = c k l p) → ∃ h : P → ℂ, AnalyticOnNhd ℂ h Z ∧ ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → G k p = G' k p + h p.1 := by
  intro P _ _ _ g K W c ω Z C G G' hW hZ hC hCc hCn hcov hG hG'
  obtain ⟨hGa, hGd, hGc⟩ := hG
  obtain ⟨hG'a, hG'd, hG'c⟩ := hG'
  classical
  have hov : ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G' k p = G l p - G' l p := by
    intro k l p hk hl hp
    have h1 := hGc k l p hk hl hp
    have h2 := hG'c k l p hk hl hp
    linear_combination h1 - h2
  let F : P × (Fin g → ℂ) → ℂ := fun p =>
    if h : ∃ k, p ∈ W k then G h.choose p - G' h.choose p else 0
  have hFeq : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → F p = G k p - G' k p := by
    intro k p hk hp
    have h : ∃ k, p ∈ W k := ⟨k, hk⟩
    simp only [F, dif_pos h]
    exact hov _ _ p h.choose_spec hk hp
  have hFloc : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → (fun q => G k q - G' k q) =ᶠ[nhds p] F := by
    intro k p hk hp
    filter_upwards [((hW k).inter (hZ.prod hC)).mem_nhds ⟨hk, hp⟩] with q hq
    exact (hFeq k q hq.1 hq.2).symm
  have hFa : AnalyticOnNhd ℂ F (Z ×ˢ C) := by
    intro p hp
    obtain ⟨k, hk⟩ := hcov p hp
    exact ((hGa k p ⟨hk, hp⟩).sub (hG'a k p ⟨hk, hp⟩)).congr (hFloc k p hk hp)
  have hFd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0 := by
    intro a p hp
    obtain ⟨k, hk⟩ := hcov p hp
    have hs : HasFDerivAt (fun q => G k q - G' k q)
        (fderiv ℂ (G k) p - fderiv ℂ (G' k) p) p :=
      (hGa k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt.sub
        (hG'a k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt
    rw [← (hFloc k p hk hp).fderiv_eq, hs.fderiv]
    simp [hGd k a p hk hp, hG'd k a p hk hp]
  obtain ⟨y₀, hy₀⟩ := hCn
  refine ⟨fun z => F (z, y₀), ?_, ?_⟩
  · intro z hz
    have hi : AnalyticAt ℂ (fun w : P => (w, y₀)) z := analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (g := F) (f := fun w : P => (w, y₀)) (hFa (z, y₀) ⟨hz, hy₀⟩) hi
  · intro k p hk hp
    have hc := eq_of_fderiv_fibre_zero_convex F Z C hC hCc hFa hFd hp.1 hp.2 hy₀
    have hp' : ((p.1, p.2) : P × (Fin g → ℂ)) = p := rfl
    rw [hp'] at hc
    show G k p = G' k p + F (p.1, y₀)
    rw [← hc, hFeq k p hk hp]
    ring

end GlobalTheory
end

section

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem iteratedFDeriv_apply_eq_foldr_fderiv :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  intro E _ _ g hg j
  induction j with
  | zero =>
    intro m x
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m x
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]
    have hfun : (List.ofFn (fun i : Fin n => m i.succ)).foldr (fun v g' => fun z => fderiv ℝ g' z v) g
        = fun z => iteratedFDeriv ℝ n g z (Fin.tail m) := by
      funext z
      exact (ih (Fin.tail m) z).symm
    simp only [hfun]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.differentiable_iteratedFDeriv (by first | exact_mod_cast ENat.coe_lt_top n | simp | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top n))) x
    rw [fderiv_continuousMultilinear_apply_const_apply hd]

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem schwartz_pairing_conj_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (w : SchwartzMap V ℂ), ∃ Λ : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      Λ u = @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (w x)) := by
  intro V _ _ _ μ hμ w
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (w x)) :=
    (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp w.hasTemperateGrowth
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (w x))), ?_⟩
  intro u
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  congr 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, mul_comm]

end GlobalTheory
end
