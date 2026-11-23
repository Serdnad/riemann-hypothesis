module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PolynomialRingOverGlobalSections
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle001
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle003
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle001
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

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def renameSumInl (k : Type u) [Field k] (M n : ℕ) :
    MvPolynomial (ULift.{u} (Fin M)) k →+* MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k :=
  (MvPolynomial.rename
      (fun a : ULift.{u} (Fin M) =>
        (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n)))).toRingHom

theorem renameSumInl_C (k : Type u) [Field k] (M n : ℕ) (c : k) :
    renameSumInl k M n (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [renameSumInl]

theorem renameSumInl_X (k : Type u) [Field k] (M n : ℕ) (a : Fin M) :
    renameSumInl k M n (MvPolynomial.X (ULift.up a)) =
      MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) := by
  simp [renameSumInl]

private theorem pderiv_inr_X_inl (k : Type u) [Field k] (M n : ℕ) (i : Fin n) (a : Fin M) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) = 0 := by
  classical
  simp [MvPolynomial.pderiv_X]

theorem pderiv_inr_renameSumInl (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (renameSumInl k M n p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i c
    simp [renameSumInl_C]
  · rename_i q r hq hr
    simp [hq, hr]
  · rename_i q a hq
    obtain ⟨a⟩ := a
    rw [map_mul, renameSumInl_X, MvPolynomial.pderiv_mul, hq, pderiv_inr_X_inl]
    simp

private theorem projLeft_appTop_affineSpaceIndexedByToSpec_appTop (k : Type u) [Field k] (M n : ℕ)
    (y : Γ(Spec (CommRingCat.of k), ⊤)) :
    (projLeft k M n).appTop ((affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y) =
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
  have h2 : ((projLeft k M n) ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y
      = (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
    rw [projLeft_comp_affineSpaceIndexedByToSpec]
  exact h2

private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (M n : ℕ) (c : k) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n)) (MvPolynomial.C c) := by
  rw [mvPolynomialEquivGlobalSections_C, mvPolynomialEquivGlobalSections_C, projLeft_appTop_affineSpaceIndexedByToSpec_appTop]

private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (M n : ℕ)
    (a : ULift.{u} (Fin M)) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n))) := by
  obtain ⟨a⟩ := a
  simp

theorem mvPolynomialEquivGlobalSections_symm_projLeft_appTop (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        ((projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) p)) =
      renameSumInl k M n p := by
  have key :
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          ((((projLeft k M n).appTop).hom).comp
            ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).toRingHom))
        = renameSumInl k M n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)))
          = renameSumInl k M n (MvPolynomial.C c)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_C, RingEquiv.symm_apply_apply, renameSumInl_C]
    · intro a
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)))
          = renameSumInl k M n (MvPolynomial.X a)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_X, RingEquiv.symm_apply_apply]
      simp [renameSumInl]
  exact RingHom.congr_fun key p

theorem mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) :
    ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp (mvPolynomialToSumCoordinateRing k M n) =
      MvPolynomial.eval₂Hom
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) := by
  apply MvPolynomial.ringHom_ext
  · intro t
    have h := mvPolynomialEquivGlobalSections_symm_projLeft_appTop k M n
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm t)
    simp only [RingEquiv.apply_symm_apply] at h
    simpa using h
  · intro i
    simp

theorem mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p) =
      MvPolynomial.eval₂
        ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom))
        (fun i : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))) p :=
  RingHom.congr_fun (mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing k M n) p

private theorem pderiv_inr_eval₂_X_inr (k : Type u) [Field k] (M n : ℕ)
    (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
      MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) (i : Fin n)
    (hf : ∀ t, MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) (f t) = 0)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.eval₂ f
          (fun j : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) p) =
      MvPolynomial.eval₂ f
        (fun j : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)))
        (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i t
    rw [MvPolynomial.eval₂_C, MvPolynomial.pderiv_C, MvPolynomial.eval₂_zero]
    exact hf t
  · rename_i q r hq hr
    simp [MvPolynomial.eval₂_add, hq, hr]
  · rename_i q j hq
    have hX : MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) =
        MvPolynomial.eval₂ f
          (fun l : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr l) : ULift.{u} (Fin M ⊕ Fin n)))
          (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
      by_cases h : i = j
      · subst h
        simp
      · simp [MvPolynomial.pderiv_X, h]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_mul,
      MvPolynomial.eval₂_add, hq, hX]

theorem pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p)) =
      (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv i p)) := by
  rw [mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing, mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing]
  refine pderiv_inr_eval₂_X_inr k M n
    ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom)) i ?_ p
  intro t
  rw [RingHom.comp_apply]
  exact pderiv_inr_renameSumInl k M n i _

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev pullbackFstSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (i : ℕ) : Scheme.{u} :=
  pullback (pullback.fst g g) (t.projectionToBase i)

abbrev pullbackSndSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (i : ℕ) : Scheme.{u} :=
  pullback (pullback.snd g g) (t.projectionToBase i)

theorem flat_fst_of_isPullback {A B C D : Scheme.{u}} {p : A ⟶ B} {q : A ⟶ C}
    {f : B ⟶ D} {h : C ⟶ D} (H : IsPullback p q f h) [AlgebraicGeometry.Flat h] :
    AlgebraicGeometry.Flat p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Flat) H.flip inferInstance

private theorem isPullback_iso_hom_comp {P P' A B C : Scheme.{u}} {pf : P' ⟶ A} {ps : P' ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (H : IsPullback pf ps f g) (e : P ≅ P') :
    IsPullback (e.hom ≫ pf) (e.hom ≫ ps) f g := by
  have E : IsPullback e.hom (e.hom ≫ ps) ps (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := E.paste_horiz H
  rwa [Category.id_comp] at h

theorem comap_map_center_eq_center_of_isPullback {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (n : ℕ) {X : Scheme.{u}} (π : X ⟶ Y)
    (γ : t.schemeAt n ⟶ X) [AlgebraicGeometry.Flat γ] [AlgebraicGeometry.QuasiCompact γ]
    (hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (hcenter : ((t.center n).comap (pullback.snd (pullback.snd g g) (t.projectionToBase n))).comap e.hom
      = (t.center n).comap (pullback.snd (pullback.fst g g) (t.projectionToBase n)))
    (hbase : e.hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase n)
      = pullback.fst (pullback.fst g g) (t.projectionToBase n))
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    ((t.center n).map γ).comap γ = t.center n := by
  have hpbSnd : IsPullback (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n))
      (pullback.fst (pullback.fst g g) (t.projectionToBase n)) (t.projectionToBase n) (pullback.snd g g) := by
    have h := isPullback_iso_hom_comp
      (IsPullback.of_hasPullback (pullback.snd g g) (t.projectionToBase n)).flip e
    rwa [hbase] at h
  have Big := hpbSnd.paste_vert (IsPullback.of_hasPullback g g).flip
  have hcond : pullback.fst (pullback.fst g g) (t.projectionToBase n) ≫ pullback.fst g g
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ t.projectionToBase n := pullback.condition
  rw [hcond, ← hsq.w] at Big
  have comm : (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n)) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ := by
    rw [Category.assoc]
    exact hgamma
  have key : IsPullback (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n))
      (pullback.snd (pullback.fst g g) (t.projectionToBase n)) γ γ :=
    IsPullback.of_bot Big comm hsq
  refine comap_map_eq_self_of_isPullback γ key (t.center n) ?_
  rw [Scheme.IdealSheafData.comap_comp]
  exact hcenter

theorem exists_isPullback_blowup_proj_map_center {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    ∃ q : t.schemeAt (n + 1) ⟶ Blowup.blowup ((t.center n).map γ),
      q ≫ Blowup.blowup.proj ((t.center n).map γ) = t.transitionMapSucc n ≫ γ ∧
        IsPullback q (t.transitionMapSucc n) (Blowup.blowup.proj ((t.center n).map γ)) γ := by
  have := hflat
  have h' : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc n) (((t.center n).map γ).comap γ) := by
    rw [hc]
    exact t.isBlowupAlongIdealSheaf_blowupMorphism n hn
  exact (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)).exists_isPullback_of_flat γ h'

def toBlowupOfMapCenter {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    t.schemeAt (n + 1) ⟶ Blowup.blowup ((t.center n).map γ) :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose

theorem toBlowupOfMapCenter_comp_proj {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    toBlowupOfMapCenter hn hflat hc ≫ Blowup.blowup.proj ((t.center n).map γ) = t.transitionMapSucc n ≫ γ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.1

theorem isPullback_toBlowupOfMapCenter {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    IsPullback (toBlowupOfMapCenter hn hflat hc) (t.transitionMapSucc n)
      (Blowup.blowup.proj ((t.center n).map γ)) γ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.2

theorem isPullback_toBlowupOfMapCenter_projectionToBase {W Y X : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    {n : ℕ} (hn : n < t.length) (π : X ⟶ Y) {γ : t.schemeAt n ⟶ X}
    (hflat : AlgebraicGeometry.Flat γ) (hc : ((t.center n).map γ).comap γ = t.center n)
    (hsq : IsPullback γ (t.projectionToBase n) π g) :
    IsPullback (toBlowupOfMapCenter hn hflat hc) (t.projectionToBase (n + 1))
      (Blowup.blowup.proj ((t.center n).map γ) ≫ π) g := by
  have h := (isPullback_toBlowupOfMapCenter hn hflat hc).paste_vert hsq
  rwa [← t.projectionToBase_succ n] at h

theorem toBlowupOfMapCenter_cocycle {W Y X : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) {n : ℕ} (hn : n < t.length) (π : X ⟶ Y)
    {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n)
    (_hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1))
    (hee : e'.hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n) ≫ e.hom)
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    e'.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ toBlowupOfMapCenter hn hflat hc
      = pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ toBlowupOfMapCenter hn hflat hc := by
  have := hflat
  have hfst : AlgebraicGeometry.Flat (pullback.fst g g) :=
    flat_fst_of_isPullback (IsPullback.of_hasPullback g g)
  have hdc : AlgebraicGeometry.Flat (toBlowupOfMapCenter hn hflat hc) :=
    flat_fst_of_isPullback (isPullback_toBlowupOfMapCenter hn hflat hc)
  have hsnd1 : pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.fst g g) (t.projectionToBase n) :=
    (t.pullbackTransitionMap_snd (pullback.fst g g) (Nat.le_succ n)).symm
  have hsnd2 : pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n
      = t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) :=
    (t.pullbackTransitionMap_snd (pullback.snd g g) (Nat.le_succ n)).symm
  have hsnd1' : pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n ≫ γ
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ := by
    rw [← Category.assoc, ← Category.assoc, hsnd1]
  have hsnd2' : pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n ≫ γ
      = t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ := by
    rw [← Category.assoc, ← Category.assoc, hsnd2]
  have hk : Blowup.IsLocallyGeneratedByNonZeroDivisor (((t.center n).map γ).comap
      (pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫
        toBlowupOfMapCenter hn hflat hc ≫ Blowup.blowup.proj ((t.center n).map γ))) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat
      (Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)).1
        (toBlowupOfMapCenter hn hflat hc)) _
  refine Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)) hk ?_ ?_
  · simp only [Category.assoc]
    rw [toBlowupOfMapCenter_comp_proj hn hflat hc, hsnd2', hsnd1', ← Category.assoc, hee,
      Category.assoc, hgamma]
  · rw [Category.assoc]

structure DescendedBlowupData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (n : ℕ)
    {X : Scheme.{u}} (π : X ⟶ Y) (γ : t.schemeAt n ⟶ X)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1)) where
  total : Scheme.{u}
  totalStruct : total ⟶ Y
  down : total ⟶ X
  totalCenter : X.IdealSheafData
  totalComparison : t.schemeAt (n + 1) ⟶ total
  center_comap : totalCenter.comap γ = t.center n
  isBlowup_down : Blowup.IsBlowupAlongIdealSheaf down totalCenter
  sq_comm : totalComparison ≫ down = t.transitionMapSucc n ≫ γ
  isPullback_sq : IsPullback totalComparison (t.transitionMapSucc n) down γ
  isPullback_base : IsPullback totalComparison (t.projectionToBase (n + 1)) totalStruct g
  hom_comparison :
    e'.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ totalComparison
      = pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ totalComparison
  structY_eq : totalStruct = down ≫ π

def descendedBlowupData {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) {n : ℕ} (hn : n < t.length)
    {X : Scheme.{u}} (π : X ⟶ Y) (γ : t.schemeAt n ⟶ X)
    (hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1))
    (hee : e'.hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n) ≫ e.hom)
    (hcenter : ((t.center n).comap (pullback.snd (pullback.snd g g) (t.projectionToBase n))).comap e.hom
      = (t.center n).comap (pullback.snd (pullback.fst g g) (t.projectionToBase n)))
    (hbase : e.hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase n)
      = pullback.fst (pullback.fst g g) (t.projectionToBase n))
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    DescendedBlowupData g t n π γ e' :=
  haveI hfl : AlgebraicGeometry.Flat γ := flat_fst_of_isPullback hsq
  haveI _hqc : AlgebraicGeometry.QuasiCompact γ := quasiCompact_of_isPullback hsq.flip
  have hc : ((t.center n).map γ).comap γ = t.center n :=
    comap_map_center_eq_center_of_isPullback g t n π γ hsq e hcenter hbase hgamma
  { total := Blowup.blowup ((t.center n).map γ)
    totalStruct := Blowup.blowup.proj ((t.center n).map γ) ≫ π
    down := Blowup.blowup.proj ((t.center n).map γ)
    totalCenter := (t.center n).map γ
    totalComparison := toBlowupOfMapCenter hn hfl hc
    center_comap := hc
    isBlowup_down := Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)
    sq_comm := toBlowupOfMapCenter_comp_proj hn hfl hc
    isPullback_sq := isPullback_toBlowupOfMapCenter hn hfl hc
    isPullback_base := isPullback_toBlowupOfMapCenter_projectionToBase g t hn π hfl hc hsq
    hom_comparison := toBlowupOfMapCenter_cocycle g t hn π hfl hc hsq e e' hee hgamma
    structY_eq := rfl }

end FunctorialResolution.EmbeddedResolution
end
end
