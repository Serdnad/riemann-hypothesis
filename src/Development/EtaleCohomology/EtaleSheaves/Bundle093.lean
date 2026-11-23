module

public import Development.EtaleCohomology.EtaleSheaves.Bundle089
public import Development.EtaleCohomology.EtaleSheaves.Bundle090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.StalkOfAlgebra

theorem stalk_of_smoothAt {R A : CommRingCat.{0}} (φ : R ⟶ A) (p : PrimeSpectrum A)
    (h : letI := φ.hom.toAlgebra; Algebra.IsSmoothAt R p.asIdeal) :
    ((Spec.map φ).stalkMap p).hom.FormallySmooth := by
  letI := φ.hom.toAlgebra
  let P := (p.comap φ.hom).asIdeal
  haveI : p.asIdeal.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P p.asIdeal
  rw [RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ p)]
  have : Algebra.FormallySmooth (Localization.AtPrime P) (Localization.AtPrime p.asIdeal) :=
    (Algebra.FormallySmooth.iff_restrictScalars (R := R) (A := Localization.AtPrime P)).mp h
  exact this

theorem core (hA : LateralTheory.E.SpreadingOutSmoothness.LeafAlgDescend) (k : Type) [Field k] (Ω : Type) [Field Ω]
    [Algebra k Ω] (R : Subalgebra k Ω) {C : Scheme.{0}} {A : CommRingCat.{0}} (φ : CommRingCat.of R ⟶ A)
    (c : C ⟶ Sp Ω) (v : C ⟶ Spec A) [LocallyOfFinitePresentation (Spec.map φ)] (hs : Smooth c)
    (hv : IsPullback v c (Spec.map φ) (toR R)) (y : C) : v y ∈ (Spec.map φ).smoothLocus := by
  letI : Algebra R A := φ.hom.toAlgebra
  have hfp0 : φ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp inferInstance
  have hfp : Algebra.FinitePresentation R A := hfp0
  have hpo := (CommRingCat.isPushout_tensorProduct R Ω A)
  have hφ : CommRingCat.ofHom (algebraMap R A) = φ := rfl
  rw [hφ] at hpo
  have hstd := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  let e := hv.isoIsPullback _ _ hstd
  have h1 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeRight.toRingHom) = v :=
    hv.isoIsPullback_hom_fst _ _ hstd
  have h2 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = c :=
    hv.isoIsPullback_hom_snd _ _ hstd
  haveI := hs
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = e.inv ≫ c := by
      rw [← h2, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  have hrs := (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)).mp hsm
  have hinc : (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[R] A) = algebraMap Ω (Ω ⊗[R] A) := by
    ext x; rfl
  have hsA : Algebra.Smooth Ω (Ω ⊗[R] A) := by
    rw [← RingHom.smooth_algebraMap, ← hinc]; exact hrs
  have key := hA k Ω R A hfp hsA (e.hom y)
  rw [← h1, Scheme.Hom.comp_apply]
  exact stalk_of_smoothAt φ _ key

theorem LeafStalkOfAlg_of : LateralTheory.E.SpreadingOutSmoothness.LeafStalkOfAlg := by
  intro hA k _ Ω _ _ R _ C D c q v hD _ hs hv y
  let e := D.isoSpec
  let φ := Spec.preimage (e.inv ≫ q)
  have hq : Spec.map φ = e.inv ≫ q := Spec.map_preimage _
  haveI : LocallyOfFinitePresentation (Spec.map φ) := by rw [hq]; infer_instance
  have hv' : IsPullback (v ≫ e.hom) c (Spec.map φ) (toR R) := by
    rw [hq]
    exact hv.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have key := core hA k Ω R φ c (v ≫ e.hom) hs.smooth hv' y
  have h2 := Scheme.Hom.preimage_smoothLocus_eq e.hom (Spec.map φ)
  have h3 : e.hom ≫ Spec.map φ = q := by rw [hq, Iso.hom_inv_id_assoc]
  have h4 : v y ∈ (e.hom ≫ Spec.map φ).smoothLocus := by
    rw [← h2]; simpa [Scheme.Hom.comp_apply] using key
  rw [Scheme.Hom.mem_smoothLocus] at h4 ⊢
  rwa [h3] at h4

end LateralTheory.E.StalkOfAlgebra

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.FMrangePfQc

theorem finset_idem {W : Type} [CommRing W] (hW : ProdACF W) (t : Finset W) :
    ∃ e : W, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum W, p ∈ (PrimeSpectrum.zeroLocus (t : Set W))ᶜ ↔ e ∉ p.asIdeal := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp⟩
  | insert a t _ ih =>
    obtain ⟨e, he, hpe⟩ := ih
    obtain ⟨f, u, hf, hu, rfl⟩ := hW.2 a
    refine ⟨f + e - f * e, ?_, fun p => ?_⟩
    · unfold IsIdempotentElem at *
      linear_combination (1 - e + (e * e - e)) * hf + (1 - f) * he
    · have hfe : f * (f + e - f * e) = f := by
        have := hf.eq; linear_combination (1 - e) * this
      have hef : e * (f + e - f * e) = e := by
        have := he.eq; linear_combination (1 - f) * this
      have key : f + e - f * e ∈ p.asIdeal ↔ f ∈ p.asIdeal ∧ e ∈ p.asIdeal := by
        constructor
        · intro h
          exact ⟨hfe ▸ p.asIdeal.mul_mem_left f h, hef ▸ p.asIdeal.mul_mem_left e h⟩
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right e h1)
      have hfu : f * u ∈ p.asIdeal ↔ f ∈ p.asIdeal := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          have := p.asIdeal.mul_mem_right v h
          rwa [mul_assoc, hv, mul_one] at this
        · exact fun h => p.asIdeal.mul_mem_right u h
      have h1 := hpe p
      simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_insert, Set.insert_subset_iff] at h1 ⊢
      rw [key]
      simp only [SetLike.mem_coe, hfu, not_iff_not.mp h1]

theorem QcIdem_pf : QcIdem := by
  intro W _ hW U hU
  obtain ⟨t, ht⟩ := (@PrimeSpectrum.isCompact_isOpen_iff W _ (U : Set (Spec (CommRingCat.of W)))).1 ⟨hU, U.isOpen⟩
  obtain ⟨e, he, hpe⟩ := finset_idem hW t
  refine ⟨e, he, fun p => ?_⟩
  rw [← hpe p, ht]
  rfl

theorem FMrange_of (hI : IdemLift) : FMrange :=
  FMrange_of_leaves hI QcIdem_pf

end LateralTheory.E.FMrangePfQc
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianNeighbourhood

def IsPtNb {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) : Prop :=
  s default = x ∧ (∀ j, IsIso (e j)) ∧ (∀ j, l j ≫ e j ≫ (a j).left = s) ∧
  (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
  (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧
  (∀ (j k : J) (f : j ⟶ k), l k ≫ Spec.map (CommRingCat.ofHom (D.map f).hom) = l j) ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (l' : Spec (CommRingCat.of Ω) ⟶ U'.left), l' ≫ b.left = s →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left ∧ l j ≫ e j ≫ g = l') ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (j : J) (g g' : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left →
      g' ≫ b.left = (a j).left → l j ≫ e j ≫ g = l j ≫ e j ≫ g' →
      ∃ (k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g =
        Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g')

def LeafSHNbSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left),
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t

def LeafSHLoc : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt

def LeafSHHens : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt →
  SH c.pt

theorem LeafSHNb_of (hS : LeafSHNbSys) (hL : LeafSHLoc) (hH : LeafSHHens) : LeafSHNb := by
  intro _ q _ k _ hq B U s0 x
  obtain ⟨Ω, _, _, s, J, _, _, D, c, hc, V, a, l, e, t, hP⟩ := hS U x
  obtain ⟨hs, he, hl, hcomp, ht, -, hcof, -⟩ := id hP
  refine ⟨J, inferInstance, inferInstance, D, c, hc, V, a, fun j => (l j ≫ e j) default, e, t, he, ?_, ?_, hcomp, ht,
    hH U x Ω s D c hc V a l e t hP (hL U x Ω s D c hc V a l e t hP), ?_⟩
  · intro j
    rw [← hs, ← hl j]
    rfl
  · intro j
    have := hq.map (Spec.preimage (e j ≫ (a j).left ≫ s0)).hom
    simpa using this
  · intro U' b y' hy'
    obtain ⟨l', hl', -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed b.left s y' (hy'.trans hs.symm)
    obtain ⟨j, g, hg, -⟩ := hcof U' b l' hl'
    exact ⟨j, g, hg⟩

end LateralTheory.E.StrictHenselianNeighbourhood
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology GlobalTheory.GlueModels LateralTheory.E.LeafGlueTwoPfFP

namespace LateralTheory.E.LeafGlueTwoPfQS

theorem qs_range {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] [QuasiSeparatedSpace A] :
    IsQuasiSeparated (Set.range e) := by
  simpa [Set.image_univ] using (isQuasiSeparated_univ (α := A)).image_of_isEmbedding e.isOpenEmbedding.isEmbedding

theorem compact_pre {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] {s : Set D} (hs : IsCompact s)
    (h : s ⊆ Set.range e) : IsCompact (e ⁻¹' s) :=
  (e.isOpenEmbedding.isInducing.isCompact_preimage_iff h).2 hs

theorem compact_inter_range {W A D : Scheme.{0}} (φ : W ⟶ A) (e : A ⟶ D) [IsOpenImmersion e] [QuasiCompact φ]
    {s : Set D} (hs : IsCompact s) (ho : IsOpen s) (h : s ⊆ Set.range e) :
    IsCompact (s ∩ Set.range (φ ≫ e)) := by
  rw [← Set.image_preimage_eq_inter_range]
  refine IsCompact.image ?_ (φ ≫ e).continuous
  have hp : ((φ ≫ e) ⁻¹' s) = φ ⁻¹' (e ⁻¹' s) := by ext x; simp
  rw [hp]
  exact QuasiCompact.isCompact_preimage (f := φ) _ (e.continuous.isOpen_preimage _ ho) (compact_pre e hs h)

set_option backward.isDefEq.respectTransparency false in
theorem leafPushoutQS : LeafPushoutQS := by
  intro DW DU DV φU φV _ _ hW hWs hUs hVs
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  have : QuasiCompact φU := quasiCompact_of_compactSpace φU
  have : QuasiCompact φV := quasiCompact_of_compactSpace φV
  let good : Set (pushout φU φV : Scheme.{0}) → Prop := fun s => IsOpen s ∧ IsCompact s ∧
    (s ⊆ Set.range (pushout.inl φU φV) ∨ s ⊆ Set.range (pushout.inr φU φV))
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := fun s : {s // good s} => s.1) ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨s, rfl⟩; exact s.2.1
    · intro x u hx hu
      rcases pushout_cover φU φV x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DU} {x : DU}, x ∈ U → ∃ U' ∈ DU.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DU.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inl φU φV ⁻¹' u, (pushout.inl φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inl φU φV '' U', ⟨⟨_, (pushout.inl φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inl φU φV).continuous, Or.inl (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DV} {x : DV}, x ∈ U → ∃ U' ∈ DV.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DV.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inr φU φV ⁻¹' u, (pushout.inr φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inr φU φV '' U', ⟨⟨_, (pushout.inr φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inr φU φV).continuous, Or.inr (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
  · have e : Set.range (φU ≫ pushout.inl φU φV) = Set.range (φV ≫ pushout.inr φU φV) := by
      rw [pushout.condition]
    have hWo : IsOpen (Set.range (φU ≫ pushout.inl φU φV)) := (φU ≫ pushout.inl φU φV).isOpenEmbedding.isOpen_range
    have mixed : ∀ s t : Set (pushout φU φV : Scheme.{0}), IsOpen s → IsCompact s →
        s ⊆ Set.range (pushout.inl φU φV) → IsOpen t → IsCompact t → t ⊆ Set.range (pushout.inr φU φV) →
        IsCompact (s ∩ t) := by
      intro s t so sc hs tO tc ht
      have hsub : s ∩ t ⊆ Set.range (φU ≫ pushout.inl φU φV) := by
        rintro x ⟨h1, h2⟩
        obtain ⟨a, rfl⟩ := hs h1
        obtain ⟨b, hb⟩ := ht h2
        obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr φU φV hb.symm
        exact ⟨w, by rw [Scheme.Hom.comp_apply, hw]⟩
      have hst : s ∩ t = (s ∩ Set.range (φU ≫ pushout.inl φU φV)) ∩ (t ∩ Set.range (φU ≫ pushout.inl φU φV)) := by
        ext x; constructor
        · intro hx; exact ⟨⟨hx.1, hsub hx⟩, ⟨hx.2, hsub hx⟩⟩
        · intro hx; exact ⟨hx.1.1, hx.2.1⟩
      rw [hst]
      refine qs_range (φU ≫ pushout.inl φU φV) _ _ Set.inter_subset_right (so.inter hWo)
        (compact_inter_range φU _ sc so hs) Set.inter_subset_right (tO.inter hWo) ?_
      rw [e]; exact compact_inter_range φV _ tc tO ht
    rintro ⟨s, so, sc, hs⟩ ⟨t, tO, tc, ht⟩
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact qs_range (pushout.inl φU φV) s t hs so sc ht tO tc
    · exact mixed s t so sc hs tO tc ht
    · show IsCompact (s ∩ t); rw [Set.inter_comm]; exact mixed t s tO tc ht so sc hs
    · exact qs_range (pushout.inr φU φV) s t hs so sc ht tO tc

theorem LeafGlueTwo_of : LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' leafPushoutQS

end LateralTheory.E.LeafGlueTwoPfQS
end
end
