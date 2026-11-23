module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
noncomputable local instance (priority := high) grpObjPullbackForModuli {S T : Scheme.{0}} (f : T ⟶ S)
    (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory

theorem splitFibre_of_isOpenImmersion {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsOpenImmersion f] (G : Over Z) [GrpObj G]
    (G' : Over Y) [GrpObj G'] (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) (h : SplitFib G') (y : Y) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField (f y)) k), FiniteDimensional (Z.residueField (f y)) k ∧
      Algebra.IsSeparable (Z.residueField (f y)) k ∧ ∃ S : SplitExt (Sp k),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫
          Z.fromSpecResidueField (f y))).obj G) := by
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := h y
  let ε : Z.residueField (f y) ≃+* Y.residueField y := (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv
  let A : Algebra (Z.residueField (f y)) k :=
    ((algebraMap (Y.residueField y) k).comp (f.residueFieldMap y).hom).toAlgebra
  have hc : (algebraMap (Z.residueField (f y)) k).comp (ε.symm : Y.residueField y →+* Z.residueField (f y)) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (Y.residueField y) k) := by
    ext a
    exact congrArg (algebraMap (Y.residueField y) k) (ε.apply_symm_apply a)
  refine ⟨k, inferInstance, A, Module.Finite.of_equiv_equiv ε.symm (RingEquiv.refl k) hc,
    Algebra.IsSeparable.of_equiv_equiv ε.symm (RingEquiv.refl k) hc, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Y.fromSpecResidueField y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫ Z.fromSpecResidueField (f y) := by
    have a₁ : Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Spec.map (f.residueFieldMap y) := by
      rw [← Spec.map_comp]
      rfl
    rw [a₁, Category.assoc, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← key]
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y)).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₀ := isGt_of_iso ((Over.pullback _).mapIso e) hGt
  have : IsMonHom (pullCompIso (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y) f G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  exact isGt_of_iso (pullCompIso _ f G).symm h₀

theorem splitFib_of_openCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  intro E _ _ _ H Z t I Y f u m ho hc hs z
  obtain ⟨i, y, rfl⟩ := hc z
  have := ho i
  exact splitFibre_of_isOpenImmersion (f i) t.G (u i).G _ (m i).cart (hs i) y

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.AbLocusLocal

private theorem isProper_of_isPullback_of_pullback_snd {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper (pullback.snd f g)) : IsProper snd := by
  rw [← h.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.hom (pullback.snd f g)).2 H

private theorem isProper_pullback_snd_of_isPullback {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper snd) : IsProper (pullback.snd f g) := by
  rw [← h.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.inv snd).2 H

private theorem isProper_snd_of_isPullback_of_isProper {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (hf : IsProper f) : IsProper snd :=
  isProper_of_isPullback_of_pullback_snd h inferInstance

theorem isProper_restrict_of_cover {X Z : Scheme.{0}} (p : X ⟶ Z) {I : Type} {Y X' : I → Scheme.{0}}
    (f : ∀ i, Y i ⟶ Z) [∀ i, IsOpenImmersion (f i)] (p' : ∀ i, X' i ⟶ Y i) (F : ∀ i, X' i ⟶ X)
    (h : ∀ i, IsPullback (F i) (p' i) p (f i)) (V : ∀ i, (Y i).Opens) (hV : ∀ i, IsProper (p' i ∣_ V i))
    (U : Z.Opens) (hle : ∀ i, Set.range ((V i).ι ≫ f i) ⊆ Set.range U.ι)
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range ((V i).ι ≫ f i)) : IsProper (p ∣_ U) := by
  have hsq : ∀ i, IsPullback (((p' i) ⁻¹ᵁ V i).ι ≫ F i) (p' i ∣_ V i) p ((V i).ι ≫ f i) := fun i =>
    (isPullback_morphismRestrict (p' i) (V i)).flip.paste_horiz (h i)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hi⟩ := hc (U.ι x) x.2
    exact ⟨i, by simpa [Scheme.Hom.coe_opensRange] using hi⟩
  · intro i
    let W : U.toScheme.Opens := U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange
    have hr : Set.range (W.ι ≫ U.ι) ⊆ Set.range ((V i).ι ≫ f i) := by
      rintro _ ⟨x, rfl⟩
      have hx : U.ι x.val ∈ ((V i).ι ≫ f i).opensRange := x.2
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hx
      exact hx
    let e := IsOpenImmersion.lift ((V i).ι ≫ f i) (W.ι ≫ U.ι) hr
    have he : e ≫ ((V i).ι ≫ f i) = W.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    have big := (isPullback_morphismRestrict (p ∣_ U) W).flip.paste_horiz (isPullback_morphismRestrict p U).flip
    rw [← he] at big
    have hw : ((((p ∣_ U) ⁻¹ᵁ W).ι ≫ (p ⁻¹ᵁ U).ι)) ≫ p = ((p ∣_ U) ∣_ W ≫ e) ≫ ((V i).ι ≫ f i) := by
      rw [big.w, Category.assoc]
    have sq : IsPullback ((hsq i).lift _ _ hw) ((p ∣_ U) ∣_ W) (p' i ∣_ V i) e := by
      refine IsPullback.of_right ?_ ((hsq i).lift_snd _ _ hw) (hsq i)
      rw [(hsq i).lift_fst]
      exact big
    exact isProper_snd_of_isPullback_of_isProper sq (hV i)

private theorem mem_abLocus_of_map_mem_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y) (hy : g y ∈ abLocus B) :
    y ∈ abLocus A := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x, rfl⟩ := hs
  have big := (IsPullback.of_hasPullback A.hom s).paste_horiz h
  exact isProper_of_isPullback_of_pullback_snd big (hy K (s ≫ g) ⟨x, by rw [Scheme.Hom.comp_apply]⟩)

private theorem map_mem_abLocus_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    [IsOpenImmersion g] {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y)
    (hy : y ∈ abLocus A) : g y ∈ abLocus B := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x0, hx0⟩ := hs
  have hr : Set.range s ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x x0, hx0]
    exact ⟨y, rfl⟩
  have hs' : IsOpenImmersion.lift g s hr ≫ g = s := IsOpenImmersion.lift_fac g s hr
  have big := (IsPullback.of_hasPullback A.hom (IsOpenImmersion.lift g s hr)).paste_horiz h
  rw [hs'] at big
  have hy' : y ∈ Set.range (IsOpenImmersion.lift g s hr) := by
    refine ⟨x0, g.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hs', hx0]
  exact isProper_pullback_snd_of_isPullback big (hy K _ hy')

theorem abOpen_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  intro E _ _ _ H Z t I Y f u m hf hc hab
  unfold AbOpen at hab ⊢
  choose V hVs hVp using hab
  have hpb : ∀ i, IsPullback (m i).φ (u i).G.hom t.G.hom (f i) := fun i => (m i).cart.1
  refine ⟨⨆ i, ((V i).ι ≫ f i).opensRange, ?_, ?_⟩
  · ext z
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, Scheme.Hom.coe_opensRange]
    constructor
    · rintro ⟨i, v, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact map_mem_abLocus_of_isPullback (hpb i) _ (by rw [← hVs i]; exact v.2)
    · intro hz
      obtain ⟨i, y, rfl⟩ := hc z
      have hy := mem_abLocus_of_map_mem_of_isPullback (hpb i) y hz
      rw [← hVs i] at hy
      exact ⟨i, ⟨y, hy⟩, rfl⟩
  · refine isProper_restrict_of_cover t.G.hom f (fun i => (u i).G.hom) _ hpb V hVp _ ?_ ?_
    · intro i z hz
      rw [Scheme.Opens.range_ι]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]; exact hz⟩
    · intro z hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hi
      exact ⟨i, hi⟩

end GlobalTheory.AbLocusLocal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem RZ.rt_coe (S A : ℕ) : ((RZ.rt H S A : RZ H S A) : ℂ) = H.rt0 := by
  have h2 : ((2 : RZ H S A) : ℂ) = 2 := map_ofNat (RZ H S A).subtype 2
  unfold RZ.rt
  push_cast
  rw [h2]
  ring

theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (KA l))
    (o : Obj D l (baseKA l) s) (β : RZ H n l.A →+* KA l) (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) :
    FullObj D (s ≫ spMap β) o.t o.etaA := by
  unfold IsInc at hβ
  have hρ : β (RZ.rt H n l.A) = (baseKA l).ρ := by
    apply Subtype.ext
    show ((β (RZ.rt H n l.A) : ℂ)) = H.rt0
    rw [← RZ.rt_coe (H := H) n l.A]
    exact hβ (RZ.rt H n l.A)
  have hze : β (RZ.ze H n l.A) = (baseKA l).ζ := by
    apply Subtype.ext
    show ((β (RZ.ze H n l.A) : ℂ)) = zeta l.A
    exact hβ (RZ.ze H n l.A)
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, ?_⟩
  intro k _ _ _ x β' hx
  obtain ⟨g0, hg0⟩ : ∃ g0 : KA l →+* k, x ≫ s = spMap g0 := by
    refine ⟨(Spec.preimage (x ≫ s)).hom, ?_⟩
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hb : β' = g0.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom (g0.comp β)) := by
      unfold spMap at hx hg0
      rw [← hx, ← Category.assoc, hg0, ← Spec.map_comp, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hb
  obtain ⟨hdet, I, hI1, hI2, -⟩ := o.geom k x g0 hg0
  refine ⟨?_, I, ?_, hI2⟩
  · rw [RingHom.comp_apply, hρ]
    exact hdet
  · rw [RingHom.comp_apply, hze]
    exact hI1

end GlobalTheory.Models
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.fullObj_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (f : S' ⟶ S), (∃ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) ∧ ∀ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → FullObj D s t lev → FullObj D (f ≫ s) t' lv := by
  intro E _ _ _ H D n N S S' s t lev f
  refine ⟨?_, fun t' m lv hlv o => ?_⟩
  · obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
      have hC := Out.CubePf.cubePull
      have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
        refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
        · have := t.semi.comm
          infer_instance
        · have := t.semi.smooth
          change Smooth (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.separated
          change IsSeparated (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.quasiCompact
          change QuasiCompact (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.geomConnected
          change GeometricallyConnected (pullback.snd t.G.hom f)
          infer_instance
        · intro Ω _ _ q
          obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ f)
          exact ⟨torusExtOfIso (pullCompIso q f t.G) A⟩
      have hp : ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
          (m : SABMap ⟨(Over.pullback f).obj t.G, hsemi, OAct.pullback f t.G t.act, PP', cub,
            sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
        have h := isGrpPullback_pullback t.G f
        obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
        have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
            pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
        have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
            pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
          Over.OverMorphism.ext (by
            show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
            rw [Category.assoc, hact, Category.assoc])
        refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
        · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
            (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
          refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
          · fin_cases i
            · exact (pa _ a).trans (by simp [U])
            · simp [U]
          · fin_cases i
            · simp [U]
            · exact (pa _ _).trans (by simp [U])
        · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
          refine LBIso.chartPull (chartPullPull t.PP.L _)
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
      obtain ⟨_, _, _, _, _, m, -⟩ := hp
      exact ⟨_, ⟨m⟩⟩
    exact ⟨t', m, fun a => GlobalTheory.ObjPull.secPull m.cart (lev a), fun a => GlobalTheory.ObjPull.secPull_left m.cart _⟩
  have hlv' : ∀ a, lv a = GlobalTheory.ObjPull.secPull m.cart (lev a) := fun a => by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · exact (hlv a).trans (GlobalTheory.ObjPull.secPull_left m.cart _).symm
    · rw [Over.w, Over.w]
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  obtain ⟨-, hamp, hk⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi) m.cart hL
  refine
    { proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
      ample := hamp o.ample
      ktriv := hk o.ktriv
      add := fun a c => by rw [hlv', hlv', hlv', o.add, map_mul]
      ker := fun a => by rw [hlv', o.ker a, map_one]
      geom := fun k _ _ _ x β hx => ?_ }
  obtain ⟨hdet, I, hI, hA⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
  refine ⟨fun τ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, hI, fun a => ?_⟩
  · rw [GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ,
      GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ]
    exact hdet τ
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
  · rw [hlv']
    exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull m.cart _ _).trans (hA a))
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem exists_lift {S S' : Scheme.{0}} (f : S' ⟶ S) {k : Type} [Field k] (x : Sp k ⟶ S) (p : Sp k)
    (hp : x p ∈ Set.range f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : k →+* Ω) (y : Sp Ω ⟶ S'), spMap i ≫ x = y ≫ f := by
  obtain ⟨q, hq⟩ := hp
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := f) p q hq.symm
  let Ω : Type := AlgebraicClosure ((pullback x f).residueField z)
  let u : Sp Ω ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField z) Ω)) ≫ (pullback x f).fromSpecResidueField z
  refine ⟨Ω, inferInstance, inferInstance, (Spec.preimage (u ≫ pullback.fst x f)).hom, u ≫ pullback.snd x f, ?_⟩
  have e : spMap (Spec.preimage (u ≫ pullback.fst x f)).hom = u ≫ pullback.fst x f := Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem tate_push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {k : Type} [Field k] {y : Sp k ⟶ S'} {x : Sp k ⟶ S} (hx : x = y ≫ f)
    (I : TateIso D k (Over.mk y ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
        (fun m g g' c => Out.WeilIs t'.G t'.PP.L m g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      J.ζ = I.ζ ∧ ∀ m a, (J.ev m a).left = (I.ev m a).left ≫ ν.φ := by
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    rfl, fun _ _ => rfl⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc

theorem torsion_ext (hL : Out.Laws) {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) :
    Function.Injective (TateIsoFieldExt.precomp
        (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G) ∧
      ∀ m, 0 < m → ∀ z : Over.mk (spMap i ≫ x) ⟶ t.G, z ^ m = 1 → ∃ y : Over.mk x ⟶ t.G, y ^ m = 1 ∧
        TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G y = z := by
  obtain ⟨P, φ, -, hφ, -⟩ := exists_polAV_pullback_of_isLocalRing E H S t hp ha hk K x
  obtain ⟨hinj, honto⟩ := torsion_points_field_extension hL (Sp K) P K Ω i (𝟙 _)
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) x (Category.id_comp _).symm
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap i ≫ 𝟙 _) (spMap i ≫ x) (by simp)
  have key : ∀ y, TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G (e y) =
      e' ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K))) ≫ y) := fun y => by
    apply Over.OverMorphism.ext
    rw [he']
    show spMap i ≫ (e y).left = (spMap i ≫ y.left) ≫ φ
    rw [he]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun y y' h => ?_, fun m hm z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [key, key] at h
    exact congrArg e (hinj (e'.injective h))
  · obtain ⟨z, rfl⟩ := e'.surjective z
    rw [← map_pow, map_eq_one_iff _ e'.injective] at hz
    obtain ⟨y, hy, rfl⟩ := honto m z (Nat.cast_ne_zero.2 hm.ne') hz
    exact ⟨e y, by rw [← map_pow, hy, map_one], key y⟩

theorem fullObj_of_cover : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  intro hL E _ _ _ H D n N S s t lv hN hp ha hk hadd hker hcov
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  obtain ⟨S', f, t', ν, lv', hq, hl, o⟩ := hcov (x (default : PrimeSpectrum k))
  obtain ⟨Ω, _, _, i, y, hy⟩ := exists_lift f x _ hq
  have : CharZero Ω := (i.charZero_iff i.injective).1 inferInstance
  have hy' : y ≫ f ≫ s = spMap (i.comp β) := by
    rw [← Category.assoc, ← hy, Category.assoc, hx]
    exact (Spec.map_comp _ _).symm
  obtain ⟨hdet, I', hI', hA'⟩ := o.geom Ω y (i.comp β) hy'
  refine ⟨?_, ?_⟩
  · refine (detCond_iff_of_field_extension E H D S t.G k Ω i x t.act _ t.semi.smooth).1 ?_
    rw [hy]
    exact (detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ Ω y _).1 hdet
  obtain ⟨J, hJ, hJ'⟩ := tate_push ν hy I'
  obtain ⟨hinj, honto⟩ := torsion_ext hL t hp ha hk i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  obtain ⟨I, hI⟩ := TateIsoFieldExt.down D i (TateIsoFieldExt.precomp g t.G)
    (act := fun a z => z ≫ t.act.act a) (act' := fun a z => z ≫ t.act.act a)
    (e' := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c))
    (e := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c)) hinj honto
    (fun c z => (Category.assoc g z (t.act.act c)).symm)
    (fun c => by
      haveI := t.act.hom c
      exact MonObj.one_comp (t.act.act c))
    (fun m z z' c => weilIs_fieldExt_iff S t.G k Ω i x t.PP.L m z z' c
      ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.PP.isLB) J
  obtain ⟨h₁, h₂⟩ := hI N hN
  refine ⟨I, i.injective ?_, fun a => hinj ?_⟩
  · rw [← h₁, hJ, hI']
    rfl
  · rw [← h₂]
    apply Over.OverMorphism.ext
    rw [hJ', ← hA', Over.comp_left, ObjPull.toUnit_left', Category.assoc, hl]
    show spMap i ≫ (toUnit (Over.mk x) ≫ lv a).left = y ≫ f ≫ (lv a).left
    rw [Over.comp_left, ObjPull.toUnit_left', ← Category.assoc y, ← hy]
    exact (Category.assoc _ _ _).symm

end GlobalTheory.FullDescent
end
