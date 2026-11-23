module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
public import Mathlib.Algebra.Category.Grp.Zero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocycles
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtFFApprox

variable {J : Type} [SmallCategory J] (D0 : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}} (g' : D0.obj j ⟶ B')

def pmap {k k' : Under j} (φ : k ⟶ k') : pushout g' (D0.map k.hom) ⟶ pushout g' (D0.map k'.hom) :=
  pushout.desc (pushout.inl _ _) (D0.map φ.right ≫ pushout.inr _ _)
    (by rw [pushout.condition, ← Category.assoc, ← D0.map_comp, Under.w φ])

@[reassoc (attr := simp)] lemma inl_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inl _ _ ≫ pmap D0 j g' φ = pushout.inl _ _ := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma inr_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inr _ _ ≫ pmap D0 j g' φ = D0.map φ.right ≫ pushout.inr _ _ := pushout.inr_desc _ _ _

def arrF : Under j ⥤ Arrow CommRingCat.{0} where
  obj k := Arrow.mk (pushout.inr g' (D0.map k.hom))
  map {k k'} φ := Arrow.homMk' (D0.map φ.right) (pmap D0 j g' φ) (inr_pmap D0 j g' φ).symm
  map_id k := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp
  map_comp φ ψ := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp

@[simp] lemma arrF_map_left {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).left = D0.map φ.right := rfl
@[simp] lemma arrF_map_right {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).right = pmap D0 j g' φ := rfl

variable {A B : CommRingCat.{0}} (ι0 : D0 ⟶ (Functor.const J).obj A) (g : A ⟶ B) (h : B' ⟶ B)
  (hnat : ∀ k : Under j, g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g)

def pdesc (k : Under j) : pushout g' (D0.map k.hom) ⟶ B := pushout.desc h (ι0.app k.right ≫ g) (hnat k)

def coc : arrF D0 j g' ⟶ (Functor.const (Under j)).obj (Arrow.mk g) where
  app k := Arrow.homMk (f := (arrF D0 j g').obj k) (g := Arrow.mk g) (ι0.app k.right) (pdesc D0 j g' ι0 g h hnat k)
    (pushout.inr_desc _ _ (hnat k)).symm
  naturality k k' φ := by
    ext : 1
    · simp only [Arrow.comp_left, Functor.const_obj_map, Arrow.id_left, Category.comp_id, Arrow.homMk_left, arrF_map_left]
      rw [ι0.naturality φ.right]
      simp
    · simp only [Arrow.comp_right, Functor.const_obj_map, Arrow.id_right, Category.comp_id, Arrow.homMk_right, arrF_map_right]
      apply pushout.hom_ext
      · simp [pdesc]
      · simp only [pdesc, inr_pmap_assoc, pushout.inr_desc]
        rw [ι0.naturality_assoc φ.right]
        simp

lemma snd_coc (k : Under j) : (Comma.snd (𝟭 _) (𝟭 _)).map ((coc D0 j g' ι0 g h hnat).app k) = pdesc D0 j g' ι0 g h hnat k := rfl

@[reassoc] lemma inl_pdesc (k : Under j) : pushout.inl _ _ ≫ pdesc D0 j g' ι0 g h hnat k = h := pushout.inl_desc _ _ _
@[reassoc] lemma inr_pdesc (k : Under j) : pushout.inr _ _ ≫ pdesc D0 j g' ι0 g h hnat k = ι0.app k.right ≫ g := pushout.inr_desc _ _ _

def leftOf (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) : Cocone (Under.forget j ⋙ D0) where
  pt := s.pt
  ι := { app := fun k => pushout.inr g' (D0.map k.hom) ≫ s.ι.app k
         naturality := fun k k' φ => by
           have hw := s.w φ
           simp only [Functor.comp_map, Comma.snd_map] at hw
           dsimp
           rw [← hw, Category.comp_id]
           simp }

@[simp] lemma leftOf_ι_app (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) (k : Under j) :
    (leftOf D0 j g' s).ι.app k = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k := rfl

def rightIsColimit (hP : IsPushout g' (ι0.app j) h g) (hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j))) :
    IsColimit ((Comma.snd (𝟭 _) (𝟭 _)).mapCocone (Cocone.mk (Arrow.mk g) (coc D0 j g' ι0 g h hnat))) where
  desc s := hP.desc (pushout.inl _ _ ≫ s.ι.app (Under.mk (𝟙 j))) (hL.desc (leftOf D0 j g' s)) (by
      have := hL.fac (leftOf D0 j g' s) (Under.mk (𝟙 j))
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [pushout.condition_assoc]
      simp only [Under.mk_right] at this
      rw [this]
      simp)
  fac s k := by
    change pdesc D0 j g' ι0 g h hnat k ≫ _ = s.ι.app k
    apply pushout.hom_ext
    · have hw := s.w (Under.homMk k.hom (by simp) : Under.mk (𝟙 j) ⟶ k)
      simp only [Functor.comp_map, Comma.snd_map, arrF_map_right] at hw
      rw [inl_pdesc_assoc, IsPushout.inl_desc, ← hw]
      exact inl_pmap_assoc D0 j g' _ _
    · have := hL.fac (leftOf D0 j g' s) k
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [inr_pdesc_assoc, IsPushout.inr_desc, this]
  uniq s m hm := by
    apply hP.hom_ext
    · rw [IsPushout.inl_desc]
      have h1 := hm (Under.mk (𝟙 j))
      change pdesc D0 j g' ι0 g h hnat (Under.mk (𝟙 j)) ≫ m = s.ι.app (Under.mk (𝟙 j)) at h1
      rw [← h1, inl_pdesc_assoc]
    · rw [IsPushout.inr_desc]
      apply hL.hom_ext
      intro k
      have h1 := hL.fac (leftOf D0 j g' s) k
      have h2 := hm k
      change ι0.app k.right ≫ _ = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k at h1
      change pdesc D0 j g' ι0 g h hnat k ≫ m = s.ι.app k at h2
      change ι0.app k.right ≫ _ = ι0.app k.right ≫ _
      rw [h1, ← h2, inr_pdesc_assoc]

end GlobalTheory.EtFFApprox


open GlobalTheory.EtFFApprox in
theorem GlobalTheory.EtC.etFF_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  intro A B g hg
  obtain ⟨J, _, _, D0, ι0, ⟨hc⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨j, B', g', h, hg', hP⟩ := GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit J D0 (Cocone.mk A ι0) hc B g hg
  have hb := GlobalTheory.EtC.etFF_basic
  haveI := hb.1.2.1
  have hP' : IsPushout g' (ι0.app j) h g := hP
  have hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget j) _).symm hc
  have hnat : ∀ (k : Under j), g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g := by
    intro k
    rw [← Category.assoc, ι0.naturality k.hom]
    simpa using hP'.w
  refine ⟨Under j, inferInstance, inferInstance, arrF D0 j g', coc D0 j g' ι0 g h hnat, ⟨?_⟩, fun k => ?_⟩
  · exact Comma.fstSndJointlyReflectColimit hL (rightIsColimit D0 j g' ι0 g h hnat hP' hL)
  · have hk : EtFF (pushout.inr g' (D0.map k.hom)) :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout (IsPushout.of_hasPushout g' (D0.map k.hom)).flip hg'
    exact ⟨hk, hft k.right, hb.2.2 _ _ _ hk (hft k.right)⟩
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FiniteTypeApprox

theorem nat_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ε.naturality, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply]

theorem comm_apply {K L : AbCx} (φ : K ⟶ L) (i j : ℤ) (x : K.X i) :
    φ.f j (K.d i j x) = L.d i j (φ.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← φ.comm, ConcreteCategory.comp_apply]

theorem map_comp_apply (N : CommRingCat.{0} ⥤ AbCx) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (x : (N.obj A).X n) : (N.map (f ≫ g)).f n x = (N.map g).f n ((N.map f).f n x) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

theorem map_id_apply (N : CommRingCat.{0} ⥤ AbCx) (A : CommRingCat.{0}) (n : ℤ) (x : (N.obj A).X n) :
    (N.map (𝟙 A)).f n x = x := by
  simp

theorem inj_of_iso {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] {x y : X} (h : f x = f y) : x = y :=
  (ConcreteCategory.bijective_of_isIso f).1 h

theorem inv_apply_eq {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] (y : Y) : f (inv f y) = y := by
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

theorem eq_zero_of_isZero {X : AddCommGrpCat.{1}} (h : IsZero X) (x : X) : x = 0 := by
  have := (AddCommGrpCat.isZero_iff_subsingleton.1 h)
  exact Subsingleton.elim _ _

theorem isIso_f {K L : AbCx} (φ : K ⟶ L) [IsIso φ] (n : ℤ) : IsIso (φ.f n) :=
  (inferInstance : IsIso ((HomologicalComplex.eval _ _ n).map φ))

theorem locInj_of_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  intro N M ε F0 ι hF0 hι hMneg hMpos hN hε
  intro n A c hc hy
  obtain ⟨y, hy⟩ := hy
  obtain ⟨J, _, _, D, ιD, ⟨hcol⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨-, hN2⟩ := GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN
  obtain ⟨⟨hmul, hcob, -⟩, -, hftB⟩ := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties
  obtain ⟨j, w, y', hw, hwc⟩ := (hN2 J D (Cocone.mk A ιD) hcol n).1 c hc
  change (N.map (ιD.app j)).f n w = c + (N.obj A).d (n - 1) n y' at hwc
  have hwv : (M.obj (D.obj j)).d n (n + 1) ((ε.app (D.obj j)).f n w) = 0 := by
    rw [← comm_apply, hw, map_zero]

  have fin : (N.map (ιD.app j)).f n w = 0 → ∃ (V : CommRingCat.{0}) (g : A ⟶ V), EtFF g ∧
      ∃ b : (N.obj V).X (n - 1), (N.obj V).d (n - 1) n b = (N.map g).f n c := by
    intro h0
    refine ⟨A, 𝟙 A, MorphismProperty.id_mem EtFF A, -y', ?_⟩
    rw [map_id_apply, map_neg]
    rw [h0] at hwc
    exact (eq_neg_of_add_eq_zero_left hwc.symm).symm
  rcases lt_trichotomy n 0 with hn | hn | hn
  ·
    apply fin
    haveI := hε _ (hft j)
    haveI := isIso_f (ε.app (D.obj j)) n
    have : w = 0 := inj_of_iso ((ε.app (D.obj j)).f n)
      ((eq_zero_of_isZero (hMneg n hn _) _).trans (map_zero _).symm)
    rw [this, map_zero]
  ·
    subst hn
    apply fin
    have hy0 : y = 0 := eq_zero_of_isZero (hMneg _ (by norm_num) _) y
    rw [hy0, map_zero] at hy
    obtain ⟨x0, hx0⟩ := ((hι (D.obj j)).2 _).1 hwv
    have hιnat : ∀ {B C : CommRingCat.{0}} (g : B ⟶ C) (x : F0.obj B),
        ι.app C (F0.map g x) = (M.map g).f 0 (ι.app B x) := by
      intro B C g x
      rw [← ConcreteCategory.comp_apply, ι.naturality, ConcreteCategory.comp_apply]
      rfl
    have hdie : F0.map (ιD.app j) x0 = 0 := by
      apply (hι A).1
      rw [hιnat, hx0, ← nat_apply, hwc, map_add (f := _), hy, comm_apply,
        eq_zero_of_isZero (hMneg _ (by norm_num) _) ((ε.app A).f (0 - 1) y'), map_zero, add_zero]
      exact (map_zero _).symm
    obtain ⟨-, hF0inj⟩ := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A ιD) hcol
    obtain ⟨k, f, hk⟩ := hF0inj j x0 hdie
    haveI := hε _ (hft k)
    haveI := isIso_f (ε.app (D.obj k)) 0
    have hwk : (N.map (D.map f)).f 0 w = 0 := by
      apply inj_of_iso ((ε.app (D.obj k)).f 0)
      rw [nat_apply, ← hx0, ← hιnat, hk, map_zero, map_zero]
    have hcw : ιD.app j = D.map f ≫ ιD.app k := by
      have := ιD.naturality f
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
      exact this.symm
    rw [hcw, map_comp_apply, hwk, map_zero]
  ·
    obtain ⟨B0, g0, hg0, y0, hy0⟩ := hMpos n hn _ _ hwv
    have hB0 := hftB _ _ g0 hg0 (hft j)
    haveI := hε _ hB0
    haveI := isIso_f (ε.app B0) n
    haveI := isIso_f (ε.app B0) (n - 1)
    set b0 := inv ((ε.app B0).f (n - 1)) y0 with hb0
    have hdb0 : (N.obj B0).d (n - 1) n b0 = (N.map g0).f n w := by
      apply inj_of_iso ((ε.app B0).f n)
      rw [comm_apply, hb0, inv_apply_eq, hy0, nat_apply]
    haveI := hcob
    have hg : EtFF (pushout.inr g0 (ιD.app j)) := MorphismProperty.pushout_inr _ _ hg0
    refine ⟨pushout g0 (ιD.app j), pushout.inr g0 (ιD.app j), hg,
      (N.map (pushout.inl g0 (ιD.app j))).f (n - 1) b0 - (N.map (pushout.inr g0 (ιD.app j))).f (n - 1) y', ?_⟩
    rw [map_sub, ← comm_apply, ← comm_apply, hdb0, ← map_comp_apply, pushout.condition, map_comp_apply, hwc,
      map_add]
    exact add_sub_cancel_right _ _
end GlobalTheory.EtC.FiniteTypeApprox
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.n0_sub_glue_le_card_mul_sum_lintegral : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  first | exact @GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le | exact GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le | (intros; apply GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.n1_cutoff_mul_section_le_lintegral : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  first | exact @GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le | exact GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le | (intros; apply GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le <;> assumption)
end

section

open TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles : ∀ (A : Type) [CommRing A], ∃ δ : ∀ (B : Type) [CommRing B] [Algebra A B], (B ⊗[A] B)ˣ → CommRing.Pic A, ∀ (B : Type) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B], (∀ u v, UCoc A B u → UCoc A B v → δ B (u * v) = δ B u * δ B v) ∧ (∀ u, UCoc A B u → (δ B u = 1 ↔ ∃ w : Bˣ, (u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) w = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) w)) ∧ (∀ c : CommRing.Pic A, CommRing.Pic.mapAlgebra A B c = 1 → ∃ u, UCoc A B u ∧ δ B u = c) ∧ (∀ u, UCoc A B u → ∃ _ : Module.Invertible A (descMod A B u), CommRing.Pic.mk A (descMod A B u) = δ B u) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : (B ⊗[A] B)ˣ) (u' : (B' ⊗[A] B')ˣ), UCoc A B u → (u' : B' ⊗[A] B') = Algebra.TensorProduct.map φ φ (u : B ⊗[A] B) → δ B' u' = δ B u := by
  first | (exact @GlobalTheory.pic_cech_descent) | (exact GlobalTheory.pic_cech_descent) | (intros; apply GlobalTheory.pic_cech_descent  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.eventually_exists_quaternion_norm_one_re_eq : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | exact GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | (intros; apply GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

open Polynomial

theorem isIntegral_of_le {k F K : Type} [Field k] [Field F] [Field K] [Algebra k F] [Algebra F K]
    {A A' : Subalgebra k F} (h : A ≤ A') {y : K} (hy : IsIntegral A y) : IsIntegral A' y := by
  obtain ⟨p, hm, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h), hm.map _, ?_⟩
  rw [eval₂_map]
  exact he

theorem rA_mono (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)
    {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  apply Algebra.adjoin_mono
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem rB_mono_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I →
    (∀ J, I ⊆ J → rB k K x I ≤ rB k K x J) ∧
    ∀ y : K, y ∈ rB k K x I ↔ ∃ N : ℕ, y * algebraMap F K (∏ j ∈ I, x j / x i) ^ N ∈ rB k K x {i} := by
  intro k _ _ F K _ _ _ _ _ _ d x hK I i hi
  have memB : ∀ (J : Finset (Fin (d + 1))) (y : K), y ∈ rB k K x J ↔ IsIntegral (rA k x J) y := fun J y => by
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  refine ⟨fun J hJ y hy => (memB J y).2 (isIntegral_of_le (rA_mono k x hJ) ((memB I y).1 hy)), fun y => ?_⟩
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsi : s ∈ rA k x {i} := Subalgebra.prod_mem _ fun j _ =>
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  have hsinv : s⁻¹ ∈ rA k x I := by
    rw [hs, ← Finset.prod_inv_distrib]
    refine Subalgebra.prod_mem _ fun j hj => ?_
    rw [inv_div]
    exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩
  have hsne : s ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hK.pd.ne j) (hK.pd.ne i)
  have hiI : rA k x {i} ≤ rA k x I := rA_mono k x (Finset.singleton_subset_iff.2 hi)
  simp only [memB]
  constructor
  · rintro ⟨p, hm, he⟩
    have hc : ∀ m, ∃ N : ℕ, (p.coeff m : F) * s ^ N ∈ rA k x {i} := fun m =>
      (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hK.pd I i hi (p.coeff m : F)).1 (p.coeff m).2
    choose Nf hNf using hc
    set N := (Finset.range (p.natDegree + 1)).sup Nf
    have hcN : ∀ m, (p.coeff m : F) * s ^ N ∈ rA k x {i} := by
      intro m
      by_cases hmd : m ≤ p.natDegree
      · have hle : Nf m ≤ N := Finset.le_sup (f := Nf) (Finset.mem_range.2 (Nat.lt_succ_of_le hmd))
        rw [← Nat.add_sub_cancel' hle, pow_add, ← mul_assoc]
        exact Subalgebra.mul_mem _ (hNf m) (Subalgebra.pow_mem _ hsi _)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hmd)]
        simp
    set q : F[X] := (p.map (algebraMap (rA k x I) F)).scaleRoots (s ^ N)
    have hqm : q.Monic := (monic_scaleRoots_iff _).2 (hm.map _)
    have hdeg : (p.map (algebraMap (rA k x I) F)).natDegree = p.natDegree :=
      natDegree_map_eq_of_injective (fun a b h => Subtype.ext h) _
    have hl : q ∈ lifts (algebraMap (rA k x {i}) F) := by
      rw [lifts_iff_coeff_lifts]
      intro m
      rw [coeff_scaleRoots, coeff_map, hdeg]
      have hmem : (algebraMap (rA k x I) F (p.coeff m)) * (s ^ N) ^ (p.natDegree - m) ∈ rA k x {i} := by
        by_cases hmd : m < p.natDegree
        · obtain ⟨e, he'⟩ : ∃ e, p.natDegree - m = e + 1 := ⟨p.natDegree - m - 1, by omega⟩
          rw [he', pow_succ', ← mul_assoc]
          exact Subalgebra.mul_mem _ (hcN m) (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ hsi _) _)
        · rw [Nat.sub_eq_zero_of_le (not_lt.1 hmd), pow_zero, mul_one]
          rcases (not_lt.1 hmd).eq_or_lt with h | h
          · rw [← h, hm.coeff_natDegree, map_one]
            exact Subalgebra.one_mem _
          · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
            exact Subalgebra.zero_mem _
      exact ⟨⟨_, hmem⟩, rfl⟩
    obtain ⟨q0, hq0, -, hq0m⟩ := lifts_and_natDegree_eq_and_monic hl hqm
    refine ⟨N, q0, hq0m, ?_⟩
    have h1 : eval₂ (algebraMap F K) y (p.map (algebraMap (rA k x I) F)) = 0 := by
      rw [eval₂_map]
      exact he
    have h2 : eval₂ (algebraMap F K) (algebraMap F K (s ^ N) * y) q = 0 :=
      scaleRoots_eval₂_eq_zero (algebraMap F K) (s := s ^ N) h1
    rw [← map_pow, mul_comm]
    rw [← hq0, eval₂_map] at h2
    exact h2
  · rintro ⟨N, hN⟩
    have h1 : IsIntegral (rA k x I) (y * algebraMap F K s ^ N) := isIntegral_of_le hiI hN
    have h2 : IsIntegral (rA k x I) (algebraMap F K s⁻¹ ^ N) := by
      have : IsIntegral (rA k x I) (algebraMap (rA k x I) K ⟨s⁻¹, hsinv⟩) := isIntegral_algebraMap
      exact this.pow N
    have h3 := h1.mul h2
    rwa [mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ hsne, map_one, one_pow, mul_one] at h3

end GlobalTheory.PD
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  first | (exact @GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (exact GlobalTheory.PD.mem_omB_of_mul_mem_omB) | (intros; apply GlobalTheory.PD.mem_omB_of_mul_mem_omB  <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.hom_eq_zero_of_isConn_of_isEt' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k), G.IsConn → H.IsEt → (∀ f : G ⟶ H, f = 0) ∧ ∀ f : H ⟶ G, f = 0 := by
  first | exact @GlobalTheory.PDivGroup.hom_eq_zero_of_isConn_of_isEt | exact GlobalTheory.PDivGroup.hom_eq_zero_of_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.hom_eq_zero_of_isConn_of_isEt <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_comp_equiv (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y)
    (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ) (hμ : μ.map T = r • μ') (h : HasGauss μ' f γ) :
    HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  intro K hK
  obtain ⟨L, hLc, hLo, hKL, hint⟩ := h (T '' K) (hK.image T.continuous)
  have hme : MeasurableEmbedding (T : X → Y) := T.toHomeomorph.measurableEmbedding
  have hset : ((L.comap (T.toAddEquiv.toAddMonoidHom) : AddSubgroup X) : Set X) = (T : X → Y) ⁻¹' (L : Set Y) := rfl
  refine ⟨L.comap T.toAddEquiv.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hset]
    exact T.toHomeomorph.isCompact_preimage.2 hLc
  · rw [hset]
    exact hLo.preimage T.continuous
  · rw [hset]
    intro x hx
    exact hKL ⟨x, hx, rfl⟩
  · rw [hset, ← hme.setIntegral_map f (L : Set Y), hμ, Measure.restrict_smul, integral_smul_nnreal_measure, hint]
    simp [NNReal.smul_def]

end GlobalTheory.KSp
end
