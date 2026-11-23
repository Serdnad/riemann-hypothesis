module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle397
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.LerayOne

def diag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      dsimp [sch, cech, Arrow.cechNerve]
      erw [Category.id_comp, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
    · dsimp [sch, cech, Arrow.cechNerve]
      erw [Category.id_comp, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]

theorem diag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : diag f ≫ cechAug f = sch.map f := by
  ext n : 1
  rw [NatTrans.comp_app]
  dsimp [diag, cechAug, sch, Arrow.augmentedCechNerve]
  erw [WidePullback.lift_base]

theorem diag_zero {Y X : Scheme.{0}} (f : Y ⟶ X) :
    WidePullback.π (fun _ : Fin 1 => yoneda.map f) (0 : Fin 1) ≫ (diag f).app (op ⦋0⦌) = 𝟙 ((cech f).obj (op ⦋0⦌)) := by
  apply WidePullback.hom_ext
  · intro j
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hj
    dsimp [diag]
    erw [Category.assoc, WidePullback.lift_π, Category.comp_id]
  · dsimp [diag]
    erw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

end GlobalTheory.EtC.LerayOne

noncomputable section
namespace GlobalTheory.EtC.LerayOne

theorem cech_cocycle_of_pull_eq_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (x : H R (sch.obj X) F 1),
      pull R (sch.map f) F 1 x = 0 →
        ∃ s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F,
          cobd (R := R) (E := cech f) (n := 1) s = 0 ∧ IsCls (R := R) s (pull R (cechAug f) F 1 x) := by
  intro R _ F Y X f x hx
  obtain ⟨-, hneg, hmono, ⟨w0, hex⟩, -, -⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz⟩ := (pull R (cechAug f) F 1 x).mk_surjective
  have h0 : pull R (diag f) F 1 (CohomologyClass.mk z) = 0 := by
    rw [hz, ← pull_comp, diag_aug, hx]
  have h0' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (diag f))) z (zero_add 1)) = 0 := h0
  rw [CohomologyClass.mk_eq_zero_iff] at h0'
  obtain ⟨m, hm, w, hw⟩ := h0'
  obtain rfl : m = 0 := by omega

  have hw01 : ((chains R).map (diag f)).f 0 ≫ z.1.v 0 1 (zero_add 1) =
      w.v 0 0 (add_zero 0) ≫ (res R F).d 0 1 := by
    have := Cochain.congr_v hw 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) w 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (sch.obj Y) 1 one_pos).eq_of_tgt (((chains R).obj (sch.obj Y)).d 0 1) 0,
      zero_comp, smul_zero, add_zero] at this
    rw [this]
    change _ = ((Cochain.ofHom ((chains R).map (diag f))).comp z.1 (zero_add 1)).v 0 1 (zero_add 1)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have cm0 : (chainsXIso R (sch.obj Y) 0).inv ≫ ((chains R).map (diag f)).f 0 =
      (free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv := CupSpec.chains_map (diag f) 0
  let r : (cech f).obj (op ⦋0⦌) ⟶ (sch.obj Y).obj (op ⦋0⦌) := WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0
  have hr : r ≫ (diag f).app (op ⦋0⦌) = 𝟙 _ := diag_zero f
  let y0 : (free R).obj ((cech f).obj (op ⦋0⦌)) ⟶ (res R F).X 0 :=
    (free R).map r ≫ (chainsXIso R (sch.obj Y) 0).inv ≫ w.v 0 0 (add_zero 0)
  have hA0 : (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1) = y0 ≫ (res R F).d 0 1 := by
    calc (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1)
        = (free R).map r ≫ ((free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv) ≫
            z.1.v 0 1 (zero_add 1) := by
          rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hr, CategoryTheory.Functor.map_id, Category.id_comp]
      _ = y0 ≫ (res R F).d 0 1 := by
          rw [← cm0, Category.assoc, hw01]
          simp only [y0, Category.assoc]
  let c : Cochain ((chains R).obj (cech f)) (res R F) 0 :=
    Cochain.single (p := 0) (q := 0) ((chainsXIso R (cech f) 0).hom ≫ y0) 0
  let b : Cocycle ((chains R).obj (cech f)) (res R F) 1 := Cocycle.mk (δ 0 1 c) 2 (by norm_num) (δ_δ 0 1 2 c)
  have hb : CohomologyClass.mk b = 0 := (CohomologyClass.mk_eq_zero_iff b).2 ⟨0, zero_add 1, c, rfl⟩
  let ζ := z - b
  have hζ : CohomologyClass.mk ζ = pull R (cechAug f) F 1 x := by
    rw [CohomologyClass.mk_sub, hb, sub_zero, hz]
  have hζv : ∀ p q hpq, ζ.1.v p q hpq = z.1.v p q hpq - (δ 0 1 c).v p q hpq := fun p q hpq => by
    simp only [ζ, b, Cocycle.coe_sub, Cochain.sub_v]
    rfl
  have hζ01 : ζ.1.v 0 1 (zero_add 1) = 0 := by
    rw [hζv, δ_v 0 1 (zero_add 1) c 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (cech f) 1 one_pos).eq_of_tgt (((chains R).obj (cech f)).d 0 1) 0,
      zero_comp, smul_zero, add_zero, Cochain.single_v]
    rw [← cancel_epi (chainsXIso R (cech f) 0).inv, Preadditive.comp_sub, hA0, comp_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, sub_self]
  have hδζ : δ 1 2 ζ.1 = 0 := Cocycle.δ_eq_zero ζ 2
  have hB : ζ.1.v (-1) 0 (by norm_num) ≫ (res R F).d 0 1 = 0 := by
    have := Cochain.congr_v hδζ (-1) 1 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-1) 1 (by norm_num) 0 0 (by norm_num) (by norm_num), hζ01, comp_zero,
      smul_zero, add_zero, Cochain.zero_v] at this
    exact this
  haveI := hmono
  let B : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ (res R F).X 0 :=
    (chainsXIso R (cech f) 1).inv ≫ ζ.1.v (-1) 0 (by norm_num)
  have hBd : B ≫ (res R F).d 0 1 = 0 := by simp only [B, Category.assoc, hB, comp_zero]
  let s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F := hex.lift B hBd
  have hs : s ≫ resι R F = B := hex.lift_f B hBd
  refine ⟨s, ?_, ζ, hζ, ?_⟩
  · have h20 := Cochain.congr_v hδζ (-2) 0 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-2) 0 (by norm_num) (-1) (-1) (by norm_num) (by norm_num),
      (hneg (-1) (by norm_num)).eq_of_tgt (ζ.1.v (-2) (-1) (by norm_num)) 0, zero_comp, zero_add, Cochain.zero_v] at h20
    have h2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
    rw [h2, one_smul] at h20
    have hd : (chainsXIso R (cech f) 2).inv ≫ ((chains R).obj (cech f)).d (-2) (-1) =
        (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (free R).map ((cech f).δ i)) ≫ (chainsXIso R (cech f) 1).inv :=
      CupSpec.chains_d (cech f) 1
    have h3 := congrArg ((chainsXIso R (cech f) 2).inv ≫ ·) h20
    simp only [comp_zero] at h3
    rw [← Category.assoc, hd, Category.assoc] at h3
    apply (cancel_mono (resι R F)).1
    rw [zero_comp, cobd, Preadditive.sum_comp]
    rw [Preadditive.sum_comp] at h3
    refine Eq.trans ?_ h3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Preadditive.zsmul_comp, Category.assoc, hs, B]
  · apply Cochain.ext
    intro p q hpq
    by_cases hp1 : p = -((1 : ℕ) : ℤ)
    · subst hp1
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hs]
      change _ = (chainsXIso R (cech f) 1).hom ≫ (chainsXIso R (cech f) 1).inv ≫ ζ.1.v _ 0 hpq
      rw [Iso.hom_inv_id_assoc]
    · rw [Cochain.single_v_eq_zero _ _ _ _ _ hp1]
      by_cases hp0 : p = 0
      · subst hp0
        obtain rfl : q = 1 := by omega
        exact hζ01
      · by_cases hpos : 0 < p
        · exact (CupSpec.isZero_chains (cech f) p hpos).eq_of_src _ _
        · exact (hneg q (by omega)).eq_of_tgt _ _

end GlobalTheory.EtC.LerayOne
end
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredSections

variable {R : Type} [CommRing R]

lemma etale_of_isPushout {A B C P : CommRingCat.{0}} {g : A ⟶ B} {f : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (sq : IsPushout g f inl inr) (hg : g.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.Etale) sq.flip hg

lemma cover_of_isPushout {ι : Type} {A C : CommRingCat.{0}} {B P : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (f : A ⟶ C) (inl : ∀ i, B i ⟶ P i) (inr : ∀ i, C ⟶ P i)
    (sq : ∀ i, IsPushout (g i) f (inl i) (inr i))
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) :
    ∀ p : Spec C, ∃ i v, Spec.map (inr i) v = p := by
  intro p
  obtain ⟨i, v, hv⟩ := hcov (Spec.map f p)
  obtain ⟨z, hz⟩ := GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (sq i).flip p v hv.symm
  exact ⟨i, z, hz⟩

lemma eq_zero_of_cover (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {B : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) (y : (onRings F).obj A)
    (hy : ∀ i, ((onRings F).map (g i)).hom y = 0) : y = 0 :=
  (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (B i)) (fun i => Spec.map (g i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (hg i)) hcov).1 y hy

lemma map_eta {M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)} {F : Shv R}
    (η : M ⟶ onRings F) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : M.obj A) :
    ((onRings F).map f).hom ((η.app A).hom x) = (η.app B).hom ((M.map f).hom x) := by
  change (η.app A ≫ (onRings F).map f).hom x = (M.map f ≫ η.app B).hom x
  rw [η.naturality]

lemma stage_of_pieces (F : Shv R) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (j : J) (y : (onRings F).obj (D.obj j)) {ι : Type} [Finite ι]
    (B : ι → CommRingCat.{0}) (g : ∀ i, D.obj j ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g i) v = p)
    (D' : ι → (Under j ⥤ CommRingCat.{0})) (u : ∀ i, Under.forget j ⋙ D ⟶ D' i)
    (v : ∀ i, (Functor.const _).obj (B i) ⟶ D' i)
    (sq : ∀ i (k : Under j), IsPushout (g i) (D.map k.hom) ((v i).app k) ((u i).app k))
    (hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  classical
  choose k hk using hk
  letI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  have e : ∀ i, k i ⟶ K := fun i => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  refine ⟨K.right, K.hom, ?_⟩
  apply eq_zero_of_cover F (fun i => (u i).app K) (fun i => etale_of_isPushout (sq i K) (hg i))
    (cover_of_isPushout g (D.map K.hom) (fun i => (v i).app K) (fun i => (u i).app K)
      (fun i => sq i K) hcov)
  intro i
  have h1 : (v i).app (k i) ≫ (D' i).map (e i) = (v i).app K := by
    simpa using ((v i).naturality (e i)).symm
  have h2 : D.map K.hom ≫ (u i).app K = g i ≫ (v i).app K := (sq i K).w.symm
  have h3 : ((onRings F).map ((u i).app K)).hom (((onRings F).map (D.map K.hom)).hom y) =
      ((onRings F).map ((D' i).map (e i))).hom
        (((onRings F).map ((v i).app (k i))).hom (((onRings F).map (g i)).hom y)) := by
    have := congrArg (fun φ => ((onRings F).map φ).hom y) h2
    rw [← h1] at this
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  rw [h3, hk i, map_zero]

lemma stage_of_eta (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R)
    (η : M ⟶ onRings F) (hM : PreservesFilteredColimitsOfSize.{0, 0} M)
    (hker : ∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι)
      (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧
      (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0)
    (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (j : J) (m : M.obj (D.obj j))
    (hm : ((onRings F).map (c.ι.app j)).hom ((η.app _).hom m) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom ((η.app _).hom m) = 0 := by
  have hMel := (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ M).2.1 hM
  rw [map_eta] at hm
  obtain ⟨ι, _, B, g, hg, hcov, hz⟩ := hker _ _ hm
  obtain ⟨j', f0, B', g', h, hsq, hcov'⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc ι B g hg hcov j
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j' (B' i) (B i) (g' i) (h i) (g i)
      (hsq i).2
  have hk : ∀ i, ∃ k : Under j', ((onRings F).map ((v i).app k)).hom
      (((onRings F).map (g' i)).hom ((η.app _).hom ((M.map (D.map f0)).hom m))) = 0 := by
    intro i
    let k0 : Under j' := Under.mk (𝟙 j')
    have e1 : D.map f0 ≫ g' i ≫ (v i).app k0 ≫ (ιB i).app k0 = c.ι.app j ≫ g i := by
      rw [(hpush i k0).2.1, (hsq i).2.w, ← Category.assoc, c.w]
    have hdie : (M.map ((ιB i).app k0)).hom ((M.map ((v i).app k0)).hom
        ((M.map (g' i)).hom ((M.map (D.map f0)).hom m))) = 0 := by
      have := congrArg (fun φ => (M.map φ).hom m) e1
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this]
      exact hz i
    obtain ⟨k, f, hf⟩ := (hMel (Under j') (D' i) _ (hcol i).some).2 k0 _ hdie
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [map_eta]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hf,
      map_zero]
  obtain ⟨k, f, hf⟩ := stage_of_pieces F D j' ((η.app _).hom ((M.map (D.map f0)).hom m)) B' g'
    (fun i => (hsq i).1) hcov' D' u v (fun i k => (hpush i k).1) hk
  refine ⟨k, f0 ≫ f, ?_⟩
  rw [map_eta] at hf ⊢
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hf

theorem eq_zero_at_stage_of_map_colimit_eq_zero : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  intro R _ M F η hM hloc hker J _ _ D c hc j y hy
  obtain ⟨ι, _, B, g, m, hg, hcov, hm⟩ := hloc _ y
  have hP : ∀ i, IsPushout (g i) (c.ι.app j) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) := fun i => IsPushout.of_hasPushout _ _
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j (B i)
      (pushout (g i) (c.ι.app j)) (g i) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) (hP i)
  have hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0 := by
    intro i
    let k0 : Under j := Under.mk (𝟙 j)
    have h0 : ((onRings F).map ((ιB i).app k0)).hom
        ((η.app _).hom ((M.map ((v i).app k0)).hom (m i))) = 0 := by
      calc ((onRings F).map ((ιB i).app k0)).hom ((η.app _).hom ((M.map ((v i).app k0)).hom (m i)))
          = (η.app _).hom ((M.map ((v i).app k0 ≫ (ιB i).app k0)).hom (m i)) := by
            rw [map_eta, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = ((onRings F).map (pushout.inl (g i) (c.ι.app j))).hom ((η.app _).hom (m i)) := by
            rw [(hpush i k0).2.1, map_eta]
            rfl
        _ = ((onRings F).map (g i ≫ pushout.inl (g i) (c.ι.app j))).hom y := by
            rw [hm i, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = 0 := by
            rw [pushout.condition, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hy,
              map_zero]
    obtain ⟨k, f, hf⟩ := stage_of_eta M F η hM hker (Under j) (D' i) _ (hcol i).some k0 _ h0
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [← hm i]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      ← map_eta]
    exact hf
  exact stage_of_pieces F D j y B g hg hcov D' u v (fun i k => (hpush i k).1) hk

end GlobalTheory.EtC.FilteredSections
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle :
    ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
      (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F),
      cobd (R := R) (E := cech f) (n := 1) s = 0 →
      ∀ x : H R (sch.obj X) F ((1 : ℕ) : ℤ),
        IsCls (R := R) (E := cech f) (n := 1) s (pull R (cechAug f) F ((1 : ℕ) : ℤ) x) →
        pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  intro R _ F Y X f s hs x hx
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc,
    cechDiag_δ, comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s :
      (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  obtain ⟨z, hzClass, hz⟩ := hx
  rw [← cechDiag_aug f, pull_comp, ← hzClass]
  simp only [pull, HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_zero]
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  change (Cochain.ofHom ((chains R).map (cechDiag f))).comp z.1 (zero_add _) = 0
  rw [hz, ClsBasic.ofHom_comp_single]
  simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
  simp [Category.assoc, hd]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) := by
  have : PreservesLimit (cospan f g) sch := by
    unfold sch; infer_instance
  exact h.map sch

theorem bc_cechAug_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S),
    ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U)
      (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U),
      e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  intro S W V r f U
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst f (pullback.fst r U.hom))
    (pullback.snd f (pullback.fst r U.hom)) f (pullback.fst r U.hom) (IsPullback.of_hasPullback _ _)
  have hQ := sch_isPullback (IsPullback.of_hasPullback r U.hom)
  have hP := hm.paste_vert hQ
  refine ⟨hP.isoPullback, hQ.isoPullback, ?_⟩
  apply pullback.hom_ext
  · simp only [bc, bcMap, Category.assoc, pullback.lift_fst, pullback.map]
    rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_fst]
    exact hm.w
  · simp only [bc, bcMap, Category.assoc, pullback.lift_snd, pullback.map, Category.comp_id]
    rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_sigmaDesc_of_isOpenImmersion {ι : Type} (V : Scheme.{0}) (Y : ι → Scheme.{0})
    (u : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (u i)] : Etale (Sigma.desc u) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

theorem etFF_preimage_of_etale_surjective (A B : CommRingCat.{0}) (k : Spec B ⟶ Spec A)
    [Etale k] [Surjective k] : EtFF (Spec.preimage k) := by
  rw [(GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.2.1 A B _), Spec.map_preimage]
  exact ⟨inferInstance, inferInstance⟩

theorem exists_etFF_of_isAffine (A : CommRingCat.{0}) (X V : Scheme.{0}) [IsAffine X]
    (h' : X ⟶ V) (f : V ⟶ Spec A) [Etale (h' ≫ f)] [Surjective (h' ≫ f)] :
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  have he : Etale (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  have hs : Surjective (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  refine ⟨Γ(X, ⊤), Spec.preimage (X.isoSpec.inv ≫ h' ≫ f), X.isoSpec.inv ≫ h',
    etFF_preimage_of_etale_surjective _ _ _, ?_⟩
  rw [Spec.map_preimage, Category.assoc]

theorem exists_etFF_refine_of_etale_surjective :
    ∀ (A : CommRingCat.{0}) (V : Scheme.{0}) (f : V ⟶ Spec A), Etale f → Surjective f →
      ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  intro A V f hf hs
  have hopen : ∀ x : V.affineCover.I₀, IsOpen (Set.range (V.affineCover.f x ≫ f)) := fun x =>
    (V.affineCover.f x ≫ f).isOpenMap.isOpen_range
  have hcov : Set.univ ⊆ ⋃ x : V.affineCover.I₀, Set.range (V.affineCover.f x ≫ f) := by
    intro y _
    obtain ⟨v, rfl⟩ := f.surjective y
    obtain ⟨x, hx⟩ := V.affineCover.covers v
    exact Set.mem_iUnion.mpr ⟨V.affineCover.idx v, ⟨_, by rw [Scheme.Hom.comp_apply, hx]⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  let Y : t → Scheme.{0} := fun i => V.affineCover.X i.1
  let u : ∀ i, Y i ⟶ V := fun i => V.affineCover.f i.1
  haveI : ∀ i, IsAffine (Y i) := fun i => inferInstanceAs (IsAffine (Spec _))
  haveI : ∀ i, IsOpenImmersion (u i) := fun i => inferInstanceAs (IsOpenImmersion (V.affineCover.f i.1))
  haveI : Etale (Sigma.desc u) := etale_sigmaDesc_of_isOpenImmersion V Y u
  have hcomp : Sigma.desc u ≫ f = Sigma.desc fun i => u i ≫ f := by
    ext i; simp
  haveI hsurj : Surjective (Sigma.desc u ≫ f) := by
    rw [hcomp]
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    refine Set.eq_univ_of_univ_subset (fun y hy => ?_)
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩
  exact exists_etFF_of_isAffine A (∐ Y) V (Sigma.desc u) f

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.complexCohomology_commutes_with_filteredColimits : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (exact GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (intros; apply GlobalTheory.EtC.ContFin.cohomology_filteredColimit  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  first | (exact @GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (exact GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (intros; apply GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType  <;> assumption)
end
