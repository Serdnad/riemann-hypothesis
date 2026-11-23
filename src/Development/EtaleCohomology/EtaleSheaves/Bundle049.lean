module

public import Development.EtaleCohomology.EtaleSheaves.Bundle031
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.EtaleCohomology.EtaleSheaves.Bundle033
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Development.EtaleCohomology.EtaleSheaves.Bundle034
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.Bundle035
public import Development.EtaleCohomology.EtaleSheaves.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.EtaleCohomology.EtaleSheaves.Bundle008

@[expose] public section

section

noncomputable section
open Polynomial IntermediateField

namespace LateralTheory.E.LeafBaseChangeFieldPf

def ratMap (F G : Type) [Field F] [Field G] [Algebra F G] : RatFunc F →+* RatFunc G :=
  RatFunc.liftRingHom ((algebraMap G[X] (RatFunc G)).comp (Polynomial.mapRingHom (algebraMap F G))) (show
      nonZeroDivisors F[X] ≤ Submonoid.comap ((algebraMap G[X] (RatFunc G)).comp
        (Polynomial.mapRingHom (algebraMap F G))) (nonZeroDivisors (RatFunc G)) from by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom]
    intro h
    apply hp0
    have h1 := RatFunc.algebraMap_injective G (h.trans (map_zero _).symm)
    exact (Polynomial.map_eq_zero_iff (algebraMap F G).injective).1 h1)

lemma ratMap_algebraMap (F G : Type) [Field F] [Field G] [Algebra F G] (f : F) :
    ratMap F G (algebraMap F (RatFunc F) f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
  have e1 : algebraMap F (RatFunc F) f = algebraMap F[X] (RatFunc F) (C f) / algebraMap F[X] (RatFunc F) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [e1, ratMap, RatFunc.liftRingHom_apply_div]
  simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

lemma mem_adjoin_of_ratFunc {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] (x : RatFunc G) :
    algebraMap (RatFunc G) L x ∈ G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := by
  have key : ∀ p : G[X], algebraMap (RatFunc G) L (algebraMap G[X] (RatFunc G) p) =
      aeval (algebraMap (RatFunc G) L RatFunc.X) p := by
    intro p
    rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]
  rw [← RatFunc.num_div_denom x, map_div₀, key, key]
  exact div_mem (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))
    (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))

lemma transc_X_image {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] : Transcendental G (algebraMap (RatFunc G) L RatFunc.X) := by
  rw [transcendental_iff_injective]
  intro p q h
  rw [aeval_algebraMap_apply, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
    RatFunc.aeval_X_left_eq_algebraMap] at h
  exact RatFunc.algebraMap_injective G ((algebraMap (RatFunc G) L).injective h)

lemma finite_over_adjoin {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] [Module.Finite (RatFunc G) L] :
    FiniteDimensional G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L := by
  let c : RatFunc G →+* G⟮algebraMap (RatFunc G) L RatFunc.X⟯ :=
    (algebraMap (RatFunc G) L).codRestrict _ mem_adjoin_of_ratFunc
  letI : Algebra (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := c.toAlgebra
  haveI : IsScalarTower (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Module.Finite.of_restrictScalars_finite (RatFunc G) _ L

end LateralTheory.E.LeafBaseChangeFieldPf

open LateralTheory.E.LeafBaseChangeFieldPf in
theorem LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField := by
  intro F G K _ _ _ _ _ t ht hfin
  let e := RatFunc.algEquivOfTranscendental t ht
  let h : F⟮t⟯ →+* RatFunc G := (ratMap F G).comp e.symm.toRingHom
  letI : Algebra F⟮t⟯ (RatFunc G) := h.toAlgebra
  haveI : Nontrivial (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ h.injective
      (algebraMap F⟮t⟯ K).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct F⟮t⟯ (RatFunc G) K)
  letI : Field (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Module.Finite.base_change F⟮t⟯ (RatFunc G) K
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (RatFunc G) M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : IsScalarTower G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := inferInstance
  refine ⟨TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M, inferInstance, inferInstance,
    algebraMap (RatFunc G) _ RatFunc.X,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := F⟮t⟯) (A := RatFunc G) (B := K)).toRingHom,
    transc_X_image, finite_over_adjoin, ?_⟩
  ext f
  have h1 : h (algebraMap F F⟮t⟯ f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
    show ratMap F G (e.symm (algebraMap F F⟮t⟯ f)) = _
    rw [AlgEquiv.commutes]
    exact ratMap_algebraMap F G f
  rw [RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply F F⟮t⟯ K, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes, IsScalarTower.algebraMap_apply F⟮t⟯ (RatFunc G)]
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M), ← h1]
  rfl
end
end

section

noncomputable section
open CategoryTheory Limits Pretriangulated Triangulated

namespace LateralTheory.E.LeafTruncPf

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

lemma mono_H_ι (Y : DerivedCategory C) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) Y
  have := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (n - 1) n (by lia)).2
    (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE _ (n + 1) (n - 1) (by lia)) _ _)
  exact this

lemma epi_H_π (X : DerivedCategory C) (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished n X
  have := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT n (n + 1) (by lia)).2
    (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isLE _ (n - 1) (n + 1) (by lia)) _ _)
  exact this

lemma lift_LT {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : φ ≫ (DerivedCategory.TStructure.t.truncGEπ n).app Y = 0) :
    ∃ ψ : X ⟶ (DerivedCategory.TStructure.t.truncLT n).obj Y,
      φ = ψ ≫ (DerivedCategory.TStructure.t.truncLTι n).app Y :=
  Triangle.coyoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n Y) φ h

lemma desc_GE {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ φ = 0) :
    ∃ ψ : (DerivedCategory.TStructure.t.truncGE n).obj X ⟶ Y,
      φ = (DerivedCategory.TStructure.t.truncGEπ n).app X ≫ ψ :=
  Triangle.yoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n X) φ h

lemma heart_zero {X Y : DerivedCategory C} (n : ℤ) [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (χ : X ⟶ Y) (hχ : (DerivedCategory.homologyFunctor C n).map χ = 0) : χ = 0 := by
  obtain ⟨A, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨B, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor C n).map_surjective (eX.inv ≫ χ ≫ eY.hom)
  have ha0 : a = 0 := by
    have eq := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) a
    dsimp at eq
    rw [← eq, ha]
    simp [hχ]
  have : χ = eX.hom ≫ (eX.inv ≫ χ ≫ eY.hom) ≫ eY.inv := by simp
  rw [this, ← ha, ha0, Functor.map_zero]
  simp

lemma zero_of_H {X Y : DerivedCategory C} (n : ℤ) [X.IsLE n] [Y.IsGE n] (φ : X ⟶ Y)
    (hφ : (DerivedCategory.homologyFunctor C n).map φ = 0) : φ = 0 := by
  have h1 : φ ≫ (DerivedCategory.TStructure.t.truncGEπ (n + 1)).app Y = 0 :=
    DerivedCategory.TStructure.t.zero _ n (n + 1)
  obtain ⟨ψ, hψ⟩ := lift_LT (n + 1) φ h1
  have h2 : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ ψ = 0 :=
    DerivedCategory.TStructure.t.zero _ (n - 1) n
  obtain ⟨χ, hχ⟩ := desc_GE n ψ h2
  have hHχ : (DerivedCategory.homologyFunctor C n).map χ = 0 := by
    have := mono_H_ι Y n
    have := epi_H_π X n
    rw [hψ, hχ, Functor.map_comp, Functor.map_comp] at hφ
    rw [← cancel_epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)),
      ← cancel_mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y))]
    simpa using hφ
  have : χ = 0 := heart_zero n χ hHχ
  rw [hψ, hχ, this]
  simp

end LateralTheory.E.LeafTruncPf

open LateralTheory.E.LeafTruncPf in
theorem LateralTheory.E.LeafGhostRelCut.LeafTrunc_of : LateralTheory.E.LeafGhostRelCut.LeafTrunc := by
  intro A _ _ _ K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  have : K0.IsLE 2 := (DerivedCategory.isLE_iff K0 2).2 hK0
  have : K2.IsGE 0 := (DerivedCategory.isGE_iff K2 0).2 hK2
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 (fun i hi => hL i (by lia))
  have : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 2).obj K1) 1 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have hP : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 1).obj K2) 0 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have e1 : f ≫ (DerivedCategory.TStructure.t.truncGEπ 2).app K1 = 0 :=
    zero_of_H 2 _ (by simp [Functor.map_comp, hf])
  obtain ⟨f', hf'⟩ := lift_LT 2 f e1
  have e2 : ((DerivedCategory.TStructure.t.truncLTι 2).app K1 ≫ g) ≫
      (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    zero_of_H 1 _ (by simp [Functor.map_comp, hg])
  obtain ⟨w, hw⟩ := lift_LT 1 _ e2
  have e3 : ℓ ≫ (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    DerivedCategory.TStructure.t.zero _ 0 1
  obtain ⟨ℓ', hℓ'⟩ := lift_LT 1 ℓ e3
  have hiso : IsIso ℓ' := by
    rw [DerivedCategory.isIso_iff]
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · have hm0 := mono_H_ι K2 0
      rw [zero_add] at hm0
      have hc : IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ' ≫
          (DerivedCategory.homologyFunctor A 0).map
            ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := by
        rw [← Functor.map_comp, ← hℓ']; exact hℓ
      have : Epi ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) :=
        epi_of_epi ((DerivedCategory.homologyFunctor A 0).map ℓ') _
      have : IsIso ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := isIso_of_mono_of_epi _
      exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor A 0).map
        ((DerivedCategory.TStructure.t.truncLTι 1).app K2))
    · have hZ : IsZero ((DerivedCategory.homologyFunctor A m).obj
          ((DerivedCategory.TStructure.t.truncLT 1).obj K2)) := by
        rcases lt_or_gt_of_ne hm with h | h
        · exact DerivedCategory.isZero_of_isGE _ 0 m h
        · exact DerivedCategory.isZero_of_isLE _ 0 m h
      exact ⟨⟨0, (hL m hm).eq_of_src _ _, hZ.eq_of_src _ _⟩⟩
  refine ⟨f' ≫ w ≫ inv ℓ', ?_⟩
  rw [hf', hℓ']
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, hw]

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf2
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafPairExtPf LateralTheory.E.LeafTwPairExistsPf

def pre {R : Type} [CommRing R] {I' I J K : Cx R} (μ : Pair I J K) (f : I' ⟶ I) : Pair I' J K where
  mul U s t w h := (μ.mul U s t w h).comp ((f.f s).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (μ.mul _ s t w h (Sec.map (f.f s) a) b) = μ.mul _ s t w h (Sec.map (f.f s) (Sec.res g a)) (Sec.res g b)
    rw [μ.nat, res_map]
  leibniz U s t w h a b := by
    change Sec.map (K.d w (w + 1)) (μ.mul U s t w h (Sec.map (f.f s) a) b) =
      μ.mul U (s + 1) t (w + 1) _ (Sec.map (f.f (s + 1)) (Sec.map (I'.d s (s + 1)) a)) b +
      s.negOnePow • μ.mul U s (t + 1) (w + 1) _ (Sec.map (f.f s) a) (Sec.map (J.d t (t + 1)) b)
    rw [μ.leibniz, map_map, map_map, f.comm]

def LeafTensUP : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ μ : Pair I J K,
  ∃ u : T ⟶ K, ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (u.f w) (τ.mul U s t w h a b) = μ.mul U s t w h a b

def LeafExtTens : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ u : S ⟶ res _ (tw q i), ∃ g : T ⟶ res _ (tw q i), ι ≫ g = u

theorem LeafExtAlongAug_of (hup : LeafTensUP) (hext : LeafExtTens) : LeafExtAlongAug := by
  intro q _ i lam
  let σ := LateralTheory.E.LeafTwTensExPf.tau (sgl (tw q 0)) (res _ (tw q i))
  let τ := LateralTheory.E.LeafTwTensExPf.tau (res _ (tw q 0)) (res _ (tw q i))
  have hσ : σ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  have hτ : τ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  obtain ⟨u, hu⟩ := hup _ σ hσ lam
  obtain ⟨ι, hι⟩ := hup _ σ hσ (pre τ (resAug (tw q 0)))
  obtain ⟨g, hg⟩ := hext q i σ τ hσ hτ ι hι u
  refine ⟨post τ g, fun U t x b => ?_⟩
  have e : Sec.map (ι.f t) (σ.mul U 0 t t (zero_add t) x b) =
      τ.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b := hι U 0 t t (zero_add t) x b
  rw [post_mul, ← e, map_map, ← HomologicalComplex.comp_f, hg, hu]

end LateralTheory.E.LeafPairExtPf2
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.inclPf

universe v u

set_option linter.dupNamespace false in
abbrev E (M : ℤ) := ComplexShape.embeddingUpIntGE M

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (M : ℤ)

lemma xiso_indep {i j : ℕ} {p : ℤ} (hi : (E M).f i = p) (hj : (E M).f j = p) :
    K.stupidTruncXIso (E M) hi = K.stupidTruncXIso (E M) hj := by
  obtain rfl : i = j := (E M).injective_f (hi.trans hj.symm)
  rfl

lemma trd (i j : ℕ) :
    (K.stupidTrunc (E M)).d ((E M).f i) ((E M).f j) ≫ (K.stupidTruncXIso (E M) (i := j) rfl).hom =
      (K.stupidTruncXIso (E M) (i := i) rfl).hom ≫ K.d ((E M).f i) ((E M).f j) := by
  simp only [HomologicalComplex.stupidTruncXIso_rfl, HomologicalComplex.stupidTrunc,
    (K.restriction (E M)).extend_d_eq (E M) (i := i) (j := j) rfl rfl,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.restriction_d]


open Classical in
def iotaf (p : ℤ) : (K.stupidTrunc (E M)).X p ⟶ K.X p :=
  if h : ∃ i, (E M).f i = p then (K.stupidTruncXIso (E M) h.choose_spec).hom else 0

lemma iotaf_eq (i : ℕ) : iotaf K M ((E M).f i) = (K.stupidTruncXIso (E M) (i := i) rfl).hom := by
  have h : ∃ j, (E M).f j = (E M).f i := ⟨i, rfl⟩
  rw [iotaf, dite_eq_left h, xiso_indep K M h.choose_spec rfl]

lemma stupidTruncation_GE_isZero_below_bound (p : ℤ) (hp : p < M) : IsZero ((K.stupidTrunc (E M)).X p) :=
  HomologicalComplex.isZero_stupidTrunc_X _ _ _ (fun i h => by simp [E] at h; omega)

lemma mem (p : ℤ) (hp : M ≤ p) : (E M).f (p - M).toNat = p := by simp [E]; omega

def iota : K.stupidTrunc (E M) ⟶ K where
  f := iotaf K M
  comm' p q hpq := by
    simp only [ComplexShape.up_Rel] at hpq
    by_cases hp : M ≤ p
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, (E M).f j = q := ⟨i + 1, by simp [E] at hpq ⊢; omega⟩
      rw [iotaf_eq, iotaf_eq]
      exact (trd K M i j).symm
    · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _

lemma iota_iso (p : ℤ) (hp : M ≤ p) : IsIso ((iota K M).f p) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
  show IsIso (iotaf K M _)
  rw [iotaf_eq]; infer_instance

lemma iota_nat {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (E M) ≫ iota L M = iota K M ≫ g := by
  ext p
  simp only [HomologicalComplex.comp_f]
  by_cases hp : M ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
    show _ ≫ iotaf L M _ = iotaf K M _ ≫ _
    rw [iotaf_eq, iotaf_eq]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom _ _ rfl
  · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _
end

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {A B I : CochainComplex C ℤ} (φ : A ⟶ B) (M : ℤ)

def P (m : ℤ) (c : Cochain B I m) : Cochain A I m := (Cochain.ofHom φ).comp c (zero_add m)

lemma precomp_injective [I.IsStrictlyGE 0] (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (m : ℤ) (hm : m + M ≤ 0) :
    Function.Injective (P (I := I) φ m) := by
  intro c c' h
  ext p q hpq
  by_cases hp : M ≤ p
  · have := hiso p hp
    have h' := congrArg (fun x : Cochain A I m => x.v p q hpq) h
    simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h'
    exact (cancel_epi _).1 h'
  · exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _

lemma precomp_surjective₂ (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (hz : ∀ p, p < M → IsZero (A.X p)) (m : ℤ) :
    Function.Surjective (P (I := I) φ m) := by
  intro d
  refine ⟨Cochain.mk (fun p q hpq => if h : M ≤ p then (haveI := hiso p h; inv (φ.f p)) ≫ d.v p q hpq else 0), ?_⟩
  ext p q hpq
  simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  by_cases hp : M ≤ p
  · rw [dite_eq_left hp]; simp
  · exact (hz p (by omega)).eq_of_src _ _
end

section
variable {R : Type} [CommRing R] {A B I : Cx R} (φ : A ⟶ B)

lemma cpull_mk (n : ℤ) (z : Cocycle B I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (Cocycle.mk (P φ n z) (n + 1) rfl
      (by simp [P, Cocycle.δ_eq_zero])) := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1

lemma cpull_bij [I.IsStrictlyGE 0] (M : ℤ) (hiso : ∀ p, M ≤ p → IsIso (φ.f p))
    (hz : ∀ p, p < M → IsZero (A.X p)) (n : ℤ) (hn : n + 1 + M ≤ 0) :
    Function.Bijective (cpull φ I n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := precomp_surjective₂ φ M hiso hz (n - 1) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨β', precomp_injective φ M hiso n (by omega) ?_⟩
    rw [Cocycle.mk_coe] at hβ
    rw [← hβ, P, P, δ_ofHom_comp]
  · intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨c, hc⟩ := precomp_surjective₂ φ M hiso hz n (z : Cochain A I n)
    have hδ : δ n (n + 1) c = 0 := by
      apply precomp_injective φ M hiso (n + 1) (by omega)
      have : P φ (n + 1) (δ n (n + 1) c) = δ n (n + 1) (P φ n c) := by simp [P]
      rw [this, hc, Cocycle.δ_eq_zero]; simp [P]
    refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl hδ), ?_⟩
    rw [cpull_mk]
    congr 1
    apply Cocycle.ext
    simp only [Cocycle.mk_coe]
    exact hc
end

theorem incl_of : LateralTheory.E.stupidPf.incl := by
  intro R _ I _ K L g N
  refine ⟨iota K (-(N : ℤ)), iota L (-(N : ℤ)), iota_nat _ g, fun n hn => ⟨?_, ?_⟩⟩
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso K _) (stupidTruncation_GE_isZero_below_bound K _) n (by omega)
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso L _) (stupidTruncation_GE_isZero_below_bound L _) n (by omega)

end LateralTheory.E.inclPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.CompCut

def LocAC : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ q : PrimeSpectrum W,
  IsField (Localization.AtPrime q.asIdeal) ∧ AIC (Localization.AtPrime q.asIdeal)

def NormAC : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (K : Type) [CommRing K], IsField K → AIC K → ∀ v : Spec (CommRingCat.of K) ⟶ P,
  AICSch v.normalization

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D)
      (ι : ∀ j, D.obj j ⟶ w.normalization), ClopenSys y D c ι ∧
      Nonempty (c.pt ≅ (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization)

theorem goal_of (hS : Sys) (hL : LocAC) (hN : NormAC) : Comp := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, c, ι, hc, ⟨e⟩⟩ := hS W w hW y
  obtain ⟨hF, hA⟩ := hL W hW q
  refine ⟨J, inferInstance, inferInstance, D, c.extend e.inv, ι, ⟨⟨IsLimit.ofIsoLimit hc.1.some (Cone.extendIso c e)⟩,
    hc.2.1, hc.2.2⟩, ?_⟩
  exact hN _ hF hA _

end LateralTheory.E.CompCut
end
end
