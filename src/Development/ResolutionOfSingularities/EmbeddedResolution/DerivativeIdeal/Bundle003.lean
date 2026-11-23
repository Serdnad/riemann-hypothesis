module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealLocalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle002
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem bijective_hom_of_iso {A B : CommRingCat.{u}} (i : A ≅ B) :
    Function.Bijective i.hom.hom :=
  ConcreteCategory.bijective_of_isIso i.hom

private theorem map_eq_comap_of_inverse {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (ψ : B →+* A) (h1 : ∀ a, ψ (φ a) = a) (h2 : ∀ b, φ (ψ b) = b) (J : Ideal A) :
    Ideal.map φ J = Ideal.comap ψ J := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, h1]
    exact ha
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have hmem := Ideal.mem_map_of_mem φ hx
    rwa [h2 x] at hmem

private theorem ideal_comap_eq_map_appLE {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (V : X.affineOpens) (hU : IsAffineOpen (f ''ᵁ (V : X.Opens)))
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens))) :
    (I.comap f).ideal V =
      (I.ideal ⟨f ''ᵁ (V : X.Opens), hU⟩).map
        (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I f V]
  have happ : f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e = (f.appIso (V : X.Opens)).hom :=
    (Scheme.Hom.appIso_hom' f (V : X.Opens)).symm
  rw [happ]
  have h1 : ∀ a, (f.appIso (V : X.Opens)).inv.hom ((f.appIso (V : X.Opens)).hom.hom a) = a :=
    fun a => CommRingCat.inv_hom_apply (f.appIso (V : X.Opens)) a
  have h2 : ∀ b, (f.appIso (V : X.Opens)).hom.hom ((f.appIso (V : X.Opens)).inv.hom b) = b :=
    fun b => CommRingCat.hom_inv_apply (f.appIso (V : X.Opens)) b
  exact (map_eq_comap_of_inverse _ _ h1 h2 _).symm

private theorem bijective_appLE_image_of_isOpenImmersion {Z W : Scheme.{u}} (f : W ⟶ Z) [IsOpenImmersion f]
    (V : W.Opens) (e : V ≤ f ⁻¹ᵁ (f ''ᵁ V)) :
    Function.Bijective (f.appLE (f ''ᵁ V) V e).hom := by
  have h : f.appLE (f ''ᵁ V) V e = (f.appIso V).hom := (Scheme.Hom.appIso_hom' f V).symm
  rw [h]
  exact bijective_hom_of_iso (f.appIso V)

private theorem appLE_sectionsAlgebraMap (K : Type u) [CommRing K] {Z W : Scheme.{u}}
    (q : Z ⟶ Spec (CommRingCat.of K)) (f : W ⟶ Z) (U : Z.Opens) (V : W.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (a : K) :
    (f.appLE U V e).hom (sectionsAlgebraMap K q U a) = sectionsAlgebraMap K (f ≫ q) V a := by
  have key : (f.appLE U V e).hom.comp (sectionsAlgebraMap K q U)
      = sectionsAlgebraMap K (f ≫ q) V := by
    rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  exact DFunLike.congr_fun key a

private theorem map_logDerivIdealIterate_of_bijective (K : Type u) [CommRing K]
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra K S] [Algebra K S']
    (φ : S →+* S') (hφ : Function.Bijective φ)
    (hcomp : ∀ a : K, φ (algebraMap K S a) = algebraMap K S' a)
    [Module.FinitePresentation S Ω[S⁄K]]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    Ideal.map φ (logDerivIdealIterate K P r J) =
      logDerivIdealIterate K (Ideal.map φ P) r (Ideal.map φ J) := by
  let _ : Algebra S S' := φ.toAlgebra
  have : IsScalarTower K S S' := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have : IsLocalization.Away (1 : S) S' :=
    IsLocalization.away_of_isUnit_of_bijective (hr := isUnit_one) (H := hφ)
  exact logDerivIdealIterate_map_away K (1 : S) hP r J

private theorem map_appLE_logDerivIdealIterate_of_bijective (K : Type u) [CommRing K] [IsNoetherianRing K]
    {Z W : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q]
    (f : W ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    (U : Z.affineOpens) (V : W.affineOpens) (e : (V : W.Opens) ≤ f ⁻¹ᵁ (U : Z.Opens))
    (hbij : Function.Bijective (f.appLE (U : Z.Opens) (V : W.Opens) e).hom)
    (P A : Ideal Γ(Z, (U : Z.Opens))) (r : ℕ) :
    Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom
        (@logDerivIdealIterate K _ _ _ (sectionsAlgebra K q (U : Z.Opens)) P r A) =
      @logDerivIdealIterate K _ _ _ (sectionsAlgebra K (f ≫ q) (V : W.Opens))
        (Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom P) r
        (Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom A) := by
  have hfp := @finitePresentation_kaehlerDifferential_sections K _ _ Z q _ U
    (sectionsAlgebra K q (U : Z.Opens)) (algebraMap_sectionsAlgebra K q (U : Z.Opens))
  have hno := @isNoetherianRing_sections K _ _ Z q _ U
    (sectionsAlgebra K q (U : Z.Opens)) (algebraMap_sectionsAlgebra K q (U : Z.Opens))
  have hP : P.FG := IsNoetherian.noetherian P
  have hcomp : ∀ a : K, (f.appLE (U : Z.Opens) (V : W.Opens) e).hom
      (@algebraMap K Γ(Z, (U : Z.Opens)) _ _ (sectionsAlgebra K q (U : Z.Opens)) a) =
      @algebraMap K Γ(W, (V : W.Opens)) _ _ (sectionsAlgebra K (f ≫ q) (V : W.Opens)) a := by
    intro a
    rw [algebraMap_sectionsAlgebra, algebraMap_sectionsAlgebra]
    exact appLE_sectionsAlgebraMap K q f (U : Z.Opens) (V : W.Opens) e a
  exact @map_logDerivIdealIterate_of_bijective K _ Γ(Z, (U : Z.Opens)) Γ(W, (V : W.Opens)) _ _
    (sectionsAlgebra K q (U : Z.Opens)) (sectionsAlgebra K (f ≫ q) (V : W.Opens))
    (f.appLE (U : Z.Opens) (V : W.Opens) e).hom hbij hcomp hfp P hP r A

variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
  (g : Y ⟶ X) [IsOpenImmersion g] [LocallyOfFiniteType (g ≫ p)]

theorem logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion
    (P A : X.IdealSheafData) (r : ℕ) (V : Y.affineOpens) :
    ((logDerivIdealSheafIterate k p P r A).comap g).ideal V =
      (logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g)).ideal V := by
  have hU : IsAffineOpen (g ''ᵁ (V : Y.Opens)) := V.2.image_of_isOpenImmersion g
  have e : (V : Y.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : Y.Opens)) := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hbij : Function.Bijective
      (g.appLE (g ''ᵁ (V : Y.Opens)) (V : Y.Opens) e).hom :=
    bijective_appLE_image_of_isOpenImmersion g (V : Y.Opens) e
  rw [ideal_comap_eq_map_appLE _ g V hU e, logDerivIdealSheafIterate_ideal,
    logDerivIdealSheafIterate_ideal, ideal_comap_eq_map_appLE P g V hU e,
    ideal_comap_eq_map_appLE A g V hU e]
  exact map_appLE_logDerivIdealIterate_of_bijective k p g ⟨g ''ᵁ (V : Y.Opens), hU⟩ V e hbij _ _ r

theorem logDerivIdealSheafIterate_comap_of_isOpenImmersion
    (P A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p P r A).comap g =
      logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g) :=
  Scheme.IdealSheafData.ext
    (funext fun V => logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion k p g P A r V)

end FunctorialResolution.EmbeddedResolution
end

section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem comp_app_apply {X Y Z : Scheme.{u}} (u : X ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) : ((u ≫ q).app U).hom a = (u.app (q ⁻¹ᵁ U)).hom ((q.app U).hom a) := by
  have h : (u ≫ q).app U = q.app U ≫ u.app (q ⁻¹ᵁ U) := Scheme.Hom.comp_app u q U
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a

private theorem comap_le_of_map_ideal_le {S X : Scheme.{u}} (ι : S ⟶ X) [IsAffineHom ι]
    (L : X.IdealSheafData) (D : S.IdealSheafData)
    (h : ∀ U : X.affineOpens, Ideal.map (ι.app (U : X.Opens)).hom (L.ideal U)
        ≤ D.ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩) :
    L.comap ι ≤ D := by
  have key : ∀ (U : X.affineOpens), L.ideal U
      ≤ RingHom.ker ((D.subschemeι ≫ ι).app (U : X.Opens)).hom := by
    intro U a ha
    have h1 := h U (Ideal.mem_map_of_mem _ ha)
    have h2 : (Scheme.Hom.ker D.subschemeι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩
        = RingHom.ker (D.subschemeι.app (ι ⁻¹ᵁ (U : X.Opens))).hom := by
      rw [Scheme.Hom.ker_apply]
    rw [Scheme.IdealSheafData.ker_subschemeι] at h2
    rw [h2] at h1
    refine RingHom.mem_ker.mpr ?_
    rw [comp_app_apply]
    exact RingHom.mem_ker.mp h1
  have hle : L ≤ Scheme.Hom.ker (D.subschemeι ≫ ι) := by
    unfold Scheme.Hom.ker
    exact Scheme.IdealSheafData.le_ofIdeals_iff.mpr key
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
  exact hle

private theorem derivIdealIterate_mono_of_le (k : Type u) [CommRing k] {T : Type u} [CommRing T]
    [Algebra k T] (r : ℕ) {I J : Ideal T} (h : I ≤ J) :
    derivIdealIterate k r I ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact h
  | succ r ih =>
      rw [derivIdealIterate_succ, derivIdealIterate_succ]
      exact derivIdeal_mono k ih

private theorem app_comp_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) :
    (ι.app U).hom.comp (sectionsAlgebraMap k p U) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) := by
  have happ : ι.appLE U (ι ⁻¹ᵁ U) le_rfl = ι.app U := Scheme.Hom.appLE_eq_app ι
  have hc : p.appLE ⊤ U (le_preimage_top k p U) ≫ ι.appLE U (ι ⁻¹ᵁ U) le_rfl
      = (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) :=
    Scheme.Hom.appLE_comp_appLE ι p ⊤ U (ι ⁻¹ᵁ U) (le_preimage_top k p U) le_rfl
  have hmor : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U))
        ≫ ι.app U
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ≫ (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) := by
    rw [Category.assoc, ← happ, hc]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k (ι ≫ p) (ι ⁻¹ᵁ U)]
  exact congrArg CommRingCat.Hom.hom hmor

private theorem app_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) (a : k) :
    (ι.app U).hom (sectionsAlgebraMap k p U a) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) a :=
  DFunLike.congr_fun (app_comp_sectionsAlgebraMap k p ι U) a

private theorem map_logDerivIdealSheafIterate_ideal_le
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) (U : X.affineOpens) :
    Ideal.map (ι.app (U : X.Opens)).hom ((logDerivIdealSheafIterate k p ι.ker r A).ideal U)
      ≤ (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι)).ideal
          ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
  have hcomm : ∀ a : k,
      (ι.app (U : X.Opens)).hom
          (@algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens)) a)
        = @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) a := by
    intro a
    have e1 : @algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens))
        = sectionsAlgebraMap k p (U : X.Opens) :=
      algebraMap_sectionsAlgebra k p (U : X.Opens)
    have e2 : @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
        = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)) :=
      algebraMap_sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))
    rw [e1, e2]
    exact app_sectionsAlgebraMap k p ι (U : X.Opens) a
  have hmapLE : ∀ (V : S.affineOpens) (e : (V : S.Opens) ≤ ι ⁻¹ᵁ (U : X.Opens)),
      Ideal.map (ι.appLE (U : X.Opens) (V : S.Opens) e).hom (A.ideal U)
        ≤ (A.comap ι).ideal V := by
    intro V e
    apply Scheme.IdealSheafData.map_appLE_le_comap_ideal
  have hmap : Ideal.map (ι.app (U : X.Opens)).hom (A.ideal U)
      ≤ (A.comap ι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
    rw [Scheme.Hom.app_eq_appLE]
    exact hmapLE ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ le_rfl
  have halg := @map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker k _ _ _ _ _
      (sectionsAlgebra k p (U : X.Opens))
      (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
      (@AlgHom.mk k _ _ _ _ _ (sectionsAlgebra k p (U : X.Opens))
        (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) (ι.app (U : X.Opens)).hom hcomm)
      (Scheme.Hom.app_surjective ι (U : X.Opens) U.2) _ rfl r (A.ideal U)
  rw [logDerivIdealSheafIterate_ideal, Scheme.Hom.ker_apply, derivIdealSheafIterate_ideal]
  refine le_trans halg ?_
  exact @derivIdealIterate_mono_of_le k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) r _ _
    hmap

private theorem logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  comap_le_of_map_ideal_le ι (logDerivIdealSheafIterate k p ι.ker r A)
    (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι))
    (map_logDerivIdealSheafIterate_ideal_le k p ι A r)

theorem comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate k p ι A r

end FunctorialResolution.EmbeddedResolution
end
