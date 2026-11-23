module

public import Development.EtaleCohomology.EtaleSheaves.Bundle076
public import Development.EtaleCohomology.EtaleSheaves.Bundle052
public import Development.EtaleCohomology.EtaleSheaves.Bundle077
public import Development.EtaleCohomology.EtaleSheaves.Bundle080
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
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.SysFMPfAlg

namespace LateralTheory.E.SysFMPfSys

def IdemSec : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), Function.Injective (phi w) ∧ ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

theorem basicOpen_one_sub {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) (x : X) :
    x ∉ X.basicOpen s ↔ x ∈ X.basicOpen (1 - s) := by
  simp only [Scheme.mem_basicOpen_top, map_sub, map_one]
  have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
  constructor
  · intro h
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
  · intro h h'
    have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self]
    exact not_isUnit_zero (hz ▸ h'.mul h)

theorem Sys_of (hI : IdemSec) : Sys := by
  intro P _ _ W _ w hW y
  obtain ⟨hinj, hrg⟩ := hI W w
  have hid : ∀ s, IsIdempotentElem (phi w s) → IsIdempotentElem s := fun s h =>
    hinj (by rw [map_mul]; exact h.eq)
  let F : Set W := {e | IsIdempotentElem e ∧ ∃ s, phi w s = e ∧ y ∈ w.normalization.basicOpen s}
  have hF0 : (0 : W) ∉ F := by
    rintro ⟨-, s, hs, hy⟩
    have : s = 0 := hinj (by rw [hs, map_zero])
    subst this
    simp at hy
  have hFu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F := by
    intro e he
    obtain ⟨s, rfl⟩ := hrg e he
    by_cases hy : y ∈ w.normalization.basicOpen s
    · exact Or.inl ⟨he, s, rfl, hy⟩
    · exact Or.inr ⟨he.one_sub, 1 - s, by rw [map_sub, map_one], (basicOpen_one_sub (hid s he) y).1 hy⟩
  have hFm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F := by
    rintro e ⟨he, s, rfl, hs⟩ f ⟨hf, t, rfl, ht⟩
    exact ⟨he.mul hf, s * t, map_mul _ _ _, by rw [Scheme.basicOpen_mul]; exact ⟨hs, ht⟩⟩
  obtain ⟨q, hq⟩ := prime_of_filter hW F (fun e h => h.1) hF0 hFu hFm
  let J : Type := {s : Γ(w.normalization, ⊤) // IsIdempotentElem (phi w s) ∧ phi w s ∉ q.asIdeal}
  letI : Preorder J := Preorder.lift (fun s : J => w.normalization.basicOpen s.1)
  have hmono : Monotone (fun s : J => w.normalization.basicOpen s.1) := fun _ _ h => h
  have hne : Nonempty J := ⟨⟨1, by rw [map_one]; exact IsIdempotentElem.one, by rw [map_one]; exact (Ideal.ne_top_iff_one _).1 q.2.ne_top⟩⟩
  haveI : IsCodirectedOrder J := by
    refine ⟨?_⟩
    rintro ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩
    refine ⟨⟨s * t, by rw [map_mul]; exact hs1.mul ht1, by rw [map_mul]; exact q.2.mul_notMem hs2 ht2⟩, ?_, ?_⟩
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen s
      rw [Scheme.basicOpen_mul]; exact inf_le_left
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen t
      rw [Scheme.basicOpen_mul]; exact inf_le_right
  haveI : IsCofiltered J := { nonempty := hne }
  let D : J ⥤ Scheme.{0} := hmono.functor ⋙ w.normalization.restrictFunctor ⋙ Over.forget _
  have hDι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ (w.normalization.basicOpen k.1).ι = (w.normalization.basicOpen j.1).ι :=
    fun f => Over.w (w.normalization.restrictFunctor.map (hmono.functor.map f))
  let ι : ∀ j : J, D.obj j ⟶ w.normalization := fun j => (w.normalization.basicOpen j.1).ι
  have hr : ∀ j : J, Set.range (ι j) = (w.normalization.basicOpen j.1 : Set w.normalization) := fun j =>
    Scheme.Opens.range_ι _
  refine ⟨q, J, inferInstance, inferInstance, D, ι, fun j => ⟨show IsOpenImmersion (w.normalization.basicOpen j.1).ι from
    inferInstance, isClosedImmersion_basicOpen_idem (hid _ j.2.1), ?_⟩, fun {j k} f => ⟨hDι f, ?_⟩, ?_⟩
  · rw [hr]
    obtain ⟨-, s, hs, hy⟩ := (hq _ j.2.1).1 j.2.2
    rwa [hinj hs] at hy
  · have hk : IsClosedImmersion (ι k) := isClosedImmersion_basicOpen_idem (hid _ k.2.1)
    have hc : IsClosedImmersion (D.map f ≫ ι k) := by
      rw [hDι f]; exact isClosedImmersion_basicOpen_idem (hid _ j.2.1)
    have := @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (D.map f) (ι k) hk hc
    infer_instance
  · ext x
    simp only [Set.mem_iInter, hr, RR, Set.mem_setOf_eq, SetLike.mem_coe]
    exact ⟨fun h s h1 h2 => h ⟨s, h1, h2⟩, fun h j => h j.1 j.2.1 j.2.2⟩

theorem SysFM_of (hI : IdemSec) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM :=
  LateralTheory.E.SysFMPf.SysFM_of (Sys_of hI) hE hR

end LateralTheory.E.SysFMPfSys
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

set_option backward.isDefEq.respectTransparency false in
theorem sep_of_cover {X S : Scheme.{0}} (f : X ⟶ S) (U : X.OpenCover)
    (H : ∀ i j, IsClosedImmersion (pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f
      (by simp) (by simp))) : IsSeparated f := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight U U f f)
  rintro ⟨i, j⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv]
  have e : (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv ≫
      (Scheme.Pullback.openCoverOfLeftRight U U f f).pullbackHom (pullback.diagonal f) (i, j) =
      pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp only [Scheme.Cover.pullbackHom, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
    · exact pullbackDiagonalMapIdIso_inv_snd_fst (U.f i) (U.f j) f
    · exact pullbackDiagonalMapIdIso_inv_snd_snd (U.f i) (U.f j) f
  rw [e]; exact H i j

theorem closed_of_pb {X S W P Q : Scheme.{0}} (f : X ⟶ S) (ia : P ⟶ X) (ib : Q ⟶ X) (pa : W ⟶ P)
    (pb : W ⟶ Q) (hp : IsPullback pa pb ia ib) (ga : P ⟶ S) (gb : Q ⟶ S) (hga : ia ≫ f = ga)
    (hgb : ib ≫ f = gb) (w : pa ≫ ga = pb ≫ gb)
    (hc : IsClosedImmersion (pullback.lift pa pb w)) :
    IsClosedImmersion (pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp)) := by
  subst hga hgb
  have e : pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift pa pb w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_inv_snd]
  rw [e]; infer_instance

def LeafGluePullback : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsPullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)).toRingHom))
    G.iA G.iB

theorem spec_w {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L) (hA : A ≤ D) (hB : B ≤ D) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hA).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]; congr 1

def LeafSpecGenClosed : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
  (hA : A ≤ D) (hB : B ≤ D), D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) →
  IsClosedImmersion (pullback.lift _ _ (spec_w A B D hA hB))

theorem dr_le {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) (hu : u⁻¹ ∈ B) :
    Dr Ω A u ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr hu))

theorem LeafGlueSep_of (hP : LeafGluePullback) (hC : LeafSpecGenClosed) :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hD := dr_le A B u h.2.2.1
  apply sep_of_cover G.c0 (LateralTheory.E.LeafGlueIsProperPf.cov G)
  intro i j
  cases i <;> cases j
  · exact closed_of_pb G.c0 G.iB G.iB (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iB) _ _ G.hcB G.hcB (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω B))))))
  · exact closed_of_pb G.c0 G.iB G.iA _ _ (hP Ω L A B u h G).flip _ _ G.hcB G.hcA _
      (hC Ω L B A _ _ _ (by rw [Set.union_comm]; exact hD))
  · exact closed_of_pb G.c0 G.iA G.iB _ _ (hP Ω L A B u h G) _ _ G.hcA G.hcB _ (hC Ω L A B _ _ _ hD)
  · exact closed_of_pb G.c0 G.iA G.iA (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iA) _ _ G.hcA G.hcA (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω A))))))

end LateralTheory.E.GluedCurveChartOverlaps
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSysPf
open LateralTheory.E.E4 LateralTheory.E.LeafVanBStalkPf

def Cof {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (ω : c.pt →+* Ω),
    ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ

theorem unit_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) {Ω : Type} [Field Ω] (ω : c.pt →+* Ω)
    (H : ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ)
    (a : c.pt) (ha : ω a ≠ 0) : IsUnit a := by
  obtain ⟨j, f, rfl⟩ := Limits.Concrete.isColimit_exists_rep D hc a
  have hu : IsUnit (ω ((c.ι.app j).hom f)) := isUnit_iff_ne_zero.2 ha
  have : Algebra.Etale (D.obj j) (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  obtain ⟨j', g, φ, h1, -⟩ := H j (Localization.Away f) inferInstance inferInstance this
    (IsLocalization.Away.lift f (g := ω.comp (c.ι.app j).hom) hu) (IsLocalization.Away.lift_comp f hu)
  have e1 : (c.ι.app j).hom f = (c.ι.app j').hom ((D.map g).hom f) := by
    rw [← CommRingCat.comp_apply, c.w g]
  rw [e1, ← h1, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit f).map ((c.ι.app j').hom.comp φ)

theorem isLocalRing_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (hC : Cof D c) : IsLocalRing c.pt := by
  obtain ⟨Ω, _, _, ω, H⟩ := hC
  have key : ∀ a : c.pt, a ∈ nonunits c.pt → ω a = 0 := fun a ha => by
    by_contra h; exact ha (unit_of_cof D c hc ω H a h)
  have : Nontrivial c.pt := ω.domain_nontrivial
  refine IsLocalRing.of_nonunits_add (fun a b ha hb hab => ?_)
  have := hab.map ω
  rw [map_add (f := _), key a ha, key b hb, add_zero] at this
  exact not_isUnit_zero this

open Polynomial in
theorem poly_rep {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (p : c.pt[X]) : ∃ (j : J) (P : (D.obj j)[X]), P.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨j1, P1, rfl⟩ := hp
    obtain ⟨j2, P2, rfl⟩ := hq
    refine ⟨IsFiltered.max j1 j2, P1.map (D.map (IsFiltered.leftToMax j1 j2)).hom +
      P2.map (D.map (IsFiltered.rightToMax j1 j2)).hom, ?_⟩
    rw [Polynomial.map_add (f := _), Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w]
  | monomial n a =>
    obtain ⟨j, f, rfl⟩ := Limits.Concrete.isColimit_exists_rep D hc a
    exact ⟨j, monomial n f, by simp⟩

open Polynomial in
theorem monic_rep {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) [Nontrivial c.pt] (p : c.pt[X]) (hp : p.Monic) :
    ∃ (j : J) (P : (D.obj j)[X]), P.map (c.ι.app j).hom = p ∧ P.Monic := by
  obtain ⟨j, P, hP⟩ := poly_rep D c hc p
  haveI : Nontrivial (((Functor.const J).obj c.pt).obj j) := inferInstanceAs (Nontrivial c.pt)
  obtain ⟨Q, hQ, -, hm⟩ := lifts_and_degree_eq_and_monic (f := (c.ι.app j).hom) ⟨P, hP⟩ hp
  exact ⟨j, Q, hQ, hm⟩


open Polynomial in
theorem root_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    {Ω : Type} [Field Ω] (ω : c.pt →+* Ω)
    (H : ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ)
    (j : J) (P : (D.obj j)[X]) (hP : P.Monic) (y : Ω) (hy : (P.map (ω.comp (c.ι.app j).hom)).eval y = 0)
    (hd : (P.derivative.map (ω.comp (c.ι.app j).hom)).eval y ≠ 0) :
    ∃ b : c.pt, (P.map (c.ι.app j).hom).eval b = 0 ∧ ω b = y := by
  let Q : StandardEtalePair (D.obj j) := ⟨P, hP, P.derivative, ⟨1, 0, 1, by ring⟩⟩
  let _ : Algebra (D.obj j) Ω := (ω.comp (c.ι.app j).hom).toAlgebra
  have hm : Q.HasMap y := by
    refine ⟨?_, ?_⟩
    · show aeval y P = 0
      rw [aeval_def, eval₂_eq_eval_map]; exact hy
    · show IsUnit (aeval y (derivative P))
      rw [aeval_def, eval₂_eq_eval_map]; exact isUnit_iff_ne_zero.2 hd
  obtain ⟨j', g, φ, h1, h2⟩ := H j Q.Ring inferInstance inferInstance inferInstance (Q.lift y hm).toRingHom
    (Q.lift y hm).comp_algebraMap
  refine ⟨(c.ι.app j').hom (φ Q.X), ?_, ?_⟩
  · have h0 : aeval Q.X Q.f = 0 := Q.hasMap_X.1
    have := congrArg ((c.ι.app j').hom.comp φ) h0
    rw [map_zero] at this
    rw [← this, aeval_def, hom_eval₂, RingHom.comp_assoc, h1, ← CommRingCat.hom_comp, c.w, Polynomial.eval_map]; rfl
  · have := RingHom.congr_fun h2 Q.X
    exact this.trans (Q.lift_X y hm)

structure NSys {B : Scheme.{0}} (U : B.Etale) (x : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  D : J ⥤ CommRingCat.{0}
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  e : ∀ j, (V j).left ≅ Spec (D.obj j)
  tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j
  tr_a : ∀ {j j' : J} (g : j ⟶ j'), tr g ≫ a j = a j'
  tr_spec : ∀ {j j' : J} (g : j ⟶ j'), (e j').inv ≫ (tr g).left ≫ (e j).hom = Spec.map (D.map g)
  hx : ∀ j, x ∈ Set.range (a j).left
  c : Cocone D
  hc : IsColimit c
  cof : Cof D c
  t : Spec c.pt ⟶ U.left
  ht : ∀ j, t = Spec.map (c.ι.app j) ≫ (e j).inv ≫ (a j).left

attribute [instance] NSys.cat NSys.filt

def LeafNSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left), Nonempty (NSys U x)

def LeafSHofCof : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
  IsColimit c → Cof D c → SH c.pt

open Polynomial IsLocalRing in
theorem SHofCof : LeafSHofCof := by
  intro J _ _ D c hc hC
  have hL := isLocalRing_of_cof D c hc hC
  obtain ⟨Ω, _, _, ω, H⟩ := hC
  have hmax : ∀ a : c.pt, a ∈ maximalIdeal c.pt ↔ ω a = 0 := fun a => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h; by_contra h'; exact h (unit_of_cof D c hc ω H a h')
    · intro h hu; have := hu.map ω; rw [h] at this; exact not_isUnit_zero this
  have : Nontrivial c.pt := ω.domain_nontrivial
  have hH : HenselianLocalRing c.pt := by
    refine { toIsLocalRing := hL, is_henselian := ?_ }
    intro f hf a₀ h1 h2
    obtain ⟨j, P, hP, hPm⟩ := monic_rep D c hc f hf
    have e : P.map (ω.comp (c.ι.app j).hom) = f.map ω := by rw [← Polynomial.map_map, hP]
    obtain ⟨b, hb, hbω⟩ := root_of_cof D c ω H j P hPm (ω a₀)
      (by rw [e, Polynomial.eval_map, eval₂_at_apply, ← hmax]; exact h1)
      (by rw [← derivative_map, e, derivative_map, Polynomial.eval_map, eval₂_at_apply]
          intro h0; have := h2.map ω; rw [h0] at this; exact not_isUnit_zero this)
    refine ⟨b, ?_, ?_⟩
    · rw [hP] at hb; exact hb
    · rw [hmax, map_sub, hbω, sub_self]
  refine ⟨hH, ?_⟩
  have hk : RingHom.ker (residue c.pt) ≤ RingHom.ker ω := fun a ha => by
    rw [RingHom.mem_ker, residue_eq_zero_iff] at ha; exact (hmax a).1 ha
  let ωb : ResidueField c.pt →+* Ω := RingHom.liftOfSurjective (residue c.pt) residue_surjective ⟨ω, hk⟩
  have hωb : ωb.comp (residue c.pt) = ω := RingHom.liftOfRightInverse_comp _ _ _ _
  refine IsSepClosed.of_exists_root _ (fun p hpm hirr hsep => ?_)
  have hl : p ∈ lifts (residue c.pt) := (lifts_iff_coeff_lifts p).2 (fun n => residue_surjective _)
  obtain ⟨pt, hpt, -, hptm⟩ := lifts_and_degree_eq_and_monic hl hpm
  obtain ⟨j, P, hP, hPm⟩ := monic_rep D c hc pt hptm
  have e : P.map (ω.comp (c.ι.app j).hom) = p.map ωb := by
    rw [← Polynomial.map_map, hP, ← hpt, Polynomial.map_map, hωb]
  have hdeg : (p.map ωb).degree ≠ 0 := by
    rw [degree_map]; intro h0
    exact hirr.not_isUnit (by rw [hpm.natDegree_eq_zero.1 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le)]; exact isUnit_one)
  obtain ⟨y, hy⟩ := IsSepClosed.exists_root (p.map ωb) hdeg hsep.map
  have hd := hsep.map (f := ωb) |>.aeval_derivative_ne_zero (x := y) (by rw [coe_aeval_eq_eval]; exact hy)
  rw [coe_aeval_eq_eval] at hd
  obtain ⟨b, hb, -⟩ := root_of_cof D c ω H j P hPm y (by rw [e]; exact hy)
    (by rw [← derivative_map, e]; exact hd)
  refine ⟨residue c.pt b, ?_⟩
  rw [← hpt, Polynomial.eval_map, eval₂_at_apply, ← hP, hb, map_zero]

theorem LeafSHSys_of (hN : LeafNSys) (hA : LeafSHofCof) : LeafSHSys := by
  intro B U x
  obtain ⟨S⟩ := hN U x
  exact ⟨{
    J := S.J
    D := S.D
    V := S.V
    a := S.a
    e := S.e
    tr := fun g => S.tr g
    tr_a := fun g => S.tr_a g
    tr_spec := fun g => S.tr_spec g
    hx := S.hx
    c := S.c
    hc := S.hc
    sh := hA S.D S.c S.hc S.cof
    t := S.t
    ht := S.ht }⟩

def LeafRingSys : Prop := ∀ (R : CommRingCat.{0}) (p : PrimeSpectrum R),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j),
    (∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j') ∧ (∀ j, (u j).hom.Etale) ∧
    (∀ j, ∃ q : PrimeSpectrum (D.obj j), q.comap (u j).hom = p) ∧
    ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Cof D c

def LeafNSysGlue : Prop := LeafRingSys → LeafNSys

theorem LeafSHSys_of_glue (hR : LeafRingSys) (hG : LeafNSysGlue) : LeafSHSys :=
  LeafSHSys_of (hG hR) SHofCof

end LateralTheory.E.LeafSHSysPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData LateralTheory.E.ProjectiveLineCharts₂

namespace LateralTheory.E.ChartBC_nnmPf

theorem res_bijective {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  obtain rfl := le_antisymm h h'
  have : (homOfLE h) = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

theorem pushout_gen {Z X Y P : CommRingCat.{0}} {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (h : IsPushout f g i j) (R : Subring P) (hi : ∀ x, i x ∈ R) (hj : ∀ y, j y ∈ R) (p : P) : p ∈ R := by
  let i' : X ⟶ CommRingCat.of R := CommRingCat.ofHom (i.hom.codRestrict R hi)
  let j' : Y ⟶ CommRingCat.of R := CommRingCat.ofHom (j.hom.codRestrict R hj)
  have w' : f ≫ i' = g ≫ j' := by
    ext z
    have := congrArg (fun φ => φ.hom z) h.w
    simpa [i', j'] using this
  let σ := h.desc i' j' w'
  have hσ : σ ≫ CommRingCat.ofHom R.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc]; ext; rfl
    · rw [h.inr_desc_assoc]; ext; rfl
  have := congrArg (fun φ => φ.hom p) hσ
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at this
  rw [← this]; exact (σ.hom p).2

theorem restrict_appTop_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ (f ∣_ U).appTop =
      f.app U ≫ X.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)).le).op := by
  rw [morphismRestrict_appTop]
  have e := f.naturality (homOfLE (Scheme.Opens.ι_image_top U).le).op
  calc _ = (Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ f.app (U.ι ''ᵁ ⊤)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op := (Category.assoc _ _ _).symm
    _ = _ := by rw [e, Category.assoc, ← Functor.map_comp]; rfl

theorem snd_eq {A : Type} [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (V : L.Opens) :
    (V.ι ≫ l).appTop = l.appLE ⊤ V le_top ≫ L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top V).le).op := by
  unfold Scheme.Hom.appLE
  rw [Category.assoc, ← Functor.map_comp]
  rfl

theorem ChartBC_of : ChartBC := by
  intro A _ L l f hf W x hW hsx
  have hpb := IsPullback.paste_vert (isPullback_morphismRestrict f W) hf
  have : IsAffine W.toScheme := hW
  have hA : IsAffineOpen (f ⁻¹ᵁ W) := IsAffine.of_isPullback hpb
  refine ⟨hA, ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hA
  have hpo := isPushout_appTop_of_isPullback hpb
  let ψ := L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le).op
  have hψ := res_bijective (X := L) (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).ge
  let R : Subring Γ((f ⁻¹ᵁ W).toScheme, ⊤) :=
    (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x)).range.map ψ.hom
  intro t
  have ht : ψ t ∈ R := pushout_gen hpo R ?_ ?_ (ψ t)
  · obtain ⟨r, ⟨q, rfl⟩, hr⟩ := Subring.mem_map.mp ht
    exact ⟨q, hψ.1 hr⟩
  · intro w
    obtain ⟨w0, rfl⟩ := (res_bijective (X := P1) (Scheme.Opens.ι_image_top W).le
      (Scheme.Opens.ι_image_top W).ge).2 w
    have h1 : (f ∣_ W).appTop (P1.presheaf.map (homOfLE (Scheme.Opens.ι_image_top W).le).op w0) =
        ψ (f.app W w0) := congrArg (fun φ => φ.hom w0) (restrict_appTop_eq f W)
    erw [h1]
    obtain ⟨q, rfl⟩ := hsx w0
    refine Subring.mem_map.mpr ⟨_, ⟨q.map (Int.castRingHom A), rfl⟩, ?_⟩
    congr 1
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
    congr 1; exact RingHom.ext_int _ _
  · intro a
    refine Subring.mem_map.mpr ⟨_, ⟨Polynomial.C ((Scheme.ΓSpecIso (CommRingCat.of A)).hom a), rfl⟩, ?_⟩
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, snd_eq]
    simp only [rA, RingHom.comp_apply]
    erw [Iso.hom_inv_id_apply]
    rfl

end LateralTheory.E.ChartBC_nnmPf
end
end
