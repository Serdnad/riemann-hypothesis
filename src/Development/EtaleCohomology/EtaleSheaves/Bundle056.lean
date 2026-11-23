module

public import Development.EtaleCohomology.EtaleSheaves.Bundle029
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Development.EtaleCohomology.EtaleSheaves.Bundle031
public import Development.EtaleCohomology.EtaleSheaves.Bundle046
import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle018
public import Development.EtaleCohomology.EtaleSheaves.Bundle037
public import Development.EtaleCohomology.EtaleSheaves.Bundle018
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
public import Development.EtaleCohomology.EtaleSheaves.Bundle045
public import Development.EtaleCohomology.EtaleSheaves.Bundle040
public import Development.EtaleCohomology.EtaleSheaves.Bundle051
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
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
import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor

theorem etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.prim_loc_of hr) (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.kumT_ex_of hk)
    LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.QuasiFiniteDescent

def QFChain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (R : Subalgebra k Ω)
    {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) : Prop :=
  IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
  IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧
  γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafQFOmega : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) ∧ LocallyQuasiFinite γ1 ∧ LocallyQuasiFinite γ2

def LeafDescendPreMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 ∧ v0 ≫ f = e

def LeafSpreadQF : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) → LocallyQuasiFinite γ1 → LocallyQuasiFinite γ2 →
    ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 → v0 ≫ f = e →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (f' : E0 ⟶ X) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2)
      (hf' : f' ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
      QFChain p R' c0 γ1 γ2 e q' e1 e2 f' w0 w1 w2 hf'

def LeafReducedSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), SmoothOfRelativeDimension 1 q → AlgebraicGeometry.IsReduced D

theorem integral_of (hI : LeafIrred) (hR : LeafReducedSmooth) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k Ω) (hFG : R.FG) {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D)
    (hc : IsCurve c) (hs : SmoothOfRelativeDimension 1 q) (hp : IsPullback v c q (toR R)) : IsIntegral D := by
  have := hI k Ω R hFG c q v hc hs hp
  have := hR k Ω R hFG q hs
  exact isIntegral_of_irreducibleSpace_of_isReduced D

theorem goal_of (hQ : LeafQFOmega) (hP : LeafDescendPreMap) (hS : LeafSpreadQF) (hI : LeafIrred)
    (hR : LeafReducedSmooth) (hD : LeafDimBound) : LateralTheory.E.LeafGeoVV2Cut.LeafDescendQF := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨q0, q1, q2⟩ := hQ k p Ω hdim c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hFG, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, hpre, hve⟩ :=
    hP k p Ω c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', hc⟩ :=
    hS k p Ω R hFG c0 γ1 γ2 e he hc0 h1 h2 q0 q1 q2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, l0, l1, l2, P0, P1, P2, m1, m2, m3⟩ := hc
  exact ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', a1, a2, a3, b1, b2, b3, c1, c2, c3,
    integral_of hI hR R' hFG' c0 q' w0 hc0 a3 P0, integral_of hI hR R' hFG' (γ1 ≫ c0) (e1 ≫ q') w1 h1 b3 P1,
    integral_of hI hR R' hFG' (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') w2 h2 c3 P2, l0, l1, l2,
    hD k Ω R' hFG' q' a3, P0, P1, P2, m1, m2, m3⟩

end LateralTheory.E.QuasiFiniteDescent

end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.LeafGhostCut LateralTheory.E.DescIntPf LateralTheory.E.KernelLocalization
namespace LateralTheory.E.RelativeTruncationSingleDegree
theorem sub_of (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (h : RelZS R F n f)
    (hf : ∀ z : Hrel R f F n, pull R f F n (fgt R f F n z) = 0) : Subsingleton (Hrel R f F n) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  have h1 : fgt R f F n z = 0 := (injective_iff_map_eq_zero _).1 h.2 _ (hf z)
  exact (injective_iff_map_eq_zero _).1 (LateralTheory.E.TruncationKernel.fgt_injective_of_pull_surjective R F f n h.1) z h1
theorem pull_fgt (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (z : Hrel R f F n) :
    pull R f F n (fgt R f F n z) = 0 := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ _ c
end LateralTheory.E.RelativeTruncationSingleDegree
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

theorem closedAt_comp {X N T : Scheme.{0}} (c' : X ⟶ N) (k' : N ⟶ T) (V : T.Opens)
    (h : ClosedAt c' (k' ⁻¹ᵁ V)) (hs : Function.Surjective (k'.app V)) : ClosedAt (c' ≫ k') V := by
  intro b hb
  obtain ⟨p, hm, hp⟩ := hb
  obtain ⟨a', ha'⟩ := h b ⟨p.map (k'.app V).hom, hm.map _, (Polynomial.eval₂_map (p := p) (k'.app V).hom (c'.app (k' ⁻¹ᵁ V)).hom b).trans hp⟩
  obtain ⟨a, rfl⟩ := hs a'
  exact ⟨a, ha'⟩

theorem normClosed : NormClosed := by
  intro Z S g _ _ _ V hV
  have H : g = g.toNormalization.toNormalization ≫
      (g.toNormalization.fromNormalization ≫ g.fromNormalization) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
      Scheme.Hom.toNormalization_fromNormalization]
  let h := g.normalizationDesc _ _ H
  have e1 : g.toNormalization ≫ h = g.toNormalization.toNormalization :=
    g.toNormalization_normalizationDesc _ _ H
  have e2 : h ≫ g.toNormalization.fromNormalization ≫ g.fromNormalization = g.fromNormalization :=
    g.normalizationDesc_comp _ _ H
  have i1 : h ≫ g.toNormalization.fromNormalization = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
      (by rw [reassoc_of% e1, Scheme.Hom.toNormalization_fromNormalization, Category.comp_id])
      (by rw [Category.assoc, e2]) (Category.id_comp _)
  have i2 : g.toNormalization.fromNormalization ≫ h = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g.toNormalization _ _ g.toNormalization.fromNormalization
      (by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, e1, Category.comp_id])
      (by rw [Category.assoc, i1, Category.comp_id]) (Category.id_comp _)
  have : IsIso g.toNormalization.fromNormalization := ⟨h, i2, i1⟩
  have e := g.toNormalization.toNormalization_fromNormalization
  rw [← e]
  exact closedAt_comp _ _ V (closedAt_preimage _ V hV)
    (ConcreteCategory.bijective_of_isIso (g.toNormalization.fromNormalization.app V)).2

theorem RelNorm_of : LateralTheory.E.SteinPf.RelNorm := RelNorm_of_closed normClosed

end LateralTheory.E.RelNormPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.TruncCokPf Opposite

namespace LateralTheory.E.LevelsPf

def CechLevel : Prop := ∀ (p : ℕ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''),
    ∃ (Ep Yp : CommRingCat.{0}) (dp : D ⟶ Ep) (wp : Y' ⟶ Yp) (φp : Ep ⟶ Yp), IsPushout φ' dp wp φp ∧
      (∀ {A : CommRingCat.{0}} (d : A ⟶ D) (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop), PushClosed P → P D d →
        P E (d ≫ e) → P Ep (d ≫ dp)) ∧
      Nonempty (Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p))) ≅
        Arrow.mk (yoneda.map (Spec.map φp)))

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (a : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R a.hom F n) := by
  have h1 : ∀ x, pull R a.inv F n (pull R a.hom F n x) = x := fun x => by
    rw [← pull_comp, Iso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R a.hom F n (pull R a.inv F n x) = x := fun x => by
    rw [← pull_comp, Iso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem transfer (R : Type) [CommRing R] (F : Shv R) {P Q P' Q' : PSh} (f : P ⟶ Q) (g : P' ⟶ Q')
    (α : Arrow.mk f ≅ Arrow.mk g) (n : ℤ) :
    (Function.Surjective (pull R (disc.map g) F n) → Function.Surjective (pull R (disc.map f) F n)) ∧
    (Function.Injective (pull R (disc.map g) F n) → Function.Injective (pull R (disc.map f) F n)) := by
  let αl : P ≅ P' := Arrow.leftFunc.mapIso α
  let αr : Q ≅ Q' := Arrow.rightFunc.mapIso α
  have hw : f ≫ αr.hom = αl.hom ≫ g := by
    exact (Arrow.w α.hom).symm
  have hf : f = αl.hom ≫ g ≫ αr.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]; exact hw
  have he : ⇑(pull R (disc.map f) F n) =
      pull R (disc.mapIso αl).hom F n ∘ pull R (disc.map g) F n ∘ pull R (disc.mapIso αr).symm.hom F n := by
    funext x
    rw [hf, Functor.map_comp, Functor.map_comp, pull_comp, pull_comp]; rfl
  have bl := pull_iso_bij R (disc.mapIso αl) F n
  have br := pull_iso_bij R (disc.mapIso αr).symm F n
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · rw [he]; exact bl.2.comp (hs.comp br.2)
  · rw [he]; exact bl.1.comp (hi.comp br.1)

theorem Levels_of (hC : CechLevel) : LateralTheory.E.TruncCokPf.Levels := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  obtain ⟨Ep, Yp, dp, wp, φp, hpp, hP, ⟨α⟩⟩ := hC p e φ' u φ'' hpo'
  have hsq : IsPushout φ (d ≫ dp) (w ≫ wp) φp := hpo.paste_vert hpp
  have hrel : RelZ q i m φp := hlow m hm Ep (d ≫ dp) (hP d P hpush hD hE) Yp (w ≫ wp) φp hsq
  have ht := fun k => transfer (ZMod q) (tw q i) _ _ α k
  refine ⟨fun k hk => (ht k).1 (hrel.1 k hk), (ht m).2 hrel.2⟩

end LateralTheory.E.LevelsPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.RelDescPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨y, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  change (Cochain.ofHom (a ≫ b)).comp y.1 (zero_add n) =
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp y.1 (zero_add n)) (zero_add n)
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) comm'' = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm := by
  simp only [rmap, Functor.map_comp]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) comm'' F n y = rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' comm comm' comm'']
  exact hkpull_comp R _ _ F n y

def RelEqvInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f), Eqv R u F → Eqv R e F → ∀ n : ℤ, Function.Injective (rpull R f f' u e comm F n)

def CechEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E)
  (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''), Et e → SpS e → IsPushout φ' e u φ'' →
  Eqv (ZMod q) (cechAug (Spec.map e)) (tw q i) ∧ Eqv (ZMod q) (cechAug (Spec.map u)) (tw q i)

def LevelInj : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  ∃ (g : cech (Spec.map u) ⟶ cech (Spec.map e)) (_hA : g ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ'))
    (i0 : sch.obj (Spec E) ⟶ cech (Spec.map e)) (j0 : sch.obj (Spec Y'') ⟶ cech (Spec.map u))
    (h0 : sch.map (Spec.map φ'') ≫ i0 = j0 ≫ g),
    i0 ≫ cechAug (Spec.map e) = sch.map (Spec.map e) ∧ j0 ≫ cechAug (Spec.map u) = sch.map (Spec.map u) ∧
    Function.Injective (rpull (ZMod q) g (sch.map (Spec.map φ'')) j0 i0 h0 (tw q i) n)

theorem relDesc_of (hEq : RelEqvInj) (hC : CechEqv) (hL : LevelInj) : LateralTheory.E.TruncationKernel.RelDesc := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨g, hA, i0, j0, h0, hi, hj, hinj⟩ := hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨hCe, hCu⟩ := hC hH q i φ' e u φ'' he hs hpo'
  have h1 := hEq (ZMod q) (tw q i) (sch.map (Spec.map φ')) g (cechAug (Spec.map u)) (cechAug (Spec.map e)) hA hCu hCe n
  have key : ∀ (a : sch.obj (Spec Y'') ⟶ sch.obj (Spec Y')) (b : sch.obj (Spec E) ⟶ sch.obj (Spec D))
      (ha : j0 ≫ cechAug (Spec.map u) = a) (hb : i0 ≫ cechAug (Spec.map e) = b)
      (c : sch.map (Spec.map φ'') ≫ b = a ≫ sch.map (Spec.map φ')),
      Function.Injective (rpull (ZMod q) (sch.map (Spec.map φ')) (sch.map (Spec.map φ'')) a b c (tw q i) n) := by
    intro a b ha hb c
    subst ha hb
    intro x y hxy
    rw [rpull_comp _ _ g _ _ _ _ _ hA h0 c, rpull_comp _ _ g _ _ _ _ _ hA h0 c] at hxy
    exact h1 (hinj hxy)
  exact key _ _ hj hi _

theorem etale_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (he : Et e) : Etale (Spec.map e) :=
  HasRingHomProperty.Spec_iff.mpr he

theorem surj_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (hs : SpS e) : Surjective (Spec.map e) := by
  constructor
  intro x
  obtain ⟨Q, hQ, hQr⟩ := hs x.asIdeal x.isPrime
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQr⟩

theorem cechEqv : CechEqv := by
  intro hH q _ i D Y' E Y'' φ' e u φ'' he hs hpo
  have hpb := isPullback_SpecMap_of_isPushout φ' e u φ'' hpo
  have hE : Etale (Spec.map e) := etale_spec e he
  have hS : Surjective (Spec.map e) := surj_spec e hs
  have hEu : Etale (Spec.map u) := MorphismProperty.of_isPullback (P := @Etale) hpb.flip hE
  have hSu : Surjective (Spec.map u) := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  exact ⟨hH.2.1 (ZMod q) (Spec.map e) (tw q i), hH.2.1 (ZMod q) (Spec.map u) (tw q i)⟩

end LateralTheory.E.RelDescPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafDescendFPPf

def FP {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f

theorem fp_of_curve {Ω : Type} [Field Ω] {C : Scheme.{0}} {c : C ⟶ Sp Ω} (h : IsCurve c) : FP c := by
  obtain ⟨_, hp, hs⟩ := h
  have := hp
  have := hs
  refine ⟨inferInstance, inferInstance, inferInstance⟩

def LeafObjFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
      FP q ∧ IsPullback v f q (toR R)

def LeafPairFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → IsPullback v0 c0 q (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

def LeafTripleFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), FP (γ2 ≫ γ1 ≫ c0) →
    ∀ {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP (d1 ≫ q) →
    IsPullback v0 c0 q (toR R) → IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) → γ1 ≫ v0 = v1 ≫ d1 →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2), PreChain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2

theorem diagramDescent_of_objects_pairs_triples (hO : LeafObjFP) (hP : LeafPairFP) (hT : LeafTripleFP) : LeafDescendFP := by
  intro k _ Ω _ _ C0 c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, q, v0, hq, hsq⟩ := hO k Ω c0 (fp_of_curve hc0)
  obtain ⟨R', hR', E0, E1, q', e1, w0, w1, hq', he1, hs0, hs1, hc⟩ :=
    hP k Ω R hR c0 γ1 (fp_of_curve h1) q v0 hq hsq
  exact hT k Ω R' hR' c0 γ1 γ2 (fp_of_curve h2) q' e1 w0 w1 hq' he1 hs0 hs1 hc

end LateralTheory.E.LeafDescendFPPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSmoothOfNormalPf

def LeafStalkSmoothClosed : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω)
  [IsIntegral C], LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → ∀ y : C, y ≠ genericPoint C → (c.stalkMap y).hom.FormallySmooth

def LeafRelDimOne : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → Smooth c → topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem smooth_of_stalks (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [LocallyOfFiniteType c]
    (h : ∀ y : C, (c.stalkMap y).hom.FormallySmooth) : Smooth c := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  exact top_le_iff.mp fun y _ => h y

theorem stalk_smooth_all (hA : LeafStalkSmoothClosed) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hC : IsIntegral C) (hc : LocallyOfFiniteType c)
    (hn : ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) (hd : topologicalKrullDim C = 1) (y : C) :
    (c.stalkMap y).hom.FormallySmooth := by
  by_cases hy : y = genericPoint C
  · subst hy
    exact c.genericPoint_mem_smoothLocus_of_perfectField
  · exact hA Ω c hc hn hd y hy

theorem LeafSmoothOfNormal_of (hA : LeafStalkSmoothClosed) (hB : LeafRelDimOne) :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hC hc hn hd
  have hs : Smooth c := smooth_of_stalks Ω c (stalk_smooth_all hA Ω c hC hc hn hd)
  exact hB Ω c hC hs hd

end LateralTheory.E.LeafSmoothOfNormalPf
end
end

section

noncomputable section

namespace LateralTheory.E.LSurjChartPf

theorem zmt_etale_at (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (q : Ideal A') [q.IsPrime] :
    ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ q ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) :=
  (Algebra.ZariskisMainProperty.of_finiteType q).exists_fg_and_exists_notMem_and_awayMap_bijective _

def GraphPatch : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (A' : Type) [CommRing A'] [Algebra A A']
    (φ : A' →ₐ[A] A ⧸ I),
    (∀ q : Ideal A', q.IsPrime → RingHom.ker φ ≤ q → ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧
      ∃ r : S', r.1 ∉ q ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r)) →
    ∃ (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
      IsUnit (φ r.1) ∧ Function.Bijective (Localization.awayMap S.val.toRingHom r)

def FiniteGraphChart : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (φ : A' →ₐ[A] A ⧸ I), ∃ (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
      IsUnit (φ r.1) ∧ Function.Bijective (Localization.awayMap S.val.toRingHom r)

def FiniteChartSurj : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → LateralTheory.E.LChartPf.IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I)
    (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
    IsUnit (φ r.1) → Function.Bijective (Localization.awayMap S.val.toRingHom r) →
    ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem FiniteGraphChart_of (hP : GraphPatch) : FiniteGraphChart := by
  intro A _ I A' _ _ _ φ
  exact hP A I A' φ (fun q hq _ => zmt_etale_at A A' q)

theorem LSurjChart_of' (hA : FiniteGraphChart) (hB : FiniteChartSurj) :
    LateralTheory.E.LChartPf.LSurjChart := by
  intro A _ I hI hid A' _ _ _ φ
  obtain ⟨S, hS, r, hr, hb⟩ := hA A I A' φ
  exact hB A I hI hid A' φ S hS r hr hb

theorem LSurjChart_of (hP : GraphPatch) (hB : FiniteChartSurj) : LateralTheory.E.LChartPf.LSurjChart :=
  LSurjChart_of' (FiniteGraphChart_of hP) hB

end LateralTheory.E.LSurjChartPf
end
end
