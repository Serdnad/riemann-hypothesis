module

public import Development.EtaleCohomology.EtaleSheaves.Bundle085
public import Development.EtaleCohomology.EtaleSheaves.Bundle086
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.EtaleCohomology.EtaleSheaves.Bundle087
public import Development.EtaleCohomology.EtaleSheaves.ClosedPointLifts.ProperBaseChangeClosedFiberStrictlyHenselianEqui
public import Development.EtaleCohomology.EtaleSheaves.ClosedPointLifts.ClosedLift
public import Development.EtaleCohomology.EtaleSheaves.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.QuasiFiniteAtDescent

theorem quasiFiniteAt_of_isOpen_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (a : X) (hza : f.fiberι y z = a) (hz : IsOpen ({z} : Set (f.fiber y))) :
    f.QuasiFiniteAt a := by
  have hy : y = f a := by
    rw [← hza, ← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst hy
  have : z = f.asFiber a := by
    apply (f.fiberι (f a)).isEmbedding.injective
    rw [hza, Scheme.Hom.fiberι_asFiber]
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← this]
  exact hz

theorem qf_of_fiberMap {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B)
    [LocallyOfFiniteType g] [LocallyOfFiniteType γ] (x : CA)
    (φ : γ.fiber (γ x) ⟶ g.fiber (vB (γ x))) (hφ : UniversallyOpen φ)
    (e : φ ≫ g.fiberι (vB (γ x)) = γ.fiberι (γ x) ≫ vA) (hx : γ.QuasiFiniteAt x) :
    g.QuasiFiniteAt (vA x) := by
  have hx' : IsOpen ({γ.asFiber x} : Set (γ.fiber (γ x))) :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx
  have hopen := φ.isOpenMap _ hx'
  have h2 : IsOpen ({φ (γ.asFiber x)} : Set (g.fiber (vB (γ x)))) := by
    convert hopen using 1
    exact (Set.image_singleton).symm
  refine quasiFiniteAt_of_isOpen_fiber g (vB (γ x)) (φ (γ.asFiber x)) (vA x) ?_ h2
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]

theorem LeafQFAtDescend_of : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend := by
  intro CA CB A B γ g vA vB sq hg x hx
  have : LocallyOfFiniteType γ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hg
  have sqF := isPullback_fiberToSpecResidueField_of_isPullback sq (γ x)
  have hφ := MorphismProperty.of_isPullback (P := @UniversallyOpen) sqF.flip inferInstance
  refine qf_of_fiberMap γ g vA vB x _ hφ ?_ hx
  exact pullback.lift_fst _ _ _

end LateralTheory.E.QuasiFiniteAtDescent
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodSystemGluing
open LateralTheory.E.LeafSHSysPf

theorem cocone_u_eq {R : CommRingCat.{0}} {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j) (hu : ∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j')
    (c : Cocone D) (j j' : J) : u j ≫ c.ι.app j = u j' ≫ c.ι.app j' := by
  have h1 := c.w (IsFiltered.leftToMax j j')
  have h2 := c.w (IsFiltered.rightToMax j j')
  rw [← h1, ← h2, ← Category.assoc, ← Category.assoc, hu, hu]

theorem LeafNSysGlue_of (hR : LeafRingSys) : LeafNSysGlue := by
  intro _ B U x
  let 𝒰 := U.left.affineOpenCover
  let R := 𝒰.X (𝒰.idx x)
  let ι : Spec R ⟶ U.left := 𝒰.f (𝒰.idx x)
  obtain ⟨y, hy⟩ := 𝒰.covers x
  obtain ⟨J, _, _, D, u, hu, het, hq, c, ⟨hc⟩, hcof⟩ := hR R y
  have hE : ∀ j, Etale (Spec.map (u j) ≫ ι ≫ U.hom) := fun j => by
    have : Etale (Spec.map (u j)) := HasRingHomProperty.Spec_iff.2 (het j)
    have : Etale U.hom := U.prop
    infer_instance
  let V : J → B.Etale := fun j => MorphismProperty.Over.mk ⊤ (Spec.map (u j) ≫ ι ≫ U.hom) (hE j)
  let a : ∀ j, V j ⟶ U := fun j => MorphismProperty.Over.homMk (Spec.map (u j) ≫ ι) (by show (Spec.map (u j) ≫ ι) ≫ U.hom = Spec.map (u j) ≫ ι ≫ U.hom; rw [Category.assoc]) trivial
  let tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j := fun {j j'} g =>
    MorphismProperty.Over.homMk (Spec.map (D.map g))
      (by show Spec.map (D.map g) ≫ Spec.map (u j) ≫ ι ≫ U.hom = Spec.map (u j') ≫ ι ≫ U.hom; rw [← Spec.map_comp_assoc, hu]) trivial
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  exact ⟨{
    J := J
    D := D
    V := V
    a := a
    e := fun j => Iso.refl _
    tr := tr
    tr_a := fun g => by
      apply MorphismProperty.Over.Hom.ext
      show Spec.map (D.map g) ≫ Spec.map _ ≫ ι = Spec.map _ ≫ ι
      rw [← Spec.map_comp_assoc, hu]
    tr_spec := fun g => by
      show 𝟙 _ ≫ Spec.map (D.map g) ≫ 𝟙 _ = _
      simp
    hx := fun j => by
      obtain ⟨q, hq⟩ := hq j
      refine ⟨q, ?_⟩
      rw [← hy]
      show ι (Spec.map (u j) q) = ι y
      congr 1
    c := c
    hc := hc
    cof := hcof
    t := Spec.map (c.ι.app j0) ≫ Spec.map (u j0) ≫ ι
    ht := fun j => by
      show _ = Spec.map (c.ι.app j) ≫ 𝟙 _ ≫ Spec.map (u j) ≫ ι
      rw [Category.id_comp, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, cocone_u_eq D u hu c j0 j] }⟩

end LateralTheory.E.NeighbourhoodSystemGluing
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem prod_surj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hA : A ≤ D) (hB : B ≤ D) (hD : D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B)) :
    Function.Surjective (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) := by
  intro x
  have hx : (x : L) ∈ (Algebra.TensorProduct.productMap A.val B.val).range := by
    rw [Algebra.TensorProduct.productMap_range, A.range_val, B.range_val]
    have := hD x.2
    rwa [Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq] at this
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  rw [← hy]
  have e : D.val.comp (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) =
      Algebra.TensorProduct.productMap A.val B.val := by
    ext <;> rfl
  exact congrArg (fun φ : _ →ₐ[Ω] L => φ y) e

theorem spec_subalgebra_pullback_lift_is_closed_immersion : LeafSpecGenClosed := by
  intro Ω L _ _ _ A B D hA hB hD
  let φ := Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)
  have e : pullback.lift _ _ (spec_w A B D hA hB) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso Ω A B).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
  rw [e]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (prod_surj A B D hA hB hD)
  infer_instance

end LateralTheory.E.GluedCurveChartOverlaps
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.SysFMPf

namespace LateralTheory.E.IdemSecPf

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.app ⊤) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  intro a b h
  exact h1 (h2 h)

theorem phi_idem {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (e : W) (he : IsIdempotentElem e) : ∃ s, phi w s = e := by
  let t : Γ(Spec (CommRingCat.of W), w.toNormalization ⁻¹ᵁ ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv e
  have ht : (w.toNormalization.app ⊤).hom.IsIntegralElem t := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
    · have : t * t = t := by
        show (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e * (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e = _
        rw [← map_mul, he.eq]
      rw [sq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, this, sub_self]
  obtain ⟨s, hs⟩ := GlobalTheory.mem_range_toNormalization_app w ⊤ t ht
  refine ⟨s, ?_⟩
  show (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (w.toNormalization.app ⊤ s) = e
  rw [hs]
  show ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom e = e
  simp

theorem IdemSec_of : LateralTheory.E.SysFMPfSys.IdemSec := by
  intro P _ _ W _ w
  exact ⟨phi_injective w, fun e he => phi_idem w e he⟩

end LateralTheory.E.IdemSecPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.Bridge_yfiPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd
  LateralTheory.E.NeighbourhoodKilling LateralTheory.E.SecondDegreeKilling

structure Sys (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) (u : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  mem : ∀ j, u ∈ Set.range (a j).left
  tr : ∀ {j k : J}, (j ⟶ k) → (V k ⟶ V j)
  tr_id : ∀ j, tr (𝟙 j) = 𝟙 (V j)
  tr_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), tr (f ≫ g) = tr g ≫ tr f
  tr_a : ∀ {j k : J} (f : j ⟶ k), tr f ≫ a j = a k
  A : Type
  [ring : CommRing A]
  sh : SH A
  t : Sp A ⟶ U.left
  gY : ∀ j, pullback p (t ≫ U.hom) ⟶ YU p (V j)
  gW : ∀ j, pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι
  sq : ∀ j, prS p ι (t ≫ U.hom) ≫ gY j = gW j ≫ prU p ι (V j)
  gY_a : ∀ j, gY j ≫ resY p (a j) = tY p U t
  gW_a : ∀ j, gW j ≫ resYW p ι (a j) = tW p ι U t
  gY_tr : ∀ {j k : J} (f : j ⟶ k), gY k ≫ resY p (tr f) = gY j
  gW_tr : ∀ {j k : J} (f : j ⟶ k), gW k ≫ resYW p ι (tr f) = gW j
  injY : ∀ j (y : Ht q (sch.obj (YU p (V j))) m i), pull (ZMod q) (sch.map (gY j)) (tw q i) m y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resY p (tr f))) (tw q i) m y = 0
  surY : ∀ y : Ht q (sch.obj (pullback p (t ≫ U.hom))) (m - 1) i,
    ∃ (j : J) (y' : Ht q (sch.obj (YU p (V j))) (m - 1) i), pull (ZMod q) (sch.map (gY j)) (tw q i) (m - 1) y' = y
  injW : ∀ j (w : Ht q (sch.obj (pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι)) (m - 1) i),
    pull (ZMod q) (sch.map (gW j)) (tw q i) (m - 1) w = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resYW p ι (tr f))) (tw q i) (m - 1) w = 0

def Geo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Pack : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
  (u : U.left) (_ : Sys q i p ι U m u) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem Bridge_of_geo_pack (hG : Geo) (hP : Pack) : Bridge := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z u
  obtain ⟨S⟩ := hG hH q k hq i toK ι p hp U m u
  exact hP q i p ι U m u S z

end LateralTheory.E.Bridge_yfiPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.PointEvaluationWitness
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.SecondDegreeKilling LateralTheory.E.LeafPtWPf

theorem hrelZero : LeafHrelZero := by
  intro R _ F U E f hf n
  exact LateralTheory.E.E8.ExciseCut.LeafConeZero_of R ((chains R).map f) F (fun m => hf m) n

theorem eqv_of_iso' {R : Type} [CommRing R] {E' E : Spc} (f : E' ⟶ E) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem eqv_of_square {R : Type} [CommRing R] {Z X Z0 X0 : Spc} (f : Z ⟶ X) (a : Z0 ⟶ Z) (g : Z0 ⟶ X0) (b : X0 ⟶ X)
    [IsIso g] (w : a ≫ f = g ≫ b) (F : Shv R) (ha : Eqv R a F) (hb : Eqv R b F) : Eqv R f F := fun n => by
  have h1 : Function.Bijective (pull R (g ≫ b) F n) := by
    have e : ⇑(pull R (g ≫ b) F n) = pull R g F n ∘ pull R b F n := funext (pull_comp R g b F n)
    rw [e]; exact (eqv_of_iso' g F n).comp (hb n)
  rw [← w] at h1
  have e : ⇑(pull R (a ≫ f) F n) = pull R a F n ∘ pull R f F n := funext (pull_comp R a f F n)
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff' (ha n) _).1 h1

theorem unit_of {k A : Type} [Field k] [CommRing A] {B : Scheme.{0}} (toK : B ⟶ Sp k) (s : Sp A ⟶ B) (q : ℕ)
    (hq : IsUnit (q : k)) : IsUnit (q : A) := by
  have := hq.map (Spec.preimage (s ≫ toK)).hom
  simpa using this

section geo
variable {B W Y : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B) {A : Type} [CommRing A] [IsLocalRing A]
  (s : Sp A ⟶ B)

abbrev rA (A : Type) [CommRing A] [IsLocalRing A] : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Sp A :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

def gF : pullback (prS p ι s ≫ pullback.snd p s) (rA A) ⟶ pullback (pullback.snd p s) (rA A) :=
  pullback.lift (pullback.fst _ _ ≫ prS p ι s) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])


variable {ι p s} in
def hF (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    pullback (pullback.snd p s) (rA A) ⟶ pullback (prS p ι s ≫ pullback.snd p s) (rA A) :=
  pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w)
      (by simp only [Category.assoc]; rw [hw, pullback.condition_assoc]))
    (pullback.snd _ _) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition])

theorem eZ : pullback.fst (prS p ι s ≫ pullback.snd p s) (rA A) ≫ pullback.snd (pullback.snd p s ≫ s) ι ≫ ι =
    pullback.snd (prS p ι s ≫ pullback.snd p s) (rA A) ≫ rA A ≫ s := by
  have c : pullback.snd (pullback.snd p s ≫ s) ι ≫ ι = prS p ι s ≫ pullback.snd p s ≫ s := pullback.condition.symm
  rw [c]
  have := pullback.condition_assoc (f := prS p ι s ≫ pullback.snd p s) (g := rA A) s
  simpa only [Category.assoc] using this

theorem gF_iso (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    IsIso (gF ι p s) := by
  refine ⟨⟨hF w hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      · rw [← cancel_mono ι]
        simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
        rw [hw, eZ]
    · simp only [hF, gF, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext <;> simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]
end geo

theorem proper_base_change_closed_fiber_strictly_henselian_equivalence_holds : ProperBaseChangeClosedFiberStrictlyHenselianEquivalence := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp A _ _ s hA w hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  have hqA := unit_of toK s q hq
  have := hp
  have : IsProper (pullback.snd p s) := inferInstance
  have : IsProper (prS p ι s ≫ pullback.snd p s) := inferInstance
  have h1 := hE2 q A hA hqA (pullback.snd p s) i
  have h2 := hE2 q A hA hqA (prS p ι s ≫ pullback.snd p s) i
  have := gF_iso ι p s w hw
  exact eqv_of_square (sch.map (prS p ι s)) (sch.map (pullback.fst _ (rA A))) (sch.map (gF ι p s))
    (sch.map (pullback.fst _ (rA A)))
    (by rw [← Functor.map_comp, ← Functor.map_comp, gF, pullback.lift_fst]) _ h2 h1

theorem LeafPtW_of : LateralTheory.E.SecondDegreeKilling.LeafPtW :=
  LateralTheory.E.LeafPtWPf.LeafPtW_of hrelZero closedLift proper_base_change_closed_fiber_strictly_henselian_equivalence_holds

end LateralTheory.E.PointEvaluationWitness
end
end
