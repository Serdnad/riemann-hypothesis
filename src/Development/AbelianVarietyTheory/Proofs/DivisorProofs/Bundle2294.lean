module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle669
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem isLocalRing_tsz (S M : Type) [CommRing S] [IsLocalRing S] [AddCommGroup M] [Module S M] [Module Sᵐᵒᵖ M]
    [IsCentralScalar S M] : IsLocalRing (TrivSqZeroExt S M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
    · exact Or.inl ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 h)
    · exact Or.inr ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by simpa using h))

theorem isLocalHom_map {S M N : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module Sᵐᵒᵖ M] [IsCentralScalar S M] [Module Sᵐᵒᵖ N] [IsCentralScalar S N] (L : M →ₗ[S] N) :
    IsLocalHom ((TrivSqZeroExt.map L : TrivSqZeroExt S M →ₐ[S] TrivSqZeroExt S N) : TrivSqZeroExt S M →+* TrivSqZeroExt S N) :=
  ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩

variable {X : Scheme.{0}}

def valAt {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (p : X) (h : x (IsLocalRing.closedPoint A) = p) :
    X.presheaf.stalk p →+* A :=
  ((X.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom

theorem valAt_comp {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (g : A →+* B)
    [IsLocalHom g] (x : Sp A ⟶ X) (p : X) (hx : x (IsLocalRing.closedPoint A) = p)
    (hy : (spMap g ≫ x) (IsLocalRing.closedPoint B) = p) (f : X.presheaf.stalk p) :
    valAt (spMap g ≫ x) p hy f = g (valAt x p hx f) := by
  subst hx
  let ψ : X.presheaf.stalk (x (IsLocalRing.closedPoint A)) ⟶ CommRingCat.of B :=
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x ≫ CommRingCat.ofHom g
  have hψl : IsLocalHom ψ.hom := by
    show IsLocalHom (g.comp (Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom)
    infer_instance
  have e1 : Spec.map ψ ≫ X.fromSpecStalk _ = spMap g ≫ x := by
    simp only [ψ, Spec.map_comp, Category.assoc]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e2 := congrArg (SpecToEquivOfLocalRing X (CommRingCat.of B)) e1
  have e3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)) (Spec.map ψ ≫ X.fromSpecStalk _) = ⟨_, ψ, hψl⟩ :=
    (SpecToEquivOfLocalRing X (CommRingCat.of B)).apply_symm_apply ⟨_, ψ, hψl⟩
  rw [e3] at e2
  obtain ⟨h1, h2⟩ := SpecToEquivOfLocalRing_eq_iff.1 e2.symm
  dsimp only [SpecToEquivOfLocalRing, Equiv.coe_fn_mk] at h2
  have h2' : Scheme.stalkClosedPointTo (R := CommRingCat.of B) (spMap g ≫ x) =
      (X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).inv ≫ ψ := h2
  simp only [valAt, h2', Iso.hom_inv_id_assoc]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, ψ]
  rfl

theorem valAt_congr {A : Type} [CommRing A] [IsLocalRing A] {x x' : Sp A ⟶ X} (e : x = x') (p : X)
    (h : x (IsLocalRing.closedPoint A) = p) (h' : x' (IsLocalRing.closedPoint A) = p) :
    valAt x p h = valAt x' p h' := by
  subst e; rfl

end GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

namespace GlobalTheory.CoordsOrigin

open GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem tanDer_add : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)),
    tanDer G (u + v) f = tanDer G u f + tanDer G v f := by
  intro R _ _ G _ _ u v f
  haveI : IsLocalRing (TrivSqZeroExt R (R × R)) := isLocalRing_tsz R (R × R)
  let P : overAt (𝟙 (Sp R)) (TrivSqZeroExt R (R × R)) ⟶ G :=
    (homAt (𝟙 (Sp R)) (tm (LinearMap.inl R R R)) ≫ tv u) * (homAt (𝟙 (Sp R)) (tm (LinearMap.inr R R R)) ≫ tv v)
  have hz : (0 : R →ₗ[R] R) = (0 : R) • (LinearMap.id : R →ₗ[R] R) := by simp
  have hid : ∀ w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G,
      homAt (𝟙 (Sp R)) (tm (LinearMap.id : R →ₗ[R] R)) ≫ w = w := by
    intro w
    simp only [tm]
    rw [TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
  have hfst : homAt (𝟙 (Sp R)) (tm (LinearMap.fst R R R)) ≫ P = tv u := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz]
    change _ * smT (𝟙 (Sp R)) 0 (tv v) = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.mul_one, hid]
  have hsnd : homAt (𝟙 (Sp R)) (tm (LinearMap.snd R R R)) ≫ P = tv v := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz]
    change smT (𝟙 (Sp R)) 0 (tv u) * _ = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.one_mul, hid]
  have hsum : homAt (𝟙 (Sp R)) (tm (LinearMap.coprod (LinearMap.id : R →ₗ[R] R) LinearMap.id)) ≫ P = tv (u + v) := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.coprod_inl, LinearMap.coprod_inr,
      hid, hid, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add]
  have hP : P.left (IsLocalRing.closedPoint (TrivSqZeroExt R (R × R))) = origin G := by
    have e : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left = (tv u).left := congrArg (fun q => q.left) hfst
    haveI := isLocalHom_map (LinearMap.fst R R R)
    have e0 : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) (IsLocalRing.closedPoint (DualNumber R)) =
        IsLocalRing.closedPoint (TrivSqZeroExt R (R × R)) :=
      Spec_closedPoint (f := CommRingCat.ofHom _)
    rw [← e0, ← tv_closedPoint G u, ← e]
    rfl
  have key : ∀ (L : R × R →ₗ[R] R) (w : TanM (𝟙 (Sp R)) G), homAt (𝟙 (Sp R)) (tm L) ≫ P = tv w →
      tanDer G w f = L (valAt P.left (origin G) hP f).snd := by
    intro L w hw
    haveI := isLocalHom_map L
    have e : (tv w).left = spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left := (congrArg (fun q => q.left) hw).symm
    have hy : (spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left) (IsLocalRing.closedPoint (DualNumber R)) = origin G :=
      e ▸ tv_closedPoint G w
    rw [tanDer_eq]
    change (valAt (tv w).left (origin G) (tv_closedPoint G w) f).snd = _
    rw [valAt_congr e (origin G) _ hy, valAt_comp _ P.left (origin G) hP hy]
    simp [tm]
  rw [key _ _ hsum, key _ _ hfst, key _ _ hsnd]
  simp

end GlobalTheory.CoordsOrigin
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

def tvStalk (v : TanM (𝟙 (Sp R)) G) : G.left.presheaf.stalk (origin G) ⟶ CommRingCat.of (DualNumber R) :=
  (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left

instance isLocalHom_tvStalk (v : TanM (𝟙 (Sp R)) G) : IsLocalHom (tvStalk G v).hom := by
  rw [tvStalk, CommRingCat.hom_comp]
  haveI := isLocalHom_of_isIso (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom
  haveI := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv v).left
  exact RingHom.isLocalHom_comp _ _

theorem specMap_fromSpecStalk_congr {X : Scheme.{0}} {A : CommRingCat.{0}} {x y : X} (h : x = y)
    (s : X.presheaf.stalk y ⟶ A) :
    Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ s) ≫ X.fromSpecStalk x =
      Spec.map s ≫ X.fromSpecStalk y := by
  subst h
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem tv_left_eq (v : TanM (𝟙 (Sp R)) G) :
    (tv v).left = Spec.map (tvStalk G v) ≫ G.left.fromSpecStalk (origin G) := by
  rw [tvStalk, specMap_fromSpecStalk_congr (tv_closedPoint G v).symm]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).symm

theorem isLocalHom_epsMul_zero : IsLocalHom (epsMul (0 : R)) :=
  ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩

theorem tvStalk_fst (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)) :
    ((tvStalk G u).hom f).fst = ((tvStalk G v).hom f).fst := by
  haveI := isLocalHom_epsMul_zero (R := R)
  have hl : ∀ w : TanM (𝟙 (Sp R)) G, IsLocalHom (tvStalk G w ≫ CommRingCat.ofHom (epsMul (0 : R))).hom := by
    intro w
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    infer_instance
  have hw : ∀ w : TanM (𝟙 (Sp R)) G, Spec.map (tvStalk G w ≫ CommRingCat.ofHom (epsMul (0 : R))) ≫
      G.left.fromSpecStalk (origin G) = (smT (𝟙 (Sp R)) 0 (tv w)).left := by
    intro w
    rw [smT_left, tv_left_eq G w, Spec.map_comp, Category.assoc]
  have e : Spec.map (tvStalk G u ≫ CommRingCat.ofHom (epsMul (0 : R))) ≫ G.left.fromSpecStalk (origin G) =
      Spec.map (tvStalk G v ≫ CommRingCat.ofHom (epsMul (0 : R))) ≫ G.left.fromSpecStalk (origin G) := by
    rw [hw, hw, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem]
  have e2 := (SpecToEquivOfLocalRing G.left (CommRingCat.of (DualNumber R))).symm.injective
    (a₁ := ⟨origin G, tvStalk G u ≫ CommRingCat.ofHom (epsMul (0 : R)), hl u⟩)
    (a₂ := ⟨origin G, tvStalk G v ≫ CommRingCat.ofHom (epsMul (0 : R)), hl v⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at e3
  have e4 : epsMul (0 : R) ((tvStalk G u).hom f) = epsMul (0 : R) ((tvStalk G v).hom f) := by
    have := congrArg (fun q : G.left.presheaf.stalk (origin G) ⟶ CommRingCat.of (DualNumber R) => q.hom f) e3
    simpa using this
  have e5 := congrArg TrivSqZeroExt.fst e4
  simpa [epsMul] using e5

theorem tanM_eq_of_tanDer : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (u v : TanM (𝟙 (Sp R)) G), (∀ f, tanDer G u f = tanDer G v f) → u = v := by
  intro R _ _ G _ _ u v h
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext
  apply Over.OverMorphism.ext
  have hs : tvStalk G u = tvStalk G v := by
    ext f
    · exact tvStalk_fst G u v f
    · have hu := tanDer_eq G u f
      have hv := tanDer_eq G v f
      exact hu.symm.trans ((h f).trans hv)
  rw [tv_left_eq G u, tv_left_eq G v, hs]

end GlobalTheory.CoordsOrigin
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem mk_algebraMap_eq_mk_baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B]
    (d : DualNumber K) :
    Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps}) (algebraMap (DualNumber K) B d) =
      Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})
        (baseMap K B (TrivSqZeroExt.fst d)) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨algebraMap (DualNumber K) B (TrivSqZeroExt.inl d.snd), ?_⟩
  rw [← map_mul, RingHom.comp_apply, ← map_sub]
  congr 1
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem chartPt_red : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l), spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ l = spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i := by
  intro K _ A _ A' _ i hi X Z h y1 m m' hm' him Ω δ n u θ Wo g B _ _ x l hx hxΩ hl
  set I : Ideal B := Ideal.span {algebraMap (DualNumber K) B DualNumber.eps} with hI
  set q : B →+* B ⧸ I := Ideal.Quotient.mk I with hq
  obtain ⟨h1, h2, h3⟩ := hl
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := fun p hp => hxΩ hp
  have hA : (spMap q ≫ l) ≫ A'.hom = (spMap q ≫ x ≫ i) ≫ A'.hom := by
    have e : q.comp (algebraMap (DualNumber K) B) =
        ((q.comp (baseMap K B)).comp (TrivSqZeroExt.fstHom K K K).toRingHom) :=
      RingHom.ext fun d => mk_algebraMap_eq_mk_baseMap K B d
    rw [Category.assoc, h1, Category.assoc, Category.assoc, hi.1.w, ← Category.assoc x, hx, GlobalTheory.DeRham.epsRed]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
  have hZ : (spMap q ≫ l) ≫ m' = (spMap q ≫ x ≫ i) ≫ m' := by
    have ha : ⊤ ≤ (spMap q ≫ l ≫ m') ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ h2
    have hb : ⊤ ≤ (spMap q ≫ x ≫ m) ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ hxm
    have e : ev (spMap q ≫ l ≫ m') Ω.1 ha = ev (spMap q ≫ x ≫ m) Ω.1 hb := by
      rw [GlobalTheory.FlagMod.ev_spMap q _ _ h2, GlobalTheory.FlagMod.ev_spMap q _ _ hxm]
      ext f
      simp only [RingHom.comp_apply]
      rw [← valR_eq_ev _ _ h2, ← valR_eq_ev _ _ hxm, h3 f, chartVal, map_add (f := _), map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl : _ ∈ I), zero_mul, add_zero]
    rw [Category.assoc, Category.assoc, Category.assoc, him,
      ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ l ≫ m') Ω.2 ha, ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ x ≫ m) Ω.2 hb, e]
  exact hm'.hom_ext hZ hA

end GlobalTheory.CechKS
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section
namespace GlobalTheory.CoordsOrigin

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

def derHom (D : G.left.presheaf.stalk (origin G) → R) (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = evO G x * D y + evO G y * D x) (hc : ∀ r, D (constO G r) = 0) :
    G.left.presheaf.stalk (origin G) →+* DualNumber R where
  toFun f := TrivSqZeroExt.inl (evO G f) + TrivSqZeroExt.inr (D f)
  map_one' := by
    have h1 : D 1 = 0 := by simpa using hc 1
    ext <;> simp [h1]
  map_mul' x y := by
    ext <;> simp [hmul]
    ring
  map_zero' := by
    have h0 : D 0 = 0 := by simpa using hadd 0 0
    ext <;> simp [h0]
  map_add' x y := by
    ext <;> simp [hadd]

end GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin
theorem exists_tan_of_derivation (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R) (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = evO G x * D y + evO G y * D x) (hc : ∀ r, D (constO G r) = 0) :
    ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  set ψ := derHom G D hadd hmul hc with hψdef
  have hψ : ∀ f, ψ f = TrivSqZeroExt.inl (evO G f) + TrivSqZeroExt.inr (D f) := fun f => rfl
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo' (R := R) (η[G]).left
  haveI hloc : IsLocalHom ψ := ⟨fun a ha => by
    have h2 : IsUnit (ψ a).fst := (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha
    simp only [hψ, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero] at h2
    exact isUnit_of_map_unit (evO G) a h2⟩
  haveI hloc' : IsLocalHom (CommRingCat.ofHom ψ).hom := hloc
  let p : Sp (DualNumber R) ⟶ G.left := spMap ψ ≫ G.left.fromSpecStalk (origin G)
  have hcomp : ψ.comp (constO G) = algebraMap R (DualNumber R) := by
    ext r <;> simp [hψ, evO_constO, hc, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : p ≫ G.hom = (overAt (𝟙 (Sp R)) (DualNumber R)).hom := by
    simp only [p, Category.assoc]
    rw [spMap_fromSpecStalk_origin_hom, hcomp]
    simp [overAt]
  let w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G := Over.homMk p hover
  have hw : smT (𝟙 (Sp R)) 0 w = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, one_left]
    have e1 : (epsMul (0 : R)).comp ψ = (algebraMap R (DualNumber R)).comp (evO G) := by
      ext f <;> simp [hψ, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    have e2 : spMap (evO G) ≫ G.left.fromSpecStalk (origin G) = (η[G]).left :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) (η[G]).left
    change spMap (epsMul (0 : R)) ≫ spMap ψ ≫ G.left.fromSpecStalk (origin G) = _
    have e3 : spMap (epsMul (0 : R)) ≫ spMap ψ = spMap ((epsMul (0 : R)).comp ψ) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have e4 : spMap ((algebraMap R (DualNumber R)).comp (evO G)) = spMap (algebraMap R (DualNumber R)) ≫ spMap (evO G) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [← Category.assoc, e3, e1, e4, Category.assoc, e2]
    simp [overAt]
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw, fun f => ?_⟩
  rw [tanDer_eq]
  have key : (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G (ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw)).symm)).hom ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw)).left =
      CommRingCat.ofHom ψ := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    rw [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom ψ) U _
  rw [key]
  simp [hψ]
end GlobalTheory.CoordsOrigin
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (ψ : G.left.presheaf.stalk (origin G) →+* Ω), spMap ψ ≫ G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (ψ.comp (constO G)) := by
  first | exact @GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom | exact GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom | (intros; apply GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  first | exact @GlobalTheory.GermConst.germ_constFn_origin | exact GlobalTheory.GermConst.germ_constFn_origin | (intros; apply GlobalTheory.GermConst.germ_constFn_origin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

theorem _root_.GlobalTheory.T.card_topVertexClasses_le_classNumberBound_norm_pow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → (Nat.card G.ClPlus : ℝ) ≤ hBd D (G.V (.top 0)).rank * (Ideal.absNorm G.modul : ℝ) ^ ((G.V (.top 0)).rank ^ 2) := by
  first | exact @GlobalTheory.ClassCount.card_clPlus_le | exact GlobalTheory.ClassCount.card_clPlus_le | (intros; apply GlobalTheory.ClassCount.card_clPlus_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens) (U : X.Opens), (∀ j, W j ≤ U) → U ≤ ⨆ j, W j → ∀ F : PtFn s, (∀ j, IsNat (W j) F) → ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  first | exact @GlobalTheory.CechKS.exists_sec_of_isNat | exact GlobalTheory.CechKS.exists_sec_of_isNat | (intros; apply GlobalTheory.CechKS.exists_sec_of_isNat <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.epsilonPart_deformationForm_class_eq_coboundary_of_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))), (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') = (constMor A).isMor.pull1 (Form.cl _ ω) + (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b) → ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (P Q : GPt A) (φ : P.Hom Q) (y : Sp (DualNumber P.B) ⟶ A'.left) (y' : Sp (DualNumber Q.B) ⟶ A'.left) (hy : IsLift i P y) (hy' : IsLift i Q y'), spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y' → ev b φ.triv = ((liftVal h ω'.1 hy').snd + G Q) - φ.ρ ((liftVal h ω'.1 hy).snd + G P) := by
  first | exact @GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary | exact GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary | (intros; apply GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lifts_of_cechKodairaSpencerDeformation : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (L : LB A.left) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → IsCechKS A A' i L u θ → ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι) (y : J → ∀ P : GPt A, Sp (DualNumber P.B) ⟶ A'.left), ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧ (∀ (k : J) (P : GPt A), P.In (W k) → IsLift i P (y k P)) ∧ (∀ (k : J) (P Q : GPt A) (φ : P.Hom Q), P.In (W k) → spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y k P = y k Q) ∧ ∀ (k k' : J) (P : GPt A) (U : A'.left.Opens) (f : Γ(A'.left, U)), P.In (W k) → P.In (W k') → P.In (i ⁻¹ᵁ U) → valR (y k P) U f - valR (y k' P) U f = (TrivSqZeroExt.inr (∑ a, (∑ b, algebraMap K P.B (θ a b) * dlog L (u b) (c k) (c k') P) * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B) := by
  first | exact @GlobalTheory.CechKS.cechKS_lifts | exact GlobalTheory.CechKS.cechKS_lifts | (intros; apply GlobalTheory.CechKS.cechKS_lifts <;> assumption)
end
