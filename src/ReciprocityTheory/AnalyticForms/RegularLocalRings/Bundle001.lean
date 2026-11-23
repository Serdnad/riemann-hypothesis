module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.ENatToNat
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem mem_nonZeroDivisors_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hb : Function.Bijective φ) {a : R} (ha : a ∈ nonZeroDivisors R) : φ a ∈ nonZeroDivisors S := by
  have key : ∀ x : S, x * φ a = 0 → x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hb.2 x
    have hz : z * a = 0 := hb.1 (by rw [map_mul, map_zero]; exact hx)
    rw [(mem_nonZeroDivisors_iff.mp ha).2 z hz, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

theorem isAffineOpen_of_iso {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) : IsAffineOpen V :=
  IsAffine.of_isIso e.hom

theorem sec_mem_nonZeroDivisors {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) {a : A} (ha : a ∈ nonZeroDivisors A) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso A).inv a)) ∈ nonZeroDivisors Γ(W, V) := by
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  have hb : Function.Bijective ((V.topIso.hom.hom).comp ((e.hom.appTop).hom.comp
      (Scheme.ΓSpecIso A).inv.hom)) :=
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).comp
      ((ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv))
  exact mem_nonZeroDivisors_of_bijective _ hb ha

theorem sec_algebraMap_of_iso {X W : Scheme.{0}} (π : W ⟶ X) (U : X.affineOpens) (V : W.Opens)
    (hV : V ≤ π ⁻¹ᵁ U.1) (A : Type) [CommRing A] [Algebra Γ(X, U.1) A]
    (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) ≫ U.2.fromSpec = V.ι ≫ π)
    (r : Γ(X, U.1)) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r))) = π.appLE _ V hV r := by
  have hVa := isAffineOpen_of_iso V e
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hVa hV
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Mono U.2.fromSpec := IsOpenImmersion.mono _
  have h3 : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) =
      hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV) := by
    rw [← cancel_mono U.2.fromSpec, Category.assoc, he, Category.assoc, h1, ← Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec]
  have n1 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
      ((Scheme.ΓSpecIso _).inv r) = (Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  have n2 : (Spec.map (π.appLE _ V hV)).appTop ((Scheme.ΓSpecIso _).inv r) =
      (Scheme.ΓSpecIso _).inv (π.appLE _ V hV r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have n3 : ∀ x : Γ(W, V), hVa.isoSpec.hom.appTop ((Scheme.ΓSpecIso _).inv x) = V.topIso.inv x := by
    intro x
    rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, Iso.inv_hom_id, CommRingCat.id_apply]
  calc V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r)))
      = V.topIso.hom ((e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n1]
    _ = V.topIso.hom ((hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV)).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by rw [h3]; rfl
    _ = π.appLE _ V hV r := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [n2, n3]
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem germ_mem_nonZeroDivisors {W : Scheme.{0}} {V : W.Opens} (hV : IsAffineOpen V) {a : Γ(W, V)}
    (ha : a ∈ nonZeroDivisors Γ(W, V)) (w : W) (hw : w ∈ V) :
    W.presheaf.germ V w hw a ∈ nonZeroDivisors (W.presheaf.stalk w) := by
  let := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨w, hw⟩
  have := hV.isLocalization_stalk ⟨w, hw⟩
  have h := IsLocalization.map_nonZeroDivisors_le (hV.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl
    (W.presheaf.stalk w) (Submonoid.mem_map_of_mem (algebraMap Γ(W, V) (W.presheaf.stalk w)) ha)
  exact h

theorem res_mem_nonZeroDivisors {W : Scheme.{0}} {V O : W.Opens} (h : O ≤ V) (hV : IsAffineOpen V)
    {a : Γ(W, V)} (ha : a ∈ nonZeroDivisors Γ(W, V)) :
    W.presheaf.map (homOfLE h).op a ∈ nonZeroDivisors Γ(W, O) := by
  have key : ∀ x : Γ(W, O), x * W.presheaf.map (homOfLE h).op a = 0 → x = 0 := by
    intro x hx
    refine TopCat.Presheaf.section_ext W.sheaf O x 0 (fun w hw => ?_)
    have hg := germ_mem_nonZeroDivisors hV ha w (h hw)
    have h1 : W.presheaf.germ O w hw x * W.presheaf.germ V w (h hw) a = 0 := by
      rw [← W.presheaf.germ_res_apply (homOfLE h) w hw a, ← map_mul, hx, map_zero]
    change W.presheaf.germ O w hw x = W.presheaf.germ O w hw 0
    rw [(mem_nonZeroDivisors_iff.mp hg).2 _ h1, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

end

end ReciprocityTheory.AnForm.R
end

section

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))

def constSec (U : S.Opens) : ℂ →+* Γ(S, U) :=
  (s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

def constRes (x : S) : ℂ →+* S.residueField x :=
  (S.evaluation ⊤ x trivial).hom.comp (constSec s ⊤)


open Classical in
def valHom (x : S) : S.residueField x → ℂ := by
  classical
  exact if h : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ then h.choose else fun _ => 0

def val {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U) : ℂ :=
  valHom s x (S.evaluation U x hx f)

theorem fromSpecResidueField_appTop_iso (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop, Scheme.evaluation]
  have hid : (Spec (S.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
  simp [hid]

theorem constRes_eq (x : S) (hx : IsClosed ({x} : Set S)) [LocallyOfFiniteType s] :
    constRes s x = (residueFieldIsoBase s x hx).inv.hom := by
  have hφ := Scheme.ΓSpecIso_naturality (Spec.preimage (S.fromSpecResidueField x ≫ s))
  rw [Spec.map_preimage] at hφ
  have hpre : Spec.preimage (S.fromSpecResidueField x ≫ s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (S.fromSpecResidueField x ≫ s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField x)).hom := by
    rw [hφ, Iso.inv_hom_id_assoc]
  have hA : s.appLE ⊤ ⊤ le_top = s.appTop := (s.app_eq_appLE (U := ⊤)).symm
  have hc : constRes s x = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ ⊤ le_top ≫
      S.evaluation ⊤ x trivial).hom := rfl
  rw [hc, hA, ← fromSpecResidueField_appTop_iso x]
  show _ = (Spec.preimage (S.fromSpecResidueField x ≫ s)).hom
  rw [hpre, Scheme.Hom.comp_appTop, Category.assoc]

theorem valHom_unique [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S))
    (ψ : S.residueField x →+* ℂ) (h : ψ.comp (constRes s x) = RingHom.id ℂ) :
    ψ = (residueFieldIsoBase s x hx).hom.hom := by
  ext y
  have h1 : (residueFieldIsoBase s x hx).inv.hom ((residueFieldIsoBase s x hx).hom.hom y) = y := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      RingHom.id_apply]
  have h2 := congrArg (fun f : ℂ →+* ℂ => f ((residueFieldIsoBase s x hx).hom.hom y)) h
  simp only [RingHom.comp_apply, RingHom.id_apply, constRes_eq s x hx, h1] at h2
  exact h2

theorem valHom_spec [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    ((residueFieldIsoBase s x hx).hom.hom).comp (constRes s x) = RingHom.id ℂ := by
  rw [constRes_eq s x hx, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]

theorem valHom_eq [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    valHom s x = (residueFieldIsoBase s x hx).hom.hom := by
  have hex : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ :=
    ⟨_, valHom_spec s x hx⟩
  unfold valHom
  rw [dite_eq_left hex, valHom_unique s x hx _ hex.choose_spec]

theorem evaluation_res {U V : S.Opens} (h : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    S.evaluation V x hx (S.presheaf.map (homOfLE h).op f) = S.evaluation U x (h hx) f := by
  have key : S.presheaf.map (homOfLE h).op ≫ S.evaluation V x hx = S.evaluation U x (h hx) := by
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  rw [← key]
  rfl

theorem constSec_res (U : S.Opens) (c : ℂ) :
    constSec s U c = S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (constSec s ⊤ c) := by
  simp only [constSec, RingHom.comp_apply]
  rw [← s.appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : U ≤ ⊤)).op]
  rfl

theorem isClosed_image_of_closed {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t] (x : S)
    (hc : IsClosed ({x} : Set S)) : IsClosed ({g.base x} : Set T) := by
  haveI : JacobsonSpace T := AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace t
  haveI : AlgebraicGeometry.LocallyOfFiniteType (g ≫ t) := by rw [hg]; infer_instance
  haveI : AlgebraicGeometry.LocallyOfFiniteType g := AlgebraicGeometry.locallyOfFiniteType_of_comp g t
  have hx : x ∈ closedPoints S := by simpa [mem_closedPoints_iff] using hc
  have := g.closePoints_subset_preimage_closedPoints hx
  simpa [mem_closedPoints_iff] using this

theorem residueFieldMap_constRes {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) (x : S) :
    (g.residueFieldMap x).hom.comp (constRes t (g.base x)) = constRes s x := by
  have hA : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)), y.appLE ⊤ ⊤ le_top = y.appTop :=
    fun Y y => (y.app_eq_appLE (U := ⊤)).symm
  have hc : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)) (z : Y), constRes y z =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ y.appTop ≫ Y.evaluation ⊤ z trivial).hom := by
    intro Y y z
    rw [← hA]; rfl
  rw [hc, hc, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc]
  rw [Scheme.evaluation_naturality g x (V := ⊤) trivial, ← hg, Scheme.Hom.comp_appTop,
    Category.assoc]
  rfl

theorem val_ringHom [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    ∃ φ : Γ(S, U) →+* ℂ, ∀ f, φ f = val s f x hx := by
  refine ⟨(residueFieldIsoBase s x hc).hom.hom.comp (S.evaluation U x hx).hom, fun f => ?_⟩
  unfold val
  rw [valHom_eq s x hc]
  rfl

theorem val_const [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) (c : ℂ) : val s (constSec s U c) x hx = c := by
  unfold val
  rw [constSec_res s U c, evaluation_res le_top _ x hx, valHom_eq s x hc]
  exact DFunLike.congr_fun (valHom_spec s x hc) c

theorem val_restrict {U V : S.Opens} (hVU : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    val s (S.presheaf.map (homOfLE hVU).op f) x hx = val s f x (hVU hx) := by
  unfold val
  rw [evaluation_res hVU f x hx]

theorem val_eq_zero_iff [LocallyOfFiniteType s] {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) : val s f x hx = 0 ↔ S.evaluation U x hx f = 0 := by
  unfold val
  rw [valHom_eq s x hc]
  exact map_eq_zero_iff _ (residueFieldIsoBase s x hc).commRingCatIsoToRingEquiv.injective

theorem val_comp {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T) (hg : g ≫ t = s)
    [LocallyOfFiniteType s] [LocallyOfFiniteType t] {U : T.Opens} {V : S.Opens} (hVU : V ≤ g ⁻¹ᵁ U)
    (f : Γ(T, U)) (x : S) (hx : x ∈ V) (hc : IsClosed ({x} : Set S)) :
    IsClosed ({g.base x} : Set T) ∧ val s (g.appLE U V hVU f) x hx = val t f (g.base x) (hVU hx) := by
  have hcl := isClosed_image_of_closed s t g hg x hc
  refine ⟨hcl, ?_⟩
  have hmor : g.appLE U V hVU ≫ S.evaluation V x hx =
      T.evaluation U (g.base x) (hVU hx) ≫ g.residueFieldMap x := by
    rw [Scheme.evaluation_naturality g x (V := U) (hVU hx :), Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  have hres : (residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom =
      (residueFieldIsoBase t (g.base x) hcl).hom.hom := by
    apply valHom_unique t (g.base x) hcl
    rw [RingHom.comp_assoc, residueFieldMap_constRes s t g hg x, valHom_spec s x hc]
  unfold val
  rw [valHom_eq s x hc, valHom_eq t (g.base x) hcl, ← hres]
  show _ = ((residueFieldIsoBase s x hc).hom.hom.comp (g.residueFieldMap x).hom)
    ((T.evaluation U (g.base x) (hVU hx)).hom f)
  rw [RingHom.comp_apply, ← RingHom.comp_apply (g.residueFieldMap x).hom, ← CommRingCat.hom_comp,
    ← hmor]
  rfl

end

end ReciprocityTheory.AnForm.R
end

section

open AlgebraicGeometry CategoryTheory TensorProduct
universe u
namespace ReciprocityTheory.AnForm.R.FinalTheorems

def EffCartier {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}

def Blowup {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  EffCartier (I.comap π) ∧
    ∀ (W : Scheme.{u}) (g : W ⟶ X), EffCartier (I.comap g) → ∃! h : W ⟶ X', h ≫ π = g

def Rsp (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) (x : Fin n → R) : Prop :=
  Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R

def Snc {Y : Scheme.{u}} (D : Y.IdealSheafData) : Prop :=
  ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      Rsp (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}

def GeomRegFib (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (P : Ideal A) [P.IsPrime] (K : Type u) [Field K] [Algebra P.ResidueField K] [Algebra A K]
    [IsScalarTower A P.ResidueField K], (⊤ : IntermediateField P.ResidueField K).FG →
    IsNoetherianRing (B ⊗[A] K) ∧
      ∀ (Q : Ideal (B ⊗[A] K)) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)

def QERing (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧
  (∀ (P : Ideal A) [P.IsPrime],
    Module.Flat (Localization.AtPrime P)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)) ∧
    GeomRegFib (Localization.AtPrime P)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))) ∧
  (∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
    IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)})

def QE (X : Scheme.{u}) : Prop := ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ QERing Γ(X, U.1)

def FFinRes (X : Scheme.{u}) : Prop :=
  ∀ (x : X) (p : ℕ) [Fact p.Prime] [CharP (X.residueField x) p], (frobenius (X.residueField x) p).Finite

def Sing (X : Scheme.{u}) : Set X := {x | ¬ IsRegularLocalRing (X.presheaf.stalk x)}

noncomputable def stalkId {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ (U : X.affineOpens) (hx : x ∈ U.1), Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U)

def LSncAt (X : Scheme.{u}) {q : ℕ} (L : Fin q → TopologicalSpace.Closeds X) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x) ∧
    ∃ (n : ℕ) (r : Fin n → X.presheaf.stalk x) (e : {i : Fin q // x ∈ L i} ↪ Fin n),
      Rsp (X.presheaf.stalk x) n r ∧
        ∀ i : {i : Fin q // x ∈ L i},
          stalkId (Scheme.IdealSheafData.vanishingIdeal (L i.1)) x = Ideal.span {r (e i)}

def CompList {X : Scheme.{u}} (B : Set X) {q : ℕ} (V : Fin q → TopologicalSpace.Closeds X) : Prop :=
  (∀ j, IsIrreducible (V j : Set X)) ∧ (⋃ j, (V j : Set X)) = B ∧ ∀ i j, (V i : Set X) ⊆ V j → i = j

def SncAt {Y : Scheme.{u}} (D : Y.IdealSheafData) (y : Y) : Prop :=
  IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : Finset (Fin n)),
      Rsp (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ U.1 y hy (f i)) ∧
        D.ideal U = Ideal.span {∏ i ∈ J, f i}

end ReciprocityTheory.AnForm.R.FinalTheorems
end
