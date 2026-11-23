module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle255
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.AevalEqZeroOfHomogeneousComponent
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)}

theorem existsUnique_pt_of_triv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) :
    ∃! y : Pt X T.B, spMap T.π ≫ y.left = T.x := by
  have hb : Function.Bijective T.π :=
    ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ by simpa [hT] using (T.ker b).1 hb, T.surj⟩
  let e := RingEquiv.ofBijective T.π hb
  let ρ : T.B₀ →+* T.B := e.symm.toRingHom
  have h1 : ρ.comp T.π = RingHom.id _ := RingHom.ext e.symm_apply_apply
  have h2 : T.π.comp ρ = RingHom.id _ := RingHom.ext e.apply_symm_apply
  have k1 : spMap ρ ≫ spMap T.π = 𝟙 _ := by rw [← Cris.spMap_comp, h1, Cris.spMap_id]
  have k2 : spMap T.π ≫ spMap ρ = 𝟙 _ := by rw [← Cris.spMap_comp, h2, Cris.spMap_id]
  have hw : (spMap ρ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B) := by
    have : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      (congrArg (T.x ≫ ·) (Category.comp_id X.hom)).symm.trans T.w
    rw [Category.assoc, this, Cris.spMap_comp, ← Category.assoc, k1, Category.id_comp]
  let point : Pt X T.B := Over.homMk (spMap ρ ≫ T.x) hw
  refine ⟨point, ?_, ?_⟩
  · change spMap T.π ≫ spMap ρ ≫ T.x = T.x
    rw [← Category.assoc, k2, Category.id_comp]
  · intro y hy
    apply Over.OverMorphism.ext
    change y.left = spMap ρ ≫ T.x
    rw [← hy, ← Category.assoc, k1]
    exact (Category.id_comp _).symm

def liftHom (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (y : Pt X T.B) (h : spMap T.π ≫ y.left = T.x) : trivAt y ⟶ T :=
  Thick.trivHom (AlgHom.id R T.B) h

private def trivObject {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) :
    (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory :=
  ⟨trivAt x, show (trivAt x).J = ⊥ from rfl⟩

theorem mem_hodgeFiltration_iff_pointwiseCoboundary (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    CatCoh.H1.mk _ f ∈ F1 (X.hom ≫ 𝟙 _) ↔ ∃ k : Fn0 X, IsCob (whole X) (fv f) k := by
  rw [F1, LinearMap.mem_ker, toH1O, CoefMap.pullCohomologyOne_class, CatCoh.H1.mk_eq_zero]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun D _ _ x ↦ g (trivObject x), ?_⟩
    intro D _ _ D' _ _ φ x _
    let a : trivObject x ⟶ trivObject (spOver φ ≫ x) := ObjectProperty.homMk (trivMap φ x)
    exact (congrFun (congrFun (congrFun hg (trivObject x)) (trivObject (spOver φ ≫ x))) a).symm
  · rintro ⟨k, hk⟩
    choose y hy hu using existsUnique_pt_of_triv (R := R) (X := X)
    refine ⟨fun T ↦ (k T.obj.B (y T.obj T.property) +
      ev f (liftHom T.obj _ (hy T.obj T.property)) : T.obj.B), ?_⟩
    funext ⟨T, hT⟩ ⟨T', hT'⟩ ⟨φ⟩
    have h' : spMap T'.π ≫ (spOver φ.φ ≫ y T hT).left = T'.x := by
      change spMap T'.π ≫ spMap (φ.φ : T.B →+* T'.B) ≫ (y T hT).left = T'.x
      have hπ : T'.π.comp (φ.φ : T.B →+* T'.B) = φ.φ₀.comp T.π :=
        RingHom.ext fun b ↦ (φ.comm b).symm
      rw [← Category.assoc, ← Cris.spMap_comp, hπ, Cris.spMap_comp, Category.assoc, hy T hT, φ.pt]
    have key : ∀ (z : Pt X T'.B) (hz : spMap T'.π ≫ z.left = T'.x), spOver φ.φ ≫ y T hT = z →
        k T'.B z + ev f (liftHom T' z hz) - φ.φ (k T.B (y T hT) + ev f (liftHom T _ (hy T hT))) = ev f φ := by
      rintro _ hz rfl
      have e1 := ev_sq f (trivMap φ.φ (y T hT)) (liftHom T' _ hz) (liftHom T _ (hy T hT)) φ fun _ ↦ rfl
      have e2 := hk T.B T'.B φ.φ (y T hT) (sm_whole _)
      change fv f T.B T'.B φ.φ (y T hT) + _ = _ at e1
      rw [map_add φ.φ]
      linear_combination e1 - e2
    exact key _ (hy T' hT') (hu T' hT' _ h')

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatConst

theorem exists_section (Y : Scheme.{0}) {K : Type} (W : K → Y.Opens) (hW : ⨆ i, W i = ⊤)
    (κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Y) → D)
    (hκ : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D' (Spec.map φ ≫ x) = φ (κ D x)) :
    ∃ s : Γ(Y, ⊤), ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D x = (Scheme.ΓSpecIso D).hom (x.appTop s) := by
  let J : Type := {U : Y.affineOpens // ∃ i, U.1 ≤ W i}
  let U : J → Y.Opens := fun j ↦ j.1.1
  have hsm : ∀ j : J, ∃ i, ⊤ ≤ j.1.2.fromSpec ⁻¹ᵁ W i := fun j ↦ by
    obtain ⟨i, hi⟩ := j.2
    refine ⟨i, ?_⟩
    rw [← j.1.2.fromSpec_preimage_self]
    exact fun _ h ↦ hi h
  have hcov : ∀ y : Y, ∃ j : J, y ∈ U j := fun y ↦ by
    have hy : y ∈ ⨆ i, W i := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨V, hV, hyV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hi
    exact ⟨⟨⟨V, hV⟩, i, hle⟩, hyV⟩
  let sf : ∀ j : J, Γ(Y, U j) := fun j ↦ κ _ j.1.2.fromSpec
  have hgerm : ∀ (j : J) (y : Y) (hy : y ∈ U j),
      Y.presheaf.germ (U j) y hy (sf j) = κ _ (Y.fromSpecStalk y) := fun j y hy ↦ by
    rw [← j.1.2.fromSpecStalk_eq_fromSpecStalk hy]
    exact (hκ _ _ _ _ (hsm j)).symm
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hcov y)) sf (fun a b ↦ by
      refine TopCat.Presheaf.section_ext Y.sheaf _ _ _ fun y hy ↦ ?_
      exact ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm a y hy.1)).trans
        ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm b y hy.2)).symm)
  have hnat : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y),
      (Scheme.ΓSpecIso D').hom ((Spec.map φ ≫ x).appTop s) = φ ((Scheme.ΓSpecIso D).hom (x.appTop s)) := by
    intro D D' φ x
    rw [Scheme.Hom.comp_appTop]
    exact congrArg (fun f ↦ CommRingCat.Hom.hom f (x.appTop s)) (Scheme.ΓSpecIso_naturality φ)
  have hj : ∀ j : J, κ _ j.1.2.fromSpec = (Scheme.ΓSpecIso _).hom (j.1.2.fromSpec.appTop s) := fun j ↦ by
    have h1 : j.1.2.fromSpec.appTop ≫ (Scheme.ΓSpecIso _).hom = Y.presheaf.map (homOfLE le_top).op := by
      have h0 := congrArg (fun q ↦ (Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop q ≫ (Scheme.ΓSpecIso _).hom)
        j.1.2.fromSpec_toSpecΓ
      simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Category.assoc,
        Iso.inv_hom_id_assoc] at h0
      exact h0
    exact (hs j).symm.trans (congrArg (fun f ↦ CommRingCat.Hom.hom f s) h1).symm
  refine ⟨s, fun D x hx ↦ Module.eq_of_localization_maximal (R := D) (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap D (Localization.AtPrime P)) _ _ fun P hP ↦ ?_⟩
  let φ : D ⟶ CommRingCat.of (Localization.AtPrime P) := CommRingCat.ofHom (algebraMap D _)
  refine (hκ _ _ φ x hx).symm.trans (Eq.trans ?_ (hnat _ _ φ x))
  obtain ⟨j, hy⟩ := hcov ((Spec.map φ ≫ x) (IsLocalRing.closedPoint (CommRingCat.of (Localization.AtPrime P))))
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem _ hy
  have hr : Set.range (Spec.map φ ≫ x) ⊆ Set.range j.1.2.fromSpec := by
    rw [j.1.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have : z ∈ (Spec.map φ ≫ x) ⁻¹ᵁ U j := by rw [htop]; trivial
    exact this
  haveI : IsOpenImmersion j.1.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec (U := j.1.1) j.1.2
  have hf := IsOpenImmersion.lift_fac j.1.2.fromSpec _ hr
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift j.1.2.fromSpec _ hr)
  rw [← hψ] at hf
  rw [← hf]
  exact (hκ _ _ ψ _ (hsm j)).trans ((congrArg ψ (hj j)).trans (hnat _ _ ψ _).symm)

theorem const_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → Function.Surjective X.hom.appTop.hom → ∀ k : Fn0 X, IsCob W (Fn1.zero X) k → ∃ r : R, ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), Sm W x → k D x = algebraMap R D r := by
  intro R _ X K W hW hs k hk
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ X.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), @Pt R _ X D _ (al D x) := fun D x ↦ by
    letI : Algebra R D := al D x
    refine Over.homMk (U := SpAlg R D) (V := X) x ?_
    change x ≫ X.hom = Spec.map (Spec.preimage (x ≫ X.hom))
    exact (Spec.map_preimage (x ≫ X.hom)).symm
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ X.left) → D := fun D x ↦ @k D _ (al D x) (pt D x)
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
      (x : Pt X D) (x' : Pt X D'), Sm W x → spMap φ ≫ x.left = x'.left → k D' x' = φ (k D x) := by
    intro D _ _ D' _ _ φ x x' hx h
    have h1 : x.left ≫ X.hom = spMap (algebraMap R D) := Over.w x
    have h2 : x'.left ≫ X.hom = spMap (algebraMap R D') := Over.w x'
    have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change spMap φ ≫ spMap _ = spMap _
      rw [← h1, ← h2, ← h, Category.assoc]
    let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
    have h4 := hk D D' ψ x hx
    have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
    rw [h5] at h4
    exact (sub_eq_zero.1 h4.symm)
  obtain ⟨s, hs'⟩ := exists_section X.left W hW κ fun D D' φ x hx ↦
    @key D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom (pt D x) (pt D' _) hx rfl
  obtain ⟨r, rfl⟩ := hs s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom r, fun D _ inst x hx ↦ ?_⟩
  have h1 : κ (CommRingCat.of D) x.left = k D x :=
    @key D _ inst D _ (al (CommRingCat.of D) x.left) (RingHom.id D) x (pt (CommRingCat.of D) x.left) hx (by
      change Spec.map (𝟙 _) ≫ _ = _
      rw [Spec.map_id, Category.id_comp]; rfl)
  rw [← h1, hs' (CommRingCat.of D) x.left hx]
  have h2 : x.left ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R D)) := Over.w x
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R D))
  rw [← h2, Scheme.Hom.comp_appTop] at h3
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3

end GlobalTheory.PtExt.NatConst
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OmRes

variable {R : Type} [CommRing R]

theorem val_map_coc {X : Scheme.{0}} {s : X ⟶ Sp R} (E E' : SqExt R) (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B)
    (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (a : Thick.triv E.C y hy ⟶ Thick.triv E'.C y' hy') (ha : ∀ c, a.φ c = φ c)
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Z1 (O (dp0 R) s)) :
    ∃ b : E'.B, E'.val y' hy' f = φ (E.val y hy f) + (ev f a : E'.C) - E'.i b := by
  have e₀ : spMap (φ₀ : E.B →+* E'.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
      spMap (E'.π : E'.C →+* E'.B) ≫ y' := by
    rw [← e, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ := E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') e₀
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ Thick.triv E'.B _ (E'.red_w hy') := Thick.trivHom φ₀ e₀
  have k1 := ev_sq f a (E'.idHom hy') (E.idHom hy) Φ ha
  have k2 := ev_sq f b (E'.secHom (E'.red_w hy') E'.i E'.π_i) (E.secHom (E.red_w hy) E.i E.π_i)
    Φ fun c ↦ (hi c).symm
  refine ⟨ev f b, ?_⟩
  rw [SqExt.val_apply, SqExt.val_apply, map_sub]
  have k1' : (ev f a : E'.C) + (ev f (E'.idHom hy') : E'.C) = φ (ev f (E.idHom hy)) + (ev f Φ : E'.C) := k1
  have k2' : E'.i (ev f b) + (ev f (E'.secHom (E'.red_w hy') E'.i E'.π_i) : E'.C) =
    φ (ev f (E.secHom (E.red_w hy) E.i E.π_i)) + (ev f Φ : E'.C) := k2
  linear_combination k2' - k1'

attribute [local instance] cotOp cotCentral cotTower

variable {D D' : Type} [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R D']

def rho (φ : D →ₐc[R] D') : (cotExt R D).C →ₐ[R] (cotExt R D').C := TrivSqZeroExt.map (cotMap φ)

theorem cotSnd_cotPt (a : D) : cotSnd R D (cotPt R D a) = dUnit (R := R) a := by
  simp [cotSnd, cotPt, TrivSqZeroExt.algebraMap_eq_inl, dUnit]

theorem cotSnd_rho (φ : D →ₐc[R] D') (c : (cotExt R D).C) : cotSnd R D' (rho φ c) = cotMap φ (cotSnd R D c) :=
  TrivSqZeroExt.snd_map _ _

theorem rho_cotPt (φ : D →ₐc[R] D') (a : D) : rho φ (cotPt R D a) = cotPt R D' (φ a) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (TrivSqZeroExt.fst_map _ _).trans ?_
    simp [cotPt, TrivSqZeroExt.algebraMap_eq_inl]
  · exact (cotSnd_rho φ _).trans (by rw [cotSnd_cotPt, cotMap_d]; exact (cotSnd_cotPt _).symm)

theorem cotVal_map {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (φ : D →ₐc[R] D') (y : Pt X D) :
    cotVal f (spOver (φ : D →ₐ[R] D') ≫ y) =
      cotMap φ (cotVal f y) + dUnit (R := R) (fv f D D' (φ : D →ₐ[R] D') y) := by
  let z : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  let z' : Pt X (cotExt R D').C := spOver (cotPt R D') ≫ spOver (φ : D →ₐ[R] D') ≫ y
  have e : spMap (rho φ : (cotExt R D).C →+* (cotExt R D').C) ≫ z.left = z'.left := by
    change spMap _ ≫ spMap _ ≫ y.left = spMap _ ≫ spMap _ ≫ y.left
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    exact RingHom.ext (rho_cotPt φ)
  let a : trivAt z ⟶ trivAt z' := Thick.trivHom (rho φ) e
  obtain ⟨b, hb⟩ := val_map_coc (cotExt R D) (cotExt R D') (rho φ) (AlgHom.id R R)
    (fun c ↦ (TrivSqZeroExt.fst_map _ _).symm) (fun r ↦ TrivSqZeroExt.map_inl _ _) z.left z.w z'.left z'.w a
    (fun _ ↦ rfl) e f
  have k : rho φ (fv f D _ (cotPt R D) y) + (ev f a : (cotExt R D').C) =
      cotPt R D' (fv f D D' (φ : D →ₐ[R] D') y) + fv f D' _ (cotPt R D') (spOver (φ : D →ₐ[R] D') ≫ y) :=
    ev_sq f (trivMap (cotPt R D) y) a (trivMap (φ : D →ₐ[R] D') y) (trivMap (cotPt R D') _) (rho_cotPt φ)
  have h0 : cotSnd R D' ((cotExt R D').i b) = 0 := rfl
  change cotSnd R D' ((cotExt R D').val z'.left z'.w f - _) =
    cotMap φ (cotSnd R D ((cotExt R D).val z.left z.w f - _)) + _
  rw [← cotSnd_rho, ← cotSnd_cotPt, ← map_add (f := _), ← sub_zero (cotSnd R D' (_ + _)), ← h0, ← map_sub, hb, map_sub (rho φ)]
  congr 1
  linear_combination k

theorem cotMap_res_om (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    cotMap (G.res n) (d.om (n + 1)) = d.om n := by
  have h := cotVal_map d.f (G.res n) (t.y (n + 1))
  rw [t.res n, d.res n] at h
  rw [Dat.om, Dat.om, h, map_sub, cotMap_d]
  simp only [dUnit, map_sub]
  abel

end GlobalTheory.PtExt.OmRes
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HilbFam

theorem sz_jet_conj : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → ω ≠ 0 → Sz l lam ρ ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2) → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ / ω ^ wt (2 * s) κ) := by
  intro hE F _ _ _ hF s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω hω0 hst
  obtain ⟨h0, hadd, hmul, hmono, hint, hsum⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hpow : ∀ (x : ℂ) (n : ℕ), Sz l lam ρ x → Sz l lam (n * ρ) (x ^ n) := by
    intro x n hx
    induction n with
    | zero => simpa using hint 1
    | succ n ih =>
      have := hmul _ _ _ _ ih hx
      rw [pow_succ]
      convert this using 1
      push_cast
      ring
  have hneg : Sz l lam ρ (-((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2)) := by
    simpa only [zero_sub] using (hadd ρ _ _ (h0 ρ) hst).2
  rw [GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion hE F hF s N L hs (Nat.pos_of_ne_zero (NeZero.ne N)) hL τ κ (wB N y), Finset.sum_div]
  refine hsum _ _ _ _ fun μ hμ ↦ ?_
  have hle : ∀ i, μ i ≤ κ i := Finset.mem_Iic.mp hμ
  have hs' : ∑ i, κ i = ∑ i, (κ i - μ i) + ∑ i, μ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.sub_add_cancel (hle i)).symm
  have hh := GlobalTheory.T.norm_hilbertEisensteinValue_le_of_integral_j hE F hF s N L hs hL z hz l lam μ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω
  have key := hmul _ _ _ _ (hmul _ _ _ _ (hint (∏ i, rco (2 * s) (κ i) (μ i))) (hpow _ (∑ i, (κ i - μ i)) hneg)) hh
  rw [GlobalTheory.wB_nonhol_correction N y τ]
  have hw : wt (2 * s) κ = 2 * (∑ i, (κ i - μ i)) + wt (2 * s) μ := by
    unfold wt
    rw [hs']
    ring
  convert key using 1
  · rw [hs']
    push_cast
    ring
  · rw [hw, pow_add, pow_mul, ← neg_div, div_pow]
    field_simp

end GlobalTheory.HilbFam
end

section

set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_isChowFormInt_of_ringKrullDim_eq (K : Type) [Field K] (N D : ℕ)
    (P : Ideal (MvPolynomial (Fin N) K)) (hP : P.IsPrime)
    (hh : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ)) :
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  classical
  have hI : P.IsHomogeneous (homogeneousSubmodule (Fin N) K) := by
    intro n g hg
    have h1 : (DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K) =
        homogeneousComponent n g := MvPolynomial.decomposition.decompose'_apply g n
    rw [h1]
    exact hh g hg n
  have hX : ∃ j, X j ∉ P := by
    by_contra hc
    push Not at hc
    have h0 := GlobalTheory.ringKrullDim_quotient_le_zero_of_forall_X_mem hc
    rw [hdim] at h0
    have h1 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h0
    have h2 : D + 1 ≤ 0 := by exact_mod_cast h1
    omega
  have hdim' : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (Fintype.card (Fin (D + 1)) : ℕ) := by
    rw [Fintype.card_fin]; exact hdim
  have hprime : (GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P).IsPrime := GlobalTheory.Chow.isPrime_elimIdeal hX
  have hne : GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P ≠ ⊥ := GlobalTheory.Chow.elimIdeal_ne_bot hI hX hdim'.le
  obtain ⟨f, hf⟩ := (GlobalTheory.Chow.isPrincipal_elimIdeal hdim').principal
  have hf' : GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P = Ideal.span {f} := hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne (by rw [hf', Ideal.span_singleton_eq_bot])
  have hfmem : f ∈ GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P := hf' ▸ Ideal.subset_span rfl
  have hfp : Prime f := (Ideal.span_singleton_prime hf0).1 (hf' ▸ hprime)
  obtain ⟨a, ha⟩ := GlobalTheory.Chow.exists_isWeightedHomogeneous_of_dvd
    (GlobalTheory.Chow.blockWeight : Fin (D + 1) × Fin N → Fin (D + 1) → ℕ) (f := f) (fun a => by
      rw [← Ideal.mem_span_singleton, ← hf']
      exact GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal hfmem a)
  have ha' : GlobalTheory.Chow.IsBlockHomogeneous f a := ha
  have hconst : ∀ i, a i = a 0 := by
    intro i
    have h1 := GlobalTheory.Chow.map_rename_elimIdeal (Equiv.swap i 0) P
    rw [hf', Ideal.map_span, Set.image_singleton] at h1
    obtain ⟨c, hc, hcf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_span_eq h1
    have h2 : GlobalTheory.Chow.IsBlockHomogeneous f (a ∘ (Equiv.swap i 0).symm) := by
      rw [hcf]
      exact IsWeightedHomogeneous.C_mul (ha'.rename (Equiv.swap i 0)) c
    have h3 := congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique hf0 ha' h2) i
    simpa using h3
  refine ⟨a 0, f, ?_, hfp.irreducible, fun u => ?_⟩
  · rw [isMultiHomogeneous_iff_block, ← (funext hconst : a = fun _ => a 0)]
    exact ha'
  · rw [← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u, hf']
    refine ⟨fun hu p hp => ?_, fun hu => hu f (Ideal.subset_span rfl)⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    rw [map_mul, hu, mul_zero]

end GlobalTheory.ChowHt
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | exact GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | (intros; apply GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.euler_char_h0_h1_bound_higher : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  first | exact @GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le | exact GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le | (intros; apply GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le <;> assumption)
end
