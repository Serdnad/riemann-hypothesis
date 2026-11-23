module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import Mathlib.LinearAlgebra.Determinant
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
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
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_of_finite_sections {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P : Scheme.{0}}
    (s : P ⟶ Spec (.of Ω)) [LocallyOfFiniteType s]
    (h : Finite {x : Spec (.of Ω) ⟶ P // x ≫ s = 𝟙 _}) : Finite P := by
  have hJ : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  have hc : (closedPoints P).Finite := by
    have : Finite (closedPoints P) := Finite.of_equiv _ (pointEquivClosedPoint s)
    exact Set.toFinite _
  have hcl : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact hc.isClosed_biUnion fun x hx ↦ hx
  have hu : closedPoints P = Set.univ := by
    have := JacobsonSpace.closure_inter_closedPoints (X := P) isClosed_univ
    rwa [Set.univ_inter, hcl.closure_eq] at this
  exact Set.finite_univ_iff.mp (hu ▸ hc)

theorem locallyQuasiFinite_of_finite_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : LocallyQuasiFinite f := by
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Spec (.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have := h Ω y'
  have hP : Finite ↥(pullback f y') := by
    refine finite_of_finite_sections (pullback.snd f y') ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y'})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y', by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

theorem finite_fiber_of_finite_ker {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Ga G T : C} [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    (h : Finite {x : T ⟶ Ga // x ≫ p = 1}) (y : T ⟶ G) :
    Finite {x : T ⟶ Ga // x ≫ p = y} := by
  rcases isEmpty_or_nonempty {x : T ⟶ Ga // x ≫ p = y} with he | ⟨⟨x₀, hx₀⟩⟩
  · infer_instance
  refine Finite.of_injective (β := {x : T ⟶ Ga // x ≫ p = 1})
    (fun x ↦ ⟨x₀⁻¹ * x.1, by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hx₀, x.2, inv_mul_cancel]⟩) ?_
  intro a b hab
  exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))

theorem locallyQuasiFinite_of_finite_geometric_ker :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      LocallyOfFiniteType p.left → QuasiCompact p.left →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S),
        Finite {x : Over.mk t ⟶ Ga // x ≫ p = 1}) → LocallyQuasiFinite p.left := by
  intro S Ga G _ _ p hp hft _ h
  refine locallyQuasiFinite_of_finite_geometric_points p.left fun Ω _ _ y ↦ ?_
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  have := finite_fiber_of_finite_ker p (h Ω (y ≫ G.hom)) y'
  refine Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ Ga // x ≫ p = y'})
    (fun x ↦ ⟨Over.homMk x.1 (by
      change x.1 ≫ Ga.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2]), Over.OverMorphism.ext x.2⟩) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun z ↦ z.1.left) hab)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem ringHom_flat_of_injective_of_isUnit {T A B : Type*} [CommRing T] [IsDomain T] [IsBezout T]
    [CommRing A] [CommRing B] (φ : T →+* A) (ψ : A →+* B) (hψ : Function.Injective ψ)
    (h : ∀ t : T, t ≠ 0 → IsUnit (ψ (φ t))) : φ.Flat := by
  letI := φ.toAlgebra
  change Module.Flat T A
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨t, ht⟩, hta⟩
  have h1 : φ t * a = 0 := hta
  have h2 : ψ (φ t) * ψ a = 0 := by rw [← map_mul, h1, map_zero]
  have h3 : ψ a = 0 := (h t (nonZeroDivisors.ne_zero ht)).mul_right_eq_zero.mp h2
  exact hψ (by rw [h3, map_zero])

theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem flat_of_isSchemeTheoreticallyDominant_of_fractionRing (T K : Type) [CommRing T]
    [IsDomain T] [IsBezout T] [Field K] [Algebra T K] [IsFractionRing T K] {Z G : Scheme.{0}}
    (p : Z ⟶ G) [QuasiCompact p] [IsSchemeTheoreticallyDominant p] (s : G ⟶ Sp T) (z : Z ⟶ Sp K)
    (w : p ≫ s = z ≫ spMap (algebraMap T K)) : Flat s := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : G.affineOpens ↦ U)
    (iSup_affineOpens_eq_top G) fun U ↦ ?_
  have key : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top) ≫ p.app U =
      CommRingCat.ofHom (algebraMap T K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        z.appLE ⊤ (p ⁻¹ᵁ U) le_top := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, p.app_eq_appLE,
      Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
    refine (Scheme.Hom.appLE_comp_appLE p s ⊤ U (p ⁻¹ᵁ U) _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE z (spMap (algebraMap T K)) ⊤ ⊤ (p ⁻¹ᵁ U) _ _).symm)
    congr 1
  have hfl : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top).hom.Flat := by
    refine ringHom_flat_of_injective_of_isUnit (T := T) _ (p.app U).hom (p.app_injective U) ?_
    intro t ht
    have h1 : IsUnit (algebraMap T K t) :=
      IsUnit.mk0 _ (by simpa using ht)
    have h2 := h1.map ((Scheme.ΓSpecIso (.of K)).inv ≫ z.appLE ⊤ (p ⁻¹ᵁ U) le_top).hom
    have h3 := congrArg (fun φ ↦ CommRingCat.Hom.hom φ t) key
    exact h3 ▸ h2
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp hfl

theorem exists_flat_closure : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (X : Over (Sp T)) (Z : Over (Sp K)) (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj X), IsClosedImmersion i.left → ∃ (Ga : Over (Sp T)) (io : Ga ⟶ X) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧ Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io := by
  intro T K _ _ _ _ _ _ X Z i hi
  let j : Sp K ⟶ Sp T := spMap (algebraMap T K)
  have hjp : IsPreimmersion j := IsPreimmersion.of_isLocalization (nonZeroDivisors T)
  have hjf : Flat j := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors T))
  let i' : Z.left ⟶ pullback X.hom j := i.left
  have hi' : IsClosedImmersion i' := hi
  have hw : i' ≫ pullback.snd X.hom j = Z.hom := Over.w i
  let f : Z.left ⟶ X.left := i' ≫ pullback.fst X.hom j
  have hqc : QuasiCompact f := inferInstance
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  have hdom := isSchemeTheoreticallyDominant_toImage f
  have hsq : f.toImage ≫ (f.imageι ≫ X.hom) = Z.hom ≫ j := by
    rw [f.toImage_imageι_assoc, Category.assoc, pullback.condition, reassoc_of% hw]
  let Ga : Over (Sp T) := Over.mk (f.imageι ≫ X.hom)
  let io : Ga ⟶ X := Over.homMk f.imageι rfl
  let t : Z.left ⟶ pullback (f.imageι ≫ X.hom) j := pullback.lift f.toImage Z.hom hsq
  let m : pullback (f.imageι ≫ X.hom) j ⟶ pullback X.hom j :=
    pullback.map _ _ _ _ f.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩
  have hm : IsClosedImmersion m :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ m = i' := by
    apply pullback.hom_ext
    · simp [t, m, f, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [t, m, hw, pullback.lift_snd]
  have : IsClosedImmersion (t ≫ m) := htm ▸ hi'
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t m
  have hpb : IsPullback (𝟙 Z.left) t f.toImage (pullback.fst (f.imageι ≫ X.hom) j) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [t, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  refine ⟨Ga, io, (Over.isoMk (f := Z) (g := (Over.pullback j).obj Ga) (asIso t) ?_).symm,
    inferInstanceAs (IsClosedImmersion f.imageι),
    flat_of_isSchemeTheoreticallyDominant_of_fractionRing T K f.toImage _ Z.hom hsq, ?_⟩
  · exact pullback.lift_snd _ _ _
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    apply Over.OverMorphism.ext
    change i' = t ≫ _
    rw [← htm]
    congr 1

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology

namespace GlobalTheory

namespace RationalPoint

variable {k : Type} [Field k]

noncomputable def pt {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) : X.left :=
  y.left (IsLocalRing.closedPoint k)

theorem range_left_subset_iff {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (Z : Set X.left) :
    Set.range y.left ⊆ Z ↔ pt y ∈ Z := by
  refine ⟨fun h => h ⟨_, rfl⟩, fun h => ?_⟩
  rintro _ ⟨a, rfl⟩
  have : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [this]
  exact h

theorem pt_comp {X Y : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (f : X ⟶ Y) :
    pt (y ≫ f) = f.left (pt y) := rfl

@[reducible] noncomputable def zariski (X : Over (Sp k)) :
    TopologicalSpace (𝟙_ (Over (Sp k)) ⟶ X) :=
  TopologicalSpace.induced pt inferInstance

theorem continuous_comp {X Y : Over (Sp k)} (f : X ⟶ Y) :
    Continuous[zariski X, zariski Y] fun y => y ≫ f := by
  letI := zariski X
  letI := zariski Y
  exact continuous_induced_rng.2 (f.left.continuous.comp continuous_induced_dom)

theorem separatelyContinuousMul (B : Over (Sp k)) [GrpObj B] :
    @SeparatelyContinuousMul (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  have h : ∀ g y : 𝟙_ (Over (Sp k)) ⟶ B, y ≫ toUnit B ≫ g = g := fun g y => by
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit B) (𝟙 _), Category.id_comp]
  refine ⟨fun {g} => ?_, fun {g} => ?_⟩
  · convert continuous_comp ((toUnit B ≫ g) * 𝟙 B) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]
  · convert continuous_comp (𝟙 B * (toUnit B ≫ g)) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]

theorem continuousInv (B : Over (Sp k)) [GrpObj B] :
    @ContinuousInv (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  refine ⟨?_⟩
  convert continuous_comp (𝟙 B)⁻¹ using 2 with y
  rw [GrpObj.comp_inv, Category.comp_id]

variable [IsAlgClosed k]

theorem isClosed_pt {X : Over (Sp k)} [LocallyOfFiniteType X.hom] (y : 𝟙_ (Over (Sp k)) ⟶ X) :
    IsClosed {pt y} :=
  (pointEquivClosedPoint X.hom ⟨y.left, Over.w y⟩).2

theorem pt_injective {X : Over (Sp k)} [LocallyOfFiniteType X.hom] :
    Function.Injective (pt : (𝟙_ (Over (Sp k)) ⟶ X) → X.left) := fun x y h =>
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w x) (Over.w y) h)

theorem exists_pt_mem {X : Over (Sp k)} [LocallyOfFiniteType X.hom] {Z : Set X.left}
    (hZ : IsClosed Z) (hne : Z.Nonempty) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne hZ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), ?_⟩
  have : pt (Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc) :
      𝟙_ (Over (Sp k)) ⟶ X) = c := pointOfClosedPoint_apply X.hom c hc _
  rwa [this]

theorem pt_mem_image_iff {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) {Z : Set X.left} (hZ : IsClosed Z)
    (y : 𝟙_ (Over (Sp k)) ⟶ Y) :
    pt y ∈ f.left '' Z ↔ ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z ∧ x ≫ f = y := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := exists_pt_mem (Z := Z ∩ f.left ⁻¹' {pt y})
      (hZ.inter ((isClosed_pt y).preimage f.left.continuous)) ⟨z, hz, hzy⟩
    exact ⟨x, hx, pt_injective hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨pt x, hx, rfl⟩


omit [IsAlgClosed k] in
theorem isConstructible_image_of_isClosed {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    {Z : Set X.left} (hZ : IsClosed Z) : IsConstructible (f.left '' Z) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian X.left := {}
  have : IsNoetherian Y.left := {}
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : LocallyOfFinitePresentation f.left := inferInstance
  have : QuasiCompact f.left := inferInstance
  refine f.left.isConstructible_image ?_
  exact ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).of_compl

end RationalPoint


open RationalPoint in
theorem exists_isClosed_image_of_isClosed_subgroup :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G B : Over (Sp k)) [GrpObj G] [GrpObj B] (q : G ⟶ B), IsMonHom q → LocallyOfFiniteType G.hom → QuasiCompact G.hom → LocallyOfFiniteType B.hom → QuasiCompact B.hom → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → ∃ Z' : Set B.left, IsClosed Z' ∧ ∀ y : (𝟙_ (Over (Sp k)) ⟶ B), (∃ x ∈ C, x ≫ q = y) ↔ Set.range y.left ⊆ Z' := by
  intro k _ _ G B _ _ q _ _ _ _ _ C Z hZ hC
  letI := RationalPoint.zariski B
  haveI := RationalPoint.separatelyContinuousMul B
  haveI := RationalPoint.continuousInv B
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (fun x => x ≫ q) fun x y => MonObj.mul_comp x y q
  have hcl : IsClosed (C.map φ : Set (𝟙_ (Over (Sp k)) ⟶ B)) := by
    refine isClosed_subgroup_of_eq_preimage_isConstructible _ (f := RationalPoint.pt)
      continuous_induced_dom (RationalPoint.isConstructible_image_of_isClosed q hZ) ?_
    ext y
    rw [Set.mem_preimage, RationalPoint.pt_mem_image_iff q hZ]
    simp only [← RationalPoint.range_left_subset_iff, ← hC]
    rfl
  obtain ⟨Z', hZ', h⟩ := isClosed_induced_iff.1 hcl
  refine ⟨Z', hZ', fun y => ?_⟩
  rw [RationalPoint.range_left_subset_iff, ← Set.mem_preimage, h]
  rfl

end GlobalTheory
end

section

set_option autoImplicit false

namespace GlobalTheory

open scoped TensorProduct

theorem char_eq_one_of_inverse_det_one_of_basis {R S V Q A : Type} [CommRing R] [CommRing S] [Finite S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V] [AddCommGroup Q] [Module R Q] [CommGroup A]
    {r : ℕ} (b : Module.Basis (Fin r) S V) (e : Q ≃ₗ[R] V) (ψ : (Q ≃ₗ[R] Q) →* A)
    (h4 : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 4 ≤ Nat.card (S ⧸ 𝔪)) (f : V →ₗ[S] V) (hf : LinearMap.det f = 1)
    (k : Q ≃ₗ[R] Q) (hk : ∀ q, f (e (k q)) = e q) : ψ k = 1 := by
  classical
  let φ2 : Module.End S V →* Module.End R V :=
    { toFun := fun g => g.restrictScalars R, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let φ4 : (V ≃ₗ[R] V) →* (Q ≃ₗ[R] Q) :=
    { toFun := fun u => e.trans (u.trans e.symm)
      map_one' := by ext q; simp
      map_mul' := by intro u v; ext q; simp }
  let Φ : GL (Fin r) S →* (Q ≃ₗ[R] Q) :=
    φ4.comp ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V).toMonoidHom.comp
      ((Units.map φ2).comp (Units.map ((Matrix.toLinAlgEquiv b :
        Matrix (Fin r) (Fin r) S ≃ₐ[S] Module.End S V) : Matrix (Fin r) (Fin r) S →* Module.End S V))))
  have hdet : IsUnit (LinearMap.toMatrix b b f).det := by
    rw [LinearMap.det_toMatrix, hf]; exact isUnit_one
  let g : GL (Fin r) S := Matrix.nonsingInvUnit _ hdet
  have hg : (g : Matrix (Fin r) (Fin r) S).det = 1 := by
    show (LinearMap.toMatrix b b f).det = 1
    rw [LinearMap.det_toMatrix, hf]
  have h1 : (ψ.comp Φ) g = 1 := generalLinearGroup_char_eq_one_of_det_eq_one S r A (ψ.comp Φ) h4 g hg
  have h2 : Φ g * k = 1 := by
    ext q
    show e.symm ((Matrix.toLinAlgEquiv b (LinearMap.toMatrix b b f)) (e (k q))) = q
    rw [show LinearMap.toMatrix b b f = LinearMap.toMatrixAlgEquiv b f from rfl,
      Matrix.toLinAlgEquiv_toMatrixAlgEquiv, hk, LinearEquiv.symm_apply_apply]
  have h3 := congrArg ψ h2
  rw [map_mul, map_one] at h3
  simp only [MonoidHom.comp_apply] at h1
  rw [h1, one_mul] at h3
  exact h3

private theorem free_quotient_tensor_of_projective {R : Type} [CommRing R] [IsDomain R] (L' : Type)
    [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R)
    [Finite (R ⧸ I)] : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] L') := by
  refine Module.free_of_flat_of_finrank_eq (R ⧸ I) _ (Module.finrank R L') fun P => ?_
  let := Ideal.Quotient.field P.1
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1)
    ((R ⧸ I) ⧸ P.1) L').finrank_eq]
  have h := Module.rankAtStalk_baseChange (R := R) (M := L') (S := (R ⧸ I) ⧸ P.1)
    ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at h
  rw [h]
  exact (Ideal.finrank_fiber_eq_rankAtStalk (M := L') _).symm.trans (Ideal.finrank_fiber_eq_finrank _)

theorem char_eq_one_of_inverse_reduction_det_one : ∀ (R : Type) [CommRing R] [IsDomain R] (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R) [Finite (R ⧸ I)] (A : Type) [CommGroup A] (ψ : ((L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))) →* A) (t : L →ₗ[R] L') (γ : L' →ₗ[R] L') (k : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))), (∀ 𝔪 : Ideal (R ⧸ I), 𝔪.IsMaximal → 4 ≤ Nat.card ((R ⧸ I) ⧸ 𝔪)) → (∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule R L')) → (∀ a, t a ∈ (I • ⊤ : Submodule R L') → a ∈ (I • ⊤ : Submodule R L)) → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 → (∀ a, ∃ a', (Submodule.Quotient.mk a' : L ⧸ (I • ⊤ : Submodule R L)) = k (Submodule.Quotient.mk a) ∧ γ (t a') - t a ∈ (I • ⊤ : Submodule R L')) → ψ k = 1 := by
  intro R _ _ L L' _ _ _ _ _ _ I _ A _ ψ t γ k h4 hsurj hinj hdet hk
  have := free_quotient_tensor_of_projective L' I
  obtain ⟨r, ⟨b⟩⟩ : ∃ r : ℕ, Nonempty (Module.Basis (Fin r) (R ⧸ I) ((R ⧸ I) ⊗[R] L')) := by
    rcases subsingleton_or_nontrivial (R ⧸ I) with h | h
    · have := Module.subsingleton (R ⧸ I) ((R ⧸ I) ⊗[R] L')
      exact ⟨0, ⟨Module.Basis.empty _⟩⟩
    · exact ⟨_, ⟨Module.finBasis (R ⧸ I) ((R ⧸ I) ⊗[R] L')⟩⟩
  have hle : (I • ⊤ : Submodule R L) ≤ (I • ⊤ : Submodule R L').comap t := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let tb := (I • ⊤ : Submodule R L).mapQ (I • ⊤ : Submodule R L') t hle
  have tbij : Function.Bijective tb := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hinj a hx)
    · intro y
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a, ha⟩ := hsurj c
      exact ⟨Submodule.Quotient.mk a, ((Submodule.Quotient.eq _).mpr ha).symm⟩
  let e : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (R ⧸ I) ⊗[R] L' :=
    (LinearEquiv.ofBijective tb tbij).trans (TensorProduct.quotTensorEquivQuotSMul L' I).symm
  have he : ∀ a, e (Submodule.Quotient.mk a) = (1 : R ⧸ I) ⊗ₜ[R] t a := by
    intro a
    simp [e, tb, TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  have hz : ∀ x ∈ (I • ⊤ : Submodule R L'), (1 : R ⧸ I) ⊗ₜ[R] x = 0 := by
    intro x hx
    have h0 : (Submodule.Quotient.mk x : L' ⧸ (I • ⊤ : Submodule R L')) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, h0, map_zero]
  refine char_eq_one_of_inverse_det_one_of_basis b e ψ h4 (LinearMap.baseChange (R ⧸ I) γ) hdet k ?_
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a', ha', hγ⟩ := hk a
  rw [← ha', he, he, LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  exact hz _ hγ

end GlobalTheory
end
