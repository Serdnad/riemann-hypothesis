module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitOnProductEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.exists_complete_dvr_finite_extension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (_ : Algebra W L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ (∀ x : L, RingHom.IsIntegralElem ((algebraMap K L).comp (algebraMap V K)) x → x ∈ Set.range (algebraMap W L)) ∧ ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] Q, _root_.GlobalTheory.SS.PotModel W L ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) Q → _root_.GlobalTheory.SS.PotModel V K A Q := by
  intro V K _ _ _ _ _ _ _ _ L _ _ _
  classical
  letI : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' rfl
  have hinj : Function.Injective (algebraMap V L) :=
    (algebraMap K L).injective.comp (IsFractionRing.injective V K)
  haveI : CharZero V := (algebraMap V K).charZero
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinj
  haveI : Algebra.IsAlgebraic V L := (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  haveI : Module.Finite V (integralClosure V L) := IsIntegralClosure.finite V K L (integralClosure V L)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := V) (M := integralClosure V L)
  obtain ⟨W, _, hc, -, hfin, -, hloc, -, hint⟩ :=
    _root_.GlobalTheory.exists_complete_dvr_finite_subalgebra V L (t.image Subtype.val)
  have hcl : ∀ x : L, IsIntegral V x → x ∈ W := by
    intro x hx
    have key : ∀ y ∈ Submodule.span V (t : Set (integralClosure V L)), (y : L) ∈ W := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hint _ (Finset.mem_image_of_mem _ hy) y.2
      | zero => exact W.zero_mem
      | add a b _ _ ha hb => exact W.add_mem ha hb
      | smul r a _ ha => exact W.smul_mem ha r
    exact key ⟨x, hx⟩ (by rw [ht]; trivial)
  have hWint : ∀ w : W, IsIntegral V (w : L) := fun w =>
    (Algebra.IsIntegral.isIntegral (R := V) w).map W.val
  haveI : IsIntegralClosure W V L :=
    ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ⟨⟨x, hcl x hx⟩, rfl⟩, by
      rintro ⟨w, rfl⟩
      exact hWint w⟩⟩
  haveI : IsFractionRing W L :=
    IsIntegralClosure.isFractionRing_of_algebraic V W (fun x hx => hinj (by rw [hx, map_zero]))
  have hcomp : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) :=
    RingHom.ext fun _ => rfl
  refine ⟨W, inferInstance, inferInstance, ‹_›, hc, inferInstance, inferInstance, inferInstance,
    hcomp, hfin, fun a b h => hinj (congrArg Subtype.val h), hloc,
    fun x hx => ⟨⟨x, hcl x hx⟩, rfl⟩, ?_⟩
  intro A _ Q hP
  exact _root_.GlobalTheory.SS.potModel_trans V K W L hcomp hfin hloc A _
    (pullback.fst _ _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _) Q hP

end GlobalTheory.SS
end

section

section

open TensorProduct

namespace GlobalTheory.UnitRigidity

end GlobalTheory.UnitRigidity

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnitRigidity

theorem geometricallyConnected_of_isPullback_of_surjective {P X Y Z : Scheme.{0}} {a : P ⟶ X}
    {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) [Surjective g]
    [GeometricallyConnected b] : GeometricallyConnected f := by
  refine ⟨fun k _ y W fst snd hW => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd g y).surjective (Classical.arbitrary _)
  let p := (pullback g y).fromSpecResidueField z
  have : Surjective (p ≫ pullback.snd g y) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have h1 := (IsPullback.of_hasPullback snd (p ≫ pullback.snd g y)).paste_horiz hW
  rw [Category.assoc, ← pullback.condition, ← Category.assoc] at h1
  have h2 := IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ h1.w) h
  have : ConnectedSpace ↥(pullback snd (p ≫ pullback.snd g y)) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h2
  exact (pullback.fst snd (p ≫ pullback.snd g y)).surjective.connectedSpace
    (pullback.fst snd (p ≫ pullback.snd g y)).continuous

theorem isPullback_act {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) :
    IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  refine ⟨⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.one_mul]
  · have hW := ex (W.fst / W.snd) (by rw [GrpObj.div_comp, W.condition, div_self'])
    refine ⟨lift hW.choose W.snd, ?_, lift_snd _ _, ?_⟩
    · change lift _ _ ≫ (_ * _) = _
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, hW.choose_spec, div_mul_cancel]
    · intro (m : W.pt ⟶ T ⊗ G) (h1 : m ≫ (_ * _) = W.fst) (h2 : m ≫ snd T G = W.snd)
      change m = _
      refine CartesianMonoidalCategory.hom_ext _ _ (inj ?_) (by rw [lift_snd, h2])
      rw [lift_fst, hW.choose_spec, ← h1, ← h2, MonObj.comp_mul, mul_div_cancel_right,
        Category.assoc]

theorem smooth_geometricallyConnected_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G]
    (h : E.IsGt G) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  obtain ⟨D⟩ := h
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := E.isAbelian.smooth
  have := E.isAbelian.geomConnected
  obtain ⟨-, -, -, -, h1, -, -, h2, -⟩ := (splitTorus_properties S).1 E.X
  have : Smooth (splitTorus S E.X).hom := SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have H := (isPullback_act D.i D.q D.isKernel).map (Over.forget S)
  have a1 : Smooth (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus S E.X).hom G.hom))
  have a2 : GeometricallyConnected (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (GeometricallyConnected (pullback.snd (splitTorus S E.X).hom G.hom))
  have b1 : Smooth D.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact D.q.left)⟩ a1
  have b2 : GeometricallyConnected D.q.left :=
    @geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ H D.q_surjective a2
  rw [← Over.w D.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

open scoped TensorProduct

theorem noZeroDivisors_tensor {K A : Type} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (g : Spec (.of A) ⟶ X) [IsOpenImmersion g]
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (F : Type) [Field F] [Algebra K F] : NoZeroDivisors (F ⊗[K] A) := by
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  let m : Spec (.of (F ⊗[K] A)) ⟶ pullback y f := (pullbackSpecIso K F A).inv ≫
    pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by simp [y]) (by simp [hg])
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := isIntegral_of_isOpenImmersion m
  have : IsDomain (F ⊗[K] A) := (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this
  infer_instance

theorem unit_eq_one_of_axes {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] (e : Spec (.of K) ⟶ X) (he : e ≫ f = 𝟙 _)
    (a₁ a₂ : X ⟶ pullback f f) (h₁ : a₁ ≫ pullback.fst f f = 𝟙 X) (h₁' : a₁ ≫ pullback.snd f f = f ≫ e)
    (h₂ : a₂ ≫ pullback.fst f f = f ≫ e) (h₂' : a₂ ≫ pullback.snd f f = 𝟙 X)
    (u : Γ(pullback f f, ⊤)) (hu : IsUnit u) (u₁ : a₁.appTop.hom u = 1) (u₂ : a₂.appTop.hom u = 1) :
    u = 1 := by
  first
  | exact @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | (apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one ..)

end GlobalTheory.UnitRigidity

namespace GlobalTheory


open UnitRigidity in
theorem unit_eq_one_of_axes_of_isGt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ u : Γ((G ⊗ G).left, ⊤), IsUnit u → (lift (𝟙 G) (1 : G ⟶ G)).left.appTop.hom u = 1 → (lift (1 : G ⟶ G) (𝟙 G)).left.appTop.hom u = 1 → u = 1 := by
  intro K _ _ E G _ h u hu u₁ u₂
  obtain ⟨_, _⟩ := UnitRigidity.smooth_geometricallyConnected_of_isGt E G h
  have := geometricallyIntegral_of_smooth G.hom
  have h1 : (1 : G ⟶ G).left = G.hom ≫ (η[G] : 𝟙_ _ ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  refine UnitRigidity.unit_eq_one_of_axes G.hom (η[G] : 𝟙_ _ ⟶ G).left (Over.w _) _ _ ?_ ?_ ?_ ?_ u hu u₁ u₂
  · exact congrArg (·.left) (lift_fst (𝟙 G) (1 : G ⟶ G))
  · exact (congrArg (·.left) (lift_snd (𝟙 G) (1 : G ⟶ G))).trans h1
  · exact (congrArg (·.left) (lift_fst (1 : G ⟶ G) (𝟙 G))).trans h1
  · exact congrArg (·.left) (lift_snd (1 : G ⟶ G) (𝟙 G))

end GlobalTheory
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrpDense

variable {Z U : Scheme.{0}} {j : U ⟶ Z}

theorem exists_generic [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] :
    ∃ (W : Scheme.{0}) (k : W ⟶ U), QuasiCompact (k ≫ j) ∧ IsSchemeTheoreticallyDominant (k ≫ j) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  refine ⟨Spec U.functionField, U.fromSpecStalk (genericPoint U), ?_, ?_⟩
  · constructor
    intro s _ _
    have : Subsingleton (Spec U.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum U.functionField))
    exact Set.subsingleton_of_subsingleton.isCompact
  · have hk : DenseRange (U.fromSpecStalk (genericPoint U)) := by
      refine Dense.mono ?_ (dense_iff_closure_eq.mpr (isGenericPoint_def.mp (genericPoint_spec U)))
      rintro _ rfl
      rw [Scheme.range_fromSpecStalk]
      exact specializes_refl _
    have hj : DenseRange j :=
      (Scheme.Hom.isOpenEmbedding j).isOpen_range.dense (Set.range_nonempty _)
    have : IsDominant (U.fromSpecStalk (genericPoint U)) := ⟨hk⟩
    have : IsDominant j := ⟨hj⟩
    exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem hom_ext_of_points [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] {X Y : Over Z} [Flat X.hom]
    [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  obtain ⟨W, k, hqc, hstd⟩ := exists_generic j
  have := hqc
  have := hstd
  apply Over.OverMorphism.ext
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant Y.hom (by simp) (pullback.fst X.hom (k ≫ j)) ?_
  have := h (Over.mk (pullback.snd X.hom (k ≫ j) ≫ k))
    (Over.homMk (pullback.fst X.hom (k ≫ j)) (by simpa using pullback.condition))
  simpa using congrArg (fun t => t.left) this

variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

theorem pushPt_surjective (h : IsPullback φ A.hom G.hom j) (T : Over U) (x₀ : Over.mk (T.hom ≫ j) ⟶ G) :
    ∃ x : T ⟶ A, pushPt h.w x = x₀ := by
  refine ⟨Over.homMk (h.lift x₀.left T.hom (by simp)) (h.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact h.lift_fst _ _ _

variable [GrpObj A] (w : φ ≫ G.hom = A.hom ≫ j)

theorem pushPt_mul {m : G ⊗ G ⟶ G}
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    {T : Over U} (x y : T ⟶ A) : lift (pushPt w x) (pushPt w y) ≫ m = pushPt w (x * y) := by
  have hsq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare
    constructor
    · rw [← Over.comp_left, lift_fst]
      rfl
    · rw [← Over.comp_left, lift_snd]
      rfl
  have key := hm _ hsq
  have hL : lift (pushPt w x) (pushPt w y) =
      Over.homMk (U := Over.mk (T.hom ≫ j)) (V := Over.mk ((A ⊗ A).hom ≫ j)) (lift x y).left
        (by
          show (lift x y).left ≫ ((A ⊗ A).hom ≫ j) = T.hom ≫ j
          rw [← Category.assoc, Over.w]) ≫
        lift (pushPt w (fst A A)) (pushPt w (snd A A)) := by
    apply hom_ext
    · rw [lift_fst, Category.assoc, lift_fst]
      apply Over.OverMorphism.ext
      change x.left ≫ φ = (lift x y).left ≫ (fst A A).left ≫ φ
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · rw [lift_snd, Category.assoc, lift_snd]
      apply Over.OverMorphism.ext
      change y.left ≫ φ = (lift x y).left ≫ (snd A A).left ≫ φ
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  apply Over.OverMorphism.ext
  rw [hL, Over.comp_left, Over.comp_left, Category.assoc, key]
  change (lift x y).left ≫ (μ[A]).left ≫ φ = (x * y).left ≫ φ
  rw [Hom.mul_def, Over.comp_left, Category.assoc]

theorem pushPt_inv {i : G ⟶ G} (hi : φ ≫ i.left = (ι[A]).left ≫ φ) {T : Over U} (x : T ⟶ A) :
    pushPt w x ≫ i = pushPt w x⁻¹ := by
  apply Over.OverMorphism.ext
  change (x.left ≫ φ) ≫ i.left = (x⁻¹).left ≫ φ
  rw [Category.assoc, hi, Hom.inv_def, Over.comp_left, Category.assoc]

theorem pushPt_one {e : 𝟙_ (Over Z) ⟶ G} (he : j ≫ e.left = (η[A]).left ≫ φ) (T : Over U) :
    toUnit _ ≫ e = pushPt w (1 : T ⟶ A) := by
  apply Over.OverMorphism.ext
  change (toUnit (Over.mk (T.hom ≫ j))).left ≫ e.left = (1 : T ⟶ A).left ≫ φ
  rw [Hom.one_def, Over.comp_left, Category.assoc, ← he]
  have h1 : (toUnit (Over.mk (T.hom ≫ j))).left = T.hom ≫ j := by
    simp
  have h2 : (toUnit T).left = T.hom := by
    simp
  rw [h1, h2, Category.assoc]

end GlobalTheory.GrpDense

namespace GlobalTheory

open GrpDense

theorem grpObj_of_dense_open :
    ∀ (Z U : Scheme.{0}) [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] (G : Over Z) [Smooth G.hom]
      [IsSeparated G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left),
      IsPullback φ A.hom G.hom j → ∀ (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G),
      (∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → j ≫ e.left = (η[A]).left ≫ φ →
      ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  intro Z U _ _ j _ G _ _ A _ _ φ h m i e hm hi he
  have : Flat G.hom := inferInstance
  have : Flat (𝟙_ (Over Z)).hom := GlobalTheory.ExtUnique.flat_tensorUnit
  have : Flat (G ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj G G
  have : Flat ((G ⊗ G) ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj (G ⊗ G) G
  have : Flat (𝟙_ (Over Z) ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj _ G
  have : Flat (G ⊗ 𝟙_ (Over Z)).hom := GlobalTheory.ExtUnique.flat_tensorObj G _
  have hext : ∀ {X : Over Z} [Flat X.hom] (f g : X ⟶ G),
      (∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) → f = g :=
    fun f g H => hom_ext_of_points j H
  have mulP : ∀ {T : Over U} (x y : T ⟶ A),
      lift (pushPt h.w x) (pushPt h.w y) ≫ m = pushPt h.w (x * y) :=
    fun x y => pushPt_mul h.w hm x y
  have invP : ∀ {T : Over U} (x : T ⟶ A), pushPt h.w x ≫ i = pushPt h.w x⁻¹ :=
    fun x => pushPt_inv h.w hi x
  have oneP : ∀ (T : Over U), toUnit _ ≫ e = pushPt h.w (1 : T ⟶ A) :=
    fun T => pushPt_one h.w he T
  have surj := pushPt_surjective h
  letI inst : GrpObj G :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        apply hext
        intro T t
        obtain ⟨y, hy⟩ := surj T (t ≫ snd _ _)
        have ht : t = lift (toUnit _) (pushPt h.w y) :=
          hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hy])
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        rw [oneP, mulP, _root_.one_mul]
      mul_one := by
        apply hext
        intro T t
        obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _)
        have ht : t = lift (pushPt h.w x) (toUnit _) :=
          hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [ht]
        simp only [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        rw [oneP, mulP, _root_.mul_one]
      mul_assoc := by
        apply hext
        intro T t
        obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := surj T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := surj T (t ≫ snd _ _)
        have ht : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          refine hom_ext _ _ ?_ (by rw [lift_snd, hz])
          rw [lift_fst]
          exact hom_ext _ _ (by rw [lift_fst, hx, Category.assoc]) (by rw [lift_snd, hy, Category.assoc])
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
          mulP, _root_.mul_assoc]
      left_inv := by
        apply hext
        intro T t
        obtain ⟨x, rfl⟩ := surj T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, invP, mulP, _root_.inv_mul_cancel, oneP]
      right_inv := by
        apply hext
        intro T t
        obtain ⟨x, rfl⟩ := surj T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, invP, mulP, _root_.mul_inv_cancel, oneP] }
  refine ⟨inst, rfl, rfl, rfl, ⟨?_⟩, ?_⟩
  · change (β_ G G).hom ≫ m = m
    apply hext
    intro T t
    obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := surj T (t ≫ snd _ _)
    have ht : t = lift (pushPt h.w x) (pushPt h.w y) :=
      hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [ht, lift_braiding_hom_assoc, mulP, mulP, _root_.mul_comm]
  · unfold IsGrpPullback
    refine ⟨h, ?_⟩
    intro T x y x₀ y₀ hx hy
    have e₀ : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    have e₁ : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    subst e₀ e₁
    rw [Hom.mul_def]
    exact congrArg (fun t => t.left) (mulP x y)

end GlobalTheory
end
end

section

universe u

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtTorus

theorem isTorus_splitTorus (k : Type u) [Field k] (X : Type u) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] : IsTorus (splitTorus (Spec (CommRingCat.of k)) X) :=
  ⟨GlobalTheory.Diag.isCommMonObj _ X, inferInstance, inferInstance,
    ⟨k, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
      GlobalTheory.Diag.baseChangeIso _ X, GlobalTheory.Diag.baseChangeIso_isMonHom _ X⟩⟩

def torusExtOfSplit {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
    (E : TorusExtension G) : TorusExt G :=
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  { B := E.B
    isAbelian := E.isAbelian
    q := E.q
    q_hom := E.q_hom
    q_flat := E.q_flat
    q_surjective := E.q_surjective
    q_quasiCompact := E.q_quasiCompact
    T₀ := splitTorus (Spec (CommRingCat.of k)) E.X
    isTorus := isTorus_splitTorus k E.X
    i := E.i
    i_hom := E.i_hom
    isKernel := E.isKernel }

theorem nonempty_torusExt_of_split : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExtension G) → Nonempty (TorusExt G) :=
  fun _ _ _ _ h => h.map torusExtOfSplit

end GlobalTheory.SplitExtTorus
end
end
