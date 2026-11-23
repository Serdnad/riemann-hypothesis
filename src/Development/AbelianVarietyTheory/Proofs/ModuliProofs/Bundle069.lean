module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle062
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle066
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.invariant_vectorField_abelianVariety_algebraic : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ w : (Fin P₀.g → ℂ), ∃ d, LocDer P₀.A.hom P₀.A.hom (𝟙 _) (fun _ => 0) ⊤ d ∧ ∀ O f z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left ((𝟙 P₀.A.left) ⁻¹ᵁ O) (d O f) = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  first | exact @GlobalTheory.KS.invariant_field_algebraic | exact GlobalTheory.KS.invariant_field_algebraic | (intros; apply GlobalTheory.KS.invariant_field_algebraic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace GaloisDescent

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := by
  unfold act
  exact pullback.lift_fst _ _ _

theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := by
  unfold act
  exact pullback.lift_snd _ _ _

theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) := by
  have hpb : IsPullback (pullback.snd T.hom π) (pullback.fst T.hom π) π T.hom :=
    (IsPullback.of_hasPullback T.hom π).flip
  exact ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 (pullback T.hom π) T.left (pullback.fst T.hom π) (act hc T)
    (pullback.snd T.hom π) T.hom (fun a => act_snd hc T a) pullback.condition.symm).2 hpb
    (fun a => act_fst hc T a)

theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g := by
  obtain ⟨f', -, huniq⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).1 Z (π ≫ f)
    (fun a => by rw [← Category.assoc, hc.inv])
  exact (huniq f rfl).trans (huniq g h.symm).symm

theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  have h1 := up_left H x
  have h2 := up_left H y
  rw [e] at h1
  apply Over.OverMorphism.ext
  exact cover_ext (isGaloisCover_act hc T) (h1.symm.trans h2)

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  refine forall_congr' fun a => ?_
  change preHom _ w = pushHom _ _ w ↔ _
  rw [Over.OverMorphism.ext_iff]
  unfold preHom pushHom
  simp only [MonoidHom.mk'_apply, Over.comp_left, Over.homMk_left]
  unfold pushPt
  simp

theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hinv : ∀ a, act hc T a ≫ (w.left ≫ φ) = w.left ≫ φ := fun a => by
    rw [← Category.assoc, (mem_equivariant hc hν).1 hw a, Category.assoc, hφ]
  obtain ⟨f', hf', -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ _ Ga _ (isGaloisCover_act hc T)).1 G'.left (w.left ≫ φ) hinv
  have hw' : w.left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w w
  have hbase : f' ≫ G'.hom = T.hom := by
    apply cover_ext (isGaloisCover_act hc T)
    rw [← Category.assoc, hf', Category.assoc, H.w, ← Category.assoc, hw', pullback.condition]
  refine ⟨Over.homMk f' hbase, GlobalTheory.QuotientDescent.hom_ext H ?_⟩
  rw [up_left]
  simp [hf']

theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := by
  rw [mem_equivariant]
  intro a
  have hu : (up H z).left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w (up H z)
  apply H.hom_ext
  · rw [Category.assoc, Category.assoc, hφ, up_left, ← Category.assoc, act_fst]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, ← Category.assoc (up H z).left, hu]
    exact act_snd hc T a

theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have hsurj : ∀ (T : Over Y) (w : equivariant hc hν T), ∃ z : T ⟶ G', up H z = w.1 :=
    fun T w => exists_up hc H hν hφ w.2
  let e : ∀ T : Over Y, (T ⟶ G') ≃ equivariant hc hν T := fun T =>
    Equiv.ofBijective (fun z => ⟨up H z, up_mem hc H hν hφ z⟩)
      ⟨fun x y h => up_injective hc H (congrArg Subtype.val h),
       fun w => (hsurj T w).imp fun z hz => Subtype.ext hz⟩
  have hmap : ∀ {T T' : Over Y} (u : T' ⟶ T) (w : equivariant hc hν T),
      (Over.pullback π).map u ≫ w.1 ∈ equivariant hc hν T' := by
    intro T T' u w
    obtain ⟨z, hz⟩ := hsurj T w
    rw [← hz, ← up_comp]
    exact up_mem hc H hν hφ (u ≫ z)
  let F : (Over Y)ᵒᵖ ⥤ CommGrpCat :=
    { obj := fun T => CommGrpCat.of (equivariant hc hν T.unop)
      map := fun {T T'} u => CommGrpCat.ofHom
        { toFun := fun w => ⟨(Over.pullback π).map u.unop ≫ w.1, hmap u.unop w⟩
          map_one' := Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_one)
          map_mul' := fun w w' => Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_mul w.1 w'.1) }
      map_id := fun T => by
        ext w
        simp
      map_comp := fun u u' => by
        ext w
        simp }
  let α : (F ⋙ forget CommGrpCat).RepresentableBy G' :=
    { homEquiv := fun {T} => e T
      homEquiv_comp := fun {T T'} u z => Subtype.ext (up_comp H u z) }
  let inst : CommGrpObj G' := CommGrpObj.ofRepresentableBy G' F α
  refine ⟨inferInstance, inferInstance, H, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hmul : up H (x₀ * y₀) = up H x₀ * up H y₀ :=
    congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy G' (F ⋙ forget₂ CommGrpCat GrpCat) α).hom.app
      (Opposite.op (Over.mk (T.hom ≫ π)))).hom.map_mul x₀ y₀)
  let s₀ : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)) :=
    Over.homMk (pullback.lift (𝟙 T.left) T.hom (by simp)) (pullback.lift_snd _ _ _)
  have hs₀ : ∀ (z : Over.mk (T.hom ≫ π) ⟶ G') (t : T ⟶ G), z.left = t.left ≫ φ → s₀ ≫ up H z = t := by
    intro z t hz
    apply GlobalTheory.QuotientDescent.hom_ext H
    rw [Over.comp_left, Category.assoc, up_left, hz]
    exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)
  have key : s₀ ≫ up H (x₀ * y₀) = x * y := by
    rw [hmul, ← hs₀ x₀ x hx, ← hs₀ y₀ y hy]
    exact (preHom s₀).map_mul (up H x₀) (up H y₀)
  have hk := congrArg (fun t : T ⟶ G => t.left ≫ φ) key
  rw [← hk, Over.comp_left, Category.assoc, up_left]
  exact ((pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)).symm

end GaloisDescent

open GaloisDescent

theorem abelianScheme_descends_galoisCover :
    ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ X Y π sY Ga _ ρ G _ ν hc hq hab hν hν1 hνmul
  obtain ⟨hcomm, hsm, hpr, hgc⟩ := hab
  have := hc.finite
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have hdown : ∀ a, ν a ≫ G.hom = G.hom ≫ ρ a := fun a => (hν a).1.w
  have hinvG : ∀ a, ν a ≫ G.hom ≫ π = G.hom ≫ π := fun a => by
    rw [← Category.assoc, hdown, Category.assoc, hc.inv]
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ G.left) (a : Ga), y ≫ ν a = y → a = 1 := by
    intro k _ _ y a hy
    have hya : (y ≫ G.hom) ≫ ρ a = y ≫ G.hom := by
      rw [Category.assoc, ← hdown, ← Category.assoc, hy]
    have hy1 : (y ≫ G.hom) ≫ ρ 1 = y ≫ G.hom := by rw [hc.one, Category.comp_id]
    exact (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique hya hy1
  obtain ⟨Y₀, π₀, sY₀, -, hc₀, -, -, -⟩ := GlobalTheory.T.exists_separated_galoisCover_of_free_action K G.left (G.hom ≫ π ≫ sY) Ga ν hq hν1 hνmul
    (fun a => by rw [← Category.assoc G.hom π sY, ← Category.assoc, hinvG]) hfree
  obtain ⟨v, hv, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares G.left Y₀ π₀ Ga ν hc₀).1 Y (G.hom ≫ π) hinvG
  have hsq : IsPullback G.hom π₀ π v :=
    ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 G.left Y₀ π₀ ν G.hom v hdown hv.symm).1 hc₀
  have H : IsPullback π₀ G.hom (Over.mk v).hom π := hsq.flip
  obtain ⟨inst, hcomm', hgp⟩ := exists_grpObj (G' := Over.mk v) (φ := π₀) hc H hν (fun a => hc₀.inv a)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) π :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hsm' : Smooth v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ hsm
  have huc : UniversallyClosed v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have hlft : LocallyOfFiniteType v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have : Surjective π₀ := hc₀.onto
  have : IsFinite π₀ := hc₀.fin
  have : IsSeparated (π₀ ≫ v) := by rw [hv]; infer_instance
  have hsep : IsSeparated v := GlobalTheory.SemiAbelianDescent.isSeparated_of_comp π₀ v
  have hgc' : GeometricallyConnected v := GlobalTheory.SemiAbelianDescent.geometricallyConnected_of_isPullback H
  exact ⟨Over.mk v, inst, π₀, ⟨hcomm', hsm', { toIsSeparated := hsep, toUniversallyClosed := huc, toLocallyOfFiniteType := hlft }, hgc'⟩, hgp, hc₀⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.OpenSubgroupPts

open GlobalTheory.Points

theorem isPreconnected_affineOpen {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p]
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsPreconnected {x : Pts p | ⊤ ≤ x.1 ⁻¹ᵁ U} := by
  have key : ∀ {R : CommRingCat.{0}} [IsDomain R] (q : Spec R ⟶ Sp ℂ) [LocallyOfFiniteType q],
      PreconnectedSpace (Pts q) := by
    intro R _ q hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact FiniteClasses.preconnectedSpace_pts R
  have := key (hU.fromSpec ≫ p)
  have h := isPreconnected_range (PtsOver.continuous_map (C := ℂ) hU.fromSpec (q := p) rfl (𝟙 _))
  rw [PtsOver.range_map, range_comp_of_isOpenImmersion, hU.opensRange_fromSpec] at h
  exact h

theorem preconnectedSpace_pts_of_isIntegral {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ)
    [LocallyOfFiniteType p] : PreconnectedSpace (Pts p) := by
  refine ⟨isPreconnected_of_forall_pair fun x _ y _ => ?_⟩
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_le x.1 (le_preimage_top _)
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top _)
  have hx' := (le_preimage_iff x.1 U).1 hx
  have hy' := (le_preimage_iff y.1 V).1 hy
  have : Nonempty U := ⟨⟨_, hx'⟩⟩
  have : Nonempty V := ⟨⟨_, hy'⟩⟩
  obtain ⟨z, hz, hzm⟩ := ComplexPoints.exists_point_mem p (Z := (U : Set Y) ∩ V)
    (U.isOpen.inter V.isOpen).isLocallyClosed
    (nonempty_preirreducible_inter U.isOpen V.isOpen ⟨_, hx'⟩ ⟨_, hy'⟩)
  exact ⟨_, Set.subset_univ _, Or.inl hx, Or.inr hy, IsPreconnected.union (⟨z, hz⟩ : Pts p)
    ((le_preimage_iff z U).2 (hzm _).1) ((le_preimage_iff z V).2 (hzm _).2)
    (isPreconnected_affineOpen p hU) (isPreconnected_affineOpen p hV)⟩

theorem subgroup_eq_top_of_nhds_one :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤ := by
  intro X G _ x H U κ _ f O hs hc hO h1 h1O hH
  let p := pullback.snd G.hom x
  have : IsIntegral (pullback G.hom x) :=
    isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback G.hom x)
  have := preconnectedSpace_pts_of_isIntegral p
  let Y : Over X := Over.mk (p ≫ x)
  let π : Y ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  let s : Y ⟶ Over.mk x := Over.homMk p rfl
  let inc : Pts p → (Over.mk x ⟶ Y) := fun y => Over.homMk y.1 (by
    show y.1 ≫ p ≫ x = x
    rw [← Category.assoc, y.2, Category.id_comp])
  have hin : ∀ y, inc y ≫ s = 𝟙 _ := fun y => Over.OverMorphism.ext y.2
  have hsurj : ∀ a : Over.mk x ⟶ G, ∃ y, inc y ≫ π = a := fun a =>
    ⟨⟨pullback.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp x).symm), pullback.lift_snd _ _ _⟩,
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hopen : IsOpen {z : Sp ℂ ⟶ G.left | ⊤ ≤ z ⁻¹ᵁ U ∧ (fun j => valAt' z U (f j)) ∈ O} :=
    (continuousOn_pi.2 fun j => continuousOn_valR (C := ℂ) (f j)).isOpen_inter_preimage
      (isOpen_setOf_le_preimage U) hO
  have hl : IsLocallyConstant fun y : Pts p => inc y ≫ π ∈ H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    let τ : Y ⟶ G := (s ≫ (inc y₀ ≫ π)⁻¹) * π
    have hτ : ∀ y, inc y ≫ τ = (inc y₀ ≫ π)⁻¹ * (inc y ≫ π) := fun y => by
      rw [MonObj.comp_mul, ← Category.assoc, hin, Category.id_comp]
    have hcont : Continuous fun y : Pts p => (show Sp ℂ ⟶ G.left from (inc y ≫ τ).left) :=
      (continuous_comp (C := ℂ) (X := pullback G.hom x) τ.left).comp continuous_subtype_val
    have hN := (hopen.preimage hcont).mem_nhds (x := y₀) (by
      simp only [Set.mem_preimage, hτ, inv_mul_cancel]
      exact ⟨h1, h1O⟩)
    filter_upwards [hN] with y hy
    have h := hH _ hy.1 hy.2
    rw [hτ] at h
    have h' := H.mul_mem_cancel_right (y := inc y₀ ≫ π) h
    rw [mul_inv_cancel_left] at h'
    exact propext h'
  rw [eq_top_iff]
  intro a _
  obtain ⟨y, rfl⟩ := hsurj a
  obtain ⟨y₁, hy₁⟩ := hsurj 1
  have h := hl.apply_eq_of_preconnectedSpace y y₁
  simp only [hy₁] at h
  rw [h]
  exact H.one_mem

end GlobalTheory.OpenSubgroupPts
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {g : ℕ}

def ReadsPeriods (t : SAB H S) {T : Over S} (c₀ : ℂˣ → Γ(T.left, ⊤)ˣ) (D : Datum H) (ty : Fin g → (E →+* ℂ))
    (P : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (T ⟶ t.G)) : Prop :=
  (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧
    ∀ (k : ℕ) (a a₂ : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a a₂ : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (c₀ c)

theorem int_eq_of_exp_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  have hk : 0 < (n - m).natAbs + 1 := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  have h0 : (((n - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = ((((n - m).natAbs + 1 : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((n - m).natAbs + 1 : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem discrete_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    DiscreteTopology P.range.toIntSubmodule := hP.2.2.1

theorem countable_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    (P.range : Set (Fin g → ℂ)).Countable :=
  have := hP.2.2.1
  countable_of_isDiscrete_finiteDimensional DiscreteTopology.isDiscrete

theorem exists_linearEquiv_of_period {t : SAB H S} {y : Sp ℂ ⟶ S} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {g₀ : ℕ} {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ t.G)}
    (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t.semi.separated
  have := discrete_periods hP
  have : IsZLattice ℝ P.range.toIntSubmodule := ⟨hP.2.2.2.1⟩
  exact he.exists_linearEquiv P.range.toIntSubmodule hk ha hs hh hc

theorem exists_isometry {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 he.1 he.2.1 he.2.2.1
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add (f := _), hr₀, hr₀, hr₀, map_add (f := _), map_add (f := _)])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem div_eq_iff {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)} (hP : Function.Injective P)
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n)
    (a b : L) : e ((n : ℂ)⁻¹ • P a) = e ((n : ℂ)⁻¹ • P b) ↔ ∃ x, a = b + n • x := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [eq_iff_sub_of_add he, hk, ← smul_sub, ← map_sub]
  refine exists_congr fun x => ?_
  rw [eq_inv_smul_iff₀ h0, Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.eq_iff, eq_sub_iff_add_eq', eq_comm]

theorem exists_div_of_pow {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)}
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) {x : Q} (hx : x ^ n = 1) :
    ∃ a, x = e ((n : ℂ)⁻¹ • P a) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨z, rfl⟩ := hs x
  have hp : ∀ m : ℕ, e (m • z) = e z ^ m := fun m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, map_zero_of_add he]
    | succ m ih => rw [succ_nsmul, he, ih, pow_succ]
  obtain ⟨a, ha⟩ := (hk _).1 ((hp n).trans hx)
  exact ⟨a, by rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]⟩

theorem exists_pointEquiv {S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {y : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G y φ) :
    ∃ β : (𝟙_ (Over S') ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (β x).left = x.left ≫ φ := by
  have w : ∀ x : 𝟙_ (Over S') ⟶ G', x.left ≫ G'.hom = 𝟙 S' := fun x => Over.w x
  let f : (𝟙_ (Over S') ⟶ G') → (Over.mk y ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = y
    rw [Category.assoc, h.1.w, ← Category.assoc, w]
    exact Category.id_comp y)
  have hb : Function.Bijective f := by
    refine ⟨fun a b hab => Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((w a).trans (w b).symm)),
      fun x => ?_⟩
    have hx : x.left ≫ G.hom = 𝟙 S' ≫ y := (Over.w x).trans (Category.id_comp y).symm
    exact ⟨Over.homMk (h.1.lift x.left (𝟙 S') hx) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ hx)⟩
  refine ⟨⟨Equiv.ofBijective f hb, fun a b => Over.OverMorphism.ext ?_⟩, fun _ => rfl⟩
  exact (h.2 _ a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm.trans
    (mul_left_congr (Category.id_comp y) _ _ _ _ rfl rfl)

theorem weilIs_congr {X : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {a b : X ⟶ S} (h : a = b) {k : ℤ}
    {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left)
    {c : Γ(X, ⊤)ˣ} (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst h
  rwa [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]

end GlobalTheory.UnifPoint
end
end
