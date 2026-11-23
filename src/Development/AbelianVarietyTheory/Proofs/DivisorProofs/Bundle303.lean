module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibre
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle194
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle195
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_base_point_of_finite_etale_over_algClosed : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀), IsFinite p → Etale p → ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) → ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  first | exact @GlobalTheory.FinEtPoints.exists_point_of_finite_etale | exact GlobalTheory.FinEtPoints.exists_point_of_finite_etale | (intros; apply GlobalTheory.FinEtPoints.exists_point_of_finite_etale <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_closedImmersion_represents_of_affineOpens : ∀ (S : Scheme.{0}) (U T : Over S) (P : ∀ Y : Over S, (Y ⟶ U) → (Y ⟶ T) → Prop), (∀ (Y Y' : Over S) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t → P Y' (f ≫ u) (f ≫ t)) → (∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ P (Over.mk (W.ι ≫ Y.hom)) (Over.homMk W.ι rfl ≫ u) (Over.homMk W.ι rfl ≫ t)) → P Y u t) → (∀ V : T.left.affineOpens, ∃ (H : Over S) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), P Y u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over S) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  intro S U T P hres hloc hV
  choose H h hci hfin hflat hsurj hrep using hV
  have key : ∀ (V : T.left.affineOpens) (Y : Over S) (g : Y ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)),
      P Y (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ fst U T)
        (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ snd U T) ↔
      ∃ z : Y.left ⟶ (H V).left, z ≫ (h V).left = g.left := by
    intro V Y g
    rw [whiskerLeft_fst, whiskerLeft_snd, ← Category.assoc g]
    rw [hrep V Y (g ≫ fst _ _) (g ≫ snd _ _), lift_comp_fst_snd]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z.left, by rw [← Over.comp_left, hz]⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · rw [← Over.w (h V), ← Category.assoc, hz, Over.w g]
      · apply Over.OverMorphism.ext; simpa using hz

  have hpb : ∀ V : T.left.affineOpens,
      IsPullback (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left
        (snd U (Over.mk (V.1.ι ≫ T.hom))).left (snd U T).left V.1.ι :=
    fun V => _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd S U T _ _
  have hoi : ∀ V : T.left.affineOpens,
      IsOpenImmersion (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left :=
    fun V => MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb V).flip inferInstance
  have hmem : ∀ y : T.left, ∃ V : T.left.affineOpens, y ∈ V.1 := by
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      T.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, hyV⟩
  have hsup : (⨆ V : T.left.affineOpens, (V.1 : T.left.Opens)) = ⊤ := by
    rw [eq_top_iff]; intro y _
    obtain ⟨V, hV⟩ := hmem y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hV⟩
  have hcov : ∀ x : (U ⊗ T).left, ∃ V : T.left.affineOpens,
      x ∈ Set.range (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left := by
    intro x
    obtain ⟨V, hV⟩ := hmem ((snd U T).left x)
    obtain ⟨v, hv⟩ : (snd U T).left x ∈ Set.range V.1.ι := by rw [Scheme.Opens.range_ι]; exact hV
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback x v hv.symm
    refine ⟨V, (hpb V).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]; exact hw1
  have compat : ∀ (V V' : T.left.affineOpens) (Y : Scheme.{0})
      (g : Y ⟶ (U ⊗ Over.mk (V.1.ι ≫ T.hom)).left) (g' : Y ⟶ (U ⊗ Over.mk (V'.1.ι ≫ T.hom)).left),
      g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left =
        g' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)).left →
      ((∃ z : Y ⟶ (H V).left, z ≫ (h V).left = g) ↔ (∃ z : Y ⟶ (H V').left, z ≫ (h V').left = g')) := by
    intro V V' Y g g' hgg
    let Y' : Over S := Over.mk (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left ≫ (U ⊗ T).hom)
    let e : Y' ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom) := Over.homMk g (by simp [Y'])
    let e' : Y' ⟶ U ⊗ Over.mk (V'.1.ι ≫ T.hom) := Over.homMk g' (by
      show _ = g ≫ _ ≫ _; rw [← Category.assoc g, hgg, Category.assoc, Over.w])
    have hm : e ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        e' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)) := by
      apply Over.OverMorphism.ext; simpa [e, e'] using hgg
    have k := key V Y' e
    have k' := key V' Y' e'
    rw [reassoc_of% hm, reassoc_of% hm] at k
    exact k.symm.trans k'
  obtain ⟨B, b, hb, hbrep⟩ := _root_.GlobalTheory.T.exists_glue_closedImmersions_open_cover (U ⊗ T).left T.left.affineOpens _ _ hoi hcov
    (fun V => (H V).left) (fun V => (h V).left) hci compat
  have hprops := _root_.GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover (U ⊗ T).left T.left (snd U T).left T.left.affineOpens
    (fun V => V.1) hsup _ _ _ hpb B b hb _ _ hci hbrep
    (fun V => ⟨hfin V, hflat V, hsurj V⟩)
  refine ⟨Over.mk (b ≫ (U ⊗ T).hom), Over.homMk b rfl, hb, hprops.1, hprops.2.1, hprops.2.2, ?_⟩
  intro Y u t

  have hW : ∀ (V : T.left.affineOpens),
      P (Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom)) (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u)
        (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t) ↔
      ∃ z : (t.left ⁻¹ᵁ V.1).toScheme ⟶ B, z ≫ b = (t.left ⁻¹ᵁ V.1).ι ≫ (lift u t).left := by
    intro V
    have hr : Set.range ((t.left ⁻¹ᵁ V.1).ι ≫ t.left) ⊆ Set.range V.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h1 : (t.left ⁻¹ᵁ V.1).ι w ∈ ((t.left ⁻¹ᵁ V.1 : Y.left.Opens) : Set Y.left) := by
        rw [← Scheme.Opens.range_ι]; exact Set.mem_range_self w
      rw [Scheme.Hom.comp_apply]; exact h1
    let tW : Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom) ⟶ Over.mk (V.1.ι ≫ T.hom) :=
      Over.homMk (IsOpenImmersion.lift V.1.ι _ hr) (by simp [IsOpenImmersion.lift_fac_assoc])
    have htW : tW ≫ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t := by
      apply Over.OverMorphism.ext; simp [tW, IsOpenImmersion.lift_fac]
    let gW := lift (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u) tW
    have hgW : gW ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ lift u t := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [gW, htW]
    have k := key V _ gW
    rw [reassoc_of% hgW, reassoc_of% hgW, lift_fst, lift_snd] at k
    rw [k, ← hbrep V _ gW.left, ← Over.comp_left, hgW]
    rfl
  constructor
  · intro hP
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source _ _ _ b hb (lift u t).left (fun y => by
      obtain ⟨V, hV⟩ := hmem (t.left y)
      exact ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mp (hres _ _ _ u t hP)⟩)
    refine ⟨Over.homMk z ?_, ?_⟩
    · simp only [Over.mk_hom]; rw [← Category.assoc, hz, Over.w]
    · apply Over.OverMorphism.ext; simpa using hz
  · rintro ⟨z, hz⟩
    apply hloc
    intro y
    obtain ⟨V, hV⟩ := hmem (t.left y)
    refine ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mpr ⟨(t.left ⁻¹ᵁ V.1).ι ≫ z.left, ?_⟩⟩
    rw [Category.assoc, ← hz]; rfl
end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (Z : Over S') (i : Z ⟶ G) (V₀ : S'.Opens) (d : ℕ) (s : S'), Mono i → s ∈ V₀ → IsFinite (Z.hom ∣_ V₀) → (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) → (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) → (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) → IsUnit ((d : ℕ) : S'.residueField s) → (∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s), T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1) → ∃ V : S'.Opens, s ∈ V ∧ V ≤ V₀ ∧ ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V : Set S') → (z ≫ i) ^ d = 1 := by
  first | (exact @GlobalTheory.FiniteKilled.killed_near) | (exact GlobalTheory.FiniteKilled.killed_near) | (intros; apply GlobalTheory.FiniteKilled.killed_near  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_group_scheme_stalk_length_constant : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  first | (exact @GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (exact GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (intros; apply GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_factor_through_integral_subalgebra : ∀ (K B E : Type) [Field K] [CommRing B] [CommRing E] [Algebra K B] [Algebra K E] (i : E →ₐ[K] B), Function.Injective i → (∀ b : B, _root_.IsIntegral K b → b ∈ i.range) → ∀ (T : Scheme.{0}) (p : T ⟶ Sp K) [IsFinite p] (t : Sp B ⟶ T), t ≫ p = spMap (algebraMap K B) → ∃ u : Sp E ⟶ T, u ≫ p = spMap (algebraMap K E) ∧ t = spMap i.toRingHom ≫ u := by
  first | exact @GlobalTheory.point_factor_integral_subalgebra | exact GlobalTheory.point_factor_integral_subalgebra | (intros; apply GlobalTheory.point_factor_integral_subalgebra <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.local_quotient_transition_cocycle : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) →
    (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) →
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    ∀ (j k l : 𝒰.I₀) (T : Scheme.{0}) (x : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k))
      (y : T ⟶ pullback ((B k).hom ≫ 𝒰.f k) (𝒰.f l)) (z : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f l)),
      x ≫ b j k = y ≫ pullback.fst _ _ → x ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ → y ≫ b k l = z ≫ b j l := by
  first | (exact @GlobalTheory.cocycle_local_quotient_transition) | (exact GlobalTheory.cocycle_local_quotient_transition) | (intros; apply GlobalTheory.cocycle_local_quotient_transition  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π] [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'), IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  first | exact @GlobalTheory.LiftLocal.lift | exact GlobalTheory.LiftLocal.lift | (intros; apply GlobalTheory.LiftLocal.lift <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem exists_ringHom_algClosure_residueField_of_isIntegral (A B : Type) [CommRing A]
    [IsLocalRing A] [CommRing B] (φ : A →+* B) (hφ : φ.IsIntegral) (P : Ideal B) [P.IsPrime]
    (hP : P.comap φ = IsLocalRing.maximalIdeal A) :
    ∃ ψ : B →+* AlgebraicClosure (IsLocalRing.ResidueField A),
      ψ.comp φ = algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  haveI : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hP.symm⟩
  letI : Algebra (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (IsLocalRing.maximalIdeal A)
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral A (B ⧸ P) := inferInstance
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Algebra.IsIntegral.tower_top (R := A)
  let l : (B ⧸ P) →ₐ[IsLocalRing.ResidueField A] AlgebraicClosure (IsLocalRing.ResidueField A) :=
    IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext a
  have h := l.commutes (algebraMap A (IsLocalRing.ResidueField A) a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  exact h

theorem exists_point_algClosure_residueField_of_isIntegralHom :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  intro A _ _ Y g hi hs
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  have h1 : IsIntegralHom (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : φ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  obtain ⟨P, hP⟩ := h2.surj (IsLocalRing.closedPoint A)
  have hP' : (PrimeSpectrum.asIdeal P).comap φ.hom = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hP
  haveI := PrimeSpectrum.isPrime P
  obtain ⟨ψ, hψ⟩ := exists_ringHom_algClosure_residueField_of_isIntegral A Γ(Y, ⊤) φ.hom h3
    (PrimeSpectrum.asIdeal P) hP'
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← hψ]
  rfl

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry

theorem _root_.GlobalTheory.T.isOpenImmersion_specMap_of_quasiFinite_of_normal : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing A] (φ : A →+* B), (∀ (𝔭 : Ideal A) [𝔭.IsPrime], IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭)) → φ.FiniteType → LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)) → (∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) → IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  first | exact @GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | exact GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | (intros; apply GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC
namespace GlobalTheory

theorem spec_map_smooth_surjective_of_isSeparable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have hfp : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  have hs : Algebra.Smooth K L := inferInstance
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    rw [RingHom.Smooth]
    simp only [CommRingCat.hom_ofHom]
    exact RingHom.smooth_algebraMap.mpr hs
  · constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem exists_clopen_integral_of_smooth_over_field :
    ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z,
      ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧
        z ∈ Set.range j := by
  intro F _ Z q hq z
  obtain ⟨hR, hN, hL⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F Z q hq
  have : GlobalTheory.IsNormalScheme Z := by first | exact hN | exact IsNormalScheme.of_pred hN
  have hC : irreducibleComponent z ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
  let C : Z.Opens := ⟨irreducibleComponent z, IsNormalScheme.isOpen_of_mem_irreducibleComponents hC⟩
  have hzC : z ∈ C := mem_irreducibleComponent
  have hrange : Set.range C.ι = (C : Set Z) := Scheme.Opens.range_ι C
  refine ⟨C.toScheme, C.ι, ?_, inferInstance, ?_, by rw [hrange]; exact hzC⟩
  · apply IsClosedImmersion.of_isPreimmersion
    rw [hrange]
    exact isClosed_of_mem_irreducibleComponents _ hC
  · have : IrreducibleSpace C := Subtype.irreducibleSpace isIrreducible_irreducibleComponent
    have : Nonempty C := ⟨⟨z, hzC⟩⟩
    exact isIntegral_of_irreducibleSpace_of_isReduced C.toScheme

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.smooth_section_lift_nilpotent_of_sqZero : (∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e) →
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  first | exact @GlobalTheory.SecLift.lift_of_nilpotent_of_sqZero | exact GlobalTheory.SecLift.lift_of_nilpotent_of_sqZero | (intros; apply GlobalTheory.SecLift.lift_of_nilpotent_of_sqZero <;> assumption)
end
