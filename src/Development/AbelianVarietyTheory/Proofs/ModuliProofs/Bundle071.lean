module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ValuativeGeneric

theorem exists_lift_of_surjectiveOnStalks {X Z : Scheme.{0}} (j : X ⟶ Z) [SurjectiveOnStalks j]
    (K : Type) [Field K] (t : Spec (.of K) ⟶ Z) (x : X)
    (hx : t (IsLocalRing.closedPoint K) = j x) :
    ∃ u : Spec (.of K) ⟶ X, u ≫ j = t ∧ ∀ p, u p = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective t
  obtain rfl : z = j x := (Scheme.fromSpecResidueField_apply z
    (Spec.map φ (IsLocalRing.closedPoint K))).symm.trans hx
  have : IsIso (j.residueFieldMap x) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
    refine ⟨Z.residue _ c, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  refine ⟨Spec.map (inv (j.residueFieldMap x) ≫ φ) ≫ X.fromSpecResidueField x, ?_, fun p => by simp⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
  rfl

theorem isClosedImmersion_of_lift {X Z : Scheme.{0}} [IsLocallyNoetherian Z] [Z.IsSeparated]
    (j : X ⟶ Z) [IsPreimmersion j] [QuasiCompact j]
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K]
      (x : Sp K ⟶ X) (y : Sp V ⟶ Z), Set.range x ⊆ genericPoints X →
      x ≫ j = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) :
    IsClosedImmersion j := by
  refine .of_isPreimmersion j (IsClosedMap.isClosed_range ?_)
  rw [isClosedMap_iff_specializingMap]
  refine j.isEmbedding.isInducing.specializingMap ?_
  rintro _ z hz ⟨x, rfl⟩
  obtain ⟨x₀, hx₀, hs⟩ := exists_mem_genericPoints_specializes x
  have hs' : j x₀ ⤳ z := (hs.map j.continuous).trans hz
  by_cases hne : j x₀ = z
  · exact ⟨x₀, hne⟩
  obtain ⟨O, _, _, _, g, hg₀, hg₁⟩ := exists_complete_discreteValuationRing_of_specializes hs' hne
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hpt : (spMap (algebraMap O (FractionRing O)) ≫ g)
      (IsLocalRing.closedPoint (FractionRing O)) = j x₀ := by
    refine Eq.trans (congrArg g (PrimeSpectrum.ext ?_)) hg₀
    change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨u, hu, hux⟩ := exists_lift_of_surjectiveOnStalks j (FractionRing O) _ x₀ hpt
  obtain ⟨x', hx'⟩ := h O (FractionRing O) u g (by rintro _ ⟨p, rfl⟩; rw [hux]; exact hx₀) hu
  have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
    refine ⟨?_⟩
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have e : x' ≫ j = g :=
    ext_of_isDominant (spMap (algebraMap O (FractionRing O))) (by rw [← Category.assoc, hx', hu])
  exact ⟨x' (IsLocalRing.closedPoint O), by rw [← hg₁, ← e]; rfl⟩

theorem isProper_of_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro R _ _ X Y _ f s hs ⟨N, i, hi, hq, e⟩ h
  have := isProper_str R N
  let j : X ⟶ pullback s (PSpace.str R N) := pullback.lift f i e.symm
  have hj₁ : j ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _
  have : IsImmersion (j ≫ pullback.snd _ _) := hj₂ ▸ hi
  have : QuasiCompact (j ≫ pullback.snd _ _) := hj₂ ▸ hq
  have : IsImmersion j := IsImmersion.of_comp j (pullback.snd _ _)
  have : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd _ _)
  have : IsLocallyNoetherian (pullback s (PSpace.str R N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  have : (pullback s (PSpace.str R N)).IsSeparated := by
    refine ⟨?_⟩
    rw [← terminal.comp_from (pullback.fst s (PSpace.str R N) ≫ s)]
    infer_instance
  have : IsClosedImmersion j := isClosedImmersion_of_lift j fun V K _ _ _ _ _ _ _ x y hx hy =>
    h V K x (y ≫ pullback.fst _ _) hx (by rw [← hj₁, ← Category.assoc, hy, Category.assoc])
  rw [← hj₁]
  infer_instance

end GlobalTheory.ValuativeGeneric
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GroupGlue

theorem exists_scheme {X : Scheme.{0}} {U V : X.Opens} {G₁ : Over U.toScheme} {G₂ : Over V.toScheme}
    {G₀ : Over (U ⊓ V).toScheme} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom (X.homOfLE inf_le_left))
    (h₂ : IsPullback φ₂ G₀.hom G₂.hom (X.homOfLE inf_le_right)) :
    ∃ (G : Over X) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom U.ι ∧
      IsPullback ψ₂ G₂.hom G.hom V.ι ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ X := pushout.desc (G₁.hom ≫ U.ι) (G₂.hom ≫ V.ι) (by
    rw [h₁.w_assoc, h₂.w_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ U.ι := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ V.ι := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = U.ι (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = V.ι (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · have hy' : y.1 = (G₂.hom x).1 := hy.trans (e2 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x ⟨y.1, y.2, hy' ▸ (G₂.hom x).2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · have hy' : y.1 = (G₁.hom x).1 := hy.trans (e1 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x ⟨y.1, hy' ▸ (G₁.hom x).2, y.2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

theorem exists_inf {X S : Scheme.{0}} {U V : X.Opens} (u : S ⟶ U) (v : S ⟶ V) (h : u ≫ U.ι = v ≫ V.ι) :
    ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
  have hr : Set.range (u ≫ U.ι) ⊆ Set.range (U ⊓ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨(u z).2, ?_⟩
    rw [h]
    exact (v z).2
  refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
  · rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, h]

theorem exists_glue_two : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) (U V : X.Opens) (G₁ : Over U.toScheme) [GrpObj G₁] (G₂ : Over V.toScheme) [GrpObj G₂] (G₀ : Over (U ⊓ V).toScheme) [GrpObj G₀] (a₁ : OAct O G₁) (a₂ : OAct O G₂) (a₀ : OAct O G₀) (φ₁ : G₀.left ⟶ G₁.left) (φ₂ : G₀.left ⟶ G₂.left), U ⊔ V = ⊤ → IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsGrpPullback G₀ G₁ (X.homOfLE inf_le_left) φ₁ → IsGrpPullback G₀ G₂ (X.homOfLE inf_le_right) φ₂ → (∀ x, (a₀.act x).left ≫ φ₁ = φ₁ ≫ (a₁.act x).left ∧ (a₀.act x).left ≫ φ₂ = φ₂ ≫ (a₂.act x).left) → ∃ (G : Over X) (_ : GrpObj G) (a : OAct O G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G₁ G U.ι ψ₁ ∧ IsGrpPullback G₂ G V.ι ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ ∧ ∀ x, (a₁.act x).left ≫ ψ₁ = ψ₁ ≫ (a.act x).left ∧ (a₂.act x).left ≫ ψ₂ = ψ₂ ≫ (a.act x).left := by
  intro O _ X U V G₁ i₁ G₂ i₂ G₀ _ a₁ a₂ a₀ φ₁ φ₂ hUV s₁ s₂ h₁ h₂ ha
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme h₁.1 h₂.1
  have m₁ : Mono ψ₁ := by
    have : IsOpenImmersion ψ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₁.flip inferInstance
    infer_instance
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ →
      ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    refine exists_inf u v ?_
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ (U ⊓ V : X.Opens))
      (a : Over.mk (w ≫ X.homOfLE inf_le_left) ⟶ G₁) (b : Over.mk (w ≫ X.homOfLE inf_le_right) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  have ca : ∀ (x : O) {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → (a ≫ a₁.act x).left ≫ ψ₁ = (b ≫ a₂.act x).left ≫ ψ₂ := by
    intro x S u v a b h
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    rw [Over.comp_left, Over.comp_left, c₁, c₂]
    simp only [Category.assoc]
    rw [← reassoc_of% (ha x).1, ← reassoc_of% (ha x).2, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) U.ι V.ι i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    · exact inferInstanceAs (IsOpenImmersion U.ι)
    · exact inferInstanceAs (IsOpenImmersion V.ι)
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    have hx : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · exact ⟨true, ⟨x, hx⟩, rfl⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  let α : ∀ i : 𝒰.I₀, OAct O (H i) := fun i => Bool.rec (motive := fun i => @OAct _ O _ (H i) (iH i)) a₁ a₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  obtain ⟨A, hA⟩ := exists_oAct hG α (by
    have d : ∀ (x : O) (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α i).act x).left ≫ ψ i := by
      intro x i S u v a b h
      obtain rfl := same i a b h
      rw [pt_ext hψ h]
    rintro x (_ | _) (_ | _) S u v a b h
    · exact d x _ S u v a b h
    · exact ca x a b h
    · exact (ca x b a h.symm).symm
    · exact d x _ S u v a b h)
  exact ⟨G, iG, A, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ,
    fun x => ⟨hA x false, hA x true⟩⟩

end GlobalTheory.GroupGlue
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMSpreadCompare

open GlobalTheory.PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Unif

theorem exists_pointEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {s : T.left ⟶ S} (hs : s = T.hom ≫ f) :
    ∃ p : (T ⟶ G') ≃* (Over.mk s ⟶ G), ∀ x, (p x).left = x.left ≫ φ := by
  subst hs
  exact ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun _ _ e => eq_of_comp_eq h.1 (congrArg (fun z => z.left) e), fun p =>
    ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩, fun _ => rfl⟩

theorem isHolTo_postcomp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  rw [show (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) from
    funext fun b => (valAt'_comp _ φ U s).symm]
  exact h (φ ⁻¹ᵁ U) _

variable {k : Type} [Field k] {κ : k →+* ℂ} {A : Over (Sp k)} [GrpObj A] {PC : Out.PolAV (Sp ℂ)}
  {ψ : PC.A.left ⟶ A.left} (hψ : IsGrpPullback PC.A A (spMap κ) ψ) (u : HolUnif PC.A PC.L PC.g)

include hψ

end Unif

section Quadratic

end Quadratic

section Transport

variable {D : Datum H} {R : Type} [CommRing R] {t : SAB H (Sp R)} {B B' : Over (Sp R)} [GrpObj B] [GrpObj B']
  {M : LB B.left} {M' : LB B'.left} {L : Submodule (𝓞 E) D.La} {ρ : R} {S S' : Set L} {φ : L → (B ⟶ t.G)}

end Transport

section Multiplication

end Multiplication

end GlobalTheory.CMSpreadCompare
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory.CMPeriodCompare

section Analytic

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)}
    (he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ}
    {v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ X} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e (L w) v) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => e (L z)) w v := by
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff] at h ⊢
  obtain ⟨h0, h1⟩ := h
  refine ⟨by simpa using h0, fun U hU f => ?_⟩
  rw [h1 U hU f]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    rw [← h0]
    intro x _
    exact hU (by trivial)
  have hd := _root_.GlobalTheory.LocalLift.hol_differentiableAt he (Set.mem_univ 0) hU0 f
  unfold _root_.GlobalTheory.FibreDeriv.jet
  simp only [map_zero]
  congr 2
  have hd' : DifferentiableAt ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f)
      (LinearMap.toContinuousLinearMap L 0) := by
    simpa using hd
  have hc := hd'.hasFDerivAt.comp (0 : Fin g' → ℂ) (LinearMap.toContinuousLinearMap L).hasFDerivAt
  rw [show (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e (L z)) U f) =
      (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f) ∘ (LinearMap.toContinuousLinearMap L) from rfl, hc.fderiv]
  simp

variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} {P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left} in
private theorem isDerivAt0_ex_of_isDiff_tangent (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g)
    {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A} (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (u.ex z).left) w t.left := by
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left = (u.ex 0).left := by
    rw [_root_.GlobalTheory.TangentOrigin.ex_zero_left]
    exact ht
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff]
  refine ⟨h0, fun U h f => ?_⟩
  ext
  · rw [_root_.GlobalTheory.FibreDeriv.fst_evEps _ _ h0, _root_.GlobalTheory.FibreDeriv.fst_jet]
  · have := hw U h f
    unfold _root_.GlobalTheory.FibreDeriv.jet
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rw [← this]
    rfl


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors in
variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} {P' : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left} in
theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_line (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g) {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A}
    (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (g := 1) (fun z => (u.ex (z 0 • w)).left ≫ φ) (fun _ => 1) (t.left ≫ φ) := by
  have hu := isDerivAt0_ex_of_isDiff_tangent u ht hw
  have he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ (fun z => (u.ex z).left) := by
    simpa using _root_.GlobalTheory.HomLinear.isHolTo_ex_comp u (𝟙 _)
  let L : (Fin 1 → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) := (LinearMap.proj 0).smulRight w
  have hL : L (fun _ => 1) = w := by simp [L]
  rw [← hL] at hu
  exact _root_.GlobalTheory.FibreDeriv.isDerivAt0_comp (_root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear he L hu) φ

variable {v : epsR R ⟶ P.A}

variable {ex : ℂ → (Over.mk (spMap s) ⟶ P.A)} {Λ : Submodule ℤ ℂ}

end Analytic

section Arithmetic

variable {K : Type} [Field K] [NumberField K]

end Arithmetic

section Data

variable (d : ℕ) (K : Type) [Field K] [NumberField K] {M : Type} [Field M] [NumberField M]

variable {d K}

end Data

section Main

variable {d : ℕ} {K : Type} [Field K] [NumberField K]

end Main

end GlobalTheory.CMPeriodCompare
end
end
