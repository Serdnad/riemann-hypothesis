module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.IrrSplit

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_lift (M : Model R A) (U : M.Y.left.Opens)
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    IsPullback (IsOpenImmersion.lift U.ι (pullback.fst M.Y.hom (spMap (algebraMap R K))) hU)
      (pullback.snd M.Y.hom (spMap (algebraMap R K))) (U.ι ≫ M.Y.hom) (spMap (algebraMap R K)) := by
  refine ⟨⟨by rw [IsOpenImmersion.lift_fac_assoc, pullback.condition]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => pullback.lift (c.fst ≫ U.ι) c.snd (by simpa using c.condition)) ?_ ?_ ?_⟩⟩
  · intro c
    rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · intro c
    rw [pullback.lift_snd]
  · intro c m h₁ h₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← h₁, Category.assoc, IsOpenImmersion.lift_fac]
    · rw [pullback.lift_snd, h₂]

def restrictModel (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) : Model R A where
  Y := Over.mk (U.ι ≫ M.Y.hom)
  e := Over.isoMk (g := (Over.pullback (spMap (algebraMap R K))).obj M.Y) (isPullback_lift M U hU).isoPullback.symm
    ((isPullback_lift M U hU).isoPullback_inv_snd) ≪≫ M.e
  smooth := by have := M.smooth; show Smooth (U.ι ≫ M.Y.hom); infer_instance
  sep := by have := M.sep; show IsSeparated (U.ι ≫ M.Y.hom); infer_instance
  qc := by have := M.qc; show QuasiCompact (U.ι ≫ M.Y.hom); infer_instance

theorem restrictModel_j (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    (restrictModel M U hU).j ≫ U.ι = M.j := by
  have h := (isPullback_lift M U hU).isoPullback_hom_fst
  show ((M.e.inv.left ≫ (isPullback_lift M U hU).isoPullback.hom) ≫
    pullback.fst (U.ι ≫ M.Y.hom) (spMap (algebraMap R K))) ≫ U.ι = _
  rw [Category.assoc, Category.assoc, reassoc_of% h, IsOpenImmersion.lift_fac]
  rfl

end

theorem exists_cover_irr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  intro R K _ _ _ _ _ _ A M
  have := M.smooth
  have := M.qc
  let f : M.Y.left ⟶ Sp R := M.Y.hom
  let c : Sp R := IsLocalRing.closedPoint R
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian f
  have hf : Smooth f := M.smooth
  have hf' : QuasiCompact f := M.qc
  have hs : Smooth (f.fiberToSpecResidueField c) :=
    inferInstanceAs (Smooth (pullback.snd f ((Sp R).fromSpecResidueField c)))
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
    ((Sp R).residueField c) (f.fiber c) (f.fiberToSpecResidueField c) hs
  have hn' : GlobalTheory.IsNormalScheme (f.fiber c) := GlobalTheory.IsNormalScheme.of_pred hn
  have : CompactSpace (f.fiber c) := inferInstance
  have : IsNoetherian (f.fiber c) := {}
  have hfin : (irreducibleComponents (f.fiber c)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hr : Set.range (f.fiberι c) = M.sp := f.range_fiberι c
  have hcl : Topology.IsClosedEmbedding (f.fiberι c) := by
    refine ⟨(f.fiberι c).isEmbedding, ?_⟩
    rw [f.range_fiberι]
    exact (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
  have : Finite (irreducibleComponents (f.fiber c)) := hfin
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents (f.fiber c))
  let U : Fin n → M.Y.left.Opens := fun i => ⟨(f.fiberι c '' (σ.symm i).1ᶜ)ᶜ,
    (hcl.isClosedMap _ (GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (σ.symm i).2).isClosed_compl).isOpen_compl⟩
  have hU : ∀ i, Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range (U i).ι := by
    rintro i _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    rintro ⟨z, -, hz⟩
    have h1 : pullback.fst M.Y.hom (spMap (algebraMap R K)) x ∈ M.sp := hr ▸ ⟨z, hz⟩
    have h2 : M.Y.hom (pullback.fst M.Y.hom (spMap (algebraMap R K)) x) =
        spMap (algebraMap R K) (pullback.snd M.Y.hom (spMap (algebraMap R K)) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 := h2.symm.trans h1
    generalize pullback.snd M.Y.hom (spMap (algebraMap R K)) x = p at h3
    have h4 : Ideal.comap (algebraMap R K) p.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg PrimeSpectrum.asIdeal h3
    have h5 : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top (K := K) p.asIdeal).resolve_right p.isPrime.ne_top
    rw [h5, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h4
    exact IsDiscreteValuationRing.not_a_field R h4.symm
  have hmem : ∀ i z, f.fiberι c z ∈ U i ↔ z ∈ (σ.symm i).1 := by
    intro i z
    show f.fiberι c z ∉ f.fiberι c '' (σ.symm i).1ᶜ ↔ _
    rw [hcl.injective.mem_set_image]
    simp
  refine ⟨n, fun i => restrictModel M (U i) (hU i), fun i => Over.homMk (U i).ι rfl,
    fun i => ⟨?_, inferInstanceAs (IsOpenImmersion (U i).ι), restrictModel_j M (U i) (hU i)⟩, ?_⟩
  · have hi : IsIrreducible (f.fiberι c '' (σ.symm i).1) :=
      (σ.symm i).2.1.image _ (f.fiberι c).continuous.continuousOn
    have he : (restrictModel M (U i) (hU i)).sp = (U i).ι ⁻¹' (f.fiberι c '' (σ.symm i).1) := by
      ext y
      constructor
      · intro hy
        have : (U i).ι y ∈ M.sp := hy
        rw [← hr] at this
        obtain ⟨z, hz⟩ := this
        refine ⟨z, (hmem i z).1 ?_, hz⟩
        rw [hz]; exact y.2
      · rintro ⟨z, -, hz⟩
        have : (U i).ι y ∈ M.sp := hr ▸ ⟨z, hz⟩
        exact this
    show IsIrreducible _
    rw [he]
    refine ⟨?_, hi.2.preimage (U i).ι.isOpenEmbedding⟩
    obtain ⟨z, hz⟩ := (σ.symm i).2.1.1
    exact ⟨⟨_, (hmem i z).2 hz⟩, z, hz, rfl⟩
  · intro y hy
    rw [← hr] at hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨σ ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩, ⟨_, (hmem _ z).2 ?_⟩, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact mem_irreducibleComponent

end GlobalTheory.SS.IrrSplit
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ChartModel

set_option backward.isDefEq.respectTransparency false

noncomputable def twoCover {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun i => Bool.rec U V i)
    (fun i => Bool.rec (motive := fun i => (Bool.rec U V i : Scheme.{0}) ⟶ X) u v i) (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩) (fun i => by cases i <;> assumption)

theorem isClosedImmersion_snd_diagonal {U Y S : Scheme.{0}} (g : U ⟶ Y) (f : Y ⟶ S) [Mono g]
    [IsSeparated (g ≫ f)] :
    IsClosedImmersion (pullback.snd (pullback.diagonal f)
      (pullback.map (g ≫ f) (g ≫ f) f f g g (𝟙 _) (Category.comp_id _) (Category.comp_id _))) := by
  have H := pullback_map_diagonal_isPullback g g f
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom,
    H.isoPullback_hom_snd, ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.diagonal g)]
  convert (inferInstance : IsClosedImmersion (pullback.diagonal (g ≫ f)))
  ext : 1 <;> simp

theorem isSeparated_of_two {U V Y S : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion u]
    [IsOpenImmersion v] [IsSeparated (u ≫ f)] [IsSeparated (v ≫ f)]
    (h : ∀ x y : Y, f x = f y → (x ∈ Set.range u ∧ y ∈ Set.range u) ∨ (x ∈ Set.range v ∧ y ∈ Set.range v)) :
    IsSeparated f := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (twoCover
    (pullback.map (u ≫ f) (u ≫ f) f f u u (𝟙 _) (Category.comp_id _) (Category.comp_id _))
    (pullback.map (v ≫ f) (v ≫ f) f f v v (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ?_) ?_
  · intro z
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_map]
    exact h _ _ (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  · rintro (_ | _)
    · exact isClosedImmersion_snd_diagonal u f
    · exact isClosedImmersion_snd_diagonal v f

theorem exists_glue_chart {S T A X W : Scheme.{0}} (i : T ⟶ S) [IsOpenImmersion i] (a : A ⟶ T) (c : X ⟶ S)
    {p : W ⟶ X} {w : W ⟶ T} (hW : IsPullback p w c i) (u : W ⟶ A) [IsOpenImmersion u] (hu : u ≫ a = w)
    [Smooth a] [IsSeparated a] [Smooth c] [IsSeparated c] [CompactSpace A] [CompactSpace X] :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (g : X ⟶ Y) (j : A ⟶ Y), IsOpenImmersion g ∧ IsPullback j a f i ∧ g ≫ f = c ∧
      p ≫ g = u ≫ j ∧ Smooth f ∧ IsSeparated f ∧ CompactSpace Y ∧ ∀ y, f y ∉ Set.range i → y ∈ Set.range g := by
  have : IsOpenImmersion p := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hW.flip ‹_›
  have := GlueModels.isOpenImmersion_inl p u
  have := GlueModels.isOpenImmersion_inr p u
  have hc := GlueModels.pushout_cover p u
  let f : pushout p u ⟶ S := pushout.desc c (a ≫ i) (by rw [hW.w, ← Category.assoc, hu])
  have h1 : pushout.inl p u ≫ f = c := pushout.inl_desc _ _ _
  have h2 : pushout.inr p u ≫ f = a ≫ i := pushout.inr_desc _ _ _
  have e1 (x : X) : f (pushout.inl p u x) = c x := congrArg (fun g => g x) h1
  have e2 (x : A) : f (pushout.inr p u x) = i (a x) := congrArg (fun g => g x) h2
  have e3 (x : W) : pushout.inl p u (p x) = pushout.inr p u (u x) :=
    congrArg (fun g => g x) (pushout.condition (f := p) (g := u))
  have hin (y) (hy : f y ∈ Set.range i) : y ∈ Set.range (pushout.inr p u) := by
    rcases hc y with ⟨x, rfl⟩ | hy
    · obtain ⟨t, ht⟩ := hy
      obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hW x t ((e1 x).symm.trans ht.symm)
      exact ⟨u z, (e3 z).symm⟩
    · exact hy
  have hout (y) (hy : f y ∉ Set.range i) : y ∈ Set.range (pushout.inl p u) := by
    rcases hc y with h | ⟨x, rfl⟩
    · exact h
    · exact absurd ⟨a x, (e2 x).symm⟩ hy
  refine ⟨_, f, pushout.inl p u, pushout.inr p u, inferInstance, ?_, h1, pushout.condition, ?_, ?_, ?_, hout⟩
  · refine (IsOpenImmersion.isPullback _ _ _ _ h2 ?_).flip
    ext y
    constructor
    · exact hin y
    · rintro ⟨x, rfl⟩
      exact ⟨a x, (e2 x).symm⟩
  · refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (twoCover _ _ hc) ?_
    rintro (_ | _)
    · change Smooth (pushout.inl p u ≫ f)
      rw [h1]; infer_instance
    · change Smooth (pushout.inr p u ≫ f)
      rw [h2]; infer_instance
  · have : IsSeparated (pushout.inl p u ≫ f) := by rw [h1]; infer_instance
    have : IsSeparated (pushout.inr p u ≫ f) := by rw [h2]; infer_instance
    refine isSeparated_of_two (pushout.inl p u) (pushout.inr p u) f fun x y hxy => ?_
    by_cases hx : f x ∈ Set.range i
    · exact Or.inr ⟨hin x hx, hin y (hxy ▸ hx)⟩
    · exact Or.inl ⟨hout x hx, hout y (hxy ▸ hx)⟩
  · refine ⟨?_⟩
    rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl p u) ∪ Set.range (pushout.inr p u)) hc]
    exact (isCompact_range (pushout.inl p u).continuous).union (isCompact_range (pushout.inr p u).continuous)

theorem exists_model_of_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by
  intro R K _ _ _ _ _ _ A hA hs hq C _ _ hC u hu hua
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hloc : IsLocalization.Away π K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M := Submonoid.powers π) (nonZeroDivisors R)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) fun r hr => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hr) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  have hi : IsOpenImmersion (spMap (algebraMap R K)) := IsOpenImmersion.of_isLocalization π
  have hW : IsPullback (spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom)
      (spMap (algebraMap K (TensorProduct R K C))) (spMap (algebraMap R C)) (spMap (algebraMap R K)) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K C)).flip
  have : Smooth (spMap (algebraMap R C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hC
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨Y, f, g, j, hg, hj, hgf, hp, h1, h2, h3, h4⟩ :=
    exists_glue_chart (spMap (algebraMap R K)) A.hom (spMap (algebraMap R C)) hW u hua
  refine ⟨⟨Over.mk f, Over.isoMk hj.isoPullback.symm hj.isoPullback_inv_snd, h1, h2,
    (inferInstance : QuasiCompact f)⟩, g, hg, hgf, ?_, fun y hy => h4 y ?_⟩
  · exact hp.trans (congrArg (u ≫ ·) hj.isoPullback_hom_fst.symm)
  · rintro ⟨t, ht⟩
    have ht' : spMap (algebraMap R K) t = IsLocalRing.closedPoint R := ht.trans hy
    have h5 : π ∈ (spMap (algebraMap R K) t).asIdeal := by
      rw [ht']; exact hπ.not_isUnit
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show algebraMap R K π ∈ t.asIdeal from h5)
      (IsLocalization.Away.algebraMap_isUnit π))

end GlobalTheory.ChartModel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem eq_of_injective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') (h ≫ s) q) (w : a ≫ h = h' ≫ b)
    (hinj : Function.Injective h') {x y : H} (hxy : h x = h y) (hx : s (h x) ∈ Set.range q) : x = y := by
  have sq : IsPullback a h' h b := IsPullback.of_bot hH w hX
  obtain ⟨t, ht⟩ := hx
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hX (h x) t ht.symm
  obtain ⟨x', rfl, hx'⟩ := Scheme.exists_preimage_of_isPullback sq x z hz.symm
  obtain ⟨y', rfl, hy'⟩ := Scheme.exists_preimage_of_isPullback sq y z (hxy.symm.trans hz.symm)
  rw [hinj (hx'.trans hy'.symm)]

theorem mem_range_of_surjective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (w : a ≫ h = h' ≫ b)
    (hsurj : Function.Surjective h') {z : X} (hz : s z ∈ Set.range q) : z ∈ Set.range h := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨z', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hX z t ht.symm
  obtain ⟨x, rfl⟩ := hsurj z'
  exact ⟨a x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩

theorem surjective_of_isClosedImmersion_of_points {k : Type} [Field k] [IsAlgClosed k] {H X : Scheme.{0}}
    (h : H ⟶ X) [IsClosedImmersion h] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hs : ∀ x : Sp k ⟶ X, x ≫ s = 𝟙 _ → ∃ c : Sp k ⟶ H, c ≫ h = x) : Function.Surjective h := by
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.range_eq_univ]
  by_contra hne
  obtain ⟨x, hx, hx'⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
    h.isClosedEmbedding.isClosed_range.isOpen_compl.isLocallyClosed
  obtain ⟨c, hc⟩ := hs _ (pointOfClosedPoint_comp s x hx')
  let a : Sp k := IsLocalRing.closedPoint k
  refine hx ⟨c a, ?_⟩
  rw [← Scheme.Hom.comp_apply, hc]
  exact pointOfClosedPoint_apply s x hx' _

theorem eq_closedPoint_or_mem_range (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp T) :
    x = IsLocalRing.closedPoint T ∨ x ∈ Set.range (spMap (algebraMap T K)) := by
  by_cases hx : PrimeSpectrum.asIdeal x = ⊥
  · refine Or.inr ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)
  · refine Or.inl (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime x).isMaximal hx)

theorem isIso_of_genericFibre_of_specialFibre (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K]
    {H X S' H' X' : Scheme.{0}} (h : H ⟶ X) (s : X ⟶ Sp T) (u : H ⟶ Sp T) (hu : h ≫ s = u)
    [Smooth s] [IsSeparated s] [Smooth u] [IsSeparated u] [QuasiCompact u]
    [ConnectedSpace ↥(pullback u (spMap (algebraMap T K)))]
    (hK : IsPullback (pullback.fst u (spMap (algebraMap T K)) ≫ h) (pullback.snd u (spMap (algebraMap T K)))
      s (spMap (algebraMap T K)))
    {q : S' ⟶ Sp T} (hq : IsLocalRing.closedPoint T ∈ Set.range q)
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') u q) (w : a ≫ h = h' ≫ b)
    (hbij : Function.Bijective h') : IsIso h := by
  subst hu
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have : ConnectedSpace ↥(pullback s t) :=
    hK.isoPullback.hom.surjective.connectedSpace hK.isoPullback.hom.continuous
  obtain ⟨hXi, hN⟩ := isIntegral_and_isNormalScheme_of_smooth T K s
  obtain ⟨hHi, -⟩ := isIntegral_and_isNormalScheme_of_smooth T K (h ≫ s)
  have : IsSeparated h := IsSeparated.of_comp h s
  have : QuasiCompact h := QuasiCompact.of_comp h s
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h s
  let j := pullback.fst (h ≫ s) t
  have hj : IsPullback j (𝟙 _ ≫ pullback.snd (h ≫ s) t) (h ≫ s) t := by
    rw [Category.id_comp]; exact .of_hasPullback _ _
  have hinj : Function.Injective h := fun x y hxy ↦ by
    rcases eq_closedPoint_or_mem_range T K (s (h x)) with hx | hx
    · exact eq_of_injective_baseChange hX hH w hbij.1 hxy (hx ▸ hq)
    · exact eq_of_injective_baseChange hK hj (Category.id_comp _).symm
        (fun _ _ e ↦ e) hxy hx
  have hsurj : Function.Surjective h := fun z ↦ by
    rcases eq_closedPoint_or_mem_range T K (s z) with hx | hx
    · exact mem_range_of_surjective_baseChange hX w hbij.2 (hx ▸ hq)
    · exact mem_range_of_surjective_baseChange (h' := 𝟙 _) hK (Category.id_comp _).symm
        (fun e ↦ ⟨e, rfl⟩) hx
  have : LocallyQuasiFinite h := LocallyQuasiFinite.of_injective hinj
  have : IsOpenImmersion (j ≫ h) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip ‹_›
  have : IsOpenImmersion (j.opensRange.ι ≫ h) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance
  have : IsOpenImmersion h :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict h (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective h).mpr ⟨this, ⟨hsurj⟩⟩

theorem isPullback_of_comp_mono {𝒞 : Type*} [Category 𝒞] {A G P U Z : 𝒞} {a : A ⟶ G} {i : G ⟶ P} [Mono i]
    {s : A ⟶ U} {t : P ⟶ Z} {u : U ⟶ Z} (h : IsPullback (a ≫ i) s t u) : IsPullback a s (i ≫ t) u :=
  ⟨⟨by rw [← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift (c.fst ≫ i) c.snd (by rw [Category.assoc, c.condition]))
    (fun c ↦ by rw [← cancel_mono i, Category.assoc, h.lift_fst]) (fun c ↦ h.lift_snd _ _ _)
    (fun c m h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, ← Category.assoc, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

theorem isAlgClosed_residueField_OO (p : ℕ) [Fact p.Prime] : IsAlgClosed (kb p) :=
  GlobalTheory.NormIntegers.isAlgClosed_residueField
    (Valuation.valuationSubring.integers (Valued.v : Valuation (PadicAlgCl p) NNReal))

theorem Core.testCart_of_fib :
    ∀ C : Core, C.Fib → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart := by
  intro C hF hS p _ y τ
  have := isAlgClosed_residueField_OO p
  have := C.proper
  have := τ.smooth
  have := τ.sep
  have := τ.qc
  have := τ.j_loc
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  let K := FractionRing τ.V
  let t : Sp K ⟶ Sp τ.V := spMap (algebraMap τ.V K)
  let q : Sp (kb p) ⟶ Sp τ.V := rPt p ≫ spMap τ.j
  have hqy : q ≫ τ.y₀ = rPt p ≫ y := by rw [Category.assoc, τ.fac]
  let h : τ.H.left ⟶ pullback C.GG.hom τ.y₀ := pullback.lift τ.f τ.H.hom τ.f_over
  have h₁ : h ≫ pullback.fst _ _ = τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = τ.H.hom := pullback.lift_snd _ _ _

  have hA : IsPullback C.a C.A.hom C.GG.hom C.U.ι :=
    isPullback_of_comp_mono C.cart
  have hφ : IsPullback τ.φ (pullback.snd τ.H.hom t) C.A.hom τ.yK := τ.φ_cart.1
  have := C.ab.geomConnected
  have : ConnectedSpace ↥(pullback τ.H.hom t) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ hφ
  have hK : IsPullback (pullback.fst τ.H.hom t ≫ h) (pullback.snd τ.H.hom t) (pullback.snd C.GG.hom τ.y₀) t := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, h₂, pullback.condition])
      (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    have := hφ.paste_horiz hA
    rw [τ.φ_f, τ.yK_fac] at this
    rw [Category.assoc, h₁]
    exact this

  let h' : pullback τ.H.hom q ⟶ pullback C.GG.hom (rPt p ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
      rw [Category.assoc, τ.f_over, pullback.condition_assoc, hqy])
  have h₁' : h' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂' : h' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion h' := τ.imm h' h₁' h₂'
  let b : pullback C.GG.hom (rPt p ≫ y) ⟶ pullback C.GG.hom τ.y₀ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by
      rw [Category.assoc, hqy, pullback.condition])
  have b₁ : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have b₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q := pullback.lift_snd _ _ _
  have hX : IsPullback b (pullback.snd _ _) (pullback.snd C.GG.hom τ.y₀) q := by
    refine IsPullback.of_right ?_ b₂ (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    rw [b₁, hqy]
    exact .of_hasPullback _ _
  have hsurj : Function.Surjective h' := by
    refine surjective_of_isClosedImmersion_of_points h' (pullback.snd _ _) fun x hx ↦ ?_
    obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
    refine ⟨pullback.lift c (𝟙 _) (by rw [Category.id_comp]; exact hc₁), pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, h₁', pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂', pullback.lift_snd, hx]
  have hq : IsLocalRing.closedPoint τ.V ∈ Set.range q := by
    refine ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    exact IsLocalRing.comap_closedPoint ((IsLocalRing.residue (OO p)).comp τ.j)
  have : IsIso h := isIso_of_genericFibre_of_specialFibre τ.V K h (pullback.snd _ _) τ.H.hom h₂ hK hq hX
    (a := pullback.fst _ _) (h' := h') (by rw [h₂']; exact .of_hasPullback _ _)
    (pullback.hom_ext (by simp only [Category.assoc, h₁, b₁, h₁'])
      (by simp only [Category.assoc, h₂, b₂, reassoc_of% h₂', pullback.condition]))
    ⟨h'.isClosedEmbedding.injective, hsurj⟩
  exact IsPullback.of_iso_pullback ⟨τ.f_over⟩ (asIso h) h₁ h₂

end GlobalTheory.ZJ
end
