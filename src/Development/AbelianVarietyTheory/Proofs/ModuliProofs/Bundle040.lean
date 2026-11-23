module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isOpenImmersion_of_isFinite_of_densePart {U W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian Z] [GlobalTheory.IsNormalScheme Z] (j : U ⟶ W) (g : W ⟶ Z) [IsFinite g]
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] [Flat (j ≫ g)]
    [SurjectiveOnStalks (j ≫ g)] : IsOpenImmersion g := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  let V : Z.Opens := GlobalTheory.IsNormalScheme.component
    ⟨_, irreducibleComponent_mem_irreducibleComponents (g (genericPoint W))⟩
  have hVc : IsClosed (V : Set Z) := GlobalTheory.IsNormalScheme.isClosed_component _
  have : IsIntegral V.toScheme := GlobalTheory.IsNormalScheme.isIntegral_component _
  have hr : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (((genericPoint_spec W).specializes (Set.mem_univ w)).map g.continuous).mem_closed hVc
      mem_irreducibleComponent
  let g' : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : IsFinite (g' ≫ V.ι) := hg' ▸ inferInstance
  have : IsFinite g' := IsFinite.of_comp g' V.ι
  have hlift : j ≫ g' = IsOpenImmersion.lift V.ι (j ≫ g) (by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨j w, rfl⟩) :=
    IsOpenImmersion.lift_uniq _ _ _ _ (by rw [Category.assoc, hg'])
  have hs : SurjectiveOnStalks ((j ≫ g') ≫ V.ι) := by rw [Category.assoc, hg']; infer_instance
  have : Flat (j ≫ g') := by
    rw [hlift]
    exact MorphismProperty.of_isPullback (P := @Flat)
      (IsOpenImmersion.isPullback_lift_id (j ≫ g) V.ι _).flip ‹Flat (j ≫ g)›
  have : SurjectiveOnStalks (j ≫ g') := SurjectiveOnStalks.of_comp _ V.ι
  have : IsDominant g' := by
    obtain ⟨u', hu', hu''⟩ := Flat.generalizingMap (j ≫ g')
      ((genericPoint_spec V.toScheme).specializes (Set.mem_univ ((j ≫ g') u)))
    refine ⟨?_⟩
    refine Dense.mono (s₁ := {genericPoint V.toScheme}) ?_ ?_
    · rintro _ rfl
      exact ⟨j u', hu''⟩
    · exact dense_iff_closure_eq.mpr (genericPoint_spec V.toScheme)
  have : IsIso (g'.stalkMap (genericPoint W)) := by
    rw [← hu]
    have h := isIso_stalkMap_of_flat_of_surjectiveOnStalks (j ≫ g') u
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j u
    rw [Scheme.Hom.stalkMap_comp] at h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g'.stalkMap (j u)) (j.stalkMap u) _ h
  have := isIso_of_isIntegralHom_of_isIso_stalkMap g' (fun y => inferInstance)
  rw [← hg']
  infer_instance

theorem etale_and_surjective_of_densePart_mono_finiteEtale : ∀ (S S₀ Y Y₀ Z : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian Y] (j : S₀ ⟶ S) (j' : Y₀ ⟶ Y) (e : Y ⟶ S) (e₀ : Y₀ ⟶ S₀) (p : Z ⟶ S) (i : Y₀ ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsFinite e → j' ≫ e = e₀ ≫ j → IsFinite p → Etale p → i ≫ p = e₀ ≫ j → Surjective e₀ → Etale e₀ → Mono i → Etale e ∧ Surjective e := by
  intro S S₀ Y Y₀ Z _ _ j j' e e₀ p i hS hY _ _ _ _ _ _ _ _ _ hj _ _ hi _ _ _
  have hYn := GlobalTheory.IsNormalScheme.of_pred hY
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
      ((isNormalScheme_iff S).mp (GlobalTheory.IsNormalScheme.of_pred hS)))
  obtain ⟨g, ⟨hg₁, hg₂⟩, -⟩ := existsUnique_lift_of_densePart Y Y₀ S Z j' hY ‹_› ‹_› ‹_› ‹_› p e i
    inferInstance (hi.trans hj.symm)
  have : IsFinite (g ≫ p) := hg₂ ▸ inferInstance
  have : IsFinite g := IsFinite.of_comp g p
  let k : Y₀ ⟶ pullback p j := pullback.lift i e₀ hi
  have hk₁ : k ≫ pullback.fst p j = i := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd p j = e₀ := pullback.lift_snd _ _ _
  have : Etale (k ≫ pullback.snd p j) := hk₂ ▸ inferInstance
  have : Etale k := Etale.of_comp k (pullback.snd p j)
  have : Mono (k ≫ pullback.fst p j) := hk₁ ▸ inferInstance
  have : Mono k := mono_of_mono k (pullback.fst p j)
  have : IsOpenImmersion k := IsOpenImmersion.of_flat_of_mono k
  have : Flat i := hk₁ ▸ inferInstance
  have : SurjectiveOnStalks i := hk₁ ▸ inferInstance
  constructor
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _
      (GlobalTheory.IsNormalScheme.iSup_component (X := Y))]
    intro W
    have : IsDominant (j' ∣_ GlobalTheory.IsNormalScheme.component W) :=
      IsZariskiLocalAtTarget.restrict (P := @IsDominant) ‹IsDominant j'› _
    have h : j' ∣_ GlobalTheory.IsNormalScheme.component W ≫ (GlobalTheory.IsNormalScheme.component W).ι ≫ g =
        (j' ⁻¹ᵁ GlobalTheory.IsNormalScheme.component W).ι ≫ i := by
      rw [morphismRestrict_ι_assoc, hg₁]
    have : Flat (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have : SurjectiveOnStalks (j' ∣_ GlobalTheory.IsNormalScheme.component W ≫
        (GlobalTheory.IsNormalScheme.component W).ι ≫ g) := h ▸ inferInstance
    have := isOpenImmersion_of_isFinite_of_densePart (j' ∣_ GlobalTheory.IsNormalScheme.component W)
      ((GlobalTheory.IsNormalScheme.component W).ι ≫ g)
    rw [← hg₂, ← Category.assoc]
    infer_instance
  · have : IsDominant (j' ≫ e) := hj ▸ inferInstance
    have : IsDominant e := IsDominant.of_comp j' e
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, ← e.isClosedMap.isClosed_range.closure_eq]
    exact e.denseRange.closure_range

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CocycleGlue

theorem exists_desc (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i := by
  exact GlobalTheory.CoverGlue.exists_hom (ψ := D.ι) (fun i => inferInstance)
    (fun x => by
      obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
      exact ⟨i, y, hy⟩)
    p (B := fun i j => D.V (i, j)) (a := fun i j => D.f i j) (b := fun i j => D.t i j ≫ D.f j i)
    (fun i j => IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)) h

theorem exists_glue {S : Scheme.{0}} {I : Type} (V X : I → Scheme.{0}) (κ : ∀ i, V i ⟶ S)
    (hκ : ∀ i, IsOpenImmersion (κ i)) (g : ∀ i, X i ⟶ V i) (B : I → I → Scheme.{0})
    (a : ∀ i j, B i j ⟶ X i) (b : ∀ i j, B i j ⟶ X j)
    (ha : ∀ i j, IsPullback (a i j) (b i j ≫ g j) (g i ≫ κ i) (κ j))
    (hb : ∀ i j, IsPullback (b i j) (a i j ≫ g i) (g j ≫ κ j) (κ i))
    (hc : ∀ i j k (T : Scheme.{0}) (x : T ⟶ B i j) (y : T ⟶ B j k) (z : T ⟶ B i k),
      x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) :
    ∃ (A : Scheme.{0}) (F : A ⟶ S) (ψ : ∀ i, X i ⟶ A),
      (∀ i, IsPullback (ψ i) (g i) F (κ i)) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  classical
  have hma : ∀ i j, IsOpenImmersion (a i j) := fun i j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (ha i j).flip (hκ j)
  have mono_a : ∀ i j, Mono (a i j) := fun i j => by
    have := hma i j
    infer_instance
  have mono_κ : ∀ i, Mono (κ i) := fun i => by
    have := hκ i
    infer_instance
  have ext_a : ∀ i j {T : Scheme.{0}} (x y : T ⟶ B i j), x ≫ a i j = y ≫ a i j → x = y :=
    fun i j _ x y h => (mono_a i j).right_cancellation x y h
  have ext_κ : ∀ i {T : Scheme.{0}} (x y : T ⟶ V i), x ≫ κ i = y ≫ κ i → x = y :=
    fun i _ x y h => (mono_κ i).right_cancellation x y h
  have hbw : ∀ i j, b i j ≫ g j ≫ κ j = a i j ≫ g i ≫ κ i := fun i j => by
    simpa only [Category.assoc] using (hb i j).w
  have iso_a : ∀ i, IsIso (a i i) := fun i => by
    have hw : a i i ≫ g i = b i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (ha i i).w)
    refine ⟨⟨(ha i i).lift (𝟙 _) (g i) (by simp), ?_, (ha i i).lift_fst _ _ _⟩⟩
    apply ext_a i i
    rw [Category.assoc, (ha i i).lift_fst, Category.comp_id, Category.id_comp]
  have iso_b : ∀ i, IsIso (b i i) := fun i => by
    have hw : b i i ≫ g i = a i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (hb i i).w)
    have hmb : Mono (b i i) := by
      have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hb i i).flip (hκ i)
      infer_instance
    refine ⟨⟨(hb i i).lift (𝟙 _) (g i) (by simp), ?_, (hb i i).lift_fst _ _ _⟩⟩
    apply hmb.right_cancellation
    rw [Category.assoc, (hb i i).lift_fst, Category.comp_id, Category.id_comp]
  have diag : ∀ i, a i i = b i i := fun i => by
    have := iso_a i
    have := iso_b i
    have h := hc i i i (B i i) (𝟙 _) (b i i ≫ inv (a i i)) (𝟙 _) (by simp) (by simp)
    have h2 : inv (a i i) ≫ b i i = 𝟙 _ := by
      rw [← cancel_epi (b i i)]
      simpa using h
    rw [IsIso.inv_comp_eq, Category.comp_id] at h2
    exact h2.symm
  have ht : ∀ i j, ∃ t : B i j ⟶ B j i, t ≫ a j i = b i j ∧ t ≫ b j i = a i j := fun i j => by
    have := iso_a i
    refine ⟨(ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w, (ha j i).lift_fst _ _ _, ?_⟩
    have h := hc i j i (B i j) (𝟙 _) ((ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w)
      (a i j ≫ inv (a i i)) (by rw [IsPullback.lift_fst, Category.id_comp]) (by simp)
    rw [h, ← diag i]
    simp
  choose t ht_a ht_b using ht
  have t_id : ∀ i, t i i = 𝟙 _ := fun i =>
    ext_a i i _ _ (by rw [ht_a, Category.id_comp, diag])
  have t_inv : ∀ i j, t i j ≫ t j i = 𝟙 _ := fun i j =>
    ext_a i j _ _ (by rw [Category.assoc, ht_a, ht_b, Category.id_comp])
  have ht' : ∀ i j k, ∃ τ : pullback (a i j) (a i k) ⟶ pullback (a j k) (a j i),
      τ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j ∧
        τ ≫ pullback.fst _ _ ≫ a j k = pullback.fst _ _ ≫ b i j := fun i j k => by
    have w : (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j =
        (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
      calc (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j
          = pullback.fst (a i j) (a i k) ≫ a i j ≫ g i ≫ κ i := by rw [Category.assoc, hbw]
        _ = pullback.snd (a i j) (a i k) ≫ a i k ≫ g i ≫ κ i := by rw [pullback.condition_assoc]
        _ = (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
          rw [← hbw]
          simp only [Category.assoc]
    refine ⟨pullback.lift ((ha j k).lift _ _ w) (pullback.fst _ _ ≫ t i j) ?_, pullback.lift_snd _ _ _, ?_⟩
    · rw [IsPullback.lift_fst, Category.assoc, ht_a]
    · rw [pullback.lift_fst_assoc, IsPullback.lift_fst]
  choose t' ht'_snd ht'_fst using ht'
  have cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _ := fun i j k => by
    have c1 := hc i j k _ (pullback.fst (a i j) (a i k)) (t' i j k ≫ pullback.fst _ _)
      (pullback.snd (a i j) (a i k)) (by rw [Category.assoc, ht'_fst]) pullback.condition
    have c2 : (t' i j k ≫ t' j k i) ≫ pullback.fst _ _ = pullback.snd (a i j) (a i k) ≫ t i k := by
      apply ext_a k i
      simp only [Category.assoc, ht'_fst, ht_a]
      simpa only [Category.assoc] using c1
    have c2' : ∀ {Z : Scheme.{0}} (h : B k i ⟶ Z),
        t' i j k ≫ t' j k i ≫ pullback.fst _ _ ≫ h = pullback.snd (a i j) (a i k) ≫ t i k ≫ h := by
      intro Z h
      simp only [← Category.assoc, c2]
    apply pullback.hom_ext
    · apply ext_a i j
      simp only [Category.assoc, Category.id_comp, ht'_fst]
      rw [c2' (b k i), ht_b]
      exact pullback.condition.symm
    · simp only [Category.assoc, Category.id_comp, ht'_snd]
      rw [c2' (t k i), t_inv, Category.comp_id]
  let D : Scheme.GlueData.{0} :=
    { J := I, U := X, V := fun p => B p.1 p.2, f := a, f_mono := mono_a,
      f_hasPullback := fun _ _ _ => inferInstance, f_id := iso_a, t := t, t_id := t_id,
      t' := t', t_fac := ht'_snd, cocycle := cocycle, f_open := hma }
  obtain ⟨F, hF⟩ := exists_desc D (fun i => g i ≫ κ i) (fun i j => by
    change a i j ≫ g i ≫ κ i = (t i j ≫ a j i) ≫ g j ≫ κ j
    rw [ht_a]
    exact (hbw i j).symm)
  have hV : ∀ i j, IsPullback (a i j) (b i j) (D.ι i) (D.ι j) := fun i j => by
    have h : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
      IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
    have e : D.t i j ≫ D.f j i = b i j := ht_a i j
    rw [e] at h
    exact h
  refine ⟨D.glued, F, fun i => D.ι i, fun i => ?_, hV⟩
  have hw : D.ι i ≫ F = g i ≫ κ i := hF i
  have hιi : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  have hr : ∀ {T : Scheme.{0}} (u : T ⟶ D.glued) (v : T ⟶ V i), u ≫ F = v ≫ κ i →
      Set.range u ⊆ Set.range (D.ι i) := by
    intro T u v huv x hx
    obtain ⟨t0, rfl⟩ := hx
    obtain ⟨j, y, hy⟩ := D.ι_jointly_surjective (u t0)
    have e1 : (g j ≫ κ j) y = κ i (v t0) := by
      have h1 := congrArg (fun φ : T ⟶ S => φ t0) huv
      have h2 := congrArg (fun φ : D.U j ⟶ S => φ y) (hF j)
      simp only [Scheme.Hom.comp_apply] at h1 h2 ⊢
      rw [← h2, hy]
      exact h1
    obtain ⟨z', hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g j ≫ κ j) (g := κ i) y (v t0) e1
    refine ⟨b j i ((ha j i).isoPullback.inv z'), ?_⟩
    have h3 := congrArg (fun φ : pullback (g j ≫ κ j) (κ i) ⟶ D.glued => φ z')
      (congrArg (fun φ => (ha j i).isoPullback.inv ≫ φ) (hV j i).w)
    simp only [Scheme.Hom.comp_apply] at h3
    rw [← h3, ← hy, ← hz1, ← IsPullback.isoPullback_inv_fst (ha j i), Scheme.Hom.comp_apply]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (D.ι i) s.fst (hr s.fst s.snd s.condition)) ?_ ?_ ?_)
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    apply ext_κ i
    rw [Category.assoc, ← hw, ← Category.assoc, IsOpenImmersion.lift_fac, s.condition]
  · intro s m h1 _
    apply (cancel_mono (D.ι i)).1
    rw [h1, IsOpenImmersion.lift_fac]

theorem glue_over_opens : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  intro S I U G B a b h1 h2 h3
  have ha : ∀ i j, IsPullback (a i j) (b i j ≫ (G j).hom) ((G i).hom ≫ (U i).ι) (U j).ι := by
    intro i j
    have h := (h1 i j).paste_vert (isPullback_opens_inf (U i) (U j))
    rw [← (h2 i j).w] at h
    exact h
  have hb : ∀ i j, IsPullback (b i j) (a i j ≫ (G i).hom) ((G j).hom ≫ (U j).ι) (U i).ι := by
    intro i j
    have h := (h2 i j).paste_vert (isPullback_opens_inf (U i) (U j)).flip
    rw [← (h1 i j).w] at h
    exact h
  obtain ⟨A, F, ψ, hψ, hab⟩ := exists_glue (fun i => (U i).toScheme) (fun i => (G i).left)
    (fun i => (U i).ι) (fun i => inferInstance) (fun i => (G i).hom) (fun i j => (B i j).left)
    a b ha hb h3
  exact ⟨Over.mk F, ψ, hψ, hab⟩

end GlobalTheory.CocycleGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem isFinite_and_etale_of_comp_of_finite_etale_cover :
    ∀ (X Y Z : Scheme.{0}) (q : X ⟶ Y) (π : Y ⟶ Z), IsFinite q → Etale q → Surjective q → IsFinite (q ≫ π) → Etale (q ≫ π) → IsSeparated π → LocallyOfFinitePresentation π → IsFinite π ∧ Etale π := by
  intro X Y Z q π _ _ _ _ _ _ _
  have he : Etale π := GlobalTheory.etale_of_comp_of_etale_of_surjective q π
  have : UniversallyClosed π := UniversallyClosed.of_comp_surjective q π
  have : IsProper π := {}
  have : LocallyQuasiFinite π := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := π.formallyUnramified_appLE hU hV e
    have h₂ := π.finiteType_appLE hU hV e
    algebraize [(π.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact ⟨.of_isProper_of_locallyQuasiFinite _, he⟩

end GlobalTheory.HkFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isIso_near_normal_point_of_finite_birational : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  first | exact @GlobalTheory.FiniteBirationalNear.main | exact GlobalTheory.FiniteBirationalNear.main | (intros; apply GlobalTheory.FiniteBirationalNear.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_binary_op : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by
  intro S I U A G ψ o hU hpb hcomp

  let p : (A ⊗ A).left ⟶ S := (A ⊗ A).hom
  let V : I → (A ⊗ A).left.Opens := fun i => p ⁻¹ᵁ U i
  let q : ∀ i, (V i).toScheme ⟶ (U i).toScheme := fun i => p ∣_ U i
  have hP : ∀ i, IsPullback (V i).ι (q i) p (U i).ι := fun i => (isPullback_morphismRestrict p (U i)).flip

  let T₀ : ∀ i, Over (U i).toScheme := fun i => Over.mk (q i)
  let r : ∀ i, Over.mk ((T₀ i).hom ≫ (U i).ι) ⟶ A ⊗ A := fun i =>
    Over.homMk (V i).ι (hP i).w

  have hx : ∀ i, ∃ x : T₀ i ⟶ G i, (r i ≫ fst A A).left = x.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  have hy : ∀ i, ∃ y : T₀ i ⟶ G i, (r i ≫ snd A A).left = y.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  choose x hx using hx
  choose y hy using hy

  let f : ∀ i, (V i).toScheme ⟶ A.left := fun i => (lift (x i) (y i) ≫ o i).left ≫ ψ i
  have hf : ∀ i j (T : Scheme.{0}) (a : T ⟶ (V i).toScheme) (b : T ⟶ (V j).toScheme),
      a ≫ (V i).ι = b ≫ (V j).ι → a ≫ f i = b ≫ f j := by
    intro i j T a b hab
    let ea : Over.mk (a ≫ q i) ⟶ T₀ i := Over.homMk a rfl
    let eb : Over.mk (b ≫ q j) ⟶ T₀ j := Over.homMk b rfl
    have key := hcomp i j T (a ≫ q i) (b ≫ q j) (ea ≫ x i) (ea ≫ y i) (eb ≫ x j) (eb ≫ y j)
      (by
        simp only [Over.comp_left, Category.assoc, ← hx, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
      (by
        simp only [Over.comp_left, Category.assoc, ← hy, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
    rw [← comp_lift, ← comp_lift] at key
    simpa only [f, ea, eb, Over.homMk_left, Over.comp_left, Category.assoc] using key
  obtain ⟨F, hF, -⟩ := existsUnique_hom (fun i => (V i).ι) (fun i => inferInstance)
    (covers hU hP) f hf

  have hFw : F ≫ A.hom = (A ⊗ A).hom := by
    refine hom_ext (fun i => (V i).ι) (fun i => inferInstance) (covers hU hP) (fun i => ?_)
    rw [reassoc_of% (hF i)]
    simp only [f, Category.assoc, (hpb i).w]
    rw [← Category.assoc (lift (x i) (y i) ≫ o i).left, Over.w]
    exact (hP i).w.symm
  refine ⟨Over.homMk F hFw, ?_⟩
  intro i T x' y' x₀ y₀ hx₀ hy₀
  have hg : (lift x₀ y₀).left ≫ p = T.hom ≫ (U i).ι := Over.w (lift x₀ y₀)
  let k : T.left ⟶ (V i).toScheme := (hP i).lift (lift x₀ y₀).left T.hom hg
  have hk₁ : k ≫ (V i).ι = (lift x₀ y₀).left := (hP i).lift_fst _ _ _
  have hk₂ : k ≫ q i = T.hom := (hP i).lift_snd _ _ _
  let e : T ⟶ T₀ i := Over.homMk k hk₂
  have ex : e ≫ x i = x' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hx i, ← hx₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (fst A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_fst]
  have ey : e ≫ y i = y' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hy i, ← hy₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (snd A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_snd]
  rw [← ex, ← ey, ← comp_lift, Category.assoc]
  change (lift x₀ y₀).left ≫ F = (k ≫ (lift (x i) (y i) ≫ o i).left) ≫ ψ i
  rw [← hk₁, Category.assoc, hF i, Category.assoc]

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.DualRigidity

theorem eq_comp_section_of_const {X T Y : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y)
    (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) (y : Y) (hy : ∀ x : X, g x = y) :
    g = p ≫ ε ≫ g := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsAffine W := hW
  have hr : Set.range g ⊆ Set.range (Scheme.Opens.ι W) := by
    rintro _ ⟨x, rfl⟩
    rw [hy x, Scheme.Opens.range_ι]
    exact hyW
  have key := GlobalTheory.eq_comp_section_of_surjective_appTop p ε (IsOpenImmersion.lift (Scheme.Opens.ι W) g hr) h hs
  have := congrArg (· ≫ Scheme.Opens.ι W) key
  simpa only [Category.assoc, IsOpenImmersion.lift_fac] using this

end GlobalTheory.DualRigidity
end
