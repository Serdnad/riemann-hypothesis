module

public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem memKL_push (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} (x : T' ⟶ A') (hx : MemKL A' L' x) : MemKL A L (pushPt h.1.w x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst T' A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst T' A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T' A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L' _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

end

theorem memKL_iff_memKL_push : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) (A' : Over S') [GrpObj A] [GrpObj A'] (φ : A'.left ⟶ A.left) (L : LB A.left) (L' : LB A'.left) (h : IsGrpPullback A' A f φ), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (T' : Over S') (x : T' ⟶ A'), GlobalTheory.MemKL A' L' x ↔ GlobalTheory.MemKL A L (pushPt h.1.w x) :=
  fun _ _ _ _ _ _ _ _ _ _ h hL hL' hw _ x => ⟨memKL_push h hL hL' hw x, memKL_of_push h hL hL' hw x⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.flat_closedSubscheme_finite_over_localRing : ∀ (V : Type) [CommRing V] [IsLocalRing V] (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → IsFinite (j ≫ f) → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → ∃ I : Ideal (X.presheaf.stalk (j h)), ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  first | exact @GlobalTheory.StabFlat.flat_of_isFinite_of_ideals | exact GlobalTheory.StabFlat.flat_of_isFinite_of_ideals | (intros; apply GlobalTheory.StabFlat.flat_of_isFinite_of_ideals <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open scoped TensorProduct in
theorem flat_SpecMap_of_flat_localization_maximal (V : Type) [CommRing V] (C : CommRingCat.{0})
    (f : CommRingCat.of V ⟶ C)
    (h : ∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd (Spec.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m)))))) :
    Flat (Spec.map f) := by
  rw [Flat.SpecMap_iff]
  letI : Algebra V C := f.hom.toAlgebra
  have key : Module.Flat V C := by
    refine Module.flat_of_isLocalized_maximal V C (fun P _ => Localization.AtPrime P ⊗[V] C)
      (fun P _ => TensorProduct.mk V (Localization.AtPrime P) C 1) fun P _ => ?_
    have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (Localization.AtPrime P) C)).flip
    have h1 := h P
    have h2 := sq.isoPullback_hom_snd
    have h3 : Flat (sq.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V C)))
        (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime P))))) := h1
      infer_instance
    rw [h2, Flat.SpecMap_iff] at h3
    haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[V] C) :=
      RingHom.flat_algebraMap_iff.mp h3
    exact Module.Flat.trans V (Localization.AtPrime P) _
  exact key

theorem flat_of_isFinite_of_flat_localization_maximal :
    ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  intro V _ H hfin h
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨f, hf⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  have hf' : H.hom = H.left.isoSpec.hom ≫ Spec.map f := by rw [hf]; simp
  have : Flat (Spec.map f) := by
    refine flat_SpecMap_of_flat_localization_maximal V _ f fun m _ => ?_
    have h1 := h m
    rw [hf, ← pullbackRightPullbackFstIso_inv_snd_snd]
    haveI : Flat (pullback.snd H.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m))))) := h1
    infer_instance
  rw [hf']
  infer_instance

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteOnePoint

theorem isIso_of_formallyUnramified {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [FormallyUnramified f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → p = s) : IsIso f := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  have ho : IsOpenImmersion s :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) s f
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal f))) (by rw [hs]; infer_instance)
  have := LocallyOfFiniteType.jacobsonSpace f
  have hsurj : Surjective s := ⟨fun x => by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.range s)ᶜ) ⟨x, hx⟩
      s.isOpenEmbedding.isOpen_range.isClosed_compl.isLocallyClosed
    refine hc ⟨IsLocalRing.closedPoint K, ?_⟩
    rw [← h _ (pointOfClosedPoint_comp f c hc')]
    exact pointOfClosedPoint_apply f c hc' _⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).2 ⟨ho, hsurj⟩
  have : IsIso (s ≫ f) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s f

theorem formallyUnramified_of_isFinite {K : Type} [Field K] [CharZero K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G] (hf : IsFinite G.hom) :
    FormallyUnramified G.hom := by
  obtain ⟨N, hN, h⟩ := FiniteFlatKilled.main K G hf inferInstance
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have h1 : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have h2 := formallyUnramified_mulA _ G N hu
  have h3 : (mulA G N).left = G.hom ≫ η[G].left := by
    rw [show mulA G N = 1 from h, Hom.one_def]
    rfl
  rw [h3] at h2
  exact FormallyUnramified.of_comp G.hom η[G].left

theorem main : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (H : Over S) (j : H ⟶ B), Mono j → IsFinite H.hom → (∃ y : 𝟙_ _ ⟶ H, y ≫ j = 1) → (∀ (T : Over S) (x y : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j) * (y ≫ j)⁻¹) → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (t : Spec (CommRingCat.of K) ⟶ S), (∀ x : Over.mk t ⟶ H, x ≫ j = 1) → ∀ (T : Over S) (_ : T ⟶ Over.mk t) (y : T ⟶ H), y ≫ j = 1 := by
  intro S B _ _ H j hj hf ⟨e, he⟩ hsub K _ _ _ t hpt T a y
  have he' : ∀ T : Over S, (toUnit T ≫ e) ≫ j = 1 := fun T => by
    rw [Category.assoc, he, MonObj.comp_one]
  have hinv : ∀ (T : Over S) (x : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j)⁻¹ := fun T x => by
    obtain ⟨z, hz⟩ := hsub T (toUnit T ≫ e) x
    exact ⟨z, by rw [hz, he', _root_.one_mul]⟩
  obtain ⟨i, hi⟩ := hinv H (𝟙 H)
  obtain ⟨w, hw⟩ := hinv (H ⊗ H) (snd H H)
  obtain ⟨m, hm⟩ := hsub (H ⊗ H) (fst H H) w
  obtain ⟨_, _⟩ := ReducedSubgroup.exists_grpObj_of_mono j e m i
    (by rw [he, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    (by
      rw [hm, hw, inv_inv, Hom.mul_def]
      congr 1)
    (by rw [hi, Category.id_comp, Hom.inv_def])
  haveI : IsCommMonObj H :=
    ⟨by rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩
  have hfin : IsFinite (pullback.snd H.hom t) := inferInstance
  have hunr : FormallyUnramified (pullback.snd H.hom t) :=
    formallyUnramified_of_isFinite ((Over.pullback t).obj H) hfin
  have hiso : IsIso (pullback.snd H.hom t) := by
    refine isIso_of_formallyUnramified _
      (pullback.lift (toUnit (Over.mk t) ≫ e).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) fun p hp => ?_
    let x : Over.mk t ⟶ H := Over.homMk (p ≫ pullback.fst H.hom t) (by
      change (p ≫ pullback.fst H.hom t) ≫ H.hom = t
      rw [Category.assoc, pullback.condition, reassoc_of% hp])
    have hx : x = toUnit _ ≫ e := by rw [← cancel_mono j, hpt, he']
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← hx]
      rfl
    · rw [pullback.lift_snd, hp]
  have key : ∀ y₁ y₂ : T ⟶ H, y₁ = y₂ := fun y₁ y₂ => by
    have h : pullback.lift y₁.left a.left ((Over.w y₁).trans (Over.w a).symm) =
        pullback.lift (f := H.hom) (g := t) y₂.left a.left ((Over.w y₂).trans (Over.w a).symm) := by
      rw [← cancel_mono (pullback.snd H.hom t)]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
    ext1
    exact (pullback.lift_fst _ _ _).symm.trans
      ((h =≫ pullback.fst H.hom t).trans (pullback.lift_fst _ _ _))
  rw [key y (toUnit T ≫ e), he']

end FiniteOnePoint

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteStabiliser

theorem apply_eq_of_range_subset_affine {K : Type} [Field K] {F Z : Scheme.{0}} [IsIntegral F]
    (q : F ⟶ Spec (.of K)) [UniversallyClosed q] (h : F ⟶ Z) {W : Z.Opens} (hW : IsAffineOpen W)
    (hh : ∀ a, h a ∈ W) (a b : F) : h a = h b := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hh c
  have : IsAffine W := hW
  let l := IsOpenImmersion.lift W.ι h hr
  have e : l ≫ W.ι = h := IsOpenImmersion.lift_fac _ _ _
  have e' : l = F.toSpecΓ ≫ Spec.map l.appTop ≫ W.toScheme.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  letI := (isField_of_universallyClosed K q).toField
  have hab : F.toSpecΓ a = F.toSpecΓ b :=
    Subsingleton.elim (α := PrimeSpectrum Γ(F, ⊤)) _ _
  rw [← e, e']
  simp only [Scheme.Hom.comp_apply, hab]

theorem slice_eq {K : Type} [Field K] [IsAlgClosed K] {F B Z : Over (Spec (CommRingCat.of K))}
    [IsIntegral F.left] [UniversallyClosed F.hom] [IsIntegral B.left] [LocallyOfFiniteType B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (g : F ⊗ B ⟶ Z) (b : 𝟙_ _ ⟶ B) (z : Z.left)
    (hz : ∀ a, (lift (𝟙 F) (toUnit F ≫ b) ≫ g).left a = z) (f f' : 𝟙_ _ ⟶ F) :
    lift (toUnit B ≫ f) (𝟙 B) ≫ g = lift (toUnit B ≫ f') (𝟙 B) ≫ g := by
  have huc : UniversallyClosed (snd F B).left := by
    change UniversallyClosed (pullback.snd F.hom B.hom); infer_instance
  let j : (𝟙_ _ ⟶ B) → (F ⟶ F ⊗ B) := fun x ↦ lift (𝟙 F) (toUnit F ≫ x)
  have hpb (x : 𝟙_ _ ⟶ B) : IsPullback (j x).left F.hom (snd F B).left x.left := by
    have hw : x.left ≫ B.hom = 𝟙 _ := Over.w x
    have hr : IsPullback (fst F B).left (snd F B).left F.hom B.hom := .of_hasPullback F.hom B.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : (j x).left ≫ (fst F B).left = 𝟙 F.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hw]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Over.comp_left]
      rfl
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
    Z.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hcl : IsClosed ((snd F B).left '' ((g.left ⁻¹ᵁ W : (F ⊗ B).left.Opens) : Set _)ᶜ) :=
    (snd F B).left.isClosedMap _ (g.left ⁻¹ᵁ W).isOpen.isClosed_compl
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hlft : LocallyOfFiniteType ((lift (toUnit B ≫ f) (𝟙 B) ≫ g).left ≫ Z.hom) := by
    rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Z.hom _ hcl.isOpen_compl.isLocallyClosed
    (hcl.isOpen_compl.dense ⟨b.left pt, ?_⟩) (fun x hxV hx ↦ ?_) (by rw [Over.w, Over.w]))
  · rintro ⟨w, hw, hwb⟩
    obtain ⟨a, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hpb b) w pt hwb
    apply hw
    change g.left ((j b).left a) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hz]
    exact hzW
  · let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B :=
      Over.homMk (pointOfClosedPoint (K := K) B.hom x hx)
        (pointOfClosedPoint_comp (K := K) B.hom x hx)
    have hp (s) : p.left s = x := pointOfClosedPoint_apply (K := K) B.hom x hx s
    have hin (a : F.left) : (j p ≫ g).left a ∈ W := by
      by_contra hn
      refine hxV ⟨(j p).left a, ?_, ?_⟩
      · rw [Over.comp_left, Scheme.Hom.comp_apply] at hn
        exact hn
      · rw [← Scheme.Hom.comp_apply, (hpb p).w, Scheme.Hom.comp_apply, hp]
    have key (u : 𝟙_ _ ⟶ F) :
        (lift (toUnit B ≫ u) (𝟙 B) ≫ g).left x = (j p ≫ g).left (u.left pt) := by
      have e : p ≫ lift (toUnit B ≫ u) (𝟙 B) ≫ g = u ≫ j p ≫ g := by
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext1
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
      rw [← hp pt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left,
        ← Over.comp_left, e]
    rw [key, key]
    exact apply_eq_of_range_subset_affine (K := K) F.hom _ hW hin _ _

theorem finite_closedPoints_of_contracted {K : Type} [Field K] [IsAlgClosed K]
    {B Z : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsIntegral B.left] [IsProper B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z)
    (hφ : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite)
    (S : TopologicalSpace.Closeds B.left) (hS : IsIrreducible (S : Set B.left)) (z : Z.left)
    (hz : ∀ y ∈ S, φ.left y = z) : ((S : Set B.left) ∩ closedPoints B.left).Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have hrange : Set.range I.subschemeι = S := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let F : Over (Spec (CommRingCat.of K)) := Over.mk (I.subschemeι ≫ B.hom)
  let i : F ⟶ B := Over.homMk I.subschemeι rfl
  have hemb := I.subschemeι.isClosedEmbedding
  have : IsReduced F.left := ReducedSubgroup.isReduced_subscheme_vanishingIdeal S
  have : IrreducibleSpace F.left := by
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hrange]; exact Subtype.irreducibleSpace hS
    exact hemb.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  have : IsIntegral F.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsProper F.hom := by change IsProper (I.subschemeι ≫ B.hom); infer_instance
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpt (y : B.left) (hy : y ∈ (S : Set B.left) ∩ closedPoints B.left) :
      ∃ u : 𝟙_ _ ⟶ F, (u ≫ i).left pt = y := by
    obtain ⟨a, rfl⟩ : y ∈ Set.range I.subschemeι := hrange ▸ hy.1
    have ha : IsClosed ({a} : Set F.left) := by
      refine hemb.isClosed_iff_image_isClosed.mpr ?_
      rw [Set.image_singleton]
      exact hy.2
    refine ⟨Over.homMk (pointOfClosedPoint (K := K) F.hom a ha)
      (pointOfClosedPoint_comp (K := K) F.hom a ha), ?_⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg I.subschemeι (pointOfClosedPoint_apply (K := K) F.hom a ha pt)
  rcases ((S : Set B.left) ∩ closedPoints B.left).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨u₀, -⟩ := hpt y₀ hy₀
  refine (hφ.image fun s ↦ (s * (u₀ ≫ i)).left pt).subset fun y hy ↦ ?_
  obtain ⟨u, rfl⟩ := hpt y hy
  refine ⟨(u ≫ i) * (u₀ ≫ i)⁻¹, ?_, by simp only [inv_mul_cancel_right]⟩
  have key := slice_eq (((fst F B ≫ i) * snd F B) ≫ φ) (1 : 𝟙_ _ ⟶ B) z (fun a ↦ by
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_one,
      _root_.mul_one, Category.id_comp, Over.comp_left, Scheme.Hom.comp_apply]
    exact hz _ (hrange.le ⟨a, rfl⟩)) u u₀
  have key' := congrArg (fun t ↦ ((toUnit B ≫ u₀ ≫ i)⁻¹ * 𝟙 B) ≫ t) key
  have hu (t : B ⟶ B) : t ≫ toUnit B = toUnit B := toUnit_unique _ _
  simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, hu, Category.comp_id,
    mul_inv_cancel_left, Category.id_comp] at key'
  change (toUnit B ≫ ((u ≫ i) * (u₀ ≫ i)⁻¹) * 𝟙 B) ≫ φ = φ
  simp only [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc, ← Category.assoc]
  exact key'

theorem locallyQuasiFinite_of_finite_stabiliser :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z), {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite → LocallyQuasiFinite φ.left := by
  intro K _ _ B _ _ hB Z _ _ φ hφ
  have := hB.proper
  have := hB.smooth
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth B.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have : IsProper (φ.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsProper φ.left := .of_comp _ Z.hom
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : IsNoetherian B.left := {}
  refine locallyQuasiFinite_of_finite_fibres_closedPoints φ.left fun y hy ↦ ?_
  have hc : IsClosed (φ.left ⁻¹' {φ.left y}) := by
    refine IsClosed.preimage φ.left.continuous ?_
    simpa using φ.left.isClosedMap _ hy
  refine finite_of_isClosed_of_finite_inter_closedPoints hc ?_
  obtain ⟨T, hT, hTc, hTi, hTU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hc
  rw [hTU, Set.sUnion_eq_biUnion, Set.iUnion₂_inter]
  refine hT.biUnion fun S hS ↦ ?_
  refine finite_closedPoints_of_contracted φ hφ ⟨S, hTc S hS⟩ (hTi S hS) (φ.left y) fun w hw ↦ ?_
  exact hTU.ge ⟨S, hS, hw⟩

end GlobalTheory.FiniteStabiliser
end
