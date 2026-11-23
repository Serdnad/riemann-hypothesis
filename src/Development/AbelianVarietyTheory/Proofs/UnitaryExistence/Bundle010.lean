module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle007
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing

namespace GlobalTheory

namespace FibreFlat

section Algebra

variable {T : Type*} (K : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
  [Algebra T K] [IsFractionRing T K]

theorem includeRight_bijective {C : Type*} [CommRing C] [Algebra T C] {π : T} (hπ : Irreducible π)
    (hu : IsUnit (algebraMap T C π)) :
    Function.Bijective (Algebra.TensorProduct.includeRight : C →ₐ[T] K ⊗[T] C) := by
  have h : Algebra.algebraMapSubmonoid C (nonZeroDivisors T) ≤ IsUnit.submonoid C := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero ht) hπ
    change IsUnit _
    rw [map_mul, map_pow]
    exact (u.isUnit.map _).mul (hu.pow n)
  have h2 : Function.Bijective (algebraMap C (C ⊗[T] K)) :=
    (IsLocalization.atUnits C (S := C ⊗[T] K) _ h).bijective
  exact (Algebra.TensorProduct.comm T C K).bijective.comp h2

theorem ringHom_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra T A] [Algebra T B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat T B] (φ : A →ₐ[T] B)
    (hK : (Algebra.TensorProduct.map (AlgHom.id T K) φ : K ⊗[T] A →+* K ⊗[T] B).Flat)
    (hκ : (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
      ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat) : (φ : A →+* B).Flat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have key : ∀ (P : Ideal B) [P.IsPrime],
      (((IsScalarTower.toAlgHom T B (Localization.AtPrime P)).comp φ : A →ₐ[T] _) :
        A →+* Localization.AtPrime P).Flat := by
    intro P _
    let l := IsScalarTower.toAlgHom T B (Localization.AtPrime P)
    have hl : (l : B →+* Localization.AtPrime P).Flat :=
      RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ P.primeCompl)
    have hbc : ∀ (L : Type _) [CommRing L] [Algebra T L],
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat →
        (Algebra.TensorProduct.map (AlgHom.id T L) (l.comp φ) :
          L ⊗[T] A →+* L ⊗[T] Localization.AtPrime P).Flat := by
      intro L _ _ h
      rw [Algebra.TensorProduct.map_id_comp]
      exact h.comp (RingHom.Flat.lTensor (S := T) L hl)
    by_cases hu : IsUnit (algebraMap T (Localization.AtPrime P) π)
    · have := IsLocalization.flat K (nonZeroDivisors T)
      refine ringHom_flat_of_square
        (α := (Algebra.TensorProduct.includeRight : A →ₐ[T] K ⊗[T] A))
        (β := (Algebra.TensorProduct.includeRight : _ →ₐ[T] K ⊗[T] Localization.AtPrime P))
        (φ' := (Algebra.TensorProduct.map (AlgHom.id T K) (l.comp φ) :
          K ⊗[T] A →+* K ⊗[T] Localization.AtPrime P)) (by ext a; simp [l]) ?_
        (.of_bijective (includeRight_bijective K hπ hu)) ?_
      · have h1 : (algebraMap A (A ⊗[T] K)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
        exact h1.comp (g := (Algebra.TensorProduct.comm T A K : A ⊗[T] K →+* K ⊗[T] A))
          (.of_bijective (Algebra.TensorProduct.comm T A K).bijective)
      · rw [Algebra.TensorProduct.map_id_comp]
        exact hK.comp (RingHom.Flat.lTensor (S := T) K hl)
    · have : IsLocalHom (algebraMap T (Localization.AtPrime P)) := by
        refine ((local_hom_TFAE (algebraMap T (Localization.AtPrime P))).out 1 3).mpr ?_
        rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
          Ideal.span_singleton_le_iff_mem]
        exact hu
      exact flat_of_flat_residueField_baseChange_dvr _ (hbc _ hκ)
  letI := (φ : A →+* B).toAlgebra
  change Module.Flat A B
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun P _ => ?_
  exact RingHom.flat_algebraMap_iff.mp (key P)

end Algebra

def FlatOver {X Y S S' : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S' ⟶ S) : Prop :=
  ∀ ⦃W Z : Scheme.{0}⦄ (a : W ⟶ X) (b : W ⟶ Z) (j : Z ⟶ Y) (h : Z ⟶ S'),
    IsPullback a b f j → j ≫ g = h ≫ s → Flat b

variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}

theorem FlatOver.target (H : FlatOver f g s) {X' Y' : Scheme.{0}} {a' : X' ⟶ X} {f' : X' ⟶ Y'}
    {u : Y' ⟶ Y} (sq : IsPullback a' f' f u) : FlatOver f' (u ≫ g) s :=
  fun _ _ a b j h sq' e => H (a ≫ a') b (j ≫ u) h (sq'.paste_horiz sq) (by simpa using e)

theorem FlatOver.source (H : FlatOver f g s) {X' : Scheme.{0}} (i : X' ⟶ X) [Flat i] :
    FlatOver (i ≫ f) g s := by
  intro W Z a b j h sq e
  have h1 := H _ _ j h (IsPullback.of_hasPullback f j) e
  let c : W ⟶ pullback f j := pullback.lift (a ≫ i) b (by simpa using sq.w)
  have hc : c ≫ pullback.snd f j = b := pullback.lift_snd _ _ _
  have sq2 : IsPullback a c i (pullback.fst f j) :=
    IsPullback.of_bot (by rw [hc]; exact sq) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback f j)
  have h2 : Flat c := MorphismProperty.of_isPullback sq2 ‹Flat i›
  rw [← hc]
  infer_instance

theorem flatOver_of_pullback {X Y : Over S} (φ : X ⟶ Y) (s : S' ⟶ S)
    (H : Flat ((Over.pullback s).map φ).left) : FlatOver φ.left Y.hom s := by
  intro W Z a b j h sq e
  have sq0 : IsPullback (pullback.fst X.hom s) ((Over.pullback s).map φ).left φ.left
      (pullback.fst Y.hom s) := by
    have e1 : ((Over.pullback s).map φ).left ≫ pullback.fst Y.hom s =
        pullback.fst X.hom s ≫ φ.left := pullback.lift_fst _ _ _
    have e2 : ((Over.pullback s).map φ).left ≫ pullback.snd Y.hom s =
        pullback.snd X.hom s := pullback.lift_snd _ _ _
    refine IsPullback.of_bot ?_ e1.symm (IsPullback.of_hasPullback Y.hom s)
    rw [e2, Over.w]
    exact IsPullback.of_hasPullback X.hom s
  let j' : Z ⟶ pullback Y.hom s := pullback.lift j h e
  have hj : j' ≫ pullback.fst Y.hom s = j := pullback.lift_fst _ _ _
  let a' := sq0.lift a (b ≫ j') (by rw [Category.assoc, hj]; exact sq.w)
  have sq1 : IsPullback a' b ((Over.pullback s).map φ).left j' :=
    IsPullback.of_right (by rw [hj, sq0.lift_fst]; exact sq) (sq0.lift_snd _ _ _) sq0
  exact MorphismProperty.of_isPullback sq1 H

theorem FlatOver.tensor {T L A B : Type} [CommRing T] [CommRing L] [CommRing A] [CommRing B]
    [Algebra T L] [Algebra T A] [Algebra T B] (φ : A →ₐ[T] B)
    (H : FlatOver (spMap (φ : A →+* B)) (spMap (algebraMap T A)) (spMap (algebraMap T L))) :
    (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B).Flat := by
  have hA := CommRingCat.isPushout_tensorProduct T L A
  have hB := CommRingCat.isPushout_tensorProduct T L B
  have sq : IsPushout (CommRingCat.ofHom (φ : A →+* B))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[T] L ⊗[T] A).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[T] L ⊗[T] B).toRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id T L) φ : L ⊗[T] A →+* L ⊗[T] B)) := by
    refine IsPushout.of_left ?_ ?_ hA.flip
    · convert hB.flip using 1
      · ext t; simp
      · ext t; simp
    · ext t; simp
  have := H _ _ _ (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[T] A)))
    (isPullback_SpecMap_of_isPushout _ _ _ _ sq)
    (isPullback_SpecMap_of_isPushout _ _ _ _ hA).w.symm
  exact Flat.SpecMap_iff.mp this

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp T)
    (h1 : Flat (f ≫ g)) (h2 : LocallyOfFiniteType (f ≫ g)) (h3 : LocallyOfFiniteType g)
    (hK : FlatOver f g (spMap (algebraMap T K))) (hκ : FlatOver f g (spMap (residue T))) :
    Flat f := by
  wlog hY : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) (Y.affineCover.f i ≫ g)
      (by rw [e]; infer_instance) (by rw [e]; infer_instance) inferInstance
      (hK.target sq) (hκ.target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance) (hK.source _) (hκ.source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h2
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h2 h3
  letI : Algebra T A := g.hom.toAlgebra
  letI : Algebra T B := (g ≫ f).hom.toAlgebra
  haveI : Module.Flat T B := h1
  haveI : Algebra.FiniteType T B := h2
  haveI : Algebra.FiniteType T A := h3
  haveI := Algebra.FiniteType.isNoetherianRing T A
  haveI := Algebra.FiniteType.isNoetherianRing T B
  let φ : A →ₐ[T] B := { f.hom with commutes' := fun _ => rfl }
  exact ringHom_flat K φ (FlatOver.tensor φ hK) (FlatOver.tensor φ hκ)

end FibreFlat

theorem flat_of_flat_fibres_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (X Y : Over (Sp T)) (φ : X ⟶ Y), Flat X.hom → Flat Y.hom →
      LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom →
      Flat ((Over.pullback (spMap (algebraMap T K))).map φ).left →
      Flat ((Over.pullback (spMap (IsLocalRing.residue T))).map φ).left → Flat φ.left := by
  intro T K _ _ _ _ _ _ X Y φ h1 _ h2 h3 hK hκ
  exact FibreFlat.flat_of_flatOver T K φ.left Y.hom (by rwa [Over.w]) (by rwa [Over.w]) h3
    (FibreFlat.flatOver_of_pullback φ _ hK) (FibreFlat.flatOver_of_pullback φ _ hκ)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem exists_grpObj_of_mono {H G : C} [GrpObj G] (j : H ⟶ G) [Mono j]
    (o : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H) (ho : o ≫ j = η[G])
    (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[G]) (hn : n ≫ j = j ≫ GrpObj.inv) :
    ∃ _ : GrpObj H, IsMonHom j := by
  letI M : MonObj H :=
    { one := o
      mul := m
      one_mul := by
        rw [← cancel_mono j, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono j, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono j]
        simp only [Category.assoc, hm]
        rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc, hm, Category.id_comp]
        have h1 : ((j ⊗ₘ j) ≫ μ[G] ⊗ₘ j) = ((j ⊗ₘ j) ⊗ₘ j) ≫ μ[G] ▷ G := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
        have h2 : (j ⊗ₘ (j ⊗ₘ j) ≫ μ[G]) = (j ⊗ₘ (j ⊗ₘ j)) ≫ G ◁ μ[G] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
        rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc] }
  refine ⟨{ inv := n, left_inv := ?_, right_inv := ?_ }, ⟨ho, hm⟩⟩
  · rw [← cancel_mono j]
    change (lift n (𝟙 H) ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.left_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this
  · rw [← cancel_mono j]
    change (lift (𝟙 H) n ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.right_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this

theorem isMonHom_of_comp_mono {A B D : C} [MonObj A] [MonObj B] [MonObj D] (e : A ⟶ B) (i : B ⟶ D)
    [Mono i] [IsMonHom i] [h : IsMonHom (e ≫ i)] : IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, h.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, h.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

theorem isCommMonObj_of_mono [BraidedCategory C] {H G : C} [MonObj H] [MonObj G] (j : H ⟶ G)
    [Mono j] [IsMonHom j] [IsCommMonObj G] : IsCommMonObj H := by
  constructor
  rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

end

theorem exists_grpObj_of_flat_closed {S S' : Scheme.{0}} (f : S' ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (P Ga : Over S) [GrpObj P] (io : Ga ⟶ P)
    (Z : Over S') [GrpObj Z] (i : Z ⟶ (Over.pullback f).obj P) (e : (Over.pullback f).obj Ga ≅ Z)
    [IsClosedImmersion io.left] [Flat Ga.hom] [hi : IsMonHom i]
    (h : e.hom ≫ i = (Over.pullback f).map io) :
    ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  have h1 : Flat (𝟙_ (Over S)).hom := inferInstanceAs (Flat (𝟙 S))
  have h2 : Flat (Ga ⊗ Ga).hom := inferInstanceAs (Flat (pullback.fst Ga.hom Ga.hom ≫ Ga.hom))
  have hm : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hm' : Mono ((Over.pullback f).map io) := inferInstance
  have h' : e.inv ≫ (Over.pullback f).map io = i := by rw [← h, e.inv_hom_id_assoc]
  have hmi : Mono i := by rw [← h']; infer_instance
  obtain ⟨o, ⟨ho, -⟩, -⟩ := existsUnique_lift_of_flat f io η[P]
    (Functor.OplaxMonoidal.η (Over.pullback f) ≫ η[Z] ≫ e.inv) (by
      rw [Category.assoc, Category.assoc, h', hi.one_hom, Functor.obj.η_def,
        Functor.Monoidal.η_ε_assoc])
  obtain ⟨m, ⟨hm, -⟩, -⟩ := existsUnique_lift_of_flat f io ((io ⊗ₘ io) ≫ μ[P])
    (Functor.OplaxMonoidal.δ (Over.pullback f) Ga Ga ≫ (e.hom ⊗ₘ e.hom) ≫ μ[Z] ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', hi.mul_hom, tensorHom_comp_tensorHom_assoc, h, Functor.obj.μ_def,
        Functor.LaxMonoidal.μ_natural_assoc, Functor.Monoidal.δ_μ_assoc, Functor.map_comp])
  obtain ⟨n, ⟨hn, -⟩, -⟩ := existsUnique_lift_of_flat f io (io ≫ GrpObj.inv)
    (e.hom ≫ GrpObj.inv ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', GrpObj.inv_hom, ← Category.assoc, h, Functor.obj.ι_def, Functor.map_comp])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono io o m n ho hm hn
  refine ⟨G, hG, ?_, fun _ => isCommMonObj_of_mono io⟩
  have : IsMonHom (e.hom ≫ i) := by rw [h]; infer_instance
  exact isMonHom_of_comp_mono e.hom i

theorem flat_closure_subgroup :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (P Ga : Over (Sp T)) [GrpObj P] (io : Ga ⟶ P) (Z : Over (Sp K)) [GrpObj Z] (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj P) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left → Flat Ga.hom → IsMonHom i → e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io → ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  intro T K _ _ _ _ _ _ P Ga _ io Z _ i e _ _ _ h
  have := schemeTheoreticallyDominant_fractionField T K
  exact exists_grpObj_of_flat_closed _ P Ga io Z i e h

end GlobalTheory
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.AdLat

variable {F : Type} [Field F] [NumberField F]

theorem valued_natCast_eq (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) = v.intValuation (N : 𝓞 F) := by
  have h : (N : v.adicCompletion F)
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (N : 𝓞 F)) := by simp
  rw [h, ← v.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) ≤ 1 := by
  rw [valued_natCast_eq]; exact v.intValuation_le_one _

theorem valued_natCast_ne_zero (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    Valued.v (N : v.adicCompletion F) ≠ 0 := by
  rw [valued_natCast_eq]
  exact v.intValuation_ne_zero _ (by exact_mod_cast hN.ne')

theorem exists_nat_valued_pow_le (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, Valued.v ((p ^ n : ℕ) : v.adicCompletion F) ≤ exp (-(n : ℤ)) := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, fun n => ?_⟩
  · exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · rw [valued_natCast_eq, HeightOneSpectrum.intValuation_le_pow_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) n

theorem eq_zero_of_valued_le_natCast (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F)
    (h : ∀ N : ℕ, 0 < N → Valued.v y ≤ Valued.v (N : v.adicCompletion F)) : y = 0 := by
  by_contra hy
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (γ := Valued.v y) (by simpa using hy)
  exact absurd ((h _ (pow_pos hp n)).trans (hpn n)) (not_le.2 hn)

theorem exists_limit_of_compatible (v : HeightOneSpectrum (𝓞 F)) (x : ℕ → v.adicCompletion F)
    (h : ∀ N m : ℕ, 0 < N → 0 < m →
      Valued.v (x (N * m) - x N) ≤ Valued.v (N : v.adicCompletion F)) :
    ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
      Valued.v (t - x N) ≤ Valued.v (N : v.adicCompletion F) := by
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit (K := F) v (fun n => x (p ^ n)) (fun m n hnm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add]
    exact (h _ _ (pow_pos hp n) (pow_pos hp k)).trans (hpn n))
  refine ⟨t, fun N hN => ?_⟩
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (valued_natCast_ne_zero v hN)
  have h1 := (ht n).trans hn.le
  have h2 := ((h _ _ (pow_pos hp n) hN).trans (hpn n)).trans hn.le
  have h3 := h _ _ hN (pow_pos hp n)
  have e : t - x N = (t - x (p ^ n)) - (x (p ^ n * N) - x (p ^ n)) + (x (N * p ^ n) - x N) := by
    rw [mul_comm N]; ring
  rw [e]
  exact Valuation.map_add_le _ (Valuation.map_sub_le _ h1 h2) h3

theorem valued_nsmul_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : a v ∈ v.adicCompletionIntegers F) :
    Valued.v ((N • a) v) ≤ Valued.v (N : v.adicCompletion F) := by
  have : (N • a) v = N • a v := rfl
  rw [this, nsmul_eq_mul, map_mul]
  exact mul_le_of_le_one_right' ha

theorem integral_finiteAdele_complete_separated :
    ∀ (F : Type) [Field F] [NumberField F], (∀ y : FiniteAdeleRing (𝓞 F) F, (∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = N • a) → y = 0) ∧ ∀ x : ℕ → FiniteAdeleRing (𝓞 F) F, (∀ N v, x N v ∈ v.adicCompletionIntegers F) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x (N * m) = x N + N • a) → ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = x N + N • a := by
  intro F _ _
  refine ⟨fun y hy => ?_, fun x hx h => ?_⟩
  · refine DFunLike.ext _ _ fun v => ?_
    refine eq_zero_of_valued_le_natCast v (y v) fun N hN => ?_
    obtain ⟨a, ha, rfl⟩ := hy N hN
    exact valued_nsmul_le v N a (ha v)
  · have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
        Valued.v (t - x N v) ≤ Valued.v (N : v.adicCompletion F) := fun v => by
      refine exists_limit_of_compatible v (fun N => x N v) fun N m hN hm => ?_
      obtain ⟨a, ha, e⟩ := h N m hN hm
      have : x (N * m) v - x N v = (N • a) v := by
        rw [e]
        exact add_sub_cancel_left (x N v) ((N • a) v)
      rw [this]
      exact valued_nsmul_le v N a (ha v)
    choose t ht using key
    have ht1 : ∀ v, t v ∈ v.adicCompletionIntegers F := fun v => by
      have h1 : Valued.v (t v - x 1 v) ≤ 1 := (ht v 1 one_pos).trans (valued_natCast_le_one v 1)
      have h2 : t v - x 1 v ∈ v.adicCompletionIntegers F := h1
      simpa using add_mem h2 (hx 1 v)
    refine ⟨⟨t, Filter.Eventually.of_forall ht1⟩, fun N hN => ?_⟩
    have hq : ∀ v, (t v - x N v) / (N : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
      fun v => by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ (ht v N hN) zero_le'
    refine ⟨⟨fun v => (t v - x N v) / (N : v.adicCompletion F),
      Filter.Eventually.of_forall hq⟩, hq, ?_⟩
    refine DFunLike.ext _ _ fun v => ?_
    change t v = x N v + N • ((t v - x N v) / (N : v.adicCompletion F))
    have hN0 : (N : v.adicCompletion F) ≠ 0 := fun h0 =>
      valued_natCast_ne_zero v hN (by rw [h0, map_zero])
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hN0]
    ring

end GlobalTheory.AdLat
end
end
