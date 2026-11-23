module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

section

universe u v w x

variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]

namespace Derivation

private theorem isUnit_algebraMap_moduleEnd (M : Submonoid S) [IsLocalization M S'] (y : M) :
    IsUnit ((algebraMap S (Module.End S N)) (y : S)) := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units (M := M) S' y
  have hcomm : ∀ (s : S) (c : S') (n : N), c • s • n = s • c • n := by
    intro s c n
    rw [← IsScalarTower.algebraMap_smul S' s n, ← IsScalarTower.algebraMap_smul S' s (c • n),
      smul_smul, smul_smul, mul_comm]
  have h1 : ∀ n : N, (y : S) • (((u⁻¹ : S'ˣ) : S') • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) (((u⁻¹ : S'ˣ) : S') • n), ← hu, smul_smul,
      u.mul_inv, one_smul]
  have h2 : ∀ n : N, ((u⁻¹ : S'ˣ) : S') • ((y : S) • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) n, ← hu, smul_smul, u.inv_mul, one_smul]
  exact ⟨⟨(algebraMap S (Module.End S N)) (y : S),
    { toFun := fun n => ((u⁻¹ : S'ˣ) : S') • n
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s n => hcomm s ((u⁻¹ : S'ˣ) : S') n },
    LinearMap.ext fun n => h1 n, LinearMap.ext fun n => h2 n⟩, rfl⟩

private theorem exists_liftToLocalization (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' N, ∀ s : S, D' (algebraMap S S' s) = D s := by
  have hu : ∀ y : M, IsUnit ((algebraMap S (Module.End S N)) (y : S)) := fun y =>
    isUnit_algebraMap_moduleEnd (S' := S') M y
  have : IsLocalizedModule M (KaehlerDifferential.map R R S S') := inferInstance
  refine ⟨(LinearMap.extendScalarsOfIsLocalization M S'
      (IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu)).compDer (KaehlerDifferential.D R S'), fun s => ?_⟩
  show IsLocalizedModule.lift M (KaehlerDifferential.map R R S S') D.liftKaehlerDifferential hu
      (KaehlerDifferential.D R S' (algebraMap S S' s)) = D s
  have key : IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu
        (KaehlerDifferential.map R R S S' (KaehlerDifferential.D R S s))
      = D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun
      (IsLocalizedModule.lift_comp M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu) (KaehlerDifferential.D R S s)
  rw [← KaehlerDifferential.map_D R R S S' s, key]
  exact D.liftKaehlerDifferential_comp_D s

theorem exists_mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' S', ∀ s : S,
      D' (algebraMap S S' s) = algebraMap S S' (D s) := by
  obtain ⟨D', hD'⟩ :=
    exists_liftToLocalization (S' := S') (N := S') ((Algebra.linearMap S S').compDer D) M
  exact ⟨D', fun s => hD' s⟩

noncomputable def mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] : Derivation R S' S' :=
  (exists_mapToLocalization (S' := S') D M).choose

@[simp]
theorem mapToLocalization_algebraMap (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] (s : S) :
    (D.mapToLocalization (S' := S') M) (algebraMap S S' s) = algebraMap S S' (D s) :=
  (exists_mapToLocalization (S' := S') D M).choose_spec s

theorem exists_derivation_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D s = algebraMap S S' (D₀ s) := by
  obtain ⟨ψ, m, hψ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    M (Algebra.linearMap S S') D.liftKaehlerDifferential
  refine ⟨m, LinearMap.compDer ψ (KaehlerDifferential.D R S), fun s => ?_⟩
  have h1 : algebraMap S S' (ψ (KaehlerDifferential.D R S s))
      = (m : S) • D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun hψ (KaehlerDifferential.D R S s)
  rw [Derivation.liftKaehlerDifferential_comp_D, Algebra.smul_def] at h1
  exact h1.symm

theorem exists_derivation_mul_eq_of_isLocalization (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S' S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₀ s) := by
  obtain ⟨m, D₀, h⟩ := exists_derivation_mul_eq (S' := S') M (D.compAlgebraMap S)
  exact ⟨m, D₀, fun s => h s⟩

end Derivation
end

section

universe u

open AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem jacobsonSpace_affineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  JacobsonSpace.of_isClosedEmbedding
    (Scheme.homeoOfIso (AffineSpace.SpecIso n (CommRingCat.of k))).isClosedEmbedding

instance instJacobsonSpaceAffineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  jacobsonSpace_affineSpace k n

end FunctorialResolution.EmbeddedResolution
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FunctorialResolution.EmbeddedResolution

private theorem isIso_sigmaDesc_of_isPullback {ι : Type u} [Finite ι] {P : Scheme.{u}}
    (B C : ι → Scheme.{u}) (f : P ⟶ ∐ B) (j : ∀ a, C a ⟶ B a) (u : ∀ a, C a ⟶ P)
    (hsq : ∀ a, IsPullback (u a) (j a) f (Sigma.ι B a)) : IsIso (Sigma.desc u) := by
  have e1 : (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as) ≫ (colimit.cocone (Discrete.functor B)).ι
      = (Cofan.mk P u).ι ≫ (Functor.const (Discrete ι)).map f := by
    apply NatTrans.ext
    funext x
    obtain ⟨a⟩ := x
    exact ((hsq a).w).symm
  have hpb : ∀ x : Discrete ι, IsPullback ((Cofan.mk P u).ι.app x)
      ((Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as).app x) f ((colimit.cocone (Discrete.functor B)).ι.app x) := by
    rintro ⟨a⟩
    exact hsq a
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (colimit.isColimit (Discrete.functor B)) (Cofan.mk P u)
      (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B) fun a => j a.as)
      f e1 (NatTrans.Equifibered.of_discrete _) hpb
  have key : Sigma.desc u
      = (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor C)) hc').hom := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (Discrete.functor C)) hc' ⟨a⟩).symm
  rw [key]
  infer_instance

theorem isPullback_sigmaMap_sigmaDesc {ι : Type u} [Finite ι] {A Y : Scheme.{u}} (i : Y ⟶ A)
    (B C : ι → Scheme.{u}) (j : ∀ a, C a ⟶ B a) (q : ∀ a, C a ⟶ Y) (h : ∀ a, B a ⟶ A)
    (hsq : ∀ a, IsPullback (j a) (q a) (h a) i) :
    IsPullback (Limits.Sigma.map j) (Limits.Sigma.desc q) (Limits.Sigma.desc h) i := by
  have hcomm : ∀ a, (j a ≫ Sigma.ι B a) ≫ Sigma.desc h = q a ≫ i := by
    intro a
    rw [Category.assoc, Sigma.ι_desc]
    exact (hsq a).w
  obtain ⟨u, hufst, husnd⟩ : ∃ u : ∀ a, C a ⟶ pullback (Sigma.desc h) i,
      (∀ a, u a ≫ pullback.fst (Sigma.desc h) i = j a ≫ Sigma.ι B a) ∧
        (∀ a, u a ≫ pullback.snd (Sigma.desc h) i = q a) :=
    ⟨fun a => pullback.lift (j a ≫ Sigma.ι B a) (q a) (hcomm a),
      fun a => pullback.lift_fst _ _ _, fun a => pullback.lift_snd _ _ _⟩
  have hP : IsPullback (pullback.fst (Sigma.desc h) i) (pullback.snd (Sigma.desc h) i)
      (Sigma.desc h) i := IsPullback.of_hasPullback _ _
  have hsq2 : ∀ a, IsPullback (j a) (u a) (Sigma.ι B a) (pullback.fst (Sigma.desc h) i) := by
    intro a
    refine IsPullback.of_bot ?_ (hufst a).symm hP
    rw [husnd a, Sigma.ι_desc]
    exact hsq a
  have : IsIso (Sigma.desc u) :=
    isIso_sigmaDesc_of_isPullback B C (pullback.fst (Sigma.desc h) i) j u
      (fun a => (hsq2 a).flip)
  have hcs : CommSq (Limits.Sigma.map j) (Sigma.desc q) (Sigma.desc h) i := by
    constructor
    apply Sigma.hom_ext
    intro a
    simp [(hsq a).w]
  refine IsPullback.of_iso_pullback hcs (asIso (Sigma.desc u)) ?_ ?_
  · apply Sigma.hom_ext
    intro a
    simp [hufst a]
  · apply Sigma.hom_ext
    intro a
    simp [husnd a]

end FunctorialResolution.EmbeddedResolution
end

section

namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

theorem support_ker_comp_subset_support_ker {T S Y : Scheme}
    (g : T ⟶ S) (f : S ⟶ Y) :
    ((g ≫ f).ker.support : Set Y) ⊆ (f.ker.support : Set Y) := by
  intro x hx
  exact Scheme.IdealSheafData.support_antitone (Scheme.Hom.le_ker_comp g f) hx

end FunctorialResolution.EmbeddedResolution
end

section

namespace IsOpenMap

theorem mem_closure_singleton_of_apply {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hopen : IsOpenMap f) (hinj : Function.Injective f)
    {a b : A} (h : f b ∈ closure ({f a} : Set B)) : b ∈ closure ({a} : Set A) := by
  rw [mem_closure_iff]
  intro O hO hbO
  obtain ⟨y, hymem, hy⟩ := (mem_closure_iff.mp h) (f '' O) (hopen O hO) ⟨b, hbO, rfl⟩
  obtain ⟨z, hzO, hz⟩ := hymem
  rw [Set.mem_singleton_iff] at hy
  have hza : z = a := hinj (hz.trans hy)
  subst hza
  exact ⟨z, hzO, rfl⟩

end IsOpenMap

namespace FunctorialResolution.EmbeddedResolution

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isIrreducible_inter_open {S U : Set X} (hS : IsIrreducible S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsIrreducible (S ∩ U) := by
  refine ⟨hne, ?_⟩
  rintro u v hu hv ⟨a, ⟨haS, haU⟩, hau⟩ ⟨b, ⟨hbS, hbU⟩, hbv⟩
  obtain ⟨c, hcS, hc⟩ := hS.2 (U ∩ u) (U ∩ v) (hU.inter hu) (hU.inter hv)
    ⟨a, haS, haU, hau⟩ ⟨b, hbS, hbU, hbv⟩
  exact ⟨c, ⟨hcS, hc.1.1⟩, hc.1.2, hc.2.2⟩

theorem closure_inter_open_eq {S U : Set X} (hS : IsClosed S) (hirr : IsIrreducible S)
    (hU : IsOpen U) (hne : (S ∩ U).Nonempty) : closure (S ∩ U) = S := by
  apply Set.Subset.antisymm
  · exact hS.closure_subset_iff.mpr Set.inter_subset_left
  · intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨c, hcS, hc⟩ := hirr.2 o U ho hU ⟨x, hx, hxo⟩ hne
    exact ⟨c, hc.1, hcS, hc.2⟩

theorem isIrreducible_preimage_of_isEmbedding {f : Y → X} (hf : Topology.IsEmbedding f)
    {T : Set X} (hT : IsIrreducible T) (hTr : T ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' T) := by
  obtain ⟨t, ht⟩ := hT.1
  obtain ⟨y, rfl⟩ := hTr ht
  refine ⟨⟨y, ht⟩, ?_⟩
  rintro u v hu hv ⟨a, haT, hau⟩ ⟨b, hbT, hbv⟩
  obtain ⟨u', hu', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hv
  obtain ⟨c, hcT, hcu, hcv⟩ := hT.2 u' v' hu' hv' ⟨f a, haT, hau⟩ ⟨f b, hbT, hbv⟩
  obtain ⟨z, rfl⟩ := hTr hcT
  exact ⟨z, hcT, hcu, hcv⟩

theorem isGenericPoint_preimage_of_isInducing {f : Y → X} (hf : Topology.IsInducing f)
    {ξ : X} {T : Set X} (h : IsGenericPoint ξ T) {y : Y} (hy : f y = ξ) :
    IsGenericPoint y (f ⁻¹' T) := by
  have h2 : closure ({y} : Set Y) = f ⁻¹' closure (f '' ({y} : Set Y)) :=
    hf.closure_eq_preimage_closure_image _
  rw [Set.image_singleton, hy, IsGenericPoint.def h] at h2
  exact h2

theorem isGenericPoint_image_of_isClosedEmbedding {f : Y → X}
    (hf : Topology.IsClosedEmbedding f) {y : Y} {T : Set Y} (h : IsGenericPoint y T) :
    IsGenericPoint (f y) (f '' T) := by
  have hyT : y ∈ T := IsGenericPoint.mem h
  show closure ({f y} : Set X) = f '' T
  apply Set.Subset.antisymm
  · have hcl : IsClosed (f '' T) := by
      rw [← IsGenericPoint.def h]
      exact hf.isClosedMap _ isClosed_closure
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, hyT, rfl⟩)
  · have h2 : f '' closure ({y} : Set Y) ⊆ closure (f '' ({y} : Set Y)) :=
      image_closure_subset_closure_image hf.continuous
    rw [Set.image_singleton] at h2
    rw [← IsGenericPoint.def h]
    exact h2

theorem closure_image_genericPoint {f : X → Y} (hcont : Continuous f) {S : Set X} {ξ : X}
    (hξ : IsGenericPoint ξ S) : closure (f '' S) = closure ({f ξ} : Set Y) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ isClosed_closure
    have hsub := image_closure_subset_closure_image (f := f) (s := ({ξ} : Set X)) hcont
    rw [Set.image_singleton] at hsub
    rw [← hξ]
    exact hsub
  · refine closure_mono ?_
    refine Set.singleton_subset_iff.2 ⟨ξ, ?_, rfl⟩
    rw [← hξ]
    exact subset_closure rfl

theorem isOpen_sUnion_of_irreducibleComponents {Z : Type*} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] (C : Set (Set Z))
    (hdisj : ∀ S ∈ C, ∀ W ∈ irreducibleComponents Z, W ∉ C → Disjoint S W) :
    IsOpen (⋃₀ C) := by
  have hcomp : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin : (irreducibleComponents Z \ C).Finite := hcomp.subset Set.sdiff_subset
  have hclosed : IsClosed (⋃₀ (irreducibleComponents Z \ C)) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun i hi => isClosed_of_mem_irreducibleComponents i hi.1
  have heq : ⋃₀ C = (⋃₀ (irreducibleComponents Z \ C))ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨S, hSmem, hxS⟩
      have hx : x ∉ ⋃₀ (irreducibleComponents Z \ C) := by
        rintro ⟨W, ⟨hW, hWC⟩, hxW⟩
        exact Set.disjoint_left.mp (hdisj S hSmem W hW hWC) hxS hxW
      exact hx
    · intro x hx
      rw [Set.mem_compl_iff] at hx
      by_cases hmem : irreducibleComponent x ∈ C
      · exact Set.mem_sUnion_of_mem mem_irreducibleComponent hmem
      · exact absurd (Set.mem_sUnion_of_mem mem_irreducibleComponent
          (Set.mem_sdiff_of_mem (irreducibleComponent_mem_irreducibleComponents x) hmem)) hx
  rw [heq]
  exact hclosed.isOpen_compl

end

section

open AlgebraicGeometry

theorem support_comap_eq {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) :=
  congrArg (fun s : TopologicalSpace.Closeds X => (s : Set X))
    (Scheme.IdealSheafData.support_comap I f)

theorem comap_ι_eq_top_of_disjoint {X : Scheme} (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.ι = ⊤ := by
  have hempty : ((I.comap U.ι).support : Set U) = ∅ := by
    rw [support_comap_eq]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxU : U.ι.base x ∈ (U : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp h hxU hx
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  exact SetLike.ext' hempty

end

end FunctorialResolution.EmbeddedResolution
end

section

open CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

private theorem isReduced_stalk_of_isAffineOpen {Z : AlgebraicGeometry.Scheme} {V : Z.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V)
    (hred : _root_.IsReduced ↥(Z.presheaf.obj (Opposite.op V))) (x : V) :
    _root_.IsReduced ↥(Z.presheaf.stalk x.1) := by
  have := hV.isLocalization_stalk x
  exact isReduced_localizationPreserves (hV.primeIdealOf x).asIdeal.primeCompl
    ↥(Z.presheaf.stalk x.1) hred

private theorem isReduced_presheaf_obj_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] (U : X.affineOpens) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.obj
      (Opposite.op ((TopologicalSpace.Opens.map
        (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U.1))) := by
  have hid : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U
      = RingHom.ker (AlgebraicGeometry.Scheme.Hom.app f U.1).hom := by
    simp
  have hq : _root_.IsReduced (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U) := by
    rw [hid]
    exact isReduced_of_injective (RingHom.kerLift (AlgebraicGeometry.Scheme.Hom.app f U.1).hom)
      (RingHom.kerLift_injective _)
  have hq' : _root_.IsReduced ↥(CommRingCat.of (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U)) := hq
  exact isReduced_of_injective
    ((AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).hom.hom)
    (AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).commRingCatIsoToRingEquiv.injective

private theorem isReduced_stalk_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f]
    (y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base y ∈ U :=
    ⟨(X.affineCover.f (X.affineCover.idx _)).opensRange,
      AlgebraicGeometry.isAffineOpen_opensRange _, X.affineCover.covers _⟩
  have hVaff : AlgebraicGeometry.IsAffineOpen ((TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U) :=
    hU.preimage (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι
  have hyV : y ∈ (TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U := hyU
  have hred := isReduced_presheaf_obj_subscheme_ker f ⟨U, hU⟩
  exact isReduced_stalk_of_isAffineOpen hVaff hred ⟨y, hyV⟩

theorem isReduced_subscheme_ker {W X : AlgebraicGeometry.Scheme}
    (f : W ⟶ X) [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.Hom.ker f).subscheme := by
  have : ∀ y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
      _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) :=
    fun y => isReduced_stalk_subscheme_ker f y
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

end FunctorialResolution.EmbeddedResolution
end
