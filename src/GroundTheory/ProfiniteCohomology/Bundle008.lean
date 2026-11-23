module

public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.Bundle002
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Topology.Algebra.OpenSubgroup
public import GroundTheory.ProfiniteCohomology.Bundle005
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import GroundTheory.ProfiniteCohomology.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section ResLE


omit [IsTopologicalGroup G] in
theorem continuous_subgroup_inclusion {U V : Subgroup G} (h : V ≤ U) :
    Continuous (Subgroup.inclusion h) :=
  continuous_induced_rng.2 continuous_subtype_val

variable (A : Rep.{u} k G)

def resResHom {U V : Subgroup G} (h : V ≤ U) :
    Rep.res (Subgroup.inclusion h) (Rep.res U.subtype A) ⟶ Rep.res V.subtype A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩


variable [IsDiscreteRep A]

noncomputable def cohomologyResLE {U V : Subgroup G} (h : V ≤ U) (n : ℕ) :
    cohomology (Rep.res U.subtype A) n ⟶ cohomology (Rep.res V.subtype A) n :=
  cohomologyMapAlong (Subgroup.inclusion h) (continuous_subgroup_inclusion h) (resResHom A h) n

theorem cohomologyResLE_eq {U V : Subgroup G} (h : V ≤ U) (n : ℕ) :
    cohomologyResLE A h n = cohomologyMapAlong (Subgroup.inclusion h)
      (continuous_subgroup_inclusion h) (resResHom A h) n :=
  rfl

instance isDiscreteRep_res_quotientToInvariants (W : Subgroup G) (N : Subgroup W) [N.Normal] :
    IsDiscreteRep ((Rep.res W.subtype A).quotientToInvariants N) :=
  isDiscreteRep_quotientToInvariants_of_normal _ _

end ResLE

noncomputable abbrev H2Open (C : Rep.{u} k G) [IsDiscreteRep C] (U : OpenSubgroup G) : Type u :=
  cohomology (Rep.res (U : Subgroup G).subtype C) 2

structure PreClassFormation (C : Rep.{u} k G) [IsDiscreteRep C] where

  inv : ∀ U : OpenSubgroup G, H2Open C U →+ QZ

  isZero_H1_open_subgroups : ∀ U : OpenSubgroup G,
    Limits.IsZero (cohomology (Rep.res (U : Subgroup G).subtype C) 1)

  inv_res : ∀ (U V : OpenSubgroup G) (h : V ≤ U) (x : H2Open C U),
    inv V ((cohomologyResLE C (show (V : Subgroup G) ≤ U from h) 2).hom x) =
      (V : Subgroup G).relIndex U • inv U x

structure ClassFormation (C : Rep.{u} k G) [IsDiscreteRep C] extends PreClassFormation C where

  inv_bijective : ∀ U : OpenSubgroup G, Function.Bijective (inv U)

structure ClassFormationAt (P : Set Nat.Primes) (C : Rep.{u} k G) [IsDiscreteRep C]
    extends PreClassFormation C where

  inv_injective : ∀ U : OpenSubgroup G, Function.Injective (inv U)

  primaryComponent_le_range : ∀ (U : OpenSubgroup G), ∀ p ∈ P,
    ∀ x ∈ AddCommMonoid.primaryComponent QZ (p : ℕ), x ∈ (inv U).range

namespace PreClassFormation

variable {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)

noncomputable abbrev H2Quotient (C : Rep.{u} k G) [IsDiscreteRep C] (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] : Type u :=
  cohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
    ((V : Subgroup G).subgroupOf U)) 2

noncomputable def fundamentalClass (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] : H2Quotient C U V :=
  haveI : Nonempty (H2Quotient C U V) := ⟨0⟩
  Function.invFun
    (fun x : H2Quotient C U V =>
      F.inv U ((cohomologyInfl (Rep.res (U : Subgroup G).subtype C)
        ((V : Subgroup G).subgroupOf U) 2).hom x))
    (QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ)))

end PreClassFormation

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Topology

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Maps

variable (U : Subgroup G)

noncomputable def coindEvalOne (B : Rep.{u} k U) :
    Rep.res U.subtype (Rep.coind U.subtype B) ⟶ B :=
  Rep.ofHom ⟨(LinearMap.proj (1 : G)).comp (Representation.coindV U.subtype B.ρ).subtype,
    fun u => by
      ext f
      change f.1 (1 * (u : G)) = B.ρ u (f.1 1)
      rw [one_mul]
      simpa using f.2 u 1⟩

noncomputable def coindUnit (A : Rep.{u} k G) :
    A ⟶ Rep.coind U.subtype (Rep.res U.subtype A) :=
  Rep.resCoindToHom U.subtype A (Rep.res U.subtype A) (𝟙 _)

@[simp]
theorem coindUnit_hom_apply (A : Rep.{u} k G) (a : A) (x : G) :
    ((coindUnit U A).hom a).1 x = A.ρ x a :=
  rfl

theorem coindUnit_comp_coindEvalOne (A : Rep.{u} k G) :
    (Rep.resFunctor U.subtype).map (coindUnit U A) ≫ coindEvalOne U (Rep.res U.subtype A) =
      𝟙 _ := by
  ext a
  change A.ρ 1 a = a
  simp

section Trace

variable (A : Rep.{u} k G)

noncomputable def coindTraceTerm (c : G ⧸ U) :
    Rep.coind U.subtype (Rep.res U.subtype A) →ₗ[k] A :=
  A.ρ c.out ∘ₗ (LinearMap.proj c.out⁻¹).comp
    (Representation.coindV U.subtype (Rep.res U.subtype A).ρ).subtype

theorem coindTraceTerm_apply (f : Rep.coind U.subtype (Rep.res U.subtype A)) (x : G) :
    coindTraceTerm U A (x : G ⧸ U) f = A.ρ x (f.1 x⁻¹) := by
  change A.ρ (x : G ⧸ U).out (f.1 (x : G ⧸ U).out⁻¹) = A.ρ x (f.1 x⁻¹)
  obtain ⟨u, hu⟩ : ∃ u : U, (x : G ⧸ U).out = x * u := by
    have h := QuotientGroup.mk_out_eq_mul U x
    obtain ⟨u, hu⟩ := h
    exact ⟨u, hu⟩
  rw [hu]
  have h1 : (x * (u : G))⁻¹ = U.subtype u⁻¹ * x⁻¹ := by simp
  rw [h1, f.2 u⁻¹ x⁻¹]
  change A.ρ (x * u) (A.ρ (u⁻¹ : U) (f.1 x⁻¹)) = _
  rw [← Module.End.mul_apply, ← map_mul]
  simp

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def coindTrace : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ A :=
  Rep.ofHom ⟨∑ c : G ⧸ U, coindTraceTerm U A c, fun g => by
    ext f
    change (∑ c : G ⧸ U, coindTraceTerm U A c) ((Rep.coind U.subtype (Rep.res U.subtype A)).ρ g f) =
      A.ρ g ((∑ c : G ⧸ U, coindTraceTerm U A c) f)

    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun c => ?_).symm
    induction c using QuotientGroup.induction_on with
    | H x =>
      simp only [MulAction.toPerm_apply, MulAction.Quotient.smul_mk]
      rw [coindTraceTerm_apply, coindTraceTerm_apply]
      change A.ρ g (A.ρ x (f.1 x⁻¹)) = A.ρ (g * x) (f.1 ((g * x)⁻¹ * g))
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_inv_rev, mul_assoc]⟩

theorem coindTrace_hom_apply (f : Rep.coind U.subtype (Rep.res U.subtype A)) :
    (coindTrace U A).hom f = ∑ c : G ⧸ U, coindTraceTerm U A c f := by
  simp [coindTrace]

theorem coindUnit_comp_coindTrace : coindUnit U A ≫ coindTrace U A = U.index • 𝟙 A := by
  ext a
  change (coindTrace U A).hom ((coindUnit U A).hom a) = (U.index • 𝟙 A : A ⟶ A).hom a
  rw [coindTrace_hom_apply]
  have h : ∀ c : G ⧸ U, coindTraceTerm U A c ((coindUnit U A).hom a) = a := fun c => by
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [coindTraceTerm_apply, coindUnit_hom_apply, ← Module.End.mul_apply, ← map_mul]
      simp
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, Rep.nsmul_hom]
  rfl

end Trace

end Maps

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Discrete

variable (U : OpenSubgroup G) (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B]

theorem isLocallyConstant_coind (f : Rep.coind (U : Subgroup G).subtype B) :
    IsLocallyConstant (f.1 : G → B) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  set S : Set G := Subtype.val '' (stabilizer B.ρ (f.1 x) : Set (U : Subgroup G))
  have hS : IsOpen S :=
    IsOpen.isOpenMap_subtype_val (s := (U : Set G)) U.isOpen _ (isOpen_stabilizer B (f.1 x))
  have h1 : S ∈ 𝓝 (1 : G) := hS.mem_nhds ⟨1, (stabilizer B.ρ (f.1 x)).one_mem, rfl⟩
  have hc : Continuous fun y : G => y * x⁻¹ := continuous_id.mul continuous_const
  have h2 : ∀ᶠ y in 𝓝 x, y * x⁻¹ ∈ S := hc.continuousAt.preimage_mem_nhds (by simpa using h1)
  filter_upwards [h2] with y hy
  obtain ⟨u, hu, huy⟩ := hy
  have hy' : y = (U : Subgroup G).subtype u * x := by
    simp only [Subgroup.subtype_apply, huy, inv_mul_cancel_right]
  rw [hy', f.2 u x]
  exact (mem_stabilizer _ _ _).1 hu

noncomputable def coindToLocallyConstant (f : Rep.coind (U : Subgroup G).subtype B) :
    LocallyConstant G B :=
  ⟨f.1, isLocallyConstant_coind U B f⟩

instance isDiscreteRep_coind [CompactSpace G] :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype B) :=
  ⟨fun f => Subgroup.isOpen_of_mem_nhds (g := 1) _ <|
    Filter.mem_of_superset (eventually_forall_mul_eq (coindToLocallyConstant U B f))
      fun g (hg : ∀ x, f.1 (x * g) = f.1 x) => Subtype.ext (funext fun x => hg x)⟩

instance finiteIndex_openSubgroup [CompactSpace G] (U : OpenSubgroup G) :
    (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

instance compactSpace_openSubgroup [CompactSpace G] (U : OpenSubgroup G) :
    CompactSpace (U : Subgroup G) :=
  isCompact_iff_compactSpace.mp (U.isClosed.isCompact)

end Discrete

section Shapiro

variable [CompactSpace G] (U : OpenSubgroup G) (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B]

noncomputable def shapiroMap (n : ℕ) :
    cohomology (Rep.coind (U : Subgroup G).subtype B) n ⟶ cohomology B n :=
  cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
    (coindEvalOne (U : Subgroup G) B) n

theorem shapiroMap_eq (n : ℕ) :
    shapiroMap U B n = cohomologyMapAlong (U : Subgroup G).subtype
      (continuous_subgroup_subtype _) (coindEvalOne (U : Subgroup G) B) n :=
  rfl

end Shapiro

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Union

variable (A : Rep.{u} k G) {ι : Type u} [Preorder ι] (W : ι → Submodule k A) (hW : Monotone W)
  (hstable : ∀ i g, W i ≤ (W i).comap (A.ρ g))

noncomputable def subrepInclusion {i j : ι} (h : i ≤ j) :
    A.subrepresentation (W i) (hstable i) ⟶ A.subrepresentation (W j) (hstable j) :=
  Rep.ofHom ⟨Submodule.inclusion (hW h), fun _ => LinearMap.ext fun _ => rfl⟩

theorem subrepInclusion_refl {i : ι} (h : i ≤ i) : subrepInclusion A W hW hstable h = 𝟙 _ := by
  ext
  rfl

theorem subrepInclusion_trans {i j l : ι} (h₁ : i ≤ j) (h₂ : j ≤ l) :
    subrepInclusion A W hW hstable (h₁.trans h₂) =
      subrepInclusion A W hW hstable h₁ ≫ subrepInclusion A W hW hstable h₂ := by
  ext
  rfl

theorem subrepInclusion_comp_subtype {i j : ι} (h : i ≤ j) :
    subrepInclusion A W hW hstable h ≫ Rep.subtype A (W j) (hstable j) =
      Rep.subtype A (W i) (hstable i) := by
  ext
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A]

noncomputable def subrepCochains : ι ⥤ CochainComplex (ModuleCat k) ℕ where
  obj i := cochainsComplex (A.subrepresentation (W i) (hstable i))
  map h := cochainsMap (subrepInclusion A W hW hstable (leOfHom h))
  map_id i := by rw [subrepInclusion_refl, cochainsMap_id]
  map_comp f g := by rw [← cochainsMap_comp, ← subrepInclusion_trans]

noncomputable def subrepCochainsCocone : Cocone (subrepCochains A W hW hstable) where
  pt := cochainsComplex A
  ι :=
    { app i := cochainsMap (Rep.subtype A (W i) (hstable i))
      naturality i j h := by
        refine (cochainsMap_comp _ _).symm.trans ?_
        rw [subrepInclusion_comp_subtype]
        exact (Category.comp_id _).symm }

theorem subrepCochainsCocone_inj (n : ℕ) (i : ι)
    (y : ((subrepCochains A W hW hstable).obj i).X n)
    (hy : (((subrepCochainsCocone A W hW hstable).ι.app i).f n).hom y = 0) :
    ∃ (j : ι) (f : i ⟶ j), (((subrepCochains A W hW hstable).map f).f n).hom y = 0 := by
  refine ⟨i, 𝟙 i, ?_⟩
  have : Mono (Rep.subtype A (W i) (hstable i)) :=
    (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  have hinj : Function.Injective ((cochainsMap (Rep.subtype A (W i) (hstable i))).f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact hinj (hy.trans (map_zero _).symm)

variable [CompactSpace G]


omit [IsTopologicalGroup G] [IsDiscreteRep A] in
include hW in
theorem exists_forall_mem_of_isLocallyConstant [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) {n : ℕ} {f : (Fin n → G) → A} (hf : IsLocallyConstant f) :
    ∃ j, ∀ g, f g ∈ W j := by
  classical
  choose idx hidx using hunion
  obtain ⟨j, hj⟩ := Finset.exists_le (hf.range_finite.toFinset.image idx)
  exact ⟨j, fun g => hW (hj _ (Finset.mem_image_of_mem _ (by simp))) (hidx (f g))⟩

theorem subrepCochainsCocone_surj [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : (subrepCochainsCocone A W hW hstable).pt.X n) :
    ∃ (j : ι) (y : ((subrepCochains A W hW hstable).obj j).X n),
      (((subrepCochainsCocone A W hW hstable).ι.app j).f n).hom y = x := by
  have hx : IsLocallyConstant (((cochainsComplexι A).f n).hom x : (Fin n → G) → A) :=
    (show locallyConstantCochains A n from x).2
  obtain ⟨j, hj⟩ := exists_forall_mem_of_isLocallyConstant A W hW hunion hx
  have hy : IsLocallyConstant fun g : Fin n → G =>
      (⟨((cochainsComplexι A).f n).hom x g, hj g⟩ : W j) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro b
    have : (fun g : Fin n → G => (⟨((cochainsComplexι A).f n).hom x g, hj g⟩ : W j)) ⁻¹' {b} =
        (((cochainsComplexι A).f n).hom x : (Fin n → G) → A) ⁻¹' {(b : A)} := by
      ext g
      simp [Subtype.ext_iff]
    rw [this]
    exact hx.isOpen_fiber _
  refine ⟨j, ⟨_, hy⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι A).f n)).1 inferInstance
  rfl


include hW in
theorem exists_cohomologyMap_subtype_eq [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : cohomology A n) :
    ∃ (i : ι) (y : cohomology (A.subrepresentation (W i) (hstable i)) n),
      (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = x :=
  exists_homologyMap_eq_of_cocone (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion n)
    (subrepCochainsCocone_inj A W hW hstable _) x

theorem exists_cohomologyMap_subrepInclusion_eq_zero [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (i : ι)
    (y : cohomology (A.subrepresentation (W i) (hstable i)) n)
    (hy : (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = 0) :
    ∃ (j : ι) (h : i ≤ j), (cohomologyMap (subrepInclusion A W hW hstable h) n).hom y = 0 := by
  obtain ⟨j, f, hf⟩ := exists_homologyMap_map_eq_zero_of_cocone
    (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion _)
    (subrepCochainsCocone_inj A W hW hstable n) i y hy
  exact ⟨j, leOfHom f, hf⟩

end Union

end GroundTheory.ProfCoh
end
