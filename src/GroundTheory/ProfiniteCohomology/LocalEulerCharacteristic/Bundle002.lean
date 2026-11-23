module

public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
public import GroundTheory.ProfiniteCohomology.CoinducedModules.CohomologyCoindCokernelIsoHom
public import GroundTheory.ProfiniteCohomology.Bundle001
public import GroundTheory.ProfiniteCohomology.InflationRestriction.CohomologyResMemCohomologyConjInvariants
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle001
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
public import GroundTheory.ProfiniteCohomology.Bundle005

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

def innerConjHom (g : Γ) : Γ →* Γ where
  toFun γ := g⁻¹ * γ * g
  map_one' := by group
  map_mul' a b := by group

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
@[simp]
theorem innerConjHom_apply (g γ : Γ) : innerConjHom g γ = g⁻¹ * γ * g :=
  rfl

theorem continuous_innerConjHom (g : Γ) : Continuous (innerConjHom g) :=
  (continuous_const.mul continuous_id).mul continuous_const

noncomputable def innerConjMor (A : Rep.{u} k Γ) (g : Γ) : Rep.res (innerConjHom g) A ⟶ A :=
  Rep.ofHom ⟨A.ρ g, fun γ => by
    ext a
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      innerConjHom_apply]
    change A.ρ g (A.ρ (g⁻¹ * γ * g) a) = A.ρ γ (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩



omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem innerConjMor_naturality {A B : Rep.{u} k Γ} (f : A ⟶ B) (g : Γ) :
    (Rep.resFunctor (innerConjHom g)).map f ≫ innerConjMor B g = innerConjMor A g ≫ f := by
  ext a
  exact (Rep.hom_comm_apply f g a).symm

noncomputable def cohomologyInnerConj (A : Rep.{u} k Γ) [IsDiscreteRep A] (n : ℕ) (g : Γ) :
    cohomology A n ⟶ cohomology A n :=
  cohomologyMapAlong (innerConjHom g) (continuous_innerConjHom g) (innerConjMor A g) n

noncomputable def innerConjShortComplexMor (S : ShortComplex (Rep.{u} k Γ)) (g : Γ) :
    S.map (Rep.resFunctor (innerConjHom g)) ⟶ S where
  τ₁ := innerConjMor S.X₁ g
  τ₂ := innerConjMor S.X₂ g
  τ₃ := innerConjMor S.X₃ g
  comm₁₂ := (innerConjMor_naturality S.f g).symm
  comm₂₃ := (innerConjMor_naturality S.g g).symm

theorem δ_comp_cohomologyInnerConj {S : ShortComplex (Rep.{u} k Γ)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j)
    (g : Γ) :
    δ hS i j hij ≫ cohomologyInnerConj S.X₁ j g = cohomologyInnerConj S.X₃ i g ≫ δ hS i j hij :=
  δ_comp_cohomologyMapAlong (innerConjHom g) (continuous_innerConjHom g)
    (innerConjShortComplexMor S g) hS hS i j hij

theorem cohomologyInnerConj_zero (A : Rep.{u} k Γ) [IsDiscreteRep A] (g : Γ) :
    cohomologyInnerConj A 0 g = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochainsComplex A) 0 x
  change (cohomologyInnerConj A 0 g).hom ((cohomologyπ A 0).hom z) = (cohomologyπ A 0).hom z
  rw [cohomologyInnerConj]
  have h := ConcreteCategory.congr_hom
    (cohomologyπ_cohomologyMapAlong (innerConjHom g) (continuous_innerConjHom g)
      (innerConjMor A g) 0) z
  change (cohomologyMapAlong (innerConjHom g) (continuous_innerConjHom g)
    (innerConjMor A g) 0).hom ((cohomologyπ A 0).hom z) =
    (cohomologyπ A 0).hom ((cocyclesMapAlong (innerConjHom g)
      (continuous_innerConjHom g) (innerConjMor A g) 0).hom z) at h
  rw [h]
  congr 1
  apply iCycles_injective (cochainsComplex A) 0
  rw [iCycles_cyclesMap_apply]
  set c := ((cochainsComplex A).iCycles 0).hom z
  have hd : ((cochainsComplex A).d 0 1).hom c = 0 := iCycles_d_apply _ 0 1 z
  have hfix : A.ρ g (c.1 Fin.elim0) = c.1 Fin.elim0 := by
    have h1 := congrArg (fun c' : locallyConstantCochains A 1 => c'.1 fun _ => g) hd
    have h2 := cochainsComplex_d_zero_apply A c (fun _ => g)
    have h3 := h2.symm.trans h1
    exact sub_eq_zero.1 h3
  apply Subtype.ext
  funext x
  change A.ρ g (c.1 (⇑(innerConjHom g) ∘ x)) = c.1 x
  rw [Subsingleton.elim (⇑(innerConjHom g) ∘ x) Fin.elim0, Subsingleton.elim x Fin.elim0, hfix]

variable [CompactSpace Γ]

theorem cohomologyInnerConj_eq_id (n : ℕ) :
    ∀ (A : Rep.{u} k Γ) [IsDiscreteRep A] (g : Γ), cohomologyInnerConj A n g = 𝟙 _ := by
  induction n with
  | zero => intro A _ g; exact cohomologyInnerConj_zero A g
  | succ n ih =>
    intro A _ g
    have h := δ_comp_cohomologyInnerConj (coindShortComplex_shortExact A) n (n + 1) rfl g
    have h3 : cohomologyInnerConj (coindShortComplex A).X₃ n g = 𝟙 _ := ih _ g
    rw [h3, Category.id_comp] at h
    change coindδ A n ≫ cohomologyInnerConj A (n + 1) g = coindδ A n at h
    rw [← cancel_epi (coindδ A n), h, Category.comp_id]

theorem cohomologyInnerConj_apply (A : Rep.{u} k Γ) [IsDiscreteRep A] (n : ℕ) (g : Γ)
    (x : cohomology A n) : (cohomologyInnerConj A n g).hom x = x := by
  rw [cohomologyInnerConj_eq_id]
  rfl

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Smul

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cochainsMap_smul (c : k) (f : A ⟶ B) : cochainsMap (c • f) = c • cochainsMap f := by
  ext n x : 3
  apply Subtype.ext
  funext y
  rfl


set_option backward.isDefEq.respectTransparency false in
theorem cohomologyMap_smul (c : k) (f : A ⟶ B) (n : ℕ) :
    cohomologyMap (c • f) n = c • cohomologyMap f n := by
  rw [cohomologyMap, cochainsMap_smul]
  dsimp [HomologicalComplex.homologyMap, cohomologyMap]
  rw [← ShortComplex.homologyMap_smul]
  rfl

end Smul

section Morphisms

variable (T : Rep.{u} k G) {M : Rep.{u} k G}


omit [TopologicalSpace G] [IsTopologicalGroup G] in
noncomputable def tensorRightMor (m : M) (hm : ∀ g : G, M.ρ g m = m) : T ⟶ T ⊗ M :=
  Rep.ofHom ⟨(TensorProduct.mk k T M).flip m, fun g => by
    ext t
    simp [Representation.tprod_apply, hm g]⟩



omit [TopologicalSpace G] [IsTopologicalGroup G] in
noncomputable def tensorFormMor (f : M →ₗ[k] k) (hf : ∀ (g : G) (m : M), f (M.ρ g m) = f m) :
    T ⊗ M ⟶ T :=
  Rep.ofHom ⟨(TensorProduct.rid k T).toLinearMap ∘ₗ LinearMap.lTensor T f, fun g => by
    ext t m
    simp [Representation.tprod_apply, hf g]⟩


end Morphisms

section TwistMap

variable (T : Rep.{u} k G) [IsDiscreteRep T] {M : Rep.{u} k G} [IsDiscreteRep M]
  (hM : ∀ (g : G) (m : M), M.ρ g m = m)

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
theorem tensorRightMor_add (m m' : M) :
    tensorRightMor T (m + m') (fun g => hM g _) =
      tensorRightMor T m (fun g => hM g m) + tensorRightMor T m' (fun g => hM g m') := by
  ext t
  change t ⊗ₜ[k] (m + m') = t ⊗ₜ[k] m + t ⊗ₜ[k] m'
  exact TensorProduct.tmul_add _ _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
theorem tensorRightMor_smul (c : k) (m : M) :
    tensorRightMor T (c • m) (fun g => hM g _) = c • tensorRightMor T m (fun g => hM g m) := by
  ext t
  change t ⊗ₜ[k] (c • m) = c • t ⊗ₜ[k] m
  exact TensorProduct.tmul_smul _ _ _

noncomputable def twistMap (n : ℕ) :
    TensorProduct k (cohomology T n) M →ₗ[k] cohomology (T ⊗ M) n :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun m => (cohomologyMap (tensorRightMor T m (fun g => hM g m)) n).hom x
          map_add' := fun m m' => by
            rw [tensorRightMor_add T hM, cohomologyMap_add]
            rfl
          map_smul' := fun c m => by
            rw [tensorRightMor_smul T hM, cohomologyMap_smul, ModuleCat.hom_smul,
              LinearMap.smul_apply, RingHom.id_apply] }
      map_add' := fun x y => by
        ext m
        simp
      map_smul' := fun c x => by
        ext m
        simp }

theorem twistMap_tmul (n : ℕ) (x : cohomology T n) (m : M) :
    twistMap T hM n (x ⊗ₜ[k] m) = (cohomologyMap (tensorRightMor T m (fun g => hM g m)) n).hom x :=
  rfl

end TwistMap

section Subgroup

variable (N : Subgroup G) (T M : Rep.{u} k G)

variable [IsDiscreteRep T] [IsDiscreteRep M] (hM : ∀ (g : N) (m : M), M.ρ g m = m)

noncomputable def twistResMap (n : ℕ) :
    TensorProduct k (cohomology (Rep.res N.subtype T) n) M →ₗ[k]
      cohomology (Rep.res N.subtype (T ⊗ M)) n :=
  (cohomologyMap (resTensorIso N.subtype T M).inv n).hom ∘ₗ
    twistMap (M := Rep.res N.subtype M) (Rep.res N.subtype T) hM n

theorem twistResMap_tmul (n : ℕ) (x : cohomology (Rep.res N.subtype T) n) (m : M) :
    twistResMap N T M hM n (x ⊗ₜ[k] m) =
      (cohomologyMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) m
        (fun g => hM g m) ≫ (resTensorIso N.subtype T M).inv) n).hom x := by
  rw [cohomologyMap_comp]
  rfl

end Subgroup

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

section Bridge

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]

def cochainsAddEquiv {A : Rep.{u} k G} {A' : Rep.{u} k' G} (e : A ≃+ A') (n : ℕ) :
    locallyConstantCochains A n ≃+ locallyConstantCochains A' n where
  toFun x := ⟨fun g => e (x.1 g), x.2.comp e⟩
  invFun x := ⟨fun g => e.symm (x.1 g), x.2.comp e.symm⟩
  left_inv _ := Subtype.ext (funext fun _ => e.symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ => e.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add e _ _)

variable [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A]
  [IsDiscreteRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))


omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A] [IsDiscreteRep A'] in
include he in
theorem addEquiv_inhomogeneousCochains_d (i : ℕ) (f : (Fin i → G) → A) (g : Fin (i + 1) → G) :
    e ((inhomogeneousCochains.d A i).hom f g) =
      (inhomogeneousCochains.d A' i).hom (fun h => e (f h)) g := by

  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, map_add (f := _), map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hk : ∀ (c : ℕ) (a : A), ((-1 : k) ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k]
    push_cast
    rfl
  have hk' : ∀ (c : ℕ) (a : A'), ((-1 : k') ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k']
    push_cast
    rfl
  rw [hk, hk', map_zsmul]


include he in
theorem cochainsAddEquiv_d (i j : ℕ) (x : (cochainsComplex A).X i) :
    cochainsAddEquiv e j (((cochainsComplex A).d i j).hom x) =
      ((cochainsComplex A').d i j).hom (cochainsAddEquiv e i x) := by
  rcases eq_or_ne (i + 1) j with rfl | hij
  · rw [cochainsComplex_d, cochainsComplex_d]
    apply Subtype.ext
    funext g
    exact addEquiv_inhomogeneousCochains_d e he i x.1 g
  · have h' : ¬ (ComplexShape.up ℕ).Rel i j := hij
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    exact map_zero _

noncomputable def cochainsAbIso (i : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).obj ((cochainsComplex A).X i) ≅
      (forget₂ (ModuleCat.{u} k') Ab).obj ((cochainsComplex A').X i) :=
  (cochainsAddEquiv e i).toAddCommGrpIso

noncomputable def cochainsScAbIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj ((cochainsComplex A).sc n) ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj ((cochainsComplex A').sc n) :=
  ShortComplex.isoMk (cochainsAbIso e _) (cochainsAbIso e _) (cochainsAbIso e _)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)

end Bridge

section HomologyAb

variable {k k' : Type u} [CommRing k] [CommRing k']

noncomputable def homologyAbIsoOfAbIso {S₁ : ShortComplex (ModuleCat.{u} k)}
    {S₂ : ShortComplex (ModuleCat.{u} k')}
    (σ : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).obj S₁ ≅
      (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).obj S₂ :=
  ((ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).app S₁).symm ≪≫
    (ShortComplex.homologyFunctor Ab).mapIso σ ≪≫
    (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).app S₂

theorem homologyMap_comp_homologyAbIsoOfAbIso
    {S₁ T₁ : ShortComplex (ModuleCat.{u} k)} {S₂ T₂ : ShortComplex (ModuleCat.{u} k')}
    (φ₁ : S₁ ⟶ T₁) (φ₂ : S₂ ⟶ T₂)
    (σS : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂)
    (σT : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj T₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj T₂)
    (h : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.map φ₁ ≫ σT.hom =
      σS.hom ≫ (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.map φ₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).map φ₁ ≫
        (homologyAbIsoOfAbIso σT).hom =
      (homologyAbIsoOfAbIso σS).hom ≫
        (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).map φ₂ := by
  have n1 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).inv.naturality φ₁
  have n2 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).hom.naturality φ₂
  have n3 : ((forget₂ (ModuleCat.{u} k) Ab).mapShortComplex ⋙
        ShortComplex.homologyFunctor Ab).map φ₁ ≫ (ShortComplex.homologyFunctor Ab).map σT.hom =
      (ShortComplex.homologyFunctor Ab).map σS.hom ≫
        ((forget₂ (ModuleCat.{u} k') Ab).mapShortComplex ⋙ ShortComplex.homologyFunctor Ab).map φ₂ := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, h]
  simp only [homologyAbIsoOfAbIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => rw [n1]
  slice_lhs 2 3 => rw [n3]
  slice_lhs 3 4 => rw [n2]

end HomologyAb

section Cohomology

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A]
  [IsDiscreteRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

noncomputable def cohomologyAddEquivOfEquiv (n : ℕ) : cohomology A n ≃+ cohomology A' n :=
  (homologyAbIsoOfAbIso (cochainsScAbIso e he n)).addCommGroupIsoToAddEquiv

theorem cohomologyAddEquivOfEquiv_mapAlong {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {B : Rep.{u} k H} {B' : Rep.{u} k' H}
    [IsDiscreteRep B] [IsDiscreteRep B'] (eB : B ≃+ B')
    (heB : ∀ (h : H) (b : B), eB (B.ρ h b) = B'.ρ h (eB b))
    (f : Rep.res φ A ⟶ B) (f' : Rep.res φ A' ⟶ B') (hf : ∀ a : A, eB (f.hom a) = f'.hom (e a))
    (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv eB heB n ((cohomologyMapAlong φ hφ f n).hom x) =
      (cohomologyMapAlong φ hφ f' n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  have key := homologyMap_comp_homologyAbIsoOfAbIso
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMapAlong φ hφ f))
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMapAlong φ hφ f'))
    (cochainsScAbIso e he n) (cochainsScAbIso eB heB n) (by
      ext x <;> exact Subtype.ext (funext fun _ => hf _))
  exact congrArg (fun f => f.hom x) key

theorem cohomologyAddEquivOfEquiv_cohomologyConj (N : Subgroup G) [N.Normal] (n : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype A) n) :
    cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
        (fun s a => he s a) n ((cohomologyConj A N n g).hom x) =
      (cohomologyConj A' N n g).hom
        (cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
          (fun s a => he s a) n x) :=
  cohomologyAddEquivOfEquiv_mapAlong (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
    (fun s a => he s a) (GroundTheory.GroupCoh.conjHom N g) (continuous_conjHom N g)
    (B := Rep.res N.subtype A) (B' := Rep.res N.subtype A') e (fun s a => he s a)
    (GroundTheory.GroupCoh.conjMor A N g) (GroundTheory.GroupCoh.conjMor A' N g) (fun a => he g a) n x

end Cohomology

section ZMod

variable {G : Type} [Group G] (l : ℕ) (A : Rep.{0} (ULift.{0} ℤ) G)
  (hA : ∀ a : A, l • a = 0)

noncomputable def zmodRepOfTorsion : Rep.{0} (ZMod l) G :=
  letI : Module (ZMod l) A := AddCommGroup.zmodModule hA
  Rep.of (X := A)
    { toFun := fun g => (A.ρ g).toAddMonoidHom.toZModLinearMap l
      map_one' := by
        ext a
        simp
      map_mul' := fun g h => by
        ext a
        simp [Module.End.mul_apply] }

def zmodRepOfTorsionEquiv : A ≃+ zmodRepOfTorsion l A hA :=
  AddEquiv.refl A

variable [TopologicalSpace G]

instance isDiscreteRep_zmodRepOfTorsion [IsDiscreteRep A] :
    IsDiscreteRep (zmodRepOfTorsion l A hA) :=
  ⟨fun a => isOpen_stabilizer A a⟩

variable [IsTopologicalGroup G] [IsDiscreteRep A]

noncomputable def cohomologyZModEquiv (n : ℕ) :
    cohomology A n ≃+ cohomology (zmodRepOfTorsion l A hA) n :=
  cohomologyAddEquivOfEquiv (zmodRepOfTorsionEquiv l A hA) (fun _ _ => rfl) n

end ZMod

end GroundTheory.ProfCoh
end
