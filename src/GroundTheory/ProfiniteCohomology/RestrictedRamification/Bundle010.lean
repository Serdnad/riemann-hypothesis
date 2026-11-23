module

public import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.ProfiniteCohomology.PoincarePairs.IsDiscreteRepResHomCoindRes
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
public import GroundTheory.ProfiniteCohomology.Bundle010
public import GroundTheory.ProfiniteCohomology.PoincarePairs.Devissage
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle009
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupKummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupNat
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

noncomputable section

attribute [local instance 2000] Rep.hV2

section Trace

variable {k G : Type u} [CommRing k] [Group G] (U : Subgroup G) [U.FiniteIndex] (A : Rep.{u} k G)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex


open Classical in
def coindTracePreimage (a : A) : Rep.coind U.subtype (Rep.res U.subtype A) :=
  ⟨fun g => if g ∈ U then A.ρ g a else 0, fun u g => by
    beta_reduce
    by_cases hg : g ∈ U
    · have hug : U.subtype u * g ∈ U := U.mul_mem u.2 hg
      rw [if_pos hug, if_pos hg, map_mul, Module.End.mul_apply]
      rfl
    · have hug : U.subtype u * g ∉ U := fun h => hg (by
        have := U.mul_mem (U.inv_mem u.2) h
        rwa [Subgroup.coe_subtype, ← mul_assoc, inv_mul_cancel, one_mul] at this)
      rw [if_neg hug, if_neg hg, map_zero]⟩

theorem coindTrace_coindTracePreimage (a : A) : (coindTrace U A).hom (coindTracePreimage U A a) = a := by
  classical
  rw [coindTrace_hom_apply, Finset.sum_eq_single ((1 : G) : G ⧸ U)]
  · rw [coindTraceTerm_apply, inv_one]
    change A.ρ 1 (if (1 : G) ∈ U then A.ρ 1 a else 0) = a
    rw [if_pos U.one_mem, map_one, Module.End.one_apply, Module.End.one_apply]
  · intro c _ hc
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [coindTraceTerm_apply]
      have hx : x⁻¹ ∉ U := fun h => hc (QuotientGroup.eq.2 (by simpa using h))
      change A.ρ x (if x⁻¹ ∈ U then A.ρ x⁻¹ a else 0) = 0
      rw [if_neg hx, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem surjective_coindTrace : Function.Surjective (coindTrace U A).hom :=
  fun a => ⟨coindTracePreimage U A a, coindTrace_coindTracePreimage U A a⟩

end Trace

section Sequence

variable {k G : Type u} [CommRing k] [Group G] (U : Subgroup G) [U.FiniteIndex] (A : Rep.{u} k G)

def coindTraceKer : Submodule k (Rep.coind U.subtype (Rep.res U.subtype A)) :=
  LinearMap.ker (coindTrace U A).hom.toLinearMap

theorem coindTraceKer_le_comap (g : G) :
    coindTraceKer U A ≤ (coindTraceKer U A).comap ((Rep.coind U.subtype (Rep.res U.subtype A)).ρ g) := by
  intro f hf
  change (coindTrace U A).hom ((Rep.coind U.subtype (Rep.res U.subtype A)).ρ g f) = 0
  rw [Rep.hom_comm_apply]
  rw [show (coindTrace U A).hom f = 0 from hf, map_zero]

def coindTraceShortComplex : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (Rep.subtype _ (coindTraceKer U A) (coindTraceKer_le_comap U A)) (coindTrace U A) (by
    ext f
    exact f.2)

theorem coindTraceShortComplex_shortExact : (coindTraceShortComplex U A).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro f hf
    exact ⟨⟨f, hf⟩, rfl⟩
  · exact (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  · exact (Rep.epi_iff_surjective _).2 (surjective_coindTrace U A)

end Sequence

section Cores

theorem inv_comp_hom_apply_base {k : Type u} [CommRing k] {X Y Z : ModuleCat.{u} k} (e : X ≅ Y) (g : X ⟶ Z)
    (x : X) : (e.inv ≫ g).hom (e.hom.hom x) = g.hom x := by
  have h := congrArg (fun f : X ⟶ X => f.hom x) e.hom_inv_id
  change g.hom (e.inv.hom (e.hom.hom x)) = g.hom x
  exact congrArg g.hom h

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem surjective_compactCores_three (V : OpenSubgroup G) (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
    [Finite D] {n : ℕ} (hD : ∀ d : D, n • d = 0)
    (hV : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Subsingleton (compactCohomologyRes φ M 4)) :
    Function.Surjective (compactCores φ V D 3).hom := by
  have hS := coindTraceShortComplex_shortExact (V : Subgroup G) D
  have : IsDiscreteRep (coindTraceShortComplex (V : Subgroup G) D).X₂ :=
    inferInstanceAs (IsDiscreteRep (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype D)))
  have : IsDiscreteRep (coindTraceShortComplex (V : Subgroup G) D).X₁ :=
    isDiscreteRep_subrepresentation _ _ _
  have : IsDiscreteRep (coindTraceShortComplex (V : Subgroup G) D).X₃ := inferInstanceAs (IsDiscreteRep D)
  have : Finite (Rep.res (V : Subgroup G).subtype D) := inferInstanceAs (Finite D)
  have : Finite (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype D)) :=
    finite_coind V _
  have : Finite (coindTraceShortComplex (V : Subgroup G) D).X₁ :=
    inferInstanceAs (Finite (coindTraceKer (V : Subgroup G) D))
  have hN : ∀ m : (coindTraceShortComplex (V : Subgroup G) D).X₁, n • m = 0 := fun m =>
    Subtype.ext (Subtype.ext (funext fun x => hD _))
  have h4 := hV _ hN
  have hg : Function.Surjective (compactCohomologyResMap φ (coindTrace (V : Subgroup G) D) 3).hom := fun y =>
    (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (compactRes_exact₃ φ hS 3)
      (@Subsingleton.elim _ h4 _ _)
  intro y
  refine (hg y).elim fun x hx => ⟨(mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype D) 3).hom.hom x, ?_⟩
  exact (inv_comp_hom_apply_base _ _ x).trans hx

end Cores

section GS

open IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem surjective_gs_compactCores_three (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
    {n : ℕ} (hn : n ≠ 0) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K.1) (V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (D : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep D] [Finite D]
    (hD : ∀ d : D, n • d = 0) :
    Function.Surjective (compactCores (gsFinFamily S ιs) V D 3).hom :=
  surjective_compactCores_three (gsFinFamily S ιs) V D hD fun M _ _ hM =>
    subsingleton_compactCohomology_four K S hn hS hK ιs M hM

end GS

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh

universe u

attribute [local instance 2000] Rep.hV2

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]


omit [NeZero n] in
theorem localInvU_eq_brauerInvOfIsSepClosure (v : HeightOneSpectrum (𝓞 K.1))
    (x : cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2) :
    localInvU v x = brauerInvOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) x :=
  ((DFunLike.congr_fun (localInvU_eq v) x).trans ((AddMonoidHom.comp_apply _ _ _).trans
    (congrArg _ (AddMonoidHom.comp_apply _ _ _)))).trans
    ((brauerInvZOfIsSepClosure_cohomologyMap_uliftInt_base _ (𝟙 _) (galUnitsToZ _ _) (fun _ => rfl) x).trans
      (congrArg _ (congrArg (fun f => ModuleCat.Hom.hom f x) (cohomologyMap_id 2))))


omit [NeZero n] in
theorem gsRootsOmegaMor_eq_gsRootsLocalMor (v : S) : gsRootsOmegaMor S ιs n v = gsRootsLocalMor S ιs n v := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun ζ => ?_))
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (restrictRootsOfUnity_coe_apply _ _).trans (gsRootsLocalMor_hom_apply S ιs n v ζ).symm

theorem zmodToQZ_gsLocalInvRoots_eq_localInvU (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsLocalInvRoots S ιs n v z) =
      localInvU (v : HeightOneSpectrum (𝓞 K.1))
        ((cohomologyMap (gsRootsOmegaMor S ιs n v ≫ rootsOfUnityToUnits _ _ n) 2).hom z) := by
  exact (zmodToQZ_gsLocalInvRoots S ιs n v z).trans ((gsLocalInvRootsQZ_eq_brauerInv_base S ιs n v z).trans
    ((congrArg (fun f => brauerInvOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        ((cohomologyMap (f ≫ rootsOfUnityToUnits _ _ n) 2).hom z))
      (gsRootsOmegaMor_eq_gsRootsLocalMor S ιs n v).symm).trans (localInvU_eq_brauerInvOfIsSepClosure _ _).symm))

theorem compactCup_congr_apply {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
    (φ : ∀ v, H v →ₜ* G) {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
    {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
    {μ₁ μ₂ : A ⊗ B ⟶ C} {μ₁ᵥ μ₂ᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v}
    (h₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₁ᵥ v)
    (h₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₂ᵥ v)
    (e : μ₁ = μ₂) (eᵥ : ∀ v, μ₁ᵥ v = μ₂ᵥ v) {r s m : ℕ} (h : r + s = m) (y : compactCohomology φ A Aᵥ a r)
    (x : cohomology B s) :
    compactCup φ μ₁ μ₁ᵥ h₁ h y x = compactCup φ μ₂ μ₂ᵥ h₂ h y x := by
  subst e
  obtain rfl : μ₁ᵥ = μ₂ᵥ := funext eᵥ
  rfl

section ActNatural

variable {H : Type} [Group H]


omit [NeZero n] in
theorem zmodActPairing_comp (D D' Z' : Rep.{0} (ULift.{0} ℤ) H) (hD : ∀ d : D, n • d = 0)
    (hD' : ∀ d : D', n • d = 0) (e : Z' →+ ZMod n) (hZ : ∀ (g : H) (z : Z'), Z'.ρ g z = z) (f : D ⟶ D') :
    zmodActPairing n D Z' hD e hZ ≫ f = (f ⊗ₘ 𝟙 Z') ≫ zmodActPairing n D' Z' hD' e hZ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun (d : D) (z : Z') => ?_))
  change f.hom ((zmodActPairing n D Z' hD e hZ).hom (d ⊗ₜ[ULift.{0} ℤ] z)) =
    (zmodActPairing n D' Z' hD' e hZ).hom (f.hom d ⊗ₜ[ULift.{0} ℤ] z)
  rw [zmodActPairing_tmul, zmodActPairing_tmul, map_zsmul]

end ActNatural


omit [NeZero n] in
theorem zmodMulPairingRight_gsRoots_eq :
    zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n) =
      zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
        (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (ζ : gsRoots S n) (a : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) => ?_))
  change (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n)).hom (a ⊗ₜ[ULift.{0} ℤ] ζ) =
    (zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
      (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl)).hom (ζ ⊗ₜ[ULift.{0} ℤ] a)
  exact (zmodMulPairing_tmul n _ _ a.down ζ).trans (zmodActPairing_tmul n (gsRoots S n)
    (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
    (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) ζ a).symm

section ResPairing

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (ψ : H →* G) {A B C : Rep.{u} k G} {C' : Rep.{u} k H}

theorem resFunctor_map_comp_id_comp (μ : A ⊗ B ⟶ C) (g : Rep.res ψ C ⟶ C') :
    (Rep.resFunctor ψ).map (μ ≫ 𝟙 C) ≫ g =
      resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ ((Rep.resFunctor ψ).map μ ≫ g) :=
  (congrArg (· ≫ g) ((congrArg (Rep.resFunctor ψ).map (Category.comp_id μ)).trans
    ((Category.comp_id _).symm.trans (resFunctor_map_comp_id ψ μ)))).trans (Category.assoc _ _ _)

theorem resFunctor_map_id_tensor_comp (μ : A ⊗ B ⟶ C) (g : Rep.res ψ C ⟶ C')
    (ν : Rep.res ψ A ⊗ Rep.res ψ B ⟶ C') (e : (Rep.resFunctor ψ).map μ ≫ g = ν) :
    (Rep.resFunctor ψ).map ((𝟙 A ⊗ₘ 𝟙 B) ≫ μ) ≫ g = resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ ν :=
  (congrArg (fun f => (Rep.resFunctor ψ).map f ≫ g)
    (((congrArg (· ≫ μ) (MonoidalCategory.id_tensorHom_id A B)).trans (Category.id_comp μ)).trans
      (Category.comp_id μ).symm)).trans
    ((resFunctor_map_comp_id_comp ψ μ g).trans (congrArg (resTensorHom ψ (𝟙 _) (𝟙 _) ≫ ·) e))

end ResPairing

abbrev gsZmodPairing :
    gsRoots S n ⊗ zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n ⟶ gsRoots S n :=
  zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
    (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl)

abbrev gsZmodPairingᵥ (v : S) :
    galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n ⊗
      Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) ⟶
    galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  zmodActPairing n _ _ (nsmul_galRootsOfUnity_eq_zero' n) (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom
    (fun _ _ => rfl)

omit [NeZero n] in
theorem resFunctor_map_gsZmodPairing (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsZmodPairing S n) =
      zmodActPairing n (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
        (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) (nsmul_gsRoots S n)
        (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl))

omit [NeZero n] in
theorem gsZmodPairing_hμ (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsZmodPairing S n) ≫ gsRootsOmegaMor S ιs n v =
      resTensorHom (gsFinFamily S ιs v).toMonoidHom (gsRootsOmegaMor S ιs n v) (𝟙 _) ≫ gsZmodPairingᵥ S ιs n v :=
  (congrArg (· ≫ gsRootsOmegaMor S ιs n v) (resFunctor_map_gsZmodPairing S ιs n v)).trans
    (zmodActPairing_comp n (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
      (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n))
      (nsmul_gsRoots S n) (nsmul_galRootsOfUnity_eq_zero' n)
      (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) (gsRootsOmegaMor S ιs n v))


omit [NeZero n] in
theorem gsRootsComparison_compactCupRes (y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2)
    (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    (gsRootsComparison S ιs n 3).hom (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) =
      compactCup (gsFinFamily S ιs) (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
        (show 2 + 1 = 3 from rfl) ((gsRootsComparison S ιs n 2).hom y) x := by
  have hg : ∀ v, 𝟙 (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (𝟙 (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v :=
    fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have e1 := compactCohomologyMap_compactCup (gsFinFamily S ιs) (A := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n) (C' := gsRoots S n)
    (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (Cᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) (C'ᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (a := fun _ => 𝟙 _) (c := fun _ => 𝟙 _) (c' := gsRootsOmegaMor S ιs n)
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
    (fun v => (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)))
    (fun v => resFunctor_map_comp_id _ _) (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg
    (fun v => resFunctor_map_comp_id_comp _ _ _) (show 2 + 1 = 3 from rfl) y x
  have e2 := compactCup_compactCohomologyMap (gsFinFamily S ιs) (A := gsRoots S n) (A' := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n)
    (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) (A'ᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (Cᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (a := fun _ => 𝟙 _) (a' := gsRootsOmegaMor S ιs n) (c := gsRootsOmegaMor S ιs n)
    (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg
    (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
    (fun v => resFunctor_map_id_tensor_comp _ _ _ _ (gsZmodPairing_hμ S ιs n v)) (show 2 + 1 = 3 from rfl) y x
  have eμ : zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n) ≫ 𝟙 (gsRoots S n) =
      (𝟙 (gsRoots S n) ⊗ₘ 𝟙 (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) ≫ gsZmodPairing S n :=
    ((Category.comp_id _).trans (zmodMulPairingRight_gsRoots_eq S n)).trans
      ((congrArg (· ≫ gsZmodPairing S n) (MonoidalCategory.id_tensorHom_id _ _)).trans (Category.id_comp _)).symm
  have eμᵥ : ∀ v, (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (gsRootsOmegaMor S ιs n v ⊗ₘ 𝟙 _) ≫ gsZmodPairingᵥ S ιs n v := fun v =>
    (congrArg (fun f => (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map f ≫ gsRootsOmegaMor S ιs n v)
      (zmodMulPairingRight_gsRoots_eq S n)).trans (gsZmodPairing_hμ S ιs n v)
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact compactCup_congr_apply (gsFinFamily S ιs) _ _ eμ eμᵥ (show 2 + 1 = 3 from rfl) y x

end

end GroundTheory.ProfCoh
end
