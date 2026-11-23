module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueExtensionOfForallNormLeOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : _root_.GlobalTheory.ZH.RatModel o Ω) in
theorem _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  infer_instance


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : _root_.GlobalTheory.ZH.RatModel o Ω) in
theorem _root_.GlobalTheory.ZH.RatModel.flat_int [CharZero Ω] (π : M.Z ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℤ) : Flat π := by
  rw [Flat.iff_flat_stalkMap]
  intro x
  haveI : CharZero (M.Z.presheaf.stalk x) :=
    RingHom.charZero ((M.O x).val.toRingHom.comp
      (M.stalkEquiv x).toRingHom)
  let q : PrimeSpectrum ℤ := π x
  haveI : q.asIdeal.IsPrime := q.isPrime
  letI : Algebra ((Spec.structureSheaf ℤ).presheaf.stalk q) (M.Z.presheaf.stalk x) :=
    (π.stalkMap x).hom.toAlgebra
  have hflat : Module.Flat ℤ (M.Z.presheaf.stalk x) := inferInstance
  have hT : @IsScalarTower ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul := by
    refine @IsScalarTower.mk ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q)
      (M.Z.presheaf.stalk x)
      (StructureSheaf.stalkAlgebra ℤ q).toSMul this.toSMul (AddCommGroup.toIntModule _).toSMul
      (fun n s m => ?_)
    have h1 := @Algebra.smul_def' ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
      (StructureSheaf.stalkAlgebra ℤ q) n s
    have h2 : @algebraMap ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra ℤ q) n = n :=
      eq_intCast _ n
    rw [h2] at h1
    erw [h1]
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  exact (@Module.flat_iff_of_isLocalization ℤ ((Spec.structureSheaf ℤ).presheaf.stalk q) _ _
    (StructureSheaf.stalkAlgebra ℤ q) q.asIdeal.primeCompl (StructureSheaf.IsLocalization.to_stalk ℤ q)
    (M.Z.presheaf.stalk x) _ _ _ hT).mpr hflat

end GlobalTheory.ZH.RatModel

namespace GlobalTheory.ZH


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
theorem _root_.GlobalTheory.ZH.classical_points_and_local_regularity :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o] [CharZero Ω]
      (M : _root_.GlobalTheory.ZH.RatModel o Ω)
      (U₀ : M.Z.Opens), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z →
      ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty →
        ∀ z : M.Z, IsClosed ({z} : Set M.Z) →
        (∃ (p : ℕ) (_ : Fact p.Prime)
          (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
          M.Cen U₁ z y) ∧
        ∀ φ ∈ M.ringOn U₁,
          (∀ (p : ℕ) [Fact p.Prime]
            (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
            M.Cen U₁ z y →
            ‖M.val (_root_.GlobalTheory.ZH.gPt p ≫ y) φ‖ ≤ 1) →
          φ ∈ M.O z) ∧ JacobsonSpace M.Z) := by
  intro o Ω _ _ _ _ _ M U₀ hN
  haveI := _root_.GlobalTheory.ZH.RatModel.locallyOfFiniteType_int M
  haveI : Flat (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) := M.flat_int _
  refine ⟨fun U₁ _ hU₁ z hz => ⟨?_, ?_⟩,
    _root_.GlobalTheory.jacobsonSpace_of_locallyOfFiniteType_int (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o))⟩
  · obtain ⟨p, hp, y, h1, h2⟩ := _root_.GlobalTheory.padicAlgCl_integral_points.1 M.Z
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) z hz U₁ hU₁
    exact ⟨p, hp, y, h1, h2⟩
  · intro φ hφ hb
    obtain ⟨f, rfl⟩ :=
      (_root_.GlobalTheory.ZH.RatModel.mem_ringOn_iff_exists hU₁).1 hφ
    haveI := _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hN z
    haveI : IsIntegrallyClosed (M.Z.presheaf.stalk z) :=
      IsIntegrallyClosed.of_equiv (M.stalkEquiv z).symm
    have hbounded : ∀ (p : ℕ) [Fact p.Prime]
        (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.GlobalTheory.ZH.OO p) ⟶ M.Z),
        y (_root_.GlobalTheory.ZH.cPt p) = z →
        Set.range (_root_.GlobalTheory.ZH.gPt p ≫ y) ⊆ U₁ →
        ‖_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF
          (_root_.GlobalTheory.ZH.gPt p ≫ y) U₁ f‖ ≤ 1 := by
      intro p _ y hy hr
      have hle := hb p y ⟨hy, hr⟩
      rwa [_root_.GlobalTheory.ZH.RatModel.val_valF hr] at hle
    haveI : Nonempty U₁ := hU₁.to_subtype
    obtain ⟨p, hp, hpx⟩ := _root_.GlobalTheory.exists_prime_residueField_eq_zero
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) hz
    haveI : Fact p.Prime := ⟨hp⟩
    have hm := _root_.GlobalTheory.mem_range_stalk_of_forall_norm_le_one
      (M.s ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℤ o)) hz hpx (φ := f) fun K _ y hy hyx => by
        haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
        have e : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) ≫ y =
            spMap K.val.toRingHom ≫
              Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y := by
          rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
          rfl
        have h1 : (spMap (integralClosureToPadicAlgClIntegers K) ≫ y) (cPt p) =
            y (IsLocalRing.closedPoint (integralClosure ℤ_[p] K)) := by
          refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg y ?_)
          exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
        have h2 : Set.range (gPt p ≫ (spMap (integralClosureToPadicAlgClIntegers K) ≫ y)) ⊆ U₁ := by
          rw [e]
          rintro _ ⟨q, rfl⟩
          exact hy (Set.mem_univ (spMap K.val.toRingHom q))
        have h3 : valF (gPt p ≫ (spMap (integralClosureToPadicAlgClIntegers K) ≫ y)) U₁ f =
            (((Scheme.ΓSpecIso (.of K)).hom
              ((Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE
                U₁ ⊤ hy f) : K) : PadicAlgCl p) := by
          rw [e]
          have ht : ⊤ ≤ (spMap K.val.toRingHom ≫
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y)) ⁻¹ᵁ U₁ :=
            fun q _ => hy (Set.mem_univ (spMap K.val.toRingHom q))
          rw [valF, dite_eq_left ht]
          have eqn : (spMap K.val.toRingHom ≫
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y)).appLE U₁ ⊤ ht ≫
              (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom =
              (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE U₁ ⊤ hy ≫
              (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom K.val.toRingHom := by
            rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap K.val.toRingHom) _ U₁ ⊤ ⊤ hy le_rfl, Category.assoc]
            rfl
          exact congrArg (fun g => g.hom f) eqn
        rw [← h3]
        exact hbounded p (spMap (integralClosureToPadicAlgClIntegers K) ≫ y) (h1.trans hyx) h2
    obtain ⟨W, hW, ψ, hzW, -, hs⟩ :=
      _root_.GlobalTheory.exists_germToFunctionField_eq_of_mem_range_stalk hm (W := ⊤) trivial
    have hg : ∀ (W : M.Z.Opens) [Nonempty W], genericPoint M.Z ∈ W := fun W h =>
      ((genericPoint_spec M.Z).mem_open_set_iff W.isOpen).mpr (by simpa using h)
    haveI : Nonempty (W ⊓ U₁ : M.Z.Opens) := ⟨⟨_, hg W, hg U₁⟩⟩
    have h := M.Z.germToFunctionField_injective (W ⊓ U₁)
      ((M.Z.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ ψ).trans
        (hs.trans (M.Z.presheaf.germ_res_apply (homOfLE inf_le_right) _ _ f).symm))
    rw [_root_.GlobalTheory.ZH.RatModel.mem_O]
    refine ⟨W, ψ, hzW, ?_⟩
    have hne := M.nonempty_inf ⟨z, hzW⟩ hU₁
    have hv := congrArg (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valF M.pt _) h
    rwa [M.valF_resG _ hne,
      M.valF_resG _ hne] at hv

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points GlobalTheory.ProjSpace GlobalTheory.TuplePoint

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {n : ℕ} {t : Fin (n + 1) → Ω}

theorem exists_div_of_closure_ratios_eq_top
    (h : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤) {i : Fin (n + 1)}
    (hi : t i ≠ 0) (x : Ω) : ∃ a ∈ Algebra.adjoin o (Set.range fun j => t j / t i),
      ∃ b ∈ Algebra.adjoin o (Set.range fun j => t j / t i), a / b = x := by
  have hle : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤
      Subfield.closure ((Algebra.adjoin o (Set.range fun j => t j / t i)).toSubring : Set Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
    · rw [← div_div_div_cancel_right₀ hi]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  have hx := hle (h ▸ Subfield.mem_top x)
  rwa [Subfield.mem_closure_iff, Subring.closure_eq] at hx

section Closed

variable {ht : t ≠ 0} {Z : Scheme.{0}} {ξ : Sp Ω ⟶ Z} {π : Z ⟶ PSpace o n} (hπ : ξ ≫ π = point o t ht)

include hπ

theorem exists_valF_preimage_chart_iff [IsClosedImmersion π] {i : Fin (n + 1)} (hi : t i ≠ 0) (x : Ω) :
    (∃ f : Γ(Z, π ⁻¹ᵁ chart o n i), valF ξ _ f = x) ↔ x ∈ Algebra.adjoin o (Set.range fun j => t j / t i) := by
  have h := (le_point_preimage_iff (o := o) (ht := ht) i).2 hi
  have key : ∀ g, valF ξ _ ((π.app (chart o n i)).hom g) = (valMap (point o t ht) _ h).hom g := fun g => by
    rw [← valR_eq, ← hπ]
    exact (valR_comp ξ π _ g).symm
  rw [← SetLike.mem_coe, ← range_valMap_point h]
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨g, rfl⟩ := π.app_surjective _ (isAffineOpen_chart o n i) f
    exact ⟨g, (key g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, key g⟩

end Closed

theorem exists_valF_eq_div {Z : Scheme.{0}} (ξ : Sp Ω ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (a b : Γ(Z, U))
    (hb : valF ξ U b ≠ 0) : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b ∧
      ∃ f : Γ(Z, Z.basicOpen b), valF ξ _ f = valF ξ U a / valF ξ U b := by
  have hle : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b := (le_preimage_basicOpen_iff _ hU b).2 (isUnit_iff_ne_zero.2 hb)
  have hu : IsUnit (resG _ (Z.basicOpen_le b) b) :=
    RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace b
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have h1 : valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) b * c) = 1 :=
    (congrArg _ hc).trans (valR_one _ _ hle)
  rw [valR_mul _ _ hle] at h1
  have h2 : ∀ s, valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) s) = valF ξ U s :=
    fun s => valR_res _ _ hle _
  refine ⟨hle, resG _ (Z.basicOpen_le b) a * c, (valR_mul _ _ hle _ _).trans ?_⟩
  rw [h2 b] at h1
  rw [h2 a, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]

theorem RatModel.isCl_of_isClosedImmersion (M : RatModel o Ω) {ht : t ≠ 0} (π : M.Z ⟶ PSpace o n)
    [IsClosedImmersion π] (hπ : M.pt ≫ π = point o t ht) : M.IsCl t := by
  have h1 : ∀ (k : Fin (n + 1)) (z : M.Z), z ∈ π ⁻¹ᵁ chart o n k → M.Div t k z := fun k z hz =>
    have hW := M.top_le_preimage_pt ⟨z, hz⟩
    ⟨ne_zero_of_le hπ hW le_rfl, fun j => ⟨_, pullRatio π _ k le_rfl j, hz, valR_pullRatio hπ hW le_rfl j⟩⟩
  have h2 : ∀ (i : Fin (n + 1)) (z : M.Z), M.Div t i z → z ∈ π ⁻¹ᵁ chart o n i := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_mem_chart o n (π z)
    have hk' : z ∈ π ⁻¹ᵁ chart o n k := hk
    have hu := ((h1 k z hk').div_iff_isUnit i).1 hz
    have e : (⟨t i / t k, (h1 k z hk').2 i⟩ : M.O z) =
        ⟨_, RatModel.valF_mem_O hk' (pullRatio π _ k le_rfl i)⟩ :=
      Subtype.ext (valR_pullRatio hπ (M.top_le_preimage_pt ⟨z, hk'⟩) le_rfl i).symm
    rw [e, RatModel.isUnit_valF_iff hk', basicOpen_pullRatio] at hu
    exact hu.2
  refine ⟨fun z => (exists_mem_chart o n (π z)).imp fun k hk => h1 k z hk, fun i hi => ?_⟩
  refine ⟨π ⁻¹ᵁ chart o n i, (isAffineOpen_chart o n i).preimage π,
    Set.ext fun z => ⟨h1 i z, h2 i z⟩, ?_⟩
  ext x
  rw [RatModel.mem_ringOn_iff_exists ⟨_, h2 i _ (RatModel.div_genericPoint hi)⟩,
    exists_valF_preimage_chart_iff hπ hi]

theorem exists_isCl_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (n : ℕ) (t : Fin (n + 1) → Ω), (∃ i, t i ≠ 0) → Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ → ∃ M : RatModel o Ω, M.IsCl t ∧ IsProjOver M.s := by
  intro o Ω _ _ _ _ n t ⟨i, hi⟩ h
  have ht : t ≠ 0 := Function.ne_iff.2 ⟨i, hi⟩
  let φ := point o t ht
  have hsep : IsProper (PSpace.str o n) :=
    projProper o _ _ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hqc : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ PSpace.str o n) := by
      rw [point_str]
      infer_instance
    exact QuasiCompact.of_comp φ (PSpace.str o n)
  have hπ : φ.toImage ≫ φ.imageι = point o t ht := φ.toImage_imageι
  have hW := le_preimage_chart hπ hi
  let M : RatModel o Ω :=
    { Z := φ.image
      s := φ.imageι ≫ PSpace.str o n
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := φ.toImage
      pt_s := by rw [← Category.assoc, hπ, point_str]
      gen := by
        have e : Set.range φ.toImage = {φ.toImage (IsLocalRing.closedPoint Ω)} :=
          Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, by
            rintro _ ⟨w, rfl⟩
            rw [Subsingleton.elim w (IsLocalRing.closedPoint Ω)]⟩
        have hd : IsGenericPoint (φ.toImage (IsLocalRing.closedPoint Ω)) Set.univ := by
          rw [isGenericPoint_def, ← e]
          exact φ.toImage.denseRange.closure_range
        rw [e, hd.eq (genericPoint_spec _)]
      onto := fun x => by
        obtain ⟨_, ha, _, hb, rfl⟩ := exists_div_of_closure_ratios_eq_top h hi x
        obtain ⟨a, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 ha
        obtain ⟨b, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 hb
        by_cases h0 : valF φ.toImage _ b = 0
        · exact ⟨_, b, ⟨_, hW (x := IsLocalRing.closedPoint Ω) trivial⟩, by rw [h0, div_zero]⟩
        · obtain ⟨hle, f, hf⟩ := exists_valF_eq_div _ hW a b h0
          exact ⟨_, f, ⟨_, hle (x := IsLocalRing.closedPoint Ω) trivial⟩, hf⟩ }
  exact ⟨M, M.isCl_of_isClosedImmersion φ.imageι hπ, n, φ.imageι, inferInstance, rfl⟩

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

open GlobalTheory.Points IsLocalRing

variable {p : ℕ} [Fact p.Prime]

noncomputable def padicIntToOO (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* OO p :=
  (algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict (OO p) fun _ =>
    (mem_OO_iff _).2 ((GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 isIntegral_algebraMap)

theorem isIntegral_padicIntToOO : (padicIntToOO p).IsIntegral := by
  intro x
  obtain ⟨q, hq, h⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (x : PadicAlgCl p)).2 ((mem_OO_iff _).1 x.2)
  refine ⟨q, hq, Subtype.ext ?_⟩
  exact (Polynomial.hom_eval₂ q (padicIntToOO p) (OO p).subtype x).trans h

theorem natCast_residueField_OO : ((p : ℕ) : ResidueField (OO p)) = 0 := by
  rw [← map_natCast (residue (OO p)), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    not_isUnit_OO_iff]
  have h : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) p := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem isIntegral_int_residueField_OO : (Int.castRingHom (ResidueField (OO p))).IsIntegral := by
  intro x
  set ψ : ℤ_[p] →+* ResidueField (OO p) := (residue (OO p)).comp (padicIntToOO p)
  have hψ : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ isIntegral_padicIntToOO
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  obtain ⟨q, hq, h⟩ := hψ x
  have hl : q.map ψ ∈ Polynomial.lifts (Int.castRingHom (ResidueField (OO p))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg ψ hc
    rw [map_sub, map_mul, map_natCast, map_natCast, natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
    exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩
  obtain ⟨r, hr, -, hrm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq.map ψ)
  refine ⟨r, hrm, ?_⟩
  rw [← Polynomial.eval_map, hr, Polynomial.eval_map, h]

theorem isMaximal_comap_maximalIdeal_OO {A : Type*} [CommRing A] (φ : A →+* OO p) :
    ((maximalIdeal (OO p)).comap φ).IsMaximal := by
  have h : ((residue (OO p)).comp φ).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom A) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact isIntegral_int_residueField_OO
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ h ⊥
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, ker_residue] at this

theorem isClosed_singleton_cPt {X : Scheme.{0}} (y : Sp (OO p) ⟶ X) : IsClosed ({y (cPt p)} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have hs : y (cPt p) ⤳ w := specializes_iff_mem_closure.2 hw
  obtain ⟨U, hU, hwU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := w) trivial
  have hzU : y (cPt p) ∈ U := hs.mem_open U.isOpen hwU
  have hle : ⊤ ≤ y ⁻¹ᵁ U := (le_preimage_iff y U).2 hzU
  have key : ∀ f : Γ(X, U), y (cPt p) ∈ X.basicOpen f ↔
      f ∉ (maximalIdeal (OO p)).comap (valMap y U hle).hom := fun f => by
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, ← le_preimage_iff,
      le_preimage_basicOpen_iff y hle, valR_eq y U hle]
  have hm := isMaximal_comap_maximalIdeal_OO (valMap y U hle).hom
  refine (Specializes.antisymm ?_ hs).eq
  rw [specializes_iff_forall_open]
  intro V hV hzV
  obtain ⟨f, hfV, hzf⟩ := hU.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨_, hzV⟩ hzU
  refine hfV ?_
  obtain ⟨g, c, hc, e⟩ := hm.exists_inv ((key f).1 hzf)
  have hwc : w ∉ X.basicOpen c := fun h => (key c).1 (hs.mem_open (X.basicOpen c).isOpen h) hc
  rw [X.mem_basicOpen _ _ hwU] at hwc
  show w ∈ X.basicOpen f
  rw [X.mem_basicOpen _ _ hwU]
  have e' := congrArg (X.presheaf.germ U w hwU).hom e
  rw [map_add (f := _), map_mul, map_one] at e'
  rcases isUnit_or_isUnit_of_add_one e' with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd h hwc

theorem isClosed_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o]
    (M : RatModel o Ω) (U : Set M.Z) (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
    M.Cen U z y → IsClosed ({z} : Set M.Z) :=
  fun _ _ _ _ _ _ _ _ _ _ _ y h => h.1 ▸ isClosed_singleton_cPt y

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_chartPull_g {Y Y' Z : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (r : Z ⟶ Y') (z : Z) (i j : A'.ι) (hi : r z ∈ A'.U i) (hj : r z ∈ A'.U j) :
    gm r z (A'.U i ⊓ A'.U j) (A'.g i j) =
      gm (r ≫ h) z (A.U (a.idx i) ⊓ A.U (a.idx j)) (A.g (a.idx i) (a.idx j)) := by
  have le : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (a.idx i) ⊓ A.U (a.idx j)) := fun y hy => ⟨a.le i hy.1, a.le j hy.2⟩
  have e : A'.g i j = res le (pullU h _ (A.g (a.idx i) (a.idx j))) := unit_ext fun y hy =>
    (a.g y i j hy.1 hy.2).trans ((gm_res (𝟙 Y') y le hy _).trans
      ((gm_pull (𝟙 Y') h y _ (le hy) _).trans (by rw [Category.id_comp]))).symm
  have hm : r z ∈ A'.U i ⊓ A'.U j := ⟨hi, hj⟩
  rw [e]
  exact (gm_res r z le hm _).trans (gm_pull r h z _ (le hm) _)

theorem exists_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF b
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec b Φ.D.q.left t ht)
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l y hy => Set.mem_iInter.2 fun _ => c.le l hy
  refine ⟨⟨fun l => (Φ.G.left.presheaf.map (homOfLE (le l)).op).hom (s.f (fun _ => c.idx l)),
    fun l l' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ l hl e => ?_⟩
  · refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l) hy.1 _)).trans
      ((sec_trans s (𝟙 _) y (le l hy.1) (le l' hy.2)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l') hy.2 _)))).symm))
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
    have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hy.1 hy.2
    have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hy.1, hy.2⟩ (Φ.N₀.g l l')
    refine Eq.trans ?_ (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).symm
    refine Eq.trans ?_ (map_pow _ _ _).symm
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rw [Category.assoc]
    rfl
  · refine (gs_res r z (le l) hl _).trans ?_
    rw [← sval_pullMulSec b Φ.D.q.left t ht r z hJ, ← hs Z r z J hJ]
    exact (sval_of s r z J (fun _ => c.idx l) (fun _ => e)).symm

end GlobalTheory.ZH.UFib
end
end
