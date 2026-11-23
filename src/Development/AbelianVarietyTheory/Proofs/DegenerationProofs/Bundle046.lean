module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem exists_mul_pow_mem_O_of_isAffineOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ V, u ∈ M.O z) (hφ : ∀ z ∈ V, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ n : ℕ, ∀ z ∈ V, φ * u ^ n ∈ M.O z := by
  obtain ⟨g, rfl⟩ := (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 hu)
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : g = 0 := (basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h)
    exact hu0 (by rw [h0, ← M.res_apply V hne, map_zero])
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg (x := φ)).1 (mem_ringOn.2 fun z hz =>
    hφ z (M.Z.basicOpen_le g hz)
      ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2)
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
  exact ⟨n, fun z hz => h1 ▸ valF_mem_O hz a⟩


variable (M) in
theorem noetherianSpace_of_isNoetherianRing [IsNoetherianRing o] : TopologicalSpace.NoetherianSpace M.Z := by
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  have : AlgebraicGeometry.IsNoetherian M.Z := {}
  infer_instance

theorem exists_forall_mul_pow_mem_O [IsNoetherianRing o] (W : M.Z.Opens)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ W, u ∈ M.O z) (hφ : ∀ z ∈ W, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * u ^ C ∈ M.O z := by
  have := M.noetherianSpace_of_isNoetherianRing
  have hmono : ∀ z ∈ W, ∀ m n : ℕ, m ≤ n → φ * u ^ m ∈ M.O z → φ * u ^ n ∈ M.O z := by
    intro z hz m n hmn h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [pow_add, ← _root_.mul_assoc]
    exact mul_mem h (pow_mem (hu z hz) k)
  have hcov : (W : Set M.Z) ⊆ ⋃ n : ℕ, {z | φ * u ^ n ∈ M.O z} := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (U := W) (x := z) hz
    obtain ⟨n, hn⟩ := exists_mul_pow_mem_O_of_isAffineOpen hV ⟨z, hzV⟩ hu0 (fun w hw => hu w (hle hw))
      (fun w hw => hφ w (hle hw))
    exact Set.mem_iUnion.2 ⟨n, hn z hzV⟩
  obtain ⟨s, hs⟩ := (TopologicalSpace.NoetherianSpace.isCompact (W : Set M.Z)).elim_finite_subcover _
    (fun n => M.isOpen_setOf_mem_O _) hcov
  refine ⟨s.sup id, fun C hC z hz => ?_⟩
  obtain ⟨n, hn, h⟩ := Set.mem_iUnion₂.1 (hs hz)
  exact hmono z hz n C ((Finset.le_sup (f := id) hn).trans hC) h

theorem exists_forall_mul_prod_div_pow_mem_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o] (J : Type)
      (t : J → Ω) (W : M.Z.Opens) (j : J), (∀ z ∈ W, M.Div t j z) → ∀ (I : Finset J) (φ : Ω),
      (∀ z ∈ W, (∀ i ∈ I, M.Div t i z) → φ ∈ M.O z) → (∀ i ∈ I, t i ≠ 0) →
      ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * (∏ i ∈ I, t i / t j) ^ C ∈ M.O z := by
  intro o Ω _ _ _ M _ J t W j hj I φ hφ hI
  by_cases hW : ∃ z, z ∈ W
  swap
  · exact ⟨0, fun _ _ z hz => (hW ⟨z, hz⟩).elim⟩
  obtain ⟨z₀, hz₀⟩ := hW
  have hj0 : t j ≠ 0 := (hj z₀ hz₀).1
  have hu0 : (∏ i ∈ I, t i / t j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => div_ne_zero (hI i hi) hj0
  refine exists_forall_mul_pow_mem_O W hu0 (fun z hz => prod_mem fun i _ => (hj z hz).2 i) fun z hz hinv => ?_
  refine hφ z hz fun i hi => ((hj z hz).div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨div_ne_zero (hI i hi) hj0, ?_⟩)
  have hmem := mul_mem (prod_mem (S := M.O z) (t := I.erase i) fun k _ => (hj z hz).2 k) hinv
  have e : (∏ k ∈ I.erase i, t k / t j) * (∏ k ∈ I, t k / t j)⁻¹ = (t i / t j)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← _root_.mul_assoc, Finset.mul_prod_erase I (fun k => t k / t j) hi, mul_inv_cancel₀ hu0]
  exact e ▸ hmem

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_functionField_point (X : Scheme.{0}) [IsIntegral X] :
    ∃ (K : Type) (_ : Field K) (pt : Sp K ⟶ X), (∀ w, pt w = genericPoint X) ∧
      ∀ x : K, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x := by
  let pt : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  refine ⟨X.functionField, inferInstance, pt, fun w => ?_, fun x => ?_⟩
  · rw [Subsingleton.elim w (IsLocalRing.closedPoint X.functionField)]
    exact Scheme.fromSpecStalk_closedPoint
  · obtain ⟨W, hW, g, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) x
    obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hW
    have hle' : V ≤ W := hle
    let φ : Γ(X, V) ⟶ CommRingCat.of X.functionField := X.presheaf.germ V (genericPoint X) hz
    have e : pt = Spec.map φ ≫ hV.fromSpec := (hV.fromSpecStalk_eq_fromSpecStalk hz).symm
    refine ⟨V, (X.presheaf.map (homOfLE hle').op).hom g, ⟨_, hz⟩, ?_⟩
    rw [e, valF_eq_valR, valR_eq _ V (le_preimage_specMap_fromSpec hV φ), valMap_specMap_fromSpec]
    exact X.presheaf.germ_res_apply (homOfLE hle') _ hz g

theorem RatModel.exists_functionField_of_isDominant (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q] :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X),
      Set.range pt = {genericPoint X} ∧
      (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  obtain ⟨K, _, pt, hpt, honto⟩ := exists_functionField_point X
  have hq : q (genericPoint X) = genericPoint M.Z := by
    have h := (genericPoint_spec X).image q.continuous
    rw [Set.image_univ, q.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec M.Z)
  have hy : ∀ w, (pt ≫ q) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hpt, hq]
  have hs : ∀ w, (pt ≫ q) w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf (pt ≫ q) _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  letI : Algebra o K := (β.comp (algebraMap o Ω)).toAlgebra
  refine ⟨K, inferInstance, inferInstance, { β with commutes' := fun _ => rfl }, pt, ?_, honto, ?_⟩
  · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hpt (IsLocalRing.closedPoint K)⟩, by
      rintro _ ⟨w, rfl⟩
      exact hpt w⟩
  · obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
    have h1 := top_le_preimage_of_specializes hs hz
    have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
    refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
    exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  infer_instance

theorem flat_int_sections [CharZero Ω] (U : M.Z.Opens) : Module.Flat ℤ Γ(M.Z, U) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨n, hn⟩, ha⟩
  rw [Submodule.mem_bot]
  rcases (U : Set M.Z).eq_empty_or_nonempty with hU | hU
  · obtain rfl : U = ⊥ := SetLike.coe_injective hU
    exact Subsingleton.elim _ _
  · have h : n • M.res U hU a = 0 := by
      rw [← map_zsmul, show n • a = 0 from ha, map_zero]
    exact (map_eq_zero_iff _ (M.res_injective U hU)).1
      ((smul_eq_zero.1 h).resolve_left (nonZeroDivisors.ne_zero hn))

theorem flat_int [CharZero Ω] (π : M.Z ⟶ Sp ℤ) : Flat π := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : M.Z.affineOpens => U)
    (iSup_affineOpens_eq_top _) fun U => ?_
  have e : (π.appLE ⊤ U le_top).hom =
      (algebraMap ℤ Γ(M.Z, U)).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom := by
    have e' : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv ≫ π.appLE ⊤ U le_top).hom = algebraMap ℤ Γ(M.Z, U) :=
      RingHom.ext_int _ _
    rw [← e', ← CommRingCat.hom_comp, Iso.hom_inv_id_assoc]
  rw [e]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.bijective)
    (RingHom.flat_algebraMap_iff.2 (flat_int_sections M U))

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH.MinorModel

end GlobalTheory.ZH.MinorModel
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem comp_opens_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (U : X.Opens)
    (eta : Sp C ⟶ U.toScheme) (h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U) :
    eta ≫ U.toSpecΓ = Spec.map (valMap (eta ≫ U.ι) U h) := by
  have e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  rw [← appLE_valMap eta U.ι e (le_preimage_top eta) h, Scheme.Opens.toSpecΓ, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Spec.map_comp, valMap, Spec.map_comp]
  have h1 : (Sp C).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).hom := by
    rw [← Scheme.isoSpec_Spec_hom]; rfl
  have h2 : U.topIso.inv = U.ι.appLE U ⊤ e := by
    rw [Scheme.Opens.ι_appLE]; rfl
  rw [h1, h2]
  rfl

theorem exists_hom_spec_of_le_ringOn :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  intro o Ω _ _ _ M U R hU hR
  let ψ : R →+* Γ(M.Z, U) :=
    (M.sectionsEquiv U hU).symm.toRingHom.comp (Subalgebra.inclusion hR).toRingHom
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), fun eta he => ?_⟩
  have h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U := he ▸ M.top_le_preimage_pt hU
  rw [← Category.assoc, comp_opens_toSpecΓ_eq_valMap U eta h, ← Spec.map_comp]
  congr 1
  ext a
  have e : (M.sectionsEquiv U hU (ψ a) : Ω) = a :=
    congrArg Subtype.val ((M.sectionsEquiv U hU).apply_symm_apply _)
  rw [coe_sectionsEquiv, ← he, valF_eq_valR, valR_eq _ U h] at e
  exact e

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ZH

theorem mul_inv_apply_mem_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range B)) (hc : B * c = 1) (i j : J) :
    (b * c) i j ∈ R := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • B k = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : b = (Matrix.of fun i k => (n i k : Ω)) * B := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  rw [e, Matrix.mul_assoc, hc, Matrix.mul_one]
  exact (n i j).2

theorem exists_mul_eq_one_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range B) ≤ Submodule.span R (Set.range b)) (hc : c * B = 1) :
    ∃ d : Matrix J J Ω, b * d = 1 := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • b k = B i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : B = (Matrix.of fun i k => (n i k : Ω)) * b := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  refine ⟨c * Matrix.of fun i k => (n i k : Ω), mul_eq_one_comm.1 ?_⟩
  rw [Matrix.mul_assoc, ← e, hc]

theorem RatModel.exists_matrix_map_valF {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {J : Type} {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (n : Matrix J J Ω)
    (h : ∀ z ∈ U, ∀ i j, n i j ∈ M.O z) : ∃ m : Matrix J J Γ(M.Z, U), m.map (M.res U hU) = n := by
  choose m hm using fun i j =>
    (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => h z hz i j)
  refine ⟨Matrix.of m, ?_⟩
  ext i j
  exact (M.res_apply U hU _).trans (hm i j)

theorem exists_matrix_mul_eq_one_of_span_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] [DecidableEq J] (W W' : M.Z.Opens) (b B : Matrix J J Ω) (c : Matrix J J Γ(M.Z, W')), (∀ z ∈ W ⊓ W', Submodule.span (M.O z) (Set.range b) = Submodule.span (M.O z) (Set.range B)) → c.map (valF M.pt W') * B = 1 → ∃ m m' : Matrix J J Γ(M.Z, W ⊓ W'), m * m' = 1 ∧ (((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty → m.map (valF M.pt (W ⊓ W')) = b * c.map (valF M.pt W')) := by
  intro o Ω _ _ _ M J _ _ W W' b B c h hc
  by_cases hne : ((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · exact ⟨1, 1, Matrix.mul_one _, fun h' => absurd h' hne⟩
  obtain ⟨z₀, hz₀⟩ := id hne
  have hc' : B * c.map (valF M.pt W') = 1 := mul_eq_one_comm.1 hc
  obtain ⟨d, hd⟩ := exists_mul_eq_one_of_span_le (M.O z₀) (h z₀ hz₀).ge hc
  obtain ⟨m, hm⟩ := M.exists_matrix_map_valF hne (b * c.map (valF M.pt W')) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).le hc'
  obtain ⟨m', hm'⟩ := M.exists_matrix_map_valF hne (B * d) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).ge hd
  refine ⟨m, m', ?_, fun _ => ?_⟩
  · apply Matrix.map_injective (M.res_injective _ hne)
    dsimp only
    rw [Matrix.map_mul, hm, hm', Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ B, hc, Matrix.one_mul, hd]
  · rw [← hm]
    ext i j
    exact (M.res_apply _ hne _).symm

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem hom_ext_of_isOpenImmersion {W : Scheme.{0}} (q : W ⟶ M'.Z) [IsOpenImmersion q] {p : Sp Ω' ⟶ W}
    (hp : p ≫ q = M'.pt) {g h : W ⟶ M.Z} (hg : p ≫ g = spMap φ.toRingHom ≫ M.pt)
    (hh : p ≫ h = spMap φ.toRingHom ≫ M.pt) : g = h := by
  have := M.sep
  have : IsReduced W := isReduced_of_isOpenImmersion q
  have : IsDominant p := by
    refine ⟨q.isOpenEmbedding.isInducing.dense_iff.2 fun w => ?_⟩
    have e : q '' Set.range p = Set.range M'.pt := by
      rw [← hp, ← Set.range_comp]
      rfl
    rw [e]
    exact M'.pt.denseRange _
  refine ext_of_isDominant_of_isSeparated M.s (ext_of_isDominant p ?_) p (hg.trans hh.symm)
  rw [← Category.assoc, hg, ← Category.assoc, hh]

theorem exists_hom_of_map_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) (hUne : (U : Set M.Z).Nonempty)
    {V : M'.Z.Opens} (hVne : (V : Set M'.Z).Nonempty) (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) :
    ∃ g : Spec Γ(M'.Z, V) ⟶ M.Z,
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt hVne)) ≫ g = spMap φ.toRingHom ≫ M.pt := by
  let χ : M.ringOn U →+* M'.ringOn V :=
    (φ.toRingHom.comp (M.ringOn U).val.toRingHom).codRestrict (M'.ringOn V) fun x => h x x.2
  let ψ : Γ(M.Z, U) →+* Γ(M'.Z, V) :=
    (M'.sectionsEquiv V hVne).symm.toRingHom.comp (χ.comp (M.sectionsEquiv U hUne).toRingHom)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  conv_rhs => rw [← specMap_valMap_fromSpec hU M.pt (M.top_le_preimage_pt hUne)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  have e : (M'.sectionsEquiv V hVne (ψ a) : Ω') = φ (M.sectionsEquiv U hUne a) :=
    congrArg Subtype.val ((M'.sectionsEquiv V hVne).apply_symm_apply _)
  exact e

theorem exists_isHom_of_local (h : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z ∈ V ∧ IsAffineOpen U ∧
    (U : Set M.Z).Nonempty ∧ ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) : ∃ f, M.IsHom M' φ f := by
  have h' : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (_ : IsAffineOpen V) (hz : z ∈ V) (g : Spec Γ(M'.Z, V) ⟶ M.Z),
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt ⟨z, hz⟩)) ≫ g = spMap φ.toRingHom ≫ M.pt := fun z => by
    obtain ⟨V, U, hz, hU, hne, H⟩ := h z
    obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    exact ⟨W, hW, hzW, exists_hom_of_map_ringOn hU hne ⟨z, hzW⟩ fun x hx => ringOn_anti hle (H x hx)⟩
  choose V hV hz g hg using h'
  have hp := fun z => specMap_valMap_fromSpec (hV z) M'.pt (M'.top_le_preimage_pt ⟨z, hz z⟩)
  let 𝒰 : M'.Z.OpenCover := Scheme.Cover.mkOfCovers M'.Z (fun z => Spec Γ(M'.Z, V z)) (fun z => (hV z).fromSpec)
    fun z => by
      have : z ∈ Set.range (hV z).fromSpec := (hV z).range_fromSpec ▸ hz z
      exact ⟨z, this⟩
  have hc : ∀ z w, pullback.fst (hV z).fromSpec (hV w).fromSpec ≫ g z =
      pullback.snd (hV z).fromSpec (hV w).fromSpec ≫ g w := fun z w =>
    hom_ext_of_isOpenImmersion (φ := φ) (pullback.fst _ _ ≫ (hV z).fromSpec)
      (p := pullback.lift _ _ ((hp z).trans (hp w).symm))
      (by rw [pullback.lift_fst_assoc, hp]) (by rw [pullback.lift_fst_assoc, hg])
      (by rw [pullback.lift_snd_assoc, hg])
  refine ⟨𝒰.glueMorphisms g hc, ?_⟩
  have e : (hV (genericPoint M'.Z)).fromSpec ≫ 𝒰.glueMorphisms g hc = g _ := 𝒰.ι_glueMorphisms g hc _
  unfold IsHom
  rw [← hg (genericPoint M'.Z), ← e, ← Category.assoc, hp]

theorem Div.map_mem_O_of_mem_adjoin {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) {x : Ω} (hx : x ∈ Algebra.adjoin o (Set.range fun j => t j / t i)) :
    φ x ∈ M'.O z := by
  refine (Algebra.adjoin_le ?_ : _ ≤ (M'.O z).comap φ) hx
  rintro _ ⟨j, rfl⟩
  simpa using h.2 j

theorem Div.map_mem_O_of_isIntegral {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) [IsIntegrallyClosed (M'.O z)] {x : Ω}
    (hx : IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) : φ x ∈ M'.O z := by
  let χ : Algebra.adjoin o (Set.range fun j => t j / t i) →+* M'.O z :=
    (φ.toRingHom.comp (Subalgebra.val _).toRingHom).codRestrict (M'.O z) fun y => h.map_mem_O_of_mem_adjoin y.2
  have hi : IsIntegral (M'.O z) (φ x) := hx.map_of_comp_eq χ φ.toRingHom (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact hy ▸ y.2

theorem IsCl.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsCl t) (hd : M'.HasDiv fun j => φ (t j)) :
    ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_mem_adjoin hw (hR ▸ hx)⟩

theorem IsNm.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsNm t) (hd : M'.HasDiv fun j => φ (t j))
    (hn : ∀ z, IsIntegrallyClosed (M'.O z)) : ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_isIntegral hw ((hR x).1 hx)⟩

end GlobalTheory.ZH.RatModel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.sameCoords_of_germs_common_unit : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (H : LB X) (H' : LB Y), H'.IsLB → ∀ (J : Type) (F : J → H.Sec) (σ : J → H'.Sec) (x : Sp k ⟶ X) (y : Sp k ⟶ Y), (∀ (z : Sp k) (l : H.ι) (l' : H'.ι), x z ∈ H.U l → y z ∈ H'.U l' → ∃ u : ((Sp k).presheaf.stalk z)ˣ, ∀ i, gs x z (H.U l) ((F i).f l) = u.val * gs y z (H'.U l') ((σ i).f l')) → ∀ v : J → k, GlobalTheory.ZH.Crd H F x v → GlobalTheory.ZH.Crd H' σ y v := by
  first | exact @GlobalTheory.ZH.UFib.crd_of_germs_unit | exact GlobalTheory.ZH.UFib.crd_of_germs_unit | (intros; apply GlobalTheory.ZH.UFib.crd_of_germs_unit <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.summable_vt_of_int : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) := by
  first | exact @GlobalTheory.Ex.summable_vt_QT | exact GlobalTheory.Ex.summable_vt_QT | (intros; apply GlobalTheory.Ex.summable_vt_QT <;> assumption)
end
