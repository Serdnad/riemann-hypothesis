module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

theorem UpperTheory.V.Z.Kato.Sym.PT.isoEx :
    UpperTheory.V.Z.Kato.Sym.PT.IsoEx := by
  intro Ω _ _ _ ε X M
  let L := topL X M
  let L' : IntermediateField Ω X.K :=
    { L with algebraMap_mem' := fun c => algebraMap_mem_lev X _ c }
  let F : IntermediateField Ω X.K := IntermediateField.adjoin Ω {X.jK}
  have hFL : F ≤ L' :=
    IntermediateField.adjoin_simple_le_iff.mpr (jK_mem_lev X _)
  have hle : F.toSubfield ≤ L := fun x hx => hFL hx
  letI : Algebra F L := (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower F L X.K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic L X.K :=
    ⟨fun f => (X.alg_j f).tower_top L⟩
  haveI : IsAlgClosure L (Kb X) := IsAlgClosure.ofAlgebraic L X.K (Kb X)
  let e : topBar X M ≃ₐ[L] Kb X := IsAlgClosure.equiv L (topBar X M) (Kb X)
  refine ⟨e.toRingEquiv, fun f => ?_⟩
  change e (algebraMap L (topBar X M) f) = algebraMap X.K (Kb X) (f : X.K)
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply L X.K (Kb X) f
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

private lemma conj_toAdd {Γ : Type} [Group Γ] {m : ℕ} (x : Γ →* Multiplicative (ZMod m)) (s h : Γ) :
    (x (s * h * s⁻¹)).toAdd = (x h).toAdd := by
  have e : x (s * h * s⁻¹) = x h := by
    rw [map_mul, map_mul, map_inv, mul_comm (x s) (x h), mul_inv_cancel_right]
  rw [e]

private lemma mul_toAdd {Γ : Type} [Group Γ] {m : ℕ} (x : Γ →* Multiplicative (ZMod m)) (g h : Γ) :
    (x (g * h)).toAdd = (x g).toAdd + (x h).toAdd := by
  rw [map_mul, toAdd_mul]

theorem UpperTheory.V.Z.Kato.Sym.PT.edgeGeo :
    UpperTheory.V.Z.Kato.Sym.PT.EdgeGeo := by
  intro Γ _ m Δ x y η hc
  refine ⟨fun g hg h hh => ?_, fun σ hσ g hg h hh => ?_⟩
  · have ha : g * h * g⁻¹ ∈ Δ := Δ.mul_mem (Δ.mul_mem hg hh) (Δ.inv_mem hg)
    have e : g * h * g⁻¹ * g = g * h := by group
    have h1 := hc _ ha g hg
    have h2 := hc g hg h hh
    rw [e, conj_toAdd x] at h1
    simp only [GlobalTheory.KEdge.edge]
    linear_combination h2 - h1
  · have hg' := hσ g hg
    have hh' := hσ h hh
    have e : σ * (g * h) * σ⁻¹ = (σ * g * σ⁻¹) * (σ * h * σ⁻¹) := by group
    have h1 := hc _ hg' _ hh'
    have h2 := hc g hg h hh
    rw [conj_toAdd x, conj_toAdd y] at h1
    simp only [GlobalTheory.KEdge.edge, e, mul_toAdd x, mul_toAdd y]
    linear_combination h1 - h2
end

section

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem isIntegral_of_mem_overY (X : Tower Ω ε) (x : X.K) (h : ∀ W, X.OverY W → x ∈ W) :
    IsIntegral (Algebra.adjoin Ω {X.jK}) x := by
  by_contra hx
  obtain ⟨V, hRV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (K := X.K) (x := x) (R := (integralClosure (Algebra.adjoin Ω {X.jK}) X.K).toSubring)
    (fun hm => hx hm)
  apply hxV
  refine h V ⟨fun c => hRV ?_, hRV ?_⟩
  · change algebraMap Ω X.K c ∈ integralClosure (Algebra.adjoin Ω {X.jK}) X.K
    have : algebraMap Ω X.K c = algebraMap (Algebra.adjoin Ω {X.jK}) X.K (algebraMap Ω _ c) := rfl
    rw [this]
    exact isIntegral_algebraMap
  · change X.jK ∈ integralClosure (Algebra.adjoin Ω {X.jK}) X.K
    have : X.jK = algebraMap (Algebra.adjoin Ω {X.jK}) X.K ⟨X.jK, Algebra.subset_adjoin rfl⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap

theorem intU : IntU := by
  intro Ω _ _ _ ε X M u hu
  refine ⟨isIntegral_of_mem_overY X u fun W hW => ?_, isIntegral_of_mem_overY X u⁻¹ fun W hW => ?_⟩
  · exact (ValuationSubring.valuation_le_one_iff W u).1 (hu.2 W hW).le
  · refine (ValuationSubring.valuation_le_one_iff W u⁻¹).1 ?_
    rw [map_inv₀, hu.2 W hW, inv_one]

end UpperTheory.V.Z.Kato.Sym.PT

end
end

section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

private theorem unif_lc {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {f : G → A} (hf : IsLocallyConstant f) : ∀ᶠ h in nhds (1 : G), ∀ g : G, f (g * h) = f g := by
  choose V hVo hV1 hVm using fun g : G => exists_open_nhds_one_mul_subset
    (show {y : G | f (g * y) = f g} ∈ nhds (1 : G) from
      ((hf.isOpen_fiber (f g)).preimage (continuous_const_mul g)).mem_nhds (by simp))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : G => (fun x => g⁻¹ * x) ⁻¹' V g)
    (fun g => (hVo g).preimage (continuous_const_mul g⁻¹))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using hV1 x⟩)
  filter_upwards [(Filter.biInter_finset_mem t).2 (fun g _ => (hVo g).mem_nhds (hV1 g))] with h hh x
  obtain ⟨g, hg, hx⟩ : ∃ g ∈ t, g⁻¹ * x ∈ V g := by
    simpa using ht (Set.mem_univ x)
  have h1 : f (g * (g⁻¹ * x * h)) = f g := hVm g (Set.mul_mem_mul hx (Set.mem_iInter₂.1 hh g hg))
  have h2 : f (g * (g⁻¹ * x * 1)) = f g := hVm g (Set.mul_mem_mul hx (hV1 g))
  simp only [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h1 h2
  rw [h1, h2]

theorem UpperTheory.V.Z.Kato.Sym.PT.lcGeo :
    UpperTheory.V.Z.Kato.Sym.PT.LcGeo := by
  classical
  intro F K E _ _ _ _ _ _ _ _ A η hη
  have l : IsLocallyConstant (fun g : E ≃ₐ[K] E => η (AlgEquiv.restrictScalarsHom F g)) :=
    hη.comp_continuous
      (f := fun g : E ≃ₐ[K] E => (⟨AlgEquiv.restrictScalarsHom F g, TopSpec.res_mem_geo g⟩ : geo F K E))
      ((TopSpec.continuous_res (F := F) (K := K) (Ω := E)).subtype_mk _)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff K E _).1 (unif_lc l)
  let b := Module.finBasis K L
  refine ⟨Finset.univ.image fun i => (b i : E), fun g hg g' hg' hB => ?_⟩
  obtain ⟨g, rfl⟩ := TopSpec.exists_res hg
  obtain ⟨g', rfl⟩ := TopSpec.exists_res hg'
  have hlin : g.toLinearMap.comp L.val.toLinearMap = g'.toLinearMap.comp L.val.toLinearMap :=
    b.ext fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hmem : g⁻¹ * g' ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hz' : g z = g' z := LinearMap.congr_fun hlin ⟨z, hz⟩
    rw [AlgEquiv.mul_apply, ← hz']
    exact g.symm_apply_apply z
  have h := hsub hmem g
  simp only [mul_inv_cancel_left] at h
  exact h.symm
end
