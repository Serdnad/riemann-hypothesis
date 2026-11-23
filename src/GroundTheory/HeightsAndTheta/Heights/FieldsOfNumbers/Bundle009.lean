module

import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Tactic.Continuity
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.Filter.AtTopBot.Map
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

namespace Relabel

section Eventual

variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

def precompOrderIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      have := h (e.symm k)
      simpa using this
    · intro h k
      exact h (e k)

theorem eventualValue_congr {K K' : Type*} {f : (K → ℤ) → ℤ} {g : (K' → ℤ) → ℤ}
    (h : ∀ c, (∀ᶠ m in atTop, f m = c) ↔ ∀ᶠ m in atTop, g m = c) :
    eventualValue f = eventualValue g := by
  unfold eventualValue
  by_cases hf : ∃ c, ∀ᶠ m in atTop, f m = c
  · have hg : ∃ c, ∀ᶠ m in atTop, g m = c := hf.imp fun c hc => (h c).1 hc
    rw [dite_eq_left hf, dite_eq_left hg]
    have h1 := (h _).1 hf.choose_spec
    have h2 := hg.choose_spec
    obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
    exact hm1.symm.trans hm2
  · have hg : ¬ ∃ c, ∀ᶠ m in atTop, g m = c := fun ⟨c, hc⟩ => hf ⟨c, (h c).2 hc⟩
    rw [dite_eq_right hf, dite_eq_right hg]

theorem eventualValue_precomp (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  refine eventualValue_congr fun c => ?_
  rw [← (precompOrderIso e).map_atTop, Filter.eventually_map]
  rfl

theorem mixedDiff_precomp {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  apply _root_.GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum.mixedDiff_comp <;> assumption

end Eventual

section Rename

variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]


include hφ in
theorem weight_mapDomain (d : (Σ k, ι₁ k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι₂) (Finsupp.mapDomain φ d) =
      Finsupp.weight (blockWeight ι₁) d ∘ e.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
    rfl
  | single v c =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hφ, Pi.smul_apply, Function.comp_apply, Pi.single_apply,
      Equiv.symm_apply_eq]


include hφ in
theorem gradedPiece_map_rename (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    gradedPiece (I.map (renameEquiv F φ)) d =
      (gradedPiece I (d ∘ e)).map
        ((Ideal.quotientEquivAlg I (I.map (renameEquiv F φ)) (renameEquiv F φ) (Ideal.map_coe _ _).symm).toLinearEquiv :
          (MRing ι₁ F ⧸ I) →ₗ[F] MRing ι₂ F ⧸ I.map (renameEquiv F φ)) := by
  rw [gradedPiece_eq_span, gradedPiece_eq_span, Submodule.map_span, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearMap_apply, Ideal.quotientEquivAlg_mk, renameEquiv_apply, rename_monomial]
  constructor
  · rintro ⟨d₂, hd₂, rfl⟩
    refine ⟨Finsupp.mapDomain φ.symm d₂, ?_, ?_⟩
    · have h := weight_mapDomain e φ hφ (Finsupp.mapDomain φ.symm d₂)
      rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id, hd₂] at h
      funext k
      have := congrFun h (e k)
      simpa using this.symm
    · rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  · rintro ⟨d₁, hd₁, rfl⟩
    refine ⟨Finsupp.mapDomain φ d₁, ?_, rfl⟩
    rw [weight_mapDomain e φ hφ, hd₁]
    funext k
    simp


include hφ in
theorem finrank_gradedPiece_map_rename (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    Module.finrank F (gradedPiece (I.map (renameEquiv F φ)) d) =
      Module.finrank F (gradedPiece I (d ∘ e)) := by
  rw [gradedPiece_map_rename e φ hφ, LinearEquiv.finrank_map_eq]


include hφ in
theorem hilbFn_map_rename (I : Ideal (MRing ι₁ F)) (m : K₂ → ℤ) :
    hilbFn (I.map (renameEquiv F φ)) m = hilbFn I (m ∘ e) := by
  unfold hilbFn
  have hpos : (∀ k, 0 ≤ m k) ↔ ∀ k, 0 ≤ (m ∘ e) k :=
    ⟨fun h k => h (e k), fun h k => by simpa using h (e.symm k)⟩
  by_cases h : ∀ k, 0 ≤ m k
  · rw [if_pos h, if_pos (hpos.1 h)]
    exact congrArg _ (finrank_gradedPiece_map_rename e φ hφ I (fun k => (m k).toNat))
  · rw [if_neg h, if_neg (mt hpos.2 h)]


include hφ in
theorem intNum_map_rename (I : Ideal (MRing ι₁ F)) {n : ℕ} (bs : Fin n → K₂ → ℤ) :
    intNum F (I.map (renameEquiv F φ)) bs = intNum F I (fun i => bs i ∘ e) := by
  unfold intNum
  have h : hilbFn (I.map (renameEquiv F φ)) = fun m => hilbFn I (m ∘ e) :=
    funext (hilbFn_map_rename e φ hφ I)
  rw [h, mixedDiff_precomp, eventualValue_precomp]

end Rename

end Relabel

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleSupport.proof : DivCycleSupport.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hdim c f hf hfP W hW
  have h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by rw [divCycle, dite_eq_right h])
  obtain ⟨hmin, hrel⟩ := h
  have hWh : IsMultiHomogIdeal W := (Bridge.isMultiHomogIdeal_iff W).mpr
    (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
      ((Bridge.isMultiHomogIdeal_iff P).mp hP.multiHomog) ((Bridge.isMultiHomog_iff f c).mp hf) hmin)
  refine ⟨⟨hmin.1.1, hWh, hrel⟩, ?_⟩
  have := hP.isPrime
  have hPd : ringKrullDim (MRing ι F ⧸ P) = ((Fintype.card K + n + 1 : ℕ) : WithBot ℕ∞) := by
    apply relDim_map_injective (K := K)
    change relDim P = _
    rw [hdim]
    show (((n + 1 : ℕ) : ℤ) : WithBot (WithTop ℤ)) =
      ((((Fintype.card K + n + 1 : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ))
    congr 1
    push_cast
    ring
  have key : ringKrullDim (MRing ι F ⧸ W) + 1 = ringKrullDim (MRing ι F ⧸ P) :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_quot_minimal_add_one hfP hmin (fun h => by
      rw [hPd] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  rw [hPd] at key
  have hWd := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  rw [relDim_of_ringKrullDim_eq W _ hWd]
  show ((((Fintype.card K + n : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) =
    (((n : ℕ) : ℤ) : WithBot (WithTop ℤ))
  congr 1
  push_cast
  ring

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section Loc

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    Subalgebra F (FractionRing (MRing ι F ⧸ P)) :=
  Algebra.adjoin F {x | ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
    g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}

theorem div_mem_degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F)))
    {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) (hgP : g ∉ P)
    (hg𝒲 : ∀ W ∈ 𝒲, g ∉ W) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ degZeroLoc P 𝒲 :=
  Algebra.subset_adjoin ⟨b, f, g, hf, hg, hgP, hg𝒲, rfl⟩

end Loc

section Fibre

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

def fibrePrimes (P' : Ideal (MRing ι' F)) (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Set (Ideal (MRing ι' F)) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ contractPrime j W' = W}

theorem map_degZeroLoc_le (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    (degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P') ≤
      degZeroLoc P' (fibrePrimes j P' W) := by
  unfold degZeroLoc
  rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_, ?_⟩
  · rintro W' ⟨-, -, hc⟩ hgW'
    apply hgW W (Set.mem_singleton W)
    rw [← hc]
    exact hgW'
  · rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]

def degZeroLocContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    degZeroLoc (contractPrime j P') {W} →ₐ[F] degZeroLoc P' (fibrePrimes j P' W) :=
  ((contractFracMap j P').comp (degZeroLoc (contractPrime j P') {W}).val).codRestrict _
    (fun x => map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩))

instance degZeroLoc.algebraContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Algebra (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) :=
  (degZeroLocContract j P' W).toRingHom.toAlgebra

theorem degZeroLoc.algebraMap_contract_coe (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (x : degZeroLoc (contractPrime j P') {W}) :
    ((algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) x :
      degZeroLoc P' (fibrePrimes j P' W)) : FractionRing (MRing ι' F ⧸ P')) =
      contractFracMap j P' x :=
  rfl

end Fibre

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
