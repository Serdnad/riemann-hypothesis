module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

section

namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing

noncomputable section

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
  {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {B : Π i, S i}

theorem continuous_unitsEquiv_symm :
    Continuous (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)).symm := by
  rw [Units.continuous_iff]
  constructor
  · exact _root_.RestrictedProduct.mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id
      (A₁ := fun i ↦ ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))
      (A₂ := fun i ↦ (B i : Set (R i)))
      (fun i (u : (R i)ˣ) ↦ (u : R i)) (.of_forall fun _ _ hu ↦ hu.1)
      (fun _ ↦ Units.continuous_val)
  · exact _root_.RestrictedProduct.mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id
      (A₁ := fun i ↦ ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))
      (A₂ := fun i ↦ (B i : Set (R i)))
      (fun i (u : (R i)ˣ) ↦ ((u⁻¹ : (R i)ˣ) : R i)) (.of_forall fun _ _ hu ↦ hu.2)
      (fun _ ↦ Units.continuous_coe_inv)

theorem continuous_unitsEquiv (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    Continuous (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  set T : Set ι :=
    {i | _root_.RestrictedProduct.unitsEquiv R x i ∈ (Submonoid.ofClass (B i)).units} with hTdef
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 (_root_.RestrictedProduct.unitsEquiv R x).2
  let U : Set (Πʳ i, [R i, B i])ˣ :=
    {y | ∀ i ∈ T, (y : Πʳ i, [R i, B i]) i ∈ B i ∧
      ((y⁻¹ : (Πʳ i, [R i, B i])ˣ) : Πʳ i, [R i, B i]) i ∈ B i}
  have hUo : IsOpen U := by
    have h1 := _root_.RestrictedProduct.isOpen_forall_imp_mem hBopen (p := (· ∈ T))
    have h2 := (h1.preimage Units.continuous_val).inter (h1.preimage Units.continuous_coe_inv)
    convert h2 using 1
    ext y
    simp only [U, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, ← forall_and]
    exact forall_congr' fun i ↦ ⟨fun h hi ↦ h hi, fun h hi ↦ h hi⟩
  have hxU : x ∈ U := fun i hi ↦ hi
  let G : U → Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T] :=
    fun y ↦ ⟨fun i ↦ _root_.RestrictedProduct.unitsEquiv R y.1 i,
      eventually_principal.2 fun i hi ↦ y.2 i hi⟩
  have hG : Continuous G := by
    rw [_root_.RestrictedProduct.continuous_rng_of_principal]
    refine continuous_pi fun i ↦ ?_
    exact (Units.continuous_map (f := _root_.RestrictedProduct.evalMonoidHom R i)
      (_root_.RestrictedProduct.continuous_eval i)).comp continuous_subtype_val
  have hFU : ContinuousOn (_root_.RestrictedProduct.unitsEquiv R (B := B) (𝓕 := cofinite)) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (_root_.RestrictedProduct.continuous_inclusion hT).comp hG
  exact hFU.continuousAt (hUo.mem_nhds hxU)

def continuousUnitsEquiv (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    (Πʳ i, [R i, B i])ˣ ≃ₜ* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units] where
  toMulEquiv := _root_.RestrictedProduct.unitsEquiv R
  continuous_toFun := continuous_unitsEquiv hBopen
  continuous_invFun := continuous_unitsEquiv_symm

end RestrictedProduct

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

theorem isOpen_units_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion K))

def finiteUnitsEquiv :
    (FiniteAdeleRing (𝓞 K) K)ˣ ≃ₜ* Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  RestrictedProduct.continuousUnitsEquiv (R := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (B := fun v ↦ v.adicCompletionIntegers K)
    (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion K))

def prodRestrictedEquiv :
    𝔸[K]ˣ ≃ₜ* (InfiniteAdeleRing K)ˣ × Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).trans
    { toMulEquiv := MulEquiv.prodCongr (MulEquiv.refl _) (finiteUnitsEquiv K).toMulEquiv
      continuous_toFun :=
        continuous_fst.prodMk ((finiteUnitsEquiv K).continuous.comp continuous_snd)
      continuous_invFun :=
        continuous_fst.prodMk ((finiteUnitsEquiv K).symm.continuous.comp continuous_snd) }

@[simp]
theorem prodRestrictedEquiv_apply_fst (x : 𝔸[K]ˣ) :
    ((prodRestrictedEquiv K x).1 : InfiniteAdeleRing K) = (x : 𝔸[K]).1 :=
  rfl

@[simp]
theorem prodRestrictedEquiv_apply_snd (x : 𝔸[K]ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((prodRestrictedEquiv K x).2 v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : 𝔸[K]).2 v :=
  rfl

end IdeleGroup

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

theorem norm_natCast_adicCompletion_eq_one {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hv : (n : 𝓞 K) ∉ v.asIdeal) : ‖(n : v.adicCompletion K)‖ = 1 := by
  have h := (FinitePlace.norm_eq_one_iff_notMem (K := K) (v := v) (n : 𝓞 K)).2 hv
  rwa [map_natCast, map_natCast] at h

theorem finprod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(n : v.adicCompletion K)‖) *
      (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := FinitePlace.prod_eq_inv_abs_norm hn'
  simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    FinitePlace.equivHeightOneSpectrum_symm_apply, map_natCast] at h
  rw [h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  have hpos : (0 : ℝ) < (n : ℝ) ^ Module.finrank ℚ K := by positivity
  push_cast
  rw [abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

theorem prod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) * (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  rw [← finprod_eq_prod_of_mulSupport_subset]
  · exact finprod_norm_natCast_adicCompletion_mul hn
  · intro v hv
    by_contra h
    exact hv (norm_natCast_adicCompletion_eq_one fun h' ↦ h (hS v h'))

theorem prod_norm_natCast_infinitePlaceCompletion_pow_mult (n : ℕ) :
    ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ Module.finrank ℚ K := by
  have h := InfinitePlace.prod_eq_abs_norm (n : K)
  have hw : ∀ w : InfinitePlace K, ‖(n : w.Completion)‖ = w (n : K) := fun w ↦ by
    rw [← map_natCast (algebraMap K w.Completion) n, AbsoluteValue.Completion.algebraMap_def,
      AbsoluteValue.Completion.norm_coe, WithAbs.algebraMap_right_apply,
      WithAbs.ofAbs_toAbs, Algebra.algebraMap_self_apply, ← InfinitePlace.coe_apply]
  simp_rw [hw, h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  push_cast
  exact abs_of_nonneg (by positivity)

theorem prod_norm_natCast_mul_prod_infinitePlace {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
      ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = 1 := by
  rw [prod_norm_natCast_infinitePlaceCompletion_pow_mult]
  exact prod_norm_natCast_adicCompletion_mul hn S hS

end GroundTheory.Global
end
