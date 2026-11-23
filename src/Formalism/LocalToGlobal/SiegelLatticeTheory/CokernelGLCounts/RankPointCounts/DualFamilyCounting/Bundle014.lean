module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle019
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOfNormRepCountNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle013
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle005
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle007
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP

@[expose] public section

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem jK_conjO (z : 𝓞 K) : jK (conjO K z) = star (jK z) := rfl

theorem jK_star (z : 𝓞 K) : jK (star z) = star (jK z) := rfl

theorem star_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (hF : IsFixF K F) {r : K}
    (hr : r ∈ HU.SP K 𝔭) : star r ∈ HU.SP K 𝔭 := by
  obtain ⟨t, ht, z, hz⟩ := HU.mem_SP.1 hr
  refine HU.mem_SP.2 ⟨t, ht, conjO K z, ?_⟩
  rw [jK_conjO, hz, star_mul', star_jK_ι hF, mul_comm]

theorem extP_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) : extP K 𝔭 ^ k = (𝔭 ^ k).map ι := by
  rw [extP, Ideal.map_pow]

theorem exists_sub_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {z : 𝓞 K}
    (hz : haveI := h𝔭.isPrime; jK z / jK (ι d) ∈ HU.SP K 𝔭) (k : ℕ) :
    ∃ w : 𝓞 K, z - w * ι d ∈ extP K 𝔭 ^ k := by
  have := h𝔭.isPrime
  obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 hz
  obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht k
  refine ⟨ι u * w, ?_⟩
  have e : w * ι d = ι t * z := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_mul, map_mul, hw, mul_assoc, div_mul_cancel₀ _ (jK_ι_ne_zero hd)]
  have e2 : z - ι u * w * ι d = ι (1 - t * u) * z := by
    rw [mul_assoc, e, map_sub, map_one, map_mul]; ring
  rw [e2, extP_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

theorem div_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {x : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / jK (ι d) ∈ HU.SP K 𝔭 :=
  (div_mem_SP_iff h𝔭 hd _).2 (Ideal.pow_le_pow_right hk hx)

theorem div_mul_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d d' : 𝓞 F} (hd : d ≠ 0)
    (hd' : d' ≠ 0) {x : 𝓞 K} {k : ℕ} (hk : vF 𝔭 d + vF 𝔭 d' ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / (jK (ι d) * jK (ι d')) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  have hx' : x ∈ extP K 𝔭 ^ vF 𝔭 d * extP K 𝔭 ^ vF 𝔭 d' := by
    rw [← pow_add]; exact Ideal.pow_le_pow_right hk hx
  refine Submodule.mul_induction_on hx' (fun y hy y' hy' => ?_) (fun u v hu hv => ?_)
  · rw [map_mul, mul_div_mul_comm]
    exact mul_mem ((div_mem_SP_iff h𝔭 hd _).2 hy) ((div_mem_SP_iff h𝔭 hd' _).2 hy')
  · rw [map_add (f := _), add_div]; exact add_mem hu hv

theorem div_mem_SP_of_sub {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {z w : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (h : z - w * ι d ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK z / jK (ι d) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  have e : jK z / jK (ι d) = jK (z - w * ι d) / jK (ι d) + jK w := by
    rw [map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ (jK_ι_ne_zero hd)]; ring
  rw [e]
  exact add_mem (div_mem_SP_of_mem h𝔭 hd hk h) (HU.jK_mem_SP w)

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def NU (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (x : K) : Prop :=
  ∃ l : K, l ≠ 0 ∧ x * (l * star l) ∈ SP K 𝔭 ∧ (x * (l * star l))⁻¹ ∈ SP K 𝔭

variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]

theorem NU.of_unit {u : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) : NU 𝔭 u :=
  ⟨1, one_ne_zero, by simpa using h1, by simpa using h2⟩

theorem NU.mul {x y : K} (hx : NU 𝔭 x) (hy : NU 𝔭 y) : NU 𝔭 (x * y) := by
  obtain ⟨a, ha, ha1, ha2⟩ := hx
  obtain ⟨b, hb, hb1, hb2⟩ := hy
  have e : x * y * (a * b * star (a * b)) = (x * (a * star a)) * (y * (b * star b)) := by
    rw [star_mul']
    ring
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · rw [e]
    exact (SP K 𝔭).mul_mem ha1 hb1
  · rw [e, mul_inv]
    exact (SP K 𝔭).mul_mem ha2 hb2

theorem NU.inv {x : K} (hx : NU 𝔭 x) : NU 𝔭 x⁻¹ := by
  obtain ⟨a, ha, h1, h2⟩ := hx
  have hs : star a⁻¹ = (star a)⁻¹ := by
    first | exact star_inv₀ a | exact star_inv' a | simp
  have e : x⁻¹ * (a⁻¹ * star a⁻¹) = (x * (a * star a))⁻¹ := by
    rw [hs, mul_inv, mul_inv]
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · rw [e]
    exact h2
  · rw [e, inv_inv]
    exact h1

theorem NU.of_mul_left {x y : K} (hxy : NU 𝔭 (x * y)) (hy : NU 𝔭 y) (hy0 : y ≠ 0) : NU 𝔭 x := by
  have h := NU.mul hxy (NU.inv hy)
  rwa [mul_assoc, mul_inv_cancel₀ hy0, mul_one] at h

theorem NU.norm_mul {u z : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) (hz : z ≠ 0) :
    NU 𝔭 (star z * u * z) := by
  have hs : star z⁻¹ = (star z)⁻¹ := by
    first | exact star_inv₀ z | exact star_inv' z | simp
  have hsz : star z ≠ 0 := by
    first | exact star_ne_zero.2 hz | simpa using hz
  have e : star z * u * z * (z⁻¹ * star z⁻¹) = u := by
    rw [hs]
    calc star z * u * z * (z⁻¹ * (star z)⁻¹) = u * (z * z⁻¹) * (star z * (star z)⁻¹) := by ring
      _ = u := by rw [mul_inv_cancel₀ hz, mul_inv_cancel₀ hsz, mul_one, mul_one]
  refine ⟨z⁻¹, inv_ne_zero hz, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e]
    exact h2

theorem NU.prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, NU 𝔭 (f i)) :
    NU 𝔭 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (NU 𝔭) (fun _ _ ha hb => NU.mul ha hb)
    (NU.of_unit (SP K 𝔭).one_mem (by rw [inv_one]; exact (SP K 𝔭).one_mem)) hf

theorem NU.pair {A C : K} (hA : A ≠ 0) (hAs : star A = A) (h1 : C * A⁻¹ ∈ SP K 𝔭)
    (h2 : A * C⁻¹ ∈ SP K 𝔭) : NU 𝔭 (A * C) := by
  have hs : star A⁻¹ = (star A)⁻¹ := by
    first | exact star_inv₀ A | exact star_inv' A | simp
  have e : A * C * (A⁻¹ * star A⁻¹) = C * A⁻¹ := by
    rw [hs, hAs]
    calc A * C * (A⁻¹ * A⁻¹) = C * A⁻¹ * (A * A⁻¹) := by ring
      _ = C * A⁻¹ := by rw [mul_inv_cancel₀ hA, mul_one]
  refine ⟨A⁻¹, inv_ne_zero hA, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e, mul_inv, inv_inv, mul_comm]
    exact h2

section Vec

variable {V : Type} [AddCommGroup V] [Module K V]

theorem linInd_orth {ι : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (g : ι → V)
    (ho : ∀ s t, s ≠ t → h (g s) (g t) = 0) (hn : ∀ s, h (g s) (g s) ≠ 0) : LinearIndependent K g := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have key := congrArg (h (g i)) hs

  rw [map_sum, map_zero, Finset.sum_eq_single i] at key
  · rw [map_smul, smul_eq_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

end Vec

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem κι_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : κ (ι a) ≠ 0 := by
  intro h
  apply ha
  have h1 : ι a = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [h1, map_zero])

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

section Line

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit hK hF in
theorem h_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
    h (μ • x) (ν • y) = star μ * ν * h x y := by
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  ring

end Line

theorem exists_norm_congr_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ∉ 𝔭) {k : ℕ}
    (hk : 1 ≤ k) : ∃ α : 𝓞 K, conjO K α * α - ι c ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hcP : ι c ∉ P := fun h => hc (Ideal.mem_comap.2 h)
  have hN := IdealNormInequalities.one_lt_absNorm hP
  obtain ⟨h1, h2⟩ := localDensity K hK P hP 1 k le_rfl hk (ι c) (idealPowerSpanBounds.conjO_map hF c) hcP
  by_cases hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have h3 := h1 hc'
    have hs : 0 < Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hpos : (0 : ℝ) < (normRepCount K (P ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos hs _) ?_
      have : (0 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) := zpow_pos hs _
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hc']
    exact hα
  · have h3 := h2 hc'
    have hpos : (0 : ℝ) < (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) 1 (ι c) : ℝ) := by
      rw [h3]
      refine mul_pos (pow_pos (by linarith) _) ?_
      have : (Ideal.absNorm P : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
        rw [Nat.cast_one, zpow_neg_one]
        exact inv_lt_one_of_one_lt₀ hN
      linarith
    obtain ⟨α, hα⟩ := Cell.exists_of_normRepCount_ne_zero (by exact_mod_cast hpos.ne')
    refine ⟨α, ?_⟩
    rw [ThirdPropositionSlot.extP_split hK hF hP hc']
    exact hα

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.FamilyMeetLattice

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

theorem alg_eq {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (t : 𝓞 F) : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K t).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F K t)
    | simp

theorem family_meet_holds : FamMeet := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  classical
  obtain ⟨hbU, hspan, -, -, -⟩ := hba
  obtain ⟨hwW, hworth, hwc, hτ, ⟨s₀, hu⟩, -, -⟩ := hg
  have hπ0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    intro e0
    exact hu.notMem (by rw [show π = 0 from RingOfIntegers.ext e0]; exact Ideal.zero_mem _)
  set p := algebraMap F K (π : F) with hp
  set G := glueFam K 𝔭 b a π w τ with hG
  have hGl : ∀ i, G (Sum.inl i) = if vF 𝔭 (a i) = 0 then b i else
      ((p)⁻¹ ^ vF 𝔭 (a i)) • (b i + w (τ i)) := fun i => rfl
  have hGr : ∀ j, G (Sum.inr j) = w j := fun j => rfl
  have hUloc : locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
    Formalism.L2.SG.Pf.G7.locF_subspace U h𝔭.isPrime
  apply le_antisymm
  ·
    rintro x ⟨hx, hxU⟩
    rw [← hspan]
    obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).1 hx
    refine (LocF.mem_locF_iff h𝔭.isPrime _ x).2 ⟨t, ht, ?_⟩
    set y := algebraMap (𝓞 F) (𝓞 K) t • x with hy
    have hyU : y ∈ U := Submodule.smul_of_tower_mem U _ hxU
    obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hty
    let cf : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then algebraMap (𝓞 K) K (γ (Sum.inl i)) else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    let co : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then 0 else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    have hz : y - ∑ i, cf i • b i = ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j := by
      rw [← hγ, Fintype.sum_sum_type, add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [hGl, ← algebraMap_smul K (γ (Sum.inl i))]
        simp only [cf, co]
        split_ifs with he
        · rw [zero_smul, sub_self]
        · rw [smul_smul, smul_add]
          abel
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hGr, ← algebraMap_smul K (γ (Sum.inr j))]
    have hzW : ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j ∈ orthK h U :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hwW _))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hwW _))
    have hzU : y - ∑ i, cf i • b i ∈ U :=
      Submodule.sub_mem _ hyU (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbU i))
    have hz0 : y - ∑ i, cf i • b i = 0 :=
      (Submodule.disjoint_def.1 hUc.disjoint) _ hzU (hz ▸ hzW)
    have hint : ∀ i, vF 𝔭 (a i) ≠ 0 → ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = cf i := by
      intro i hi
      have h0 := congrArg (h (w (τ i))) (hz.symm.trans hz0)

      rw [map_zero, map_add (f := _), map_sum, map_sum] at h0
      simp only [LinearMap.map_smul, smul_eq_mul] at h0
      rw [Finset.sum_eq_single i, Finset.sum_eq_single (τ i)] at h0
      · have hc := hwc (τ i)
        rw [hc.1, ← add_mul] at h0
        have hc0 : algebraMap F K (c (τ i)) ≠ 0 := by rw [map_ne_zero]; exact hc.2
        have h1 := (mul_eq_zero.1 h0).resolve_right hc0
        refine ⟨-γ (Sum.inr (τ i)), ?_⟩
        simp only [cf, co, if_neg hi] at h1 ⊢
        rw [map_neg]
        linear_combination -h1
      · intro j _ hj
        rw [hworth _ _ (Ne.symm hj), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro i' _ hi'
        simp only [co]
        split_ifs with he
        · rw [zero_mul]
        · rw [hworth _ _ (fun e => hi' (hτ i' i he hi e.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [sub_eq_zero.1 hz0]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases he : vF 𝔭 (a i) = 0
    · have : cf i = algebraMap (𝓞 K) K (γ (Sum.inl i)) := if_pos he
      rw [this, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · obtain ⟨r, hr⟩ := hint i he
      rw [← hr, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  ·
    rw [← hspan]
    refine le_inf (LocF.locF_mono 𝔭 ?_) ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases he : vF 𝔭 (a i) = 0
      · have : G (Sum.inl i) = b i := by rw [hGl, if_pos he]
        exact Submodule.subset_span ⟨Sum.inl i, this⟩
      · have e1 : b i = algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i) • G (Sum.inl i) - G (Sum.inr (τ i)) := by
          rw [hGl, if_neg he, hGr, ← algebraMap_smul K, map_pow, alg_eq, smul_smul, ← mul_pow,
            mul_inv_cancel₀ hπ0, one_pow, one_smul, add_sub_cancel_right]
        rw [e1]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.subset_span ⟨_, rfl⟩)
    · calc locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ≤ locF 𝔭 (U.restrictScalars (𝓞 K)) :=
            LocF.locF_mono 𝔭 (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbU i))
        _ = U.restrictScalars (𝓞 K) := hUloc

end Formalism.L2.SG.Pf.FamilyMeetLattice
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluedFormOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem form_U_orth {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {u z : V} (hu : u ∈ U)
    (hz : z ∈ orthK h U) : h u z = 0 := by
  have hz' : z ∈ ⨅ w ∈ U, LinearMap.ker (h w) := hz
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hz'
  exact hz' u hu

theorem form_orth_U {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V} {u z : V}
    (hu : u ∈ U) (hz : z ∈ orthK h U) : h z u = 0 :=
  hs.eq_iff.1 (form_U_orth hu hz)

theorem glue_inl_inl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hbo : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hwW : ∀ j, w j ∈ orthK h U) (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0)
    (hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) {i i' : Fin n} (hii : i ≠ i') :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i')) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1 h2 h2
  · exact hbo _ _ hii
  · simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _)]
  · simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_orth_U hs (hbU i') (hwW _)]
  · have hτ' : τ i ≠ τ i' := fun e => hii (hτ i i' h1 h2 e)
    simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _),
      form_orth_U hs (hbU i') (hwW _), hwo _ _ hτ']

theorem glue_inl_w {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hwW : ∀ j, w j ∈ orthK h U)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) {i : Fin n} {j : Fin m}
    (hj : vF 𝔭 (a i) ≠ 0 → τ i ≠ j) :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (w j) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1
  · exact form_U_orth (hbU i) (hwW j)
  · simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, form_U_orth (hbU i) (hwW j), hwo _ _ (hj h1)]

end Formalism.L2.SG.Pf.GluedFormOrthogonality
end
end
