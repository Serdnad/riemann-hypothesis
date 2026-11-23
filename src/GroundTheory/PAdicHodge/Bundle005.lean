module

public import GroundTheory.PAdicHodge.Bundle003
public import GroundTheory.PAdicHodge.NormalizedTraceTower
public import GroundTheory.PAdicHodge.SenTateCharUnits
public import GroundTheory.PAdicHodge.NormalizedTrace
public import Mathlib.FieldTheory.KrullTopology
public import GroundTheory.PAdicHodge.AxLemma
public import GroundTheory.PAdicHodge.NormalizedTraceClosure
public import GroundTheory.PAdicHodge.CyclotomicTower
import GroundTheory.PAdicHodge.Bundle001
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

open WittVector Filter Topology

namespace GroundTheory.PAdicHodge

section Coordinates

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

variable [CharP R p]

end Coordinates

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]




theorem isAdicComplete_p : IsAdicComplete (Ideal.span {(p : AInf K p)}) (AInf K p) :=
  inferInstance


end AInf

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Module Set

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

def tateTrace (n : ℕ) : PadicAlgCl p → PadicAlgCl p := normTrace (cyclotomicLayer K n)

theorem tateTrace_add (n : ℕ) (y z : PadicAlgCl p) :
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  normTrace_add _ y z

theorem tateTrace_mem (n : ℕ) (y : PadicAlgCl p) : tateTrace K n y ∈ cyclotomicLayer K n :=
  normTrace_mem _ y

theorem tateTrace_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTrace K n a = a :=
  normTrace_of_mem _ ha

theorem tateTrace_mul_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n)
    (y : PadicAlgCl p) : tateTrace K n (a * y) = a * tateTrace K n y :=
  normTrace_mul_of_mem _ ha y

theorem tateTrace_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    tateTrace K n (σ y) = σ (tateTrace K n y) :=
  normTrace_cyclotomicLayer_gal K σ n y

theorem tateTrace_tateTrace_of_le {n n' : ℕ} (h : n ≤ n') (y : PadicAlgCl p) :
    tateTrace K n (tateTrace K n' y) = tateTrace K n y :=
  normTrace_normTrace_of_le (cyclotomicLayer_mono K h) y

theorem exists_norm_tateTrace_le_of_stableIndex_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, stableIndex K ≤ n → ∀ x ∈ cyclotomicLimit K,
      ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  refine ⟨p * ∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro n hn x hx
  obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hx
  have hm' : x ∈ cyclotomicLayer K (max m n) := cyclotomicLayer_mono K (le_max_left m n) hm
  refine norm_normTrace_cyclotomicLayer_le K (Nat.cast_nonneg p) ?_ hn (le_max_right m n) hm'
  intro n' m' hn' hnm' y hy
  exact norm_normTrace_cycl_le
    (le_trans (by norm_num) ((two_le_stableIndex K).trans hn')) hnm' hy

theorem exists_norm_tateTrace_le_on_layer (n N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ cyclotomicLayer K N, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  let S : Submodule ℚ_[p] (PadicAlgCl p) := (cyclotomicLayer K N).toSubalgebra.toSubmodule
  haveI : FiniteDimensional ℚ_[p] S :=
    inferInstanceAs (FiniteDimensional ℚ_[p] (cyclotomicLayer K N))
  let f : S →ₗ[ℚ_[p]] PadicAlgCl p :=
    ((normTraceₗ (cyclotomicLayer K n)).restrictScalars ℚ_[p]).comp S.subtype
  let f' := LinearMap.toContinuousLinearMap f
  refine ⟨‖f'‖, ContinuousLinearMap.opNorm_nonneg f', fun x hx => ?_⟩
  have := f'.le_opNorm ⟨x, hx⟩
  exact this

theorem exists_norm_tateTrace_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, ∀ x ∈ cyclotomicLimit K, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_tateTrace_le_of_stableIndex_le K
  choose c' hc'0 hc' using fun n => exists_norm_tateTrace_le_on_layer K n (stableIndex K)
  refine ⟨c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n), by
    have : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
    positivity, ?_⟩
  intro n x hx
  have hs : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
  by_cases hn : stableIndex K ≤ n
  · calc ‖tateTrace K n x‖ ≤ c * ‖x‖ := hc n hn x hx
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        nlinarith [mul_nonneg (mul_nonneg hc0 hs) (norm_nonneg x)]
  · push_neg at hn
    have hle : c' n ≤ ∑ n ∈ Finset.range (stableIndex K), c' n :=
      Finset.single_le_sum (fun n _ => hc'0 n) (Finset.mem_range.2 hn)
    rw [← tateTrace_tateTrace_of_le K hn.le x]
    calc ‖tateTrace K n (tateTrace K (stableIndex K) x)‖
        ≤ c' n * ‖tateTrace K (stableIndex K) x‖ := hc' n _ (tateTrace_mem K _ x)
      _ ≤ c' n * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hc _ le_rfl x hx) (hc'0 n)
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        have := norm_nonneg x
        nlinarith [mul_nonneg hc0 this]

def tateBound : ℝ := Classical.choose (exists_norm_tateTrace_le K)

theorem tateBound_nonneg : 0 ≤ tateBound K := (Classical.choose_spec (exists_norm_tateTrace_le K)).1

theorem norm_tateTrace_le (n : ℕ) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    ‖tateTrace K n x‖ ≤ tateBound K * ‖x‖ :=
  (Classical.choose_spec (exists_norm_tateTrace_le K)).2 n x hx

section Completion

def cyclotomicCompletion : Set ℂ_[p] := closureInCp (cyclotomicLimit K)

def tateTraceHat (n : ℕ) : ℂ_[p] → ℂ_[p] := extendToClosure (cyclotomicLimit K) (tateTrace K n)

variable {K}

theorem tateTrace_add_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K, ∀ z ∈ cyclotomicLimit K,
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  fun y _ z _ => tateTrace_add K n y z

theorem norm_tateTrace_le_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ :=
  fun _ hy => norm_tateTrace_le K n hy

theorem norm_tateTraceHat_le (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    ‖tateTraceHat K n x‖ ≤ tateBound K * ‖x‖ :=
  norm_extendToClosure_le (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx

theorem tateTraceHat_add (n : ℕ) {x x' : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K)
    (hx' : x' ∈ cyclotomicCompletion K) :
    tateTraceHat K n (x + x') = tateTraceHat K n x + tateTraceHat K n x' :=
  (extendToClosure_add (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx hx').2

theorem tateTraceHat_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n x ∈
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (cyclotomicLayer K n : Set (PadicAlgCl p)) :=
  extendToClosure_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (fun y _ => tateTrace_mem K n y) hx

theorem tateTraceHat_coe_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a :=
  extendToClosure_coe_of_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha => tateTrace_of_mem K ha) ha

theorem tateTraceHat_mul {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x :=
  extendToClosure_mul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha y _ => tateTrace_mul_of_mem K ha y) ha hx

theorem gal_mem_cyclotomicLimit (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLimit K) : σ y ∈ cyclotomicLimit K :=
  map_mem_cyclotomicLimit K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) hy

theorem smul_mem_cyclotomicCompletion (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K :=
  smul_mem_closureInCp σ (fun _ hy => gal_mem_cyclotomicLimit σ hy) hx

theorem tateTraceHat_smul (n : ℕ) (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : tateTraceHat K n (σ • x) = σ • tateTraceHat K n x :=
  extendToClosure_smul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) σ
    (fun _ hy => gal_mem_cyclotomicLimit σ hy) (fun y _ => tateTrace_gal K σ n y) hx

end Completion

section Gamma

variable {K}

end Gamma

end

end GroundTheory.PAdicHodge
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open IntermediateField

variable {p : ℕ} [hp : Fact p.Prime]

def inertiaGal (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup Gal(PadicAlgCl p/K) where
  carrier := {σ | ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {σ τ} hσ hτ y hy => by
    have hτy : ‖τ y‖ ≤ 1 := by rwa [norm_gal_apply]
    have e : (σ * τ) y - y = (σ (τ y) - τ y) + (τ y - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt ((PadicAlgCl.isNonarchimedean p) _ _) (max_lt (hσ _ hτy) (hτ y hy))
  inv_mem' := fun {σ} hσ y hy => by
    have e : σ (σ⁻¹ y - y) = -(σ y - y) := by
      rw [map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]; ring
    rw [← norm_gal_apply σ, e, norm_neg]
    exact hσ y hy

theorem mem_inertiaGal {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {σ : Gal(PadicAlgCl p/K)} :
    σ ∈ inertiaGal K ↔ ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1 := Iff.rfl

namespace SenTateChar

open SenTateChar

theorem exists_mem_inertiaGal_unitsOneAdd_two (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ) (hη : Continuous η)
    (hinf : (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Infinite) :
    ∃ τ ∈ inertiaGal K, η τ ∈ unitsOneAdd p 2 ∧ η τ ≠ 1 := by
  by_contra hne
  push Not at hne
  apply hinf
  set U : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p 2).comap η
  have hU : IsOpen (U : Set Gal(PadicAlgCl p/K)) := (isOpen_unitsOneAdd 2).preimage hη
  have hfin : Finite (Gal(PadicAlgCl p/K) ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  classical

  let f : Gal(PadicAlgCl p/K) ⧸ U → ℤ_[p]ˣ := fun c =>
    if h : ∃ τ ∈ inertiaGal K, (τ : Gal(PadicAlgCl p/K) ⧸ U) = c then η h.choose else 1
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨τ, hτ, rfl⟩
  refine ⟨(τ : Gal(PadicAlgCl p/K) ⧸ U), ?_⟩
  have h : ∃ τ' ∈ inertiaGal K, (τ' : Gal(PadicAlgCl p/K) ⧸ U) = τ := ⟨τ, hτ, rfl⟩
  simp only [f, dif_pos h]
  obtain ⟨hτ', hτ'U⟩ := h.choose_spec
  have hq : (h.choose)⁻¹ * τ ∈ U := QuotientGroup.eq.1 hτ'U
  have hI : (h.choose)⁻¹ * τ ∈ inertiaGal K := mul_mem (inv_mem hτ') hτ
  have h1 : η ((h.choose)⁻¹ * τ) = 1 := hne _ hI hq
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem eq_zero_of_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (M : ℕ → IntermediateField K (PadicAlgCl p)) (hM : Monotone M)
    [∀ k, FiniteDimensional K (M k)]
    (hstab : ∀ (σ : Gal(PadicAlgCl p/K)) (k : ℕ), ∀ y ∈ M k, σ y ∈ M k)
    (hker : ∀ σ : Gal(PadicAlgCl p/K), (∀ k, σ ∈ (M k).fixingSubgroup) → η σ = 1)
    (C : ℝ) (n₁ : ℕ)
    (hbound : ∀ n, n₁ ≤ n → ∀ m, ∀ y ∈ M m, ‖normTrace (M n) y‖ ≤ C * ‖y‖)
    (hgen : ∀ n, n₁ ≤ n → ∃ γ ∈ (M n).fixingSubgroup, η γ ≠ 1)
    {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  classical
  set Ms : IntermediateField K (PadicAlgCl p) := ⨆ k, M k with hMs
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := Ms.restrictScalars ℚ_[p] with hE
  have hdir : Directed (· ≤ ·) M := hM.directed_le
  have hmemE : ∀ {y : PadicAlgCl p}, y ∈ E → ∃ m, y ∈ M m := fun {y} hy => by
    have h : y ∈ ((⨆ k, M k : IntermediateField K (PadicAlgCl p)) : Set (PadicAlgCl p)) :=
      (mem_restrictScalars _).1 hy
    rw [coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  have hME : ∀ {m} {y : PadicAlgCl p}, y ∈ M m → y ∈ E := fun {m} {y} hy =>
    (mem_restrictScalars _).2 (le_iSup M m hy)

  have hxc : x ∈ closureInCp E := by
    have hfixed : ∀ σ ∈ Ms.fixingSubgroup, σ • x = x := by
      intro σ hσ
      have h1 : η σ = 1 := hker σ fun k => by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
        exact fun y hy => hσ y (le_iSup M k hy)
      have := hx σ
      rwa [h1, Units.val_one, PadicInt.coe_one, map_one, one_mul] at this
    have h := fixedPoints_closedSubgroup_eq_closure Ms.fixingSubgroup
      (InfiniteGalois.fixingSubgroup_isClosed Ms)
    have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ Ms.fixingSubgroup, σ • x = x} := hfixed
    rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
    exact hx'

  have hC1 : 1 ≤ C := by
    have h := hbound n₁ le_rfl n₁ 1 (one_mem _)
    rwa [normTrace_of_mem _ (one_mem _), norm_one, mul_one] at h
  have hC0 : 0 ≤ C := zero_le_one.trans hC1

  have hadd : ∀ n, ∀ y ∈ E, ∀ z ∈ E, normTrace (M n) (y + z) = normTrace (M n) y + normTrace (M n) z :=
    fun n y _ z _ => normTrace_add _ y z
  have hbd : ∀ n, n₁ ≤ n → ∀ y ∈ E, ‖normTrace (M n) y‖ ≤ C * ‖y‖ := by
    intro n hn y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hbound n hn m y hm
  have hmapsE : ∀ (σ : Gal(PadicAlgCl p/K)), ∀ y ∈ E, σ y ∈ E := by
    intro σ y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hME (hstab σ m y hm)
  have hcomm : ∀ (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p),
      normTrace (M n) (σ y) = σ (normTrace (M n) y) := by
    intro σ n y
    refine normTrace_map_of_map_eq (M n) σ ?_ y
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hstab σ n z hz
    · intro z hz
      refine ⟨σ⁻¹ z, hstab σ⁻¹ n z hz, ?_⟩
      change σ (σ⁻¹ z) = z
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

  have hR : ∀ n, n₁ ≤ n → extendToClosure E (normTrace (M n)) x = 0 := by
    intro n hn
    set k' : IntermediateField ℚ_[p] (PadicAlgCl p) := (M n).restrictScalars ℚ_[p]
    have : FiniteDimensional ℚ_[p] (M n) := Module.Finite.trans K (M n)
    have : FiniteDimensional ℚ_[p] k' := (inferInstance : FiniteDimensional ℚ_[p] (M n))
    have hkE : k' ≤ E := fun y hy => hME ((mem_restrictScalars _).1 hy)
    have hmaps : ∀ y ∈ E, normTrace (M n) y ∈ k' := fun y _ =>
      (mem_restrictScalars _).2 (normTrace_mem _ y)
    have hfix : ∀ a ∈ k', normTrace (M n) a = a := fun a ha =>
      normTrace_of_mem _ ((mem_restrictScalars _).1 ha)
    have hmul : ∀ a ∈ k', ∀ y ∈ E, normTrace (M n) (a * y) = a * normTrace (M n) y :=
      fun a ha y _ => normTrace_mul_of_mem _ ((mem_restrictScalars _).1 ha) y
    obtain ⟨γ, hγ, hγη⟩ := hgen n hn
    obtain ⟨b, hb, hbx⟩ := extendToClosure_mem (hadd n) (hbd n hn) hmaps hxc

    set q : ℚ_[p] := ((η γ : ℤ_[p]) : ℚ_[p])
    have hq : algebraMap ℚ_[p] ℂ_[p] q = ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) :=
      rfl
    have hqk : algebraMap ℚ_[p] (PadicAlgCl p) q ∈ k' := k'.algebraMap_mem q
    have hγx : γ • x ∈ closureInCp E := smul_mem_closureInCp γ (hmapsE γ) hxc
    have key : extendToClosure E (normTrace (M n)) x =
        algebraMap ℚ_[p] ℂ_[p] q * extendToClosure E (normTrace (M n)) x := by
      conv_lhs => rw [← hx γ]
      rw [hq, extendToClosure_mul (hadd n) (hbd n hn) hkE hmul hqk hγx,
        extendToClosure_smul (hadd n) (hbd n hn) γ (hmapsE γ) (fun y _ => hcomm γ n y) hxc, ← hbx,
        gal_smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ b ((mem_restrictScalars _).1 hb)]
    have hq1 : algebraMap ℚ_[p] ℂ_[p] q ≠ 1 := by
      rw [Ne, ← map_one (algebraMap ℚ_[p] ℂ_[p]), (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff]
      intro h
      apply hγη
      have h' : (η γ : ℤ_[p]) = 1 := Subtype.ext (by simpa [q] using h)
      exact Units.ext h'
    have h2 : (algebraMap ℚ_[p] ℂ_[p] q - 1) * extendToClosure E (normTrace (M n)) x = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hq1)

  have hbound' : ∀ ε > 0, ‖x‖ ≤ (1 + C) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := hmemE hy
    set m' := max m n₁
    have hym : y ∈ M m' := hM (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ closureInCp E := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ closureInCp E := sub_mem_closureInCp hyc hxc
    have hadd' := hadd m'
    have hbd' := hbd m' (le_max_right _ _)
    have h1 : extendToClosure E (normTrace (M m')) (y : ℂ_[p]) =
        extendToClosure E (normTrace (M m')) ((y : ℂ_[p]) - x) +
          extendToClosure E (normTrace (M m')) x := by
      rw [extendToClosure_sub hadd' hbd' hyc hxc]
      ring
    rw [extendToClosure_coe hadd' hbd' hy, normTrace_of_mem _ hym, hR m' (le_max_right _ _),
      add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ C * ε := by
      rw [h1]
      refine (norm_extendToClosure_le hadd' hbd' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hC0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + C * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + C) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound' (‖x‖ / (2 * (1 + C))) (by positivity)
  have h' : (1 + C) * (‖x‖ / (2 * (1 + C))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

end SenTateChar

end GroundTheory.PAdicHodge
end
end
