module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARSqA

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

section Gen

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem fockT_cm_cp {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) {ε : Fin n → Bool}
    {j b u v : Fin n} (hjb : ¬(ε j = true ∧ ε b = false)) (huv : ε u = true ∧ ε v = false) (y : W) :
    cm j b (cp u v y) = -(cp u v (cm j b y)) := by
  have h3 := (hC j b u v).2.2
  have hne : ¬(j = u ∧ b = v) := by
    rintro ⟨rfl, rfl⟩
    exact hjb huv
  rw [if_neg hne] at h3
  have h := LinearMap.congr_fun h3 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_cm_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (j b w z : Fin n) (y : W) :
    cm j b (cm w z y) = -(cm w z (cm j b y)) := by
  have h := LinearMap.congr_fun (hC j b w z).2.1 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_stable_gen {E cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (hK : CommutesCAR E cp cm) (ε : Fin n → Bool) {j b : Fin n} (hjb : ¬(ε j = true ∧ ε b = false))
    {x : W} (hx : ∀ j b, ¬(ε j = true ∧ ε b = false) → cm j b x = 0) :
    (∀ a c, cm j b (E a c x) = 0) ∧ (∀ a c, cm j b (diagE ε E cp cm a c x) = 0) ∧
      cm j b (dOp ε E cp x) = 0 ∧ cm j b (dOp' ε E cm x) = 0 := by
  have hEc : ∀ a c y, cm j b (E a c y) = E a c (cm j b y) := fun a c y => by
    have h := LinearMap.congr_fun (hK a c j b).2 y
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hx0 := hx j b hjb
  have hE0 : ∀ a c, cm j b (E a c x) = 0 := fun a c => by rw [hEc, hx0, map_zero]
  have hcpcm : ∀ u v w z, ε u = true ∧ ε v = false → cm j b (cp u v (cm w z x)) = 0 := by
    intro u v w z huv
    rw [fockT_cm_cp hC hjb huv, fockT_cm_cm hC, hx0]
    simp
  refine ⟨hE0, ?_, ?_, ?_⟩
  · intro a c
    simp only [diagE, LinearMap.add_apply, map_add (f := _), hE0, zero_add, sgE]
    by_cases ha : ε a = true <;> by_cases hc : ε c = true
    · simp only [if_pos (And.intro ha hc), LinearMap.sum_apply, map_sum, Module.End.mul_apply]
      refine Finset.sum_eq_zero fun y hy => hcpcm a y c y ⟨ha, ?_⟩
      simpa [minusIdx] using hy
    · simp [ha, hc, sgE]
    · simp [ha, hc, sgE]
    · have ha0 : ε a = false := by cases h : ε a <;> simp_all
      have hc0 : ε c = false := by cases h : ε c <;> simp_all
      simp only [if_neg (show ¬(ε a = true ∧ ε c = true) from fun h => ha h.1),
        if_pos (And.intro ha0 hc0), LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum,
        Module.End.mul_apply]
      refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i hi => hcpcm i c i a ⟨?_, hc0⟩)
      simpa [plusIdx] using hi
  · simp only [dOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
    rw [hEc, fockT_cm_cp hC hjb ⟨by simpa [plusIdx] using hi, by simpa [minusIdx] using ha⟩, hx0]
    simp
  · simp only [dOp', LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Module.End.mul_apply]
    refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_)
    rw [hEc, fockT_cm_cm hC, hx0]
    simp

theorem fockT_anti_sum {R : Type*} [Ring R] {ι κ : Type*} (s : Finset ι) (t : Finset κ) (G : R)
    (A B : ι → κ → R) (hA : ∀ i k, G * A i k = A i k * G) (hB : ∀ i k, G * B i k = -(B i k * G)) :
    G * ∑ i ∈ s, ∑ k ∈ t, A i k * B i k = -((∑ i ∈ s, ∑ k ∈ t, A i k * B i k) * G) := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  calc G * (A i k * B i k) = A i k * (G * B i k) := by rw [← mul_assoc, hA, mul_assoc]
    _ = -(A i k * B i k * G) := by rw [hB, mul_neg, mul_assoc]

end Gen

section FockLemmas

variable {n : ℕ}

theorem fock_contractLeft_involute (d : Module.Dual ℂ (Fin n × Fin n → ℂ)) (x : Fock n) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]
  | ι_mul x m hx =>
    simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg, CliffordAlgebra.contractLeft_ι_mul,
      hx, map_sub, map_smul, mul_neg]

theorem fock_inv_sq :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap *
      (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap = 1 :=
  LinearMap.ext fun x => CliffordAlgebra.involute_involute x

theorem fock_inv_cp (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cpFock i a =
      -(cpFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cpFock, CliffordAlgebra.involute_ι]

theorem fock_inv_cm (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cmFock i a =
      -(cmFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cmFock, fock_contractLeft_involute]

end FockLemmas

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def physFock (ε : Fin n → Bool) : Submodule ℂ (Fock n) :=
  ⨅ i : Fin n, ⨅ a : Fin n, ⨅ (_ : ¬ (ε i = true ∧ ε a = false)), LinearMap.ker (cmFock i a)

section
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def khwSub (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ W) (γ : Fin n → ℝ) : Submodule ℂ W :=
  (⨅ a, LinearMap.ker (F a a - ((γ a : ℝ) : ℂ) • (1 : Module.End ℂ W))) ⊓
    ⨅ a, ⨅ b, ⨅ (_ : a < b ∧ ε a = ε b), LinearMap.ker (F a b)
end

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def HasGelfandChar (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (S : Submodule ℂ M) : Prop :=
  ∀ k : ℕ, ∀ x ∈ S, gelfand E k x = gval (icShift μ) k • x ∧
    gelfand (antiE E) k x = gval (icShift (-μ)) k • x

def resSeries (a : Fin n → ℂ) : PowerSeries ℂ :=
  ∏ s, (1 + PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) - 1

def poleV (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)

def poleVd (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)

theorem rescale_neg_one_const (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) (PowerSeries.C c) = PowerSeries.C c := by
  ext m
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem rescale_neg_one_geometric_inv (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) ((1 - PowerSeries.C c * PowerSeries.X)⁻¹) =
      (1 + PowerSeries.C c * PowerSeries.X)⁻¹ := by
  have h1 : PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.C c * PowerSeries.X) =
      1 + PowerSeries.C c * PowerSeries.X := by
    simp [PowerSeries.rescale_X, rescale_neg_one_const]
  have hc0 : PowerSeries.constantCoeff (1 - PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  have hc1 : PowerSeries.constantCoeff (1 + PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc1, ← h1, ← map_mul, PowerSeries.inv_mul_cancel _ hc0, map_one]

theorem residueSeries_neg (l : Fin n → ℂ) :
    resSeries (-l) = -PowerSeries.rescale (-1 : ℂ) (gelfandSeries l) := by
  have key : ∀ s, (1 + PowerSeries.X * (1 - PowerSeries.C ((-l) s) * PowerSeries.X)⁻¹) =
      PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
    intro s
    rw [map_sub, map_one, map_mul, PowerSeries.rescale_X, rescale_neg_one_geometric_inv]
    simp only [Pi.neg_apply, map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add]
  unfold resSeries gelfandSeries
  simp_rw [key]
  rw [← map_prod, map_sub, map_one]
  ring

theorem coeff_residueSeries_neg (l : Fin n → ℂ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries (-l)) = (-1 : ℂ) ^ k * gval l k := by
  rw [residueSeries_neg, map_neg, PowerSeries.coeff_rescale]
  unfold gval
  ring

theorem pole_eq_neg_shift (μ : Fin n → ℝ) : poleV μ = -icShift (-μ) := by
  funext s
  simp only [poleV, icShift, Pi.neg_apply]
  push_cast
  ring

theorem dualPole_eq_neg_shift (μ : Fin n → ℝ) : poleVd μ = -icShift μ := by
  funext s
  simp only [poleVd, icShift, Pi.neg_apply]
  push_cast
  ring

theorem ptr_eeV_pow_char {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : HasGelfandChar E μ S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeV E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleV μ)) • x := by
  rw [ptr_eeV_pow, LinearMap.smul_apply, (hS k x hx).2, smul_smul, pole_eq_neg_shift, coeff_residueSeries_neg]

theorem ptr_eeVd_pow_char {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : HasGelfandChar E μ S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeVd E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleVd μ)) • x := by
  rw [ptr_eeVd_pow, LinearMap.smul_apply, (hS k x hx).1, smul_smul, dualPole_eq_neg_shift, coeff_residueSeries_neg]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (i a j b : Fin n) :
    cm i a * cp j b = (if i = j ∧ a = b then 1 else 0) - cp j b * cm i a :=
  eq_sub_of_add_eq (hC i a j b).2.2

private theorem isCAR_cm_mul_cm_eq_neg_swap {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (i a j b : Fin n) :
    cm i a * cm j b = -(cm j b * cm i a) :=
  eq_neg_of_add_eq_zero_left (hC i a j b).2.1

private theorem sum_sum_ite_eq_eq_sum {R ι : Type*} [AddCommMonoid R] [DecidableEq ι] (s : Finset ι)
    (f : ι → R) : ∑ x ∈ s, ∑ y ∈ s, (if x = y then f x else 0) = ∑ x ∈ s, f x :=
  Finset.sum_congr rfl fun x hx => by simp [hx]

private theorem isCAR_cp_cm_cp_cm_reorder_shared_snd {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b x y : Fin n) :
    cp a x * cm b x * (cp b y * cm a y) =
      (if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y) := by
  rw [show cp a x * cm b x * (cp b y * cm a y) = cp a x * (cm b x * cp b y) * cm a y by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC b x b y]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hxy h.2), if_neg hxy]
    noncomm_ring

private theorem isCAR_cp_cm_cp_cm_reorder_shared_fst {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b i j : Fin n) :
    cp i b * cm i a * (cp j a * cm j b) =
      (if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b) := by
  rw [show cp i b * cm i a * (cp j a * cm j b) = cp i b * (cm i a * cp j a) * cm j b by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC i a j a]
  by_cases hij : i = j
  · subst hij
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hij h.1), if_neg hij]
    noncomm_ring

theorem casimirK_sgE {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool) :
    casimirK ε (sgE ε cp cm) = (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • sgE ε cp cm a a := by
  have hpos : ∀ a ∈ plusIdx ε, ∀ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ x ∈ minusIdx ε, ∑ y ∈ minusIdx ε,
          ((if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y)) := by
    intro a ha b hb
    rw [csq_sgE_pp ε cp cm ha hb, csq_sgE_pp ε cp cm hb ha, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => isCAR_cp_cm_cp_cm_reorder_shared_snd hC a b x y
  have hneg : ∀ a ∈ minusIdx ε, ∀ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε,
          ((if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b)) := by
    intro a ha b hb
    rw [csq_sgE_mm ε cp cm ha hb, csq_sgE_mm ε cp cm hb ha, neg_mul_neg,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => isCAR_cp_cm_cp_cm_reorder_shared_fst hC a b i j
  have hposBlock : ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (pOf ε : ℂ) •
            ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x -
          ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
            ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hpos a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const, ← Finset.smul_sum]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hnegBlock : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (qOf ε : ℂ) •
            ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b -
          ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
            ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hneg a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hT : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) =
      -∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
        ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [sum_comm_pair_pair, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [isCAR_cm_mul_cm_eq_neg_swap hC i a j b, mul_neg]
  have hN : ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b =
      ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.sum_comm]
  have hR1 : ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • sgE ε cp cm a a =
      (qOf ε : ℂ) •
        ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_pp ε cp cm ha ha]
  have hR2 : ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • sgE ε cp cm a a =
      -((pOf ε : ℂ) •
        ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b) := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_mm ε cp cm ha ha, smul_neg]
  rw [casimirK_pm, two_rho_sum, hposBlock,
    hnegBlock, hR1, hR2, hT, hN]
  abel

theorem csq_E_comm_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (x y a b : Fin n) :
    E x y * sgE ε cp cm a b = sgE ε cp cm a b * E x y := by
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← mul_assoc, (hEC x y a z).1, mul_assoc, (hEC x y b z).2, ← mul_assoc]
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, (hEC x y i b).1, mul_assoc, (hEC x y i a).2, ← mul_assoc]
  · rw [mul_zero, zero_mul]

def crossT (ε : Fin n → Bool) (E cp cm : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, E x y * sgE ε cp cm y x +
    ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, E a b * sgE ε cp cm b a

private theorem sum_sum_add_mul_add_of_commute (s : Finset (Fin n)) (E S : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b c d, S a b * E c d = E c d * S a b) :
    ∑ a ∈ s, ∑ b ∈ s, (E a b + S a b) * (E b a + S b a) =
      ∑ a ∈ s, ∑ b ∈ s, E a b * E b a + (2 : ℂ) • ∑ a ∈ s, ∑ b ∈ s, E a b * S b a +
        ∑ a ∈ s, ∑ b ∈ s, S a b * S b a := by
  have hsw : ∑ a ∈ s, ∑ b ∈ s, S a b * E b a = ∑ a ∈ s, ∑ b ∈ s, E a b * S b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h b a a b
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [hsw, two_smul]
  abel

theorem casimirK_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) :
    casimirK ε (diagE ε E cp cm) =
      casimirK ε E + (2 : ℂ) • crossT ε E cp cm + casimirK ε (sgE ε cp cm) := by
  have hc : ∀ a b c d, sgE ε cp cm a b * E c d = E c d * sgE ε cp cm a b :=
    fun a b c d => (csq_E_comm_sgE hEC ε c d a b).symm
  simp only [casimirK_pm, diagE, crossT]
  rw [sum_sum_add_mul_add_of_commute (plusIdx ε) E (sgE ε cp cm) hc,
    sum_sum_add_mul_add_of_commute (minusIdx ε) E (sgE ε cp cm) hc, smul_add]
  abel

end ReciprocityTheory.ChartRestriction.DS
end
end
