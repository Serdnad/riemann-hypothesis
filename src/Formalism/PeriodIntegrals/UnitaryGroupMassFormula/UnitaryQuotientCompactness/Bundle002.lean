module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle001
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModCore
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

lemma le_one_of_pow_le {x M : ℝ} (h : ∀ m : ℕ, x ^ m ≤ M) : x ≤ 1 := by
  by_contra hx
  push_neg at hx
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt M hx
  linarith [h m]

variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {D : Matrix (Fin m) (Fin m) ℂ → ℝ}

lemma modOne (hG : IsMatGroup G) (hD : ModProps G D) : D 1 = 1 := by
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G := hG.2.1
  have hpos := hD.1 1 h1
  have hm := hD.2.1 1 h1 1 h1
  rw [mul_one] at hm
  exact mul_left_cancel₀ hpos.ne' (hm.symm.trans (mul_one (D 1)).symm)

lemma pow_mem (hG : IsMatGroup G) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G) (n : ℕ) : x ^ n ∈ G := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact hG.2.1
  | succ n ih =>
    rw [pow_succ]
    exact hG.2.2.1 _ ih _ hx

lemma modPow (hG : IsMatGroup G) (hD : ModProps G D) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G)
    (n : ℕ) : D (x ^ n) = D x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact modOne hG hD
  | succ n ih =>
    rw [pow_succ, pow_succ, hD.2.1 _ (pow_mem hG hx n) _ hx, ih]

lemma modEqOne (hG : IsMatGroup G) (hD : ModProps G D) {x : Matrix (Fin m) (Fin m) ℂ} (hx : x ∈ G)
    (h1 : D x ≤ 1) (h2 : D x⁻¹ ≤ 1) : D x = 1 := by
  have hinv := (hG.2.2.2 x hx).1
  have hxx := (hG.2.2.2 x hx).2
  have hm := hD.2.1 x hx x⁻¹ hinv
  rw [hxx, modOne hG hD] at hm
  have h0 := hD.1 x hx
  have hle : D x * D x⁻¹ ≤ D x := by
    calc D x * D x⁻¹ ≤ D x * 1 := mul_le_mul_of_nonneg_left h2 h0.le
      _ = D x := mul_one _
  linarith

def box1 (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) := {x | ∀ i j, ‖(x - 1) i j‖ ≤ 1}

lemma isCompact_inter_unit_box (hG : IsClosed G) : IsCompact (G ∩ box1 m) := by
  have hbox : box1 m = Set.pi Set.univ (fun i => Set.pi Set.univ
      (fun j => Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1)) := by
    ext x
    simp only [box1, Set.mem_setOf_eq, Matrix.sub_apply]
    constructor
    · intro h
      show ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1
      intro i _ j _
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact h i j
    · intro h i j
      have h' : ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ Metric.closedBall ((1 : Matrix (Fin m) (Fin m) ℂ) i j) 1 := h
      have h2 := h' i (Set.mem_univ _) j (Set.mem_univ _)
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      exact h2
  have hc : IsCompact (box1 m) := by
    rw [hbox]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  exact hc.inter_left hG

theorem trivS_of (hSG : SsetGroup) (hUW : UWCompact) (hN : NGroup) (hNC : NContract) : TrivS := by
  unfold TrivS
  intro k r z hz hT D hD
  have hG := hSG k r z hz hT
  obtain ⟨hN1, hNmul, hNinv⟩ := hN k r
  have h1S : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Sset k r z := hG.2.1
  obtain ⟨h0, hh0, m0, hm0, he0⟩ := h1S
  have hNS : ∀ n ∈ Nset k r, n ∈ Sset k r z := by
    intro n hn
    refine ⟨h0, hh0, m0 * n, hNmul _ hm0 _ hn, ?_⟩
    rw [← mul_assoc, ← he0, one_mul]
  have hUS : ∀ h ∈ UWset k r z, h ∈ Sset k r z := by
    intro h hh
    exact ⟨h, hh, 1, hN1, (mul_one h).symm⟩
  have hpowN : ∀ n ∈ Nset k r, ∀ j : ℕ, n ^ j ∈ Nset k r := by
    intro n hn j
    induction j with
    | zero =>
      rw [pow_zero]
      exact hN1
    | succ j ih =>
      rw [pow_succ]
      exact hNmul _ ih _ hn
  obtain ⟨M, hM⟩ := hD.2.2.2 _ Set.inter_subset_left (isCompact_inter_unit_box hG.1)
  have hNle : ∀ n ∈ Nset k r, D n ≤ 1 := by
    intro n hn
    apply le_one_of_pow_le (M := M)
    intro j
    have hnj := hpowN n hn j
    obtain ⟨c, hcu, hcS, hcb⟩ := hNC k r z hz (n ^ j) hnj 1 one_pos
    have hnjS := hNS _ hnj
    rw [← modPow hG hD (hNS n hn) j, ← hD.2.2.1 c hcu hcS _ hnjS]
    apply hM
    exact ⟨(hcS _).mpr hnjS, fun i' j' => hcb i' j'⟩
  obtain ⟨M', hM'⟩ := hD.2.2.2 _ (fun h hh => hUS h hh) (hUW k r z hz hT)
  have hSle : ∀ g ∈ Sset k r z, D g ≤ M' := by
    intro g hg
    obtain ⟨h, hh, m, hm, rfl⟩ := hg
    rw [hD.2.1 h (hUS h hh) m (hNS m hm)]
    have h1 := hNle m hm
    have h2 := hD.1 h (hUS h hh)
    have h3 := hM' h hh
    calc D h * D m ≤ D h * 1 := mul_le_mul_of_nonneg_left h1 h2.le
      _ ≤ M' := by
        rw [mul_one]
        exact h3
  have hle1 : ∀ g ∈ Sset k r z, D g ≤ 1 := by
    intro g hg
    apply le_one_of_pow_le (M := M')
    intro j
    rw [← modPow hG hD hg j]
    exact hSle _ (pow_mem hG hg j)
  intro g hg
  exact modEqOne hG hD hg (hle1 g hg) (hle1 _ (hG.2.2.2 g hg).1)

end PI.QuotSetU.UnitaryGroupMassFormula.SW
end
end

section

open MeasureTheory Matrix

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

theorem quotSetU_of (hUH : UHGroup) (hSub : SsetSub) (hSG : SsetGroup) (hMod : ModExists)
    (hTG : TrivG) (hTS : TrivS) : PI.QuotSetU := by
  intro k r z hz hT
  refine ⟨hUH k r, hSG k r z hz hT, hSub k r z, ?_, ?_⟩
  · intro μG hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hUH k r)
    exact hD1 (hTG k r D hD) μG hμ
  · intro μS hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hSG k r z hz hT)
    exact hD1 (hTS k r z hz hT D hD) μS hμ

end PI.QuotSetU.UnitaryGroupMassFormula
end

section

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI ModW ModW.MG

open scoped Classical in
open Classical in
def modFun {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (hG : IsMatGroup G)
    (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  if h : g ∈ G then (Measure.modularCharacterFun (mk hG g h) : ℝ) else 1

theorem exists_modular_function : ModExists := by
  intro m G hG
  refine ⟨modFun G hG, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg
    simp only [modFun, dite_eq_left hg]
    exact_mod_cast Measure.modularCharacterFun_pos (mk hG g hg)
  ·
    intro a ha b hb
    have hab : a * b ∈ G := hG.2.2.1 a ha b hb
    simp only [modFun, dite_eq_left ha, dite_eq_left hb, dite_eq_left hab]
    have hmk : mk hG (a * b) hab = mk hG a ha * mk hG b hb := by
      apply toM_injective
      simp only [toM_mk, toM_mul]
    rw [hmk]
    have h := (Measure.modularCharacter (G := MG G hG)).map_mul (mk hG a ha) (mk hG b hb)
    exact_mod_cast h
  ·
    intro c hc hcG g hg
    have hcg : c * g * c⁻¹ ∈ G := (hcG g).2 hg
    simp only [modFun, dite_eq_left hg, dite_eq_left hcg]
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    have hConj : ∃ φ : MG G hG ≃ₜ* MG G hG,
        ∀ x, (φ x).toM = c * x.toM * c⁻¹ := by
      refine ⟨{
        toFun := fun x => mk hG (c * x.toM * c⁻¹) ((hcG _).2 x.toM_mem)
        invFun := fun x => mk hG (c⁻¹ * x.toM * c) (by
          apply (hcG _).1
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
            Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
          exact x.toM_mem)
        left_inv := fun x => by
          apply toM_injective
          simp only [toM_mk]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd,
            Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
        right_inv := fun x => by
          apply toM_injective
          simp only [toM_mk]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
            Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
        map_mul' := fun x y => by
          apply toM_injective
          simp only [toM_mk, toM_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc c⁻¹ c, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        continuous_toFun := by
          rw [continuous_iff_toM]
          simp only [toM_mk]
          exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
        continuous_invFun := by
          rw [continuous_iff_toM]
          simp only [toM_mk]
          exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
      }, fun x => toM_mk _ ((hcG _).2 x.toM_mem)⟩
    obtain ⟨φ, hφ⟩ := hConj
    have hmk : mk hG (c * g * c⁻¹) hcg = φ (mk hG g hg) := by
      apply toM_injective
      simp only [hφ, toM_mk]
    rw [hmk, modF_conj]
  ·
    intro V hVG hV
    have hK : IsCompact ((fun y : MtM m => Matrix.of y) ⁻¹' V) := hV
    have hW : IsCompact ((val : MG G hG → MtM m) ⁻¹' ((fun y : MtM m => Matrix.of y) ⁻¹' V)) :=
      isClosedEmbedding_val.isCompact_preimage hK
    obtain ⟨M, hM⟩ := modF_bdd _ hW
    refine ⟨M, fun v hv => ?_⟩
    have hvG : v ∈ G := hVG hv
    simp only [modFun, dite_eq_left hvG]
    apply hM
    show Matrix.of (mk hG v hvG).1 ∈ V
    exact hv
  ·
    intro h1 μ hμ
    refine rightInv_of (hG := hG) μ hμ (fun g => ?_)
    have hg := h1 g.toM g.toM_mem
    simp only [modFun, dite_eq_left g.toM_mem, mk_toM] at hg
    exact_mod_cast hg

end PI.QuotSetU.UnitaryGroupMassFormula
end
end
