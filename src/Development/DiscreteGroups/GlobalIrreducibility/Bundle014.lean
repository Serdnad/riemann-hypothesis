module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle011
public import Development.DiscreteGroups.GlobalIrreducibility.LConvIrrPre
public import Development.DiscreteGroups.GlobalIrreducibility.LConvIrrAvg
public import Development.DiscreteGroups.GlobalIrreducibility.MulRowOfGood
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle013
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

include hinv in
theorem closure_top (hext : IsExtremeForm ρ B) (Z : Submodule ℂ M) (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z)
    (z₀ : M) (hz₀ : z₀ ∈ Z) (hne : B z₀ z₀ ≠ 0) (y : Hs B hB) :
    y ∈ (Z.map (iota B hB)).topologicalClosure := by
  set W := (Z.map (iota B hB)).topologicalClosure with hW
  have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hWinv : ∀ g, ∀ w ∈ W, pi B hB ρ hinv g w ∈ W := by
    intro g w hw
    rw [← SetLike.mem_coe, hW, Submodule.topologicalClosure_coe] at hw ⊢
    refine map_mem_closure (pi B hB ρ hinv g).continuous hw fun v hv => ?_
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨ρ g z, hZ g z hz, (pi_iota B hB ρ hinv g z).symm⟩
  have hP : ∀ g, W.starProjection * pi B hB ρ hinv g = pi B hB ρ hinv g * W.starProjection := by
    intro g
    refine ContinuousLinearMap.ext fun v => ?_
    show W.starProjection (pi B hB ρ hinv g v) = pi B hB ρ hinv g (W.starProjection v)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hWinv g _ (W.starProjection_apply_mem v)
    · intro w hw
      rw [← map_sub, inner_left]
      exact W.starProjection_inner_eq_zero v _ (hWinv _ _ hw)
  obtain ⟨c, hc⟩ := commutant B hB ρ hinv hext _ hP
  have hι0 : iota B hB z₀ ≠ 0 := fun h => hne (by rw [← inner_iota B hB, h, inner_zero_left])
  have hmem : iota B hB z₀ ∈ W := Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hz₀)
  have h1 : W.starProjection (iota B hB z₀) = iota B hB z₀ := Submodule.starProjection_eq_self_iff.2 hmem
  rw [hc] at h1
  have hc1 : c = 1 := by
    have e : (c - 1) • iota B hB z₀ = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]; simpa using h1
    rcases smul_eq_zero.1 e with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hι0
  apply Submodule.starProjection_eq_self_iff.1
  rw [hc, hc1, one_smul]; rfl

end DiscreteGroups.sglob.LConv.IrreduciblePresentation

namespace DiscreteGroups.sglob.LConv

open IrreduciblePresentation in
theorem extremeIrred : ExtremeIrred := by
  intro G M _ _ _ _ _ ρ hsm hK hAdm B hext Z hZ
  by_cases h0 : ∀ z ∈ Z, B z z = 0
  · exact Or.inl h0
  right
  simp only [not_forall, exists_prop] at h0
  obtain ⟨z₀, hz₀, hne⟩ := h0
  have hB : IsPsd B := ⟨hext.1.1, hext.1.2.1⟩
  have hinv := hext.1.2.2
  intro x
  obtain ⟨K, hKo, hKc, hxK⟩ := hK x
  obtain ⟨s, hs⟩ := hAdm K hKo hKc (Hs B hB) (pi B hB ρ hinv) (norm_pi B hB ρ hinv)
    (commutant B hB ρ hinv hext)
  set L : Submodule ℂ (Hs B hB) := (Z ⊓ fixSub ρ K).map (iota B hB) with hL
  have hle : L ≤ Submodule.span ℂ (s : Set (Hs B hB)) := by
    intro v hv
    obtain ⟨a, ⟨_, haK⟩, rfl⟩ := Submodule.mem_map.1 hv
    exact hs _ fun κ hκ => by rw [pi_iota, haK κ hκ]
  have : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hle
  have hcl : IsClosed (L : Set (Hs B hB)) := L.closed_of_finiteDimensional
  have hxL : iota B hB x ∈ L := by
    rw [← SetLike.mem_coe, ← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hxW := closure_top B hB ρ hinv hext Z hZ z₀ hz₀ hne (iota B hB x)
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hxW
    obtain ⟨_, hb, hd⟩ := hxW ε hε
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hb
    obtain ⟨a, haZ, haK, hda⟩ := avg_exists B hB ρ hinv hsm Z hZ K hKc x hxK z hz
    exact ⟨iota B hB a, Submodule.mem_map_of_mem ⟨haZ, haK⟩, lt_of_le_of_lt hda hd⟩
  obtain ⟨a, ⟨haZ, _⟩, ha⟩ := Submodule.mem_map.1 hxL
  refine ⟨a, haZ, ?_⟩
  rw [← inner_iota B hB, map_sub, ha, sub_self, inner_zero_left]

end DiscreteGroups.sglob.LConv
end
end

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem entries_of_mem_unipRad (j : ℕ) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) (i l : Fin n) (hil : ¬ (i.val < j ∧ j ≤ l.val)) :
    (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 hg i l ?_
  rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two]
  by_cases hi : i.val < j
  · have hl : l.val < j := by omega
    simp [hi, hl]
  · simp only [hi, if_false]
    split_ifs <;> decide

theorem peel_rad (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 0 := by
  have hent := entries_of_mem_unipRad j h hg
  have key : ∀ i l : Fin n, ¬ (i.val < j ∧ j + 1 ≤ l.val) →
      ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hil
    rw [peel_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi, hent ⟨j, hj⟩ l (by simp)]
      by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        rw [one_apply_eq, mul_one, add_neg_cancel, one_apply_ne]
        intro e; rw [e] at hi; simp at hi
      · have hne : (⟨j, hj⟩ : Fin n) ≠ l := fun e => hlj (by rw [← e])
        rw [one_apply_ne hne, mul_zero, add_zero, hent i l (by omega)]
    · rw [if_neg hi, add_zero, hent i l (by omega)]
  refine ⟨fun i l hil => key i l (by
    rcases hil with hil | hil
    · rw [Fin.le_iff_val_le_val] at hil; omega
    · omega), ?_⟩
  rw [sdS]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
  split_ifs with hh
  · rw [key i l (by omega), one_apply_ne]
    intro e; rw [e] at hh; omega
  · rfl

def TopLeft (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

theorem TopLeft.good {j : ℕ} {x : Matrix (Fin n) (Fin n) k} (hx : TopLeft j x) : Good j x :=
  fun i l h => hx i l (by omega)

def dotj (j : ℕ) (ξ c : Fin n → k) : k := ∑ i : Fin n, if i.val < j then ξ i * c i else 0

def rowMul (j : ℕ) (ξ : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) : Fin n → k :=
  fun a => ∑ i : Fin n, if i.val < j then ξ i * Y i a else 0

def colMul (j : ℕ) (Y : Matrix (Fin n) (Fin n) k) (c : Fin n → k) : Fin n → k :=
  fun i => ∑ a : Fin n, if a.val < j then Y i a * c a else 0

theorem dotj_colMul (j : ℕ) (ξ c : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) :
    dotj j ξ (colMul j Y c) = dotj j (rowMul j ξ Y) c := by
  let F : Fin n → Fin n → k := fun i a => if i.val < j ∧ a.val < j then ξ i * Y i a * c a else 0
  have hL : dotj j ξ (colMul j Y c) = ∑ i : Fin n, ∑ a : Fin n, F i a := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < j
    · rw [if_pos hi, colMul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by by_cases ha : a.val < j <;> simp [F, hi, ha, mul_assoc]
    · rw [if_neg hi]; simp [F, hi]
  have hR : dotj j (rowMul j ξ Y) c = ∑ a : Fin n, ∑ i : Fin n, F i a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < j
    · rw [if_pos ha, rowMul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by by_cases hi : i.val < j <;> simp [F, hi, ha]
    · rw [if_neg ha]; simp [F, ha]
  rw [hL, hR, Finset.sum_comm]

end DiscreteGroups.sglob.LConvGenM
end
end
