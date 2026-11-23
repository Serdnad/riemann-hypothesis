module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm Filter Asymptotics

noncomputable section

theorem TwoBlockChainSum.gridSum_chain (D i : ℕ) (hi : i ≤ D) :
    (fun n : ℕ => (∑ j ∈ Finset.range n,
        ((n - j - 1 : ℕ) : ℝ) ^ i * (j : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ))) -
      (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  refine (GridSum.proof D i hi).congr_left fun n => ?_
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  have e1 : n - 1 - (n - j - 1) = j := by omega
  have e2 : n - 1 - j = n - j - 1 := by omega
  simp only [e1, e2]

theorem TwoBlockChainSum.gPoly_chain (D : ℕ) (c : ℕ → ℝ) :
    (fun n : ℕ => ∑ j ∈ Finset.range n, gPoly D c (n - j - 1) j -
      (∑ i ∈ Finset.range (D + 1), c i) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
  refine (IsBigO.fun_sum fun i hi => (TwoBlockChainSum.gridSum_chain D i
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).const_mul_left (c i)).congr_left fun n => ?_
  unfold gPoly
  rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, Finset.mul_sum]
  ring

theorem TwoBlockChainSum.proof (hL : TwoBlockStepLocal.Statement) (hB : TwoBlockStepBound.Statement) :
    TwoBlockChainSum.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨a₀, C, hC⟩ := hL D Ω κ I x B m m' hI hX hx hBi hm hm' hsp
  obtain ⟨K, hK⟩ := hB D Ω κ x B hX hx hBi hsp
  rw [← sum_twoBlockCoeff]
  generalize twoBlockCoeff I x (matAct B x) m m' D = c at hC ⊢
  generalize twoBlockStep x (matAct B x) = s at hC hK ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ i ∈ Finset.range (D + 1), |c i| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ Finset.sum_nonneg fun i _ => abs_nonneg _

  have hterm : ∀ n j : ℕ, j < n →
      |s (n - j - 1) j - gPoly D c (n - j - 1) j| ≤
        if a₀ ≤ n - j - 1 ∧ a₀ ≤ j then |C| * ((n : ℝ) ^ D / n) else (|K| + G) * (n : ℝ) ^ D := by
    intro n j hj
    have hn : ((n - j - 1 : ℕ) : ℝ) + (j : ℝ) + 1 = n := by
      have : n - j - 1 + j + 1 = n := by omega
      exact_mod_cast this
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    split_ifs with h
    · have h1 := hC (n - j - 1) j h.1 h.2
      rw [hn] at h1
      refine le_trans h1 ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    · have hg := abs_gPoly_le D c (n - j - 1) j
      have hn' : ((n - j - 1 + j : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_add]; exact hn
      rw [hn', ← hG] at hg
      have hk := hK (n - j - 1) j
      rw [hn] at hk
      have hk' : K * (n : ℝ) ^ D ≤ |K| * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self K) hpow
      calc _ ≤ |s (n - j - 1) j| + |gPoly D c (n - j - 1) j| := abs_sub _ _
        _ ≤ _ := by linarith

  have h1 : (fun n : ℕ => ∑ j ∈ Finset.range n, (s (n - j - 1) j - gPoly D c (n - j - 1) j)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D := by
    refine IsBigO.of_bound (|C| + 2 * a₀ * (|K| + G)) (Eventually.of_forall fun n => ?_)
    have hpow : 0 ≤ (n : ℝ) ^ D := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpow]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => hterm n j (Finset.mem_range.mp hj)).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hgood : ((Finset.filter (fun j => a₀ ≤ n - j - 1 ∧ a₀ ≤ j) (Finset.range n)).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    have hbad : ((Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card : ℝ) ≤ 2 * a₀ := by
      have hsub : Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n) ⊆
          Finset.range a₀ ∪ Finset.Ico (n - a₀) n := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        omega
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_range, Nat.card_Ico] at hc
      have hc' : (Finset.filter (fun j => ¬(a₀ ≤ n - j - 1 ∧ a₀ ≤ j)) (Finset.range n)).card ≤ 2 * a₀ := by
        omega
      exact_mod_cast hc'
    have hcn : (n : ℝ) * ((n : ℝ) ^ D / n) ≤ (n : ℝ) ^ D := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.cast_zero, zero_mul]
        positivity
      · rw [mul_div_cancel₀]
        exact_mod_cast hn.ne'
    have hq : 0 ≤ (n : ℝ) ^ D / n := by positivity
    have hKG : 0 ≤ (|K| + G) * (n : ℝ) ^ D := mul_nonneg (add_nonneg (abs_nonneg K) hG0) hpow
    have e1 := mul_le_mul_of_nonneg_right hgood (mul_nonneg (abs_nonneg C) hq)
    have e2 := mul_le_mul_of_nonneg_right hbad hKG
    have e3 := mul_le_mul_of_nonneg_left hcn (abs_nonneg C)
    nlinarith
  refine (h1.add (TwoBlockChainSum.gPoly_chain D c)).congr_left fun n => ?_
  simp only [Finset.sum_sub_distrib]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelTorsionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∀ k0 : K, ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ f ∈ relSecM R y (b + Pi.single k0 1),
        (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ D : ℕ, ∃ g ∈ relSecM R y (b + fun _ => D),
          (∏ k, y ⟨k, c k⟩) ^ D * f = y ⟨k0, c0 k0⟩ * g) →
        ∃ g ∈ relSecM R y b, f = y ⟨k0, c0 k0⟩ * g

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def ResolutionImageSup.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ y : d.R.X, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockHorizDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ)
    (l : Ix κ → ℤ),
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), IsHorizontal W →
      (W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) ↔
          W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c)) ∧
        (W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) →
          multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W =
            multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Module

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def modPieceCard (J₁ J₂ : Ideal (MRing ι)) (a : K → ℕ) : ℕ :=
  (J₂.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup.relIndex (J₁.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup

def topComps (J : Ideal (MRing ι)) (d : ℕ) : Set (Ideal (MRing ι)) :=
  {W | W ∈ J.minimalPrimes ∧ IsRelevant W ∧
    ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)}

theorem modPieceCard_self (J : Ideal (MRing ι)) (a : K → ℕ) : modPieceCard J J a = 1 :=
  AddSubgroup.relIndex_self _

end Module

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockMOuter (x x' : Ix κ → Ω) (c : κ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩)

def twoBlockMInner (x x' : Ix κ → Ω) (l : Ix κ → ℤ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩)

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set

noncomputable section

namespace AnResNullForm

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_trans_nf {a b c : (Σ k, ι k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  exact ⟨fun k => c1 k * c2 k, fun k => mul_ne_zero (hc1 k) (hc2 k), by funext q; simp [mul_assoc]⟩

theorem sameOrbit_symm_nf {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp [← mul_assoc, inv_mul_cancel₀ (hc q.1)]

theorem isClosed_blockProportional :
    IsClosed {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
  simp only [ofPred_forall]
  refine isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun i' => isClosed_eq ?_ ?_ <;>
    fun_prop

theorem blockProportional_of_sameOrbit {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) :
    ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  intro k i i'
  ring

theorem sameOrbit_of_blockProportional {a b : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hb : ∀ k, ∃ i, b ⟨k, i⟩ ≠ 0) (h : ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩) :
    SameOrbit a b := by
  choose p hp using hb
  refine ⟨fun k => a ⟨k, p k⟩ / b ⟨k, p k⟩, fun k => ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ := ha k
    have h1 := h k i (p k)
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · rw [h0, zero_mul] at h1
      exact hi ((mul_eq_zero_iff_right (hp k)).1 h1)
    · exact hp k h0
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, p k⟩ / b ⟨k, p k⟩ * b ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hp k)]
    exact h k i (p k)

theorem eval_eq_zero_iff_of_sameOrbit {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    eval z (map (Int.castRingHom ℂ) G) = 0 ↔ eval z' (map (Int.castRingHom ℂ) G) = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_smul_of_isMultiHomog hG,
    mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))]

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem continuousAt_lift (R : AnRes P J e) (x y : R.X) (hy : y ∈ R.U x) : ContinuousAt (R.lift x) y := by
  obtain ⟨j, hj⟩ := R.A.cover y
  rw [continuousAt_pi]
  intro p
  have hya : R.A.chart j y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by simpa [(R.A.chart j).left_inv hj] using hy⟩
  have h1 : ContinuousAt ((fun y' => R.lift x y' p) ∘ (R.A.chart j).symm) (R.A.chart j y) :=
    (R.holo x p j _ hya).continuousAt
  have h2 := h1.comp ((R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(R.A.chart j).left_inv hy']

theorem isAnalyticSubset (R : AnRes P J e) {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG) :
    R.A.IsAnalyticSubset {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} := by
  intro x
  refine ⟨R.U x, R.isOpen_U x, R.mem_U x, 1, fun _ y => eval (R.lift x y) (map (Int.castRingHom ℂ) G),
    fun _ j y hy => ?_, ?_⟩
  · exact analyticAt_eval_comp (F := fun y' => R.lift x ((R.A.chart j).symm y')) (fun p => R.holo x p j y hy) G
  · ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hy⟩
      exact ⟨hy, fun _ => (eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).2 h0⟩
    · rintro ⟨hy, h0⟩
      exact ⟨(eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).1 (h0 0), hy⟩

theorem interior_eq_empty (hND : NonvanishingDense.Statement) (R : AnRes P J e) (hP : IsArithVar P (e + 1))
    {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG) (hGP : G ∉ P) :
    interior {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} = ∅ := by
  set S := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} with hS
  by_contra hne
  obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.2 hne

  obtain ⟨x, hxW, hxJ⟩ : ∃ x ∈ interior S, R.lift x x ∉ mcPts J := by
    by_contra! hall
    obtain ⟨j, hj⟩ := R.A.cover x0
    have hopen : IsOpen (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      ((R.A.chart j).isOpen_image_iff_of_subset_source inter_subset_right).2
        (isOpen_interior.inter (R.A.chart j).open_source)
    have hpos : 0 < volume (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      hopen.measure_pos volume ⟨R.A.chart j x0, x0, ⟨hx0, hj⟩, rfl⟩
    have hsub : R.A.chart j '' (interior S ∩ (R.A.chart j).source) ⊆
        (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      rintro _ ⟨y, ⟨hyW, hys⟩, rfl⟩
      exact ⟨(R.A.chart j).map_source hys, by simpa [(R.A.chart j).left_inv hys] using hall y hyW⟩
    exact hpos.ne' (measure_mono_null hsub (R.null j))
  set z := R.lift x x with hzdef
  have hzP : z ∈ mcPts P := R.mem x x (R.mem_U x)

  set C := {z' : (Σ k, ι k) → ℂ | ∀ f ∈ J, eval z' (map (Int.castRingHom ℂ) f) = 0} with hC
  have hCc : IsClosed C := by
    simp only [hC, ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _)
      continuous_const
  have hzC : z ∉ C := fun h => hxJ ⟨hzP.1, h⟩
  set T := {z' | z' ∈ mcPts P ∧ eval z' (map (Int.castRingHom ℂ) G) ≠ 0} ∩ Cᶜ with hT
  have hzT : z ∈ closure T := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨w, ⟨hwt, hwC⟩, hw⟩ :=
      mem_closure_iff_nhds.1 (hND K ι P (e + 1) G hP hGP hzP) (t ∩ Cᶜ)
        (inter_mem ht (hCc.isOpen_compl.mem_nhds hzC))
    exact ⟨w, hwt, hw, hwC⟩

  have hex : ∀ z', ∃ x', z' ∈ T → SameOrbit (R.lift x' x') z' := fun z' => by
    by_cases h : z' ∈ T
    · obtain ⟨x', hx'⟩ := R.surj z' h.1.1 (fun hJ => h.2 hJ.2)
      exact ⟨x', fun _ => hx'⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose xc hxc using hex
  have hxcW : ∀ z' ∈ T, xc z' ∉ interior S := fun z' hz' hW =>
    hz'.1.2 ((eval_eq_zero_iff_of_sameOrbit hG (hxc z' hz')).1 (show xc z' ∈ S from interior_subset hW))
  have : NeBot (𝓝[T] z) := mem_closure_iff_nhdsWithin_neBot.1 hzT
  obtain ⟨x', hx'⟩ := exists_clusterPt_of_compactSpace (map xc (𝓝[T] z))

  have hprop : (R.lift x' x', z) ∈ {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
    refine isClosed_blockProportional.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht
    have hU : R.U x' ∩ R.lift x' ⁻¹' u ∈ 𝓝 x' :=
      inter_mem ((R.isOpen_U x').mem_nhds (R.mem_U x')) (continuousAt_lift R x' x' (R.mem_U x') hu)
    have hV : xc '' (v ∩ T) ∈ map xc (𝓝[T] z) :=
      mem_map.2 (mem_of_superset (inter_mem_nhdsWithin T hv) fun z' hz' => ⟨z', ⟨hz'.2, hz'.1⟩, rfl⟩)
    obtain ⟨_, ⟨hyU, hyu⟩, z', ⟨hz'v, hz'T⟩, rfl⟩ := clusterPt_iff_nonempty.1 hx' hU hV
    refine ⟨(R.lift x' (xc z'), z'), huv ⟨hyu, hz'v⟩, ?_⟩
    exact blockProportional_of_sameOrbit
      (sameOrbit_trans_nf (R.compat x' (xc z') (xc z') ⟨hyU, R.mem_U _⟩) (hxc z' hz'T))
  have horb : SameOrbit (R.lift x' x') z :=
    sameOrbit_of_blockProportional (R.mem x' x' (R.mem_U x')).1 hzP.1 hprop
  have hxx' : x = x' := R.inj x x' hxJ (sameOrbit_symm_nf horb)
  subst hxx'
  obtain ⟨_, hyW, z', hz'T, rfl⟩ :=
    clusterPt_iff_nonempty.1 hx' (isOpen_interior.mem_nhds hxW)
      (mem_map.2 (mem_of_superset self_mem_nhdsWithin fun z' hz' => ⟨z', hz', rfl⟩) :
        xc '' T ∈ map xc (𝓝[T] z))
  exact hxcW z' hz'T hyW

end AnResNullForm

theorem AnResNullForm.proof (hND : NonvanishingDense.Statement) : AnResNullForm.Statement := by
  intro e K _ ι _ P J R G dG hP hG hGP j
  have h := analyticNull R.A _ (AnResNullForm.isAnalyticSubset R hG)
    (AnResNullForm.interior_eq_empty hND R hP hG hGP) j
  refine measure_mono_null ?_ h
  rintro a ⟨ha, haS⟩
  exact ⟨(R.A.chart j).symm a, ⟨haS, (R.A.chart j).map_target ha⟩, (R.A.chart j).right_inv ha⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockCoeffCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)) (c : κ) (l : Ix κ → ℤ),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ i ≤ D, twoBlockCoeff I x (matAct B x) m m' D i = twoBlockVert x (matAct B x) c l (twoBlockDegList D i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
