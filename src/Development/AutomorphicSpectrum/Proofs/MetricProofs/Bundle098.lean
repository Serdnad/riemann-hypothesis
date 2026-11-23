module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle079
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle091
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle092
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell

theorem det_sub_congr {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P Q : Fin N → Prop)
    [Fintype {a // P a}] [Fintype {a // Q a}] [DecidableEq {a // P a}] [DecidableEq {a // Q a}]
    (hPQ : ∀ a, P a ↔ Q a) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det =
      (h.submatrix (Subtype.val : {a // Q a} → Fin N) Subtype.val).det := by
  obtain rfl : P = Q := funext fun a => propext (hPQ a)
  congr!

theorem det_sub_eq_minorIJ {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, P a ↔ a ∈ S) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ h S S := by
  let e : Fin S.card ≃ {a // P a} :=
    (S.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight fun a => (hP a).symm)
  rw [minorIJ, dite_eq_left rfl, ← Matrix.det_submatrix_equiv_self e]
  congr 1

theorem exists_upper_of_minors : ∀ (N j : ℕ) (h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → h.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ h (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ B : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsLowerUni (h * B) := by
  intro N j h hj hbd hdet hmin
  have hsplit := Matrix.twoBlockTriangular_det h (fun a : Fin N => (a : ℕ) < N - j)
    (fun a ha b hb => hbd a b fun e => ha (e.2 hb))
  rw [hsplit] at hdet
  have hA := left_ne_zero_of_mul hdet
  have hC := right_ne_zero_of_mul hdet
  have hu : ∀ b : Fin N, IsUnit (h.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := by
    intro b
    rw [isUnit_iff_ne_zero]
    have hbN := b.isLt
    by_cases hb : (b : ℕ) < N - j
    · by_cases hl : (b : ℕ) + 1 = N - j
      · rw [det_sub_congr h _ (fun a : Fin N => (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_true]; omega]
        exact hA
      · let i : Fin N := ⟨(b : ℕ) + j, by omega⟩
        have hi : (i : ℕ) = (b : ℕ) + j := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : ¬ ((i : ℕ) + 1 ≤ j) := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg this, Fin.le_def, hb, iff_true]
          omega
    · by_cases hl : (b : ℕ) + 1 = N
      · rw [det_sub_congr h _ (fun a : Fin N => ¬ (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_false]
          have := a.isLt
          omega]
        exact hC
      · let i : Fin N := ⟨(b : ℕ) - (N - j), by omega⟩
        have hi : (i : ℕ) = (b : ℕ) - (N - j) := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : (i : ℕ) + 1 ≤ j := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos this, Fin.le_def, hb, iff_false]
          omega
  obtain ⟨B, h1, h2, h3⟩ := hbd.exists_upper hu
  refine ⟨B, h1, h2, fun hB => ?_, h3⟩
  have := h3.det
  rw [Matrix.det_mul, hB, mul_zero] at this
  exact zero_ne_one this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem isValueAt_of_base : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ) (s : M.Ω), z ∈ mcPts (mCoordIdeal y) → basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal (basePart M.blk z)) s → IsValueAt y (algebraMap M.Ω Φ s) z (valAt M.x s (basePart M.blk z)) := by
  intro K _ ι _ Φ _ y Ψ N j M z s _ hb hs
  obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hb hs
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt_eq hb hv]
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  let f : (Σ k, baseIdx ι M.blk k) → (Σ k, ι k) := fun q => ⟨q.1.1, q.2⟩
  have ha : ∀ p : MRing (baseIdx ι M.blk), aeval y (rename f p) = algebraMap M.Ω Φ (aeval M.x p) := fun p => by
    have e : y ∘ f = algebraMap M.Ω Φ ∘ M.x := funext M.y_base
    rw [aeval_rename, e, aeval_algebraMap_apply]
  have hev : ∀ p : MRing (baseIdx ι M.blk), eval z (map (Int.castRingHom ℂ) (rename f p)) =
      eval (basePart M.blk z) (map (Int.castRingHom ℂ) p) := fun p => by
    rw [map_rename, eval_rename]
    rfl
  refine ⟨_, rename f g, rename f h, isMultiHomog_rename_base M.blk hg, isMultiHomog_rename_base M.blk hh, ?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact (map_ne_zero _).2 hy
  · rw [ha, ha, heq, map_mul]
  · rw [hev]
    exact hz0
  · rw [hev, hev]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt

section Minors

variable {R : Type} [CommRing R] {S : Type} [CommRing S] {N : ℕ}

theorem minorIJ_map (ρ : R →+* S) (T : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T.map ρ) I J = ρ (minorIJ T I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · simp

theorem detFac_map (ρ : R →+* S) (j : ℕ) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    detFac j i (T.map ρ) = ρ (detFac j i T) := by
  unfold detFac
  simp only [minorIJ_map, map_mul]
  split_ifs <;> simp

def moveMat (R : Type) [CommRing R] (I C : Finset (Fin N)) (e : I.card = C.card) : Matrix (Fin N) (Fin N) R :=
  fun a b => ∑ t : Fin C.card, if a = I.orderEmbOfFin e t ∧ b = C.orderEmbOfFin rfl t then 1 else 0

theorem moveMat_apply (I C : Finset (Fin N)) (e : I.card = C.card) (s t : Fin C.card) :
    moveMat R I C e (I.orderEmbOfFin e s) (C.orderEmbOfFin rfl t) = if s = t then 1 else 0 := by
  unfold moveMat
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' _ h
    rw [if_neg]
    rintro ⟨-, h2⟩
    exact h ((C.orderEmbOfFin rfl).injective h2).symm
  · simp

theorem moveMat_eq_zero (I C : Finset (Fin N)) (e : I.card = C.card) {a b : Fin N}
    (h : ¬ (a ∈ I ∧ b ∈ C)) : moveMat R I C e a b = 0 := by
  unfold moveMat
  refine Finset.sum_eq_zero fun t _ => if_neg ?_
  rintro ⟨rfl, rfl⟩
  exact h ⟨Finset.orderEmbOfFin_mem _ _ _, Finset.orderEmbOfFin_mem _ _ _⟩

theorem moveMat_blockDiag (j : ℕ) (I C : Finset (Fin N)) (e : I.card = C.card)
    (h : ∀ a ∈ I, ∀ b ∈ C, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) : IsBlockDiag j (moveMat R I C e) :=
  fun a b hab => moveMat_eq_zero I C e fun hm => hab (h a hm.1 b hm.2)

theorem minorIJ_moveMat (I C I' : Finset (Fin N)) (e : I.card = C.card) :
    minorIJ (moveMat R I C e) I' C = if I' = I then 1 else 0 := by
  by_cases hI : I' = I
  · subst hI
    rw [if_pos rfl]
    unfold minorIJ
    rw [dite_eq_left e]
    have : (moveMat R I' C e).submatrix (I'.orderEmbOfFin e) (C.orderEmbOfFin rfl) = 1 := by
      ext s t
      rw [Matrix.submatrix_apply, moveMat_apply, Matrix.one_apply]
    rw [this, det_one]
  · rw [if_neg hI]
    unfold minorIJ
    split_ifs with e'
    · have hex : ∃ a ∈ I', a ∉ I := by
        by_contra hc
        push_neg at hc
        exact hI (Finset.eq_of_subset_of_card_le hc (by rw [e, e']))
      obtain ⟨a, ha, haI⟩ := hex
      have hr : a ∈ Set.range (I'.orderEmbOfFin e') := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      obtain ⟨s, rfl⟩ := hr
      refine det_eq_zero_of_row_eq_zero s fun t => ?_
      rw [Matrix.submatrix_apply]
      exact moveMat_eq_zero I C e fun hm => haI hm.1
    · rfl

theorem stepRows_same (j : ℕ) (hj : j ≤ N) (i : Fin N) {I : Finset (Fin N)} (hI : IsStepRows N j i I) :
    ∀ a ∈ I, ∀ b ∈ stepCols N j i, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  intro a ha b hb
  have hi := i.2
  have ha' := hI.2 ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  by_cases c : (i : ℕ) + 1 ≤ j
  · rw [if_pos c] at ha' hb
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    omega
  · rw [if_neg c] at ha' hb
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    omega

theorem stepCols_nonempty (j : ℕ) (hj : j ≤ N) (i : Fin N) (hp : IsProperStep N j i) :
    stepCols N j i ≠ ∅ := by
  have hi := i.2
  obtain ⟨h1, h2⟩ := hp
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg c]
    omega

theorem coeff_eq (j : ℕ) (hj : j ≤ N) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) (c u : Finset (Fin N) → R) (D P : R)
    (H : ∀ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h →
      D * ∑ I, c I * minorIJ (T * h) I (stepCols N j i) = P * ∑ I, u I * minorIJ h I (stepCols N j i))
    (I₀ : Finset (Fin N)) (hI : IsStepRows N j i I₀) :
    D * ∑ I, c I * minorIJ T I I₀ = P * u I₀ := by
  have h1 := H (moveMat R I₀ (stepCols N j i) hI.1) (moveMat_blockDiag j _ _ _ (stepRows_same j hj i hI))
  have cb := (GlobalTheory.T.block_diagonal_minor_vanishing R N j i hj).1
  simp only [cb, minorIJ_moveMat, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  exact h1

theorem map_identity (j : ℕ) (hj : j ≤ N) (i : Fin N) (hC : stepCols N j i ≠ ∅) (T : Matrix (Fin N) (Fin N) R)
    (c u : Finset (Fin N) → R) (D P : R)
    (H : ∀ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h →
      D * ∑ I, c I * minorIJ (T * h) I (stepCols N j i) = P * ∑ I, u I * minorIJ h I (stepCols N j i))
    (ρ : R →+* S) (h : Matrix (Fin N) (Fin N) S) (hh : IsBlockDiag j h) :
    ρ D * ∑ I, ρ (c I) * minorIJ (T.map ρ * h) I (stepCols N j i) =
      ρ P * ∑ I, ρ (u I) * minorIJ h I (stepCols N j i) := by
  have cb := (GlobalTheory.T.block_diagonal_minor_vanishing S N j i hj).1
  have l : ρ D * ∑ I, ρ (c I) * minorIJ (T.map ρ * h) I (stepCols N j i) =
      ∑ I', ρ (D * ∑ I, c I * minorIJ T I I') * minorIJ h I' (stepCols N j i) := by

    simp only [cb, minorIJ_map, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have r : ρ P * ∑ I, ρ (u I) * minorIJ h I (stepCols N j i) =
      ∑ I', ρ (P * u I') * minorIJ h I' (stepCols N j i) := by
    simp only [map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [l, r]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j i I'
  · rw [coeff_eq j hj i T c u D P H I' hI]
  · rw [((GlobalTheory.T.block_diagonal_minor_vanishing S N j i hj).2.1 h I' hh hI).resolve_right hC, mul_zero, mul_zero]

end Minors

theorem frame_identity_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (S : Type) [CommRing S] (ρ : M.Ω →+* S) (F : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → detFac j p.2 ((F.T p.1).map ρ) * ∑ I, ρ (M.coef ⟨k, m⟩ I) * minorIJ ((F.T p.1).map ρ * h) I (stepCols N j p.2) = ρ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, ρ (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M S _ ρ F hF p k hp m h hh
  have hprop : IsProperStep N j p.2 := by
    by_contra hc
    rw [(M.blk_none p).2 hc] at hp
    exact absurd hp (by simp)
  rw [detFac_map]
  exact map_identity j M.j_le p.2 (stepCols_nonempty j M.j_le p.2 hprop) (F.T p.1) _ _ _ _
    (fun h' hh' => hF.2.1 p k hp m h' hh') ρ h hh

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem regAt_minorIJ_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (N : ℕ) (A : Matrix (Fin N) (Fin N) Ω), z ∈ mcPts (mCoordIdeal x) → (∀ a b, RegAt x (mCoordIdeal z) (A a b)) → ∀ I J : Finset (Fin N), RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (Matrix.of fun a b => valAt x (A a b) z) I J := by
  intro K _ ι _ Ω _ x z N A hz hA I J
  let A' : Matrix (Fin N) (Fin N) (GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) :=
    Matrix.of fun a b => ⟨A a b, hA a b⟩
  have hAA : A = A'.map (GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z).subtype := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) : Ω) := by
    rw [hAA, GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.minorIJ_map]
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h1]
    have h2 : valAt x ((minorIJ A' I J : GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) : Ω) z =
        GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regVal x hz (minorIJ A' I J) := rfl
    rw [h2, ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.minorIJ_map]
    congr 1

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty

theorem flagAn_S_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Nonempty FA.S.X := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  exact FA.Re.nonempty_base

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem coord_image (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact renPt_zero (chartIdeal P p) (affCoord p (rep x))
      ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))
  · intro ht
    obtain ⟨w, hwd⟩ : ∃ w, w = t ∘ Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
    have hren : renPt w = t := by
      subst hwd
      funext l
      simp [renPt]
    have hw : ∀ h ∈ chartIdeal P p, eval w h = 0 := by
      intro h hh
      rw [← eval_renC w h, hren]
      exact ht _ (Ideal.mem_map_of_mem _ hh)
    obtain ⟨hc, h1, ha⟩ := conePts_of_chartIdeal hP p w hw
    let x : Pts P := ⟨proj w, w, hc, rfl⟩
    have ho : SameOrbit (rep x) w := sameOrbit_of_proj_eq (rep_mem x).1 hc.1 (proj_rep x)
    refine ⟨x, fun k => ?_, ?_⟩
    · obtain ⟨c, hcn, hcz⟩ := ho
      have hk : rep x ⟨k, p k⟩ = c k * w ⟨k, p k⟩ := congrFun hcz ⟨k, p k⟩
      rw [hk, h1 k, mul_one]
      exact hcn k
    · show renPt (affCoord p (rep x)) = t
      rw [affCoord_eq_of_sameOrbit p ho, ha, hren]

theorem coord_trans (p p' : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p ∩ src P p') :
    ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
      (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
      eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
        ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.equivFin (Σ k, ι k) := ⟨_, rfl⟩
  have hev : ∀ (y : Pts P) (q : Σ k, ι k), eval (coord P p y) (X (e q)) = affCoord p (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  have hev' : ∀ (y : Pts P) (q : Σ k, ι k), coord P p' y (e q) = affCoord p' (rep y) q := by
    intro y q
    subst he
    simp [coord, renPt]
  refine ⟨∏ k, X (e ⟨k, p' k⟩),
    fun l => X l * ∏ k ∈ Finset.univ.erase (e.symm l).1, X (e ⟨k, p' k⟩), ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [hev]
    exact div_ne_zero (hx.2 k) (hx.1 k)
  · intro y hy _ l
    obtain ⟨r, rfl⟩ := e.surjective l
    have hprod := Finset.mul_prod_erase Finset.univ
      (fun k => affCoord p (rep y) ⟨k, p' k⟩) (Finset.mem_univ r.1)
    have hA : affCoord p' (rep y) r * affCoord p (rep y) ⟨r.1, p' r.1⟩ = affCoord p (rep y) r := by
      have h1 := hy.1 r.1
      have h2 := hy.2 r.1
      simp only [affCoord]
      field_simp
    simp only [map_prod, map_mul, hev, hev', Equiv.symm_apply_apply]
    rw [← hprod, ← mul_assoc, hA]

theorem chart_image_and_trans (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (∀ p : (k : K) → ι k, coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0}) ∧
    ∀ p p' : (k : K) → ι k, ∀ x ∈ src P p ∩ src P p',
      ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
        (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
        eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
          ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) :=
  ⟨coord_image hP, fun p p' x hx => coord_trans p p' x hx⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_cover_and_cone : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ReciprocityTheory.AnForm.R.IsMultiHomogIdeal D → (∀ x : SncRes.Pts P, ∃ p : (k : K) → ι k, x ∈ SncRes.src P p) ∧ (∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts P) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x) (SncRes.lift p' q))) ∧ (∀ z ∈ ReciprocityTheory.AnForm.R.conePts P, ∃ p : (k : K) → ι k, ∃ x ∈ SncRes.src P p, ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) z) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ x' ∈ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x') (SncRes.lift p' q)) → x = x') ∧ ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ((∀ h ∈ SncRes.bd P D p, eval (SncRes.coord P p x) h = 0) ↔ (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_local_chart_polynomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.symbolic_power_in_affine_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), IsMultiHomogIdeal P → IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → IsMultiHomog f a → s' ∉ SncRes.ideal Q p → s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p → ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises
end
