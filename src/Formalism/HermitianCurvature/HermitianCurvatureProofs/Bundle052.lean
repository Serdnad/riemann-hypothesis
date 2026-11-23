module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianCovectors.HermBvecLeft
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.Bundle007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle010
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OutsideSystemsBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle043
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.FixFlag
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.FixSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.NilpotentOrthogonalComplement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.StabilizerSplittingOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem herm_bvec_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    herm H (bvec p) (bvec q) = H q p := by
  have hs : star (bvec q) = bvec q := by
    ext i
    by_cases h : i = q <;> simp [bvec, Pi.single_apply, h]
  unfold herm
  rw [hs]
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

section dp
variable {k r : ℕ} (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))

theorem dp1 (hp : p.val < r) (hq : q.val < r) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, if_pos ⟨hp, hq⟩]
theorem dp2 (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    dpsiP k r z' p q = if p.val + 1 = r then z' q else 0 := by
  rw [dpsiP, if_neg (by omega), if_pos ⟨hp, hq1, hq2⟩]
theorem dp0 (hp : p.val < r) (hq : r + k < q.val) : dpsiP k r z' p q = 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem dp3 (hp1 : r ≤ p.val) (hp2 : p.val ≤ r + k) (hq : r + k < q.val) :
    dpsiP k r z' p q = if q.val = r + k + 1 then herm (Hpk k r) (bvec p) z' else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_pos ⟨hp1, hp2, hq⟩]
theorem dp4 (hp : r + k < p.val) (hq : r + k < q.val) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hp, hq⟩]
end dp

theorem hpk_row_eI {k r : ℕ} (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) p = if p.val = 2 * r + k - b.val then 1 else 0 := by
  have hb := b.isLt
  have heI : (eI k r b).val = b.val := rfl
  simp only [Hpk]
  by_cases h : p.val = 2 * r + k - b.val
  · rw [if_pos h, if_pos ⟨by rw [heI]; exact hb, by rw [heI]; omega⟩]
  · rw [if_neg h, if_neg (fun hc => h (by rw [heI] at hc; omega)),
      if_neg (fun hc => by rw [heI] at hc; omega),
      if_neg (fun hc => by rw [heI] at hc; exact absurd hc.1 (by omega))]

theorem herm_unitary {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r))
    (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hg']

theorem herm_bvec_eI {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (eI k r b)) = v (esI k r b) := by
  have h1 : herm (Hpk k r) v (bvec (eI k r b)) = ∑ p, Hpk k r (eI k r b) p * v p := by
    have hs : star (bvec (eI k r b)) = bvec (eI k r b) := by
      ext i
      by_cases h : i = eI k r b <;> simp [bvec, Pi.single_apply, h]
    unfold herm
    rw [hs]
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  simp_rw [hpk_row_eI]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp [esI]
  · intro p _ hp
    rw [if_neg, zero_mul]
    intro h
    exact hp (Fin.ext (by simp [esI, h]))
  · simp

theorem xi_Y_zhat_identity : XiYZhat := by
  apply CovecW.covec_entries <;> assumption

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gN_mt_cont : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem conv_pt (hNI : NormInv) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) {t g : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) := by
  obtain ⟨_, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  have htg : t⁻¹ * g ∈ UH (Hpk k r) := hmul _ (hinv t ht).2 _ hg
  have hA : 1 ≤ B.gN t := ((hNI k r).2 t ht).2
  have hG : 1 ≤ B.gN g := ((hNI k r).2 g hg).2
  have hC : 1 ≤ B.gN (t⁻¹ * g) := ((hNI k r).2 _ htg).2

  have hsub : B.gN g ≤ B.gN t * B.gN (t⁻¹ * g) := by
    have h1 : t * (t⁻¹ * g) = g := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hinv t ht).1, one_mul]
    calc B.gN g = B.gN (t * (t⁻¹ * g)) := by rw [h1]
      _ ≤ _ := (hNI k r).1 _ _
  have hA0 : 0 < B.gN t := by linarith
  have hC0 : 0 < B.gN (t⁻¹ * g) := by linarith
  have hG0 : 0 < B.gN g := by linarith
  have h1 : B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b) ≤ B.gN g ^ (-b) := by
    rw [← Real.mul_rpow hA0.le hC0.le, Real.rpow_neg (by positivity), Real.rpow_neg hG0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hG0 b) (Real.rpow_le_rpow hG0.le hsub hb)
  have h2 : B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN (t⁻¹ * g) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a)
      ≤ B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0.le _)
    _ = B.gN t ^ (b - a) * (B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b)) := by
        rw [← mul_assoc, ← Real.rpow_add hA0, show b - a + -b = -a by ring]
    _ ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le _)

end Formalism.FourierDecayAlt.P.S3dx6
end
end

section

open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lpt (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (s : ℕ) (t : E) (h : TB.Pt E) : C.LPt :=
  C.loc (S.σ v) h ++ [(s, S.σ v t)]

theorem re_real_sum {W : Type} (c : ℝ) (Ws : Finset W) (p : W → ℝ) (N : W → ℂ) :
    ((c : ℂ) * ∑ w ∈ Ws, (p w : ℂ) * N w).re = c * ∑ w ∈ Ws, p w * (N w).re := by
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

theorem liftOfLoc_statement : KB.LiftOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ hpos _ _ hloc
  intro ε hε i s hs hsi hir w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by
    have := len_le_cnt S w.1 v; omega
  have hb1 : 1 ≤ i - s + 1 := by omega
  have hbs : i - s + 1 + s ≤ S.G.r + 1 := by omega
  have hlev : i - s + 1 + s - 1 = i := by omega
  have hi : i ≤ S.G.r + 1 := by omega
  have hwn : w.1.cnt ≤ w.1.cnt + C.Kst := by omega
  have hL := fun v => hloc v (i - s + 1) s hb1 hs hbs (w.1 v) ⟨w, rfl⟩ (hlen v)
  simp only [hlev] at hL
  choose Up θp Um θm hPp hPm hblk using hL
  have hUp : ∀ v, ∀ a ∈ Up v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPp v).2 a ha).1, ((hPp v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hUm : ∀ v, ∀ a ∈ Um v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPm v).2 a ha).1, ((hPm v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hprobP := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θp) (fun v _ => (hPp v).1) (fun v _ => hUp v) hwn hcnt'
  have hprobM := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θm) (fun v _ => (hPm v).1) (fun v _ => hUm v) hwn hcnt'
  refine ⟨fun A x => pθ S A w θp x.1 * pθ S A w θm x.2, fun A => pair_prob (hprobP A) (hprobM A), ?_⟩
  intro Y T κ hY hκ t ht t' ht' ht0 ht0' _ A
  have hσ : ∀ v, S.σ v t ≠ 0 := fun v => (map_ne_zero _).2 ht0
  have hσ' : ∀ v, S.σ v t' ≠ 0 := fun v => (map_ne_zero _).2 ht0'
  have hsz : ∀ v, ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = i - s + 1 - 1 := by
    intro v p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
    rw [ptSize_loc, hY h hh]; omega
  have hU : ∀ v, ∃ u : ℂ, ‖u‖ = 1 ∧ (v ∈ A → KB.BlockPSD Y Y
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h'))
      (fun h h' => u * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst *
        KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h'))) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, hB⟩ := hblk v ε hε (S.σ v t) (S.σ v t') (Y.image (C.loc (S.σ v))) (hσ v) (hσ' v) (hsz v)
      exact ⟨u, hu, fun _ => blockPSD_comp _ _ _ _ hB Y (C.loc (S.σ v))
        (fun x hx => Finset.mem_image_of_mem _ hx)⟩
    · exact ⟨1, by simp, fun h => absurd h hv⟩
  choose u hu1 hu2 using hU
  have hprod := blockPSD_prod (Y₁ := Y) (Y₂ := Y) univ
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t h')))
    (fun v h h' => (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t' h) (lpt S v s t' h')))
    (by
      intro v _
      by_cases hv : v ∈ A
      · simp only [if_pos hv]; exact hu2 v hv
      · simp only [if_neg hv, one_mul]
        exact blockPSD_pull (Y.image (lpt S v s t) ∪ Y.image (lpt S v s t')) (KB.gN S v ε i (w.1 v))
          (gN_psd S hpos v hε hi w _) Y (lpt S v s t) (lpt S v s t')
          (fun h hh => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh))
          (fun h hh => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh)))
  have hmem : ∀ τ ∈ T, ∀ h ∈ Y, TB.join h s τ ∈ TB.pts Y s T := by
    classical
    intro τ hτ h hh
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(h, τ), Finset.mem_product.2 ⟨hh, hτ⟩, rfl⟩
  have hκb : KB.BlockPSD Y Y (TB.blk κ s t t) (TB.blk κ s t t') (TB.blk κ s t' t') :=
    blockPSD_pull (TB.pts Y s T) κ hκ Y (fun h => TB.join h s t) (fun h => TB.join h s t')
      (hmem t ht) (hmem t' ht')
  have hmain := block_cross_le (blockPSD_mul hκb hprod)

  have eL : (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s t t' h h' * ∏ v, (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h')) =
      (∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t' := by
    rw [Nst_eq S hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    simp only [lpt]; ring

  have eD : ∀ (τ : E) (Uq : Fin S.f → Finset (List C.Letter)) (θq : Fin S.f → List C.Letter → ℝ),
      (∀ v, TB.IsProb (Uq v) (θq v)) → (∀ v, ∀ a ∈ Uq v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst) →
      (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s τ τ h h' * ∏ v,
        (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
      ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S A w θq w' : ℂ) * S.base.Nst ε i s w' Y (TB.blk κ s τ τ) τ τ := by
    intro τ Uq θq hP hUq
    have hx : ∀ h h', (∏ v, (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
        ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst),
          (pθ S A w θq w' : ℂ) * ∏ v, KB.gN S v ε i (w'.1 v) (lpt S v s τ h) (lpt S v s τ h') := by
      intro h h'
      have he := expand (A := A) (w := w) (θ := θq) (U := Uq) (fun v _ => hP v) (fun v _ => hUq v) hwn hcnt'
        (fun v a => KB.gN S v ε i a (lpt S v s τ h) (lpt S v s τ h'))
      rw [he, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Complex.ofReal_prod]
      rfl
    simp only [hx]
    rw [mix_sum]
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Nst_eq S hi]; rfl
  have hK : S.base.K = C.Kst := rfl
  have hcw : S.base.cnt w = w.1.cnt := rfl
  rw [eL, eD t Up θp (fun v => (hPp v).1) hUp, eD t' Um θm (fun v => (hPm v).1) hUm, re_real_sum, re_real_sum]
    at hmain
  have hsp := sum_pair (S.base.Wb (w.1.cnt + C.Kst)) (S.base.Wb (w.1.cnt + C.Kst)) (pθ S A w θp) (pθ S A w θm)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t t) t t).re)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t' t') t' t').re) (hprobM A).2.2 (hprobP A).2.2
  rw [hK, hcw, hsp]
  calc (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ C.Kst) * ‖S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ =
      ‖(∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ := by
        rw [norm_mul, norm_prod]
        congr 1
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [norm_mul, hu1, one_mul, norm_pow, av_eq, map_sub, map_inv₀, map_inv₀]
    _ ≤ _ := hmain
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.PBA
end

section

open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

theorem top_of_local : KB.TopOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ' hpos _ hloc ε hε s hs2 hsr w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v =>
    le_trans (Nat.add_le_add_right (len_le_cnt S w.1 v) _) hcnt'
  choose U θ hUθ using fun v => hloc v s hs2 hsr (w.1 v) ⟨w, rfl⟩ (hlen v)
  have hU : ∀ v, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hUθ v).1.2 a ha).1,
      le_trans ((hUθ v).1.2 a ha).2 (Nat.add_le_add_right (len_le_cnt S w.1 v) _)⟩
  have hw : w.1.cnt ≤ w.1.cnt + C.Kst := Nat.le_add_right _ _
  refine ⟨fun B => pθ S B w θ, fun B => pθ_prob (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt', ?_⟩
  intro Y hY κ hκ t ht B
  let g : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, S.σ v t)]
  let G : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.gN S v ε (S.G.r + 1) (w.1 v) (g v h) (g v h')
  let M : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.mix S v ε (S.G.r + 1) (U v) (θ v) (g v h) (g v h')
  let c : Fin S.f → ℝ := fun v => (‖S.σ v t‖ * Λ' (S.G.r + 2 - s) s v) ^ (2 * C.Kst)
  let A : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    if v ∈ B then (c v : ℂ) * M v h h' else G v h h'
  have hG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (G v) := fun v _ =>
    psd_comp _ _ (gN_psd S hpos v hε le_rfl w (Y.image (g v))) Y (g v)
      (fun h hh => mem_image_of_mem _ hh)
  have hAG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (fun x y => A v x y - G v x y) := by
    intro v _
    by_cases hv : v ∈ B
    · have hσ : S.σ v t ≠ 0 := (map_ne_zero (S.σ v)).mpr ht
      have hY' : ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = S.G.r + 1 - s := by
        intro p hp
        obtain ⟨h, hh, rfl⟩ := mem_image.mp hp
        rw [ptSize_loc]
        exact hY h hh
      have h1 := psd_comp _ _ ((hUθ v).2 ε hε (S.σ v t) _ hσ hY') Y (C.loc (S.σ v))
        (fun h hh => mem_image_of_mem _ hh)
      refine Jx8.psd_congr ?_ h1
      intro x _ y _
      simp only [A, if_pos hv]
      rfl
    · refine Jx8.psd_congr ?_ (Jx8.zero_psd Y)
      intro x _ y _
      simp only [A, if_neg hv, sub_self]
  have hle := BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (Jx7.psd_prod_dom univ G A hG hAG)
  have hprod : ∀ h h', ∏ v, A v h h' =
      (∏ v ∈ B, (c v : ℂ)) * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    intro h h'
    calc ∏ v, A v h h'
        = ∏ v, ((if v ∈ B then (c v : ℂ) else 1) * (if v ∈ B then M v h h' else G v h h')) :=
          prod_congr rfl (fun v _ => by by_cases hv : v ∈ B <;> simp [A, hv])
      _ = (∏ v, (if v ∈ B then (c v : ℂ) else 1)) * ∏ v, (if v ∈ B then M v h h' else G v h h') :=
          prod_mul_distrib
      _ = _ := by rw [prod_ite_mem, univ_inter]
  have hexp : ∀ h h', ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h') =
      ∏ v, (if v ∈ B then M v h h' else G v h h') := fun h h' =>
    expand (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt'
      (fun v a => KB.gN S v ε (S.G.r + 1) a (g v h) (g v h'))
  have hR : ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    simp only [Nst_eq S (i := S.G.r + 1) le_rfl]
    have hm := mix_sum Y (S.base.Wb (w.1.cnt + C.Kst)) κ 1 (fun w' => (pθ S B w θ w' : ℂ))
      (fun w' h h' => ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h'))
    simp only [one_mul] at hm
    rw [← hm]
    refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
    rw [hexp h h']
  have hC : ∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K) = ∏ v ∈ B, c v :=
    prod_congr rfl fun v _ => by rw [av_eq]; rfl
  have hsum : ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K),
        pθ S B w θ w' * (S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re =
      (∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun w' _ => ?_
    rw [Complex.re_ofReal_mul]
  rw [hC, hsum, hR, Nst_eq S (i := S.G.r + 1) le_rfl s w Y κ t t, ← Complex.re_ofReal_mul,
    Complex.ofReal_prod]
  have hA : (∏ v ∈ B, (c v : ℂ)) * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, A v h h' := by
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h' _ => ?_
    rw [hprod h h', mul_left_comm]
  rw [hA]
  simp only [mul_sub, sum_sub_distrib, Complex.sub_re] at hle
  linarith

end

end Formalism.FourierDecayAlt.P.PBA
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

def GLFibre : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ j, j + 1 ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ a b : C.LPt, D.IsLocPt a j → D.IsLocPt b j →
      Integrable (fun c : ℂ => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) ∧
      ∫ c : ℂ, TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)]) = TBB.NP p nn F j w a b

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

theorem Formalism.FourierDecayAlt.P.stabilizer_split : Formalism.FourierDecayAlt.C2.C1ii :=
  PI.StabSplit.stabilizer_splitting_of_parts PI.StabSplit.fixed_point_subgroup PI.StabSplit.stabilizer_subgroup_flag
    PI.StabSplit.unipotent_nilpotent_radical PI.StabSplit.nilpotent_orthogonal_complement
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem admissible_length_holds : AdmLen := by
  intro E _ _ _ Wp Wq _ _ _ _ S v a ha
  obtain ⟨w, rfl⟩ := ha
  exact le_trans (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)) w.2.2

end Formalism.FourierDecayAlt.P.CutMP.En
end
