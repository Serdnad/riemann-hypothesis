module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle028
public import Mathlib.Analysis.Matrix.Normed
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle244
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle245
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle239
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PolarCompare

theorem abs_qf_le_sum_sq {P Q : ℕ} (z : Sp P Q) : |qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
  have h1 : 0 ≤ ∑ i : Fin P, ‖z (Sum.inl i)‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h2 : 0 ≤ ∑ j : Fin Q, ‖z (Sum.inr j)‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  rw [Fintype.sum_sum_type]
  simp only [qf, Complex.normSq_eq_norm_sq]
  rw [abs_le]
  constructor <;> linarith

theorem sq_compare_left {T S N r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 3 * r < 1 - s) (h1 : N ≤ T + S)
    (h : T ^ 2 + 2 * S < s * r ^ 2) : N ^ 2 + 2 * S < r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hs : s < 1 := by linarith
  have hsr : s * r ^ 2 < r ^ 2 := by nlinarith
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hT2 : T ^ 2 < r ^ 2 := by nlinarith
  have hTr : T < r := by nlinarith
  have hN2 : N * N ≤ (T + S) * (T + S) := mul_self_le_mul_self hN h1
  have a1 : T * S ≤ r * S := mul_le_mul_of_nonneg_right hTr.le hS
  have a2 : r * (2 * S) ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left hS2.le hr0.le
  have a3 : (2 * S) * (2 * S) ≤ r ^ 2 * r ^ 2 := mul_self_le_mul_self (by linarith) hS2.le
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 3 * r * r ^ 2 < (1 - s) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem sq_compare_right {T S N E r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 11 * r < s - 1) (h1 : E ≤ N + S) (h2 : T ≤ 2 * E)
    (h3 : T ≤ 2 → T - T ^ 3 / 16 ≤ E)
    (h : N ^ 2 + 2 * S < r ^ 2) : T ^ 2 + 2 * S < s * r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hNr : N < r := by nlinarith
  have hrr : r ^ 2 < r / 2 := by nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
  have hT3r : T ≤ 3 * r := by linarith
  have hTE : T - T ^ 3 / 16 ≤ E := h3 (by linarith)
  have hc1 : T * T ≤ 3 * r * (3 * r) := mul_self_le_mul_self hT hT3r
  have hc2 : T * T * T ≤ 3 * r * (3 * r) * (3 * r) := mul_le_mul hc1 hT3r hT (by positivity)
  have hr3 : r ^ 2 * r ≤ r ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hr1.le (sq_nonneg r)
  have hb0 : 0 ≤ S + T ^ 3 / 16 := by positivity
  have hb2 : S + T ^ 3 / 16 ≤ 2 * r ^ 2 := by nlinarith
  have hTNb : T ≤ N + (S + T ^ 3 / 16) := by linarith
  have hT2 : T * T ≤ (N + (S + T ^ 3 / 16)) * (N + (S + T ^ 3 / 16)) :=
    mul_self_le_mul_self hT hTNb
  have a1 : N * (S + T ^ 3 / 16) ≤ r * (S + T ^ 3 / 16) :=
    mul_le_mul_of_nonneg_right hNr.le hb0
  have a2 : r * (S + T ^ 3 / 16) ≤ r * (2 * r ^ 2) := mul_le_mul_of_nonneg_left hb2 hr0.le
  have a3 : (S + T ^ 3 / 16) * (S + T ^ 3 / 16) ≤ (2 * r ^ 2) * (2 * r ^ 2) :=
    mul_self_le_mul_self hb0 hb2
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 11 * r * r ^ 2 < (s - 1) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem polar_sq_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanSq u < (t⁻¹ * r) ^ 2 → ptSq e (polarPt e u) < r ^ 2) ∧ (ptSq e (polarPt e u) < r ^ 2 → tanSq u < (t * r) ^ 2) := by
  intro P Q P' Q' e t ht
  have ht0 : 0 < t := by linarith
  have hA : 0 < 1 - t⁻¹ ^ 2 := by
    have h1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have h2 : 0 < t⁻¹ := inv_pos.mpr ht0
    nlinarith
  have hB : 0 < t ^ 2 - 1 := by nlinarith
  have hc : 0 < min (1 / 2 : ℝ) (min ((1 - t⁻¹ ^ 2) / 3) ((t ^ 2 - 1) / 11)) :=
    lt_min (by norm_num) (lt_min (div_pos hA (by norm_num)) (div_pos hB (by norm_num)))
  filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds hc)] with r hr
  obtain ⟨hr0, hrc⟩ := hr
  simp only [Set.mem_Ioi, Set.mem_Iio] at hr0 hrc
  have hr1 : r < 1 / 2 := lt_of_lt_of_le hrc (min_le_left _ _)
  have hr2 : 3 * r < 1 - t⁻¹ ^ 2 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hr3 : 11 * r < t ^ 2 - 1 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  rintro ⟨θ, z⟩ hu
  simp only [Set.mem_Ioo] at hu
  have hθ : |θ| ≤ Real.pi := abs_le.mpr ⟨hu.1.le, hu.2.le⟩

  have hq : |sg (e none) * qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
    rw [abs_mul]
    rcases sg_eq (e none) with h | h <;> rw [h] <;> simpa using abs_qf_le_sum_sq z
  have hρ1 := (abs_sqrt_sub_one_le (sg (e none) * qf z)).trans hq
  have hw1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hpt : ptSq e (polarPt e (θ, z)) =
      ‖(Real.sqrt (1 - sg (e none) * qf z) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 +
        2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [ptSq, polarPt_none, polarPt_some]
  have htan : tanSq (θ, z) = |θ| ^ 2 + 2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [tanSq, sq_abs]
  obtain ⟨hb1, hb2, hb3⟩ := exp_bounds θ hθ
  rw [hpt, htan]
  generalize Real.sqrt (1 - sg (e none) * qf z) = ρ at hρ1 ⊢
  generalize Complex.exp ((θ : ℂ) * Complex.I) = w at hw1 hb1 hb2 hb3 ⊢
  generalize ∑ i, ‖z i‖ ^ 2 = S at hρ1 ⊢
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hρ1
  have hdiff : ‖(ρ : ℂ) * w - w‖ = |ρ - 1| := by
    have : (ρ : ℂ) * w - w = ((ρ - 1 : ℝ) : ℂ) * w := by push_cast; ring
    rw [this, norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hNE : ‖(ρ : ℂ) * w - 1‖ ≤ |θ| + S := by
    have := norm_sub_le_norm_sub_add_norm_sub ((ρ : ℂ) * w) w 1
    rw [hdiff] at this
    linarith
  have hEN : ‖w - 1‖ ≤ ‖(ρ : ℂ) * w - 1‖ + S := by
    have := norm_sub_le_norm_sub_add_norm_sub w ((ρ : ℂ) * w) 1
    rw [norm_sub_rev w ((ρ : ℂ) * w), hdiff] at this
    linarith
  constructor
  · intro h
    rw [mul_pow] at h
    exact sq_compare_left (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr2 hNE h
  · intro h
    rw [mul_pow]
    exact sq_compare_right (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr3 hEN hb2 hb3 h

end GlobalTheory.PolarCompare
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.SectionHsCompare

variable {P Q P' Q' : ℕ}

section Frob
open scoped Matrix.Norms.Frobenius

theorem frob_sq (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]

theorem frob_split (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖Z‖ ^ 2 = ‖Z (e none) (e none)‖ ^ 2 + ∑ b, ‖Z (e none) (e (some b))‖ ^ 2 +
      ∑ i, ‖Z (e (some i)) (e none)‖ ^ 2 + ∑ i, ∑ b, ‖Z (e (some i)) (e (some b))‖ ^ 2 := by
  have h : ∀ x, ∑ w, ‖Z x w‖ ^ 2 = ∑ o, ‖Z x (e o)‖ ^ 2 := fun x =>
    (e.sum_comp (fun w => ‖Z x w‖ ^ 2)).symm
  rw [frob_sq, Finset.sum_congr rfl (fun x _ => h x),
    ← e.sum_comp (fun x => ∑ o, ‖Z x (e o)‖ ^ 2)]
  simp only [Fintype.sum_option, Finset.sum_add_distrib]
  ring

theorem add_le_mul_pow_of_sq_le_of_le_mul {t η R W : ℝ} (ht : 1 < t) (hη : η = (t - 1) / (3 * t)) (hR : 0 ≤ R)
    (hW : 0 ≤ W) (h1 : W ≤ R + η * R) (h2 : R ≤ W + η * R) :
    R ^ 2 ≤ t * W ^ 2 ∧ W ^ 2 ≤ t * R ^ 2 := by
  have h3 : 0 < 3 * t := by linarith
  have hη0 : 0 ≤ η := by rw [hη]; exact div_nonneg (by linarith) h3.le
  have key : η * (3 * t) = t - 1 := by rw [hη]; field_simp
  have hηt : η < 1 / 3 := by nlinarith
  constructor
  ·
    have hW' : (1 - η) * R ≤ W := by linarith
    have hsq : ((1 - η) * R) ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by nlinarith) hW' 2
    have hge : 1 ≤ t * (1 - η) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ t), sq_nonneg R]
  ·
    have hW' : W ≤ (1 + η) * R := by linarith
    have hsq : W ^ 2 ≤ ((1 + η) * R) ^ 2 := pow_le_pow_left₀ hW hW' 2
    have hle : (1 + η) ^ 2 ≤ t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R)]

private lemma le_of_sq_le_sq_of_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  nlinarith

theorem hsDist_section_mul_block : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptSq e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptSq e y + hsDist g ≤ t * hsDist (a * j g) ∧ hsDist (a * j g) ≤ t * (ptSq e y + hsDist g) := by
  intro P Q P' Q' e j hj t ht
  set η : ℝ := (t - 1) / (3 * t) with hη
  have hηpos : 0 < η := div_pos (by linarith) (by linarith)
  have hη3 : η < 1 / 3 := by
    rw [hη, div_lt_iff₀ (by linarith)]; linarith
  set c : ℝ := η / 3 with hc
  have hcpos : 0 < c := by positivity
  have hc1 : c < 1 := by linarith
  refine ⟨min 1 (c ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro y a hy hya hrow hblk g
  have hyc : ptSq e y < c ^ 2 := lt_of_lt_of_le hy (min_le_right _ _)
  have hy1 : ptSq e y < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  obtain ⟨h00, h0b, ha0, hab⟩ := hj g

  have hcol : ∀ x, UpqT.mat a x (e none) = y x := by
    intro x
    have := congrFun hya x
    simpa [act, baseVec, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  set S : ℝ := ∑ i, ‖y (e (some i))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hpt : ptSq e y = ‖y (e none) - 1‖ ^ 2 + 2 * S := rfl
  have hSpt : S ≤ ptSq e y := by nlinarith [sq_nonneg ‖y (e none) - 1‖]
  have hSc : S < c ^ 2 := lt_of_le_of_lt hSpt hyc
  have hS1 : S < 1 := lt_of_le_of_lt hSpt hy1

  have hn1 : 1 ≤ ‖1 + y (e none)‖ := by
    have h1 : ‖y (e none) - 1‖ < 1 := by
      nlinarith [norm_nonneg (y (e none) - 1), sq_nonneg ‖y (e none) - 1‖]
    have h2 : (2 : ℂ) = (1 + y (e none)) - (y (e none) - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖1 + y (e none)‖ + ‖y (e none) - 1‖ := by
      rw [h2]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith

  set M := UpqT.mat a with hM
  set K := UpqT.mat (j g) - 1 with hK
  set Ep : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun x w =>
    (e.symm x).elim 0 (fun _ => (e.symm w).elim 0 (fun _ => (M - 1) x w)) with hEp
  set Z0 := (M - 1) + K - Ep with hZ0
  set Z := UpqT.mat (a * j g) - 1 with hZ
  have hmul : UpqT.mat (a * j g) = M * UpqT.mat (j g) := rfl
  have hZe : Z = (M - 1) + K + (M - 1) * K := by
    rw [hZ, hmul, hK]; noncomm_ring
  have hdiff : Z - Z0 = Ep + (M - 1) * K := by
    rw [hZe, hZ0]; abel

  have hK2 : ‖K‖ ^ 2 = hsDist g := by
    rw [frob_split e K]
    simp [hK, Matrix.sub_apply, Matrix.one_apply, h00, h0b, ha0, hab, hsDist]
  have hEp2 : ‖Ep‖ ^ 2 = ∑ i, ∑ b, ‖(M - 1) (e (some i)) (e (some b))‖ ^ 2 := by
    rw [frob_split e Ep]
    simp [hEp, Matrix.of_apply]
  have hEpS : ‖Ep‖ ^ 2 ≤ S ^ 2 := by
    rw [hEp2, sq, hS, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_
    rw [hblk i b, div_pow, ← mul_pow]
    have hp : 0 ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := sq_nonneg _
    calc (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / ‖1 + y (e none)‖ ^ 2
        ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / 1 :=
          div_le_div_of_nonneg_left hp one_pos (by nlinarith)
      _ = (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := div_one _
  have hM2 : ‖M - 1‖ ^ 2 = ptSq e y + ‖Ep‖ ^ 2 := by
    rw [frob_split e (M - 1), hEp2, hpt]
    simp [Matrix.sub_apply, Matrix.one_apply, hcol, hrow]
    rw [hS, Fintype.sum_sum_type]
    ring
  have e00 : Z0 (e none) (e none) = y (e none) - 1 := by
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, hcol, h00]
  have e0b : ∀ b, Z0 (e none) (e (some b)) = M (e none) (e (some b)) := by
    intro b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, h0b]
  have ei0 : ∀ i, Z0 (e (some i)) (e none) = y (e (some i)) := by
    intro i
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hcol, ha0]
  have eib : ∀ i b, Z0 (e (some i)) (e (some b)) = (UpqT.mat g - 1) i b := by
    intro i b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hab]
  have hZ02 : ‖Z0‖ ^ 2 = ptSq e y + hsDist g := by
    rw [frob_split e Z0, e00]
    simp only [e0b, ei0, eib, hrow]
    rw [hpt, hS]
    unfold hsDist
    ring
  have hZ2 : ‖Z‖ ^ 2 = hsDist (a * j g) := by
    rw [frob_sq]; rfl

  have hR0 : 0 ≤ ‖Z0‖ := norm_nonneg _
  have hEpb : ‖Ep‖ ≤ c * ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [mul_pow, hZ02]
    have hg : 0 ≤ hsDist g := by rw [← hK2]; positivity
    calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
      _ = S * S := sq S
      _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
      _ ≤ ptSq e y * c ^ 2 := mul_le_mul_of_nonneg_right hSpt (sq_nonneg c)
      _ ≤ c ^ 2 * (ptSq e y + hsDist g) := by
        rw [mul_comm, mul_add]; exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) hg)
  have hMb : ‖M - 1‖ ≤ 2 * c := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [hM2]
    have h1 : ‖Ep‖ ^ 2 ≤ c ^ 2 :=
      calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
        _ = S * S := sq S
        _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
        _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hS1.le (sq_nonneg c)
        _ = c ^ 2 := one_mul _
    have h2 : (2 * c) ^ 2 = 4 * c ^ 2 := by ring
    rw [h2]
    linarith [sq_nonneg c]
  have hKb : ‖K‖ ≤ ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg hR0
    rw [hK2, hZ02]
    have : 0 ≤ ptSq e y := by rw [hpt]; positivity
    linarith
  have hdb : ‖Z - Z0‖ ≤ η * ‖Z0‖ := by
    rw [hdiff]
    calc ‖Ep + (M - 1) * K‖ ≤ ‖Ep‖ + ‖(M - 1) * K‖ := norm_add_le _ _
      _ ≤ ‖Ep‖ + ‖M - 1‖ * ‖K‖ := by gcongr; exact Matrix.frobenius_norm_mul _ _
      _ ≤ c * ‖Z0‖ + 2 * c * ‖Z0‖ := by gcongr
      _ = η * ‖Z0‖ := by rw [hc]; ring
  have h1 : ‖Z‖ ≤ ‖Z0‖ + η * ‖Z0‖ := by
    calc ‖Z‖ = ‖Z0 + (Z - Z0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖Z0‖ + ‖Z - Z0‖ := norm_add_le _ _
      _ ≤ ‖Z0‖ + η * ‖Z0‖ := by gcongr
  have h2 : ‖Z0‖ ≤ ‖Z‖ + η * ‖Z0‖ := by
    calc ‖Z0‖ = ‖Z - (Z - Z0)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Z‖ + ‖Z - Z0‖ := norm_sub_le _ _
      _ ≤ ‖Z‖ + η * ‖Z0‖ := by gcongr
  obtain ⟨hA, hB⟩ := add_le_mul_pow_of_sq_le_of_le_mul ht hη hR0 (norm_nonneg _) h1 h2
  rw [hZ02, hZ2] at hA hB
  exact ⟨hA, hB⟩

end Frob

end GlobalTheory.SectionHsCompare
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.FockTen

theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    have hf : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    rw [hf, zero_mul, zero_mul]

theorem fockF_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (ten f) (ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [fockF_eq_fockL]
  show Formalism.L2.DIV.fockL (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ)) (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) = _
  rw [Formalism.L2.DIV.fk_fock_prod]
  exact Finset.prod_congr rfl fun τ _ => (fockF_eq_fockL _ _).symm

theorem fockF_extremal_ne {n : ℕ} (l : DomWeight n) : Formalism.REAL.fockF (extremal ℂ n l) (extremal ℂ n l) ≠ 0 := by
  intro h0
  have h1 : normFock l (extremal ℂ n l) (extremal ℂ n l) = 1 := bridge_normFock_extremal_holds n l
  rw [normFock, h0, div_zero] at h1
  exact zero_ne_one h1

theorem nfAll_ten : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  intro ι _ n lam
  have hden : ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => fockF_extremal_ne (lam τ)
  refine ⟨fun f g => ?_, fun p hp => ?_, fun G M s f y => ?_⟩
  · rw [nfAll, fockF_ten]
    simp only [normFock]
    rw [Finset.prod_div_distrib]
  · rw [nfAll, div_eq_zero_iff] at hp
    rcases hp with hp | hp
    · by_contra hne
      exact (@LT.lt.ne' ℂ Complex.partialOrder.toPreorder _ _ (Formalism.L2.DIV.ps_fockF_pos p hne)) hp
    · exact absurd hp hden
  · show (∏ τ, (M τ * y.1 τ).det ^ s τ) *
        MvPolynomial.eval _ (∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)) = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_rename]
    rfl

end GlobalTheory.FockTen
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.CmHermitianRankFrames

theorem four_mul_add_five_le_rank (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    4 * D.R.rS + 5 ≤ X.B.I.n := by

  rw [X.n_eq]
  have hk := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

theorem cm_herm_rank_frames : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J ∧ 4 * D.R.rS + 5 ≤ X.B.I.n ∧ ∀ u, ∃ T : X.B.I.F, (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T :=
  fun D X => ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X,
    fun u => MassDataLevelSSteps.frameStd_holds X u⟩

end GlobalTheory.CmHermitianRankFrames
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.localModel_modulus_properties_on_units : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → (∀ x y : E, IsUnit x → IsUnit y → M.modK (x * y) = M.modK x * M.modK y) ∧ (∀ x : E, IsUnit x → 0 < M.modK x ∧ M.modK (M.L.cj x) = M.modK x) ∧ ∀ x : E, x ∈ M.L.O → (∃ y ∈ M.L.O, x * y = 1) → M.modK x = 1 := by
  first | exact @GlobalTheory.ModuleUnits.modK_units | exact GlobalTheory.ModuleUnits.modK_units | (intros; apply GlobalTheory.ModuleUnits.modK_units <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pairLattice_le_liftedPairLattice_sup_isotropic : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), IsPair Λ F F' F'' β g → Mlat Λ F F' F'' β g ≤ La Λ g F F'' ⊔ toO S (Xsp F) := by
  first | exact @GlobalTheory.LoopC.PairLat.Mlat_le_La_sup | exact GlobalTheory.LoopC.PairLat.Mlat_le_La_sup | (intros; apply GlobalTheory.LoopC.PairLat.Mlat_le_La_sup <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unitaryComplement_moves_hermitianTerms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  first | exact @GlobalTheory.HL.ComplMove.main | exact GlobalTheory.HL.ComplMove.main | (intros; apply GlobalTheory.HL.ComplMove.main <;> assumption)
end
