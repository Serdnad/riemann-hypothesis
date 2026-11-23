module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle225
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle226
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoincareValueBoundOnCube
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle206
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobSecK

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_congr (w : List (Ix n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) :
    Set.EqOn (Rw w f) (Rw w h) (GLs n) := by
  induction w with
  | nil => exact e
  | cons p w ih => exact RCalc.Rd_congr (bs p) ih

theorem Rw_smooth (w : List (Ix n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact RCalc.Rd_contDiffOn (bs p) ih

theorem Rw_append (w w' : List (Ix n)) (f : Mat n → V) : Rw w' (Rw w f) = Rw (w' ++ w) f := by
  induction w' with
  | nil => rfl
  | cons p w' ih =>
    show Rd (bs p) (Rw w' (Rw w f)) = Rd (bs p) (Rw (w' ++ w) f)
    rw [ih]

end Words

section HWords

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HWords

section Skew

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Skew

section Bracket

def cf (M : Mat n) (p : Ix n) : ℝ := if p.1 then (M p.2.1 p.2.2).re else (M p.2.1 p.2.2).im

theorem sum_cf (M : Mat n) : ∑ p : Ix n, cf M p • bs p = M := by
  rw [OmDec.sum_Ix]
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ext i j
  simp only [cf, bs, if_true, Bool.false_eq_true, if_false, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · simp only [h, and_self, if_true]
    obtain ⟨rfl, rfl⟩ := h
    simp [Complex.real_smul, Complex.re_add_im]
  · simp [h]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sum_cf (M : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd M f g = ∑ p : Ix n, ((cf M p : ℝ) : ℂ) • Rd (bs p) f g := by
  conv_lhs => rw [← sum_cf M]

  simp only [Rd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, map_smul]
  exact (Complex.coe_smul _ _).symm

end Bracket

section HBracket

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HBracket

section Sections

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Sections

section Powers

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Powers

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Main

end GlobalTheory.CompanionTheory.SobSecK
end
end

section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.cone_measure_congruence_invariant : ∀ (n : ℕ) (g : Mat n), g.det ≠ 0 → ∀ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ), (∀ v, hOf (T v) = g * hOf v * gᴴ) → LinearMap.det T = ‖g.det‖ ^ (2 * n) → Measure.map T (coneMeas n) = coneMeas n := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.map_coneMeas_eq | exact GlobalTheory.CompanionTheory.ConeHaar.map_coneMeas_eq | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.map_coneMeas_eq <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.left_translate_right_derivative : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | exact GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | (intros; apply GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.chart_and_right_words_smooth : ∀ n : ℕ, IsOpen (GLs n) ∧ Continuous (cm (n := n)) ∧ cm (n := n) 0 = 0 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n)) ∧ ∀ L : List (Idx n), ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all | exact GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all | (intros; apply GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.haar_chart_integral_comparison : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)), IsCompact Q → IsCompact S → (∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | exact GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | (intros; apply GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.poincare_value_bound_on_cube : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℝ), 0 < ε →
    ∃ (T : Finset (List ι)) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (U : Set (ι → ℝ)) (F : (ι → ℝ) → V), IsOpen U → Set.Icc (0 : ι → ℝ) (fun _ => ε) ⊆ U → ContDiffOn ℝ ∞ F U →
        ‖F 0‖ ^ 2 ≤ C * ∑ L ∈ T, ∫ t in Set.Icc (0 : ι → ℝ) (fun _ => ε), ‖pd L F t‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SobCube.sobolev_cube | exact GlobalTheory.CompanionTheory.SobCube.sobolev_cube | (intros; apply GlobalTheory.CompanionTheory.SobCube.sobolev_cube <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Nonv

theorem ltIter_succ_eq {B : Type} [CommRing B] (ϖ : B) (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q := by
  simp only [ltIter, Function.iterate_succ_apply']

theorem norm_step_eq {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q)
    (h : ‖c‖ ^ (q - 1) < ‖a‖) : ‖a * c + c ^ q‖ = ‖a‖ * ‖c‖ := by
  by_cases hc : c = 0
  · subst hc
    have : q ≠ 0 := by omega
    simp [this]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hlt : ‖c ^ q‖ < ‖a * c‖ := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      rw [norm_pow, norm_mul, pow_succ]
      simp only [Nat.add_sub_cancel] at h
      exact mul_lt_mul_of_pos_right h hcpos
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt), max_eq_left hlt.le, norm_mul]

theorem norm_step_le {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q) :
    ‖a * c + c ^ q‖ ≤ max ‖a‖ (‖c‖ ^ (q - 1)) * ‖c‖ := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [norm_mul, norm_pow, pow_succ, max_mul_of_nonneg _ _ (norm_nonneg c)]

theorem exists_norm_geometric {C : Type} [NormedField C] [IsUltrametricDist C] (a : C) (q : ℕ) (hq : 2 ≤ q)
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) (c : ℕ → C) (hc : ∀ n, c (n + 1) = a * c n + c n ^ q)
    (h0 : ‖c 0‖ < 1) : ∃ n, ∀ j, ‖c (n + j)‖ = ‖a‖ ^ j * ‖c n‖ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set ρ := max ‖a‖ (‖c 0‖ ^ (q - 1)) with hρ
  have hρ1 : ρ < 1 := max_lt ha (pow_lt_one₀ (norm_nonneg _) h0 (by omega))
  have hρ0 : 0 ≤ ρ := hapos.le.trans (le_max_left _ _)
  have hdec : ∀ n, ‖c n‖ ≤ ρ ^ n * ‖c 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : ‖c n‖ ≤ ‖c 0‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le))
      have hm : max ‖a‖ (‖c n‖ ^ (q - 1)) ≤ ρ :=
        max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hle _)
      rw [hc n]
      calc ‖a * c n + c n ^ q‖ ≤ max ‖a‖ (‖c n‖ ^ (q - 1)) * ‖c n‖ := norm_step_le a _ q hq
        _ ≤ ρ * (ρ ^ n * ‖c 0‖) := mul_le_mul hm ih (norm_nonneg _) hρ0
        _ = ρ ^ (n + 1) * ‖c 0‖ := by ring
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hapos hρ1
  have hcn : ‖c n‖ < ‖a‖ :=
    ((hdec n).trans (mul_le_of_le_one_right (pow_nonneg hρ0 n) h0.le)).trans_lt hn
  have hsmall : ∀ x : C, ‖x‖ ≤ ‖c n‖ → ‖x‖ ^ (q - 1) < ‖a‖ := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := hx.trans (hcn.trans ha).le
    exact ((pow_le_of_le_one (norm_nonneg _) hx1 (by omega)).trans hx).trans_lt hcn
  refine ⟨n, fun j => ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hle : ‖c (n + j)‖ ≤ ‖c n‖ := by
      rw [ih]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hapos.le ha.le)
    rw [← add_assoc, hc (n + j), norm_step_eq a _ q hq (hsmall _ hle), ih]
    ring

variable {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}

theorem ltIter_mem (hE : PerEnv S F ϖ) (q : ℕ) {Q : B} (hQ : Q ∈ S) (n : ℕ) : ltIter ϖ q n Q ∈ S := by
  induction n with
  | zero => simpa [ltIter] using hQ
  | succ n ih =>
    rw [ltIter_succ_eq]
    exact S.add_mem (S.mul_mem hE.mem ih) (S.pow_mem ih q)

theorem ltIter_mem_succ (hE : PerEnv S F ϖ) (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (q : ℕ) (hq : 2 ≤ q) {Q : B} (hQ : Q ∈ S)
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) (n m : ℕ) (hm : 1 ≤ m)
    (hy : ltIter ϖ q n Q ∈ F m) : ltIter ϖ q n Q ∈ F (m + 1) := by
  have hanti : Antitone F := antitone_nat_of_succ_le hE.anti
  have hD : ∀ j, ltIter ϖ q (n + j) Q - ϖ ^ j * ltIter ϖ q n Q ∈ F (m + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hym : ltIter ϖ q (n + j) Q ∈ F m := by
        have h1 := (F m).add_mem (hE.anti m ih) ((F m).mul_mem_left (ϖ ^ j) hy)
        simpa using h1
      have hsq : ltIter ϖ q (n + j) Q * ltIter ϖ q (n + j) Q ∈ F (m + 1) :=
        hanti (by omega : m + 1 ≤ m + m) (hE.mul_le m m (Ideal.mul_mem_mul hym hym))
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
      have he : ltIter ϖ (r + 2) (n + (j + 1)) Q - ϖ ^ (j + 1) * ltIter ϖ (r + 2) n Q =
          ϖ * (ltIter ϖ (r + 2) (n + j) Q - ϖ ^ j * ltIter ϖ (r + 2) n Q) +
            ltIter ϖ (r + 2) (n + j) Q ^ r * (ltIter ϖ (r + 2) (n + j) Q * ltIter ϖ (r + 2) (n + j) Q) := by
        rw [← add_assoc, ltIter_succ_eq]
        ring
      rw [he]
      exact (F (m + 1)).add_mem ((F (m + 1)).mul_mem_left _ ih) ((F (m + 1)).mul_mem_left _ hsq)
  obtain ⟨c, hc⟩ := hT (m + 1)
  refine hE.closed (m + 1) _ (ltIter_mem hE q hQ n) fun M => ?_
  obtain ⟨N, hN⟩ := hc (M + c)
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  refine ⟨ϖ ^ n * s, S.mul_mem (S.pow_mem hE.mem n) hs, ?_⟩
  have h1 : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h2 : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h3 : ϖ ^ N * ϖ' ^ N = 1 := by rw [← mul_pow, hϖ, one_pow]
  have he : ltIter ϖ q n Q - ϖ ^ M * (ϖ ^ n * s) =
      ϖ ^ n * ϖ' ^ c * (ϖ ^ c * (ϖ' ^ (n + N) * ltIter ϖ q (n + N) Q - 0) - ϖ ^ (M + c) * s) -
        ϖ' ^ N * (ltIter ϖ q (n + N) Q - ϖ ^ N * ltIter ϖ q n Q) := by
    linear_combination (-ltIter ϖ q n Q) * h3 +
      (ϖ ^ M * ϖ ^ n * s - ϖ' ^ N * ltIter ϖ q (n + N) Q * (ϖ ^ n * ϖ' ^ n)) * h1 -
      ϖ' ^ N * ltIter ϖ q (n + N) Q * h2
  rw [he]
  exact (F (m + 1)).sub_mem ((F (m + 1)).mul_mem_left _ hd) ((F (m + 1)).mul_mem_left _ (hD N))

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem exists_ltIter_mem_one (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (θ : B →+* C) (hθ : ∀ x, θ x = 0 ↔ x ∈ F 1)
    (hS : ∀ s ∈ S, ‖θ s‖ ≤ 1) (ha : ‖θ ϖ‖ < 1) (q : ℕ) (hq : 2 ≤ q) (Q : B) (hQ : Q ∈ S)
    (hQM : ∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M))
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) : ∃ n, ltIter ϖ q n Q ∈ F 1 := by
  have haa : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
  have ha0 : θ ϖ ≠ 0 := left_ne_zero_of_mul_eq_one haa
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr ha0
  have hnn : ‖θ ϖ‖ * ‖θ ϖ'‖ = 1 := by rw [← norm_mul, haa, norm_one]
  have hpos' : 0 < ‖θ ϖ'‖ := by
    have := right_ne_zero_of_mul_eq_one haa
    exact norm_pos_iff.mpr this
  have h0 : ‖θ (ltIter ϖ q 0 Q)‖ < 1 := by
    obtain ⟨M, hM, s, hs, hd⟩ := hQM
    have e : θ Q ^ M = θ ϖ * θ s := by
      have := (hθ _).mpr hd
      simp only [map_sub, map_mul, map_pow, pow_one] at this
      exact sub_eq_zero.mp this
    by_contra hcon
    have h1 : (1 : ℝ) ≤ ‖θ Q‖ := by simpa [ltIter] using hcon
    have h2 : (1 : ℝ) ≤ ‖θ Q‖ ^ M := one_le_pow₀ h1
    have h3 : ‖θ Q‖ ^ M = ‖θ ϖ‖ * ‖θ s‖ := by rw [← norm_pow, e, norm_mul]
    have h4 : ‖θ ϖ‖ * ‖θ s‖ < 1 :=
      (mul_le_of_le_one_right hapos.le (hS s hs)).trans_lt ha
    linarith
  obtain ⟨n, hn⟩ := exists_norm_geometric (θ ϖ) q hq ha0 ha (fun n => θ (ltIter ϖ q n Q))
    (fun n => by simp only [ltIter_succ_eq, map_add (f := _), map_mul, map_pow]) h0
  refine ⟨n, (hθ _).mp ?_⟩
  by_contra hne
  have hcpos : 0 < ‖θ (ltIter ϖ q n Q)‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := hT 1
  have hK : 0 < ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hK ha
  obtain ⟨N, hN⟩ := hc m
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  have e := (hθ _).mpr hd
  simp only [map_sub, map_mul, map_pow, map_zero, sub_zero] at e
  have e2 : ‖θ ϖ‖ ^ c * (‖θ ϖ'‖ ^ (n + N) * ‖θ (ltIter ϖ q (n + N) Q)‖) = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    have := congrArg norm (sub_eq_zero.mp e)
    simpa only [norm_mul, norm_pow] using this
  have hNN : ‖θ ϖ‖ ^ N * ‖θ ϖ'‖ ^ N = 1 := by rw [← mul_pow, hnn, one_pow]
  have e3 : ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    rw [← e2, hn N, pow_add]
    linear_combination (-(‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖)) * hNN
  have h5 : ‖θ ϖ‖ ^ m * ‖θ s‖ ≤ ‖θ ϖ‖ ^ m :=
    mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hs)
  linarith

end GlobalTheory.CompanionTheory.LTPer.Nonv

namespace GlobalTheory.CompanionTheory.LTPer


open GlobalTheory.CompanionTheory.LTPer.Nonv in
theorem exists_ltIter_eq_zero_of_tends : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0 → ∃ n, ltIter ϖ q n Q = 0 := by
  intro B _ S F ϖ C _ _ hE ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  obtain ⟨n, hn⟩ := exists_ltIter_mem_one ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  refine ⟨n, hE.sep _ fun k => ?_⟩
  have hall : ∀ m, 1 ≤ m → ltIter ϖ q n Q ∈ F m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hn
    | succ m hm ih => exact ltIter_mem_succ hE ϖ' hϖ q hq hQ hT n m hm ih
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hE.top]; exact Submodule.mem_top
  · exact hall k hk

end GlobalTheory.CompanionTheory.LTPer
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem theta_period_eq_zero_of_theta_eq_zero :
    ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q, θ Q = 0 → ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → θ t = 0 := by
  intro B _ S F ϖ C _ _ ϖ' hϖ θ hker hS hlt q hq Q hQ t ht
  have hy : ∀ n, θ (ltIter ϖ q n Q) = 0 := by
    intro n
    induction n with
    | zero => simpa [ltIter] using hQ
    | succ n ih =>
      have hs : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + (ltIter ϖ q n Q) ^ q := by
        simp only [ltIter, Function.iterate_succ_apply']
      rw [hs, map_add (f := _), map_mul, map_pow, ih]
      simp [show q ≠ 0 by omega]
  have hne : θ ϖ ≠ 0 := by
    intro h0
    have h1 : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := ht 1
  have hbound : ∀ m : ℕ, ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ ‖θ ϖ‖ ^ m := by
    intro m
    obtain ⟨N, hN⟩ := hc m
    obtain ⟨s, hsS, hs⟩ := hN N le_rfl
    have h0 := (hker _).mpr hs
    simp only [map_sub, map_mul, map_pow, hy, mul_zero, zero_sub] at h0
    have h1 : θ ϖ ^ c * θ t = -(θ ϖ ^ m * θ s) := by linear_combination -h0
    have h2 : ‖θ ϖ‖ ^ c * ‖θ t‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
      have := congrArg norm h1
      simpa [norm_mul, norm_pow, norm_neg] using this
    rw [h2]
    exact mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hsS)
  have hlim : Filter.Tendsto (fun m : ℕ => ‖θ ϖ‖ ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hapos.le hlt
  have hle : ‖θ ϖ‖ ^ c * ‖θ t‖ ≤ 0 := ge_of_tendsto' hlim hbound
  have hz : ‖θ t‖ ≤ 0 := by
    by_contra hcon
    have : 0 < ‖θ ϖ‖ ^ c * ‖θ t‖ := mul_pos (pow_pos hapos c) (not_le.mp hcon)
    linarith
  exact norm_le_zero_iff.mp hz

end GlobalTheory.CompanionTheory.LTPer
end
end
