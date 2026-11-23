module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Continuity
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Order.ModularLattice
public import Mathlib.MeasureTheory.Group.FundamentalDomain

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma re_det_gram_mul_eq_normSq_det_mul {r i : ℕ} (B : Matrix (Fin r) (Fin i) ℂ)
    (X : Matrix (Fin i) (Fin i) ℂ) :
    ((B * X)ᴴ * (B * X)).det.re = Complex.normSq X.det * (Bᴴ * B).det.re := by
  have h : (B * X)ᴴ * (B * X) = Xᴴ * (Bᴴ * B) * X := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [h, det_mul, det_mul, det_conjTranspose, Complex.star_def,
    show (starRingEnd ℂ) X.det * (Bᴴ * B).det * X.det
      = ((Complex.normSq X.det : ℝ) : ℂ) * (Bᴴ * B).det by
        rw [Complex.normSq_eq_conj_mul_self]; ring,
    Complex.re_ofReal_mul]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma norm_apply_le_one_of_conjTranspose_mul_self_eq_one {r i : ℕ} (Q : Matrix (Fin r) (Fin i) ℂ)
    (hQ : Qᴴ * Q = 1) (j : Fin r) (k : Fin i) : ‖Q j k‖ ≤ 1 := by
  have h := congrFun (congrFun hQ k) k
  simp only [Matrix.mul_apply, conjTranspose_apply, one_apply_eq] at h
  have h' : ∑ l, Complex.normSq (Q l k) = 1 := by
    have : ∑ l, ((Complex.normSq (Q l k) : ℝ) : ℂ) = 1 := by
      rw [← h]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    exact_mod_cast this
  have hle : Complex.normSq (Q j k) ≤ 1 :=
    h' ▸ Finset.single_le_sum (fun l _ => Complex.normSq_nonneg (Q l k)) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at hle
  nlinarith [norm_nonneg (Q j k)]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma exists_mul_right_orthonormal_of_re_det_gram_pos {r i : ℕ} (M : Matrix (Fin r) (Fin i) ℂ)
    (hM : 0 < (Mᴴ * M).det.re) :
    ∃ X : Matrix (Fin i) (Fin i) ℂ, (M * X)ᴴ * (M * X) = 1 := by
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self M
  have hunit : IsUnit (Mᴴ * M) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h; rw [h] at hM; simp at hM
  have hPD := hPSD.posDef_iff_isUnit.mpr hunit
  have hpos := hPD.eigenvalues_pos
  have hspec := hPD.1.spectral_theorem
  have hUU : star (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) *
      (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hPD.1.eigenvectorUnitary.2
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  generalize hPD.1.eigenvalues = lam at hpos hspec
  generalize (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) = U at hspec hUU
  refine ⟨U * diagonal (fun k => ((Real.sqrt (lam k))⁻¹ : ℂ)), ?_⟩
  have e1 : ∀ X : Matrix (Fin i) (Fin i) ℂ, (M * X)ᴴ * (M * X) = Xᴴ * (Mᴴ * M) * X := by
    intro X; simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hspec, conjTranspose_mul, ← star_eq_conjTranspose U]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
    Matrix.one_mul, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext k
  have hk := hpos k
  have hs0 : ((Real.sqrt (lam k) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hs' : ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) = (lam k : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hk.le
  change star ((Real.sqrt (lam k) : ℂ))⁻¹ * (((lam k : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℂ))⁻¹) = 1
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal, ← hs']
  field_simp

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma exists_pos_uniform_le_sum_log_ratio_det_gram {r i : ℕ}
    (S : Finset (Matrix (Fin r) (Fin r) ℂ))
    (hpt : ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (Mᴴ * M).det.re →
      (∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re) ∧
      0 < ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re)) :
    ∃ η : ℝ, 0 < η ∧ ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (Mᴴ * M).det.re →
      η ≤ ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) := by
  set F : Matrix (Fin r) (Fin i) ℂ → ℝ :=
    fun M => ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) with hF
  set K : Set (Matrix (Fin r) (Fin i) ℂ) := {Q | Qᴴ * Q = 1} with hK
  have hK1 : ∀ Q ∈ K, 0 < (Qᴴ * Q).det.re := by
    intro Q hQ
    rw [show Qᴴ * Q = 1 from hQ]
    simp
  have hinv : ∀ (M : Matrix (Fin r) (Fin i) ℂ) (X : Matrix (Fin i) (Fin i) ℂ),
      (M * X)ᴴ * (M * X) = 1 → F (M * X) = F M := by
    intro M X hX
    have hone : Complex.normSq X.det * (Mᴴ * M).det.re = 1 := by
      rw [← re_det_gram_mul_eq_normSq_det_mul, hX]; simp
    have hs : Complex.normSq X.det ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hone; exact zero_ne_one hone
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show a * (M * X) = a * M * X from (Matrix.mul_assoc _ _ _).symm,
      re_det_gram_mul_eq_normSq_det_mul, re_det_gram_mul_eq_normSq_det_mul, mul_div_mul_left _ _ hs]
  have hgram : ∀ B : Matrix (Fin r) (Fin i) ℂ → Matrix (Fin r) (Fin i) ℂ, Continuous B →
      Continuous fun Q => ((B Q)ᴴ * B Q).det.re := by
    intro B hB
    exact Complex.continuous_re.comp
      ((hB.matrix_conjTranspose.matrix_mul hB).matrix_det)
  have hclosed : IsClosed K :=
    isClosed_eq ((continuous_id.matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have hcomp : IsCompact K := by
    refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hclosed ?_
    intro Q hQ
    simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, forall_const]
    exact fun j k => norm_apply_le_one_of_conjTranspose_mul_self_eq_one Q hQ j k
  have hcont : ContinuousOn F K := by
    refine continuousOn_finsetSum _ fun a _ => ?_
    refine ContinuousOn.log ?_ ?_
    · refine ((hgram _ (continuous_const.matrix_mul continuous_id)).continuousOn).div
        (hgram _ continuous_id).continuousOn ?_
      exact fun Q hQ => (hK1 Q hQ).ne'
    · intro Q hQ
      exact (div_pos ((hpt Q (hK1 Q hQ)).1 a ‹_›) (hK1 Q hQ)).ne'
  by_cases hne : K.Nonempty
  · obtain ⟨Q₀, hQ₀, hmin⟩ := hcomp.exists_isMinOn hne hcont
    refine ⟨F Q₀, (hpt Q₀ (hK1 Q₀ hQ₀)).2, fun M hM => ?_⟩
    obtain ⟨X, hX⟩ := exists_mul_right_orthonormal_of_re_det_gram_pos M hM
    show F Q₀ ≤ F M
    rw [← hinv M X hX]
    exact hmin (show M * X ∈ K from hX)
  · refine ⟨1, one_pos, fun M hM => ?_⟩
    obtain ⟨X, hX⟩ := exists_mul_right_orthonormal_of_re_det_gram_pos M hM
    exact absurd ⟨M * X, hX⟩ hne


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
theorem _root_.GlobalTheory.uniform_log_expansion_of_pointwise :
    (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, 0 < (((a * M)ᴴ * (a * M)).det.re)) ∧ 0 < ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ η : ℝ, 0 < η ∧ ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → η ≤ ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  intro hpt r S hS hirr
  have key : ∀ i : ℕ, ∃ η : ℝ, 0 < η ∧ (0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ,
      0 < (Mᴴ * M).det.re →
      η ≤ ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re)) := by
    intro i
    by_cases hi : 0 < i ∧ i < r
    · obtain ⟨η, hη, h⟩ := exists_pos_uniform_le_sum_log_ratio_det_gram S
        (fun M hM => hpt r S hS hirr i hi.1 hi.2 M hM)
      exact ⟨η, hη, fun _ _ => h⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hi⟩
  choose η hη hb using key
  have hmem1 : (1 : ℝ) ∈ (Finset.range r).image η ∪ {1} :=
    Finset.mem_union_right _ (Finset.mem_singleton_self 1)
  refine ⟨((Finset.range r).image η ∪ {1}).min' ⟨1, hmem1⟩, ?_, ?_⟩
  · rcases Finset.mem_union.mp (Finset.min'_mem _ ⟨1, hmem1⟩) with hy | hy
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hy
      rw [← hj]
      exact hη j
    · rw [Finset.mem_singleton.mp hy]; exact one_pos
  · intro i hi hir M hM
    exact (Finset.min'_le _ _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem η (Finset.mem_range.mpr hir)))).trans (hb i hi hir M hM)

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem gramDet_contraction : (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ η : ℝ, 0 < η ∧ ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → η ≤ ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) → (∀ (N : ℕ) (ω η : ℝ), 1 ≤ ω → 0 < η → ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ ∀ (σ : Type) (S : Finset σ) (t : σ → ℝ), S.card = N → (∀ s ∈ S, ω⁻¹ ≤ t s ∧ t s ≤ ω) → η ≤ ∑ s ∈ S, Real.log (t s) → ∑ s ∈ S, t s ^ (-δ) ≤ N * c) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) := by
  intro h1 h2 h3 r S hS hirr
  choose w hw1 hw using h1 r
  obtain ⟨η, hη, hη2⟩ := h2 r S hS hirr
  have hw0 : ∀ a, 0 ≤ w a := fun a => le_trans zero_le_one (hw1 a)
  have hΩ1 : (1:ℝ) ≤ 1 + ∑ a ∈ S, w a := by
    have := Finset.sum_nonneg (s := S) (fun a _ => hw0 a)
    linarith
  have hwΩ : ∀ a ∈ S, w a ≤ 1 + ∑ a ∈ S, w a := by
    intro a ha
    have := Finset.single_le_sum (s := S) (fun a _ => hw0 a) ha
    linarith
  generalize (1 + ∑ a ∈ S, w a) = Ω at hΩ1 hwΩ
  obtain ⟨δ, c, hδ, hc0, hc1, hc⟩ := h3 S.card Ω η hΩ1 hη
  refine ⟨δ, c, Ω, hδ, hc0, hc1, hΩ1, ?_⟩
  intro i M hM
  have hΩ0 : 0 < Ω := lt_of_lt_of_le one_pos hΩ1
  have key : ∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ Ω * (((M)ᴴ * (M)).det.re) ∧
      (((M)ᴴ * (M)).det.re) ≤ Ω * (((a * M)ᴴ * (a * M)).det.re) := by
    intro a ha
    obtain ⟨-, hdet, hinv⟩ := hS a ha
    refine ⟨(hw a (Fin i) M).trans (mul_le_mul_of_nonneg_right (hwΩ a ha) hM.le), ?_⟩
    have h := hw a⁻¹ (Fin i) (a * M)
    have e : a⁻¹ * (a * M) = M := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mul]
    rw [e] at h
    have hpos : 0 < (((a * M)ᴴ * (a * M)).det.re) := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos (hw0 a⁻¹) (not_lt.mp hn)
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right (hwΩ _ hinv) hpos.le)
  refine ⟨key, fun hi hir => ?_⟩
  refine hc _ S (fun a => (((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) rfl ?_
    (hη2 i hi hir M hM)
  intro a ha
  obtain ⟨k1, k2⟩ := key a ha
  refine ⟨?_, (div_le_iff₀ hM).mpr k1⟩
  rw [le_div_iff₀ hM, inv_mul_le_iff₀ hΩ0]
  exact k2

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem offDiagonal_matrixUnits_irreducible :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ),
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
        (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤) := by
  intro r p hp hpr W h
  have hs : ∀ (j k : Fin r) (v : Fin r → ℂ),
      (Matrix.single j k (1 : ℂ)).mulVec v = v k • (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    intro j k v
    ext i
    rw [Matrix.single_mulVec]
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  have key : ∀ (j k : Fin r) (v : Fin r → ℂ), v k ≠ 0 →
      (Matrix.single j k (1 : ℂ)).mulVec v ∈ W → (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro j k v hv hm
    rw [hs] at hm
    exact (W.smul_mem_iff hv).1 hm
  have up : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v k ≠ 0 →
      (Pi.single j (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvk => key j k v hvk (h j k hj hk v hv).1
  have down : ∀ (j k : Fin r) (v : Fin r → ℂ), (j : ℕ) < p → p ≤ (k : ℕ) → v ∈ W → v j ≠ 0 →
      (Pi.single k (1 : ℂ) : Fin r → ℂ) ∈ W :=
    fun j k v hj hk hv hvj => key k j v hvj (h j k hj hk v hv).2
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : v k ≠ 0 := hk
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨p, hpr⟩
  have ha : (a : ℕ) < p := hp
  have hb : p ≤ (b : ℕ) := le_rfl
  have hbW : (Pi.single b (1 : ℂ) : Fin r → ℂ) ∈ W := by
    rcases lt_or_ge (k : ℕ) p with hkp | hkp
    · exact down k b v hkp hb hv hk'
    · exact down a b _ ha hb (up a k v ha hkp hv hk') (by simp)
  have haW : (Pi.single a (1 : ℂ) : Fin r → ℂ) ∈ W := up a b _ ha hb hbW (by simp)
  have hall : ∀ i : Fin r, (Pi.single i (1 : ℂ) : Fin r → ℂ) ∈ W := by
    intro i
    rcases lt_or_ge (i : ℕ) p with hi | hi
    · exact up i b _ hi hb hbW (by simp)
    · exact down a i _ ha hi haW (by simp)
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem relIndex_sup_mul_relIndex_inf_same {A : Type} [AddCommGroup A] (M L N : AddSubgroup A)
    (h : M ≤ L) :
    (M ⊔ N).relIndex (L ⊔ N) * (M ⊓ N).relIndex (L ⊓ N) = M.relIndex L := by
  have h1 : (M ⊔ N).relIndex (L ⊔ N) = (M ⊔ (N ⊓ L)).relIndex L := by
    have e : L ⊔ N = L ⊔ (M ⊔ N) := by
      rw [← sup_assoc, sup_eq_left.mpr h]
    rw [e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (M ⊔ N) L,
      sup_inf_assoc_of_le N h]
  have h2 : (M ⊓ N).relIndex (L ⊓ N) = M.relIndex (M ⊔ (N ⊓ L)) := by
    have e : M ⊓ N = M ⊓ (L ⊓ N) := by
      rw [← inf_assoc, inf_eq_left.mpr h]
    rw [e, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_sup_left, inf_comm]
  rw [h1, h2, mul_comm]
  exact AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le h inf_le_right)

theorem relIndex_sup_mul_relIndex_inf :
    (∀ (A : Type) [AddCommGroup A] (M₁ L₁ M₂ L₂ : AddSubgroup A), M₁ ≤ L₁ → M₂ ≤ L₂ →
      (M₁ ⊔ M₂).relIndex (L₁ ⊔ L₂) * (M₁ ⊓ M₂).relIndex (L₁ ⊓ L₂) =
        M₁.relIndex L₁ * M₂.relIndex L₂) := by
  intro A _ M₁ L₁ M₂ L₂ h₁ h₂
  have a := relIndex_sup_mul_relIndex_inf_same M₁ L₁ M₂ h₁
  have b := relIndex_sup_mul_relIndex_inf_same M₂ L₂ L₁ h₂
  rw [sup_comm M₂, sup_comm L₂, inf_comm M₂, inf_comm L₂] at b
  rw [← a, ← b,
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊔ M₂) (L₁ ⊔ M₂) (L₁ ⊔ L₂)
      (sup_le_sup_right h₁ _) (sup_le_sup_left h₂ _),
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊓ M₂) (L₁ ⊓ M₂) (L₁ ⊓ L₂)
      (inf_le_inf_right _ h₁) (inf_le_inf_left _ h₂)]
  ring

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_relCompl_submodule {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U W : Submodule K V} (h : U ≤ W) : ∃ C : Submodule K V, Disjoint U C ∧ U ⊔ C = W := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  refine ⟨C ⊓ W, hC.disjoint.mono_right inf_le_left, ?_⟩
  rw [← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]

theorem exists_fin_independent_span_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) :
    ∃ (n : ℕ) (v : Fin n → V), LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasis K S
  refine ⟨_, S.subtype ∘ b, b.linearIndependent.map' S.subtype (Submodule.ker_subtype S), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

theorem exists_basis_adapted_two_subspaces (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W₁ W₂ : Submodule K V) :
    ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → V), LinearIndependent K w ∧
      Submodule.span K (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧
      Submodule.span K (Set.range w) = W₁ ⊔ W₂ := by
  obtain ⟨C₁, hd₁, hs₁⟩ := exists_relCompl_submodule (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
  obtain ⟨C₂, hd₂, hs₂⟩ := exists_relCompl_submodule (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
  obtain ⟨a, u, hu, hus⟩ := exists_fin_independent_span_eq (W₁ ⊓ W₂)
  obtain ⟨b, v₁, hv₁, hvs₁⟩ := exists_fin_independent_span_eq C₁
  obtain ⟨c, v₂, hv₂, hvs₂⟩ := exists_fin_independent_span_eq C₂
  have hC₁ : C₁ ≤ W₁ := hs₁ ▸ le_sup_right
  have hC₂ : C₂ ≤ W₂ := hs₂ ▸ le_sup_right
  have h12 : Disjoint C₁ C₂ := by
    rw [Submodule.disjoint_def]
    intro x hx₁ hx₂
    exact (Submodule.disjoint_def.1 hd₁) x ⟨hC₁ hx₁, hC₂ hx₂⟩ hx₁
  have hU : Disjoint (W₁ ⊓ W₂) (C₁ ⊔ C₂) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hz1 : z ∈ W₁ := by
      have := W₁.sub_mem hx.1 (hC₁ hy)
      simpa using this
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd₂) z ⟨hz1, hC₂ hz⟩ hz
    subst hz0
    rw [add_zero] at hx ⊢
    exact (Submodule.disjoint_def.1 hd₁) y hx hy
  have hv : LinearIndependent K (Sum.elim v₁ v₂) :=
    hv₁.sum_type hv₂ (by rw [hvs₁, hvs₂]; exact h12)
  have hvs : Submodule.span K (Set.range (Sum.elim v₁ v₂)) = C₁ ⊔ C₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hvs₁, hvs₂]
  refine ⟨a, b, c, Sum.elim u (Sum.elim v₁ v₂),
    hu.sum_type hv (by rw [hus, hvs]; exact hU), ?_, ?_, ?_, ?_⟩
  · rw [Sum.elim_comp_inl, hus]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inl = Sum.elim u v₁ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₁, hs₁]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inr = Sum.elim u v₂ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₂, hs₂]
  · rw [Set.Sum.elim_range, Submodule.span_union, hus, hvs, sup_sup_distrib_left, hs₁, hs₂]

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem fundamentalSet_lintegral_mul_right_and_measure_le :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) := by
  intro G _ _ _ _ _ _ _ _ ν _ Γ _ F hF hex
  have hFD : IsFundamentalDomain Γ F ν :=
    IsFundamentalDomain.mk' hF.nullMeasurableSet (fun g => hex g)
  refine ⟨?_, ?_⟩
  · intro h hh φ hφ hinv
    have hmeas : MeasurableSet {g : G | g * h⁻¹ ∈ F} := (measurable_mul_const h⁻¹) hF
    have hFD' : IsFundamentalDomain Γ {g : G | g * h⁻¹ ∈ F} ν := by
      refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet (fun g => ?_)
      have := hex (g * h⁻¹)
      simpa [Subgroup.smul_def, mul_assoc] using this
    have h1 : ∫⁻ g in {g : G | g * h⁻¹ ∈ F}, φ g ∂ν = ∫⁻ g in F, φ (g * h) ∂ν := by
      conv_lhs => rw [← hh]
      rw [setLIntegral_map hmeas hφ (measurable_mul_const h)]
      congr 2
      ext g
      simp
    rw [← h1]
    exact hFD'.setLIntegral_eq hFD φ (fun γ g => hinv γ γ.2 g)
  · intro K hK
    rw [hFD.measure_eq_tsum K]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro g ⟨hg, γ, hγ, k, hk, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hg⟩

end GlobalTheory
end
