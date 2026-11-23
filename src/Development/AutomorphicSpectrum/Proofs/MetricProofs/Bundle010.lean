module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinors
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolyTowtBound
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle008
public import Mathlib.Analysis.Matrix.Order
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle010
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001

@[expose] public section

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.flag_domain_unitary_triangular : ∀ (N j : ℕ), j ≤ N → ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∃ u b : Matrix (Fin N) (Fin N) ℂ, gramOf (sigForm N j) u = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) ∧ b.BlockTriangular id ∧ IsUnit b.det ∧ u * g = b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag | exact GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

local notation "coeff" m:arg P:arg => AddMonoidAlgebra.coeff P m


theorem _root_.GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ, (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWt Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWt Q)| ≤ Cst * M)) ∧ ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWtS Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWtS Q)| ≤ Cst * M) := by
  classical
  intro Ψ _ N n
  have substitution_bound (σ : Type) [Finite σ] (f : σ → MvPolynomial σ ℝ)
      (hf : ∀ i, (f i).IsHomogeneous 1) :
      ∃ C : ℝ, ∀ (Q : MvPolynomial σ ℝ) (M : ℝ), Q.IsHomogeneous n →
        (aeval f Q).IsHomogeneous n ∧
          ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (aeval f Q)| ≤ C * M) := by
    let S : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset
    let image (d : σ →₀ ℕ) := aeval f (monomial d (1 : ℝ))
    let B (d : σ →₀ ℕ) := ∑ e ∈ (image d).support, |coeff e (image d)|
    have hB (d : σ →₀ ℕ) : 0 ≤ B d := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨∑ d ∈ S, B d, fun Q M hQ => ⟨?_, fun hM m => ?_⟩⟩
    · simpa only [one_mul] using hQ.aeval f hf
    · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      have hsub : Q.support ⊆ S := by
        intro d hd
        simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        by_contra h
        exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero h)
      have hcoeff (d : σ →₀ ℕ) : |coeff m (image d)| ≤ B d := by
        by_cases hm : m ∈ (image d).support
        · exact Finset.single_le_sum (f := fun e => |coeff e (image d)|)
            (fun _ _ => abs_nonneg _) hm
        · rw [notMem_support_iff.mp hm, abs_zero]
          exact hB d
      have hexpand : coeff m (aeval f Q) =
          ∑ d ∈ Q.support, coeff d Q * coeff m (image d) := by
        calc
          _ = coeff m (aeval f (∑ d ∈ Q.support, monomial d (coeff d Q))) :=
            congrArg (fun P => coeff m (aeval f P)) Q.as_sum
          _ = _ := by
            simp only [map_sum, coeff_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            have hmonomial : monomial d (coeff d Q) =
                MvPolynomial.C (coeff d Q) * monomial d (1 : ℝ) := by
              rw [C_mul_monomial, mul_one]
            rw [hmonomial, map_mul, aeval_C, algebraMap_eq, coeff_C_mul]
      rw [hexpand]
      calc
        _ ≤ ∑ d ∈ Q.support, |coeff d Q * coeff m (image d)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Q.support, B d * M := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul (hcoeff d) (hM d) (abs_nonneg _) (hB d)
        _ ≤ ∑ d ∈ S, B d * M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => mul_nonneg (hB d) hM0
        _ = _ := Finset.sum_mul .. |>.symm
  have gapX_hom := @PositivityTheory.Xgp.poly_towt_bound.gapX_hom Ψ N
  obtain ⟨C1, H1⟩ := substitution_bound (Ψ × Fin N) gapX gapX_hom
  obtain ⟨C2, H2⟩ := substitution_bound (Option (Ψ × Fin N))
    (fun o => o.elim (X none) fun p => rename some (gapX p)) (by
      rintro (_ | p)
      · exact isHomogeneous_X ℝ _
      · exact (gapX_hom p).rename_isHomogeneous)
  refine ⟨max C1 C2, ?_, ?_⟩
  · intro Q M hQ
    obtain ⟨hHom, hBound⟩ := H1 Q M hQ
    exact ⟨hHom, fun hM m => (hBound hM m).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ((abs_nonneg _).trans (hM 0)))⟩
  · intro Q M hQ
    obtain ⟨hHom, hBound⟩ := H2 Q M hQ
    exact ⟨hHom, fun hM m => (hBound hM m).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) ((abs_nonneg _).trans (hM 0)))⟩
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem toWt_toWtS_homogeneous_coeff_bound :
    ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ,
      (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWt Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWt Q).coeff m| ≤ Cst * M)) ∧
      ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWtS Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWtS Q).coeff m| ≤ Cst * M) :=
  @PositivityTheory.Xgp.t_poly_towt_bound

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.dense_coordinate_torus : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.harmonic_annulus_maximum_principle : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b → ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} → (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) → (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero <;> assumption)
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

section SlopeTestRemainingChoices

open scoped ComplexOrder MatrixOrder

variable {g k : ℕ}

theorem subframe_map_posSemidef {A : Matrix (Fin g) (Fin g) ℝ} (h : A.PosSemidef) :
    (A.map Complex.ofReal).PosSemidef := by
  have hH : (A.map Complex.ofReal).IsHermitian :=
    h.isHermitian.map _ (fun x => by simp [Complex.conj_ofReal])
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => ?_)
  have hu := h.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hv := h.dotProduct_mulVec_nonneg (fun i => (x i).im)
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial] at hu hv
  have key : (star x ⬝ᵥ (A.map Complex.ofReal) *ᵥ x).re =
      ∑ i, ((x i).re * ∑ j, A i j * (x j).re + (x i).im * ∑ j, A i j * (x j).im) := by
    simp only [dotProduct, mulVec, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.map_apply, Complex.mul_re, Complex.re_sum, Complex.im_sum,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [RCLike.im_to_complex] at him
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  rw [key, Finset.sum_add_distrib]
  exact add_nonneg hu hv

theorem subframe_inv_bounds (Y : Matrix (Fin g) (Fin g) ℝ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (h1 : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef)
    (h2 : (D • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) :
    D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ (Y⁻¹).map Complex.ofReal ∧
      (Y⁻¹).map Complex.ofReal ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  have hmap : ∀ {P Q : Matrix (Fin g) (Fin g) ℝ}, P ≤ Q →
      P.map Complex.ofReal ≤ Q.map Complex.ofReal := by
    intro P Q hPQ
    rw [Matrix.le_iff] at hPQ ⊢
    have := subframe_map_posSemidef hPQ
    rwa [Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b)] at this
  have hone : ∀ t : ℝ, (t • (1 : Matrix (Fin g) (Fin g) ℝ)).map Complex.ofReal =
      t • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    intro t; ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Complex.real_smul]
  have hc1 : (c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have hle1 : c • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y := Matrix.le_iff.mpr h1
  have hle2 : Y ≤ D • (1 : Matrix (Fin g) (Fin g) ℝ) := Matrix.le_iff.mpr h2
  have hY : Y.PosDef := GlobalTheory.posDef_of_le hc1 hle1
  have hlo : D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y⁻¹ :=
    GlobalTheory.inv_smul_one_le_inv_of_le_smul_one hY hD hle2
  have hhi : Y⁻¹ ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) := by
    have := GlobalTheory.inv_le_inv_of_posDef_of_le hc1 hle1
    rwa [GlobalTheory.inv_real_smul_of_posDef Matrix.PosDef.one hc.ne', inv_one] at this
  refine ⟨?_, ?_⟩
  · have := hmap hlo
    rwa [hone] at this
  · have := hmap hhi
    rwa [hone] at this

theorem subframe_det_bounds (P : Matrix (Fin g) (Fin k) ℂ) (A : Matrix (Fin g) (Fin g) ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (h1 : a • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ A)
    (h2 : A ≤ b • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    a ^ k * (Pᴴ * P).det.re ≤ (Pᴴ * A * P).det.re ∧
      (Pᴴ * A * P).det.re ≤ b ^ k * (Pᴴ * P).det.re := by
  have hA : A.PosSemidef := GlobalTheory.posSemidef_of_le (Matrix.PosSemidef.one.smul ha) h1
  have hPP : (Pᴴ * P).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self P
  have hsm : ∀ t : ℝ, Pᴴ * (t • (1 : Matrix (Fin g) (Fin g) ℂ)) * P = t • (Pᴴ * P) := by
    intro t; rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hlo : a • (Pᴴ * P) ≤ Pᴴ * A * P := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h1 P
    rwa [hsm] at this
  have hhi : Pᴴ * A * P ≤ b • (Pᴴ * P) := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h2 P
    rwa [hsm] at this
  have hdetsm : ∀ t : ℝ, ((t • (Pᴴ * P)).det).re = t ^ k * ((Pᴴ * P).det).re := by
    intro t
    have he : t • (Pᴴ * P) = (t : ℂ) • (Pᴴ * P) := by
      ext i j; simp [Complex.real_smul]
    rw [he, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  refine ⟨?_, ?_⟩
  · have := GlobalTheory.pow_mul_re_det_le_of_smul_le hPP ha hlo
    simpa [Fintype.card_fin] using this
  · have := GlobalTheory.re_det_le_re_det_of_posSemidef_of_le (hA.conjTranspose_mul_mul_same P) hhi
    rw [RCLike.re_to_complex, RCLike.re_to_complex, hdetsm] at this
    exact this

theorem subframe_gram_posDef (F : Matrix (Fin g) (Fin k) ℂ) (h : F.rank = k) :
    ((F.map star)ᴴ * F.map star).PosDef := by
  have hr : (F.map star).rank = k := by
    have he : F.map star = (Fᴴ)ᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he, Matrix.rank_transpose, Matrix.rank_conjTranspose, h]
  have hr' : Module.finrank ℂ (LinearMap.range (F.map star).mulVecLin) = k := by simpa only [Matrix.finrank_range_mulVecLin] using hr
  have hsum := LinearMap.finrank_range_add_finrank_ker (F.map star).mulVecLin
  rw [Module.finrank_fin_fun, hr'] at hsum
  have hker0 : Module.finrank ℂ (LinearMap.ker (F.map star).mulVecLin) = 0 := by omega
  have hbot : LinearMap.ker (F.map star).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker0
  have hinj : Function.Injective (F.map star).mulVec := by
    intro v w hvw
    have h0 : (F.map star).mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have := (Matrix.ker_mulVecLin_eq_bot_iff.mp hbot) (v - w) h0
    exact sub_eq_zero.mp this
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

theorem subframe_continuous_det :
    Continuous fun M : Matrix (Fin g) (Fin k) ℂ => ((Mᵀ * M.map star).det).re := by
  exact Complex.continuous_re.comp
    ((continuous_id.matrix_transpose.matrix_mul (continuous_id.matrix_map continuous_star)).matrix_det)

end SlopeTestRemainingChoices

theorem subframe_det_log_growth : ∀ (g k : ℕ) (X : Type) [TopologicalSpace X] (K : Set X), IsCompact K → ∀ (F : X → Matrix (Fin g) (Fin k) ℂ), ContinuousOn F K → (∀ x ∈ K, (F x).rank = k) → ∀ c C : ℝ, 0 < c → ∃ C' : ℝ, 0 < C' ∧ ∀ x ∈ K, ∀ (Y : Matrix (Fin g) (Fin g) ℝ) (r : ℝ), 1 ≤ r → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ((C * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → (let d := (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re; d ≤ C' ∧ 1 ≤ C' * r ^ k * d) := by
  intro g k X _ K hK F hF hrank c C hc
  by_cases hne : K.Nonempty
  swap
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hT : ∀ x, ((F x).map star)ᴴ = (F x)ᵀ := by
    intro x; ext i j; simp [Matrix.conjTranspose_apply]
  have hGc : ContinuousOn (fun x => (((F x)ᵀ * (F x).map star).det).re) K :=
    subframe_continuous_det.comp_continuousOn hF
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hGc
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hne hGc
  have hGpos : ∀ x ∈ K, 0 < (((F x)ᵀ * (F x).map star).det).re := by
    intro x hx
    have hpd := subframe_gram_posDef (F x) (hrank x hx)
    rw [hT] at hpd
    have := GlobalTheory.re_det_pos_of_posDef hpd
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m, m = (((F x₀)ᵀ * (F x₀).map star).det).re := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact hGpos x₀ hx₀K
  have hA0 : 0 ≤ c⁻¹ ^ k * |M| := mul_nonneg (pow_nonneg (inv_nonneg.2 hc.le) k) (abs_nonneg M)
  have hB0 : 0 ≤ |C| ^ k / m := div_nonneg (pow_nonneg (abs_nonneg C) k) hmpos.le
  refine ⟨c⁻¹ ^ k * |M| + |C| ^ k / m + 1, by linarith, ?_⟩
  intro x hx Y r hr h1 h2 d
  have hd : d = (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re := rfl
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  · subst hg0
    have hk : k = 0 := by
      have := Matrix.rank_le_height (F x)
      rw [hrank x hx] at this
      omega
    subst hk
    have hd1 : d = 1 := by
      rw [hd, Matrix.det_isEmpty, Complex.one_re]
    rw [hd1]
    simp only [pow_zero, one_mul, mul_one] at hA0 hB0 ⊢
    refine ⟨?_, ?_⟩ <;> linarith
  · have hdiag := (h1.add h2).diag_nonneg (i := ⟨0, hgpos⟩)
    have hcr : c ≤ C * r := by
      simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq] at hdiag
      linarith
    have hCr : 0 < C * r := lt_of_lt_of_le hc hcr
    have hr0 : 0 < r := by linarith
    have hC : 0 < C := by nlinarith
    have hinv := subframe_inv_bounds Y hc hCr h1 h2
    have hb := subframe_det_bounds ((F x).map star) ((Y⁻¹).map Complex.ofReal)
      (inv_nonneg.2 hCr.le) hinv.1 hinv.2
    rw [hT] at hb
    obtain ⟨hlo, hhi⟩ := hb
    have hGx_le : (((F x)ᵀ * (F x).map star).det).re ≤ |M| := by
      have := hM x hx
      simp only [Real.norm_eq_abs] at this
      exact le_trans (le_abs_self _) (le_trans this (le_abs_self M))
    have hGx_ge : m ≤ (((F x)ᵀ * (F x).map star).det).re := by
      have := isMinOn_iff.mp hx₀ x hx
      rw [hm]; exact this
    rw [hd]
    generalize (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re = D at hlo hhi ⊢
    generalize (((F x)ᵀ * (F x).map star).det).re = Gx at hlo hhi hGx_le hGx_ge
    have hpk : 0 < (C * r)⁻¹ ^ k := pow_pos (inv_pos.2 hCr) k
    refine ⟨?_, ?_⟩
    · have h3 : c⁻¹ ^ k * Gx ≤ c⁻¹ ^ k * |M| :=
        mul_le_mul_of_nonneg_left hGx_le (pow_nonneg (inv_nonneg.2 hc.le) k)
      linarith
    · have hDlo : (C * r)⁻¹ ^ k * m ≤ D := le_trans (mul_le_mul_of_nonneg_left hGx_ge hpk.le) hlo
      have hone : |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) = 1 := by
        rw [abs_of_pos hC, inv_pow, mul_pow]
        field_simp
      calc (1 : ℝ) = |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) := hone.symm
        _ ≤ (c⁻¹ ^ k * |M| + |C| ^ k / m + 1) * r ^ k * D := by
          apply mul_le_mul _ hDlo (mul_nonneg hpk.le hmpos.le)
          · exact mul_nonneg (by linarith) (pow_nonneg hr0.le k)
          · exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0.le k)

end GlobalTheory.CompanionTheory.Ar.Flat
end
