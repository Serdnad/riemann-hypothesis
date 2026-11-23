module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_adele_approx_scaled : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  exact @GlobalTheory.EvAdm.exists_rational_rep_scaledInt
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.scaled_indicator_coset_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 → ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | exact GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | (intros; apply GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum <;> assumption)
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  have hA : ∀ i k, ‖A i k‖ ≤ ‖toL A‖ := fun i k =>
    (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  have hB : ∀ i k, ‖B i k‖ ≤ ‖toL B‖ := fun i k =>
    (norm_le_pi_norm (toL B i) k).trans (norm_le_pi_norm (toL B) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖A i k * B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖toL B‖ :=
        Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
          (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (norm_nonneg _))
    _ = a * (‖toL A‖ * ‖toL B‖) := by simp

theorem continuousOn_toL_inv : ContinuousOn (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hd : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
  exact continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hd.unit)

end SlopeTestRemainingChoices

theorem smoothing_mem_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α →
    ∀ f ∈ growth E a, smoothing ν α f ∈ growth E a := by
  intro E _ _ _ a ν _ α hα f hf g
  obtain ⟨C, N, hC⟩ := hf g
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  have hK : IsCompact (tsupport α) := hα.2.1
  obtain ⟨M, M0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ tsupport α, ‖x‖ ≤ M ∧ ‖toL (Matrix.of x)⁻¹‖ ≤ M := by
    obtain ⟨M1, h1⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨M2, h2⟩ := hK.exists_bound_of_continuousOn (continuousOn_toL_inv.mono hα.2.2)
    refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  set c : ℝ := 1 + a * M with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) * M := by positivity
    linarith
  refine ⟨(∫ x, ‖α x‖ ∂ν) * C * c ^ N, N, fun y => ?_⟩
  have hb : ∀ x, ‖α x * chart f (g * infGL E a y) x‖ ≤ ‖α x‖ * (C * c ^ N * height y ^ N) := by
    intro x
    by_cases hx : x ∈ tsupport α
    · obtain ⟨u, hu⟩ : IsUnit (Matrix.of x) := hα.2.2 hx
      have hxu : x = toL u.val := by rw [hu]; rfl
      subst hxu
      obtain ⟨m1, m2⟩ := hM _ hx
      have m2' : ‖toL (u⁻¹).val‖ ≤ M := by rw [Matrix.coe_units_inv]; exact m2
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [chart_val, mul_assoc, ← map_mul]
      refine (hC (y * u)).trans ?_
      have hh : height (y * u) ≤ c * height y := by
        have e2 : ((y * u)⁻¹ : GL (Fin a) (Cinf E)).val = (u⁻¹).val * (y⁻¹).val := by
          rw [_root_.mul_inv_rev]; rfl
        have p1 := norm_toL_mul_le y.val u.val
        have p2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
        have n1 := norm_nonneg (toL y.val)
        have n2 := norm_nonneg (toL (y⁻¹).val)
        have q1 : (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * M * ‖toL y.val‖ := by
          calc (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * (‖toL y.val‖ * M) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m1 n1) (Nat.cast_nonneg a)
            _ = a * M * ‖toL y.val‖ := by ring
        have q2 : (a : ℝ) * (‖toL (u⁻¹).val‖ * ‖toL (y⁻¹).val‖) ≤ a * M * ‖toL (y⁻¹).val‖ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m2' (Nat.cast_nonneg a)) n2
        have aM : 0 ≤ (a : ℝ) * M := by positivity
        unfold height
        rw [show toL (y * u).val = toL (y.val * u.val) from rfl, e2, hc]
        nlinarith
      calc C * height (y * u) ^ N ≤ C * (c * height y) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * u)]) hh N) C0
        _ = C * c ^ N * height y ^ N := by rw [mul_pow, mul_assoc]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  change ‖∫ x, α x * chart f (g * infGL E a y) x ∂ν‖ ≤ _
  have hi : Integrable (fun x => ‖α x‖) ν :=
    hα.1.continuous.norm.integrable_of_hasCompactSupport hα.2.1.norm
  refine (norm_integral_le_of_norm_le (hi.mul_const _) (.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const]
  ring

end GlobalTheory.AutGrowth
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjKinf (k : Kinf E a) : Lie E a ≃L[ℝ] Lie E a :=
  ContinuousLinearEquiv.equivOfInverse
    ((lmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))).comp (rmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))))
    ((lmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))).comp (rmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))))
    (fun x => by
      change toL (star (k : Matrix (Fin a) (Fin a) (Cinf E)) * ((k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) * (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]; rfl)
    (fun x => by
      change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * (k : Matrix (Fin a) (Fin a) (Cinf E))) * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.one_mul]; rfl)

theorem conjKinf_apply (k : Kinf E a) (x : Lie E a) :
    conjKinf k x = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) := by
  change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = _
  rw [Matrix.mul_assoc]

def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w‖ ^ 2

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem trace_mul_conjTranspose_cinf (M : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    (M * M.conjTranspose).trace w = ((∑ i, ∑ j, ‖M i j w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_apply,
    Pi.mul_apply, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem frobSq_eq (x : Lie E a) :
    frobSq x = ∑ w, ((Matrix.of x * (Matrix.of x).conjTranspose).trace w).re := by
  simp only [frobSq, trace_mul_conjTranspose_cinf, Complex.ofReal_re]; rfl

theorem frobSq_conjKinf (k : Kinf E a) (x : Lie E a) : frobSq (conjKinf k x) = frobSq x := by
  rw [frobSq_eq, frobSq_eq, conjKinf_apply]
  have h : ∀ M : Matrix (Fin a) (Fin a) (Cinf E),
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
        ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))).conjTranspose =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (M * M.conjTranspose) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro M
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (k : Matrix (Fin a) (Fin a) (Cinf E))) (k : Matrix (Fin a) (Fin a) (Cinf E)),
      Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]
  rw [show Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
    (k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) from rfl, h,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]

theorem norm_le_one_of_frobSq (x : Lie E a) (h : frobSq x < 1) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | (apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one ..)

theorem continuous_frobSq : Continuous (frobSq : Lie E a → ℝ) := by
  unfold frobSq
  fun_prop

theorem measurePreserving_conjKinf (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (k : Kinf E a) :
    MeasurePreserving (conjKinf k) ν ν := by
  refine ⟨(conjKinf k).continuous.measurable, ?_⟩
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have hdet : LinearMap.det ((conjKinf k : Lie E a ≃L[ℝ] Lie E a).toLinearEquiv.toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have e := Measure.map_linearMap_addHaar_eq_smul_addHaar ν hdet
  change Measure.map (conjKinf k) ν = _ at e
  set B : Set (Lie E a) := frobSq ⁻¹' Set.Iio 1
  have hBo : IsOpen B := isOpen_Iio.preimage continuous_frobSq
  have hB0 : (0 : Lie E a) ∈ B := by simp [B, frobSq]
  have hpos : ν B ≠ 0 := (hBo.measure_pos ν ⟨0, hB0⟩).ne'
  have hfin : ν B ≠ ⊤ := (measure_mono fun x hx => (mem_closedBall_zero_iff.2 (norm_le_one_of_frobSq x hx))).trans_lt
    (measure_closedBall_lt_top (μ := ν) (x := (0 : Lie E a)) (r := 1)) |>.ne
  have hpre : conjKinf k ⁻¹' B = B := by
    ext x; simp [B, frobSq_conjKinf]
  have h1 := congrArg (fun m : Measure (Lie E a) => m B) e
  simp only [Measure.map_apply (conjKinf k).continuous.measurable hBo.measurableSet, hpre, Measure.smul_apply,
    smul_eq_mul] at h1
  have hc := (ENNReal.mul_eq_right hpos hfin).1 h1.symm
  rw [e, hc, one_smul]

theorem smoothing_rt_Kinf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a))
    [ν.IsAddHaarMeasure] (α : Lie E a → ℂ) (hα : KInv α) (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a) :
    smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  unfold smoothing
  rw [chart_rt_inf, chart_mul, ← (measurePreserving_conjKinf ν k).integral_comp (conjKinf k).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  congr 1
  · rw [conjKinf_apply]; exact hα k x
  · congr 1
    rw [conjKinf_apply]
    change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
      (k : Matrix (Fin a) (Fin a) (Cinf E))) = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x)
    rw [Matrix.mul_assoc _ (star _), Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]

end GlobalTheory.AutGrowth
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def leftInv : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g}
  zero_mem' _ _ := rfl
  add_mem' {ψ ψ'} h h' γ g := by simp [h γ g, h' γ g]
  smul_mem' c ψ h γ g := by simp [h γ g]

theorem lie_mem_leftInv (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ leftInv E a) : lie E a X ψ ∈ leftInv E a := by
  intro γ g
  have e : chart ψ.1 (ratGL E a γ * g) = chart ψ.1 g := by
    funext x
    simp only [chart, mul_assoc]
    split_ifs
    · exact h γ _
    · rfl
  simp only [lie_apply, lieD, e]


variable (E a) in
def fixL (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ k ∈ L, finRep E a k ψ = ψ}
  zero_mem' k _ := map_zero _
  add_mem' {ψ ψ'} h h' k hk := by rw [map_add (f := _), h k hk, h' k hk]
  smul_mem' c ψ h k hk := by rw [map_smul, h k hk]

theorem lie_mem_fixL (L : Subgroup (GL (Fin a) (Af E))) (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ fixL E a L) :
    lie E a X ψ ∈ fixL E a L := by
  intro k hk
  have e := LinearMap.congr_fun (lie_rt_fin X k) ψ
  simp only [Module.End.mul_apply] at e
  change rt E a (finGL E a k) (lie E a X ψ) = lie E a X ψ
  rw [← e]
  exact congrArg (lie E a X) (h k hk)

theorem comp_mem_maps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W)
    (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  intro E _ _ _ a L W hW T hT z hz
  refine ⟨fun k w => ?_, fun w => ⟨?_, ?_, ?_⟩⟩
  · simp only [LinearMap.comp_apply, hT.1 k w]
    exact (LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E a k z hz) (T w))
  · exact Zalg_stable (V := tame E a) (fun X _ h => lie_mem_tame X h) hz _ (hT.2 w).1
  · exact Zalg_stable (V := leftInv E a) (fun X _ h => lie_mem_leftInv X h) hz _ (hT.2 w).2.1
  · exact Zalg_stable (V := fixL E a L) (fun X _ h => lie_mem_fixL L X h) hz _ (hT.2 w).2.2

end GlobalTheory.AutGrowth
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem flat_polyMap_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  intro K κ' _ _ _ _ A m v h
  have h1 : (Algebra.TensorProduct.map (AlgHom.id ℂ κ')
      (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A)).toRingHom.Flat :=
    RingHom.Flat.tensorProductMap (f := AlgHom.id ℂ κ') (RingHom.Flat.id κ') h
  let e1 := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm.toRingEquiv
  let e2 := ((Algebra.TensorProduct.comm ℂ κ' A).trans (tensEquiv (κ' := κ') A)).toRingEquiv
  have h2 := ((RingHom.Flat.of_bijective (f := e1.toRingHom) e1.bijective).comp h1).comp
    (RingHom.Flat.of_bijective (f := e2.toRingHom) e2.bijective)
  convert h2 using 1
  refine MvPolynomial.ringHom_ext (fun b => Subtype.ext ?_) (fun i => Subtype.ext ?_)
  · have : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm (MvPolynomial.C b)
        = b ⊗ₜ 1 := by
      rw [AlgEquiv.symm_apply_eq]; simp [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
    simp [e1, e2, tensMap, this]
  · simp [e1, e2, tensMap]

end GlobalTheory.GraphLocal
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilDiagIso

theorem hTens_diag_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (c : A →ₐ[R] A) (JA : Matrix (Fin (n + n)) (Fin (n + n)) A) (JB : Matrix (Fin m) (Fin m) A)
    (x y : Matrix (Fin (n + n)) (Fin m) A)
    (hx : ∀ i j, x (Fin.natAdd n i) j = x (Fin.castAdd n i) j)
    (hy : ∀ i j, y (Fin.natAdd n i) j = y (Fin.castAdd n i) j)
    (h1 : ∀ i k, JA (Fin.castAdd n i) (Fin.natAdd n k) = 0)
    (h2 : ∀ i k, JA (Fin.natAdd n i) (Fin.castAdd n k) = 0)
    (h3 : ∀ i k, JA (Fin.natAdd n i) (Fin.natAdd n k) = - JA (Fin.castAdd n i) (Fin.castAdd n k)) :
    hTens c JA JB x y = 0 := by
  unfold hTens
  simp only [Fin.sum_univ_add, hx, hy, h1, h2, h3, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]

theorem symp_diag_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (u u' : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)),
    symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u)
      (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u') = 0 := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ u u'
  unfold symp
  rw [hTens_diag_eq_zero]
  · simp
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i j
    simp [Matrix.mul_apply, diagCols, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]
  · intro i k
    simp [incM, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, -Fin.natAdd_eq_addNat]

end GlobalTheory.WeilDiagIso
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem continuous_tensorMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing R'] [Algebra ℚ R'] [TopologicalSpace R'] [IsTopologicalRing R']
    {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
    letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
    Continuous (Algebra.TensorProduct.map f (AlgHom.id ℚ C)) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsModuleTopology R' (R' ⊗[ℚ] C) := ⟨rfl⟩
  haveI : ContinuousAdd (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousAdd R' _
  haveI : ContinuousSMul R' (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousSMul R' _
  let b := Module.finBasis ℚ C
  let bA := Algebra.TensorProduct.basis R b
  let bB := Algebra.TensorProduct.basis R' b
  have key : ∀ x, Algebra.TensorProduct.map f (AlgHom.id ℚ C) x = ∑ i, f (bA.repr x i) • bB i := by
    intro x
    conv_lhs => rw [← bA.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bA, bB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id ℚ C))) = fun x => ∑ i, f (bA.repr x i) • bB i := funext key
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (hf.comp (IsModuleTopology.continuous_of_linearMap (bA.coord i))).smul continuous_const

theorem continuous_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  intro p _ G v
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) _
  have hf : Continuous (AfP.eval v) := RestrictedProduct.continuous_eval v
  have hφ := continuous_tensorMap (C := G.C) (AfP.eval v) hf
  have h1 := Units.continuous_map (f := (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom.toMonoidHom) hφ
  have h2 := Units.continuous_map (f := (AfP.eval v).toRingHom.toMonoidHom) hf
  refine continuous_induced_rng.2 ?_
  exact (h1.comp (continuous_fst.comp continuous_subtype_val)).prodMk (h2.comp (continuous_snd.comp continuous_subtype_val))

end GlobalTheory.OrbFinAf
end
end
