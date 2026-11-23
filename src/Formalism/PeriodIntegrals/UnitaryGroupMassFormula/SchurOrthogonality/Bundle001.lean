module

import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
public import Formalism.PeriodIntegrals.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.Params
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory Measure TopologicalSpace Matrix

theorem isCompact_unitaryGroup (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · have e : (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) =
        {A : Matrix (Fin N) (Fin N) ℂ | A * star A = 1} := by
      ext A
      exact Matrix.mem_unitaryGroup_iff
    rw [e]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  · intro A hA
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hA i j

instance compactSpace_unitaryGroup (N : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup N)

theorem isMulRightInvariant_of_compact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] : IsMulRightInvariant μ := by
  apply GlobalTheory.isMulRightInvariant_of_compactSpace <;> assumption

theorem unitary_haar_measure : HaarU := by
  intro N
  haveI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) := compactSpace_unitaryGroup N
  let μG : Measure (Matrix.unitaryGroup (Fin N) ℂ) := Measure.haarMeasure ⊤
  haveI : μG.IsMulRightInvariant := isMulRightInvariant_of_compact μG
  have hm : Measurable (Subtype.val : Matrix.unitaryGroup (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
    measurable_subtype_coe
  refine ⟨Measure.map Subtype.val μG, ?_, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
    have h1 := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin N) ℂ)))
    simpa using h1
  · have hmeas : MeasurableSet {x : Matrix (Fin N) (Fin N) ℂ | x ∈ Matrix.unitaryGroup (Fin N) ℂ} :=
      (isCompact_unitaryGroup N).isClosed.measurableSet
    rw [ae_map_iff hm.aemeasurable hmeas]
    exact Filter.Eventually.of_forall fun y => y.2
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (x * u)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_mul_const u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_right_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (u * x)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_const_mul u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_left_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1

end PI.WSF
end
end

section

noncomputable section

namespace PI.WSF

open MvPolynomial MeasureTheory Matrix

private theorem entry_le_lemma {N : ℕ} {x : Matrix (Fin N) (Fin N) ℂ} (hx : x ∈ unitaryGroup (Fin N) ℂ)
    (i j : Fin N) : ‖x i j‖ ≤ 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hx) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h3 : (∑ k, Complex.normSq (x i k) : ℝ) = 1 := by
    have h4 : ((∑ k, Complex.normSq (x i k) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h]
      exact Finset.sum_congr rfl fun k _ => (Complex.mul_conj (x i k)).symm
    exact_mod_cast h4
  have h5 : Complex.normSq (x i j) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (x i k)) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at h5
  nlinarith [norm_nonneg (x i j)]

theorem ci_compact (N : ℕ) : IsCompact (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hset : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) = {x | x * star x = 1} := by
    ext x
    exact Matrix.mem_unitaryGroup_iff
  have hclosed : IsClosed (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
    rw [hset]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  have hbound : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    intro x hx
    exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
      mem_closedBall_zero_iff.mpr (entry_le_lemma hx i j)
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset
    hclosed hbound

theorem ci_cont {N : ℕ} (p : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p := by
  unfold evalM
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun v => (continuous_apply v.2).comp (continuous_apply v.1))

theorem ci_cont2 {N : ℕ} (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p * star (evalM x q) :=
  (ci_cont p).mul (ci_cont q).star

theorem ci_integrable {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    {f : Matrix (Fin N) (Fin N) ℂ → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨hprob, hae, -, -⟩ := hμ
  have h := hf.continuousOn.integrableOn_compact (μ := μ) (ci_compact N)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h
  exact h

theorem ci_evalM_add {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (p + q) = evalM x p + evalM x q := by
  simp [evalM]

theorem ci_evalM_smul {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (c • p) = c * evalM x p := by
  simp [evalM]

def Aform {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  ∫ x, evalM x p * star (evalM x q) ∂μ

def Alin {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (q : MvPolynomial (Fin N × Fin N) ℂ) : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun p := Aform μ p q
  map_add' p p' := by
    unfold Aform
    rw [← integral_add (ci_integrable hμ (ci_cont2 p q)) (ci_integrable hμ (ci_cont2 p' q))]
    congr 1
    funext x
    rw [ci_evalM_add]
    ring
  map_smul' c p := by
    unfold Aform
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    rw [ci_evalM_smul]
    ring

theorem ci_Alin_apply {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) : Alin hμ q p = Aform μ p q := rfl

theorem ci_herm {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ q p = star (Aform μ p q) := by
  unfold Aform
  have h := integral_conj (μ := μ) (f := fun x => evalM x p * star (evalM x q))
  rw [show star (∫ x, evalM x p * star (evalM x q) ∂μ) =
    (starRingEnd ℂ) (∫ x, evalM x p * star (evalM x q) ∂μ) from rfl, ← h]
  congr 1
  funext x
  simp [mul_comm]

private theorem evalM_rowAct {N : ℕ} (u x : Matrix (Fin N) (Fin N) ℂ)
    (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ u p) = evalM (u * x) p := by
  induction p using MvPolynomial.induction_on
  next a =>
    simp [evalM, Formalism.GradedWeylDivisibility.rowAct]
  next p q hp hq =>
    rw [map_add (f := _), ci_evalM_add, ci_evalM_add, hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem ci_invariant {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ unitaryGroup (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ (Formalism.GradedWeylDivisibility.rowAct ℂ u p) (Formalism.GradedWeylDivisibility.rowAct ℂ u q) = Aform μ p q := by
  obtain ⟨-, -, -, hL⟩ := hμ
  unfold Aform
  simp only [evalM_rowAct]
  exact hL u hu (fun x => evalM x p * star (evalM x q)) (ci_cont2 p q)

end PI.WSF
end
end

section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial

theorem cr_rowAct_X {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (w : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (X w : MvPolynomial (Fin N × Fin N) ℂ) = ∑ b : Fin N, C (g w.1 b) * X (b, w.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem cr_rowAct_C {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (C a : MvPolynomial (Fin N × Fin N) ℂ) = C a :=
  (Formalism.GradedWeylDivisibility.rowAct ℂ g).commutes a

theorem cr_evalM_rowAct {N : ℕ} (g x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM (g * x) s := by
  induction s using MvPolynomial.induction_on
  next a =>
    rw [cr_rowAct_C]
    simp [evalM]
  next p q hp hq =>
    simp only [map_add (f := _), evalM] at hp hq ⊢
    rw [hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp, cr_rowAct_X]
    congr 1
    simp [Matrix.mul_apply]

theorem cr_rowAct_one {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) s = s := by
  have h : (Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) :
      MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro w
    rw [cr_rowAct_X]
    simp [Matrix.one_apply]
  rw [h]
  rfl

theorem cr_rowAct_rowAct {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h s) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) s := by
  have hc : (Formalism.GradedWeylDivisibility.rowAct ℂ g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) =
      (Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro w

    rw [AlgHom.comp_apply, cr_rowAct_X, map_sum, cr_rowAct_X]

    simp only [map_mul, cr_rowAct_C, cr_rowAct_X, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]
    exact Finset.sum_comm
  rw [← hc, AlgHom.comp_apply]

theorem cr_polyFun {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    ∀ L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ, ∃ P : MvPolynomial (Fin N × Fin N) ℂ,
      ∀ g : Matrix (Fin N) (Fin N) ℂ, L (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM g P := by
  intro L
  let Φ : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ]
      MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) ℂ) :=
    aeval fun v => ∑ b : Fin N, C (X (v.1, b) : MvPolynomial (Fin N × Fin N) ℂ) * X (b, v.2)
  have hmap : ∀ g : Matrix (Fin N) (Fin N) ℂ,
      MvPolynomial.map (MvPolynomial.eval fun v : Fin N × Fin N => g v.1 v.2) (Φ s) = Formalism.GradedWeylDivisibility.rowAct ℂ g s := by
    intro g
    induction s using MvPolynomial.induction_on
    next a =>
      rw [cr_rowAct_C]
      simp [Φ]
    next p q hp hq =>
      simp only [map_add (f := _), hp, hq]
    next p w hp =>
      simp only [map_mul, hp, cr_rowAct_X]

      simp only [Φ, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.eval_X]
  have hmono : ∀ (m : Fin N × Fin N →₀ ℕ) (a : ℂ), L (monomial m a) = a * L (monomial m 1) := by
    intro m a
    calc L (monomial m a) = L (a • monomial m (1 : ℂ)) := by rw [smul_monomial, smul_eq_mul, mul_one]
      _ = a * L (monomial m 1) := by rw [map_smul, smul_eq_mul]
  refine ⟨∑ m ∈ (Φ s).support, (Φ s).coeff m * C (L (monomial m 1)), fun g => ?_⟩
  rw [← hmap g]
  conv_lhs => rw [(Φ s).as_sum]

  simp only [map_sum, MvPolynomial.map_monomial, evalM, map_mul, MvPolynomial.eval_C]
  exact Finset.sum_congr rfl fun m _ => hmono m _

end PI.WSF
end
end

section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

theorem schurFock_of_steps (hB : HaarU) (hC : SchurOrth) : PI.SchurFock := by
  intro N lam s hs hbd
  obtain ⟨μ, hμ⟩ := hB N
  have hprob := hμ.1
  have hae := hμ.2.1
  rw [hC N lam μ hμ s hs]
  have hint : ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ 1 := by
    calc ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (integrable_const 1)
          filter_upwards [hae] with x hx
          exact pow_le_one₀ (norm_nonneg _) (hbd x hx)
      _ = 1 := by simp
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hint

end PI.WSF
end
end
