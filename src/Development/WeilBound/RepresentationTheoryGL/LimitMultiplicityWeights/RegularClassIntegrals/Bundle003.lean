module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle029
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PBoundT

lemma entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    star (l i) * l j = 1 := by
  have e := congrFun (congrFun h i) j
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul] at e
  have e2 : (star (l i) * l j - 1) * J i j = 0 := by
    simp only [Pi.star_apply] at e
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hJ)

lemma norm_entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    ‖l i‖ * ‖l j‖ = 1 := by
  have e := congrArg (fun x : ℂ => ‖x‖) (entry J l h i j hJ)
  simpa [norm_mul, norm_star] using e

end MainStatements.WeightKernel.PBoundT

namespace MainStatements.WeightKernel

open PBoundT in
theorem boundT : BoundT := by
  intro n J l hdet hinj hl a b ha
  refine ⟨max b (max (1 / a) 1), ?_⟩
  intro τ hτ hbd j
  have col : ∃ i, J i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : J.det = 0 := Matrix.det_eq_zero_of_column_eq_zero j hc
    rw [this] at hdet
    exact not_isUnit_zero hdet
  obtain ⟨i, hij⟩ := col
  have hl2 := norm_entry J l hl i j hij
  have hτ2 := norm_entry J τ hτ i j hij
  rcases lt_trichotomy ‖l j‖ 1 with hlt | heq | hgt
  · have hli : 1 < ‖l i‖ := by
      by_contra hc
      push_neg at hc
      have h0 : 0 ≤ ‖l j‖ := norm_nonneg _
      nlinarith
    have ha' := (hbd i hli).1
    have hτj : ‖τ j‖ ≤ 1 / a := by
      rw [le_div_iff₀ ha]
      have h0 : 0 ≤ ‖τ j‖ := norm_nonneg _
      nlinarith
    exact le_trans hτj (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hli : ‖l i‖ = 1 := by
      rw [heq, mul_one] at hl2
      exact hl2
    have ent := entry J l hl i j hij
    have hsq : l i * star (l i) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hli]
      simp
    have hij' : l i = l j := by
      have : l i * (star (l i) * l j) = l i := by rw [ent, mul_one]
      rw [← mul_assoc, hsq, one_mul] at this
      exact this.symm
    have hieq : i = j := hinj hij'
    subst hieq
    have h0 : 0 ≤ ‖τ i‖ := norm_nonneg _
    have h1 : ‖τ i‖ = 1 := by nlinarith
    rw [h1]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact le_trans (hbd j hgt).2 (le_max_left _ _)

end MainStatements.WeightKernel

end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem kerSwap : KerUnif → KerSwap := by
  intro hU H _ _ _ _ _ _ _ _ n ι hι μ _ Ω I _ _ m _ c q hk P _ _ _ W p K C hW hp hK hC hWC
  obtain ⟨B, hB⟩ := hU H n ι hι Ω I m c q hk P W p K C hW hp hK hC hWC
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hmc : Continuous (matCoord ι) := hι.continuous
  set G : H × H → ℂ := fun z => W (matCoord ι z.1, p z.2) with hG
  have hGc : Continuous G := hW.continuous.comp ((hmc.comp continuous_fst).prodMk (hp.comp continuous_snd))
  set F : H → Ω → ℂ := fun k x => ker c q (fun y => W (matCoord ι y, p k)) x with hF

  have hvan : ∀ x, ∀ k ∈ K, ∀ i, i ∉ (hk.fin x C hC).toFinset → c i x * W (matCoord ι (q i x), p k) = 0 := by
    intro x k hkK i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
    rcases hi with h | h
    · simp [h]
    · simp [hWC k hkK _ h]

  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict K).prod m) := by
    obtain ⟨u, hu⟩ := (atTop : Filter (Finset I)).exists_seq_tendsto
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N (z : H × Ω) => ∑ i ∈ u N, c i z.2 * W (matCoord ι (q i z.2), p z.1)) ?_ ?_
    · intro N
      refine (Finset.measurable_sum _ fun i _ => ?_).aestronglyMeasurable
      refine ((hk.mc i).comp measurable_snd).mul ?_
      have : Measurable fun z : H × Ω => ((q i z.2, z.1) : H × H) :=
        ((hk.mq i).comp measurable_snd).prodMk measurable_fst
      exact hGc.measurable.comp this
    · have hae : ∀ᵐ z ∂((μ.restrict K).prod m), z.1 ∈ K :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_restrict_mem hKm)
      filter_upwards [hae] with z hz
      have hs : HasSum (fun i => c i z.2 * W (matCoord ι (q i z.2), p z.1))
          (∑' i, c i z.2 * W (matCoord ι (q i z.2), p z.1)) :=
        (summable_of_ne_finset_zero (s := (hk.fin z.2 C hC).toFinset) (hvan z.2 z.1 hz)).hasSum
      exact hs.comp hu
  have hint : Integrable (Function.uncurry F) ((μ.restrict K).prod m) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hKm] with k hkK
      exact (hB k hkK).1
    · refine Integrable.mono' (integrable_const B) hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hKm] with k hkK
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hB k hkK).2
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF, ker]
  have hT := hvan x
  set T := (hk.fin x C hC).toFinset
  rw [setIntegral_congr_fun hKm (fun k hkK => tsum_eq_sum (s := T) (hT k hkK))]
  rw [integral_finsetSum]
  · rw [tsum_eq_sum (s := T)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_const_mul _ _
    · intro i hi
      simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
      rcases hi with h | h
      · simp [h]
      · rw [setIntegral_eq_zero_of_forall_eq_zero (fun k hkK => hWC k hkK _ h), mul_zero]
  · intro i _
    exact (ContinuousOn.integrableOn_compact hK
      (continuous_const.mul (hW.continuous.comp (continuous_const.prodMk hp))).continuousOn)

end MainStatements.WeightKernel
end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Polynomial
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PLagr

variable {n : ℕ}

lemma cd_mul {F G : Mx n → Matrix (Fin n) (Fin n) ℂ} (hF : ∀ a b, ContDiff ℝ ∞ (fun Y => F Y a b))
    (hG : ∀ a b, ContDiff ℝ ∞ (fun Y => G Y a b)) : ∀ a b, ContDiff ℝ ∞ (fun Y => (F Y * G Y) a b) := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun j _ => (hF a j).mul (hG j b)

lemma cd_pow (k : ℕ) : ∀ a b, ContDiff ℝ ∞ (fun Y : Mx n => ((Matrix.of Y) ^ k) a b) := by
  induction k with
  | zero => intro a b; simp only [pow_zero]; exact contDiff_const
  | succ k ih =>
    simp only [pow_succ]
    exact cd_mul ih (fun a b => by simp only [Matrix.of_apply]; exact contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) a b)

lemma cd_aeval (P : ℂ[X]) : ∀ a b, ContDiff ℝ ∞ (fun Y : Mx n => (aeval (Matrix.of Y) P) a b) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => intro a b; simp only [map_add (f := _), Matrix.add_apply]; exact (hp a b).add (hq a b)
  | monomial k c =>
    simp only [Polynomial.aeval_monomial]
    exact cd_mul (fun a b => contDiff_const) (cd_pow k)

lemma conj_pow (g g' D : Matrix (Fin n) (Fin n) ℂ) (h1 : g' * g = 1) (h2 : g * g' = 1) (k : ℕ) :
    (g' * D * g) ^ k = g' * D ^ k * g :=
  _root_.UpperTheory.Reformulated.B.Yhd8.main g g' D h1 h2 k

lemma aeval_conj (g g' D : Matrix (Fin n) (Fin n) ℂ) (h1 : g' * g = 1) (h2 : g * g' = 1) (P : ℂ[X]) :
    aeval (g' * D * g) P = g' * aeval D P * g := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, mul_add, add_mul]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, conj_pow g g' D h1 h2,
      ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

lemma aeval_diag (l : Fin n → ℂ) (P : ℂ[X]) :
    aeval (diagonal l) P = diagonal fun j => P.eval (l j) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), hp, hq, Matrix.diagonal_add]; simp [Polynomial.eval_add]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [Polynomial.eval_monomial]

end PLagr

open PLagr in
theorem lagr : Lagr := by
  intro n l hl
  refine ⟨fun i Y => fun a b => (aeval (Matrix.of Y) (Lagrange.basis Finset.univ l i)) a b, fun i => ?_, ?_⟩
  · exact contDiff_pi.2 fun a => contDiff_pi.2 fun b => cd_aeval _ a b
  · intro i g g' h1 h2
    change aeval (g' * diagonal l * g) (Lagrange.basis Finset.univ l i) = _
    rw [aeval_conj g g' _ h1 h2, aeval_diag]
    have hv : (fun j => (Lagrange.basis Finset.univ l i).eval (l j)) = Pi.single i 1 := by
      funext j
      by_cases h : j = i
      · subst h
        rw [Pi.single_eq_same, Lagrange.eval_basis_self hl.injOn (Finset.mem_univ _)]
      · rw [Pi.single_eq_of_ne h, Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)]
    rw [hv, Matrix.diagonal_single]

end MainStatements.WeightKernel

end
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PWeight

variable {n : ℕ}

theorem cancel_l {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

def conjHom {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) : H →* Matrix (Fin n) (Fin n) ℂ where
  toFun h := Q * ι h * P
  map_one' := by simp [hQP]
  map_mul' a b := by simp only [map_mul, Matrix.mul_assoc, cancel_l hPQ]

theorem conjHom_apply {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (g : H) : conjHom ι Q P hPQ hQP g = Q * ι g * P := rfl

def conjHomeo (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ where
  toFun Y := Q * Y * P
  invFun Y := P * Y * Q
  left_inv Y := by simp only [Matrix.mul_assoc, cancel_l hPQ, hPQ, Matrix.mul_one]
  right_inv Y := by simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem isUGroup_conj {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hU : IsUGroup ι J) :
    IsUGroup (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) := by
  have hPQh : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
  have hQPh : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩
  have hPh : IsUnit Pᴴ.det := isUnit_iff_exists_inv.2 ⟨Qᴴ.det, by rw [← det_mul, hQPh, det_one]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact (hPh.mul hU.1).mul hP
  · exact (conjHomeo Q P hPQ hQP).isClosedEmbedding.comp hU.2.1
  · have key1 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (Q * X * P)ᴴ * (Pᴴ * J * P) * (Q * X * P) = Pᴴ * (Xᴴ * J * X) * P := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc, cancel_l hPQh, cancel_l hPQ]
    have key2 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (P * X * Q)ᴴ * J * (P * X * Q) = Qᴴ * (Xᴴ * (Pᴴ * J * P) * X) * Q := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have key3 : Qᴴ * (Pᴴ * J * P) * Q = J := by
      simp only [Matrix.mul_assoc, cancel_l hPQh, hPQ, Matrix.mul_one]
    intro M
    constructor
    · rintro ⟨h, rfl⟩
      have hA := (hU.2.2 (ι h)).1 ⟨h, rfl⟩
      rw [conjHom_apply, key1, hA]
    · intro hM
      have hN : (P * M * Q)ᴴ * J * (P * M * Q) = J := by rw [key2, hM, key3]
      obtain ⟨h, hh⟩ := (hU.2.2 _).2 hN
      refine ⟨h, ?_⟩
      rw [conjHom_apply, hh]
      simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]

def conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) (Y : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n :=
  fun i j => (Q * Matrix.of Y * P) i j

theorem contDiff_conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (conjMx Q P) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [conjMx, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun x _ => ContDiff.mul (ContDiff.sum fun y _ =>
    contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) x).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) y))) contDiff_const

end MainStatements.WeightKernel.PWeight

namespace MainStatements.WeightKernel

open PWeight in
theorem weight : WeightDiag → Weight := by
  intro hWD H _ _ _ _ _ _ _ _ n ι J hU s hreg hprop
  obtain ⟨P, Q, l, hl, hPQ, hQP, hd⟩ := GlobalTheory.CompanionTheory.WeylNear.exists_diag n (ι s) hreg
  obtain ⟨B', hB'⟩ := hWD H n (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) (isUGroup_conj ι J Q P hPQ hQP hU) s l hl
    hd hprop
  refine ⟨fun z => B' (conjMx Q P z.1, conjMx Q P z.2), ?_, fun z => hB'.nonneg _, hB'.pos, hB'.shift, hB'.proper⟩
  exact hB'.smooth.comp (((contDiff_conjMx Q P).comp contDiff_fst).prodMk ((contDiff_conjMx Q P).comp contDiff_snd))

end MainStatements.WeightKernel

end
end
