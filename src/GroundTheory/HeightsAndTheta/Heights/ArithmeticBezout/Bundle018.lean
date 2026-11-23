module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughTwoPointsTrdeg.proof (hT : TrdegAdjoinLe.Statement) : ThroughTwoPointsTrdeg.Statement := by
  intro K Ω _ _ n k _ _ _ hinj x c hcx y j hyj hprop hy
  let u : Fin k × Fin n → Ω := fun im => algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (X im)
  let z : Fin n → Ω := fun m => y m * (y j)⁻¹
  let x' : Fin n → Ω := fun m => algebraMap K Ω (x m)
  let c' : Fin n → Ω := fun m => algebraMap K Ω (c m)
  let s : Fin k → Ω := fun i => ∑ l, u (i, l) * x' l
  have hC : ∀ a : K, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (C a) = algebraMap K Ω a := fun a => by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin k × Fin n) K) Ω, MvPolynomial.algebraMap_eq]

  have heq : ∀ i, ∑ m, u (i, m) * z m = s i * ∑ m, c' m * z m := by
    intro i
    have h := hy i

    simp only [genSubst, map_sub, map_mul, map_sum, hC] at h
    have h' : ∑ m, u (i, m) * y m = s i * ∑ m, c' m * y m := by
      rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [u, s, x', c']
      ring
    simp only [z, ← mul_assoc, ← Finset.sum_mul]
    rw [h']

  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcx
  have hx'p : x' p ≠ 0 := by simpa [x'] using hp
  obtain ⟨q, hD⟩ : ∃ q, x' p * z q - x' q * z p ≠ 0 := by
    by_contra h
    push Not at h
    apply hprop (y j * (z p * (x' p)⁻¹))
    funext m
    have hm := h m
    simp only [z, x'] at hm hx'p ⊢
    have hm2 : (algebraMap K Ω (x p) * y m - algebraMap K Ω (x m) * y p) * (y j)⁻¹ = 0 := by
      rw [← hm]; ring
    have hm3 := (mul_eq_zero.1 hm2).resolve_right (inv_ne_zero hyj)
    have e : y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        y p * algebraMap K Ω (x m) * (algebraMap K Ω (x p))⁻¹ := by
      rw [show y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        (y j * (y j)⁻¹) * (y p * algebraMap K Ω (x m)) * (algebraMap K Ω (x p))⁻¹ by ring,
        mul_inv_cancel₀ hyj, one_mul]
    rw [e, eq_mul_inv_iff_mul_eq₀ hx'p]
    linear_combination hm3
  set D := x' p * z q - x' q * z p with hDdef
  have hqp : q ≠ p := by
    rintro rfl
    exact hD (by simp [D])
  let E := (Finset.univ.erase p).erase q
  have hqE : q ∈ Finset.univ.erase p := Finset.mem_erase.2 ⟨hqp, Finset.mem_univ q⟩
  have hsplit : ∀ g : Fin n → Ω, ∑ m, g m = g p + g q + ∑ m ∈ E, g m := fun g => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hqE, add_assoc]

  let t : Fin k ⊕ (Fin k × E) → Ω := fun a => Sum.elim s (fun b => u (b.1, b.2.1)) a
  let B := Algebra.adjoin K (Set.range z ∪ Set.range t)
  have hzB : ∀ m, z m ∈ B := fun m => Algebra.subset_adjoin (Or.inl ⟨m, rfl⟩)
  have hsB : ∀ i, s i ∈ B := fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩)
  have huB : ∀ i, ∀ m ∈ E, u (i, m) ∈ B := fun i m hm =>
    Algebra.subset_adjoin (Or.inr ⟨Sum.inr (i, ⟨m, hm⟩), rfl⟩)
  have hKB : ∀ a : K, algebraMap K Ω a ∈ B := fun a => B.algebraMap_mem a
  have hczB : ∑ m, c' m * z m ∈ B := B.sum_mem fun m _ => B.mul_mem (hKB _) (hzB m)
  have hDB : D ∈ B := B.sub_mem (B.mul_mem (hKB _) (hzB q)) (B.mul_mem (hKB _) (hzB p))
  have halg : ∀ v, D * v ∈ B → IsAlgebraic B v := fun v hv =>
    IsAlgebraic.of_mul (y := D) (mem_nonZeroDivisors_of_ne_zero hD)
      (isAlgebraic_algebraMap (⟨D, hDB⟩ : B)) (isAlgebraic_algebraMap (⟨D * v, hv⟩ : B))
  have hw : ∀ im, IsAlgebraic B (u im) := by
    rintro ⟨i, m⟩
    have hSx : ∑ m ∈ E, u (i, m) * x' m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hKB _)
    have hSz : ∑ m ∈ E, u (i, m) * z m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hzB m)
    have e1 := hsplit (fun m => u (i, m) * x' m)
    have e2 := hsplit (fun m => u (i, m) * z m)
    rw [heq i] at e2
    change s i = _ at e1
    by_cases hmp : m = p
    · subst hmp
      refine halg _ ?_
      have : D * u (i, m) = z q * (s i - ∑ m ∈ E, u (i, m) * x' m) -
          x' q * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) := by
        rw [hDdef]; linear_combination -z q * e1 + x' q * e2
      rw [this]
      exact B.sub_mem (B.mul_mem (hzB q) (B.sub_mem (hsB i) hSx))
        (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
    by_cases hmq : m = q
    · subst hmq
      refine halg _ ?_
      have : D * u (i, m) = x' p * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) -
          z p * (s i - ∑ m ∈ E, u (i, m) * x' m) := by
        rw [hDdef]; linear_combination -x' p * e2 + z p * e1
      rw [this]
      exact B.sub_mem (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
        (B.mul_mem (hzB p) (B.sub_mem (hsB i) hSx))
    exact isAlgebraic_algebraMap
      (⟨u (i, m), huB i m (Finset.mem_erase.2 ⟨hmq, Finset.mem_erase.2 ⟨hmp, Finset.mem_univ m⟩⟩)⟩ : B)
  have hle := hT K Ω (Set.range z) (Fin k ⊕ (Fin k × E)) t (Fin k × Fin n) u hw

  have hadj : Algebra.adjoin K (Set.range u) = (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω).range := by
    rw [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hinj' : Function.Injective (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω) := hinj
  have htr : Algebra.trdeg K (Algebra.adjoin K (Set.range u)) = ((k * n : ℕ) : Cardinal) := by
    rw [hadj, ← (AlgEquiv.ofInjective _ hinj').trdeg_eq, MvPolynomial.trdeg_of_isDomain]
    simp
  have hcard : Fintype.card (Fin k ⊕ (Fin k × E)) = k + k * (n - 2) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Finset.card_erase_of_mem hqE, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    rfl
  rw [htr, hcard] at hle
  have hn : 2 ≤ n := by
    have := Fin.val_ne_of_ne hqp
    omega
  rcases lt_or_ge (Algebra.trdeg K (Algebra.adjoin K (Set.range z))) Cardinal.aleph0 with hfin | hinf
  · obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.1 hfin
    rw [hd] at hle ⊢
    norm_cast at hle ⊢
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left] at hle
    nlinarith
  · exact (Cardinal.natCast_lt_aleph0 (n := k)).le.trans hinf

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal NNReal

noncomputable section

theorem ConeSlabBound.proof (hV : VarietySlabMeasure.Statement) : ConeSlabBound.Statement := by
  intro n e h W f u hW hf hu
  have hWp : W.IsPrime := hW.isPrime
  have hdim := ChowFormDimLe.proof ℂ n (e + 1) W f hW hf

  let E := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let F : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ h.matᵀ.mulVecLin ∘ₗ E.toLinearMap)
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ (h.matᵀ)⁻¹.mulVecLin ∘ₗ E.toLinearMap)
  have hF : ∀ y i, F y i = h.pointOf y i := fun _ _ => rfl
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hLF : ∀ y, L (F y) = y := by
    intro y
    ext i
    change ((h.matᵀ)⁻¹ *ᵥ (h.matᵀ *ᵥ fun j => y j)) i = y i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  obtain ⟨C, α, hC, hα, hb⟩ := hV n (e + 1) W u hWp hdim hu ‖F‖
  set s : ℝ := ((2 * (e + 1) : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  let K : ℝ≥0 := ‖L‖₊
  refine ⟨(K : ℝ) ^ s * C, α, hα, fun ε hε hε1 => ?_⟩

  have hsub : coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖} ⊆
      L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    rintro y ⟨⟨hy1, hyW⟩, hyu⟩
    refine ⟨F y, ⟨fun q hq => ?_, ?_, ?_⟩, hLF y⟩
    · have : (fun i => F y i) = h.pointOf y := funext (hF y)
      rw [this]
      exact hyW q hq
    · calc ‖F y‖ ≤ ‖F‖ * ‖y‖ := F.le_opNorm y
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hy1.le (norm_nonneg _)
        _ = ‖F‖ := mul_one _
    · simp only [hF]
      calc ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖ := hyu
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hy1.le hε.le
        _ = ε := mul_one _
  calc μH[s] (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖})
      ≤ μH[s] (L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε}) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ s * μH[s] {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} :=
        L.lipschitz.hausdorffMeasure_image_le hs0 _
    _ ≤ (K : ℝ≥0∞) ^ s * ENNReal.ofReal (C * ε ^ α) := by
        gcongr
        exact hb ε hε hε1
    _ = ENNReal.ofReal ((K : ℝ) ^ s * C * ε ^ α) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg K.coe_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg K.coe_nonneg hs0, ENNReal.ofReal_coe_nnreal]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem aeval_scale_of_isWeightedHomogeneous {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {w : σ → ℕ} {p : MvPolynomial σ R} {a : ℕ} (hp : IsWeightedHomogeneous w p a)
    (t : A) (u : σ → A) : aeval (fun j => t ^ w j * u j) p = t ^ a * aeval u p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hw : ∑ j ∈ d.support, w j * d j = a := by
    rw [← hp (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul, mul_comm]
  rw [hw]
  ring

variable {F : Type} [Field F] {n k : ℕ}

theorem scale_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence I k) (i : Fin k)
    (t : AlgebraicClosure F) : (fun ij => t ^ inGroup i ij * u ij) ∈ incidence I k := by
  obtain ⟨x, hx0, hxI, hux⟩ := hu
  refine ⟨x, hx0, hxI, fun i' => ?_⟩
  have hc : ∀ j : Fin n, t ^ inGroup i (i', j) * u (i', j) * x j =
      t ^ (if i' = i then 1 else 0) * (u (i', j) * x j) := fun j => by rw [mul_assoc]; rfl
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hc j) ?_
  rw [← Finset.mul_sum, hux i', mul_zero]

theorem component_vanish_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : ∀ u ∈ incidence I k, aeval u f = 0) (i : Fin k)
    {a : ℕ} (ha : a ∈ weightSet (inGroup (n := n) i) f) :
    ∀ u ∈ incidence I k, aeval u (weightedHomogeneousComponent (inGroup (n := n) i) a f) = 0 := by
  classical
  intro u hu
  set w := inGroup (n := n) i
  set S := weightSet w f
  set q : Polynomial (AlgebraicClosure F) :=
    ∑ b ∈ S, Polynomial.C (aeval u (weightedHomogeneousComponent w b f)) * Polynomial.X ^ b with hq_def
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have h1 := hf _ (scale_mem_incidence hu i t)

    rw [← sum_weightSet_component (w := w) f, map_sum] at h1
    simp only [hq_def, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aeval_scale_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous b f),
      mul_comm]
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p a) hq
  simp only [hq_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq, if_pos ha] at hc
  exact hc

theorem IsChowForm.exists_isWeightedHomogeneous_inGroup {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup (n := n) i) f a := by
  obtain ⟨a, ha⟩ := weightSet_nonempty (w := inGroup (n := n) i) hf.1
  have hvan : ∀ u ∈ incidence I k, aeval u f = 0 := (hf.2 f).mpr dvd_rfl
  obtain ⟨r, hr⟩ := (hf.2 _).mp (component_vanish_incidence hvan i ha)
  have hc := component_ne_zero_of_mem ha
  rw [hr] at hc
  refine isWeightedHomogeneous_of_mul_left (m := a) ?_ hf.1 (right_ne_zero_of_mul hc)
  rw [← hr]
  exact weightedHomogeneousComponent_isWeightedHomogeneous a f

theorem zero_mem_incidence {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) (k : ℕ) :
    (0 : Fin k × Fin n → AlgebraicClosure F) ∈ incidence P k := by
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hex : ∃ x ∈ zeroLocus (AlgebraicClosure F) P, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    have hrad : X j ∈ vanishingIdeal F (zeroLocus (AlgebraicClosure F) P) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [h x hx]
      simp
    rwa [vanishingIdeal_zeroLocus_eq_radical, hP.isPrime.radical] at hrad
  obtain ⟨x, hx, hx0⟩ := hex
  exact ⟨x, hx0, fun g hg => mem_zeroLocus_iff.mp hx g hg, fun i => by simp⟩

theorem IsChowForm.exists_multiHomog {P : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hP : IsProjPrime P) (hf : IsChowForm P k f) :
    ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ f := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact ⟨1, le_rfl, fun d _ => funext fun i => i.elim0⟩
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  refine ⟨a ⟨0, hk⟩, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hδ⟩
  rw [h0] at hδ
  have hd0 : ∀ d ∈ f.support, d = 0 := by
    intro d hd
    have h := congrFun (hδ (mem_support_iff.mp hd))
    ext ij
    by_contra hne
    have h1 := h ij.1
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h1
    have h2 := (Finset.sum_eq_zero_iff.mp h1) ij (Finsupp.mem_support_iff.mpr hne)
    simp [groupWeight] at h2
    exact hne h2
  have hC : f = C (AddMonoidAlgebra.coeff f 0) := by
    ext d
    rw [coeff_C]
    split_ifs with hd
    · rw [hd]
    · by_contra hne
      exact hd (hd0 d (mem_support_iff.mpr hne)).symm
  have hz := (hf.2 f).mpr dvd_rfl 0 (zero_mem_incidence hP k)
  rw [hC, aeval_C, map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective] at hz
  exact hf.1 (by rw [hC, hz, C_0])

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)

variable {n : ℕ}

theorem specFirst_eq {R : Type*} [CommRing R] {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R)
    (u : Fin n → R) : specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f := by
  rw [specFirst, IndefiniteRowSideFullHecke.ArithBezout.specFirst, aeval_eq_bind₁]
  rfl

theorem map_specFirst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {e : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R) :
    map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f) := by
  have h : (fun ij => map φ (specFirstVar u ij)) =
      (specFirstVar (φ ∘ u) : Fin (e + 1) × Fin n → MvPolynomial (Fin e × Fin n) S) := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [specFirstVar]
  rw [← specFirst_eq, ← specFirst_eq, specFirst, specFirst, map_bind₁, h]

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem chowHeightMul_of_mahlerMul (hM : MahlerMul.Statement) : ChowHeightMul.Statement := by
  intro K _ _ n H k δ₁ δ₂ f₁ f₂ h₁ h₂
  unfold chowHt
  have hmah : ∀ σ : K →+* ℂ, mahler (H.normAt σ) k ((f₁ * f₂).map σ) =
      mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) := by
    intro σ
    rw [map_mul]
    exact hM n k _ _ _ (fun h => h₁ (map_injective σ σ.injective (by rw [h, map_zero])))
      (fun h => h₂ (map_injective σ σ.injective (by rw [h, map_zero])))
  rw [finsum_log_gaussNorm_mul h₁ h₂]
  simp_rw [hmah]
  rw [← mul_add]
  congr 1
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) +
      (k : ℝ) * ((δ₁ + δ₂ : ℕ) : ℝ) * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + (k : ℝ) * δ₁ * (harmonic (n - 1) : ℝ) / 2) +
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₂.map σ) + (k : ℝ) * δ₂ * (harmonic (n - 1) : ℝ) / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  rw [hs]
  ring

end

end GroundTheory.Heights₂.Heights
end
