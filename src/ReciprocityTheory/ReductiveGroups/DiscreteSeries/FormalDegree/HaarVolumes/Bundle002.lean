module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriHaarA
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

variable {N : ℕ}

def skML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := skMat p.1
  map_add' p q := by
    ext a b
    simp only [skMat, Prod.fst_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [skMat, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def upML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := upMat p.2
  map_add' p q := by
    ext a b
    simp only [upMat, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [upMat, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chartWR_strict :
    HasStrictFDerivAt (chartWR (N := N))
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) 0 := by
  let skL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap skML
  let upL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap upML
  let ofL : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hsk0 : skL 0 = 0 := map_zero _
  have hup0 : upL 0 = 0 := map_zero _
  have h1 : HasStrictFDerivAt (fun p : UCo N × TriCo N => NormedSpace.exp (skL p))
      ((1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) 0 := by
    have he := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℂ)
    rw [← hsk0] at he
    exact he.comp 0 skL.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : UCo N × TriCo N => 1 + upL p) upL 0 :=
    upL.hasStrictFDerivAt.const_add 1
  have h3 := h1.mul' h2
  have h4 := ofL.hasStrictFDerivAt.comp 0 h3
  have hF : (fun x => ofL (((fun p => NormedSpace.exp (skL p)) * fun p => 1 + upL p) x)) = chartWR := by
    funext p; rfl
  have hD : ofL.comp (NormedSpace.exp (skL 0) • upL + MulOpposite.op (1 + upL 0) •
      (1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) =
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) := by
    refine ContinuousLinearMap.ext fun p => ?_
    rw [hsk0, hup0, NormedSpace.exp_zero]
    simp
    exact (add_comm _ _).trans rfl
  rw [hF] at h4
  exact h4.congr_fderiv hD

end Deriv

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def uToLieMat (x : UCo N) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ :=
  Matrix.reindex (Equiv.sumEmpty (Fin N) (Fin 0)).symm (Equiv.sumEmpty (Fin N) (Fin 0)).symm (skMat x)

theorem uToLieMat_apply (x : UCo N) (i j : Fin N ⊕ Fin 0) :
    uToLieMat x i j = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) i) (Equiv.sumEmpty (Fin N) (Fin 0) j) := by
  rfl

theorem uToLieMat_mem (x : UCo N) : uToLieMat x ∈ Formalism.BasicNotions.lieU N 0 := by
  rw [mem_lieU_zero_iff_om]
  ext i j
  have h := congrFun (congrFun (skMat_conjTranspose_om x) (Equiv.sumEmpty (Fin N) (Fin 0) i))
    (Equiv.sumEmpty (Fin N) (Fin 0) j)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h ⊢
  rw [uToLieMat_apply, uToLieMat_apply]
  exact h

def uToLie (x : UCo N) : Formalism.BasicNotions.lieU N 0 := ⟨uToLieMat x, uToLieMat_mem x⟩

def uToLieLin : UCo N →ₗ[ℝ] Formalism.BasicNotions.lieU N 0 where
  toFun := uToLie
  map_add' x y := by
    apply Subtype.ext
    show uToLieMat (x + y) = uToLieMat x + uToLieMat y
    ext i j
    simp [uToLieMat_apply, skMat_add_om]
  map_smul' c x := by
    apply Subtype.ext
    show uToLieMat (c • x) = c • uToLieMat x
    ext i j
    simp [uToLieMat_apply, skMat_smul_om, Complex.real_smul]

theorem uToLieLin_bij : Function.Bijective (uToLieLin (N := N)) := by
  constructor
  · intro x y hxy
    have hm : ∀ a b : Fin N, skMat x a b = skMat y a b := fun a b => by
      have := congrArg (fun z : Formalism.BasicNotions.lieU N 0 =>
        (z : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) (Sum.inl a) (Sum.inl b)) hxy
      simpa [uToLieLin, uToLie, uToLieMat_apply] using this
    refine Prod.ext (funext fun a => ?_) (funext fun l => ?_)
    · have h := hm a a
      rw [skMat_diag_om, skMat_diag_om] at h
      have h' := mul_left_cancel₀ Complex.I_ne_zero h
      exact_mod_cast h'
    · have h := hm l.1.1 l.1.2
      rwa [skMat_low_om, skMat_low_om] at h
  · rintro ⟨X, hX⟩
    have hX' := (mem_lieU_zero_iff_om X).1 hX
    have hent : ∀ i j, star (X j i) = -X i j := fun i j => by
      have := congrFun (congrFun hX' i) j
      simpa [Matrix.conjTranspose_apply] using this
    refine ⟨((fun a => (X (Sum.inl a) (Sum.inl a)).im), fun l => X (Sum.inl l.1.1) (Sum.inl l.1.2)), ?_⟩
    apply Subtype.ext
    show uToLieMat _ = X
    ext i j
    rcases i with a | i
    · rcases j with b | j
      · rw [uToLieMat_apply]
        simp only [Equiv.sumEmpty_apply_inl]
        unfold skMat
        split_ifs with h1 h2 h3
        · subst h1
          have hre : (X (Sum.inl a) (Sum.inl a)).re = 0 := by
            have := congrArg Complex.re (hent (Sum.inl a) (Sum.inl a))
            simp at this
            linarith
          apply Complex.ext <;> simp [hre]
        · rfl
        · show -star (X (Sum.inl b) (Sum.inl a)) = X (Sum.inl a) (Sum.inl b)
          rw [hent (Sum.inl a) (Sum.inl b), neg_neg]
        · exact absurd (lt_trichotomy a b) (by tauto)
      · exact j.elim0
    · exact i.elim0

def uToLieE : UCo N ≃L[ℝ] Formalism.BasicNotions.lieU N 0 :=
  (LinearEquiv.ofBijective uToLieLin uToLieLin_bij).toContinuousLinearEquiv

theorem uToLieE_coe : ⇑(uToLieE (N := N)) = uToLie := rfl

def phiOmE : (UCo N × UCo N) ≃L[ℝ] ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ) :=
  (uToLieE.prodCongr uToLieE).trans complexifyLieEquiv

theorem phiOmE_apply (x y : UCo N) (p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0)) :
    phiOmE (x, y) p = skMat x (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) +
      Complex.I * skMat y (Equiv.sumEmpty (Fin N) (Fin 0) p.1) (Equiv.sumEmpty (Fin N) (Fin 0) p.2) := by
  show complexifyLieEquiv (uToLieE x, uToLieE y) p = _
  rw [complexifyLieEquiv_coe, uToLieE_coe]
  simp [Formalism.BasicNotions.entries, uToLie, uToLieMat_apply]

theorem phiOmE_haar : ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))).IsAddHaarMeasure := by
  exact phiOmE.isAddHaarMeasure_map volume
theorem gaussEOm_phiOmE (x y : UCo N) : gaussEOm (phiOmE (x, y)) = gaussUOm x * gaussUOm y := by
  have hsum : ∑ p : (Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0), Complex.normSq (phiOmE (x, y) p) =
      ∑ a, (x.1 a ^ 2 + y.1 a ^ 2) + ∑ l : LoOm N, 2 * (Complex.normSq (x.2 l) + Complex.normSq (y.2 l)) := by
    rw [← normSq_skMat_sum]
    exact Fintype.sum_equiv ((Equiv.sumEmpty (Fin N) (Fin 0)).prodCongr (Equiv.sumEmpty (Fin N) (Fin 0))) _ _
      (fun p => by rw [phiOmE_apply]; rfl)
  calc gaussEOm (phiOmE (x, y)) = Real.exp (-(∑ p, Complex.normSq (phiOmE (x, y) p))) := by
        rw [gaussEOm, ← Real.exp_sum]
        congr 1
        simp [Finset.sum_neg_distrib]
    _ = gaussUOm x * gaussUOm y := by
        rw [hsum]
        simp only [gaussUOm, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
        ring

theorem integral_gaussEOm_phiOmE : ∫ Z, gaussEOm Z ∂((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N))) =
    (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by
  rw [MeasureTheory.integral_map phiOmE.continuous.measurable.aemeasurable
    continuous_gaussEOm.aestronglyMeasurable]
  show ∫ z : UCo N × UCo N, gaussEOm (phiOmE (z.1, z.2)) = _
  simp_rw [gaussEOm_phiOmE]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (f := gaussUOm) (g := gaussUOm), integral_gaussUOm, sq]

theorem map_uToLie_haar : (Measure.map (uToLie (N := N)) volume).IsAddHaarMeasure := by
  rw [← uToLieE_coe]
  exact uToLieE.isAddHaarMeasure_map volume

private lemma prod_map_lemma (c : ENNReal) :
    ((c • Measure.map (uToLie (N := N)) volume).prod (c • Measure.map (uToLie (N := N)) volume)).map
      (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) =
      (c * c) • (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  have hm : Measurable (uToLie (N := N)) := by
    rw [← uToLieE_coe]
    exact uToLieE.continuous.measurable
  have hp : Measurable (fun ab : Formalism.BasicNotions.lieU N 0 × Formalism.BasicNotions.lieU N 0 =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) := by
    rw [← complexifyLieEquiv_coe]
    exact complexifyLieEquiv.continuous.measurable
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul (c * c) hp.aemeasurable,
    Measure.map_prod_map _ _ hm hm, Measure.map_map hp (hm.prodMap hm)]
  congr 2

private lemma vol_eq_lemma_2 :
    (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ)) =
      ENNReal.ofReal (2 ^ (N * (N - 1) / 2) * 2 ^ (N * (N - 1) / 2)) •
        (volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)) := by
  haveI := phiOmE_haar (N := N)
  have h1 := Measure.isAddLeftInvariant_eq_smul (volume : Measure ((Fin N ⊕ Fin 0) × (Fin N ⊕ Fin 0) → ℂ))
    ((volume : Measure (UCo N × UCo N)).map (phiOmE (N := N)))
  rw [ENNReal.smul_def] at h1
  have hI := integral_gaussEOm (N := N)
  rw [h1, integral_smul_measure, integral_gaussEOm_phiOmE, smul_eq_mul, ENNReal.coe_toReal] at hI
  have hk := omega_key_real (N := N)
  have hI2 : (0 : ℝ) < (Real.sqrt Real.pi ^ N * (Real.pi / 2) ^ Fintype.card (LoOm N)) ^ 2 := by positivity
  have hs := mul_right_cancel₀ hI2.ne' (hI.trans hk.symm)
  rw [h1, ← ENNReal.ofReal_coe_nnreal, hs]

theorem isOmegaLeb_uToLie :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) • Measure.map (uToLie (N := N)) volume) := by
  refine ⟨?_, ?_⟩
  · haveI := map_uToLie_haar (N := N)
    exact Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top
  · rw [prod_map_lemma, ← ENNReal.ofReal_mul (by positivity), vol_eq_lemma_2]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices

variable {N : ℕ}

theorem upMat_triCoOf_mul (t t0 : TriCo N) :
    upMat (triCoOf (upMat t * upMat t0)) = upMat t * upMat t0 ∧
      ∀ j, (triCoOf (upMat t * upMat t0)).1 j = t.1 j * t0.1 j := by
  have hU : ∀ (s : TriCo N) (a b : Fin N), upMat s a b =
      if a = b then ((s.1 a : ℝ) : ℂ) else if h : a < b then s.2 ⟨(a, b), h⟩ else 0 :=
    fun s a b => rfl
  have hz : ∀ (s : TriCo N) (a b : Fin N), b < a → upMat s a b = 0 := by
    intro s a b h
    rw [hU s a b, if_neg (ne_of_gt h), dite_eq_right (not_lt.mpr h.le)]
  have hlow : ∀ a b : Fin N, b < a → (upMat t * upMat t0) a b = 0 := by
    intro a b hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hka : k < a
    · rw [hz t a k hka, zero_mul]
    · rw [hz t0 k b (lt_of_lt_of_le hba (not_lt.mp hka)), mul_zero]
  have hdiag : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ) := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU t a a, hU t0 a a, if_pos rfl, if_pos rfl, Complex.ofReal_mul]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · rw [hz t a k h, zero_mul]
      · rw [hz t0 k a h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  refine ⟨?_, fun j => ?_⟩
  · ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hU _ a b, if_neg (ne_of_lt h), dite_eq_left h]
      rfl
    · subst h
      rw [hU _ a a, if_pos rfl]
      show (((upMat t * upMat t0) a a).re : ℂ) = (upMat t * upMat t0) a a
      rw [hdiag, Complex.ofReal_re]
    · rw [hU _ a b, if_neg (ne_of_gt h), dite_eq_right (not_lt.mpr h.le), hlow a b h]
  · show ((upMat t * upMat t0) j j).re = t.1 j * t0.1 j
    rw [hdiag, Complex.ofReal_re]

theorem triMeas_map_mul_right (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) (triMeas N) = triMeas N := by
  classical
  have hfun : (fun t : TriCo N => triCoOf (upMat t * upMat t0)) = ⇑(rmulL (upMat t0)) := by
    funext t
    rw [rmulL_apply]
  set L : TriCo N →ₗ[ℝ] TriCo N := rmulL (upMat t0) with hL
  have hdet : LinearMap.det L = ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) := det_rmulL_upMat t0 h0
  set D : ℝ := ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) with hD
  have hDpos : 0 < D := Finset.prod_pos fun j _ => pow_pos (h0 j) _
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI hC : (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hR : (volume : Measure (Fin N → ℝ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hT : (volume : Measure (TriCo N)).IsAddHaarMeasure := by
    first
      | exact Measure.prod.instIsAddHaarMeasure volume volume
      | infer_instance
  have hvol : Measure.map L (volume : Measure (TriCo N)) = ENNReal.ofReal |D⁻¹| • volume := by
    rw [← hdet]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hDpos.ne')
  have hP : MeasurableSet (triPos N) := by
    have : triPos N = ⋂ j : Fin N, {t : TriCo N | 0 < t.1 j} := by
      ext t
      simp [triPos]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)
  have hpre : ∀ S : Set (TriCo N), L ⁻¹' S ∩ triPos N = L ⁻¹' (S ∩ triPos N) := by
    intro S
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [hL, rmulL_mem_triPos t0 x h0]
  rw [hfun]
  ext s hs
  have hS : MeasurableSet (s ∩ triPos N) := hs.inter hP
  rw [Measure.map_apply hLm hs, triMeas, withDensity_apply _ (hLm hs), withDensity_apply _ hs,
    Measure.restrict_restrict (hLm hs), Measure.restrict_restrict hs, hpre s]
  have h1 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), triDens x =
      ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) := by
    refine lintegral_congr fun x => ?_
    rw [hL, hD, ← triDens_rmulL t0 x h0]
  have h2 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) =
      ENNReal.ofReal D * ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator (hLm hS)]
    congr 1
  have h3 : ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) =
      ENNReal.ofReal |D⁻¹| * ∫⁻ y in s ∩ triPos N, triDens y := by
    rw [← lintegral_map ((triDens_measurable).indicator hS) hLm, hvol, lintegral_smul_measure,
      lintegral_indicator hS]
    rfl
  rw [h1, h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul hDpos.le, abs_of_pos (inv_pos.mpr hDpos),
    mul_inv_cancel₀ hDpos.ne', ENNReal.ofReal_one, one_mul]

theorem triMeas_compact_lt_top (K : Set (TriCo N)) (hK : IsCompact K) (hK0 : K ⊆ triPos N) :
    triMeas N K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold triMeas
  rw [withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.mpr hK0]
  have hgc : ContinuousOn (fun t : TriCo N => ∏ j : Fin N, t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1))) K := by
    refine continuousOn_finsetProd _ (fun j _ => ?_)
    exact ContinuousOn.zpow₀ (by fun_prop : Continuous fun t : TriCo N => t.1 j).continuousOn _
      (fun x hx => Or.inl (hK0 hx j).ne')
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgc
  calc ∫⁻ a in K, triDens a ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
        refine setLIntegral_mono' hKm (fun x hx => ?_)
        exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC x hx))
    _ = ENNReal.ofReal C * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS
end
end
