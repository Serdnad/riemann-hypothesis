module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Nullstellensatz
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem specFirstVar_isWeightedHomogeneous {k n : ℕ} (u : Fin n → ℂ) (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X ℂ (groupWeight k n) (i', j)

theorem SpecFirstHomog.proof : SpecFirstHomog.Statement := by
  intro n k δ f u hf
  unfold IsMultiHomog specFirst

  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous u ij).pow _

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

open MeasureTheory Matrix

namespace GroundTheory.Heights₂.Heights

theorem FsLogAverage.proof (h1 : BallAverageLinear.Statement) (h2 : FsLogPointOf.Statement)
    (h3 : SphereMeanLinearBall.Statement) (h4 : BallVolume.Statement) : FsLogAverage.Statement := by
  intro n h y hy
  set y' : Fin n → ℂ := fun i => y i with hy'def
  have hy' : y' ≠ 0 := by
    intro hz
    apply hy
    ext i
    exact congrFun hz i
  set φ : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y' with hφ
  have hrw : (fun v => fsLog h (nrmv h v) (h.pointOf y)) = fun v => φ (h.mat *ᵥ v) := by
    funext v
    exact h2 n h v y
  obtain ⟨hint, hle, hmean⟩ := h3 n y' hy'
  have habs : (fun w => |φ w|) = fun w => -φ w := by
    funext w
    exact abs_of_nonpos (hle w)
  have hmeanAbs : ⨍ v in ballH h, |φ (h.mat *ᵥ v)| = (harmonic (n - 1) : ℝ) / 2 := by
    rw [(h1 n h (fun w => |φ w|)).2, habs]
    change (⨍ w in ballH (HermNorm.std n), (-φ) w) = _
    rw [average_neg, hmean]
    ring
  obtain ⟨_, hfin⟩ := h4 n h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrw]
    exact (h1 n h φ).1.mpr hint
  · simp only [show ∀ v, fsLog h (nrmv h v) (h.pointOf y) = φ (h.mat *ᵥ v) from fun v => h2 n h v y]
    rw [← measure_smul_setAverage _ hfin.ne, hmeanAbs, smul_eq_mul, measureReal_def]
    ring
  · rw [hrw, (h1 n h φ).2]
    exact hmean

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

theorem FsLogMeasurable.proof : FsLogMeasurable.Statement := by
  intro n h
  have hn : Continuous h.norm := by
    unfold HermNorm.norm
    fun_prop
  have hd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hp : Continuous h.pointOf := by
    unfold HermNorm.pointOf
    fun_prop
  have hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp hn).measurable.inv
  have hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1 := by
    unfold nrmv
    refine Measurable.of_eval fun j => ?_
    exact (hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)
  have hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2 :=
    hp.measurable.comp measurable_snd
  unfold fsLog
  refine Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))
  refine Measurable.norm ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem mahler_specFirst_eq (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by
  unfold mahler
  congr 1
  funext w
  rw [h3]

theorem MahlerAverageSplit.proof (h1 : MahlerIntegrand.Statement) (h2 : SphereMeanFubini.Statement)
    (h3 : EvalSpecFirst.Statement) : MahlerAverageSplit.Statement := by
  intro n e δ h f hf hhom
  have hint := h1 n (e + 1) δ h f hf hhom
  obtain ⟨hI, hM⟩ := h2 n e h (fun u => Real.log ‖eval u f‖) hint
  have key : (fun v => mahler h e (specFirst f (nrmv h v))) =
      fun v => sphereMean h e (fun w => Real.log ‖eval (consGroup (nrmv h v) w) f‖) := by
    funext v
    exact mahler_specFirst_eq h3 h f (nrmv h v)
  rw [key]
  exact ⟨hI, hM⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem MahlerSectionOfConst.proof (h1 : DefectAverage.Statement) (h2 : AdmissibleAENrm.Statement)
    (h3 : BallVolume.Statement) : MahlerSectionOfConst.Statement := by
  intro e hconst n δ h Z f u data hu
  set K := mahlerDefect h e Z f u with hK
  have hrel : ∀ W ∈ Z.support, IsRelevant W := fun W hW => (data.prime W hW).isRelevant
  have hae : (fun v => mahlerDefect h e Z f (nrmv h v)) =ᵐ[volume.restrict (ballH h)] fun _ => K := by
    filter_upwards [h2 n h Z hrel] with v hv
    exact hconst n δ h Z f (nrmv h v) u data hv hu
  have havg : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = K := by
    rw [average_congr hae]
    obtain ⟨hpos, hfin⟩ := h3 n h
    exact setAverage_const hpos.ne' hfin.ne K
  have hmean := (h1 n e δ h Z f data).2
  rw [havg] at hmean
  have hK' : K = mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u) := rfl
  linarith
end Heights
end Heights₂
end GroundTheory
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set

noncomputable section

namespace SphereMeanFubini

def groupSplit (k n : ℕ) : Fin n ⊕ (Fin k × Fin n) ≃ Fin (k + 1) × Fin n where
  toFun := Sum.elim (fun j => (0, j)) (fun p => (p.1.succ, p.2))
  invFun p := Fin.cases (motive := fun _ => Fin n ⊕ (Fin k × Fin n)) (Sum.inl p.2)
    (fun i => Sum.inr (i, p.2)) p.1
  left_inv := by rintro (j | ⟨i, j⟩) <;> simp
  right_inv := by
    rintro ⟨i, j⟩
    cases i using Fin.cases <;> simp

def consEquiv {n : ℕ} (k : ℕ) : ((Fin n → ℂ) × (Fin k × Fin n → ℂ)) ≃ᵐ (Fin (k + 1) × Fin n → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ (Fin k × Fin n) => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (groupSplit k n))

theorem consEquiv_apply {n k : ℕ} (p : (Fin n → ℂ) × (Fin k × Fin n → ℂ)) :
    consEquiv k p = consGroup p.1 p.2 := by
  funext ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
    have e : ((0 : Fin (k + 1)), j) = groupSplit k n (Sum.inl j) := rfl
    rw [e]
    simp [consEquiv, consGroup, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_apply]
    rfl
  | succ i =>
    have e : (i.succ, j) = groupSplit k n (Sum.inr (i, j)) := rfl
    rw [e]
    simp [consEquiv, consGroup, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_apply]
    rfl

theorem measurePreserving_consEquiv {n : ℕ} (k : ℕ) :
    MeasurePreserving (consEquiv (n := n) k) volume volume :=
  (measurePreserving_piCongrLeft (fun _ : Fin (k + 1) × Fin n => (volume : Measure ℂ))
    (groupSplit k n)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ (Fin k × Fin n) => (volume : Measure ℂ)))

theorem preimage_ballProd {n : ℕ} (h : HermNorm n) (k : ℕ) :
    consEquiv k ⁻¹' ballProd h (k + 1) = ballH h ×ˢ ballProd h k := by
  ext p
  simp only [mem_preimage, consEquiv_apply, ballProd, mem_ofPred_eq, mem_prod, ballH,
    Fin.forall_fin_succ, consGroup, Fin.cases_zero, Fin.cases_succ]

theorem nrmGroups_consGroup {n : ℕ} (h : HermNorm n) (k : ℕ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) :
    nrmGroups h (k + 1) (consGroup v w) = consGroup (nrmv h v) (nrmGroups h k w) := by
  funext ⟨i, j⟩
  cases i using Fin.cases <;> simp [nrmGroups, consGroup, nrmv]

theorem proof : SphereMeanFubini.Statement := by
  intro n k h G hG
  have hmp := measurePreserving_consEquiv (n := n) k
  have hme := (consEquiv (n := n) k).measurableEmbedding
  have hpre := preimage_ballProd h k
  set H : (Fin n → ℂ) × (Fin k × Fin n → ℂ) → ℝ :=
    fun p => G (nrmGroups h (k + 1) (consEquiv k p)) with hH
  have hHi : IntegrableOn H (ballH h ×ˢ ballProd h k) (volume.prod volume) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hme (f := fun u => G (nrmGroups h (k + 1) u))).2 hG
  have hint : ∫ p in ballH h ×ˢ ballProd h k, H p ∂(volume.prod volume) =
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb hme (fun u => G (nrmGroups h (k + 1) u)) _
  have hvol : volume (ballProd h (k + 1)) = volume (ballH h) * volume (ballProd h k) := by
    rw [← hmp.measure_preimage_equiv, hpre, Measure.volume_eq_prod, Measure.prod_prod]
  rw [IntegrableOn, ← Measure.prod_restrict] at hHi
  rw [← Measure.prod_restrict, integral_prod _ hHi] at hint
  have hB0 : (volume (ballProd h k)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(volume_ballProd_pos h k).ne', (volume_ballProd_lt_top h k).ne⟩
  have hinner : ∀ v, sphereMean h k (fun w => G (consGroup (nrmv h v) w)) =
      (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) := by
    intro v
    simp only [hH, consEquiv_apply, nrmGroups_consGroup]
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  have hfun : (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) =
      fun v => (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) :=
    funext hinner
  have hlhs : sphereMean h (k + 1) G = (volume (ballProd h (k + 1))).toReal⁻¹ *
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHi.integral_prod_left.const_mul _
  · rw [hlhs, ← hint, hvol, setAverage_eq, smul_eq_mul, measureReal_def, hfun, integral_const_mul,
      ENNReal.toReal_mul, mul_inv]
    ring

end SphereMeanFubini

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowDegreePos.proof : ChowDegreePos.Statement := by
  intro n k δ W g hk hW hg hδ
  by_contra hlt
  have hδ0 : δ = 0 := by omega
  subst hδ0

  have hnt : NonTorsionWeight (groupWeight k n) := by
    intro m ij h
    have := congrFun h ij.1
    simpa [groupWeight] using this

  have hsupp : ∀ m ∈ g.support, m = 0 := by
    intro m hm
    have h1 : Finsupp.weight (groupWeight k n) m = 0 := hδ (mem_support_iff.1 hm)
    ext ij
    exact (weightedDegree_eq_zero_iff hnt).1 h1 ij
  obtain ⟨c, rfl⟩ : ∃ c, g = C c := by
    refine ⟨AddMonoidAlgebra.coeff g 0, ?_⟩
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      exact hm (hsupp m (mem_support_iff.2 hne)).symm
  have hc : c ≠ 0 := by
    intro h
    apply hg.1
    rw [h, C_0]
  have hdvd : (C c : MvPolynomial (Fin k × Fin n) ℂ) ∣ 1 :=
    ⟨C c⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hvan := (hg.2 1).2 hdvd

  obtain ⟨x, hx0, hx⟩ : ∃ x : Fin n → AlgebraicClosure ℂ, x ≠ 0 ∧ ∀ p ∈ W, aeval x p = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hW.isRelevant
    apply hj
    have hrad : X j ∈ W.radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℂ)]
      rw [mem_vanishingIdeal_iff]
      intro y hy
      by_cases hy0 : y = 0
      · subst hy0
        simp
      · exact absurd ⟨y, hy0, hy⟩ hne
    rwa [hW.isPrime.radical] at hrad
  have hmem : (0 : Fin k × Fin n → AlgebraicClosure ℂ) ∈ incidence W k :=
    ⟨x, hx0, hx, fun i => by simp⟩
  have := hvan 0 hmem
  simp at this

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Matrix

noncomputable section

namespace BallAverageLinear

def matEquiv {n : ℕ} (h : HermNorm n) : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (f := (Matrix.mulVecLin h.mat).restrictScalars ℝ)
      (g := (Matrix.mulVecLin h.mat⁻¹).restrictScalars ℝ)
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h.isUnit_det])
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]))

theorem matEquiv_apply {n : ℕ} (h : HermNorm n) (v : Fin n → ℂ) : matEquiv h v = h.mat *ᵥ v := rfl

theorem ballH_eq_preimage {n : ℕ} (h : HermNorm n) :
    ballH h = matEquiv h ⁻¹' ballH (HermNorm.std n) := by
  ext v
  simp [ballH, HermNorm.norm, HermNorm.std, matEquiv_apply]

end BallAverageLinear

open BallAverageLinear in
theorem BallAverageLinear.proof : BallAverageLinear.Statement := by
  intro n h φ
  set L := matEquiv h
  have hb := ballH_eq_preimage h
  have hpre : ∀ s : Set (Fin n → ℂ), IntegrableOn (fun v => φ (h.mat *ᵥ v)) (L ⁻¹' s) ↔
      IntegrableOn φ s := by
    intro s
    have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
    have hmap : (map L volume).IsAddHaarMeasure := L.isAddHaarMeasure_map volume
    have h2 : map L (volume : Measure (Fin n → ℂ)) =
        addHaarScalarFactor (map L volume) volume • volume := isAddLeftInvariant_eq_smul _ _
    have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L (volume : Measure (Fin n → ℂ))) volume
    rw [show (fun v => φ (h.mat *ᵥ v)) = φ ∘ L from rfl, ← he.integrableOn_map_iff, h2,
      show (addHaarScalarFactor (map L volume) volume • (volume : Measure (Fin n → ℂ))) =
        ((addHaarScalarFactor (map L volume) volume : ENNReal) • volume) from rfl,
      IntegrableOn, IntegrableOn, Measure.restrict_smul,
      integrable_smul_measure (by simpa using hpos.ne') ENNReal.coe_ne_top]
  refine ⟨by rw [hb]; exact hpre _, ?_⟩
  rw [hb]
  exact SphereMean.setAverage_comp_linearEquiv volume volume L _ φ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem ballProd_subset_polydisc {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem MahlerIntegrand.proof : MahlerIntegrand.Statement := by
  intro n k δ h f hf _
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  have e : nrmGroups h k = LogInt.normT h Finset.univ := by
    funext u ij
    simp [nrmGroups, LogInt.normT]
  rw [e]
  exact (LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)

end GroundTheory.Heights₂.Heights
end
