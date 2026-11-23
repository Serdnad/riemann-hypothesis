module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem continuous_opBeta (k : ℕ) (a : Fin k) : Continuous (fun q : TrE k => opBeta k q a) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  unfold opBeta
  exact ((hq _).add ((hq _).mul continuous_const)).div_const _

theorem continuous_opGen (k r : ℕ) : Continuous (opGen k r : TrE k → Mat k r) := by

  have hq : ∀ i, Continuous (fun q : TrE k => ((q i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  unfold opGen
  split_ifs
  all_goals first
    | exact continuous_const
    | exact continuous_opBeta k _
    | exact (continuous_opBeta k _).star
    | exact (hq none).mul continuous_const

theorem continuous_opEmap (k r : ℕ) (T' : ℝ) :
    Continuous (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) := by

  letI : NormedRing (Mat k r) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mat k r) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Mat k r) := Matrix.linftyOpNormedAlgebra
  have h1 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q)) :=
    NormedSpace.exp_continuous.comp (continuous_opGen k r)
  have h2 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') :=
    h1.matrix_mulVec continuous_const
  unfold opCo
  exact (continuous_pi (fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp h2)).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp h2)

theorem opEMeas : OpEMeas := by

  intro k r T' ρ
  unfold opE
  have hball : Metric.ball (0 : TrE k) ρ = ⋃ n : ℕ, Metric.closedBall 0 (ρ - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Metric.mem_ball, Metric.mem_closedBall, Set.mem_iUnion, dist_zero_right]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hball, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun n => ?_)
  exact ((isCompact_closedBall _ _).image (continuous_opEmap k r T')).isClosed.measurableSet

theorem normSq_sum_eq (k : ℕ) (y : EuclideanSpace ℂ (Fin k)) : ∑ i, Complex.normSq (y i) = ‖y‖ ^ 2 := by

  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl (fun i _ => by rw [Complex.sq_norm])

theorem hypPar_mem (k : ℕ) (T' : ℝ) (hT' : 0 < T') (q : EuclideanSpace ℂ (Fin k) × ℝ) :
    hypPar k T' q ∈ hypS k T' := by

  have h1 : Complex.normSq (Complex.exp (q.2 * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  simp only [hypS, hypPar, Set.mem_setOf_eq]
  rw [normSq_sum_eq, Complex.normSq_mul, Complex.normSq_ofReal, h1, mul_one,
    Real.mul_self_sqrt (by positivity)]
  ring

theorem hypLF : HypLF := by
  intro k T' hT'
  have hcont : Continuous (hypPar k T') := by
    unfold hypPar
    refine (continuous_pi (fun i => ?_)).prodMk ?_
    · exact (EuclideanSpace.proj i).continuous.comp continuous_fst
    · refine (Complex.continuous_ofReal.comp ?_).mul ?_
      · exact Real.continuous_sqrt.comp (((continuous_norm.comp continuous_fst).pow 2).add continuous_const)
      · exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hmeas : Measurable (hypPar k T') := hcont.measurable
  have hSc : IsClosed (hypS k T') := by
    have h1 : Continuous (fun p : (Fin k → ℂ) × ℂ => ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2) :=
      (continuous_finsetSum _ (fun i _ => Complex.continuous_normSq.comp ((continuous_apply i).comp continuous_fst))).sub
        (Complex.continuous_normSq.comp continuous_snd)
    exact isClosed_eq h1 continuous_const
  constructor
  · unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hSc.measurableSet.compl]
    have h2 : hypPar k T' ⁻¹' (hypS k T')ᶜ = ∅ := by
      ext q
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact hypPar_mem k T' hT' q
    rw [h2, measure_empty, smul_zero]
  · intro C hC
    obtain ⟨R, hR⟩ := (hC.image continuous_fst).isBounded.exists_norm_le
    have hsub : hypPar k T' ⁻¹' C ⊆
        Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ := by
      intro q hq
      refine ⟨?_, Set.mem_univ _⟩
      have h1 : ‖(hypPar k T' q).1‖ ≤ R := hR _ ⟨_, hq, rfl⟩
      have h2 : ∀ i, ‖q.1 i‖ ≤ R := fun i => le_trans (norm_le_pi_norm (hypPar k T' q).1 i) h1
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖q.1 i‖ ^ 2 ≤ ∑ i : Fin k, R ^ 2 :=
            Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h2 i) 2)
        _ = k * R ^ 2 := by simp
    unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hC.isClosed.measurableSet, smul_eq_mul]
    refine ENNReal.mul_lt_top (ENNReal.div_lt_top ENNReal.one_ne_top two_ne_zero) ?_
    calc _ ≤ (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))
          (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ) :=
          measure_mono hsub
      _ = volume (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2))) *
          volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) Set.univ := Measure.prod_prod _ _
      _ < ⊤ := by
        apply ENNReal.mul_lt_top measure_closedBall_lt_top
        rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top

end PI.RhsWLim.W
end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem herm_mulVec_right {p : Mat k r} (hp : p ∈ UH (Hpk k r)) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (p *ᵥ u) = herm (Hpk k r) (p⁻¹ *ᵥ v) u := by
  have hu := HU.isUnit_of_uh hp
  have hp' : pᴴ * Hpk k r * p = Hpk k r := hp
  have key : pᴴ * Hpk k r = Hpk k r * p⁻¹ := by
    calc pᴴ * Hpk k r = pᴴ * Hpk k r * (p * p⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (pᴴ * Hpk k r * p) * p⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * p⁻¹ := by rw [hp']
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]

theorem tau_wLast : HU.tau k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
  unfold HU.tau wI
  apply Fin.ext
  simp only [Fin.val_last]
  split_ifs <;> omega

theorem sgn_wLast : HU.sgn k r (wI k r (Fin.last k)) = -1 := by
  unfold HU.sgn wI
  simp

theorem hpk_mulVec_wLast (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (wI k r (Fin.last k)) = -v (wI k r (Fin.last k)) := by
  simp only [Matrix.mulVec, dotProduct, HU.hpk_row, tau_wLast, sgn_wLast, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem herm_wLast (v : Fin (2 * r + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k r) v ((s : ℂ) • wLast k r) = -((s : ℂ) * v (wI k r (Fin.last k))) := by
  have hs : star ((s : ℂ) • wLast k r) = Pi.single (wI k r (Fin.last k)) (s : ℂ) := by
    funext j
    simp only [wLast, bvec, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  unfold herm
  rw [hs, single_dotProduct, hpk_mulVec_wLast, mul_neg]

theorem pairF_std (z' : Fin (2 * r + k + 1) → ℂ) (s : ℝ) (x : Mt k r) :
    pairF k r ((s : ℂ) • wLast k r) z' x = -((s : ℂ) * (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) :=
  herm_wLast _ _

theorem rmulM_cont (p : Mat k r) : Continuous (rmulM p : Mt k r → Mt k r) := by
  unfold rmulM
  exact (continuous_id (X := Mat k r)).matrix_mul continuous_const

theorem continuous_coords (z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => ((fun i : Fin k => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i))),
      (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) := by
  have hc : Continuous fun x : Mt k r => Matrix.of x *ᵥ z' :=
    Continuous.matrix_mulVec (continuous_id (X := Mat k r)) continuous_const
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)

theorem orbitPushG_of (hO : OrbitPush) (hT : TransW) (hU : UnimodW) : OrbitPushG := by
  intro k r z' hk hz' hT' νg hG f hf
  obtain ⟨p, hp, hpz⟩ := hT k r z' hz' hT'
  set zs := ((Real.sqrt (Tz k r z') : ℂ) • wLast k r) with hzs
  have hFm := hf.comp (continuous_coords (k := k) (r := r) zs).measurable
  have e : ∀ x : Mt k r, Matrix.of x *ᵥ z' = Matrix.of (rmulM p x) *ᵥ zs := by
    intro x
    rw [← hpz]
    show Matrix.of x *ᵥ (p *ᵥ zs) = (Matrix.of x * p) *ᵥ zs
    rw [Matrix.mulVec_mulVec]
  calc ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg
      = ∫⁻ x, (fun y : Mt k r => f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k)))) (rmulM p x) ∂νg := by
        refine lintegral_congr fun x => ?_
        simp only [e x]
    _ = ∫⁻ y, f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k))) ∂(νg.map (rmulM p)) :=
        (lintegral_map hFm (rmulM_cont p).measurable).symm
    _ = _ := by
        rw [hU k r νg hk hG p hp]
        exact hO k r (Tz k r z') hk hT' νg hG f hf

theorem pairPush_of (hT : TransW) (hO : OrbitPushG) (h4 : PolarHyp) (h5 : VolURatio) : PairPush := by
  intro k r νg hk hG z z' hz hz' hTz hTz' g hg
  obtain ⟨p, hp, hpz⟩ := hT k r z hz hTz
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hTz).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs

  have e1 : ∀ x : Mt k r, pairF k r z z' x = pairF k r zs z' (lmulM p⁻¹ x) := by
    intro x
    unfold pairF
    rw [← hpz, herm_mulVec_right hp.1, Matrix.mulVec_mulVec]
    rfl
  have hgm : Measurable fun y : Mt k r => g (pairF k r zs z' y) := hg.comp (continuous_pairF k r zs z').measurable
  have hpinv := HU.uwb_inv hp
  have step1 : ∫⁻ x, g (pairF k r z z' x) ∂νg = ∫⁻ y, g (pairF k r zs z' y) ∂νg := by
    calc ∫⁻ x, g (pairF k r z z' x) ∂νg = ∫⁻ x, (fun y => g (pairF k r zs z' y)) (lmulM p⁻¹ x) ∂νg := by
          refine lintegral_congr fun x => ?_
          simp only [e1 x]
      _ = ∫⁻ y, g (pairF k r zs z' y) ∂(νg.map (lmulM p⁻¹)) :=
          (lintegral_map hgm (HU.lmulM_cont _).measurable).symm
      _ = _ := by rw [hG.1.2.2.2 _ hpinv]

  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 := hO k r z' hk hz' hTz' νg hG f hfm

  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := h4 k (Tz k r z) (Tz k r z') hk hTz hTz' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  rw [step1]
  have e2 : ∫⁻ y, g (pairF k r zs z' y) ∂νg = ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg := by
    refine lintegral_congr fun x => ?_
    rw [pairF_std]
  rw [e2, step2]
  have e3 : hypMeas k (Tz k r z') f =
      hypMeas k (Tz k r z') (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [e3, step3]
  simp only [hGdef, hcancel]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := volU_pos k; positivity)]
  congr 2
  have hV := h5 k hk
  have h1 := volU_pos (k - 1)
  have h2 : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
  have h3 := Real.pi_pos
  have h4 : Tz k r z ≠ 0 := hTz.ne'
  have h5 : Tz k r z' ≠ 0 := hTz'.ne'
  unfold pairConst
  rw [hV]
  field_simp
  ring

theorem constVal_of_polarHyp (hR : RhsTest) (hT : TransW) (hU : UnimodW) (hO : OrbitPush) (h4 : PolarHyp) :
    ConstVal :=
  constVal_of hR (pairPush_of hT (orbitPushG_of hO hT hU) h4 volURatio)

end PI.RhsWLim.W
end
end
