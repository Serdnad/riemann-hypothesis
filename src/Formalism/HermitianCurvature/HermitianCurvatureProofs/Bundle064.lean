module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle058
import Aesop.Main
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Convolution

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

section IsAdjProof

variable (P : M.Par)

def adjSub : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | IsAdj a}
  mul_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).2
  add_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).1
  algebraMap_mem' z := by
    have h := (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.1 z 1 (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).1
    rw [Algebra.algebraMap_eq_smul_one]
    exact h

theorem adjSub_star {a : (DQ P).Pr} (ha : a ∈ adjSub P) : star a ∈ adjSub P :=
  (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.2 a ha

theorem gen_adj (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : w ∈ adjSub P :=
  Formalism.FourierDecayAlt.P.adjoint_generators P.r P.TT hτ w hw

abbrev MSa : Subalgebra ℂ (A P (DQ P)) := Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (adjSub P) (M.Ty P)

theorem sc_memMS (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : sc P (DQ P) w ∈ MSa P :=
  Formalism.FourierDecayAlt.P.MAx2.Jet.scalar_mem _ _ (gen_adj P hτ hw)

theorem star_memMS {a : A P (DQ P)} (ha : a ∈ MSa P) : star a ∈ MSa P := fun i j => by
  rw [Matrix.star_apply]; exact adjSub_star P (ha j i)

variable {P}

section Lv

variable (hτ : 0 ≤ P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hτ hL

theorem lv_p (l : Fin P.r) : L.p l ∈ MSa P := by
  rw [hL.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_pb (l : Fin P.r) : L.pb l ∈ MSa P := by
  rw [hL.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_c (l : Fin P.r) : L.c l ∈ MSa P := by
  rw [hL.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ci (l : Fin P.r) : L.ci l ∈ MSa P := by
  rw [hL.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cb (l : Fin P.r) : L.cb l ∈ MSa P := by
  rw [hL.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cbi (l : Fin P.r) : L.cbi l ∈ MSa P := by
  rw [hL.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem zeta_mem_self_adjoint : L.ζ ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zi : L.ζi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zb : L.ζb ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zbi : L.ζbi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_gg : L.GG ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ggi : L.GGi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_nab : L.nab ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (gen_adj P hτ (by simp [DAlg.gens]))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)
theorem lv_nabs : L.nabs ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (neg_mem (gen_adj P hτ (by simp [DAlg.gens])))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)

theorem lv_Dr : L.Dr ∈ MSa P := by
  unfold LevelData.Dr
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_c hτ hL l
theorem lv_Drb : L.Drb ∈ MSa P := by
  unfold LevelData.Drb
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cb hτ hL l
theorem lv_Dri : L.Dri ∈ MSa P := by
  unfold LevelData.Dri
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_ci hτ hL l
theorem lv_Drbi : L.Drbi ∈ MSa P := by
  unfold LevelData.Drbi
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cbi hτ hL l

theorem lv_Tprod (Y : ℂ) : L.Tprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (Subalgebra.algebraMap_mem _ _) (lv_p hτ hL l)
  · exact neg_mem (lv_c hτ hL l)
  · exact lv_ci hτ hL l
  · exact zero_mem _

theorem lv_Tvprod (Y : ℂ) : L.Tvprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tvprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tvl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact sub_mem (Subalgebra.algebraMap_mem _ _) (lv_pb hτ hL l)
  · exact neg_mem (lv_cb hτ hL l)
  · exact lv_cbi hτ hL l
  · exact zero_mem _

theorem lv_hat {X : A P (DQ P)} (hX : X ∈ hatSet P L) : X ∈ MSa P := by
  have hl0 : ∀ Y, L.l0 Y ∈ MSa P := fun Y => by
    unfold LevelData.l0
    exact sub_mem (neg_mem (lv_nab hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (lv_zb hτ hL) (lv_ggi hτ hL)))
  have hm0 : ∀ Y, L.m0 Y ∈ MSa P := fun Y => by
    unfold LevelData.m0
    exact sub_mem (neg_mem (lv_nabs hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (zeta_mem_self_adjoint hτ hL) (lv_ggi hτ hL)))
  rcases hX with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · exact mul_mem (lv_Dr hτ hL) (lv_Tprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Drb hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hl0 Y) (lv_Tprod hτ hL Y 0 0)) (lv_Tprod hτ hL Y 1 0))
  · exact mul_mem (lv_Drb hτ hL) (lv_Tvprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Dr hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hm0 Y) (lv_Tvprod hτ hL Y 0 0)) (lv_Tvprod hτ hL Y 1 0))

theorem lv_SS (i : ℕ) : SS P (DQ P) i ∈ MSa P := fun a b => by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact zero_mem _

theorem lv_kap (g : M.Ty P → ℂ) : kap P (DQ P) g ∈ MSa P := by
  have : kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) := rfl
  rw [this]
  exact Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => Subalgebra.algebraMap_mem _ _

theorem lv_bdd {b : A P (DQ P)} (hb : b ∈ bddSet P L) : b ∈ MSa P := by
  have hD : L.D ∈ MSa P := mul_mem (lv_Dr hτ hL) (zeta_mem_self_adjoint hτ hL)
  have hDi : L.Di ∈ MSa P := mul_mem (lv_zi hτ hL) (lv_Dri hτ hL)
  have hDb : L.Db ∈ MSa P := mul_mem (lv_Drb hτ hL) (lv_zb hτ hL)
  have hDbi : L.Dbi ∈ MSa P := mul_mem (lv_zbi hτ hL) (lv_Drbi hτ hL)
  have hS : ∀ i, L.Drb * L.Dri * SS P (DQ P) i ∈ MSa P := fun i =>
    mul_mem (mul_mem (lv_Drb hτ hL) (lv_Dri hτ hL)) (lv_SS hτ hL i)
  rcases hb with ((h4 | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h4
    rcases h4 with rfl | rfl | rfl | rfl
    · exact lv_zi hτ hL
    · exact lv_zbi hτ hL
    · exact mul_mem hD hDbi
    · exact mul_mem hDb hDi
  · exact lv_kap hτ hL g
  · exact hS i
  · exact star_memMS P (hS i)

end Lv

theorem transfer_is_adjoint_holds : JAIsAdj := by
  intro P L hτ hL a ha
  have hsub : Submonoid.closure (hatSet P L ∪ bddSet P L) ≤ (MSa P).toSubmonoid :=
    Submonoid.closure_le.2 fun x hx => by
      rcases hx with hx | hx
      · exact lv_hat (le_of_lt hτ) hL hx
      · exact lv_bdd (le_of_lt hτ) hL hx
  intro π π'
  exact hsub ha π π'

end IsAdjProof

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

open MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

private theorem parameter_smooth_lemma {Pm X W : Type} [NormedAddCommGroup Pm] [NormedSpace ℝ Pm]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (h : Pm → X → W) (s : Set Pm) (K : Set X) (hs : IsOpen s) (hK : IsCompact K)
    (hv : ∀ p ∈ s, ∀ x ∉ K, h p x = 0)
    (hh : ContDiffOn ℝ ∞ (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ)) :
    (∀ p ∈ s, ∀ x ∉ K, (fderiv ℝ (fun q : Pm × X => h q.1 q.2) (p, x)).comp
        (ContinuousLinearMap.inl ℝ Pm X) = 0) ∧
    ContDiffOn ℝ ∞ (fun q : Pm × X => (fderiv ℝ (fun q : Pm × X => h q.1 q.2) (q.1, q.2)).comp
        (ContinuousLinearMap.inl ℝ Pm X)) (s ×ˢ Set.univ) ∧
    ∀ p ∈ s, ∀ x, HasFDerivAt (fun p' => h p' x)
      ((fderiv ℝ (fun q : Pm × X => h q.1 q.2) (p, x)).comp (ContinuousLinearMap.inl ℝ Pm X)) p := by
  have hO : IsOpen (s ×ˢ (Set.univ : Set X)) := hs.prod isOpen_univ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp x hx
    have hU : IsOpen (s ×ˢ Kᶜ) := hs.prod hK.isClosed.isOpen_compl
    have hz : (fun q : Pm × X => h q.1 q.2) =ᶠ[nhds (p, x)] fun _ => 0 := by
      filter_upwards [hU.mem_nhds ⟨hp, hx⟩] with q hq
      exact hv q.1 hq.1 q.2 hq.2
    rw [hz.fderiv_eq]
    simp
  · have h1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (fun q : Pm × X => h q.1 q.2) q) (s ×ˢ Set.univ) :=
      hh.fderiv_of_isOpen hO (by simp)
    exact h1.clm_comp contDiffOn_const
  · intro p hp x
    have hd : DifferentiableAt ℝ (fun q : Pm × X => h q.1 q.2) (p, x) :=
      (hh.contDiffAt (hO.mem_nhds ⟨hp, trivial⟩)).differentiableAt (by simp)
    have hl : HasFDerivAt (fun e : Pm => (e, x)) (ContinuousLinearMap.inl ℝ Pm X) p :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) p x
    exact HasFDerivAt.comp (x := p) hd.hasFDerivAt hl

private theorem parameter_smooth_lemma_2 {Pm X W : Type} [NormedAddCommGroup Pm] [NormedSpace ℝ Pm]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
    [BorelSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (h : Pm → X → W) (D : Pm → X → (Pm →L[ℝ] W)) (s : Set Pm) (K : Set X)
    (hs : IsOpen s) (hK : IsCompact K)
    (hv : ∀ p ∈ s, ∀ x ∉ K, h p x = 0) (hDv : ∀ p ∈ s, ∀ x ∉ K, D p x = 0)
    (hc : ContinuousOn (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ))
    (hDc : ContinuousOn (fun q : Pm × X => D q.1 q.2) (s ×ˢ Set.univ))
    (hD : ∀ p ∈ s, ∀ x, HasFDerivAt (fun p' => h p' x) (D p x) p)
    (p0 : Pm) (hp0 : p0 ∈ s) :
    HasFDerivAt (fun p => ∫ x, h p x ∂μ) (∫ x, D p0 x ∂μ) p0 := by
  have hO : IsOpen (s ×ˢ (Set.univ : Set X)) := hs.prod isOpen_univ
  have hcont : ∀ p ∈ s, Continuous (h p) := fun p hp =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)
  have hDcont : ∀ p ∈ s, Continuous (D p) := fun p hp =>
    hDc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hDcont p0 hp0).continuousOn
  have hev : ∀ᶠ p in nhds p0, ∀ x ∈ K, ‖D p x‖ < C + 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hca : ContinuousAt (fun q : Pm × X => D q.1 q.2) (p0, x) :=
      hDc.continuousAt (hO.mem_nhds ⟨hp0, trivial⟩)
    exact hca.norm.eventually (gt_mem_nhds (lt_of_le_of_lt (hC x hx) (lt_add_one C)))
  have hS : {p | p ∈ s ∧ ∀ x ∈ K, ‖D p x‖ < C + 1} ∈ nhds p0 :=
    Filter.inter_mem (hs.mem_nhds hp0) hev
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := K.indicator fun _ => C + 1) hS
    ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs.mem_nhds hp0] with p hp
    exact (hcont p hp).aestronglyMeasurable
  · exact (hcont p0 hp0).integrable_of_hasCompactSupport (HasCompactSupport.intro hK (hv p0 hp0))
  · exact (hDcont p0 hp0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x p hp => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact (hp.2 x hx).le
    · rw [Set.indicator_of_notMem hx, hDv p hp.1 x hx, norm_zero]
  · exact (integrable_indicator_iff hK.isClosed.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
  · exact Filter.Eventually.of_forall fun x p hp => hD p hp.1 x

theorem parameter_smooth : ParamSmooth := by
  intro Pm X W _ _ _ _ _ _ _ _ _ μ _ h s K hs hK hv hh
  have key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (g : Pm → X → V),
      (∀ p ∈ s, ∀ x ∉ K, g p x = 0) →
      ContDiffOn ℝ ∞ (fun q : Pm × X => g q.1 q.2) (s ×ˢ Set.univ) →
      ContDiffOn ℝ n (fun p => ∫ x, g p x ∂μ) s := by
    intro n
    induction n with
    | zero =>
      intro V _ _ g hgv hg
      obtain ⟨hDv, hDs, hD⟩ := parameter_smooth_lemma g s K hs hK hgv hg
      have hdiff : DifferentiableOn ℝ (fun p => ∫ x, g p x ∂μ) s := fun p hp =>
        (parameter_smooth_lemma_2 μ g _ s K hs hK hgv hDv hg.continuousOn hDs.continuousOn hD p
          hp).differentiableAt.differentiableWithinAt
      exact contDiffOn_zero.2 hdiff.continuousOn
    | succ n ih =>
      intro V _ _ g hgv hg
      obtain ⟨hDv, hDs, hD⟩ := parameter_smooth_lemma g s K hs hK hgv hg
      have hder := fun p hp =>
        parameter_smooth_lemma_2 μ g _ s K hs hK hgv hDv hg.continuousOn hDs.continuousOn hD p hp
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun p hp => (hder p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (Pm →L[ℝ] V) (fun p x => (fderiv ℝ (fun q : Pm × X => g q.1 q.2) (p, x)).comp
        (ContinuousLinearMap.inl ℝ Pm X)) hDv hDs).congr fun p hp => (hder p hp).fderiv
  exact contDiffOn_infty.2 fun n => key n W h hv hh

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def PolyOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  ∀ Tm ∈ Θ, Tm.word.length ≤ o ∧ ∃ P : B.Mat k r → ℂ, U.IsPolyDeg κ P ∧
    (∀ g, Tm.coef g = P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) ∧
    ∀ g, Tm.coefAdj g = star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)

def JDPolyOK : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq),
    PolyOp o κ Θ → (∀ UU : Set (B.Mat k r), B.SmoothCoef UU Θ) ∧ (∀ d : ℝ, (κ : ℝ) ≤ d → GlobCoef Θ d) ∧
      B.opOrder Θ ≤ o

def JDCapA : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℂ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (L.Ahat y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (L.Ahatv y) (trJ S T v e J)

def JDCapR : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℝ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (RhM (D.parOf S v) L y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (RhvM (D.parOf S v) L y) (trJ S T v e J)

theorem hatOK_of_poly (hP : JDPolyOK) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cc : ℝ} (hCc : 1 ≤ Cc) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}
    {Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    (hΘ : PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ)
    (hc : B.Commutes (T v).base (B.GPos (T v).base) Θ) : HatOK Cc S T v Θ := by
  obtain ⟨hs, hg, ho⟩ := hP S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) _ _ Θ hΘ
  have hn : (0 : ℝ) ≤ nDim S.G.k S.G.r := by unfold nDim; positivity
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  refine ⟨hs _, hc, hg _ ?_, ?_⟩
  · have e1 : (((S.G.r + 1) * (2 * S.G.r + S.G.k + 1) : ℕ) : ℝ) = ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
      unfold nDim; push_cast; ring
    rw [e1, mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg hr hn) hCc
  · have e2 : ((B.opOrder Θ : ℕ) : ℝ) ≤ nDim S.G.k S.G.r := by
      unfold nDim; exact_mod_cast ho
    exact e2.trans (le_mul_of_one_le_left hn hCc)

theorem jDOpA_of_parts (hP : JDPolyOK) (hC : JDCapA) : JDOpA := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩

theorem jDOpR_of_parts (hP : JDPolyOK) (hC : JDCapR) : JDOpR := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end
