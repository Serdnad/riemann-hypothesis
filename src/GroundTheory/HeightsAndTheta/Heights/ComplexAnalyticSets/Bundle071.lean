module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionCluster
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle042
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Polynomial
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.AnalyticCharts.OsgoodA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeDeepMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      Integrable ({y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def deepMap {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  vecCons (eval y P) fun i => s y (I i)

def deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) (y : Fin (d + 1) → ℂ) : ℂ :=
  LinearMap.det ((fderiv ℂ (deepMap P s I) y : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))

def TubeDeepRankOne.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (U : Set (Fin (d + 1) → ℂ)) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ),
    IsOpen U → y ∈ U → DifferentiableOn ℂ s U → (∀ y' ∈ U, A *ᵥ s y' = y') → eval y P ≠ 0 →
      ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y =
        (2 / Real.pi) ^ (d + 1) * ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 / ‖eval y P‖ ^ 2

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeEuclMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 → Integrable (tubeDens J A P R (fun _ => euclPot))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeFormCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      ∃ C : ℝ, ∀ y, tubeDens J A P R φ y ≤ C * tubeDens J A P R (fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem hessC_of_eventually_const {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {c : ℝ}
    (h : φ =ᶠ[𝓝 y] fun _ => c) : hessC φ y = 0 ∧ hessC (fun z => φ z ^ 2 / 2) y = 0 := by
  have h2 : (fun z => φ z ^ 2 / 2) =ᶠ[𝓝 y] fun _ => c ^ 2 / 2 := by
    filter_upwards [h] with z hz
    rw [hz]
  have hc : ∀ a : ℝ, hessC (fun _ : Fin D → ℂ => a) y = 0 := by
    intro a
    ext i j
    simp [hessC]
  exact ⟨(hessC_congr' h).trans (hc c), (hessC_congr' h2).trans (hc _)⟩

theorem cutStep_of_one_le {s : ℝ} (hs : 1 ≤ s) : cutStep s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutStep_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : cutStep s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem continuousAt_normSq_eval {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    ContinuousAt (fun z => ‖eval z Q‖ ^ 2) y :=
  ((AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)).continuousAt.norm).pow 2

theorem logLogCut_eventually_zero {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : ‖eval y Q‖ ^ 2 < cutLevel k) : logLogCut Q k =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Iio_mem_nhds hy)] with z hz
  have hz : ‖eval z Q‖ ^ 2 < cutLevel k := hz
  have hlt := (cutLevel_mem k).2
  unfold logLogCut
  split_ifs with h0 h1
  · rfl
  · linarith
  · have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have e1 : Real.log (‖eval z Q‖ ^ 2) < -Real.exp ((k : ℝ) + 1) :=
      (Real.log_lt_iff_lt_exp hw0).2 hz
    have e2 : (k : ℝ) + 1 < Real.log (-logAbsSq Q z) :=
      (Real.lt_log_iff_exp_lt (by rw [logAbsSq]; linarith [Real.exp_pos ((k : ℝ) + 1)])).2
        (by rw [logAbsSq]; linarith)
    apply cutStep_of_one_le
    rw [le_div_iff₀ (by positivity)]
    linarith

theorem logLogCut_eventually_one {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (hy : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval y Q‖ ^ 2) :
    logLogCut Q k =ᶠ[𝓝 y] fun _ => 1 := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioi_mem_nhds hy)] with z hz
  have hz : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < ‖eval z Q‖ ^ 2 := hz
  have hw0 : 0 < ‖eval z Q‖ ^ 2 := lt_trans (Real.exp_pos _) hz
  unfold logLogCut
  split_ifs with h0 h1
  · linarith
  · rfl
  · have hw1 : ‖eval z Q‖ ^ 2 < 1 := not_le.1 h1
    have e1 : -Real.exp (((k : ℝ) + 1) / 2) < Real.log (‖eval z Q‖ ^ 2) :=
      (Real.lt_log_iff_exp_lt hw0).2 hz
    have e0 : Real.log (‖eval z Q‖ ^ 2) < 0 := Real.log_neg hw0 hw1
    have e2 : Real.log (-logAbsSq Q z) < ((k : ℝ) + 1) / 2 :=
      (Real.log_lt_iff_lt_exp (by rw [logAbsSq]; linarith)).2 (by rw [logAbsSq]; linarith)
    apply cutStep_of_le_half
    rw [div_le_iff₀ (by positivity)]
    linarith

theorem logLogCut_eventually_step {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (h0 : 0 < ‖eval y Q‖ ^ 2) (h1 : ‖eval y Q‖ ^ 2 < 1) :
    logLogCut Q k =ᶠ[𝓝 y] fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioo_mem_nhds h0 h1)] with z hz
  have hz : ‖eval z Q‖ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := hz
  unfold logLogCut
  rw [if_neg hz.1.ne', if_neg (not_le.2 hz.2)]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Topology

noncomputable section

namespace FiniteProjectionCluster

variable {n d : ℕ}

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by
    ext x; simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem exists_monic (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (j : Fin n) :
    ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧
      ∀ x ∈ zeroSet J, (P.map (eval (A.mulVec x))).IsRoot (x j) := by
  obtain ⟨P, hPm, hP⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (X j))
  refine ⟨P, hPm, fun x hx => ?_⟩
  have hf : (projHom J A).toRingHom = (Ideal.Quotient.mk J).comp (pullback A).toRingHom := rfl
  rw [hf, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hP
  have h0 := hx _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) :=
    RingHom.ext (FibreBound.eval_pullback A x)
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

theorem exists_bound (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (c : Fin d → ℂ) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ zeroSet J, dist (A.mulVec x) c ≤ R → ‖x‖ ≤ C := by
  choose P hPm hP using exists_monic J A hA
  let g : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval y ((P j).coeff i)‖)
  have hg : Continuous g :=
    continuous_finsetSum _ fun j _ => continuous_const.add
      (continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).norm)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x hx hd => ?_⟩
  have hy : A.mulVec x ∈ Metric.closedBall c R := hd
  have hgC : g (A.mulVec x) ≤ C := (Real.le_norm_self _).trans (hC _ hy)
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hC _ hy))).2 fun j => ?_
  have hj := IndefiniteRowSideFullHecke.ComplexSets.norm_lt_of_isRoot_map_eval (hPm j) (A.mulVec x) (hP j x hx)
  have hle : (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval (A.mulVec x) ((P j).coeff i)‖) ≤
      g (A.mulVec x) :=
    Finset.single_le_sum (f := fun j => 1 + ∑ i ∈ Finset.range (P j).natDegree,
      ‖eval (A.mulVec x) ((P j).coeff i)‖)
      (fun k _ => add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Finset.mem_univ j)
  linarith

theorem fibre_finite (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (y : Fin d → ℂ) :
    {x | x ∈ zeroSet J ∧ A.mulVec x = y}.Finite := by
  choose P hPm hP using exists_monic J A hA
  refine (Set.Finite.pi (t := fun j => {a | ((P j).map (eval y)).IsRoot a})
    fun j => Polynomial.finite_setOfPred_isRoot ((hPm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxA⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro j
  rw [← hxA]
  exact hP j x hx

end FiniteProjectionCluster


open FiniteProjectionCluster in
theorem FiniteProjectionCluster.proof : FiniteProjectionCluster.Statement := by
  intro n d J A w U hA hw hU
  have hcont : Continuous fun x : Fin n → ℂ => A.mulVec x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  obtain ⟨C, hC⟩ := exists_bound J A hA (A.mulVec w) 1
  have hF := fibre_finite J A hA (A.mulVec w)
  obtain ⟨ε0, hε0, hballU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, ⟨hε, hεlt⟩, hεF⟩ :=
    ((Set.Ioo_infinite hε0).sdiff (hF.image fun x => dist x w)).nonempty
  set K := zeroSet J ∩ {x | dist (A.mulVec x) (A.mulVec w) ≤ 1} ∩ Metric.sphere w ε with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact ((isClosed_zeroSet J).inter (isClosed_le (hcont.dist continuous_const)
        continuous_const)).inter Metric.isClosed_sphere
    · exact (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx =>
        mem_closedBall_zero_iff.2 (hC x hx.1.1 hx.1.2)
  have hT : IsCompact (A.mulVec '' K) := hKc.image hcont
  have hnot : A.mulVec w ∉ A.mulVec '' K := by
    rintro ⟨x, ⟨⟨hx, _⟩, hxs⟩, hxA⟩
    exact hεF ⟨x, ⟨hx, hxA⟩, hxs⟩
  obtain ⟨r0, hr0, hr0T⟩ := Metric.isOpen_iff.1 hT.isClosed.isOpen_compl _ hnot
  refine ⟨min r0 1, Metric.ball w ε, (Metric.closedBall w ε)ᶜ, lt_min hr0 one_pos, Metric.isOpen_ball,
    Metric.isClosed_closedBall.isOpen_compl, Metric.mem_ball_self hε,
    (Metric.ball_subset_ball hεlt.le).trans hballU,
    Set.disjoint_left.2 fun x hx hx' => hx' (Metric.ball_subset_closedBall hx), ?_, ?_⟩
  · rintro x ⟨hx, hxr⟩
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hxr
    by_cases h : dist x w < ε
    · exact Or.inl h
    · refine Or.inr fun hcb => ?_
      have heq : dist x w = ε := le_antisymm hcb (not_lt.1 h)
      have hxK : x ∈ K := ⟨⟨hx, hxr'.le.trans (min_le_right _ _)⟩, heq⟩
      exact hr0T (Metric.mem_ball.2 (hxr'.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩
  · refine (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx => ?_
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hx.2
    exact mem_closedBall_zero_iff.2 (hC x hx.1 (hxr'.le.trans (min_le_right _ _)))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices

open scoped Real

noncomputable section

namespace OsgoodSeparate

theorem cons_mem_ball {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} (hx : x ∈ ball (c 0) R)
    {y : Fin n → ℂ} (hy : y ∈ ball (Fin.tail c) R) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball c R := by
  have hR : 0 < R := pos_of_mem_ball hx
  refine (mem_ball_pi_iff hR).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa [Fin.tail] using (mem_ball_pi_iff hR).mp hy j

theorem cauchy_torus : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : ℝ),
    ContinuousOn G (ball c R) →
    (∀ z ∈ ball c R, ∀ i, DifferentiableAt ℂ (fun t => G (Function.update z i t)) (z i)) →
    ∀ r : ℝ, 0 < r → r < R → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  | 0, G, c, _, _, _, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, G, c, R, hc, hs, r, hr0, hrR, z, hz => by
    have htor : ∀ θ, torusMap c (fun _ => r) θ ∈ ball c R := fun θ =>
      closedBall_subset_ball hrR (torusMap_mem_closedBall c hr0.le θ)
    have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * G ζ) c (fun _ => r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      refine Continuous.mul ?_ (hc.comp_continuous (continuous_torusMap c r) htor)
      refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr0 hz θ i
      exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    refine (torusIntegral_succ hint).trans ?_
    have hz' : Fin.tail z ∈ ball (Fin.tail c) r :=
      (mem_ball_pi_iff hr0).mpr fun i => by simpa [Fin.tail] using (mem_ball_pi_iff hr0).mp hz i.succ
    have hz'R : Fin.tail z ∈ ball (Fin.tail c) R := ball_subset_ball hrR.le hz'
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr0).mp hz 0
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * G (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))))
        (sphere (c 0) r) := by
      intro x hx
      have hxR : x ∈ ball (c 0) R := mem_ball.mpr (by rw [mem_sphere.mp hx]; exact hrR)
      have hc' : ContinuousOn (fun y => G (Fin.cons x y)) (ball (Fin.tail c) R) :=
        hc.comp (differentiable_cons_right x).continuous.continuousOn fun y hy => cons_mem_ball hxR hy
      have hs' : ∀ w ∈ ball (Fin.tail c) R, ∀ i : Fin n,
          DifferentiableAt ℂ (fun t => (fun y => G (Fin.cons x y)) (Function.update w i t)) (w i) := by
        intro w hw i
        have h := hs _ (cons_mem_ball hxR hw) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      have ih := cauchy_torus n (fun y => G (Fin.cons x y)) (Fin.tail c) R hc' hs' r hr0 hrR
        (Fin.tail z) hz'
      have e0 : c ∘ Fin.succ = Fin.tail c := rfl
      have e1 : ((fun _ : Fin (n + 1) => r) ∘ Fin.succ) = fun _ => r := rfl
      simp only [e0, e1]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr0.le key, circleIntegral.integral_const_mul]
    have hcont : ContinuousOn (fun x => G (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      hc.comp (differentiable_cons_left (Fin.tail z)).continuous.continuousOn fun x hx =>
        cons_mem_ball (closedBall_subset_ball hrR hx) hz'R
    have hdiff : ∀ x ∈ ball (c 0) r \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun x => G (Fin.cons x (Fin.tail z))) x := by
      intro x hx
      have h := hs _ (cons_mem_ball (ball_subset_ball hrR.le hx.1) hz'R) 0
      simp only [Fin.cons_zero, Fin.update_cons_zero] at h
      exact h
    have h1 := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      hz0 hcont hdiff
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

end OsgoodSeparate


open OsgoodSeparate in
theorem analyticOnNhd_of_continuousOn_of_separately {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    AnalyticOnNhd ℂ g U := by
  intro c hcU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hcU
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  have hcb : ContinuousOn g (ball c ε) := hc.mono hball
  have hsb : ∀ z ∈ ball c ε, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i) :=
    fun z hz => hs z (hball hz)
  have htor : Continuous fun θ => g (torusMap c (fun _ => ε / 2) θ) :=
    hcb.comp_continuous (continuous_torusMap c _) fun θ =>
      closedBall_subset_ball hrε (torusMap_mem_closedBall c hr.le θ)
  set L := torusFunctional c (ε / 2) g htor
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * L (kern c (ε / 2) z)) c :=
    analyticAt_const.mul ((L.analyticAt _).comp (kern_analyticAt_of_mem c hr (mem_ball_self hr)))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  show ((2 * π * I : ℂ) ^ n)⁻¹ * fctl c (ε / 2) g (kern c (ε / 2) z) = g z
  rw [fctl_kern hr g hz, OsgoodSeparate.cauchy_torus n g c ε hcb hsb (ε / 2) hr hrε z hz, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
