module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem BranchLift.proof (hR : RiemannExtensionAnalytic.Statement)
    (hB : BranchOffHypersurface.Statement) (hO : NormalModelOpenMapping.Statement)
    (hP : NormalModelProper.Statement) : BranchLift.Statement := by
  intro n k J p M γ hJ hdim
  set Δ := Metric.ball (0 : Fin k → ℂ) γ.radius with hΔ
  have hγd : DifferentiableOn ℂ γ.toFun Δ := γ.differentiableOn
  have hγZ : ∀ τ ∈ Δ, γ.toFun τ ∈ zeroSetIn J := fun τ hτ => γ.mapsTo hτ
  choose a b hbJ hab using M.birational
  have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, Differentiable ℂ (fun z : Fin n → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq =>
      simp only [eval_add]
      exact hp.add hq
    | mul_X p i hp =>
      simp only [eval_mul, eval_X]
      exact hp.mul (differentiable_apply i)
  have hcomp : ∀ q, DifferentiableOn ℂ (fun τ => eval (γ.toFun τ) q) Δ := fun q =>
    (hpoly q).comp_differentiableOn hγd
  set g : (Fin k → ℂ) → ℂ := fun τ => eval (γ.toFun τ) (∏ i, b i) with hg
  have hBJ : (∏ i, b i) ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  have hgne : ∀ V, IsOpen V → V ⊆ Δ → V.Nonempty → ∃ t ∈ V, g t ≠ 0 := fun V hV hVΔ hne =>
    hB n k J _ V γ.toFun hJ hdim hBJ hV hne (hγd.mono hVΔ) (γ.injOn.mono hVΔ)
      fun τ hτ => hγZ τ (hVΔ hτ)
  have hbne : ∀ τ, g τ ≠ 0 → ∀ i, eval (γ.toFun τ) (b i) ≠ 0 := fun τ hτ i h =>
    hτ (by simp only [hg, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)
  set f : Fin M.m → (Fin k → ℂ) → ℂ := fun i τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)
  have hgraph : ∀ τ ∈ Δ, g τ ≠ 0 → (Sum.elim (γ.toFun τ) fun i => f i τ) ∈ zeroSetIn M.ideal :=
    fun τ hτ hgτ => M.graph_mem_zeroSetIn a b hab _ (hγZ τ hτ) (hbne τ hgτ)
  have hfd : ∀ i, DifferentiableOn ℂ (f i) (Δ ∩ {t | g t ≠ 0}) := fun i τ hτ => by
    have h1 := (hcomp (a i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    have h2 := (hcomp (b i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    show DifferentiableWithinAt ℂ (fun τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)) _ τ
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv (hbne τ hτ.2 i))
  have hbdd : ∀ i, ∀ τ ∈ Δ, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f i '' (N ∩ Δ ∩ {t | g t ≠ 0})) := by
    intro i τ hτ
    obtain ⟨ε, hε, hεΔ⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball τ hτ
    have hsub : Metric.closedBall τ (ε / 2) ⊆ Δ :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεΔ
    have hK : Bornology.IsBounded (γ.toFun '' Metric.closedBall τ (ε / 2)) :=
      ((isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hγd.continuousOn.mono hsub)).isBounded
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hP n J M _ hK)
    refine ⟨Metric.closedBall τ (ε / 2), Metric.closedBall_mem_nhds τ (by linarith),
      isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩⟩
    rintro _ ⟨t, ⟨⟨ht, htΔ⟩, hgt⟩, rfl⟩
    have hw := hC _ ⟨hgraph t htΔ hgt, ⟨t, ht, rfl⟩⟩
    exact (norm_le_pi_norm (Sum.elim (γ.toFun t) fun i => f i t) (Sum.inr i)).trans hw
  choose F hFd hFeq using fun i => hR k Δ g (f i) Metric.isOpen_ball
    ((hpoly _).comp_differentiableOn hγd) hgne (hfd i) (hbdd i)
  set Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ := fun τ => Sum.elim (γ.toFun τ) fun i => F i τ with hΓ
  have hΓd : DifferentiableOn ℂ Γ Δ := by
    refine differentiableOn_pi.2 fun s => ?_
    rcases s with j | i
    · simpa [hΓ] using differentiableOn_pi.1 hγd j
    · simpa [hΓ] using hFd i
  have hdense : Δ ⊆ closure (Δ ∩ {t | g t ≠ 0}) := by
    intro τ hτ
    rw [mem_closure_iff]
    intro o ho hτo
    obtain ⟨t, ⟨hto, htΔ⟩, hgt⟩ := hgne (o ∩ Δ) (ho.inter Metric.isOpen_ball)
      Set.inter_subset_right ⟨τ, hτo, hτ⟩
    exact ⟨t, hto, htΔ, hgt⟩
  have hΓZ : ∀ τ ∈ Δ, Γ τ ∈ zeroSetIn M.ideal := by
    intro τ hτ q hq
    have heq : Set.EqOn (fun t => eval (Γ t) q) (fun _ => (0 : ℂ)) (Δ ∩ {t | g t ≠ 0}) := by
      intro t ht
      have hΓt : Γ t = Sum.elim (γ.toFun t) fun i => f i t := by
        simp only [hΓ]
        congr 1
        funext i
        exact hFeq i ht
      simp only [hΓt]
      exact hgraph t ht.1 ht.2 q hq
    exact heq.of_subset_closure ((MvPolynomial.continuous_eval q).comp_continuousOn hΓd.continuousOn)
      continuousOn_const Set.inter_subset_left hdense hτ
  have hΓinj : Set.InjOn Γ Δ := fun s hs t ht hst =>
    γ.injOn hs ht (by
      have := congrArg firstCoords hst
      exact this)
  refine ⟨Γ, hΓd, fun τ hτ => ⟨hΓZ τ hτ, rfl⟩, fun V hV hVo => ?_⟩
  exact hO n k J M V Γ hJ hdim hVo (hΓd.mono hV) (hΓinj.mono hV) fun τ hτ => hΓZ τ (hV hτ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

namespace VarietySlabMeasure

theorem isFiniteLinProj_of {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (h : ComplexSets.IsFiniteProjection J A) :
    IsFiniteLinProj J A :=
  ⟨h.injective, h.finite⟩

theorem fibreCount_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {U : Matrix (Fin n) (Fin n) ℂ}
    {s : Fin d → Fin n} (hA : ComplexSets.IsFiniteProjection J (U.submatrix s id))
    (B : Set (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin d)) :
    {z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard ≤
      ComplexSets.projDegree J (U.submatrix s id) := by
  obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.proof n d J _ hJ hd hA (WithLp.ofLp x)
  calc _ ≤ (ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).encard := by
        refine Set.encard_le_encard_of_injOn (f := fun z : EuclideanSpace ℂ (Fin n) => WithLp.ofLp z)
          ?_ (fun a _ b _ h => WithLp.ofLp_injective 2 h)
        rintro z ⟨⟨hz, -⟩, hx⟩
        exact ⟨hz, congrArg WithLp.ofLp hx⟩
    _ = ((ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).ncard : ℕ∞) :=
        hfin.cast_ncard_eq.symm
    _ ≤ _ := by exact_mod_cast hle

end VarietySlabMeasure

theorem VarietySlabMeasure.proof (hG : ComplexSets.FiniteProjectionsGeneric.Statement)
    (hW : VarietyProjectionMass.Statement) (hP : IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.Statement) :
    VarietySlabMeasure.Statement := by
  classical
  intro n d J u hJ hdim hu R
  rcases hdim.lt_or_eq with hlt | heq
  · refine ⟨1, 1, one_pos, one_pos, fun ε _ _ => ?_⟩
    calc _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J) := measure_mono (by exact fun z hz => hz.1)
      _ = 0 := NullSmaller.proof n d J hlt
      _ ≤ _ := by simp
  obtain ⟨U, hU, hfin⟩ := (hG n d J hJ heq).2.2 1 (fun _ => 1)
  have hA : ∀ s : Fin d → Fin n, StrictMono s →
      ComplexSets.IsFiniteProjection J (U.submatrix s id) := fun s hs => by
    simpa using hfin 0 ⟨s, hs.injective⟩

  have hQ : ∀ s : Fin d → Fin n, ∃ Q : MvPolynomial (Fin d) ℂ, StrictMono s → Q ≠ 0 ∧
      ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R →
        ‖eval ((U.submatrix s id).mulVec fun j => z j) Q‖ ≤ ‖∑ j, u j * z j‖ := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨Q, hQ0, hb⟩ := IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine n d J (U.submatrix s id) u hJ
        (VarietySlabMeasure.isFiniteLinProj_of (hA s hs)) hu
      obtain ⟨C, hC⟩ := hb R
      have hK : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
      refine ⟨MvPolynomial.C ((max C 1 : ℝ) : ℂ)⁻¹ * Q, fun _ => ⟨?_, fun z hz hzR => ?_⟩⟩
      · exact mul_ne_zero (by simpa using hK.ne') hQ0
      · rw [eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_of_nonneg hK.le, inv_mul_le_iff₀ hK]
        exact (hC z hz hzR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact ⟨0, fun h => absurd h hs⟩
  choose Q hQ using hQ

  have hR' : ∀ s : Fin d → Fin n, ∃ R' : ℝ, 0 < R' ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ R → ‖rowsProj U s z‖ < R' := by
    intro s
    have hc : Continuous (rowsProj U s) := by
      unfold rowsProj
      fun_prop
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨max K 0 + 1, by positivity, fun z hz => ?_⟩
    have := hK z (mem_closedBall_zero_iff.mpr hz)
    linarith [le_max_left K 0]
  choose R' hR'0 hR' using hR'

  have hS : ∀ s : Fin d → Fin n, ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ (StrictMono s → ∀ η : ℝ, 0 < η → η ≤ 1 →
      μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
        ‖eval (fun i => x i) (Q s)‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α)) := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨C, α, hC, hα, hb⟩ := hP d (Q s) (hQ s hs).1 (R' s) (hR'0 s)
      exact ⟨C, α, hC, hα, fun _ => hb⟩
    · exact ⟨1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose C α hC hα hS using hS
  set T := Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s) with hT

  obtain ⟨α₀, hα₀, hα₀le⟩ : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ s ∈ T, α₀ ≤ α s := by
    by_cases hne : T.Nonempty
    · exact ⟨T.inf' hne α, (Finset.lt_inf'_iff hne).2 fun s _ => hα s,
        fun s hs => Finset.inf'_le _ hs⟩
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, hs⟩ hne⟩
  set N : (Fin d → Fin n) → ℕ := fun s => ComplexSets.projDegree J (U.submatrix s id)
  have hNC : 0 ≤ ∑ s ∈ T, (N s : ℝ) * C s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hC s).le
  refine ⟨∑ s ∈ T, (N s : ℝ) * C s + 1, α₀, by linarith, hα₀, fun ε hε hε1 => ?_⟩
  set B : Set (EuclideanSpace ℂ (Fin n)) := {z | ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
  have hB : MeasurableSet B := by
    have hc : Continuous fun z : EuclideanSpace ℂ (Fin n) => ‖∑ j, u j * z j‖ := by fun_prop
    exact (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le hc.measurable measurable_const)
  have hεα : 0 < ε ^ α₀ := Real.rpow_pos_of_pos hε _
  have hterm : ∀ s ∈ T,
      (⨆ x : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
          μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B)) ≤
        ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := by
    intro s hs
    have hs' : StrictMono s := (Finset.mem_filter.mp hs).2
    rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
    · refine iSup_le fun x => ?_
      have := VarietySlabMeasure.fibreCount_le hJ heq (hA s hs') B x
      exact_mod_cast ENat.toENNReal_le.mpr this
    · calc _ ≤ μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
            ‖eval (fun i => x i) (Q s)‖ ≤ ε} := by
            refine measure_mono ?_
            rintro _ ⟨z, ⟨hz, hzR, hzε⟩, rfl⟩
            exact ⟨mem_ball_zero_iff.mpr (hR' s z hzR), ((hQ s hs').2 z hz hzR).trans hzε⟩
        _ ≤ ENNReal.ofReal (C s * ε ^ α s) := hS s hs' ε hε hε1
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hε hε1 (hα₀le s hs)) (hC s).le)
  calc μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
        = μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) := rfl
    _ ≤ _ := hW n d J hJ heq U hU B hB
    _ ≤ ∑ s ∈ T, ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ s ∈ T, (N s : ℝ) * C s * ε ^ α₀) :=
        (ENNReal.ofReal_sum_of_nonneg fun s _ => by have := hC s; positivity).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_mul, add_mul, one_mul]
        linarith

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

def TangentGraphLowerDensity.inPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i))

def TangentGraphLowerDensity.outPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I} :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : {j : Fin n // j ∉ I} => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : {j : Fin n // j ∉ I} => innerSL ℂ (b j))

theorem TangentGraphLowerDensity.inPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (i : I) :
    TangentGraphLowerDensity.inPart b I z i = inner ℂ (b i) z := by
  simp [TangentGraphLowerDensity.inPart]

theorem TangentGraphLowerDensity.outPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : {j : Fin n // j ∉ I}) :
    TangentGraphLowerDensity.outPart b I z j = inner ℂ (b j) z := by
  simp [TangentGraphLowerDensity.outPart]

theorem TangentGraphLowerDensity.inPart_eq_toLp {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    TangentGraphLowerDensity.inPart b I z = WithLp.toLp 2 (frameProj b I z) := by
  refine PiLp.ext fun i => ?_
  simp [TangentGraphLowerDensity.inPart_apply, frameProj]

theorem TangentGraphLowerDensity.norm_sq_split {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖TangentGraphLowerDensity.inPart b I z‖ ^ 2 + ‖TangentGraphLowerDensity.outPart b I z‖ ^ 2 := by
  classical
  rw [← b.repr.norm_map z, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [TangentGraphLowerDensity.inPart_apply, TangentGraphLowerDensity.outPart_apply,
    OrthonormalBasis.repr_apply_apply]
  convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I) (fun i => ‖inner ℂ (b i) z‖ ^ 2)).symm using 3
  congr 1; exact Subsingleton.elim _ _

theorem TangentGraphLowerDensity.proof : TangentGraphLowerDensity.Statement := by
  intro n d b I₀ S Ω V g w₀ hcard hΩ _hV hw₀ hg hproj hSV htan θ hθ
  classical
  set P := TangentGraphLowerDensity.inPart b I₀ with hPdef
  set Q := TangentGraphLowerDensity.outPart b I₀ with hQdef
  have hgd : DifferentiableAt ℂ g w₀ := hg.differentiableAt (hΩ.mem_nhds hw₀)

  have hQ0 : Q.comp (fderiv ℂ g w₀) = 0 := by
    refine ContinuousLinearMap.ext fun v => PiLp.ext fun j => ?_
    have h1 : HasFDerivAt (fun w => inner ℂ (b j) (g w))
        ((innerSL ℂ (b (j : Fin n))).comp (fderiv ℂ g w₀)) w₀ :=
      (innerSL ℂ (b (j : Fin n))).hasFDerivAt.comp w₀ hgd.hasFDerivAt
    have h2 := h1.fderiv
    rw [htan j j.2] at h2
    have h3 := congrArg (fun L => L v) h2
    simpa [hQdef, TangentGraphLowerDensity.outPart_apply] using h3.symm
  have hQd : HasFDerivAt (fun w => Q (g w)) (0 : (I₀ → ℂ) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I₀}) w₀ := by
    have h := Q.hasFDerivAt.comp w₀ hgd.hasFDerivAt
    rw [hQ0] at h
    exact h

  obtain ⟨η, hη, hθη⟩ : ∃ η : ℝ, 0 < η ∧ θ * (1 + η) ^ (2 * d) < 1 := by
    have hc : Continuous fun η : ℝ => θ * (1 + η) ^ (2 * d) := by fun_prop
    have h0 : ∀ᶠ η in 𝓝 (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using hθ.2)
    have h0' : ∀ᶠ η in 𝓝[>] (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 := nhdsWithin_le_nhds h0
    obtain ⟨η, h1, h2⟩ := (h0'.and (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
    exact ⟨η, h2, h1⟩
  have hlo := hasFDerivAt_iff_isLittleO.1 hQd
  have hev : ∀ᶠ w in 𝓝 w₀, ‖Q (g w) - Q (g w₀)‖ ≤ η * ‖w - w₀‖ ∧ w ∈ Ω := by
    refine ((hlo.def hη).mono fun w hw => ?_).and (hΩ.mem_nhds hw₀)
    simpa using hw
  obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨(1 + η) * δ, by positivity, fun ρ hρ => ?_⟩
  have h1η : 0 < 1 + η := by linarith
  set s := ρ / (1 + η) with hs
  have hs0 : 0 < s := div_pos hρ.1 h1η
  have hsδ : s < δ := by
    rw [hs, div_lt_iff₀ h1η]
    linarith [hρ.2]
  set x₀ : EuclideanSpace ℂ I₀ := WithLp.toLp 2 w₀ with hx₀
  have hPx : ∀ w ∈ Ω, P (g w) = WithLp.toLp 2 w := fun w hw => by
    rw [hPdef, TangentGraphLowerDensity.inPart_eq_toLp, hproj w hw]

  have hsub : Metric.ball x₀ s ⊆ P '' (S ∩ Metric.ball (g w₀) ρ) := by
    intro v hv
    have hv' : ‖v - x₀‖ < s := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    have hww : ‖WithLp.ofLp v - w₀‖ ≤ ‖v - x₀‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simpa [hx₀] using PiLp.norm_apply_le (v - x₀) i
    have hwδ : dist (WithLp.ofLp v) w₀ < δ := by
      rw [dist_eq_norm]
      linarith
    obtain ⟨hQw, hwΩ⟩ := hδw hwδ
    refine ⟨g (WithLp.ofLp v), ⟨?_, ?_⟩, by rw [hPx _ hwΩ, WithLp.toLp_ofLp]⟩
    · have hm : g (WithLp.ofLp v) ∈ S ∩ V := hSV ▸ Set.mem_image_of_mem g hwΩ
      exact hm.1
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsplit := TangentGraphLowerDensity.norm_sq_split b I₀ (g (WithLp.ofLp v) - g w₀)
      have hPd : P (g (WithLp.ofLp v) - g w₀) = v - x₀ := by
        rw [map_sub, hPx _ hwΩ, hPx _ hw₀, WithLp.toLp_ofLp]
      have hQd' : Q (g (WithLp.ofLp v) - g w₀) = Q (g (WithLp.ofLp v)) - Q (g w₀) := map_sub _ _ _
      rw [← hPdef, ← hQdef, hPd, hQd'] at hsplit
      have hle : ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + ‖Q (g (WithLp.ofLp v)) - Q (g w₀)‖ := by
        nlinarith [norm_nonneg (g (WithLp.ofLp v) - g w₀), norm_nonneg (v - x₀),
          norm_nonneg (Q (g (WithLp.ofLp v)) - Q (g w₀))]
      calc ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + η * ‖v - x₀‖ := by nlinarith
        _ = (1 + η) * ‖v - x₀‖ := by ring
        _ < (1 + η) * s := by gcongr
        _ = ρ := by rw [hs]; field_simp

  have hd0 : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcardI : Fintype.card I₀ = d := by rw [Fintype.card_coe, hcard]
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFinOfCardEq hcardI)
  have hball : μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) =
      ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
    rw [← VarietyLelongMono.euclBall_measure d (L x₀) hs0, ← L.image_ball,
      L.isometry.hausdorffMeasure_image (Or.inl hd0)]
  have hLip : LipschitzWith 1 P := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    have h := TangentGraphLowerDensity.norm_sq_split b I₀ (x - y)
    rw [← hPdef, ← hQdef] at h
    nlinarith [norm_nonneg (P (x - y)), norm_nonneg (x - y), norm_nonneg (Q (x - y))]
  have hreal : θ * ρ ^ (2 * d) ≤ s ^ (2 * d) := by
    have hpos : 0 < (1 + η) ^ (2 * d) := by positivity
    have hρp : 0 ≤ ρ ^ (2 * d) := by have := hρ.1; positivity
    rw [hs, div_pow, le_div_iff₀ hpos]
    calc θ * ρ ^ (2 * d) * (1 + η) ^ (2 * d) = ρ ^ (2 * d) * (θ * (1 + η) ^ (2 * d)) := by ring
      _ ≤ ρ ^ (2 * d) * 1 := by gcongr
      _ = ρ ^ (2 * d) := mul_one _
  calc ENNReal.ofReal (θ * ρ ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1)
      ≤ ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
        gcongr
    _ = μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) := hball.symm
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (P '' (S ∩ Metric.ball (g w₀) ρ)) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ) := by
        have h := hLip.hausdorffMeasure_image_le hd0 (S ∩ Metric.ball (g w₀) ρ)
        simpa using h

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section


open Classical in
def LocalGraphProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))), I₀.card = d →
    (∀ z ∈ S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω) →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (S ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))

end

end GroundTheory.Heights₂.Heights
end
