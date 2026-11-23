module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle005
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.ClassGroup.Basic

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem sum_nonneg_of_swap_conj_fintype (Q : Type) [AddCommGroup Q] [Fintype Q] (ψ : Q → ℂ)
    (P S L : Q →+ Q) (hL : Function.Injective L)
    (hP : ∀ x, P (P x) = P x) (hS : ∀ x, S (S x) = x)
    (hSP : ∀ x, S (P x) = S x - P (S x)) (hLP : ∀ x, L (P x) = P (L x))
    (hψ : ∀ x, ψ x = ψ (P x) * ψ (x - P x)) (hψS : ∀ x, ψ (S x) = ψ x)
    (hψL : ∀ x, ψ (L x) = (starRingEnd ℂ) (ψ x)) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ q : Q, ψ q = (r : ℂ) := by
  set A : Finset Q := Finset.univ.filter (fun x => P x = x) with hA
  set A' : Finset Q := Finset.univ.filter (fun x => P x = 0) with hA'
  have mA : ∀ x, x ∈ A ↔ P x = x := by intro x; simp [hA]
  have mA' : ∀ x, x ∈ A' ↔ P x = 0 := by intro x; simp [hA']
  have h1 : ∑ q : Q, ψ q = ∑ p ∈ A ×ˢ A', ψ p.1 * ψ p.2 := by
    refine Finset.sum_nbij' (fun q => (P q, q - P q)) (fun p => p.1 + p.2) ?_ ?_ ?_ ?_ ?_
    · intro q _
      simp [Finset.mem_product, mA, mA', hP]
    · intro p _
      exact Finset.mem_univ _
    · intro q _
      simp
    · intro p hp
      rw [Finset.mem_product, mA, mA'] at hp
      ext <;> simp [hp.1, hp.2]
    · intro q _
      exact hψ q
  have h2 : ∑ x ∈ A', ψ x = ∑ x ∈ A, ψ x := by
    refine Finset.sum_nbij' S S ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA'] at hx
      rw [mA]
      have := hSP x
      rw [hx, map_zero] at this
      exact (sub_eq_zero.mp this.symm).symm
    · intro x hx
      rw [mA] at hx
      rw [mA']
      have := hSP x
      rw [hx] at this
      exact sub_eq_self.mp this.symm
    · intro x _
      exact hS x
    · intro x _
      exact hS x
    · intro x _
      exact (hψS x).symm
  have h3 : (starRingEnd ℂ) (∑ x ∈ A, ψ x) = ∑ x ∈ A, ψ x := by

    rw [map_sum]
    refine Finset.sum_bij (fun x _ => L x) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA] at hx
      rw [mA, ← hLP, hx]
    · intro x _ y _ h
      exact hL h
    · intro y hy
      obtain ⟨x, rfl⟩ := (Finite.injective_iff_surjective.mp hL) y
      refine ⟨x, ?_, rfl⟩
      rw [mA] at hy ⊢
      apply hL
      rw [hLP, hy]
    · intro x _
      exact (hψL x).symm
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp h3
  refine ⟨t * t, mul_self_nonneg t, ?_⟩
  rw [h1, Finset.sum_product, ← Finset.sum_mul_sum, h2, ht]
  push_cast
  rfl

theorem finsum_quotient_nonneg_of_swap_conj :
    ∀ (G : Type) [AddCommGroup G] (B : AddSubgroup G) [Finite (G ⧸ B)] (φ : G → ℂ) (P S L : G →+ G), (∀ x, ∀ w ∈ B, φ (x + w) = φ x) → (∀ w ∈ B, P w ∈ B ∧ S w ∈ B) → (∀ x, L x ∈ B ↔ x ∈ B) → (∀ x, P (P x) = P x) → (∀ x, S (S x) = x) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, L (P x) = P (L x)) → (∀ x, φ x = φ (P x) * φ (x - P x)) → (∀ x, φ (S x) = φ x) → (∀ x, φ (L x) = (starRingEnd ℂ) (φ x)) → ∃ r : ℝ, 0 ≤ r ∧ ∑ᶠ q : G ⧸ B, φ q.out = (r : ℂ) := by
  intro G _ B _ φ P S L hper hB hLB hP hS hSP hLP hφ hφS hφL
  haveI : Fintype (G ⧸ B) := Fintype.ofFinite _
  have hout : ∀ x : G, φ (QuotientAddGroup.mk x : G ⧸ B).out = φ x := by
    intro x
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_out_eq_mul B x
    rw [hw]
    exact hper x w w.2
  let P' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B P (fun w hw => (hB w hw).1)
  let S' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B S (fun w hw => (hB w hw).2)
  let L' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B L (fun w hw => (hLB w).2 hw)
  have eP : ∀ x : G, P' (x : G ⧸ B) = (P x : G) := fun x => rfl
  have eS : ∀ x : G, S' (x : G ⧸ B) = (S x : G) := fun x => rfl
  have eL : ∀ x : G, L' (x : G ⧸ B) = (L x : G) := fun x => rfl
  rw [finsum_eq_sum_of_fintype]
  refine sum_nonneg_of_swap_conj_fintype (G ⧸ B) (fun q => φ q.out) P' S' L' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [eL, QuotientAddGroup.eq_zero_iff] at hq
      exact (QuotientAddGroup.eq_zero_iff x).2 ((hLB x).1 hq)
  all_goals
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      simp only [eP, eS, eL, ← QuotientAddGroup.mk_sub, hout]
      first
        | rw [hP]
        | rw [hS]
        | rw [hSP]
        | rw [hLP]
        | exact hφ x
        | exact hφS x
        | exact hφL x

end GlobalTheory
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSupBall

open MeasureTheory Filter Set
open scoped Pointwise

theorem integral_le_of_disjoint_translates {ι : Type} [Fintype ι]
    (A : AddSubgroup (EuclideanSpace ℂ ι)) [Countable A]
    (D t : Set (EuclideanSpace ℂ ι)) (hD : IsAddFundamentalDomain A D volume)
    (ht : MeasurableSet t)
    (hd : ∀ y₁ y₂ : A, y₁ ≠ y₂ → Disjoint (y₁ +ᵥ t) (y₂ +ᵥ t))
    (f : EuclideanSpace ℂ ι → ℝ) (hf0 : ∀ u, 0 ≤ f u) (hfc : Continuous f)
    (hf : ∀ (y : A) u, f (y +ᵥ u) = f u) (hi : IntegrableOn f D) :
    ∫ u in t, f u ≤ ∫ u in D, f u := by
  haveI : VAddInvariantMeasure A (EuclideanSpace ℂ ι) volume :=
    ⟨fun g s _ => measure_preimage_add volume (g : EuclideanSpace ℂ ι) s⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable]
  refine ENNReal.toReal_mono (Integrable.lintegral_lt_top hi).ne ?_
  calc ∫⁻ u in t, ENNReal.ofReal (f u)
      = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f (-y +ᵥ u)) :=
        hD.setLIntegral_eq_tsum' (fun u => ENNReal.ofReal (f u)) t
    _ = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by simp_rw [hf]
    _ = ∫⁻ u in ⋃ y : A, (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by
        refine (lintegral_iUnion₀ (fun y => ?_) ?_ _).symm
        · exact (ht.const_vadd y).nullMeasurableSet.inter hD.nullMeasurableSet
        · intro y₁ y₂ h
          exact (((hd y₁ y₂ h).inf_left _).inf_right _).aedisjoint
    _ ≤ ∫⁻ u in D, ENNReal.ofReal (f u) :=
        lintegral_mono_set (iUnion_subset fun _ => inter_subset_right)

theorem factorial_div_le (g : ℕ) {v r : ℝ} (hv : 1 ≤ v) (hr : r ^ 2 = 1 / (4 * v)) :
    (g.factorial : ℝ) / (Real.pi ^ g * r ^ (2 * g)) ≤ (2 * (g : ℝ) * v + 1) ^ g := by
  have hv0 : 0 < v := by linarith
  have hpi := Real.pi_gt_three
  rw [pow_mul, hr, ← mul_pow]
  have h1 : (g.factorial : ℝ) ≤ (g : ℝ) ^ g := by exact_mod_cast Nat.factorial_le_pow g
  calc (g.factorial : ℝ) / (Real.pi * (1 / (4 * v))) ^ g
      ≤ (g : ℝ) ^ g / (Real.pi * (1 / (4 * v))) ^ g := by gcongr
    _ = ((g : ℝ) / (Real.pi * (1 / (4 * v)))) ^ g := by rw [div_pow]
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ g
        rw [div_le_iff₀ (by positivity)]
        have h2 : (2 * (g : ℝ) * v + 1) * (Real.pi * (1 / (4 * v)))
            = Real.pi / 2 * g + Real.pi / (4 * v) := by field_simp; ring
        rw [h2]
        have h3 : 0 ≤ Real.pi / (4 * v) := by positivity
        have h4 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
        nlinarith

theorem sup_le_mean_square : ∀ (ι : Type) [Fintype ι] (A : AddSubgroup (EuclideanSpace ℂ ι)) (v : ℝ) (Fd : Set (EuclideanSpace ℂ ι)) (G : EuclideanSpace ℂ ι → ℂ), 1 ≤ v → (∀ x ∈ A, x ≠ 0 → 1 / v ≤ ‖x‖ ^ 2) → MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume → MeasureTheory.volume Fd = 1 → Differentiable ℂ G → (∀ x ∈ A, ∀ z, ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2) = ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) → MeasureTheory.IntegrableOn (fun z => ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) Fd → ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * ∫ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro ι _ A v Fd G hv hA hD _ hG hinv hint z
  have hv0 : 0 < v := by linarith
  set r : ℝ := Real.sqrt (1 / (4 * v)) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 1 / (4 * v) := Real.sq_sqrt (by positivity)
  set N : EuclideanSpace ℂ ι → ℝ := fun u => ‖G u‖ ^ 2 * Real.exp (-Real.pi * ‖u‖ ^ 2) with hN
  have hN0 : ∀ u, 0 ≤ N u := fun u => by positivity
  have hGc := hG.continuous
  have hNc : Continuous N := by simp only [hN]; fun_prop
  have hdisj : ∀ y₁ y₂ : A, y₁ ≠ y₂ →
      Disjoint (y₁ +ᵥ Metric.ball z r) (y₂ +ᵥ Metric.ball z r) := by
    intro y₁ y₂ hne
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hpq' : (y₂ : EuclideanSpace ℂ ι) + q = (y₁ : EuclideanSpace ℂ ι) + p := hpq
    have hy : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) = q - p := by
      rw [AddSubgroup.coe_sub, sub_eq_sub_iff_add_eq_add, ← hpq', add_comm]
    have hne' : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) ≠ 0 := fun h0 =>
      hne (sub_eq_zero.mp (Subtype.ext h0))
    have h1 := hA _ (y₁ - y₂ : A).2 hne'
    rw [hy] at h1
    have h2 : ‖q - p‖ < 2 * r := by
      have hp' : dist p z < r := hp
      have hq' : dist q z < r := hq
      rw [← dist_eq_norm]
      calc dist q p ≤ dist q z + dist z p := dist_triangle _ _ _
        _ < 2 * r := by rw [dist_comm z p]; linarith
    have h3 : ‖q - p‖ ^ 2 < (2 * r) ^ 2 := by gcongr
    have h4 : (2 * r) ^ 2 = 1 / v := by rw [mul_pow, hr2]; field_simp; norm_num
    linarith
  haveI : Countable A := by
    rw [← Set.countable_univ_iff]
    refine Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun y : A => y +ᵥ Metric.ball z r) (fun a _ b _ h => hdisj a b h) ?_ ?_
    · intro y _
      exact Metric.isOpen_ball.vadd (y : EuclideanSpace ℂ ι)
    · intro y _
      exact ⟨y +ᵥ z, z, Metric.mem_ball_self hr0, rfl⟩
  have hpk : ∫ u in Metric.ball z r, N u ≤ ∫ u in Fd, N u := by
    refine integral_le_of_disjoint_translates A Fd _ hD measurableSet_ball hdisj N hN0 hNc ?_ hint
    intro y u
    have e : y +ᵥ u = u + (y : EuclideanSpace ℂ ι) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    rw [e]
    exact hinv y y.2 u
  set φ : EuclideanSpace ℂ ι → ℂ :=
    fun u => G u * Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z (u - z)) with hφ
  have hφd : Differentiable ℂ φ := by
    refine hG.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    exact (innerSL ℂ z).differentiable.comp (differentiable_id.sub_const z)
  have hφi : IntegrableOn (fun u => ‖φ u‖ ^ 2) (Metric.ball z r) :=
    GlobalTheory.integrableOn_norm_pow_ball volume hφd.continuous.continuousOn 2
  have hsub := GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball hr0 hφd.differentiableOn 2 hφi
  rw [finrank_euclideanSpace] at hsub
  have hφz : φ z = G z := by simp [hφ]
  rw [hφz] at hsub
  have hpt : ∀ u ∈ Metric.ball z r,
      ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * N u := by
    intro u hu
    have hu' : ‖u - z‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : ‖u - z‖ ^ 2 ≤ 1 / 4 := by
      have : ‖u - z‖ ^ 2 ≤ r ^ 2 := by gcongr
      refine this.trans ?_
      rw [hr2]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : ‖u‖ ^ 2 = ‖z‖ ^ 2 + 2 * (inner ℂ z (u - z)).re + ‖u - z‖ ^ 2 := by
      have := norm_add_sq (𝕜 := ℂ) z (u - z)
      rwa [add_sub_cancel] at this
    have h3 : Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ 3 := by
      have hpi := Real.pi_le_four
      have hpi0 := Real.pi_pos
      calc Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖u - z‖])
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h4 : ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
        = Real.exp (Real.pi * ‖u - z‖ ^ 2) * N u := by
      simp only [hφ, hN]
      rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
        mul_left_comm, ← Real.exp_add, h2]
      congr 2
      simp only [innerSL_apply_apply, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
      push_cast
      ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right h3 (hN0 u)
  have hNi : IntegrableOn N (Metric.ball z r) :=
    (hNc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  have hb : (∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ 3 * ∫ u in Metric.ball z r, N u := by
    rw [← integral_mul_const, ← integral_const_mul]
    exact setIntegral_mono_on (hφi.mul_const _) (hNi.const_mul _) measurableSet_ball hpt
  have hnum := factorial_div_le (Fintype.card ι) hv hr2
  have hI0 : 0 ≤ ∫ u in Fd, N u := integral_nonneg hN0
  set c : ℝ := ((Fintype.card ι).factorial : ℝ) /
    (Real.pi ^ Fintype.card ι * r ^ (2 * Fintype.card ι)) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ (c * ∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hsub (Real.exp_pos _).le
    _ ≤ c * (3 * ∫ u in Metric.ball z r, N u) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hc0
    _ ≤ c * (3 * ∫ u in Fd, N u) := by gcongr
    _ ≤ (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * (3 * ∫ u in Fd, N u) := by gcongr
    _ = _ := by ring

end GlobalTheory.ThetaSupBall
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.setAverage_prod_fundamentalDomain_planeLattice_pow : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ (f : ℂ → ℝ), (∀ ω ∈ Λ, ∀ z, f (ω + z) = f z) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (r : ℕ) (e : V ≃ₗ[ℝ] (Fin r → ℂ)) (A : AddSubgroup V), (∀ x, x ∈ A ↔ ∀ k, e x k ∈ Λ) → ⨍ z in Classical.epsilon (fun Fd : Set V => MeasureTheory.IsAddFundamentalDomain A Fd μ), ∏ k, f (e z k) ∂μ = (⨍ z in Classical.epsilon (fun Fd : Set ℂ => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume), f z) ^ r := by
  first | exact @GlobalTheory.LatticeMean.mean_prod_eq_pow | exact GlobalTheory.LatticeMean.mean_prod_eq_pow | (intros; apply GlobalTheory.LatticeMean.mean_prod_eq_pow <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem nonarch_le_pow_of_mem_ideal_pow {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K))
    (v : K →*₀ ℝ) (h0 : ∀ x, 0 ≤ v x) (hadd : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hint : ∀ c : 𝓞 K, v (c : K) ≤ 1) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ J, v (y : K) ≤ M) (k : ℕ) : ∀ y ∈ J ^ k, v (y : K) ≤ M ^ k := by
  induction k with
  | zero => intro y _; simpa using hint y
  | succ k ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := by simp
      rw [this, map_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hM b hb) (h0 _) (pow_nonneg hM0 _)
    · intro a b ha hb
      have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
      rw [this]
      exact (hadd _ _).trans (max_le ha hb)

theorem exists_generator_pow_fractional_size : ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K), I ≠ ⊥ → (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap (𝓞 K) K).range) → ∃ (h : ℕ) (α : K), 0 < h ∧ α ≠ 0 ∧ ∀ v : K →*₀ ℝ, (∀ x, 0 ≤ v x) → (∀ x y, v (x + y) ≤ max (v x) (v y)) → (∀ c : 𝓞 K, v (c : K) ≤ 1) → ∀ x₀ ∈ I, (∀ x ∈ I, v x ≤ v x₀) → v α = v x₀ ^ h := by
  intro K _ _ I hI ⟨n, hn, hnI⟩
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let J : Ideal (𝓞 K) :=
    { carrier := {c | ∃ x ∈ I, (c : K) = (n : K) * x}
      zero_mem' := ⟨0, I.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        refine ⟨x + y, I.add_mem hx hy, ?_⟩
        have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
        rw [this, ha, hb]; ring
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        refine ⟨c • x, I.smul_mem c hx, ?_⟩
        have : ((c • a : 𝓞 K) : K) = (c : K) * (a : K) := by simp
        have h2 : c • x = (c : K) * x := Algebra.smul_def c x
        rw [this, ha, h2]; ring }
  have hmem : ∀ x ∈ I, ∃ c ∈ J, (c : K) = (n : K) * x := by
    intro x hx
    obtain ⟨c, hc⟩ := hnI x hx
    exact ⟨c, ⟨x, hx, hc⟩, hc⟩
  have hJ : J ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, hcx⟩ := hmem x hx
    intro h
    rw [h] at hc
    have : c = 0 := by simpa using hc
    rw [this] at hcx
    exact mul_ne_zero hnK hx0 (by simpa using hcx.symm)
  have hJ' : J ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hJ
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hprin : (J ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨J, hJ'⟩ ^ h : nonZeroDivisors (Ideal (𝓞 K))) = 1 := by
      rw [map_pow]; exact pow_card_eq_one
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hJ' h)).mp h1
  obtain ⟨a, ha⟩ := hprin
  have ha0 : a ≠ 0 := by
    intro h0
    apply pow_ne_zero h hJ
    rw [ha, h0]; simp
  have haK : (a : K) ≠ 0 := by simpa using ha0
  refine ⟨h, (a : K) / (n : K) ^ h, hpos, div_ne_zero haK (pow_ne_zero _ hnK), ?_⟩
  intro v h0 hadd hint x₀ hx₀ hmax
  have hvn : v (n : K) ≠ 0 := (map_ne_zero v).mpr hnK
  have hM : ∀ y ∈ J, v (y : K) ≤ v (n : K) * v x₀ := by
    rintro y ⟨x, hx, hy⟩
    rw [hy, map_mul]
    exact mul_le_mul_of_nonneg_left (hmax x hx) (h0 _)
  have h1 : v (a : K) ≤ (v (n : K) * v x₀) ^ h :=
    nonarch_le_pow_of_mem_ideal_pow J v h0 hadd hint _ (mul_nonneg (h0 _) (h0 _)) hM h a
      (by rw [ha]; exact Submodule.mem_span_singleton_self a)
  have h2 : (v (n : K) * v x₀) ^ h ≤ v (a : K) := by
    obtain ⟨c, hc, hcx⟩ := hmem x₀ hx₀
    have hch : c ^ h ∈ J ^ h := Ideal.pow_mem_pow hc h
    rw [ha] at hch
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hch
    have hd' : (d : K) * (a : K) = (c : K) ^ h := by
      have := congrArg (algebraMap (𝓞 K) K) hd
      simpa using this
    rw [← map_mul, ← hcx, ← map_pow, ← hd', map_mul]
    exact mul_le_of_le_one_left (h0 _) (hint d)
  rw [map_div₀, map_pow, le_antisymm h1 h2, mul_pow]
  field_simp

end GlobalTheory
end
