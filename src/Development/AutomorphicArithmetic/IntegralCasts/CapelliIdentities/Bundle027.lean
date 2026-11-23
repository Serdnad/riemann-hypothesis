module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecificLimits.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Qf31.isCompact_box :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
    [ProperSpace L] (c : Matrix (Fin m) (Fin m) L) (r : ℝ),
    IsCompact
      {g : GL (Fin m) L |
        (∀ (i j : Fin m), ‖(↑g : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r) ∧
          ∀ (i j : Fin m), ‖(↑g⁻¹ : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r} := by
  intro L _ _ m _ c r
  have hK : IsCompact {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} := by
    have h : IsCompact (Set.univ.pi fun i : Fin m =>
        Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (c i j) r
    have e : {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} =
        (Set.univ.pi fun i : Fin m =>
          Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) := by
      ext A
      constructor
      · intro hA i _ j _
        exact mem_closedBall_iff_norm.2 (hA i j)
      · intro hA i j
        exact mem_closedBall_iff_norm.1 (hA i (Set.mem_univ i) j (Set.mem_univ j))
    rw [e]
    exact h
  have hK' : IsCompact (MulOpposite.unop ⁻¹'
      {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r}) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin m) (Fin m) L)).symm.isCompact_preimage.2 hK
  exact (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) L)).isCompact_preimage (hK.prod hK')
end

section

noncomputable def UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing :
    (K : Type) → [inst : NormedField K] → [IsUltrametricDist K] → Subring K :=
  fun K _ _ =>
    { carrier := {x : K | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : K)‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : K)‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha' }
end

section

theorem UpperTheory.Reformulated.B.Qe17.norm_sum_lt :
    ∀ {F ι : Type} [inst : NormedField F] [IsUltrametricDist F]
    (s : Finset ι) (f : ι → F) {C : ℝ}, (0 : ℝ) < C → (∀ i ∈ s, ‖f i‖ < C) → ‖∑ i ∈ s, f i‖ < C := by
  intro F ι _ _ s f C hC h
  refine Finset.sum_induction f (fun x => ‖x‖ < C) ?_ ?_ h
  · intro a b ha hb
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
  · simpa using hC
end

section

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv (F * G) := by
  intro p _ σ F G hF hG n
  classical
  change ‖MvPowerSeries.coeff n (F * G)‖ ≤ 1
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro q _
  rw [norm_mul]
  exact mul_le_one₀ (hF q.1) (norm_nonneg _) (hG q.2)
end

section

noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

private def UpperTheory.Reformulated.B.UnitBallLemmas.unitBall (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv F →
        (MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F = (1 : ℂ_[p]) →
          ∃ (G : MvPowerSeries σ ℂ_[p]), UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv G ∧ F * G = (1 : MvPowerSeries σ ℂ_[p]) := by
  intro p _ σ F hF h1
  let F' : MvPowerSeries σ (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) :=
    fun n => ⟨MvPowerSeries.coeff n F, hF n⟩
  have hmap : MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype F' = F := by
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  have hc : MvPowerSeries.constantCoeff F' = ((1 : (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p)ˣ) : UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) := by
    apply Subtype.ext
    exact h1
  refine ⟨MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype (MvPowerSeries.invOfUnit F' 1), ?_, ?_⟩
  · intro n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n (MvPowerSeries.invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, MvPowerSeries.mul_invOfUnit F' 1 hc, map_one]
end

section

noncomputable def UpperTheory.Reformulated.B.Gwb7.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwb7.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.Gwb7.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.Gwb7.intMv_pderiv.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]} (i : σ),
      UpperTheory.Reformulated.B.Gwb7.IntegralMv F →
        UpperTheory.Reformulated.B.Gwb7.IntegralMv ((MvPowerSeries.pderiv (R := ℂ_[p]) i : MvPowerSeries σ ℂ_[p] → MvPowerSeries σ ℂ_[p]) F) := by
  intro p _ σ F i hF n
  have h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1 := hF _
  have h2 : ‖((n i : ℕ) : ℂ_[p]) + 1‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n i + 1)
    rwa [Nat.cast_add, Nat.cast_one] at h
  change ‖MvPowerSeries.coeff n (MvPowerSeries.pderiv (R := ℂ_[p]) i F)‖ ≤ 1
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.kb :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ AlgebraicClosure (ZMod p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.WW :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ WittVector p (UpperTheory.Reformulated.B.Qi32.kb p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.K0 :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ FractionRing (UpperTheory.Reformulated.B.Qi32.WW p)

theorem UpperTheory.Reformulated.B.Qi32.mem_W_of_norm :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (i0 : UpperTheory.Reformulated.B.Qi32.K0 p →+* ℂ_[p]),
      (∀ (x : UpperTheory.Reformulated.B.Qi32.WW p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p])
                ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  x)‖ ≤
            (1 : ℝ)) →
        ∀ (x : UpperTheory.Reformulated.B.Qi32.K0 p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p]) x‖ ≤ (1 : ℝ) →
            ∃ (w : UpperTheory.Reformulated.B.Qi32.WW p),
              (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  w =
                x := by
  intro p inst i0 hW x hx
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
    rw [h, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rcases ValuationRing.isInteger_or_isInteger (UpperTheory.Reformulated.B.Qi32.WW p) x with h | ⟨w, hw⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, map_zero _⟩
  by_cases hu : IsUnit w
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : (UpperTheory.Reformulated.B.Qi32.WW p)ˣ) : UpperTheory.Reformulated.B.Qi32.WW p), ?_⟩
    rw [map_units_inv, hw, inv_inv]
  · exfalso
    have hirr : Irreducible (p : UpperTheory.Reformulated.B.Qi32.WW p) := WittVector.irreducible p
    have hmem : w ∈ IsLocalRing.maximalIdeal (UpperTheory.Reformulated.B.Qi32.WW p) := hu
    rw [hirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨v, rfl⟩ := hmem
    have h1 : ‖i0 x‖ * ‖i0 x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h2 : ‖i0 x⁻¹‖ < 1 := by
      rw [← hw, map_mul, map_mul, map_natCast, map_natCast, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hW v)) hp
    have h3 : ‖i0 x‖ * ‖i0 x⁻¹‖ ≤ ‖i0 x⁻¹‖ := mul_le_of_le_one_left (norm_nonneg _) hx
    linarith
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj8.E :
    ℕ → Type :=
    fun (d : ℕ) ↦ EuclideanSpace ℝ (Fin d)

theorem UpperTheory.Reformulated.B.Qj8.conv_sq_le :
    ∀ {d : ℕ} (k g : UpperTheory.Reformulated.B.Qj8.E d → ENNReal),
      Measurable k →
        Measurable g →
          ∀ (ξ : UpperTheory.Reformulated.B.Qj8.E d),
            (∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η) ^ (2 : ℕ) ≤
              (∫⁻ (ζ : UpperTheory.Reformulated.B.Qj8.E d), k ζ) * ∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η ^ (2 : ℕ) := by
  intro d k g hk hg ξ
  have hk' : Measurable (fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η)) :=
    hk.comp (measurable_const.sub measurable_id)
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsq : ∀ a : ENNReal, (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq' : ∀ a : ENNReal, (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have H := ENNReal.lintegral_mul_norm_pow_le (μ := MeasureTheory.volume)
    (f := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η))
    (g := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η) * g η ^ (2 : ℕ))
    hk'.aemeasurable (hk'.mul (hg.pow_const 2)).aemeasurable hh hh (by norm_num)
  have hpt : ∀ η : UpperTheory.Reformulated.B.Qj8.E d,
      k (ξ - η) ^ (1 / 2 : ℝ) * (k (ξ - η) * g η ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = k (ξ - η) * g η := by
    intro η
    rw [ENNReal.mul_rpow_of_nonneg _ _ hh, hsq', ← mul_assoc, ← pow_two, hsq]
  simp only [hpt] at H
  rw [MeasureTheory.lintegral_sub_left_eq_self k ξ] at H
  calc _ ≤ _ := pow_le_pow_left₀ bot_le H 2
    _ = _ := by rw [mul_pow, hsq, hsq]
end

section

private theorem UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.step {A : Type} [NormedRing A] [NormedAlgebra ℝ A] (a : A)
    (h : ‖a - 1‖ ≤ (1 / 2 : ℝ)) : ‖a - 1‖ ≤ (2 / 3 : ℝ) * ‖a * a - 1‖ := by
  have e : (2 : ℝ) • (a - 1) = (a * a - 1) - (a - 1) * (a - 1) := by
    rw [two_smul]; noncomm_ring
  have h1 : ‖(2 : ℝ) • (a - 1)‖ = 2 * ‖a - 1‖ := by
    rw [norm_smul]; simp
  have h2 : ‖(a * a - 1) - (a - 1) * (a - 1)‖ ≤ ‖a * a - 1‖ + ‖a - 1‖ * ‖a - 1‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)
  rw [← e, h1] at h2
  have h3 : ‖a - 1‖ * ‖a - 1‖ ≤ ‖a - 1‖ * (1 / 2) :=
    mul_le_mul_of_nonneg_left h (norm_nonneg _)
  linarith

theorem UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.nss :
    ∀ {G A : Type} [inst : Group G]
    [inst_1 : NormedRing A] [NormedAlgebra ℝ A] (ρ : G →* A) (H : Subgroup G),
    (∀ g ∈ H, ‖(ρ : G → A) g - (1 : A)‖ ≤ (1 / 2 : ℝ)) → ∀ g ∈ H, (ρ : G → A) g = (1 : A) := by
  intro G A _ _ _ ρ H h
  have key : ∀ n : ℕ, ∀ g ∈ H, ‖ρ g - 1‖ ≤ (2 / 3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro g hg; have := h g hg; rw [pow_zero]; linarith
    | succ n ih =>
      intro g hg
      have h1 := UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.step (ρ g) (h g hg)
      have h2 := ih (g * g) (H.mul_mem hg hg)
      rw [map_mul] at h2
      rw [pow_succ]
      linarith
  intro g hg
  have lim : Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h0 : ‖ρ g - 1‖ ≤ 0 := ge_of_tendsto' lim (fun n => key n g hg)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
end

section

noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper.{u_1, u_2} :
    {𝕜 : Type u_1} → [RCLike 𝕜] → {n : Type u_2} → [LinearOrder n] → Matrix n n 𝕜 → Prop :=
  fun {𝕜} [RCLike 𝕜] {n} [LinearOrder n] X ↦
    ∀ (i j : n), j ≤ i → X i j = 0

noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow.{u_2} :
    {n : Type u_2} → [Fintype n] → [LinearOrder n] → n → ℕ :=
  fun {n} [Fintype n] [LinearOrder n] i ↦
    ({x : n | x < i} : Finset n).card

theorem UpperTheory.Reformulated.B.StrictlyUpperRank.rank_add_le_of_pow_ne_zero.{u_1, u_2} :
    ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : Fintype n] [inst_2 : LinearOrder n] {X : Matrix n n 𝕜},
      @UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper 𝕜 inst n inst_2 X →
        ∀ (k : Nat) (i j : n),
          @Ne 𝕜
              (@HPow.hPow (Matrix n n 𝕜) Nat (Matrix n n 𝕜)
                (@instHPow (Matrix n n 𝕜) Nat
                  (@NPow.toPow (Matrix n n 𝕜)
                    (@Monoid.toNPow (Matrix n n 𝕜)
                      (@Semiring.toMonoid (Matrix n n 𝕜)
                        (@Matrix.semiring n 𝕜
                          (@DivisionSemiring.toSemiring 𝕜
                            (@Semifield.toDivisionSemiring 𝕜
                              (@Field.toSemifield 𝕜
                                (@NormedField.toField 𝕜
                                  (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst))))))
                          inst_1 fun (a b : n) ↦ @LinearOrder.toDecidableEq n inst_2 a b)))))
                X k i j)
              (@OfNat.ofNat 𝕜 (nat_lit 0)
                (@Zero.toOfNat0 𝕜
                  (@MulZeroClass.toZero 𝕜
                    (@instMulZeroClassOfSemiring 𝕜
                      (@DivisionSemiring.toSemiring 𝕜
                        (@Semifield.toDivisionSemiring 𝕜
                          (@Field.toSemifield 𝕜
                            (@NormedField.toField 𝕜
                              (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst)))))))))) →
            @LE.le Nat instLENat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 i) k)
              (@UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow n inst_1 inst_2 j) := by
  intro 𝕜 _ n _ _ X hX k
  induction k with
  | zero =>
    intro i j h
    have hij : i = j := by
      by_contra hne
      exact h (by rw [pow_zero]; exact Matrix.one_apply_ne hne)
    subst hij
    exact le_rfl
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih i l (left_ne_zero_of_mul hl)
    have hlj : l < j := by
      by_contra hle
      exact right_ne_zero_of_mul hl (hX l j (not_lt.mp hle))
    have h2 : UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow l < UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow j := by
      unfold UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans hlj
      · have hm := @hsub l (by simpa using hlj)
        simp at hm
    omega
end

section

theorem UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff :
    ∀ (t : ℝ),
    Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ)) = (1 : ℂ) ↔ ∃ (n : ℤ), t = (↑n : ℝ) := by
  intro t
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm ((n : ℤ) : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl
end

section

theorem UpperTheory.Reformulated.B.Qh67.imag_of_sq :
    ∀ {c : ℂ} {d : ℕ},
    (0 : ℕ) < d → c ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) c = -c ∧ c ≠ (0 : ℂ) := by
  intro c d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : c.re * c.re - c.im * c.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : c.re * c.im + c.im * c.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : c.re * c.im = 0 := by linarith [mul_comm c.re c.im]
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg c.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext
    · simp [hre]
    · simp
  · rintro rfl
    simp at h1
    omega
end
