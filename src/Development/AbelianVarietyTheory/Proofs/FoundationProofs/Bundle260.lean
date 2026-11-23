module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle246
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle017
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
namespace GlobalTheory.FrobStick

theorem det_column_alg {R : Type*} [CommRing R] (x e w q : Fin 3 → R) (ε r a₁ a₃ S D1 D2 D3 : R)
    (hq : ∀ i, q i * w i = 1) (hu : IsUnit (2 * ε ^ 4))
    (h : Matrix.det (Matrix.of fun i j => (![ε ^ 3 * x i ^ 3 * e i ^ 3,
      ε * e i ^ 3 * (x i * q i + ε ^ 2 * r * x i ^ 3),
      e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)] : Fin 3 → R) j) =
      2 * (ε * S) * (ε * D1) * (ε * D2) * (ε * D3)) :
    (x 0 ^ 3 * w 0 * (x 2 - x 1) + x 1 ^ 3 * w 1 * (x 0 - x 2) + x 2 ^ 3 * w 2 * (x 1 - x 0))
      * e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 = w 0 * w 1 * w 2 * S * D1 * D2 * D3 := by
  have hrow : ∀ i, e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)
      = e i ^ 3 * (a₁ * x i * q i + a₃ * x i ^ 3 - 2 * q i) := fun i => by
    linear_combination e i ^ 3 * a₃ * x i ^ 3 * hq i
  simp only [hrow] at h
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  have h2 : 2 * ε ^ 4 * (e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 *
      (x 0 ^ 3 * (q 1 * q 2) * (x 2 - x 1) + x 1 ^ 3 * (q 0 * q 2) * (x 0 - x 2)
        + x 2 ^ 3 * (q 0 * q 1) * (x 1 - x 0))) = 2 * ε ^ 4 * (S * D1 * D2 * D3) := by
    linear_combination h
  have h3 := hu.mul_left_cancel h2
  have h12 : q 1 * q 2 * (w 1 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h02 : q 0 * q 2 * (w 0 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h01 : q 0 * q 1 * (w 0 * w 1) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  linear_combination w 0 * w 1 * w 2 * h3
    - e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 * (x 0 ^ 3 * w 0 * (x 2 - x 1) * h12
      + x 1 ^ 3 * w 1 * (x 0 - x 2) * h02 + x 2 ^ 3 * w 2 * (x 1 - x 0) * h01)

theorem det_column_ops : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  intro p _ E wq ε r a₁ a₃ s d₁ d₂ d₃ hε hw hs h1 h2 h3 h
  have hC : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), HasSubst a → ∀ c : ℂ_[p],
      PowerSeries.subst a (PowerSeries.C c : PowerSeries ℂ_[p]) = MvPowerSeries.C c := by
    intro a ha c
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes c
  have hlin : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (PowerSeries.C ε * PowerSeries.X * E) =
        MvPowerSeries.C ε * (a * PowerSeries.subst a E) := by
    intro a ha
    have ha' : HasSubst a := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul ha', subst_mul ha', hC a ha', subst_X ha', mul_assoc]
  have hX : ∀ i : Fin 3, HasSubst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) := fun i =>
    HasSubst.of_constantCoeff_zero (by simp [GL3Theta.Xv])
  rw [hlin s hs, hlin d₁ h1, hlin d₂ h2, hlin d₃ h3] at h
  refine det_column_alg (fun i => (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]))
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) E)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq⁻¹)
    (MvPowerSeries.C ε) (MvPowerSeries.C r) (MvPowerSeries.C a₁) (MvPowerSeries.C a₃) _ _ _ _
    ?_ ?_ ?_
  · intro i
    rw [← subst_mul (hX i), PowerSeries.inv_mul_cancel _ (by rw [hw]; exact one_ne_zero),
      ← coe_substAlgHom (hX i), map_one]
  · have : (2 * MvPowerSeries.C ε ^ 4 : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.C (2 * ε ^ 4) := by
      rw [map_mul, map_pow, map_ofNat]
    rw [this]
    exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (pow_ne_zero _ hε))).map _
  · rw [← h]
    congr 1
    ext1 i j
    have hCi := hC _ (hX i)
    have hXi := subst_X (R := ℂ_[p]) (hX i)
    rw [← coe_substAlgHom (hX i)] at hCi hXi
    simp only [Matrix.of_apply]
    rw [← coe_substAlgHom (hX i)]
    fin_cases j
    all_goals
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, map_mul, map_pow, map_add, map_sub, map_ofNat, hCi, hXi]

end GlobalTheory.FrobStick
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_eq_one_or_of_add_eq_one {L : Type*} [NormedField L] [IsUltrametricDist L] {b c : L}
    (h : b + c = 1) (hn : ‖b * c‖ < 1) : ‖b‖ = 1 ∨ ‖c‖ = 1 := by
  by_contra hne
  push_neg at hne
  obtain ⟨hb, hc⟩ := hne
  rw [norm_mul] at hn
  have h1 : ‖c‖ = max 1 ‖b‖ := by
    have : c = 1 + -b := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hb.symm)]
    simp
  have h2 : ‖b‖ = max 1 ‖c‖ := by
    have : b = 1 + -c := by linear_combination h
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hc.symm)]
    simp
  have h3 : 1 ≤ ‖c‖ := h1 ▸ le_max_left _ _
  have h4 : 1 ≤ ‖b‖ := h2 ▸ le_max_left _ _
  nlinarith

theorem norm_two_mul_natCast_lt_one (k : ℕ) : ‖((2 * k : ℕ) : ℂ_[2])‖ < 1 := by
  have h2 : ‖(2 : ℂ_[2])‖ < 1 := by
    have : (2 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] ((2 : ℕ) : ℚ_[2]) := by simp [map_ofNat]
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hk : ‖(k : ℂ_[2])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
  push_cast
  rw [norm_mul]
  nlinarith [norm_nonneg (k : ℂ_[2]), norm_nonneg (2 : ℂ_[2])]

theorem exists_int_trace_one_unit_at_two :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  intro D lam
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by omega⟩
  have hk' : (D.host.d : ℂ) + 1 = 8 * (k : ℂ) := by exact_mod_cast hk
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hw : StandardLatticesGL3.w0 D = (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := rfl
  have hw' : 1 - StandardLatticesGL3.w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by
    rw [hw]; ring
  have hc : starRingEnd ℂ (StandardLatticesGL3.w0 D) = 1 - StandardLatticesGL3.w0 D := by
    rw [hw', hw, map_div₀, map_add (f := _), map_mul, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hp : StandardLatticesGL3.w0 D * (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ) := by
    rw [hw', hw]
    push_cast
    linear_combination (1 / 4 : ℂ) * hk' + (1 / 4 : ℂ) * hs
      - (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
  have hQ : StandardLatticesGL3.w0 D ∈ Qbar := ha ▸ hm _
  have hQ' : 1 - StandardLatticesGL3.w0 D ∈ Qbar := Qbar.sub_mem Qbar.one_mem hQ
  have hadd : lamC lam (StandardLatticesGL3.w0 D) + lamC lam (1 - StandardLatticesGL3.w0 D) = 1 := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_add (f := _), ← map_one lam]
    congr 1
    apply Subtype.ext
    simp
  have hmul : lamC lam (StandardLatticesGL3.w0 D) * lamC lam (1 - StandardLatticesGL3.w0 D) = ((2 * k : ℕ) : ℂ_[2]) := by
    simp only [lamC, dif_pos hQ, dif_pos hQ']
    rw [← map_mul, ← map_natCast lam]
    congr 1
    apply Subtype.ext
    exact hp.trans (by simp; exact Or.inl rfl)
  rcases norm_eq_one_or_of_add_eq_one hadd (hmul ▸ norm_two_mul_natCast_lt_one k) with h | h
  · refine ⟨a, StandardLatticesGL3.w0 D, k, ha, hQ, h, by rw [hc]; ring, by rw [hc, hp], ?_⟩
    intro Λ t ht
    exact ⟨ht.2.1, hw' ▸ ht.2.2⟩
  · refine ⟨1 - a, 1 - StandardLatticesGL3.w0 D, k, ?_, hQ', h, ?_, ?_, ?_⟩
    · rw [← ha]
      simp
    · rw [map_sub, map_one, hc]; ring
    · rw [map_sub, map_one, hc, ← hp]; ring
    · intro Λ t ht
      rw [sub_sub_cancel]
      exact ⟨hw' ▸ ht.2.2, ht.2.1⟩

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogMv

open PowerSeries

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [coeff_subst (HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem expMv_eq_subst {G : MvPowerSeries σ ℂ_[p]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (exp ℂ_[p]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem logMv_eq_subst {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 1) :
    GL3Theta.logMv F = (log ℂ_[p]).subst (F - 1) := by
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  ext α
  rw [coeff_subst_range h1]
  show GL3Theta.logMv F α = _
  rw [GL3Theta.logMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_log]
  split_ifs
  · simp
  · simp
    ring

theorem exp_neg_log_one_var (K : Type*) [Field K] [CharZero K] :
    (exp K).subst (-log K) * (1 + X : PowerSeries K) = 1 := by
  have h0 : constantCoeff (-log K) = 0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' h0
  have e : (1 + X) * PowerSeries.derivative (log K) = 1 := by
    rw [derivative_log]
    ext n
    cases n with
    | zero => simp [add_mul]
    | succ n => simp [add_mul, coeff_succ_X_mul, coeff_one, pow_succ]
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, derivative_subst hs, derivative_exp, map_neg, derivative_one, map_add (f := _),
      derivative_one, derivative_X]
    simp only [smul_eq_mul]
    linear_combination (-(exp K).subst (-log K)) * e
  · have : constantCoeff ((exp K).subst (-log K) : PowerSeries K) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
      · simp
      · intro k hk
        simp [hk]
    simp [this]

theorem expMv_neg_logMv_mul : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (F : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff F = 1 → MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 ∧ expMv (-GL3Theta.logMv F) * F = 1 := by
  intro p _ σ F hF
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  have hs := HasSubst.of_constantCoeff_zero h1
  have h0 : MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 := by
    rw [logMv_eq_subst hF]
    exact constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  refine ⟨h0, ?_⟩
  have hl : HasSubst (-log ℂ_[p]) := HasSubst.of_constantCoeff_zero' (by simp)
  have e := congrArg (substAlgHom (R := ℂ_[p]) hs) (exp_neg_log_one_var ℂ_[p])
  have en : subst (F - 1) (-log ℂ_[p]) = -GL3Theta.logMv F := by
    rw [logMv_eq_subst hF, ← coe_substAlgHom hs, map_neg]
  rw [map_mul, map_add (f := _), map_one, substAlgHom_X, coe_substAlgHom, subst_comp_subst_apply hl hs,
    en, add_sub_cancel] at e
  rw [expMv_eq_subst (by rw [map_neg, h0, neg_zero])]
  exact e

end GlobalTheory.ExpLogMv
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.DupNorm

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem i_add {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem i_sub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 :=
  by rw [sub_eq_add_neg]; exact i_add ha (by rwa [norm_neg])

theorem i_mul {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem i_pow {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem i_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one K (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

theorem i_neg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by rwa [norm_neg]

theorem i_one : ‖(1 : K)‖ ≤ 1 := by simp

theorem b_le (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg

theorem delta_eq (W : WeierstrassCurve K) (x : K) :
    W.Δ = (-48 * x ^ 2 - 8 * W.b₂ * x + (W.b₂ ^ 2 - 32 * W.b₄)) *
        (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) +
      (12 * x ^ 3 - W.b₂ * x ^ 2 - 10 * W.b₄ * x + (W.b₂ * W.b₄ - 27 * W.b₆)) *
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem max_norm_eq (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) (x : K) :
    max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ =
      max 1 ‖x‖ ^ 4 := by
  obtain ⟨b2, b4, b6, b8⟩ := b_le W h1 h2 h3 h4 h6
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · have hp : ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    have hq : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    rw [max_eq_left hx, one_pow]
    refine le_antisymm (max_le hp hq) ?_
    rw [← hΔ, delta_eq W x]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_) <;> rw [norm_mul] <;>
      refine mul_le_of_le_one_left (norm_nonneg _) ?_ <;> repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
  · have hR1 : 1 ≤ ‖x‖ := hx.le
    have bd : ∀ {c : K}, ‖c‖ ≤ 1 → ∀ {k m : ℕ}, k ≤ m → ‖c * x ^ k‖ ≤ ‖x‖ ^ m := by
      intro c hc k m hkm
      rw [norm_mul, norm_pow]
      calc ‖c‖ * ‖x‖ ^ k ≤ 1 * ‖x‖ ^ m :=
            mul_le_mul hc (pow_le_pow_right₀ hR1 hkm) (by positivity) zero_le_one
        _ = ‖x‖ ^ m := one_mul _
    have hφ : x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ =
        x ^ 4 + -(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0) := by ring
    have hψ : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
        4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0 := by ring
    have hr : ‖W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0‖ ≤ ‖x‖ ^ 2 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (bd b4 le_rfl) (bd (i_mul (i_ofNat 2) b6) (by norm_num)))) (bd b8 (by norm_num)))
    have hs : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0‖ ≤ ‖x‖ ^ 3 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le (bd (i_ofNat 4) le_rfl) (bd b2 (by norm_num))))
          (bd (i_mul (i_ofNat 2) b4) (by norm_num)))) (bd b6 (by norm_num)))
    have h24 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have h34 : ‖x‖ ^ 3 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have hne : ‖x ^ 4‖ ≠ ‖-(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0)‖ := by
      rw [norm_neg, norm_pow]; exact (hr.trans_lt h24).ne'
    rw [hφ, hψ, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_pow,
      max_eq_left (hr.trans h24.le), max_eq_left (hs.trans h34.le), max_eq_right hR1]

theorem max_norm_eq_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]),
    ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 →
      ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖
        ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 :=
  fun _ _ W h1 h2 h3 h4 h6 hΔ x => max_norm_eq W h1 h2 h3 h4 h6 hΔ x

end GlobalTheory.DupNorm
end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k → FiniteDimensional ℂ (ModularForm Γ (k : ℤ)) ∧ FiniteDimensional ℂ (CuspForm Γ (k : ℤ)) ∧ (k - 1) * Γ.index ≤ 12 * (Module.finrank ℂ (ModularForm Γ (k : ℤ)) + Module.finrank ℂ (CuspForm Γ (k : ℤ))) := by
  first | exact @GlobalTheory.OddFrame.dim_lower_bound | exact GlobalTheory.OddFrame.dim_lower_bound | (intros; apply GlobalTheory.OddFrame.dim_lower_bound <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.mvPowerSeries_fin_three_eq_zero_of_subst_lines : ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines | exact GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines | (intros; apply GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines <;> assumption)
end
