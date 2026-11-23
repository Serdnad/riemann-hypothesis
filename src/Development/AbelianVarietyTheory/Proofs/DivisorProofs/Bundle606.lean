module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferential
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageStepIndependent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMul

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :
    nmul μ 0 = fun _ => 0 := rfl

theorem nmul_succ' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem nmul_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul_zero']
  | succ n ih =>
    rw [nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ n) (fun i => X i) (fun _ => 0) ih
      (fun i => constantCoeff_X i) (fun _ => map_zero _)).1

theorem nmul_add (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nmul_zero']
    exact ((GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun _ => 0) (fun _ => 0)
      (nmul_const μ hμ m) (fun _ => map_zero _) (fun _ => map_zero _)).2.2.2.1).symm
  | succ n ih =>
    rw [← Nat.add_assoc, nmul_succ', ih, nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (nmul μ n) (fun i => X i)
      (nmul_const μ hμ m) (nmul_const μ hμ n) (fun i => constantCoeff_X i)).2.1

theorem nmul_one (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) :
    nmul μ 1 = fun i => X i := by
  rw [nmul_succ', nmul_zero']
  have h := GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (fun i => X i) (fun _ => 0) (fun _ => 0)
    (fun i => constantCoeff_X i) (fun _ => map_zero _) (fun _ => map_zero _)
  rw [← h.2.2.1, h.2.2.2.1]

theorem nmul_mul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    ∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i) := by
  have ha : HasSubst (nmul μ n) := hasSubst_of_constantCoeff_zero (nmul_const μ hμ n)
  induction m with
  | zero =>
    intro i
    rw [Nat.zero_mul, nmul_zero']
    exact (map_zero (substAlgHom (R := R) ha)).symm.trans (by rw [coe_substAlgHom])
  | succ m ih =>
    intro i
    rw [Nat.succ_mul, nmul_add μ hμ, nmul_succ']
    rw [(GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun i => X i) (fun _ => 0)
      (nmul_const μ hμ m) (fun i => constantCoeff_X i) (fun _ => map_zero _)).2.2.2.2
      (Fin d) (nmul μ n) (nmul_const μ hμ n) i]
    have e1 : (fun j => subst (nmul μ n) (nmul μ m j)) = nmul μ (m * n) := funext fun j => (ih j).symm
    have e2 : (fun j => subst (nmul μ n) ((X j : MvPowerSeries (Fin d) R))) = nmul μ n :=
      funext fun j => subst_X ha j
    rw [e1, e2]

theorem nmul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧
      nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧
      (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i :=
  fun _ _ _ μ hμ m n => ⟨nmul_const μ hμ n, nmul_add μ hμ m n, nmul_mul μ hμ m n, nmul_one μ hμ⟩

end GlobalTheory.NMul
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobRel
theorem coeff_subst_sub_mem :
    ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
      (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
      (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
      ∀ (m : ℕ) (c : MvPowerSeries σ Q),
        (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
        ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N,
          coeff w (MvPowerSeries.subst (QLog.up (Q := Q) u) c) -
            coeff w (MvPowerSeries.subst (QLog.up (Q := Q) ℓ) c) = algebraMap B Q r := by
  apply GlobalTheory.SubstMod.subst_coeff_sub_mem <;> assumption

theorem coeff_op_of_degree_le_one : ∀ {B O : Type} [CommRing B] [CommRing O] (θ : B →+* O) {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}, IsLift θ μ → ∀ {τ : Type} (u v : Fin d → MvPowerSeries τ B), (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ (i : Fin d) (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (op μ u v i) = coeff β (u i + v i) := GlobalTheory.T.coeff_formalGroupLawEvalPoints_of_degree_le_one

theorem coeff_prod_addLeft : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) = if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_first_add_second_threeGroups

theorem coeff_prod_addRight : ∀ {R : Type} [CommRing R] {d : ℕ} (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (α.prod fun s k => (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) s) ^ k) = if α = Finsupp.sumElim a (b + e) then (∏ i, ((b + e) i).choose (b i) : R) else 0 := GlobalTheory.T.coeff_prod_pow_x1_x2_add_x3

theorem coeff_evalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero

theorem coeff_evalTwoGroups_first_second_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), e ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := GlobalTheory.T.coeff_evalTwoGroups_threeGroups_eq_zero_of_ne_zero

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem degree_sumElim3 {d : ℕ} (a b e : Fin d →₀ ℕ) :
    (Finsupp.sumElim a (Finsupp.sumElim b e)).degree = a.degree + b.degree + e.degree := by
  simp [Finsupp.degree_eq_sum, Fintype.sum_sum_type, add_assoc]

theorem x_hasSubst {R : Type} [CommRing R] {d : ℕ} (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)
    (hu : ∀ j, constantCoeff (u j) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

end GlobalTheory.CobRel

namespace GlobalTheory.CobRel

theorem cocycle_rel_mod : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (QLog.up (Q := Q) μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  intro B O Q _ _ _ _ θ d μ hμ N m c hc hcob n hn a b ha _ hab hab'
  set e := n - (a + b) with he_def
  have he : e ≠ 0 := fun h => hab' (le_antisymm hab (tsub_eq_zero_iff_le.1 h))
  have hbe : b + e = n - a := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  have hn' : a + b + e = n := by
    ext i
    have := hab i
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Pi.sub_apply, he_def] at this ⊢
    omega
  set w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ := Finsupp.sumElim a (Finsupp.sumElim b e) with hw_def
  have hw : w.degree = m := by
    rw [← hn, ← hn', hw_def, degree_sumElim3, map_add (f := _), map_add (f := _)]
  have hX : ∀ (R : Type) [CommRing R] (j : Fin d),
      constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 ∧
      constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := fun R _ j => by
    simp [x1, x2, x3]
  have hop : ∀ (R : Type) [CommRing R] (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (ν i) = 0) → ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      constantCoeff (op ν u v i) = 0 := fun R _ ν hν u v hu hv i =>
    constantCoeff_subst_eq_zero (x_hasSubst u v hu hv) (fun s => by cases s <;> simp [hu, hv]) (hν i)
  have hmapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B),
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) → ∀ i,
      map (algebraMap B Q) (op μ u v i) = op (QLog.up (Q := Q) μ) (fun j => map (algebraMap B Q) (u j))
        (fun j => map (algebraMap B Q) (v j)) i := fun u v hu hv i => by
    simp only [op, at2, QLog.up]
    rw [map_subst (x_hasSubst u v hu hv)]
    congr 1
    funext s
    cases s <;> rfl
  have hmX : ∀ j, (map (algebraMap B Q) (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x1 j) ∧
      (map (algebraMap B Q) (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x2 j) ∧
      (map (algebraMap B Q) (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B) = x3 j) := fun j => by
    simp [x1, x2, x3, map_X]

  have hc2 : ∀ s, constantCoeff (Sum.elim (op μ x1 x2) x3 s) = 0 := by
    intro s
    cases s with
    | inl i => exact hop B μ hμ.const _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i
    | inr i => exact (hX B i).2.2
  have hd2 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim (op μ x1 x2) x3 s) = coeff β (Sum.elim (fun i => x1 i + x2 i) x3 s) := by
    intro s β hβ
    cases s with
    | inl i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1) i β hβ
    | inr i => rfl
  obtain ⟨r2, hr2, h2⟩ := coeff_subst_sub_mem N _ _ hc2 hd2 m c hc w hw
  have hu2 : QLog.up (Q := Q) (Sum.elim (op μ x1 x2) x3) = Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3 := by
    funext s
    cases s with
    | inl i =>
      simp only [QLog.up, Sum.elim_inl]
      rw [hmapop _ _ (fun j => (hX B j).1) (fun j => (hX B j).2.1)]
      simp only [(hmX _).1, (hmX _).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  have hl2 : QLog.up (Q := Q) (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B)) x3) =
      Sum.elim (fun i => x1 i + x2 i) x3 := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl, map_add (f := _), (hmX i).1, (hmX i).2.1]
    | inr i => simp only [QLog.up, Sum.elim_inr]; exact (hmX i).2.2
  rw [hu2, hl2] at h2
  have hv2 : coeff w (MvPowerSeries.subst (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q)) x3) c) =
      (∏ i, ((a + b) i).choose (a i) : Q) * coeff (Finsupp.sumElim (a + b) e) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => by simp [(hX Q j).1, (hX Q j).2.1]) (fun j => (hX Q j).2.2)),
      finsum_eq_single _ (Finsupp.sumElim (a + b) e)]
    · rw [hw_def, coeff_prod_addLeft, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addLeft, ite_eq_right hα, smul_zero]

  have hc3 : ∀ s, constantCoeff (Sum.elim x1 (op μ x2 x3) s) = 0 := by
    intro s
    cases s with
    | inl i => exact (hX B i).1
    | inr i => exact hop B μ hμ.const _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i
  have hd3 : ∀ s (β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ), β.degree ≤ 1 →
      coeff β (Sum.elim x1 (op μ x2 x3) s) = coeff β (Sum.elim x1 (fun i => x2 i + x3 i) s) := by
    intro s β hβ
    cases s with
    | inl i => rfl
    | inr i => exact coeff_op_of_degree_le_one θ hμ _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2) i β hβ
  obtain ⟨r3, hr3, h3⟩ := coeff_subst_sub_mem N _ _ hc3 hd3 m c hc w hw
  have hu3 : QLog.up (Q := Q) (Sum.elim x1 (op μ x2 x3)) = Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i =>
      simp only [QLog.up, Sum.elim_inr]
      rw [hmapop _ _ (fun j => (hX B j).2.1) (fun j => (hX B j).2.2)]
      simp only [(hmX _).2.1, (hmX _).2.2]
  have hl3 : QLog.up (Q := Q) (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) B))) =
      Sum.elim x1 (fun i => x2 i + x3 i) := by
    funext s
    cases s with
    | inl i => simp only [QLog.up, Sum.elim_inl]; exact (hmX i).1
    | inr i => simp only [QLog.up, Sum.elim_inr, map_add (f := _), (hmX i).2.1, (hmX i).2.2]
  rw [hu3, hl3] at h3
  have hv3 : coeff w (MvPowerSeries.subst (Sum.elim x1 (fun i => (x2 i + x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) Q))) c) =
      (∏ i, ((b + e) i).choose (b i) : Q) * coeff (Finsupp.sumElim a (b + e)) c := by
    rw [coeff_subst (x_hasSubst _ _ (fun j => (hX Q j).1) (fun j => by simp [(hX Q j).2.1, (hX Q j).2.2])),
      finsum_eq_single _ (Finsupp.sumElim a (b + e))]
    · rw [hw_def, coeff_prod_addRight, ite_eq_left rfl, smul_eq_mul, mul_comm]
    · intro α hα
      rw [hw_def, coeff_prod_addRight, ite_eq_right hα, smul_zero]

  obtain ⟨k, hk, hk'⟩ := hcob w
  have hsplit : coeff w (cob2 (QLog.up (Q := Q) μ) c) = coeff w (at2 c x2 x3) -
      coeff w (MvPowerSeries.subst (Sum.elim (op (QLog.up (Q := Q) μ) x1 x2) x3) c) +
      coeff w (MvPowerSeries.subst (Sum.elim x1 (op (QLog.up (Q := Q) μ) x2 x3)) c) - coeff w (at2 c x1 x2) := by
    simp only [cob2, map_sub, map_add (f := _)]; rfl
  rw [hsplit, hw_def, coeff_evalTwoGroups_second_third_eq_zero c a b e ha, coeff_evalTwoGroups_first_second_eq_zero c a b e he, ← hw_def] at hk'
  rw [hbe] at hv3
  refine ⟨-k - r2 + r3, N.add_mem (N.sub_mem (N.neg_mem hk) hr2) hr3, ?_⟩
  rw [map_add (f := _), map_sub, map_neg, ← hk', ← h2, ← h3, hv2, hv3]
  ring

end GlobalTheory.CobRel
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries TensorProduct GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup WithConv

namespace GlobalTheory.EvMul

theorem coeff_subst_eq_zero_of_degree {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) {N : ℕ}
    {f : MvPowerSeries σ R} (hf : ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0)
    (β : τ →₀ ℕ) (hβ : β.degree < N) : coeff β (subst a f) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree < N
  · rw [hf α h, zero_smul]
  · rw [coeff_of_lt_order (f := α.prod fun s e => a s ^ e) (d := β) ?_, smul_zero]
    refine lt_of_lt_of_le (b := ((α.degree : ℕ) : ℕ∞)) (by exact_mod_cast (by omega : β.degree < α.degree)) ?_
    rw [Finsupp.prod]
    refine le_trans ?_ (le_order_prod _ _)
    show ((∑ i ∈ α.support, α i : ℕ) : ℕ∞) ≤ _
    push_cast
    exact Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun l => (X l : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    have e : nmul μ (k + 1) i = at2 (μ i) (nmul μ k) (fun l => X l) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    rw [e, at2]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ i)

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

theorem mulBy_succ_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (k : ℕ) (a : A) :
    PDiv.mulBy O A (k + 1) a = Algebra.TensorProduct.lmul' O
      (Algebra.TensorProduct.map (PDiv.mulBy O A k : A →ₐ[O] A) (AlgHom.id O A) (Coalgebra.comul a)) := by
  rw [PDiv.mulBy, pow_succ]
  rfl

theorem mulBy_zero_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (a : A) :
    PDiv.mulBy O A 0 a = algebraMap O A (Coalgebra.counit a) := by
  rw [PDiv.mulBy, pow_zero]
  rfl

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]

theorem pow_dvd_map {A B : Type} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (φ : A →ₐ[O] B) {m : ℕ} {a : A} (h : (p : A) ^ m ∣ a) : (p : B) ^ m ∣ φ a := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨φ y, by rw [map_mul, map_pow, map_natCast]⟩

theorem cont_subst {σ τ : Type} [Finite τ] {A : Type} [CommRing A] [Algebra O A]
    (E : MvPowerSeries σ O →ₐ[O] A)
    (hE : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ E f)
    {a : τ → MvPowerSeries σ O} (ha : ∀ i, constantCoeff (a i) = 0) :
    ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : A) ^ m ∣ E.comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha)) f := by
  intro m
  obtain ⟨N, hN⟩ := hE m
  exact ⟨N, fun f hf => by
    rw [AlgHom.comp_apply, substAlgHom_apply]
    exact hN _ (coeff_subst_eq_zero_of_degree ha hf)⟩

variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_subst_of_gen (n k : ℕ)
    (hk : ∀ i, c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i))
    (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  have ha := constantCoeff_nmul c.isLaw.const k
  have gens : ∀ i, ((c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha))) (X i) =
      ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) (X i) := by
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X, (c.isEval n).1, hk]
    rfl
  have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : G.A n) ^ m ∣ ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) f := by
    intro m
    obtain ⟨N, hN⟩ := (c.isEval n).2 m
    exact ⟨N, fun f hf => by
      rw [AlgHom.comp_apply]
      exact pow_dvd_map (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (hN f hf)⟩
  have e := GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext p O (Fin d) (G.A n) _ _ gens (cont_subst (c.ev n) (c.isEval n).2 ha) cont'
  have := DFunLike.congr_fun e h
  rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply] at this
  exact this

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]
variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_nmul (n k : ℕ) (i : Fin d) :
    c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  induction k generalizing i with
  | zero =>
    rw [mulBy_zero_apply, c.aug, map_zero]
    exact map_zero _
  | succ k ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun l => (X l : MvPowerSeries (Fin d) O)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul c.isLaw.const k j
      · exact constantCoeff_X _
    set Θ := (c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero hs)) with hΘ
    set Λ := (Algebra.TensorProduct.lmul' O).comp ((Algebra.TensorProduct.map
      (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (AlgHom.id O (G.A n))).comp (c.ev₂ n)) with hΛ
    have gens : ∀ j, Θ (X j) = Λ (X j) := by
      rintro (j | j)
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one]
        exact ih j
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul]
        exact (c.isEval n).1 j
    have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
        (p : G.A n) ^ m ∣ Λ f := by
      intro m
      obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
      exact ⟨N, fun f hf => by
        rw [hΛ, AlgHom.comp_apply, AlgHom.comp_apply]
        exact pow_dvd_map _ (pow_dvd_map _ (hN f hf))⟩
    have e : Θ = Λ := GlobalTheory.T.padicContinuous_mvPowerSeries_algHom_ext p O (Fin d ⊕ Fin d) (G.A n) Θ Λ gens
      (cont_subst (c.ev n) (c.isEval n).2 hs) cont'
    have e1 : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun l => X l) (c.μ i) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    have e2 := DFunLike.congr_fun e (c.μ i)
    rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply,
      c.comul] at e2
    rw [e1, e2, mulBy_succ_apply]

theorem ev_subst_nmul : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n k : ℕ) (h : MvPowerSeries (Fin d) O),
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  intro p _ O _ _ G d c n k h
  exact ev_subst_of_gen c n k (ev_nmul c n k) h

end GlobalTheory.EvMul
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural : ∀ (p : ℕ) (R A σ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype σ] [IsAdicComplete (Ideal.span {(p : A)}) A] (x : σ → A), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∃! E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E) ∧ ∀ E : MvPowerSeries σ R →ₐ[R] A, IsEval p x E → (∀ (τ : Type) [Fintype τ] (u : τ → MvPowerSeries σ R) (E' : MvPowerSeries τ R →ₐ[R] A), (∀ j, constantCoeff (u j) = 0) → IsEval p (fun j => E (u j)) E' → ∀ f, E (subst u f) = E' f) ∧ (∀ f, constantCoeff f = 0 → ∃ N : ℕ, (p : A) ∣ E f ^ N) ∧ ∀ (R' A' : Type) [CommRing R'] [CommRing A'] [Algebra R' A'] [IsHausdorff (Ideal.span {(p : A')}) A'] (r : R →+* R') (g : A →+* A') (E' : MvPowerSeries σ R' →ₐ[R'] A'), (∀ c, g (algebraMap R A c) = algebraMap R' A' (r c)) → IsEval p (fun i => g (x i)) E' → ∀ f, g (E f) = E' (map r f) := by
  first | exact @GlobalTheory.CEval.continuous_eval | exact GlobalTheory.CEval.continuous_eval | (intros; apply GlobalTheory.CEval.continuous_eval <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit (R := O) (c.ev n f) = ∑ i, lin f i • PDiv.dUnit (R := O) (c.x n i) := by
  first | exact @GlobalTheory.chart_form_basis | exact GlobalTheory.chart_form_basis | (intros; apply GlobalTheory.chart_form_basis <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_devissage_step_independent : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → ∀ N' N : Ideal B, IsStep p θ N' N → ∀ (b : ι → B) (s : MvPowerSeries (Fin d) Q), (∀ i, b i ∈ N) → In N s → QL μ N' (comb b e - s) → (∀ i, b i ∈ N') ∧ In N' s := by
  first | exact @GlobalTheory.step_independent | exact GlobalTheory.step_independent | (intros; apply GlobalTheory.step_independent <;> assumption)
end
