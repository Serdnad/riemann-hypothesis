module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle502
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

open GlobalTheory.PDiv

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}

theorem exists_eq_add_single {α : Fin d →₀ ℕ} (h : α ≠ 0) :
    ∃ (i : Fin d) (β : Fin d →₀ ℕ), α = β + Finsupp.single i 1 ∧ α.degree = β.degree + 1 := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hle : Finsupp.single i 1 ≤ α := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  refine ⟨i, α - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  conv_lhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add (f := _), Finsupp.degree_single]

variable (c : Chart G d)

theorem counit_ev_monomial (n : ℕ) {β : Fin d →₀ ℕ} (hβ : β ≠ 0) (a : O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n (monomial β a)) = 0 := by
  obtain ⟨i, γ, rfl, -⟩ := exists_eq_add_single hβ
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, map_mul]
  change _ * Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, mul_zero]

theorem dUnit_ev_monomial (n : ℕ) {α : Fin d →₀ ℕ} (hα : 2 ≤ α.degree) (a : O) :
    dUnit (R := O) (c.ev n (monomial α a)) = 0 := by
  have h0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single h0
  have hβ : β ≠ 0 := by
    have hb : β.degree ≠ 0 := by omega
    exact fun h => hb (by rw [h]; simp)
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, dUnit, AugCot.d_mul,
    c.counit_ev_monomial n hβ]
  change _ • _ + Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) • _ = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, zero_smul, zero_smul, add_zero]

theorem dUnit_ev_of_high (n N : ℕ) (hN : ∀ f : MvPowerSeries (Fin d) O,
    (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → (p : G.A n) ^ n ∣ c.ev n f)
    (f : MvPowerSeries (Fin d) O) (hf : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) :
    dUnit (R := O) (c.ev n f) = 0 := by
  obtain ⟨b, hb⟩ := hN f hf
  rw [hb, dUnit, AugCot.d_mul]
  have h1 : ((p : G.A n) ^ n) = algebraMap O (G.A n) ((p : O) ^ n) := by simp
  rw [h1, AugCot.d_algebraMap, smul_zero, add_zero, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact G.pow_smul_cot n _

theorem dUnit_ev_of_two (n : ℕ) (f : MvPowerSeries (Fin d) O)
    (hf : ∀ α : Fin d →₀ ℕ, α.degree ≤ 1 → coeff α f = 0) : dUnit (R := O) (c.ev n f) = 0 := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 n
  classical
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) f with hP
  have hsplit : f = (P : MvPowerSeries (Fin d) O) + (f - P) := by ring
  rw [hsplit, map_add (f := _), dUnit, map_add (f := _), ← dUnit, ← dUnit]
  rw [c.dUnit_ev_of_high n N hN (f - P) fun α hα => ?_, add_zero]
  · rw [MvPolynomial.as_sum P]
    have : ((∑ v ∈ P.support, MvPolynomial.monomial v (AddMonoidAlgebra.coeff P v) :
        MvPolynomial (Fin d) O) : MvPowerSeries (Fin d) O) =
        ∑ v ∈ P.support, monomial v (AddMonoidAlgebra.coeff P v) := by

      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]

    rw [this, map_sum, dUnit, map_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv' : AddMonoidAlgebra.coeff P v ≠ 0 := MvPolynomial.mem_support_iff.1 hv
    have h2 : 2 ≤ v.degree := by
      by_contra hc
      apply hv'
      rw [hP, coeff_trunc']
      split_ifs
      · exact hf v (by omega)
      · rfl
    exact c.dUnit_ev_monomial n h2 _
  · rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro j
    exact ((Finsupp.le_degree j α).trans hα.le)

theorem dlog_eq_sum_lin [Fact p.Prime] (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O)
    (h1 : constantCoeff u = 1) (hu : ∀ n, c.ev n u = charElem χ n) :
    dlog G χ = ∑ i, lin u i • c.form i := by
  classical
  apply Subtype.ext
  funext n
  rw [Submodule.coe_sum, Finset.sum_apply, dlog_val, ← hu n]
  simp only [Submodule.coe_smul, Pi.smul_apply]
  set g : MvPowerSeries (Fin d) O := ∑ i, lin u i • X i with hg
  have hsplit : u = 1 + g + (u - 1 - g) := by ring
  have hev : c.ev n g = ∑ i, lin u i • c.x n i := by

    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, (c.isEval n).1 i]
  have e1 : dUnit (R := O) (c.ev n u) = dUnit (R := O) (c.ev n 1) + dUnit (R := O) (c.ev n g) +
      dUnit (R := O) (c.ev n (u - 1 - g)) := by
    conv_lhs => rw [hsplit]
    simp only [PDiv.dUnit, map_add (f := _)]
  rw [e1, c.dUnit_ev_of_two n (u - 1 - g) ?_, add_zero, map_one, hev]

  · simp only [PDiv.dUnit, AugCot.d_one, zero_add, map_sum, map_smul]
    rfl
  intro α hα
  have hcg : ∀ i, coeff (Finsupp.single i 1) g = lin u i := fun i => by

    rw [hg, map_sum]
    simp only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj ((Finsupp.single_left_inj one_ne_zero).1 h).symm
    · simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1'
  · rw [(Finsupp.degree_eq_zero_iff α).1 h0]
    have hg0 : coeff 0 g = 0 := by

      rw [hg, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, coeff_X, if_neg, smul_zero]
      intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this
    rw [map_sub, map_sub, hg0, coeff_zero_eq_constantCoeff_apply, h1,
      coeff_zero_eq_constantCoeff_apply, map_one]
    ring
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h1'
    obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single hne
    have hβ : β = 0 := (Finsupp.degree_eq_zero_iff β).1 (by omega)
    subst hβ
    rw [zero_add, map_sub, map_sub, hcg, coeff_one, if_neg, sub_zero]
    · exact sub_self _
    · intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

theorem dlog_eq_sum_lin' : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i :=
  fun _ _ _ _ _ _ _ _ c χ u h1 hu => c.dlog_eq_sum_lin χ u h1 hu

end GlobalTheory.QLog.Chart
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCoef

theorem coeff_frob_single (p : ℕ) [hp : Fact p.Prime] {Q : Type} [CommRing Q] {d : ℕ}
    (s : Q →+* Q) (f : MvPowerSeries (Fin d) Q) (j : Fin d) :
    coeff (Finsupp.single j p) (frob p s f) = s (lin f j) := by
  classical
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hs : HasSubst (fun i => (X i : MvPowerSeries (Fin d) Q) ^ p) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hp0]
  rw [frob, coeff_subst hs]
  have key : ∀ e : Fin d →₀ ℕ, (e.prod fun i n => ((X i : MvPowerSeries (Fin d) Q) ^ p) ^ n) =
      monomial (p • e) 1 := by
    intro e
    induction e using Finsupp.induction with
    | zero => simp
    | single_add i n e hi hn ih =>
      rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.prod_single_index
        (by simp), ← pow_mul, X_pow_eq, monomial_mul_monomial, one_mul, smul_add,
        Finsupp.smul_single, smul_eq_mul]
  simp_rw [key]
  rw [finsum_eq_single _ (Finsupp.single j 1)]
  · rw [coeff_monomial, if_pos (by rw [Finsupp.smul_single, smul_eq_mul, mul_one]), smul_eq_mul,
      mul_one, coeff_map, lin]
  · intro e he
    rw [coeff_monomial, if_neg, smul_zero]
    intro h
    apply he
    ext i
    have := congrArg (fun g => g i) h
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at this ⊢
    split_ifs at this ⊢ with h1
    · exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) (this.symm.trans (mul_one p).symm)
    · exact (mul_eq_zero.1 this.symm).resolve_left hp0

theorem coef_logs_inv_frob : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  intro p _ B Q _ _ _ s σ hs _ d k e U hU h hlin hint
  classical
  set x : Fin d → Fin d ⊕ Fin k → Q := fun j l => (p : Q) * coeff (Finsupp.single j p) (e l) with hx
  have hD : ∀ l i, (U * blk d k (p : B) 1) l i =
      U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i := by
    intro l i
    simp [blk, Matrix.mul_diagonal]
  have hco : ∀ i j, coeff (Finsupp.single j p)
      (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) =
      s (lin (e i) j) - ∑ l, algebraMap B Q (U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i) *
        coeff (Finsupp.single j p) (e l) := by
    intro i j

    rw [map_sub, GlobalTheory.FrobCoef.coeff_frob_single, comb, map_sum]
    simp_rw [coeff_smul, hD]
  have key : ∀ j, ∃ y : Fin d ⊕ Fin k → B, (∀ i, ∑ l, algebraMap B Q (U l i) * x j l =
      algebraMap B Q (y i)) ∧ ∀ i, ∃ t, y i - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
    intro j
    have H : ∀ i, ∃ yi : B, ∑ l, algebraMap B Q (U l i) * x j l = algebraMap B Q yi ∧
        ∃ t, yi - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
      rintro (a | r)
      · obtain ⟨b, hb, hbe⟩ := (h (Sum.inl a)).2 a rfl (Finsupp.single j p)
        obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.1 hb
        rw [hco, hlin] at hbe
        refine ⟨(Pi.single a (1 : B) : Fin d → B) j - β * p, ?_, -β, ?_⟩
        · have h1 : s ((Pi.single a (1 : Q) : Fin d → Q) j) = algebraMap B Q ((Pi.single a (1 : B) : Fin d → B) j) := by
            by_cases haj : j = a
            · subst haj; simp
            · simp [Pi.single_apply, haj]
          have hS : ∑ l, algebraMap B Q (U l (Sum.inl a)) * x j l = ∑ l, algebraMap B Q
              (U l (Sum.inl a) * (p : B)) * coeff (Finsupp.single j p) (e l) :=
            Finset.sum_congr rfl fun l _ => by simp only [hx, Sum.elim_inl, map_mul, map_natCast]; ring
          simp only [Sum.elim_inl] at hbe
          rw [hS, map_sub, ← h1]
          linear_combination -hbe
        · by_cases haj : a = j
          · subst haj; simp; ring
          · simp [Pi.single_apply, haj, Ne.symm haj]; ring
      · obtain ⟨b1, -, hb1⟩ := (h (Sum.inr r)).1 (Finsupp.single j p)
        obtain ⟨b0, hb0⟩ := hint (Sum.inr r) j
        rw [hco, hb0, hs] at hb1
        refine ⟨p * (σ b0 - b1), ?_, σ b0 - b1, by simp⟩
        simp only [Sum.elim_inr, mul_one] at hb1
        have : ∑ l, algebraMap B Q (U l (Sum.inr r)) * coeff (Finsupp.single j p) (e l) =
            algebraMap B Q (σ b0 - b1) := by
          rw [map_sub, ← hb1]; ring
        simp only [hx, map_mul, map_natCast, ← this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
    choose y hy1 hy2 using H
    exact ⟨y, hy1, hy2⟩
  choose y hy1 hy2 using key
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  refine ⟨fun a j => ∑ i, U⁻¹ i (Sum.inl a) * y j i, fun a j => ⟨?_, ?_⟩⟩
  · have : ∀ m, algebraMap B Q (∑ i, U⁻¹ i m * y j i) = x j m := by
      intro m
      calc algebraMap B Q (∑ i, U⁻¹ i m * y j i)
          = ∑ i, algebraMap B Q (U⁻¹ i m) * ∑ l, algebraMap B Q (U l i) * x j l := by

            simp only [map_sum, map_mul, hy1]
        _ = ∑ l, algebraMap B Q ((U * U⁻¹) l m) * x j l := by

            simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x j m := by
            rw [hUU]
            simp [Matrix.one_apply]
    exact this _
  · choose t ht using hy2 j
    refine ⟨∑ i, U⁻¹ i (Sum.inl a) * t i, ?_⟩
    have h1 : U⁻¹ (Sum.inl j) (Sum.inl a) = ∑ i, U⁻¹ i (Sum.inl a) * (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i := by
      simp [Pi.single_apply]
    rw [h1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ht i]; ring

end GlobalTheory.FrobCoef
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CChartLimit

theorem smod_span_iff {R : Type} [CommRing R] (a x y : R) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem exists_series_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [Fintype σ]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)], (∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)) →
    ∀ (x : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n) (t : ∀ n, A n),
    (∀ n, IsEval p (x n) (E n)) → (∀ n, ∃ f, E n f = t n) →
    (∀ n f, E (n + 1) f = t (n + 1) → E n f = t n) →
    (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
    ∃ g, ∀ n, E n g = t n := by
  intro p O σ _ _ _ A _ _ hH x E t hE hs hstep hker
  classical
  choose g hg using hs
  have hdown : ∀ n d f, E (n + d) f = t (n + d) → E n f = t n := by
    intro n d f
    induction d with
    | zero => exact id
    | succ d ih => exact fun hf => ih (hstep (n + d) f hf)
  have hgk : ∀ n k, n ≤ k → E n (g k) = t n := by
    intro n k hnk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
    exact hdown n d _ (hg _)
  choose K hK using hker
  let K' : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup (fun i => max i (K i i))
  have hK'mono : Monotone K' := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hK'ge : ∀ j, j ≤ K' j ∧ K j j ≤ K' j := fun j => by
    have := Finset.le_sup (f := fun i => max i (K i i)) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  let h : ℕ → MvPowerSeries σ O := fun j => g (K' j)
  have hcau : ∀ j j', j ≤ j' → ∀ α : σ →₀ ℕ, α.degree < j →
      (p : O) ^ j ∣ coeff α (h j) - coeff α (h j') := by
    intro j j' hjj α hα
    have h0 : E (K j j) (h j - h j') = 0 := by
      rw [map_sub, hgk _ _ (hK'ge j).2, hgk _ _ ((hK'ge j).2.trans (hK'mono hjj)), sub_self]
    have := hK j j _ h0 α hα
    rwa [map_sub] at this
  have hc : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ n, (p : O) ^ n ∣ coeff α (h (n + α.degree + 1)) - L := by
    intro α
    have hpre : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
    obtain ⟨L, hL⟩ := hpre.prec (f := fun n => coeff α (h (n + α.degree + 1))) (by
      intro m n hmn
      rw [smod_span_iff]
      have := hcau (m + α.degree + 1) (n + α.degree + 1) (by omega) α (by omega)
      exact (pow_dvd_pow _ (by omega)).trans this)
    exact ⟨L, fun n => (smod_span_iff _ _ _ _).1 (hL n)⟩
  choose L hL using hc
  let μ : MvPowerSeries σ O := L
  have hμ : ∀ α, coeff α μ = L α := fun α => rfl
  refine ⟨μ, fun n => ?_⟩
  haveI := hH n
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A n)})).2
  intro m
  rw [smod_span_iff]
  obtain ⟨N, hN⟩ := (hE n).2 m
  have hj : E n (h (m + N + n)) = t n :=
    hgk n (K' (m + N + n)) (le_trans (by omega) (hK'ge (m + N + n)).1)
  have hd : ∀ α : σ →₀ ℕ, α.degree < N →
      (p : O) ^ m ∣ coeff α μ - coeff α (h (m + N + n)) := by
    intro α hα
    have h1 := hL α m
    have h2 := hcau (m + α.degree + 1) (m + N + n) (by omega) α (by omega)
    have h2' : (p : O) ^ m ∣ coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n)) :=
      (pow_dvd_pow _ (by omega)).trans h2
    have e : coeff α μ - coeff α (h (m + N + n)) =
        (coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n))) -
          (coeff α (h (m + α.degree + 1)) - L α) := by rw [hμ]; ring
    rw [e]; exact dvd_sub h2' h1
  choose q hq using hd
  let Q : MvPowerSeries σ O := fun α => if hα : α.degree < N then q α hα else 0
  have hQ : ∀ α (hα : α.degree < N), coeff α Q = q α hα := fun α hα => by
    show (if hα : α.degree < N then q α hα else 0) = q α hα
    rw [dite_eq_left hα]
  let R := μ - h (m + N + n) - (p : O) ^ m • Q
  have hR : ∀ α : σ →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro α hα
    simp only [R, map_sub, MvPowerSeries.coeff_smul, hQ α hα, smul_eq_mul, hq α hα, sub_self]
  have hER := hN R hR
  have hsplit : E n μ - t n = E n R + (p : A n) ^ m * E n Q := by
    have hμeq : μ = h (m + N + n) + ((p : O) ^ m • Q + R) := by simp only [R]; abel
    rw [hμeq, map_add (f := _), map_add (f := _), hj, map_smul, Algebra.smul_def, map_pow, map_natCast]
    ring
  rw [hsplit]
  exact dvd_add hER (dvd_mul_right _ _)

end GlobalTheory.CChartLimit
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.FrNil

theorem counit_ev_sub_constantCoeff (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O) :
    (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  set P : MvPolynomial (Fin d) O := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F with hP

  have halg : ((Bialgebra.counitAlgHom O (G.A n)).comp
      ((c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O))) =
      MvPolynomial.aeval (fun _ => (0 : O)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.coe_X,
      MvPowerSeries.map_id]
    rw [(c.isEval n).1 i]
    exact c.aug n i
  have hPc : Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) = constantCoeff F := by
    have := congrArg (fun φ => φ P) halg
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.map_id] at this
    rw [show Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) =
      Bialgebra.counitAlgHom O (G.A n) (c.ev n (P : MvPowerSeries (Fin d) O)) from rfl, this]
    rw [MvPolynomial.aeval_zero', hP, ← coeff_zero_eq_constantCoeff_apply, Algebra.algebraMap_self,
      RingHom.id_apply, MvPolynomial.constantCoeff_eq, coeff_trunc', if_pos]
    intro i
    exact Nat.zero_le _
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α (F - (P : MvPowerSeries (Fin d) O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_trans (Finsupp.le_degree i α) hα.le
  obtain ⟨a, ha⟩ := hN _ hT
  rw [pow_one] at ha
  have hsplit : c.ev n F = c.ev n (F - (P : MvPowerSeries (Fin d) O)) + c.ev n P := by
    rw [← map_add (f := _), sub_add_cancel]
  refine ⟨Coalgebra.counit (R := O) a, ?_⟩
  rw [hsplit, map_add (f := _), ha, hPc, add_sub_cancel_right]
  rw [show ((p : G.A n)) * a = (p : O) • a by rw [Algebra.smul_def, map_natCast], map_smul, smul_eq_mul]

end GlobalTheory.FrNil
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.mapPowerSeriesFamilyToFractions_formalGroupLawNatMultiple : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  first | exact @GlobalTheory.QLog.up_nmul | exact GlobalTheory.QLog.up_nmul | (intros; apply GlobalTheory.QLog.up_nmul <;> assumption)
end
