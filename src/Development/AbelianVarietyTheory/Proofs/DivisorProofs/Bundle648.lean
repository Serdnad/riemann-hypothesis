module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle604
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.Assoc

theorem isEval_comp (p : ℕ) {O A B σ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] B) (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨c, hc⟩ := hN f hf
  exact ⟨φ c, by simp [hc, map_mul, map_pow, map_natCast]⟩

theorem constantCoeff_op {O : Type} [CommRing O] {d : ℕ} {τ : Type}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ O) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (j : Fin d) : constantCoeff (op μ u v j) = 0 := by
  have h : ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    rintro (k | k) <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ j)

theorem dvd_pow_map (p : ℕ) {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (φ : A →ₐ[O] B) {a : A} (h : ∃ N : ℕ, (p : A) ∣ a ^ N) :
    ∃ N : ℕ, (p : B) ∣ φ a ^ N := by
  obtain ⟨N, c, hc⟩ := h
  exact ⟨N, φ c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

end GlobalTheory.Chart.Assoc

namespace GlobalTheory.Chart.Assoc

theorem assoc_eval (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ}
    (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A)
    (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hx : ∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (h2 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂)
    (h3 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃)
    (hc : ∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) :
    ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  let Φ₁ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Algebra.TensorProduct.includeLeft (S := O))
  let Φ₃ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) := Algebra.TensorProduct.includeRight
  let Φ₂ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    (Algebra.TensorProduct.assoc O O O A A A).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom O A) (AlgHom.id O A))
  let Φ₄ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Bialgebra.comulAlgHom O A)
  have hnil : ∀ k, ∃ N : ℕ, (p : A ⊗[O] (A ⊗[O] A)) ∣ (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) k ^ N := by
    rintro (k | k | k)
    · exact dvd_pow_map p (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A ⊗[O] A)) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A))) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A))) (hx k)
  have sub := ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ hnil).2 E₃ h3).1
  have c1 : ∀ j, constantCoeff (x1 (R := O) (d := d) j) = 0 := fun j => by simp [x1]
  have c2 : ∀ j, constantCoeff (x2 (R := O) (d := d) j) = 0 := fun j => by simp [x2]
  have c3 : ∀ j, constantCoeff (x3 (R := O) (d := d) j) = 0 := fun j => by simp [x3]
  have ce : ∀ {u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O},
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) →
      ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    intro u v hu hv k; rcases k with k | k <;> simp [hu, hv]
  have L1 : ∀ j, E₃ (op μ x1 x2 j) = Φ₁ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₁ h2
    have := sub _ (Sum.elim x1 x2) (Φ₁.comp E₂) (ce c1 c2) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x1, x2, h3.1, Φ₁, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  have L3 : ∀ j, E₃ (op μ x2 x3 j) = Φ₃ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₃ h2
    have := sub _ (Sum.elim x2 x3) (Φ₃.comp E₂) (ce c2 c3) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x2, x3, h3.1, Φ₃, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  intro i
  have LL : E₃ (op μ (op μ x1 x2) x3 i) = Φ₂ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₂ h2
    have := sub _ (Sum.elim (op μ x1 x2) x3) (Φ₂.comp E₂)
      (ce (constantCoeff_op μ hμ _ _ c1 c2) c3) (by
      convert e using 2 with k
      rcases k with k | k
      · simp only [Sum.elim_inl]
        rw [L1]
        have key : ∀ c : A ⊗[O] A, Φ₁ c = (Algebra.TensorProduct.assoc O O O A A A) (c ⊗ₜ[O] 1) := by
          intro c
          induction c using TensorProduct.induction_on with
          | zero => simp
          | tmul a b => simp [Φ₁, Algebra.TensorProduct.one_def]
          | add a b ha hb => rw [map_add (f := _), ha, hb, TensorProduct.add_tmul, map_add (f := _)]
        rw [key]
        simp [Φ₂]
      · simp [x3, h3.1, Φ₂, Algebra.TensorProduct.one_def]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  have RR : E₃ (op μ x1 (op μ x2 x3) i) = Φ₄ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₄ h2
    have := sub _ (Sum.elim x1 (op μ x2 x3)) (Φ₄.comp E₂)
      (ce c1 (constantCoeff_op μ hμ _ _ c2 c3)) (by
      convert e using 2 with k
      rcases k with k | k
      · simp [x1, h3.1, Φ₄, Algebra.TensorProduct.one_def]
      · simp only [Sum.elim_inr]
        rw [L3]
        simp [Φ₃, Φ₄]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  rw [LL, RR]
  have ka : ∀ w : (A ⊗[O] A) ⊗[O] A,
      (Algebra.TensorProduct.assoc O O O A A A) w = TensorProduct.assoc O A A A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul a a' => simp
      | add c c' hc hc' => rw [TensorProduct.add_tmul, map_add (f := _), hc, hc', map_add (f := _)]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]
  have k2 : ∀ c : A ⊗[O] A, Φ₂ c = TensorProduct.assoc O A A A (LinearMap.rTensor A (Coalgebra.comul (R := O) (A := A)) c) := by
    intro c
    rw [← ka]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₂]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have k4 : ∀ c : A ⊗[O] A, Φ₄ c = LinearMap.lTensor A (Coalgebra.comul (R := O) (A := A)) c := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₄]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]
  rw [k2, k4, Coalgebra.coassoc_apply]

end GlobalTheory.Chart.Assoc
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
open TensorProduct

namespace GlobalTheory.QLog.Chart

theorem subst_μ_eq_inL_mul_inR : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) →
    subst c.μ u = inL u * inR u := by
  intro p _ O _ _ _ G d c χ u hu
  set D := subst c.μ u - inL u * inR u with hD
  have hev : ∀ n, c.ev₂ n D = 0 := by
    intro n
    obtain ⟨h1, h2, h3, -⟩ := ev₂_eval p O G d c n u
    rw [hD, map_sub, map_mul, h1, h2, h3, hu n, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      (isGroupLikeElem_charElem χ n).comul_eq_tmul_self, sub_self]
  rw [← sub_eq_zero, ← hD]
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) _ fun m => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O (G.A n) (G.A n) (Fin d) (Fin d) (c.x n) (c.x n) (c.ev n) (c.ev n) (c.ev₂ n) m
    (α.degree + 1) (c.isEval n) (c.isEval n) (c.isEval₂ n) (c.surj n) (c.surj n) hn hn D (hev n) α
    (Nat.lt_succ_self _)

end GlobalTheory.QLog.Chart
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.frobenius_congruence_combination_over_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ (W : Fin d ⊕ Fin k → F.B) (b : Fin k → F.B), (∀ l, ¬IsUnit (F.θ (W l))) → In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb W e) → In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => 0) b) e)) - frob p F.s (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e))) → ∃ (F₁ : MvPowerSeries (Fin d ⊕ Fin d) F.B) (t : MvPowerSeries (Fin d) O), map (algebraMap F.B F.Q) F₁ = cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e) ∧ (∀ i, ¬IsUnit (lin t i)) ∧ (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - F.θ (coeff β F₁) ^ p)) ∧ ∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t)) := by
  first | exact @GlobalTheory.SmallSecond.frob_congr_to_O | exact GlobalTheory.SmallSecond.frob_congr_to_O | (intros; apply GlobalTheory.SmallSecond.frob_congr_to_O <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DivSub

theorem eval_trunc'_eq_sum {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] (w : σ → R)
    (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.eval w (trunc' R n f) = ∑ β ∈ Finset.Iic n, coeff β f * ∏ i ∈ β.support, w i ^ β i := by
  have hsub : (trunc' R n f).support ⊆ Finset.Iic n := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, coeff_trunc'] at hm
    split_ifs at hm with h
    · exact Finset.mem_Iic.mpr h
    · exact absurd rfl hm
  rw [MvPolynomial.eval_eq, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_trunc', if_pos (Finset.mem_Iic.mp hm)]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

theorem eval_trunc'_subst_eq_sum :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] [DecidableEq σ]
      [Fintype τ] [DecidableEq τ] (z : σ → B) (u : τ → MvPowerSeries σ B),
      (∀ j, constantCoeff (u j) = 0) → ∀ (g : MvPowerSeries τ Q) (n : σ →₀ ℕ)
      (S : Finset (τ →₀ ℕ)), (∀ α : τ →₀ ℕ, α.degree ≤ n.degree → α ∈ S) →
      MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) g)) =
        ∑ α ∈ S, coeff α g *
          algebraMap B Q (MvPolynomial.eval z (trunc' B n (α.prod fun j e => u j ^ e))) := by
  intro B Q _ _ _ σ τ _ _ _ _ z u hu g n S hS
  have ha : HasSubst (up Q u) :=
    hasSubst_of_constantCoeff_zero fun j => by simp [up, constantCoeff_map, hu j]
  have hP : ∀ α : τ →₀ ℕ, (α.prod fun j e => (up Q u j) ^ e) =
      map (algebraMap B Q) (α.prod fun j e => u j ^ e) := by
    intro α
    rw [map_finsuppProd]
    simp [up, map_pow]
  have hcoeff : ∀ β ≤ n, coeff β (subst (up Q u) g) =
      ∑ α ∈ S, coeff α g * algebraMap B Q (coeff β (α.prod fun j e => u j ^ e)) := by
    intro β hβ
    rw [coeff_subst ha]
    simp_rw [hP, coeff_map, smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro α hα
    by_contra hαS
    apply hα
    dsimp only
    have hlt : n.degree < α.degree := lt_of_not_ge fun h => hαS (hS α h)
    rw [GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt B σ τ u hu α β (lt_of_le_of_lt (Finsupp.degree_mono hβ) hlt), map_zero,
      mul_zero]
  rw [eval_trunc'_eq_sum, Finset.sum_congr rfl fun β hβ => by
    rw [hcoeff β (Finset.mem_Iic.mp hβ)]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_

  rw [eval_trunc'_eq_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, map_prod]
  simp_rw [map_pow]
  ring

end GlobalTheory.DivSub
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalChart_evalSquare_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧ c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧ c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev₂_eval | exact GlobalTheory.QLog.Chart.ev₂_eval | (intros; apply GlobalTheory.QLog.Chart.ev₂_eval <;> assumption)
end

section

open GlobalTheory GlobalTheory.TopForm

namespace GlobalTheory

open KaehlerDifferential IsLocalRing Module

theorem isFreeGen_dForm_uniformiser_cons : ∀ (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (α : k →+* V) (n : ℕ) (t : V) (w : Fin n → V), α.EssFiniteType →
    Irreducible t → Nonempty (Module.Basis (Fin (n + 1)) V (Omega α)) →
    (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ α w P)) →
    IsFreeGen V (dForm α (Fin.cons t w : Fin (n + 1) → V)) := by
  intro k V _ _ _ _ _ α n t w hft ht hb₀ hw
  obtain ⟨b₀⟩ := hb₀
  letI := α.toAlgebra
  haveI : Algebra.EssFiniteType k V := hft
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)

  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ α w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP

  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg

    simp only [map_add (f := _), map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
    Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)
  exact isFreeGen_dForm z b hb

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

open CategoryTheory TensorProduct MvPowerSeries in
private lemma mem_quasiLog_iff (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ)
    (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)) :
    f ∈ _root_.GlobalTheory.Katz.quasiLog p h ↔
      f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d) ∧
        _root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f ∈
          _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) 1 := by
  unfold _root_.GlobalTheory.Katz.quasiLog
  exact Iff.rfl

open CategoryTheory TensorProduct MvPowerSeries in
private lemma exists_lin_eq_algebraMap_of_mem_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    {d : ℕ} {f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d)) (i : Fin d) :
    ∃ a, _root_.GlobalTheory.Katz.lin f i = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a := by
  obtain ⟨a, ha⟩ := hf (Finsupp.single i 1) i
  exact ⟨a, by simpa [_root_.GlobalTheory.Katz.lin] using ha⟩

open CategoryTheory TensorProduct MvPowerSeries in
private lemma isCoc_of_red_cob1_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (h : _root_.GlobalTheory.Katz.IsLaw μ) (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k))
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d))
    (c : MvPowerSeries (Fin d ⊕ Fin d) k)
    (hc : _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c) :
    _root_.GlobalTheory.Katz.IsCoc μ c := by
  obtain ⟨-, huniq, -, hadd, -, hdivp, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, huniq3, -, -, -, hdivp3, -⟩ :=
    _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d ⊕ Fin d)
  obtain ⟨htwo, hswap⟩ := _root_.GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem p k d μ h f hf
  obtain ⟨hcomm, -⟩ := _root_.GlobalTheory.Katz.red_coboundaries p k d μ
    h.const
  obtain ⟨hred2, hredswap⟩ := hcomm _ c hc
  unfold _root_.GlobalTheory.Katz.IsCoc
  refine ⟨huniq3 _ _ _ hred2 ((hdivp3 _).1 htwo), ?_⟩
  exact sub_eq_zero.1 (huniq _ _ _ (hadd _ _ _ _ hredswap hc).2 ((hdivp _).1 hswap))


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.quasiLog_reduces : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ), (∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∃ c w, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin f) w) ∧ ∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∀ c, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c → _root_.GlobalTheory.Katz.IsCoc μ c := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun f hf => ?_, fun f hf c hc => ?_⟩
  · obtain ⟨hint, hcob⟩ := (mem_quasiLog_iff p k d μ h f).1 hf
    obtain ⟨c, hc⟩ := ((_root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)).1 _).1 hcob
    choose a ha using exists_lin_eq_algebraMap_of_mem_quasiInt p k hint
    exact ⟨c, fun i => WittVector.constantCoeff (a i), hc, fun i => ⟨a i, ha i, rfl⟩⟩
  · exact isCoc_of_red_cob1_quasiInt p k d μ h f
      ((mem_quasiLog_iff p k d μ h f).1 hf).1 c hc

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.coboundaryOne_teichmullerLift_isCocycle_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ f ∈ quasiInt p k (Fin d), cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧ swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈ intBy p k _ p := by
  first | exact @GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem | exact GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem | (intros; apply GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent : ∀ (k : Type) [CommRing k] (d : ℕ) (A : Type) [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)), (∀ i, Coalgebra.counit (R := k) (x i) = 0) → ∀ f : MvPowerSeries (Fin d) k, Coalgebra.counit (R := k) (evA k x hx f) = constantCoeff f ∧ dUnit (R := k) (evA k x hx f) = ∑ i, lin f i • dUnit (R := k) (x i) := by
  first | exact @GlobalTheory.Katz.counit_dUnit_evA | exact GlobalTheory.Katz.counit_dUnit_evA | (intros; apply GlobalTheory.Katz.counit_dUnit_evA <;> assumption)
end
