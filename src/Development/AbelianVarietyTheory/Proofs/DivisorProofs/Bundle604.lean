module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle553
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftLaw

def cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) : MvPowerSeries σ S :=
  fun α => g (coeff α f)

theorem coeff_cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) (α : σ →₀ ℕ) :
    coeff α (cmap g f) = g (coeff α f) := rfl

theorem swap_cmap {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (g : R → S)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (cmap g c) = cmap g (swap c) := by
  ext α
  obtain ⟨⟨a, e⟩, rfl⟩ := (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm.surjective α
  have h : (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm (a, e) = Finsupp.sumElim a e := rfl
  rw [h, coeff_cmap, SwapCoeff.coeff_swap, SwapCoeff.coeff_swap, coeff_cmap]

theorem coeff_subst_elim_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (β : Fin d →₀ ℕ) :
    coeff β (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      coeff (Finsupp.embDomain (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) β) c := by
  classical
  have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) :=
    hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
  have hb : HasSubst (X ∘ (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) :
      Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :=
    hasSubst_of_constantCoeff_zero fun s => by simp
  have hr : rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)
      (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      subst (fun s : Fin d ⊕ Fin d => if s.isLeft then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0) c := by
    rw [rename_eq_subst, subst_comp_subst_apply ha hb]
    congr 1
    funext s
    rcases s with i | i
    · simp [subst_X hb]
    · simp only [Sum.elim_inr, Sum.isLeft_inr]
      rw [← coe_substAlgHom hb, map_zero]
      rfl
  rw [← coeff_embDomain_rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d), hr,
    OnePair.coeff_subst_kill]
  rw [if_pos]
  rintro (i | i) hi
  · simp at hi
  · simp [Finsupp.embDomain_apply]

theorem exists_isLift : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  intro B O _ _ θ hθ d μ hμ
  classical
  by_cases h1 : (1 : O) = 0
  ·
    haveI : Subsingleton O := subsingleton_of_zero_eq_one h1.symm
    have hm : ∀ i, map θ (addLaw B d i) = μ i := fun i => by
      ext α
      exact Subsingleton.elim _ _
    have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) B)) fun (_ : Fin d) => 0) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    have hs : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
        fun i => X (Sum.inl i)) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    refine ⟨addLaw B d, ⟨fun i => by simp [addLaw], ?_, fun i => ?_, ?_⟩, hm⟩
    · funext i
      simp only [op, at2, addLaw]
      rw [subst_add ha, subst_X ha, subst_X ha]
      simp
    · simp only [swap, at2, addLaw]
      rw [subst_add hs, subst_X hs, subst_X hs]
      simp [add_comm]
    · have : (fun i => map θ (addLaw B d i)) = μ := funext hm
      rw [this]
      exact hμ
  ·
    let s : O → B := fun x => if x = 0 then 0 else if x = 1 then 1 else (hθ x).choose
    have hs : ∀ x, θ (s x) = x := fun x => by
      simp only [s]
      split_ifs with h h'
      · rw [map_zero, h]
      · rw [map_one, h']
      · exact (hθ x).choose_spec
    have hs0 : s 0 = 0 := by simp [s]
    have hs1 : s 1 = 1 := by simp [s, h1]
    refine ⟨fun i => cmap s (μ i), ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_cmap, coeff_zero_eq_constantCoeff_apply,
        hμ.const i, hs0]
    · funext i
      ext β
      have hu := congrArg (coeff β) (congrFun hμ.unit i)
      simp only [op, at2] at hu ⊢
      rw [coeff_subst_elim_zero] at hu ⊢
      rw [coeff_cmap, hu, coeff_X, coeff_X]
      split_ifs
      · exact hs1
      · exact hs0
    · rw [swap_cmap, hμ.comm i]
    · have : (fun i => map θ (cmap s (μ i))) = μ := funext fun i => by
        ext α
        rw [coeff_map, coeff_cmap, hs]
      rw [this]
      exact hμ
    · ext α
      rw [coeff_map, coeff_cmap, hs]

end GlobalTheory.LiftLaw
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.LogUniq

theorem eq_zero_of_linear_zero_coboundary_zero_fractions : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E]
    [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ R : MvPowerSeries (Fin d) E,
    lin R = 0 → cob1 (up E μ) R = 0 → R = 0 := by
  intro p _ O E _ _ _ hF d μ hμ R hlin hcob
  classical
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : E) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    rw [Nat.cast_mul, Nat.cast_pow]
    refine (hF.unit_p.pow a).mul ?_
    have hc : Nat.Coprime m p :=
      Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
    have := (hF.unit_coprime m hc).map (algebraMap O E)
    simpa using this
  have hL : IsLift (RingHom.id O) μ := ⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩
  have hlow : ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 →
      coeff α (up E μ i) = coeff α (addLaw E d i) := by
    intro i α hα
    rw [up, coeff_map, GlobalTheory.CobHom.coeff_lift_low hL i α hα, GlobalTheory.Katz.LowLaw.coeff_addLaw]
    split_ifs <;> simp
  have hdeg : ∀ a e : Fin d →₀ ℕ, (Finsupp.sumElim a e).degree = (a + e).degree := by
    intro a e
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
    simp
  have key : ∀ N : ℕ, ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro N
    induction N with
    | zero => intro α h; omega
    | succ N ih =>
      intro α hα
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hα) with h | h
      · exact ih α h
      have hc := (GlobalTheory.CobLead.cob_eq_additive_lead E d (up E μ) N hlow).1 R ih
      have hcoef : ∀ a e : Fin d →₀ ℕ, a + e = α →
          coeff (Finsupp.sumElim a e) (cob1 (addLaw E d) R) = 0 := by
        intro a e hae
        rw [← (hc _).2 (by rw [hdeg, hae, h]), hcob, map_zero]
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N
        · have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 h
          subst h0
          have := hcoef 0 0 (by simp)
          rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial] at this
          simpa using this
        · obtain ⟨j, rfl⟩ := GlobalTheory.Katz.LowLaw.eq_single_of_degree_eq_one h
          exact congrFun hlin j
      · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
          by_contra! hc0
          have : α = 0 := Finsupp.ext hc0
          rw [this, map_zero] at h
          omega
        set a := α - Finsupp.single i 1 with ha
        have hae : a + Finsupp.single i 1 = α := by
          ext k
          simp only [ha, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs with h1 <;> (try subst h1) <;> omega
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, zero_add] at hae
          rw [← hae, Finsupp.degree_single] at h
          omega
        have hs0 : Finsupp.single i 1 ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
        have := hcoef a (Finsupp.single i 1) hae
        rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial, if_neg hs0, if_neg ha0, sub_zero, sub_zero, hae] at this
        have hpos : (∏ s, (α s).choose (a s)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.2 fun s _ => (Nat.choose_pos ?_).ne'
          rw [← hae]; simp
        exact (hunit _ hpos).mul_right_eq_zero.1 this
  ext α
  simpa using key (α.degree + 1) α (by omega)

end GlobalTheory.LogUniq
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.hasPAdicPowerSeriesValue_sub_mem_pd_ideal : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q), (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' → ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  first | exact @GlobalTheory.HasValCong.hasVal_sub_mem | exact GlobalTheory.HasValCong.hasVal_sub_mem | (intros; apply GlobalTheory.HasValCong.hasVal_sub_mem <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B) (m N : ℕ), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → (∀ f, evA f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, evB f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ f, E f = 0 → ∀ α : σ ⊕ τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  first | exact @GlobalTheory.KerTensor.ker_tensor | exact GlobalTheory.KerTensor.ker_tensor | (intros; apply GlobalTheory.KerTensor.ker_tensor <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.surjective_isEval_tmul_of_surjective : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  first | exact @GlobalTheory.SurjTens.surjective_eval_tmul | exact GlobalTheory.SurjTens.surjective_eval_tmul | (intros; apply GlobalTheory.SurjTens.surjective_eval_tmul <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C), constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  first | exact @GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | exact GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.exists_series_of_compatible' : ∀ (p : ℕ) (O σ : Type) [CommRing O] [Fintype σ] [IsAdicComplete (Ideal.span {(p : O)}) O] (A : ℕ → Type) [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)], (∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)) → ∀ (x : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n) (t : ∀ n, A n), (∀ n, IsEval p (x n) (E n)) → (∀ n, ∃ f, E n f = t n) → (∀ n f, E (n + 1) f = t (n + 1) → E n f = t n) → (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∃ g, ∀ n, E n g = t n := by
  first | exact @GlobalTheory.CChartLimit.exists_series_of_compatible | exact GlobalTheory.CChartLimit.exists_series_of_compatible | (intros; apply GlobalTheory.CChartLimit.exists_series_of_compatible <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i := by
  first | exact @GlobalTheory.QLog.Chart.dlog_eq_sum_lin' | exact GlobalTheory.QLog.Chart.dlog_eq_sum_lin' | (intros; apply GlobalTheory.QLog.Chart.dlog_eq_sum_lin' <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.coeff_p_logarithms_congr_inv_frobenius_matrix_mod_p : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  first | exact @GlobalTheory.FrobCoef.coef_logs_inv_frob | exact GlobalTheory.FrobCoef.coef_logs_inv_frob | (intros; apply GlobalTheory.FrobCoef.coef_logs_inv_frob <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct


theorem _root_.GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  first | exact @GlobalTheory.FrNil.counit_ev_sub_constantCoeff | exact GlobalTheory.FrNil.counit_ev_sub_constantCoeff | (intros; apply GlobalTheory.FrNil.counit_ev_sub_constantCoeff <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_pDivGroupChart_level_one_nilpotent_mod_p : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 → (p : G.A 1) ∣ c.ev 1 f ^ N := by
  first | exact @GlobalTheory.AugNil.aug_nil | exact GlobalTheory.AugNil.aug_nil | (intros; apply GlobalTheory.AugNil.aug_nil <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  first | exact @GlobalTheory.QLog.ql_comb_top | exact GlobalTheory.QLog.ql_comb_top | (intros; apply GlobalTheory.QLog.ql_comb_top <;> assumption)
end
