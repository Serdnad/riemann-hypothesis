module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle630
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvP

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

theorem constantCoeff_nmul {O : Type} [CommRing O] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ j, constantCoeff (μ j) = 0) :
    ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul μ k j) = 0 := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ihk =>
    intro j
    have hsucc : nmul μ (k + 1) j =
        subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (μ j) := by
      simp only [nmul, Function.iterate_succ_apply']
      rfl
    rw [hsucc]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (hμ j) <;>
    · rintro (l | l)
      · simpa using ihk l
      · simp

theorem ev_subst_nmul_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), c.ev (n + 1) (subst (nmul c.μ p) s) = G.mulP n (c.ev n s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n s
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A (n + 1)) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A (n + 1))}) (G.A (n + 1)) :=
    isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.CEval.continuous_eval p O (G.A (n + 1)) (Fin d) (c.x (n + 1)) (c.nil (n + 1))).2
    (c.ev (n + 1)) (c.isEval (n + 1))
  let E' : MvPowerSeries (Fin d) O →ₐ[O] G.A (n + 1) :=
    (G.mulP n : G.A n →ₐ[O] G.A (n + 1)).comp (c.ev n)
  have hu : ∀ j, constantCoeff (nmul c.μ p j) = 0 :=
    constantCoeff_nmul c.μ (fun j => c.isLaw.const j) p
  have hE' : IsEval p (fun j => c.ev (n + 1) (nmul c.μ p j)) E' := by
    constructor
    · intro j
      show G.mulP n (c.ev n (X j)) = c.ev (n + 1) (nmul c.μ p j)
      rw [(c.isEval n).1 j, GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c (n + 1) p j, ← c.res n j, mulP_res]
    · intro m
      obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun f hf => ?_⟩
      have := map_dvd (G.mulP n : G.A n →ₐ[O] G.A (n + 1)) (hN f hf)
      rwa [map_pow, map_natCast] at this
  exact hT.1 (Fin d) (nmul c.μ p) E' hu hE' s

end GlobalTheory.EvP
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem cob1_defect_and_defect_mul_of_isLaw : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ),
    cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧
    defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  intro O E _ _ _ d μ hμ f m n
  obtain ⟨hL, hmap⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E (algebraMap O E)
  have hup : ∀ k, up E (nmul μ k) = nmul (up E μ) k := fun k =>
    funext fun i => (hmap k i).2
  have hc : ∀ i, constantCoeff (up E μ i) = 0 := hL.const
  have hk : ∀ k, HasSubst (up E (nmul μ k)) := fun k =>
    hasSubst_of_constantCoeff_zero fun i => by
      rw [hup k]; exact ((GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL 0 k).1 i)
  have hsub : ∀ a b : MvPowerSeries (Fin d) E, cob1 (up E μ) (a - b) = cob1 (up E μ) a - cob1 (up E μ) b :=
    fun a b => by rw [eq_sub_iff_add_eq, ← formalCoboundary_add hc, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · unfold defect
    rw [hsub, formalCoboundary_smul hc, hup n]
    rw [GlobalTheory.T.coboundary_subst_eq_pullback_of_is_hom E d (up E μ) (up E μ) (nmul (up E μ) n) hc hc (GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple E d (up E μ) hL n) f]
  · have hcomp : subst (up E (nmul μ n)) (subst (up E (nmul μ m)) f) = subst (up E (nmul μ (m * n))) f := by
      rw [subst_comp_subst_apply (hk m) (hk n)]
      congr 1
      funext i
      rw [hup, hup, hup, (GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL m n).2.2.1 i]
    unfold defect
    rw [subst_sub (hk n), subst_smul (hk n), hcomp, smul_sub, Nat.cast_mul, mul_smul]
    abel

end GlobalTheory.QLog
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.tail_subst_small : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → ∀ m : ℕ, ∃ M0 : ℕ, ∀ M ≥ M0, ∀ n : σ →₀ ℕ, ∃ b : B, MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) (f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q)))) = algebraMap B Q (p ^ m * b) := by
  intro p hp B O Q _ _ _ _ θ hF σ _ _ z hz τ _ _ u f hu hD m
  have hpr : p.Prime := hp.out
  obtain ⟨L, hL⟩ := GlobalTheory.T.pow_dvd_eval_trunc_of_high_order p B σ z hz
  obtain ⟨M0, hM0⟩ := GlobalTheory.T.add_mul_le_of_pow_le_of_large p L m hpr.two_le
  refine ⟨M0, fun M hM n => ?_⟩
  set g : MvPowerSeries τ Q := f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q) with hg
  have hfin := Finsupp.finite_of_degree_le (σ := τ) n.degree
  rw [GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum B Q σ τ z u hu g n hfin.toFinset (fun α hα => by simpa using hα)]

  have key : ∀ α : τ →₀ ℕ, ∃ b : B, coeff α g * algebraMap B Q (MvPolynomial.eval z
      (trunc' B n (α.prod fun j e => u j ^ e))) = algebraMap B Q (p ^ m * b) := by
    intro α
    by_cases hα : α ≤ Finsupp.equivFunOnFinite.symm fun _ => M
    · refine ⟨0, ?_⟩
      have : coeff α g = 0 := by
        simp [hg, coeff_trunc', hα]
      simp [this]
    · have hcg : coeff α g = coeff α f := by
        simp [hg, coeff_trunc', hα]
      rw [hcg]
      obtain ⟨i, hi⟩ : ∃ i, M < α i := by
        by_contra h
        push_neg at h
        exact hα (fun i => by simpa using h i)
      obtain ⟨b, -, hb⟩ := hD α i
      obtain ⟨v, n', hn', hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := α i) (by omega) p hpr.one_lt.ne'
      have hcop : Nat.Coprime n' p := ((Nat.Prime.coprime_iff_not_dvd hpr).2 hn').symm
      obtain ⟨w, hw⟩ := (hF.unit_coprime n' hcop).exists_right_inv
      have hn'pos : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hdec; omega)
      have hpv : p ^ v ≤ α.degree := by
        have : p ^ v ≤ α i := by rw [hdec]; exact Nat.le_mul_of_pos_right _ hn'pos
        exact this.trans (Finsupp.le_degree i α)
      have hdeg : (v + m) * L ≤ α.degree :=
        hM0 α.degree v (by have := Finsupp.le_degree i α; omega) hpv
      obtain ⟨c, hc⟩ := hL (v + m) (α.prod fun j e => u j ^ e) (fun β hβ =>
        GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt B σ τ u hu α β (by rw [mul_comm] at hβ; omega)) n
      refine ⟨b * w * c, ?_⟩
      rw [hc]
      rw [hdec] at hb
      have hw' := congrArg (algebraMap B Q) hw
      simp only [map_mul, map_pow, map_natCast, map_one, Nat.cast_mul, Nat.cast_pow] at hb hw' ⊢
      linear_combination ((p : Q) ^ m * algebraMap B Q w * algebraMap B Q c) * hb
        - (coeff α f * (p : Q) ^ (v + m) * algebraMap B Q c) * hw'
  choose bb hbb using key
  refine ⟨∑ α ∈ hfin.toFinset, bb α, ?_⟩

  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => hbb α
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvTor

theorem isHausdorff_of_projective (p : ℕ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := O) (P := A)
  refine ⟨fun a ha => ?_⟩
  have hdiv : ∀ m : ℕ, (p : A) ^ m ∣ a := fun m => by
    have := CEval.dvd_of_smodEq p m (ha m)
    simpa using this
  have hcoord : ∀ x, s a x = 0 := fun x => by
    refine CEval.eq_of_forall_dvd p fun m => ?_
    obtain ⟨b, hb⟩ := hdiv m
    have : a = ((p : O) ^ m) • b := by
      rw [hb, Algebra.smul_def, map_pow, map_natCast]
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, sub_zero]
    exact dvd_mul_right _ _
  have h0 : s a = 0 := Finsupp.ext hcoord
  rw [← hs a, h0, map_zero]

theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] (E : MvPowerSeries σ R →ₐ[R] A)
    (hE : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ E f)
    (u : τ → MvPowerSeries σ R) (hu : ∀ j, constantCoeff (u j) = 0) (ψ : MvPowerSeries τ R →+* A)
    (hC : ∀ c, ψ (C c) = algebraMap R A c) (hX : ∀ j, ψ (X j) = E (u j))
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ ψ f)
    (f : MvPowerSeries τ R) : E (subst u f) = ψ f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact CEval.ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) ψ
    (fun c => by
      show E (substAlgHom hs (C c)) = ψ (C c)
      rw [hC, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = ψ (X j)
      rw [substAlgHom_X, hX])
    (fun m => by
      obtain ⟨N, hN⟩ := hE m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hψ f

end GlobalTheory.EvTor

namespace GlobalTheory.EvTor

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ)
    (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have e : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
    rw [e]
    have h0 : ∀ s : Fin d ⊕ Fin d,
        constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) s) = 0 := by
      rintro (s | s)
      · exact ih s
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem constantCoeff_subst_var {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (e : σ → τ)
    (f : MvPowerSeries σ R) (hf : constantCoeff f = 0) :
    constantCoeff (subst (fun i => (X (e i) : MvPowerSeries τ R)) f) = 0 := by
  have h0 : ∀ s, constantCoeff ((fun i => (X (e i) : MvPowerSeries τ R)) s) = 0 := fun s => by simp
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf

end GlobalTheory.EvTor

namespace GlobalTheory.EvTor

theorem ev₂_at_nmul_pow_self : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (g : MvPowerSeries (Fin d ⊕ Fin d) O), c.ev₂ n (at2 g (fun i => inL (nmul c.μ (p ^ n) i)) (fun i => inR (nmul c.μ (p ^ n) i))) = algebraMap O (G.A n ⊗[O] G.A n) (constantCoeff g) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n g
  haveI : IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    isHausdorff_of_projective (O := O) (A := G.A n ⊗[O] G.A n) p
  have hz : ∀ i, c.ev n (nmul c.μ (p ^ n) i) = 0 := fun i => by
    rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i,
      map_zero]
  have hcont : ∀ (φ : G.A n →ₐ[O] G.A n ⊗[O] G.A n) (m : ℕ), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O,
      (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
        ((p : G.A n ⊗[O] G.A n)) ^ m ∣ (φ.comp (c.ev n)).toRingHom f := fun φ m => by
    obtain ⟨N, hN⟩ := (c.isEval n).2 m
    refine ⟨N, fun f hf => ?_⟩
    have := map_dvd φ (hN f hf)
    rwa [map_pow, map_natCast] at this
  have hL : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := fun f =>
    eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp)
      ((Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n)).toRingHom
      (fun r => by
        show (Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n) (MvPowerSeries.C r) = _
        rw [c_eq_algebraMap, AlgHom.commutes])
      (fun i => by
        show Algebra.TensorProduct.includeLeft (S := O) (c.ev n (X i)) = _
        rw [(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inl i)]
        rfl)
      (hcont _) f
  have hR : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inR f) = (1 : G.A n) ⊗ₜ[O] c.ev n f := fun f =>
    eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp)
      ((Algebra.TensorProduct.includeRight).comp (c.ev n)).toRingHom
      (fun r => by
        show (Algebra.TensorProduct.includeRight).comp (c.ev n) (MvPowerSeries.C r) = _
        rw [c_eq_algebraMap, AlgHom.commutes])
      (fun i => by
        show Algebra.TensorProduct.includeRight (c.ev n (X i)) = _
        rw [(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inr i)]
        rfl)
      (hcont _) f
  have hμ := c.isLaw.const
  have hu : ∀ j, constantCoeff (Sum.elim (fun i => inL (nmul c.μ (p ^ n) i))
      (fun i => inR (nmul c.μ (p ^ n) i)) j) = 0 := by
    rintro (j | j)
    · exact constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)
    · exact constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)
  refine eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ hu
    ((algebraMap O (G.A n ⊗[O] G.A n)).comp constantCoeff) (fun r => by simp) ?_ ?_ g
  · rintro (j | j)
    · simp only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inl]
      rw [hL, hz, TensorProduct.zero_tmul]
    · simp only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inr]
      rw [hR, hz, TensorProduct.tmul_zero]
  · intro m
    refine ⟨1, fun f hf => ?_⟩
    have h0 : constantCoeff f = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hf 0 (by simp)
    simp [h0]

end GlobalTheory.EvTor
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  first | exact @GlobalTheory.FrobCongr.frob_cong | exact GlobalTheory.FrobCongr.frob_cong | (intros; apply GlobalTheory.FrobCongr.frob_cong <;> assumption)
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace CobSymCoc

open GlobalTheory.Katz.CobCob

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (elim_has hu hv)]
  congr 1
  funext k
  cases k <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map φ (op μ u v i) = op (fun j => map φ (μ j)) (fun j => map φ (u j)) (fun j => map φ (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem map_threeGroupsFirstVariables (φ : R →+* S) : (fun j => map φ (x1 (R := R) (d := d) j)) = x1 := by
  funext j; exact map_X φ _
theorem map_threeGroupsSecondVariables (φ : R →+* S) : (fun j => map φ (x2 (R := R) (d := d) j)) = x2 := by
  funext j; exact map_X φ _
theorem map_threeGroupsThirdVariables (φ : R →+* S) : (fun j => map φ (x3 (R := R) (d := d) j)) = x3 := by
  funext j; exact map_X φ _

theorem map_assocL (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ x1 (op μ x2 x3) i)) =
      op (fun j => map φ (μ j)) x1 (op (fun j => map φ (μ j)) x2 x3) := by
  funext i
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables (op_const h constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables), map_threeGroupsFirstVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem map_assocR (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ (op μ x1 x2) x3 i)) =
      op (fun j => map φ (μ j)) (op (fun j => map φ (μ j)) x1 x2) x3 := by
  funext i
  rw [map_op φ μ (op_const h constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables, map_threeGroupsThirdVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables]

end CobSymCoc


open CobSymCoc CobCob in
theorem cob_symCoc_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL N f hf
  have hM : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, constantCoeff_map, hL.const i, map_zero]
  obtain ⟨A, Bs, -⟩ := formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hM f
  refine ⟨?_, ?_⟩
  · rw [A]
    have eL : op (up Q μ) x1 (op (up Q μ) x2 x3) = up Q (op μ x1 (op μ x2 x3)) :=
      (map_assocL (algebraMap B Q) μ hL.const).symm
    have eR : op (up Q μ) (op (up Q μ) x1 x2) x3 = up Q (op μ (op μ x1 x2) x3) :=
      (map_assocR (algebraMap B Q) μ hL.const).symm
    rw [eL, eR]
    refine GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p B O Q θ hF (RingHom.ker θ) ?_ (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) N f _ _ hf
      (op_const hL.const constantCoeff_threeGroupsFirstVariables (op_const hL.const constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables))
      (op_const hL.const (op_const hL.const constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables) ?_
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
      exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
    · intro i α
      rw [RingHom.mem_ker, ← coeff_map, map_sub]
      have h1 := congrFun (map_assocL θ μ hL.const) i
      have h2 := congrFun (map_assocR θ μ hL.const) i
      rw [h1, h2, hL.law.assoc, sub_self, map_zero]
  · have hs : (fun i => swap (up Q μ i)) = up Q μ := by
      funext i
      have e : map (algebraMap B Q) (swap (μ i)) = swap (map (algebraMap B Q) (μ i)) := by
        unfold swap
        rw [mvPowerSeriesMap_evalTwoGroups (algebraMap B Q) (μ i) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
        simp only [map_X]
      show swap (map (algebraMap B Q) (μ i)) = map (algebraMap B Q) (μ i)
      rw [← e, hL.comm i]
    rw [hs, sub_self] at Bs
    exact sub_eq_zero.1 Bs

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  first | exact @GlobalTheory.Katz.semiHom_constantCoeff_and_ev | exact GlobalTheory.Katz.semiHom_constantCoeff_and_ev | (intros; apply GlobalTheory.Katz.semiHom_constantCoeff_and_ev <;> assumption)
end
