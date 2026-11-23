module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
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

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.CobLog

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem hasSubst_inl : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_inr : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst hasSubst_inl]
  simp

theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst hasSubst_inr]
  simp

theorem constantCoeff_subst_one {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 1) :
    constantCoeff (subst a f) = 1 := by
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero ha ha0, hf, map_one]

theorem constantCoeff_inL {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inL f) = 1 :=
  constantCoeff_subst_one hasSubst_inl (fun _ => constantCoeff_X _) hf

theorem constantCoeff_inR {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inR f) = 1 :=
  constantCoeff_subst_one hasSubst_inr (fun _ => constantCoeff_X _) hf

end SlopeTestRemainingChoices

theorem cob1_formalLog_mem_ker : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ)
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) →
    ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 →
    subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) →
    In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  intro p _ B O Q _ _ _ _ _ θ hF d μ' hμ g hg hmul
  have hsμ : HasSubst μ' := hasSubst_of_constantCoeff_zero hμ
  have hμQ : ∀ i, constantCoeff (up Q μ' i) = 0 := fun i => by
    simp [up, hμ i]
  have hsμQ : HasSubst (up Q μ') := hasSubst_of_constantCoeff_zero hμQ
  set a : MvPowerSeries (Fin d ⊕ Fin d) B := subst μ' g with ha_def
  set b : MvPowerSeries (Fin d ⊕ Fin d) B := inL g * inR g with hb_def
  have ha1 : constantCoeff a = 1 := constantCoeff_subst_one hsμ hμ hg
  have hbL : constantCoeff (inL g) = 1 := constantCoeff_inL hg
  have hbR : constantCoeff (inR g) = 1 := constantCoeff_inR hg
  have hb1 : constantCoeff b = ((1 : Bˣ) : B) := by simp [hb_def, hbL, hbR]
  set h : MvPowerSeries (Fin d ⊕ Fin d) B := a * invOfUnit b 1 with hh_def
  have hab : a = h * b := by
    rw [hh_def, mul_assoc, invOfUnit_mul b 1 hb1, mul_one]
  have hh1 : constantCoeff h = 1 := by
    rw [hh_def, map_mul, ha1, constantCoeff_invOfUnit]
    simp

  have hG : constantCoeff (map (algebraMap B Q) g) = 1 := by simp [hg]
  have key : cob1 (up Q μ') (formalLog (map (algebraMap B Q) g)) =
      formalLog (map (algebraMap B Q) h) := by
    unfold cob1
    have e1 : subst (up Q μ') (formalLog (map (algebraMap B Q) g)) =
        formalLog (map (algebraMap B Q) a) := by
      rw [subst_formalLog hsμQ hG, ha_def, map_subst hsμ]
      rfl
    have e2 : inL (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inL g)) := by
      rw [map_inL]
      exact subst_formalLog hasSubst_inl hG
    have e3 : inR (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inR g)) := by
      rw [map_inR]
      exact subst_formalLog hasSubst_inr hG
    have hmh : constantCoeff (map (algebraMap B Q) h) = 1 := by simp [hh1]
    have hmL : constantCoeff (map (algebraMap B Q) (inL g)) = 1 := by simp [hbL]
    have hmR : constantCoeff (map (algebraMap B Q) (inR g)) = 1 := by simp [hbR]
    have e4 : formalLog (map (algebraMap B Q) a) = formalLog (map (algebraMap B Q) h) +
        formalLog (map (algebraMap B Q) (inL g)) + formalLog (map (algebraMap B Q) (inR g)) := by
      rw [hab, hb_def, ← mul_assoc, map_mul, map_mul,
        formalLog_mul (by rw [map_mul, hmh, hmL, mul_one]) hmR, formalLog_mul hmh hmL]
    rw [e1, e2, e3, e4]
    abel

  have hθb : IsUnit (map θ b) := isUnit_iff_constantCoeff.mpr (by simp [hb_def, hbL, hbR])
  have hθh : map θ h = 1 := by
    have h1 : map θ a = map θ b := by
      rw [ha_def, map_subst hsμ, hmul, hb_def, map_mul, map_inL, map_inR]
    rw [hab, map_mul] at h1
    exact (IsUnit.mul_left_inj hθb).1 (h1.trans (one_mul _).symm)
  have hJ : ∀ x ∈ RingHom.ker θ, ∃ y ∈ RingHom.ker θ, x ^ p = p * y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
    exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
  have hker : ∀ α, coeff α (h - 1) ∈ RingHom.ker θ := by
    intro α
    rw [RingHom.mem_ker, ← coeff_map, map_sub, hθh, map_one, sub_self, map_zero]
  rw [key]
  exact GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF (RingHom.ker θ) hJ (Fin d ⊕ Fin d) h hh1 hker

end GlobalTheory.CobLog
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem in_frob_formalLog_sub_smul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B)
    (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) →
    (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 →
    In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) -
      (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  intro p _ B O Q _ _ _ _ _ θ hF σB s hs hσ d g hg
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hXB : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) := HasSubst.X_pow hp
  have hXQ : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hX0 : ∀ i : Fin d, constantCoeff ((X i : MvPowerSeries (Fin d) B) ^ p) = 0 := fun i => by
    simp [hp]
  set v := subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) with hv
  have hv1 : constantCoeff v = 1 := by
    rw [hv, constantCoeff_subst_of_zero hXB hX0]
    simp [hg]
  have hgp1 : constantCoeff (g ^ p) = 1 := by simp [hg]
  obtain ⟨u, hu⟩ := isUnit_iff_constantCoeff.mpr (hgp1 ▸ isUnit_one : IsUnit (constantCoeff (g ^ p)))
  set k : MvPowerSeries (Fin d) B := ↑u⁻¹ with hk
  have hgk : g ^ p * k = 1 := by rw [hk, ← hu, Units.mul_inv]
  have hk1 : constantCoeff k = 1 := by
    have := congrArg constantCoeff hgk
    rwa [map_mul, hgp1, one_mul, map_one] at this

  have hc := fun α => GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p p B σB hσ d g α
  choose r hr using hc
  set R : MvPowerSeries (Fin d) B := fun α => r α with hR
  have hvR : v - g ^ p = C (p : B) * R := by
    ext α
    rw [coeff_C_mul, hr α]
    rfl
  set h := v * k with hh
  have hh1 : constantCoeff h = 1 := by rw [hh, map_mul, hv1, hk1, one_mul]
  have hhv : h * g ^ p = v := by rw [hh, mul_assoc, mul_comm k, hgk, mul_one]
  have hhJ : ∀ α, coeff α (h - 1) ∈ Ideal.span {(p : B)} := by
    intro α
    have : h - 1 = C (p : B) * (R * k) := by
      rw [hh, ← hgk, ← sub_mul, hvR, mul_assoc]
    rw [this, coeff_C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hJ : ∀ x ∈ Ideal.span {(p : B)}, ∃ y ∈ Ideal.span {(p : B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨(p : B) ^ (p - 1) * a ^ p,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (by omega)), ?_⟩
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), mul_comm]
  have hlog := GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF _ hJ (Fin d) h hh1 hhJ

  set ι := algebraMap B Q with hι
  have hG1 : constantCoeff (map ι g) = 1 := by simp [hg]
  have hmapG : map s (map ι g) = map ι (map σB g) := by
    ext α
    simp [coeff_map, hs]
  have hmapv : map ι v = subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)
      (map ι (map σB g)) := by
    rw [hv, map_subst hXB]
    congr 1
    funext i
    simp
  have hσG1 : constantCoeff (map ι (map σB g)) = 1 := by simp [hg]
  have key : frob p s (formalLog (map ι g)) - (p : Q) • formalLog (map ι g) =
      formalLog (map ι h) := by
    rw [frob, map_formalLog s hG1, hmapG, subst_formalLog hXQ hσG1, ← hmapv, ← hhv, map_mul,
      map_pow, formalLog_mul (by simp [hh1]) (by simp [hg]), formalLog_pow p hG1,
      Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
  rw [key]
  intro α
  obtain ⟨b, -, hb⟩ := hlog α
  exact ⟨b, trivial, hb⟩

end GlobalTheory.QLog
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.LawDer TensorProduct

namespace GlobalTheory.LawDer

theorem convPow_ev_sub_constantCoeff_iterate_mem : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m →
    ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) →
    ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O),
      (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  intro p O _ G d c n m hp u φ hφ k
  induction k with
  | zero =>
    intro F
    obtain ⟨a, ha⟩ := GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd p O G d c n F
    rw [pow_zero, Function.iterate_zero, id, LinearMap.convOne_apply, Algebra.algebraMap_self,
      RingHom.id_apply, ha]
    exact m.mul_mem_right a hp
  | succ k ih =>
    intro F
    obtain ⟨t, ht⟩ := GlobalTheory.T.comul_chart_sub_subst_mem_p_smul p O G d c n F
    rw [pow_succ, LinearMap.convMul_apply, Function.iterate_succ_apply, sub_eq_iff_eq_add.1 ht,
      map_add, map_add, map_smul, map_smul]
    have h1 := GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max p O G d c n m hp u φ hφ (φ ^ k).ofConv (subst c.μ F)
    have h2 := ih (invDer c.μ u F)
    have h3 : (p : O) • LinearMap.mul' O O (TensorProduct.map (φ ^ k).ofConv φ.ofConv t) ∈ m := by
      rw [smul_eq_mul]; exact m.mul_mem_right _ hp
    have := m.add_mem (m.add_mem h1 h2) h3
    convert this using 1
    simp only [invDer]
    ring

end GlobalTheory.LawDer
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct WithConv Coalgebra


theorem _root_.GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
      ∀ (G : GlobalTheory.PDivGroup p O) (d : ℕ) (c : GlobalTheory.QLog.Chart G d)
        (n k : ℕ) (i : Fin d),
        c.ev n (nmul c.μ k i) = PDiv.mulBy (R := O) (A := G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  have : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.NMul.isAdicComplete_ring_of_module (O := O) p
  have heval := ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural
    p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)).1
  have hsucc (k : ℕ) (i : Fin d) : nmul c.μ (k + 1) i =
      subst (Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)) (c.μ i) := by
    rw [nmul, Function.iterate_succ_apply']
    rfl
  have hconstant (k : ℕ) (i : Fin d) : constantCoeff (nmul c.μ k i) = 0 := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih =>
      rw [hsucc]
      have hzero : ∀ j, constantCoeff
          (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
        rintro (j | j)
        · exact ih j
        · exact constantCoeff_X j
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hzero) hzero
        (c.isLaw.const i)
  have hmul (k : ℕ) : (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n) =
      (toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
    PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) k
  induction k with
  | zero =>
    intro i
    have hzero : nmul c.μ 0 i = 0 := rfl
    change c.ev n (nmul c.μ 0 i) =
      (PDiv.mulBy (R := O) (A := G.A n) 0 : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hzero, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    let u := Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)
    let lift : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
      Algebra.TensorProduct.lift (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
    have hu : ∀ j, constantCoeff (u j) = 0 := by
      rintro (j | j)
      · exact hconstant k j
      · exact constantCoeff_X j
    have hlift : IsEval p (fun j => c.ev n (u j)) (lift.comp (c.ev₂ n)) := by
      constructor
      · rintro (j | j)
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl j), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one]
          exact (ih j).symm
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr j), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 j]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        simpa only [AlgHom.comp_apply, map_pow, map_natCast] using map_dvd lift (hN f hf)
    rw [hsucc, heval _ u _ hu hlift, AlgHom.comp_apply, c.comul n i]
    change lift (comul (R := O) (c.x n i)) =
      (PDiv.mulBy (R := O) (A := G.A n) (k + 1) : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hmul, pow_succ, AlgHom.convMul_apply]
    simp only [lift, hmul]
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] [DecidableEq σ]
      [Fintype τ] [DecidableEq τ] (z : σ → B) (u : τ → MvPowerSeries σ B),
      (∀ j, constantCoeff (u j) = 0) → ∀ (g : MvPowerSeries τ Q) (n : σ →₀ ℕ)
      (S : Finset (τ →₀ ℕ)), (∀ α : τ →₀ ℕ, α.degree ≤ n.degree → α ∈ S) →
      MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q n (MvPowerSeries.subst (σ := τ) (τ := σ) (R := Q) (S := Q) (up Q u) g)) =
        ∑ α ∈ S, coeff α g *
          algebraMap B Q (MvPolynomial.eval z (trunc' B n (α.prod fun j e => u j ^ e))) := by
  intro B Q _ _ _ σ τ _ _ _ _ z u hu g n S hS
  have ha : HasSubst (up Q u) :=
    hasSubst_of_constantCoeff_zero fun j => by simp [up, constantCoeff_map, hu j]
  have hprod (α : τ →₀ ℕ) : (α.prod fun j e => up Q u j ^ e) =
      map (algebraMap B Q) (α.prod fun j e => u j ^ e) := by
    rw [map_finsuppProd]
    simp [up, map_pow]
  have hcoeff (β : σ →₀ ℕ) (hβ : β ≤ n) :
      coeff β (MvPowerSeries.subst (σ := τ) (τ := σ) (R := Q) (S := Q) (up Q u) g) =
        ∑ α ∈ S, coeff α g * algebraMap B Q (coeff β (α.prod fun j e => u j ^ e)) := by
    rw [coeff_subst ha]
    simp_rw [hprod, coeff_map, smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro α hα
    by_contra hαS
    apply hα
    dsimp only
    have hlt : n.degree < α.degree := lt_of_not_ge fun h => hαS (hS α h)
    rw [GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt B σ τ u hu α β
      (lt_of_le_of_lt (Finsupp.degree_mono hβ) hlt), map_zero, mul_zero]
  rw [GlobalTheory.DivSub.eval_trunc'_eq_sum, Finset.sum_congr rfl fun β hβ => by
    rw [hcoeff β (Finset.mem_Iic.mp hβ)]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_

  rw [GlobalTheory.DivSub.eval_trunc'_eq_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, map_prod]
  simp_rw [map_pow]
  ring
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.hasVal_subst_polynomial_eval : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B), (∀ j, constantCoeff (u j) = 0) → ∀ g : MvPolynomial τ Q, HasVal p z (subst (up Q u) (g : MvPowerSeries τ Q)) (MvPolynomial.eval (fun j => algebraMap B Q (E (u j))) g) := by
  first | exact @GlobalTheory.QLog.hasVal_subst_poly | exact GlobalTheory.QLog.hasVal_subst_poly | (intros; apply GlobalTheory.QLog.hasVal_subst_poly <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : O)}) O] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, constantCoeff (μ i) = 0 := by
  first | exact @GlobalTheory.constantCoeff_eq_zero_of_eval_eq_comul | exact GlobalTheory.constantCoeff_eq_zero_of_eval_eq_comul | (intros; apply GlobalTheory.constantCoeff_eq_zero_of_eval_eq_comul <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroupChart_integral_additive_series_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ s : MvPowerSeries (Fin d) O, cob1 (up E c.μ) (map (algebraMap O E) s) = 0 → s = 0 := by
  first | exact @GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero | exact GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) → In (J * N) (subst (up Q u) f - subst (up Q v) f) := by
  first | exact @GlobalTheory.KatzCongr.subst_sub_in | exact GlobalTheory.KatzCongr.subst_sub_in | (intros; apply GlobalTheory.KatzCongr.subst_sub_in <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.isEval_comul_assoc_of_isEval : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A)) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, constantCoeff (μ i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A)) (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A))) fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  first | exact @GlobalTheory.Chart.Assoc.assoc_eval | exact GlobalTheory.Chart.Assoc.assoc_eval | (intros; apply GlobalTheory.Chart.Assoc.assoc_eval <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.divided_in_of_quasi_logarithm : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → DIn N f := by
  first | exact @GlobalTheory.QLogDiff.dIn_of_QL | exact GlobalTheory.QLogDiff.dIn_of_QL | (intros; apply GlobalTheory.QLogDiff.dIn_of_QL <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.quasiLog_reduces_to_cocycle : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ f ∈ quasiLog p h, ∃ c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w) ∧ ∀ f ∈ quasiLog p h, ∀ c, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c → IsCoc μ c := by
  first | exact @GlobalTheory.quasiLog_reduces | exact GlobalTheory.quasiLog_reduces | (intros; apply GlobalTheory.quasiLog_reduces <;> assumption)
end
