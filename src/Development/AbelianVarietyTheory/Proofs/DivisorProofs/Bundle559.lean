module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
public import Mathlib.RingTheory.PowerSeries.Log
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem dIn_top_formalLog_map : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q]
    (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 →
      DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  intro B Q _ _ _ _ σ g hg α i
  classical
  obtain ⟨u, hu⟩ : IsUnit g := isUnit_iff_constantCoeff.mpr (by rw [hg]; exact isUnit_one)
  set φ := algebraMap B Q
  have hG : constantCoeff (map φ g) = 1 := by simp [hg]
  have hd : pderiv (R := Q) i (formalLog (map φ g)) = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
    have h1 := mul_pderiv_formalLog hG i
    rw [pderiv_map] at h1
    have h2 : map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    calc pderiv (R := Q) i (formalLog (map φ g))
        = (map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g) * pderiv (R := Q) i (formalLog (map φ g)) := by
          rw [h2, one_mul]
      _ = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g) := by
          rw [mul_assoc, h1, map_mul]
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · refine ⟨coeff (α - Finsupp.single i 1) ((↑u⁻¹ : MvPowerSeries σ B) * pderiv (R := B) i g),
      Submodule.mem_top, ?_⟩
    rw [natCast_mul_coeff_of_pderiv_eq hd hα, coeff_map]

end GlobalTheory.QLog
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace LawUp

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (CobCob.elim_has hu hv)]
  congr 1
  funext j
  cases j <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => map φ (op μ u v i)) =
      op (fun i => map φ (μ i)) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  funext i
  exact mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem isLaw_map (φ : R →+* S) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : IsLaw μ) :
    IsLaw (fun i => map φ (μ i)) := by
  have h12 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
  have h23 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have e := map_op φ μ (τ := Fin d) (u := fun i => (X i : MvPowerSeries (Fin d) R))
      (v := fun _ => 0) (fun _ => constantCoeff_X _) (fun _ => map_zero _)
    rw [h.unit] at e
    simp only [map_X, map_zero] at e
    exact e.symm
  · have e := mvPowerSeriesMap_evalTwoGroups φ (μ i) (τ := Fin d ⊕ Fin d)
      (u := fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (v := fun i => X (Sum.inl i)) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
    simp only [map_X] at e
    unfold swap
    rw [← e]
    exact congrArg (map φ) (h.comm i)
  · have e1 := map_op φ μ h12 CobCob.constantCoeff_threeGroupsThirdVariables
    have e2 := map_op φ μ CobCob.constantCoeff_threeGroupsFirstVariables h23
    have e3 := map_op φ μ (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
    have e4 := map_op φ μ (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
    have hx1 : (fun i => map φ (x1 (R := R) (d := d) i)) = x1 := by funext i; exact map_X _ _
    have hx2 : (fun i => map φ (x2 (R := R) (d := d) i)) = x2 := by funext i; exact map_X _ _
    have hx3 : (fun i => map φ (x3 (R := R) (d := d) i)) = x3 := by funext i; exact map_X _ _
    rw [hx1, hx2] at e3
    rw [hx2, hx3] at e4
    rw [e3, hx3] at e1
    rw [e4, hx1] at e2
    rw [← e1, ← e2, h.assoc]

end LawUp

theorem formalGroupLawCoboundaryTwo_coboundaryOne_fractions : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  intro B Q _ _ _ d μ h g
  have hL : IsLaw (up Q μ) := LawUp.isLaw_map (algebraMap B Q) h
  exact ((formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hL.const g).2.2.2.2.2 hL).1

end GlobalTheory
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul

theorem subst_pow_log (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (m : ℕ) :
    subst (up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B)))
      (PowerSeries.log Q : MvPowerSeries Unit Q)
      = (m : Q) • (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  have h1 : up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B))
      = fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit Q) := by
    funext j
    simp [up]
  have h2 : formalLog (1 + X () : MvPowerSeries Unit Q)
      = (PowerSeries.log Q : MvPowerSeries Unit Q) := by
    rw [formalLog, add_sub_cancel_left, PowerSeries.subst]
    exact congrFun MvPowerSeries.subst_self _
  have h3 := formalLog_pow m (g := (1 + X () : MvPowerSeries Unit Q)) (by simp)
  rw [h2] at h3
  rw [h1, Nat.cast_smul_eq_nsmul, ← h3]
  rfl

end GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.PullQuasiLog

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (j : σ) :
    Katz.lift p (X j : MvPowerSeries σ k) = X j := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs <;> simp

theorem intBy_le_one (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type}
    (c : WittVector p k) : intBy p k σ c ≤ intBy p k σ 1 := by
  intro f hf α
  obtain ⟨w, hw⟩ := hf α
  exact ⟨c * w, by rw [hw, one_mul]⟩

theorem constantCoeff_subst_zero {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) : constantCoeff (subst a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha hf

theorem elim_const {R : Type} [CommRing R] {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hν : IsLaw ν), ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) f = f ∧ (∀ (d' : ℕ) (φ : Fin d → MvPowerSeries (Fin d') k) (ψ : Fin e → MvPowerSeries (Fin d) k), (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (subst φ (ψ l))) f - subst (fun j => Katz.lift p (φ j)) (subst (fun l => Katz.lift p (ψ l)) f) ∈ intBy p k (Fin d') 1) ∧ ∀ φ ψ : Fin e → MvPowerSeries (Fin d) k, (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (op ν φ ψ l)) f - subst (fun l => Katz.lift p (φ l)) f - subst (fun l => Katz.lift p (ψ l)) f ∈ intBy p k (Fin d) 1 := by
  intro p _ k _ _ _ d e ν hν f hf
  have hf' : f ∈ quasiInt p k (Fin e) ∧ cob1 (fun i => lift p (ν i)) f ∈ intBy p k _ 1 := hf
  have hred := fun (σ : Type) => GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k σ
  refine ⟨?_, ?_, ?_⟩
  · have : (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) = X := funext fun j => lift_X p j
    rw [this, subst_self]; rfl
  · intro d' φ ψ hφ hψ
    have hΦ : ∀ j, constantCoeff (lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (lift p (ψ j)) = 0 := fun j => constantCoeff_lift p (hψ j)
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hΨ)
      (hasSubst_of_constantCoeff_zero hΦ)]
    apply intBy_le_one p (p : WittVector p k)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d') _ _ (fun l => subst φ (ψ l)) f
      (fun l => constantCoeff_lift p (constantCoeff_subst_zero hφ (hψ l)))
      (fun l => constantCoeff_subst_zero hΦ (hΨ l))
      (fun l => (hred (Fin d')).2.2.1 _)
      (fun l => (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d') (fun j => lift p (φ j)) φ hΦ
        (fun j => (hred (Fin d')).2.2.1 _)).1 _ _ ((hred (Fin d)).2.2.1 _)) hf'.1
  · intro φ ψ hφ hψ
    set Φ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (φ l) with hΦdef
    set Ψ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (ψ l) with hΨdef
    have hΦ : ∀ j, constantCoeff (Φ j) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (Ψ j) = 0 := fun j => constantCoeff_lift p (hψ j)
    have hL : ∀ i, constantCoeff (lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
    have hcalc := GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) e (Fin d) (Fin d) Φ Ψ hΦ hΨ
    have hredE : ∀ s, Red p (Sum.elim Φ Ψ s) (Sum.elim φ ψ s) := fun s => by
      cases s <;> exact (hred (Fin d)).2.2.1 _
    have hsub := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e ⊕ Fin e) (Fin d) (Sum.elim Φ Ψ) (Sum.elim φ ψ)
      (elim_const hΦ hΨ) hredE
    have hcob : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ =
        subst (op (fun i => lift p (ν i)) Φ Ψ) f - subst Φ f - subst Ψ f := by
      unfold cob1
      rw [(hcalc.2.2.1 _ _).2, (hcalc.2.2.1 _ _).2, hcalc.1, hcalc.2.1,
        hcalc.2.2.2.2.2.1 e _ hL f]
      rfl
    have h1 : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ ∈ intBy p k (Fin d) 1 :=
      hsub.2 1 _ hf'.2
    have h2 : subst (fun l => lift p (op ν φ ψ l)) f - subst (op (fun i => lift p (ν i)) Φ Ψ) f
        ∈ intBy p k (Fin d) 1 := by
      apply intBy_le_one p (p : WittVector p k)
      refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d) _ _ (op ν φ ψ) f
        (fun l => constantCoeff_lift p (constantCoeff_subst_zero (elim_const hφ hψ) (hν.const l)))
        (fun l => constantCoeff_subst_zero (elim_const hΦ hΨ) (hL l))
        (fun l => (hred (Fin d)).2.2.1 _)
        (fun l => hsub.1 _ _ ((hred (Fin e ⊕ Fin e)).2.2.1 _)) hf'.1
    have := add_mem h2 h1
    rw [hcob] at this
    convert this using 1
    abel

end GlobalTheory.Katz.PullQuasiLog
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WittStart

theorem eq_zero_or_single {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ι →₀ ℕ) (h : γ.degree < 2) :
    γ = 0 ∨ ∃ s, γ = Finsupp.single s 1 := by
  by_cases h0 : γ = 0
  · exact Or.inl h0
  right
  obtain ⟨s, hs⟩ : ∃ s, γ s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Finsupp.ext hc)
  rw [Finsupp.degree_eq_sum] at h
  have hsum : ∑ i, γ i = γ s + ∑ i ∈ Finset.univ.erase s, γ i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm
  refine ⟨s, Finsupp.ext fun t => ?_⟩
  by_cases hts : t = s
  · subst hts
    have : ∑ i ∈ Finset.univ.erase t, γ i ≥ 0 := Nat.zero_le _
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_apply, Ne.symm hts, if_false]
    have : γ t ≤ ∑ i ∈ Finset.univ.erase s, γ i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩)
    omega

variable {R : Type} [CommRing R] {d : ℕ}

theorem coeff_single_linear_substitution_pair {τ : Type} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (at2 c u v) =
      ∑ i, coeff (Finsupp.single (Sum.inl i) 1) c * coeff (Finsupp.single t 1) (u i) +
      ∑ i, coeff (Finsupp.single (Sum.inr i) 1) c * coeff (Finsupp.single t 1) (v i) := by
  unfold at2
  rw [GlobalTheory.FormalCalc.coeff_single_subst, Fintype.sum_sum_type]
  · rfl
  · rintro (i | i)
    · exact hu i
    · exact hv i

theorem constantCoeff_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  unfold op at2
  rw [constantCoeff_subst0 (fun s => by cases s with | inl s => exact hu s | inr s => exact hv s)]
  exact hμ0 i

theorem coeff_single_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) (t : τ) :
    coeff (Finsupp.single t 1) (op μ u v i) =
      coeff (Finsupp.single t 1) (u i) + coeff (Finsupp.single t 1) (v i) := by
  classical
  unfold op
  rw [coeff_single_linear_substitution_pair _ _ _ hu hv]
  simp only [hμ, addLaw, map_add (f := _), GlobalTheory.FormalCalc.coeff_single_X]
  simp [add_mul, Finset.sum_add_distrib]

theorem coeff_single_coc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0)
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : IsCoc μ c) (s : Fin d ⊕ Fin d) :
    coeff (Finsupp.single s 1) c = 0 := by
  classical
  have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hinl : ∀ j, coeff (Finsupp.single (Sum.inl j) 1) c = 0 := by
    intro j
    have h := congrArg (coeff (Finsupp.single (Sum.inl j : Fin d ⊕ (Fin d ⊕ Fin d)) 1)) hc.1
    unfold cob2 at h
    rw [map_sub, map_add (f := _), map_sub, map_zero,
      coeff_single_linear_substitution_pair _ _ _ hx2 hx3,
      coeff_single_linear_substitution_pair _ _ _ (constantCoeff_op hμ0 _ _ hx1 hx2) hx3,
      coeff_single_linear_substitution_pair _ _ _ hx1 (constantCoeff_op hμ0 _ _ hx2 hx3),
      coeff_single_linear_substitution_pair _ _ _ hx1 hx2] at h
    simp only [coeff_single_op hμ _ _ hx1 hx2, coeff_single_op hμ _ _ hx2 hx3, x1, x2, x3,
      GlobalTheory.FormalCalc.coeff_single_X] at h
    simpa using h
  cases s with
  | inl j => exact hinl j
  | inr j =>
    have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) hc.2
    unfold swap at h
    rw [coeff_single_linear_substitution_pair _ _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)] at h
    simp only [GlobalTheory.FormalCalc.coeff_single_X] at h
    simp only [Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, zero_add,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← h]
    simp [hinl]

end GlobalTheory.WittStart

namespace GlobalTheory.WittStart

theorem start : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c →
    ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc w
  classical
  have hL := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have hdeg : ∀ s : Fin d ⊕ Fin d, (Finsupp.single s 1).degree ≤ 1 := fun s => by
    rw [Finsupp.degree_single]
  have hμk : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw k d i) :=
    fun i s => (hL i _ (hdeg s)).1
  have hμF : ∀ i s, coeff (Finsupp.single s 1) (Katz.lift p (μ i)) =
      coeff (Finsupp.single s 1) (addLaw (Fr p k) d i) := fun i s => (hL i _ (hdeg s)).2
  have hμ0F : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hclin := coeff_single_coc hμ.const hμk c hc
  set T : k → Fr p k := fun x => algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p x)
    with hT
  set f : MvPowerSeries (Fin d) (Fr p k) :=
    (-(WittVector.teichmuller p (constantCoeff c))) • (1 : MvPowerSeries (Fin d) (Fr p k)) +
      ∑ i, WittVector.teichmuller p (w i) • (X i : MvPowerSeries (Fin d) (Fr p k)) with hf
  have hcoeff : ∀ α, coeff α f = (if α = 0 then -T (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then T (w i) else 0 := by
    intro α

    rw [hf, map_add (f := _), map_sum]
    have e : ∀ (r : WittVector p k) (g : MvPowerSeries (Fin d) (Fr p k)),
        coeff α (r • g) = algebraMap (WittVector p k) (Fr p k) r * coeff α g := fun r g => by
      rw [← algebraMap_smul (Fr p k) r g, coeff_smul]
    simp only [e, coeff_one, coeff_X, hT, map_neg]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
  refine ⟨f, ?_, ?_, ?_⟩
  · intro α
    rw [hcoeff α]
    refine ⟨(if α = 0 then -WittVector.teichmuller p (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then WittVector.teichmuller p (w i) else 0, ?_⟩

    rw [one_mul, map_add (f := _), map_sum]
    congr 1
    · split_ifs <;> simp [hT]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [hT]
  · intro i
    refine ⟨WittVector.teichmuller p (w i), ?_, ?_⟩
    · show coeff _ f = _
      rw [hcoeff]
      simp [Finsupp.single_eq_single_iff, hT]
    · rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  · intro γ hγ
    refine ⟨0, ?_⟩
    rw [mul_zero, map_zero]
    rcases eq_zero_or_single γ hγ with rfl | ⟨s, rfl⟩
    · have h0s : ∀ i : Fin d, (0 : Fin d →₀ ℕ) ≠ Finsupp.single i 1 :=
        fun i => (Finsupp.single_ne_zero.mpr one_ne_zero).symm
      rw [coeff_zero_eq_constantCoeff_apply, map_sub]
      unfold cob1 inL inR
      rw [map_sub, map_sub, constantCoeff_subst0 hμ0F, constantCoeff_subst0 (fun _ => constantCoeff_X _),
        constantCoeff_subst0 (fun _ => constantCoeff_X _), ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_zero_eq_constantCoeff_apply, coeff_lift, hcoeff]
      simp [hT, coeff_zero_eq_constantCoeff_apply, h0s]
    · rw [map_sub, coeff_lift, hclin, WittVector.teichmuller_zero, map_zero, sub_zero]
      unfold cob1 inL inR
      rw [map_sub, map_sub, GlobalTheory.FormalCalc.coeff_single_subst hμ0F,
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _),
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _)]
      simp only [hμF, addLaw, map_add (f := _), mul_add, Finset.sum_add_distrib]
      ring

end GlobalTheory.WittStart
end
end

section

open GlobalTheory.WeilM Matrix

theorem _root_.GlobalTheory.T.rank_chart_bounded_coefficients : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 → C ∈ GlobalTheory.LocMod.Inhab.box T R a := by
  first | exact @GlobalTheory.RankChart.bounded_coeff_of_SB | exact GlobalTheory.RankChart.bounded_coeff_of_SB | (intros; apply GlobalTheory.RankChart.bounded_coeff_of_SB <;> assumption)
end

section

open GlobalTheory.WeilM Matrix

theorem _root_.GlobalTheory.T.rank_chart_shear_invariance : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D], ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k), ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  first | exact @GlobalTheory.RankChart.sb_shear_invariant | exact GlobalTheory.RankChart.sb_shear_invariant | (intros; apply GlobalTheory.RankChart.sb_shear_invariant <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.exists_GL_diagonal_congruent_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  first | exact @GlobalTheory.KSp.exists_gl_diagonal_hermitian | exact GlobalTheory.KSp.exists_gl_diagonal_hermitian | (intros; apply GlobalTheory.KSp.exists_gl_diagonal_hermitian <;> assumption)
end
