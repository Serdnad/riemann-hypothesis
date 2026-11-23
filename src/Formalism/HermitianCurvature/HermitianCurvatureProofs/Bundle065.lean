module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormBasics
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle042
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle046
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle021
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle014
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle018
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle019
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle017
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkipSuccessorIndex.SkipSucc2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
public import Formalism.PeriodIntegrals.Bundle026

@[expose] public section

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace UnipotentUpperFacts

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector

section gen

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

end gen

variable {k r : ℕ}

lemma N_upper {g : B.Mat k r} (hg : g ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hji : j ≤ i) :
    g i j = if i = j then 1 else 0 := by
  have hc := ((WeylGroupFacts.nset_iff g).mp hg).2
  by_cases hj : j.val ≤ r + k
  · exact hc i j hj (Or.inl hji)
  · push Not at hj
    have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
      apply Matrix.inv_eq_left_inv
      calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, WeylGroupFacts.hpk_sq]
    have hci := ((WeylGroupFacts.nset_iff _).mp (WeylGroupFacts.mem_n_inv hg)).2
    rw [hinv] at hci
    have hsj := GBasic.sig_val k r j
    have hsi := GBasic.sig_val k r i
    rw [if_pos (Or.inr hj)] at hsj
    rw [if_pos (Or.inr (by omega))] at hsi
    have h := hci (GBasic.sig k r j) (GBasic.sig k r i) (by omega) (Or.inl (by omega))
    rw [Matrix.mul_assoc, Hpk_mul_apply, mul_Hpk_apply, Matrix.conjTranspose_apply, GBasic.sig_sig,
      GBasic.sig_sig] at h
    have hs1 : GBasic.sgn k r (GBasic.sig k r j) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    have hs2 : GBasic.sgn k r (GBasic.sig k r i) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    rw [hs1, hs2, one_mul, mul_one] at h
    have hiff : (GBasic.sig k r j = GBasic.sig k r i) ↔ (i = j) := by
      constructor
      · intro e; have := congrArg (GBasic.sig k r) e; rw [GBasic.sig_sig, GBasic.sig_sig] at this; exact this.symm
      · intro e; rw [e]
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : i = j
    · rw [if_pos (hiff.mpr e), if_pos e, star_one]
    · rw [if_neg (fun e' => e (hiff.mp e')), if_neg e, star_zero]

lemma N_unip {g : B.Mat k r} (hg : g ∈ Nset k r) : (g - 1) ^ (2 * r + k + 1) = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, N_upper hg i j hji, Matrix.one_apply, sub_self]

end UnipotentUpperFacts

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_self_ne_zero {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  rw [Tz, h] at hT
  simp at hT

theorem herm_proj_zero (x z : Fin (2 * r + k + 1) → ℂ) (hc : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (x - (herm (Hpk k r) x z / herm (Hpk k r) z z) • z) z = 0 := by
  rw [herm_sub_left, herm_smul_left]
  field_simp
  ring

theorem coreW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ξ : B.Mat k r)
    (h1 : ∀ u, inWb k r u → inWb k r (ξ *ᵥ u))
    (h2 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) (ξ *ᵥ u) v = -herm (Hpk k r) u (ξ *ᵥ v))
    (h3 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u z = 0 → herm (Hpk k r) v z = 0 →
      herm (Hpk k r) (ξ *ᵥ u) v = 0)
    (N : ℕ) (h4 : ∀ u, inWb k r u → (ξ ^ N) *ᵥ u = 0) :
    ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
  set c := herm (Hpk k r) z z with hcdef
  have hc0 : c ≠ 0 := herm_self_ne_zero hT

  have stepA : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (herm (Hpk k r) (ξ *ᵥ w) z / c) • z := by
    intro w hw hwz
    set y := ξ *ᵥ w - (herm (Hpk k r) (ξ *ᵥ w) z / c) • z with hydef
    have hy : inWb k r y := inWb_sub (h1 w hw) (inWb_smul _ hz)
    have hyz : herm (Hpk k r) y z = 0 := herm_proj_zero _ _ hc0
    have hyy : herm (Hpk k r) y y = 0 := by
      have e1 : herm (Hpk k r) (ξ *ᵥ w) y = 0 := h3 w y hw hy hwz hyz
      have e2 : herm (Hpk k r) z y = 0 := by rw [herm_swap, hyz, star_zero]
      calc herm (Hpk k r) y y
          = herm (Hpk k r) (ξ *ᵥ w) y - (herm (Hpk k r) (ξ *ᵥ w) z / c) * herm (Hpk k r) z y := by
            conv_lhs => rw [hydef]
            rw [herm_sub_left, herm_smul_left]
        _ = 0 := by rw [e1, e2]; ring
    have : y = 0 := wb_definite hz hT hy hyz (by rw [hyy]; simp)
    exact sub_eq_zero.1 this
  set μ := herm (Hpk k r) (ξ *ᵥ z) z / c with hμ
  set b := ξ *ᵥ z - μ • z with hbdef
  have hb : inWb k r b := inWb_sub (h1 z hz) (inWb_smul _ hz)
  have hbz : herm (Hpk k r) b z = 0 := herm_proj_zero _ _ hc0
  have hξz : ξ *ᵥ z = μ • z + b := by rw [hbdef]; abel

  have stepB : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (-(herm (Hpk k r) w b) / c) • z := by
    intro w hw hwz
    rw [stepA w hw hwz, h2 w z hw hz, hξz, herm_add_right, herm_smul_right, hwz]
    congr 1
    ring
  have hξb : ξ *ᵥ b = (-(herm (Hpk k r) b b) / c) • z := stepB b hb hbz
  have hNz := h4 z hz

  have hb0 : b = 0 := by
    by_contra hb0
    have hbb : herm (Hpk k r) b b ≠ 0 := by
      intro h
      exact hb0 (wb_definite hz hT hb hbz (by rw [h]; simp))
    set l := -(herm (Hpk k r) b b) / c with hl
    have hl0 : l ≠ 0 := div_ne_zero (neg_ne_zero.2 hbb) hc0
    let f : ℕ → ℂ × ℂ := fun m => Nat.rec (motive := fun _ => ℂ × ℂ) (1, 0)
      (fun _ pq => (μ * pq.1 + l * pq.2, pq.1)) m
    have hf0 : f 0 = (1, 0) := rfl
    have hfs : ∀ m, f (m + 1) = (μ * (f m).1 + l * (f m).2, (f m).1) := fun m => rfl
    have hpow : ∀ m, (ξ ^ m) *ᵥ z = (f m).1 • z + (f m).2 • b := by
      intro m
      induction m with
      | zero => rw [hf0, pow_zero, one_mulVec]; simp
      | succ m ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, mulVec_smul, hξz, hξb, hfs]
        module
    rw [hpow] at hNz
    have hp : (f N).1 = 0 := by
      have := congrArg (fun x => herm (Hpk k r) x z) hNz
      simp only [herm_add_left, herm_smul_left, hbz, herm_zero_left, mul_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hc0
    have hq : (f N).2 = 0 := by
      rw [hp, zero_smul, zero_add] at hNz
      exact (smul_eq_zero.1 hNz).resolve_right hb0
    have hnz : ∀ m, (f m).1 ≠ 0 ∨ (f m).2 ≠ 0 := by
      intro m
      induction m with
      | zero => left; rw [hf0]; exact one_ne_zero
      | succ m ih =>
        by_contra hcon
        push Not at hcon
        rw [hfs] at hcon
        obtain ⟨e1, e2⟩ := hcon
        simp only at e1 e2
        rw [e2, mul_zero, zero_add] at e1
        have : (f m).2 = 0 := (mul_eq_zero.1 e1).resolve_left hl0
        rcases ih with h | h
        · exact h e2
        · exact h this
    rcases hnz N with h | h
    · exact h hp
    · exact h hq

  have hξz' : ξ *ᵥ z = μ • z := by rw [hξz, hb0, add_zero]
  have hpow2 : ∀ m, (ξ ^ m) *ᵥ z = μ ^ m • z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hξz', smul_smul, pow_succ]
  rw [hpow2] at hNz
  have hμ0 : μ = 0 := by
    have := congrArg (fun x => herm (Hpk k r) x z) hNz
    simp only [herm_smul_left, herm_zero_left] at this
    exact pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hc0) |>.1
  have hξz0 : ξ *ᵥ z = 0 := by rw [hξz', hμ0, zero_smul]
  intro u hu
  set α := herm (Hpk k r) u z / c
  have hu' : inWb k r (u - α • z) := inWb_sub hu (inWb_smul _ hz)
  have hu'z : herm (Hpk k r) (u - α • z) z = 0 := herm_proj_zero _ _ hc0
  have e : u = α • z + (u - α • z) := by abel
  rw [e, mulVec_add, mulVec_smul, hξz0, stepB _ hu' hu'z, hb0, herm_zero_right]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

section

theorem Formalism.FourierDecayAlt.P.expansion_first_column : Formalism.FourierDecayAlt.Q.ExpFirstCol := PI.QmColExpWork.expFirstCol

theorem Formalism.FourierDecayAlt.P.expansion_last_column : Formalism.FourierDecayAlt.Q.ExpLastCol := PI.QmColExpWork.expLastCol

theorem Formalism.FourierDecayAlt.P.expansion_first_line : Formalism.FourierDecayAlt.Q.ExpFirstRow := PI.QmRowExpWork.expFirstRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.expansion_last_line : Formalism.FourierDecayAlt.Q.ExpLastRow := PI.QmRowExpWork.expLastRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.line_form_of_minor : Formalism.FourierDecayAlt.Q.RowForm := quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.skip_succ_identity : Formalism.FourierDecayAlt.Q.SkipSucc := PI.QmSkipWork.skipSucc

theorem Formalism.FourierDecayAlt.P.skip_succ_double_identity : Formalism.FourierDecayAlt.Q.SkipSucc2 := PI.QmSkipWork.skipSucc2

theorem Formalism.FourierDecayAlt.P.star_quantum_minor : Formalism.FourierDecayAlt.Q.StarMinor := quantum_minor_star

theorem Formalism.FourierDecayAlt.P.rtt_independence : Formalism.FourierDecayAlt.Q.RTTIndependence := rtt_independence'

theorem Formalism.FourierDecayAlt.P.contractions_covariant : Formalism.FourierDecayAlt.Q.ContractionsCovariant := PI.contractionsCovariant_iff.mpr ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩

theorem Formalism.FourierDecayAlt.P.first_contraction_adapted : Formalism.FourierDecayAlt.Q.ChatAdapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).1

theorem Formalism.FourierDecayAlt.P.second_contraction_adapted : Formalism.FourierDecayAlt.Q.Chat2Adapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).2

theorem Formalism.FourierDecayAlt.P.generator_gl_level : Formalism.FourierDecayAlt.Q.EabGlLev := qnEabGl

theorem Formalism.FourierDecayAlt.P.generator_action_preserved : Formalism.FourierDecayAlt.Q.EabPres := qnEabPres

theorem Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian : Formalism.FourierDecayAlt.Q.QMinorLeftH := quantum_minor_left

theorem Formalism.FourierDecayAlt.P.right_differential_skew : Formalism.FourierDecayAlt.Q.RdSkew := qnRdSkew

theorem Formalism.FourierDecayAlt.P.right_action_rule : Formalism.FourierDecayAlt.Q.RuleRight := qnRuleRight

theorem Formalism.FourierDecayAlt.P.weyl_level_element_properties : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts := weyl_level_element_properties'

theorem Formalism.FourierDecayAlt.P.twisted_leibniz_rule : Formalism.FourierDecayAlt.Q.YLeibniz := qnYLeibniz
end
