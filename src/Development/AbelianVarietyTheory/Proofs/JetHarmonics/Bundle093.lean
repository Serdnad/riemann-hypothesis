module

import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle019
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PlacePartEigenLifts
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle032
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
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
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensorKFinite

variable {k r : ℕ} {ι : Type} [Fintype ι]

theorem smMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have h := hT.smul 0 0 R.smSub.zero_mem
  simpa using h

theorem kfin_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm)
    (hA : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, R'.σ g (T c y) = ∑ i, a i • T i (R.σ g y))
    (c : ι) (y : R.H) (hy : R.KFin y) : R'.KFin (T c y) := by
  apply Gp91.GlobalTheory.TensorKFinite.kfin_of_family <;> assumption

theorem tk_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm) (hTK : ∀ v ∈ R.TK, v ∈ R.sm)
    (hF : ∀ c y, R.KFin y → R'.KFin (T c y))
    (hB : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, T c (R.σ g y) = ∑ i, a i • R'.σ g (T i y))
    (c : ι) (y : R.H) (hy : y ∈ R.TK) : T c y ∈ R'.TK := by
  apply Gp91.GlobalTheory.TensorKFinite.tk_of_family <;> assumption

theorem inv_rows [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι ι ℂ) (h : A * B = 1)
    (u v : ι → V) (huv : ∀ i, u i = ∑ j, B i j • v j) (c : ι) : v c = ∑ i, A c i • u i := by
  simp_rw [huv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply]
  simp

end GlobalTheory.TensorKFinite


open GlobalTheory.TensorKFinite in
theorem GlobalTheory.tensor_decomposition_kfinite : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  intro hKS k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hRσ, hRT, -, hRK, -, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε mu R hR
  have hIT : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hIK : ∀ I, ∀ v, (RI I).KFin v → v ∈ (RI I).sm := fun I v hv =>
    hIT I v ((GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.2.2.1 v hv)
  have hRK' : ∀ v, R.KFin v → v ∈ R.sm := fun v hv => hRT v (hRK v hv)
  obtain ⟨-, -, h1, hmul, -⟩ := hF
  have hinv : ∀ g ∈ GG k r, ρ g⁻¹ * ρ g = 1 ∧ ρ g * ρ g⁻¹ = 1 := fun g hg => by
    obtain ⟨a, b, c⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    exact ⟨by rw [← hmul _ a _ hg, c, h1], by rw [← hmul _ hg _ a, b, h1]⟩
  have ioB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      io I c ((RI I).σ g y) = ∑ i, ρ g c i • R.σ g (io I i y) := fun I g hg c y hy =>
    congrFun (hT.io_eq I g hg y hy) c
  have ioA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      R.σ g (io I c y) = ∑ i, ρ g⁻¹ c i • io I i ((RI I).σ g y) := fun I g hg c y hy =>
    inv_rows _ _ (hinv g hg).1 (fun i => io I i ((RI I).σ g y)) (fun i => R.σ g (io I i y))
      (fun i => ioB I g hg i y hy) c
  have prA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      (RI I).σ g (pr I c x) = ∑ i, (ρ g)ᵀ c i • pr I i (R.σ g x) := fun I g hg c x hx => by
    have hs : ∀ e, (Pi.single c x : ι → R.H) e ∈ R.sm := fun e => by
      by_cases he : e = c
      · subst he; simpa using hx
      · rw [Pi.single_eq_of_ne he]; exact R.smSub.zero_mem
    have h := hT.pr_eq I g hg (Pi.single c x) hs
    have e1 : ∑ e, pr I e ((Pi.single c x : ι → R.H) e) = pr I c x := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        rw [Pi.single_eq_of_ne he, smMap_zero (hT.pr_sm I e)]
      · simp
    have e2 : ∀ i, act ρ R g (Pi.single c x) i = ρ g i c • R.σ g x := fun i => by
      unfold act
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        simp [Pi.single_eq_of_ne he]
      · simp
    rw [e1] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, (hT.pr_sm I i).smul _ _ (hRσ g hg x hx), Matrix.transpose_apply]
  have prB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      pr I c (R.σ g x) = ∑ i, (ρ g⁻¹)ᵀ c i • (RI I).σ g (pr I i x) := fun I g hg c x hx =>
    inv_rows _ _ (by rw [← Matrix.transpose_mul, (hinv g hg).2, Matrix.transpose_one])
      (fun i => (RI I).σ g (pr I i x)) (fun i => pr I i (R.σ g x)) (fun i => prA I g hg i x hx) c
  have K1 : ∀ I c y, (RI I).KFin y → R.KFin (io I c y) := fun I =>
    kfin_of_family (io I) (hT.io_sm I) (hIK I) fun g hg c y hy => ⟨_, ioA I g hg c y hy⟩
  have K2 : ∀ I c x, R.KFin x → (RI I).KFin (pr I c x) := fun I =>
    kfin_of_family (pr I) (hT.pr_sm I) hRK' fun g hg c y hy => ⟨_, prA I g hg c y hy⟩
  exact ⟨K1, K2,
    fun I => tk_of_family (io I) (hT.io_sm I) (hIK I) (hIT I) (K1 I) fun g hg c y hy => ⟨_, ioB I g hg c y hy⟩,
    fun I => tk_of_family (pr I) (hT.pr_sm I) hRK' hRT (K2 I) fun g hg c y hy => ⟨_, prB I g hg c y hy⟩⟩
end
end

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.JetAlg

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_sub_one_lt {y : ℂ_[p]} {k : ℕ} (h : y ^ p ^ k = 1) : ‖y - 1‖ < 1 := by
  apply GlobalTheory.MomOne.ShiftComp.norm_sub_one_lt_of_root <;> assumption

theorem bd_derivative {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (PowerSeries.derivative f) := by
  intro n
  rw [coeff_derivative, norm_mul]
  refine mul_le_one₀ (hf _) (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  simpa using this

theorem bd_DT {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (DT f) := by
  have h := bd_derivative hf
  intro n
  rw [DT, add_mul, one_mul, map_add (f := _)]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h n) ?_)
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul]; exact h n

theorem bd_iterate {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (DT^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact bd_DT ih

theorem differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

theorem differentiable_W1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (W1 d x F) := by
  have := differentiable_U1 d x hF
  unfold W1
  fun_prop

end GlobalTheory.MomOne.JetAlg

namespace GlobalTheory.MomOne
open JetAlg

theorem jets_algebraic : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsTh d θ → δ ≠ 0 → (∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ) → ∀ (ι : ℂ ≃+* ℂ_[q]) (t y : ℂ) (n s k : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y → δ⁻¹ ^ k * iteratedDeriv k (W1 d y (U1 d t θ)) 0 ∈ algebraicClosure ℚ ℂ := by
  intro d q hq δ θ hd hd16 hsp hθ hδ hL ι t y n s k hs ht hy
  refine mem_algebraicClosure_of_norm_le q ι _ 1 ?_
  intro ι' hι'
  obtain ⟨Ω, hΩ, h1', h2', -⟩ := hL ι'
  obtain ⟨hA, hB, -⟩ := okArith d q ι hd hd16 hsp
  have hy' : Good ι' d n s y := by
    obtain ⟨v, hv, hn, rfl⟩ := hy
    refine ⟨v, hv, ?_, rfl⟩
    have hc : InOK d (conj v) := (hA.2.2 v v hv hv).2.2.2
    have := hι' ⟨conj v, (hB _ hc).2.2⟩
    simp only at this
    rw [this]; exact hn
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exact absurd (by simpa using hs) hq.out.ne_one
    · exact h
  obtain ⟨hζ, hE⟩ := h2' t y n s hs ht hy'
  have hb := (Shift.shift_laws q _ (norm_sub_one_lt hζ)).1 _ _ (h1' t ⟨s, hs0, hs, ht⟩)
  rw [← hE] at hb
  have han : AnalyticAt ℂ (W1 d y (U1 d t θ)) 0 :=
    (differentiable_W1 d y (differentiable_U1 d t hθ.1)).analyticAt 0
  have hk := (hat_multiplicative_chart q ι' (Ω / ι' δ) _ han).2.1 k
  have hc := bd_iterate hb k 0
  rw [coeff_zero_eq_constantCoeff_apply, hk, div_eq_mul_inv, mul_pow, mul_assoc, norm_mul, norm_pow, hΩ,
    one_pow, one_mul] at hc
  rw [map_mul, map_pow, map_inv₀]
  exact hc

end GlobalTheory.MomOne
end
end

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TwistMom
open GlobalTheory.MomOne.Shift
variable {q : ℕ} [Fact q.Prime]

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  have h := PadicComplex.norm_extends' q (a : ℚ_[q])
  simpa [zc] using h

theorem zc_natCast (m : ℕ) : zc (m : ℤ_[q]) = (m : ℂ_[q]) := by simp [zc]

theorem continuous_zc : Continuous (zc : ℤ_[q] → ℂ_[q]) := by
  refine (Isometry.of_dist_eq fun a b => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← norm_zc]
  simp [zc]

theorem norm_sub_one_lt_of_root {ζ : ℂ_[q]} {n : ℕ} (h : ζ ^ (q ^ n) = 1) : ‖ζ - 1‖ < 1 := by
  apply GlobalTheory.MomOne.ShiftComp.norm_sub_one_lt_of_root <;> assumption

theorem continuous_redFun (r : ℕ) (g : ZMod (q ^ r) → ℂ_[q]) :
    Continuous fun a : ℤ_[q] => g (PadicInt.toZModPow r a) := by
  have hl : q.Prime := Fact.out
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := g (PadicInt.toZModPow r x))).congr ?_
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-(r : ℤ)) := zpow_pos (by exact_mod_cast hl.pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  rw [hy]

theorem hasSum_coeff_iter {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {S : ℂ_[q]⟦X⟧} (hS : Bdd S) (k : ℕ) :
    ∀ n, HasSum (fun m => coeff m S * coeff n (DT^[k] (sS ζ ^ m)))
      (coeff n (DT^[k] (shiftS ζ S))) := by
  obtain ⟨B, hB⟩ := hS
  induction k with
  | zero =>
    intro n
    simp only [Function.iterate_zero, id]
    rw [coeff_shiftS]
    exact (summable_term h hB n).hasSum
  | succ k ih =>
    intro n
    simp only [Function.iterate_succ_apply', coeff_DT]
    have := ((ih (n + 1)).mul_right ((n : ℂ_[q]) + 1)).add ((ih n).mul_right (n : ℂ_[q]))
    simpa only [mul_add, mul_assoc] using this

theorem DT_one_add_pow (c : ℂ_[q]) (j : ℕ) :
    DT (C c * (1 + X) ^ j) = C (c * j) * (1 + X) ^ j := by
  have hDT (f : ℂ_[q]⟦X⟧) : DT f = (1 + X) * PowerSeries.derivative f := by
    ext n
    rw [coeff_DT, add_mul, one_mul, map_add, coeff_derivative]
    cases n with
    | zero => simp
    | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp
  cases j with
  | zero => simp [hDT]
  | succ j =>
    have hd : PowerSeries.derivative (1 + X : ℂ_[q]⟦X⟧) = 1 := by
      rw [map_add, derivative_one, derivative_X, zero_add]
    rw [hDT, Derivation.leibniz]
    simp only [derivative_C, smul_eq_mul]
    rw [derivative_pow (1 + X : ℂ_[q]⟦X⟧) (j + 1), hd]
    simp only [Nat.add_sub_cancel, mul_one, map_mul, map_natCast, pow_succ]
    ring

theorem DT_iter_sum (s : Finset ℕ) (c : ℕ → ℂ_[q]) (k : ℕ) :
    DT^[k] (∑ j ∈ s, C (c j) * (1 + X) ^ j) = ∑ j ∈ s, C (c j * (j : ℂ_[q]) ^ k) * (1 + X) ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum (f : ℕ → ℂ_[q]⟦X⟧) : DT (∑ j ∈ s, f j) = ∑ j ∈ s, DT (f j) := by
      ext n
      simp only [map_sum, coeff_DT, Finset.sum_mul, Finset.sum_add_distrib]
    rw [Function.iterate_succ_apply', ih, hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [DT_one_add_pow, pow_succ, mul_assoc]

theorem sS_pow_eq (ζ : ℂ_[q]) (m : ℕ) :
    sS ζ ^ m = ∑ j ∈ Finset.range (m + 1),
      C ((-1) ^ (m - j) * (m.choose j : ℂ_[q]) * ζ ^ j) * (1 + X) ^ j := by
  rw [sS, sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_pow]
  ring

theorem twisted_moments : ∀ (q : ℕ) [Fact q.Prime] (S : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (n k : ℕ), Bdd S → ζ ^ (q ^ n) = 1 → ∃ f : C(ℤ_[q], ℂ_[q]), (∀ a, f a = ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k) ∧ HasSum (fun m : ℕ => coeff m S * (fwdDiff (1 : ℤ_[q]))^[m] f 0) (constantCoeff (DT^[k] (shiftS ζ S))) := by
  intro q _ S ζ n k hS h
  have hζ := norm_sub_one_lt_of_root h
  refine ⟨⟨fun a => ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k,
    (continuous_redFun n fun x => ζ ^ x.val).mul (continuous_zc.pow k)⟩, fun _ => rfl, ?_⟩
  have := hasSum_coeff_iter hζ hS k 0
  rw [coeff_zero_eq_constantCoeff] at this
  convert this using 3 with m

  rw [fwdDiff_iter_eq_sum_shift, sS_pow_eq, DT_iter_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (0 : ℤ_[q]) + j • (1 : ℤ_[q]) = (j : ℤ_[q]) := by simp
  rw [e]
  simp only [ContinuousMap.coe_mk, map_natCast, ZMod.val_natCast, zc_natCast]
  rw [← pow_eq_pow_mod j h]
  simp
  ring

end GlobalTheory.MomOne.TwistMom
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RamChartCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts GlobalTheory.PowGerm GlobalTheory.HarmCopies
open Matrix

section Val

variable (T : CDVR) (e : ℕ)

theorem nval_nonneg_of_mem {x : T.Fr} (hx : x ∈ (algebraMap T.V T.Fr).range) : (0 : EReal) ≤ nval T.V e x := by
  obtain ⟨r, rfl⟩ := hx
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]; exact le_top
  rw [nval_of_ne hr]
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) r
  have h2 : valV T.V (algebraMap T.V T.Fr r) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  have h4 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by
    have : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by unfold vV; omega
    exact_mod_cast this
  exact_mod_cast div_nonneg h4 (Nat.cast_nonneg e)

theorem le_nval_int_comb {ι : Type} (s : Finset ι) (cf S : ι → T.Fr) (r : EReal)
    (hc : ∀ i, cf i ∈ (algebraMap T.V T.Fr).range) (hS : ∀ i, r ≤ nval T.V e (S i)) :
    r ≤ nval T.V e (∑ i ∈ s, cf i * S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nval_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min ?_ ih) (nval_add e _ _)
    rw [nval_mul]
    calc r = 0 + r := (zero_add r).symm
      _ ≤ _ := add_le_add (nval_nonneg_of_mem T e (hc a)) (hS a)

theorem isIntPS_iff {n d : ℕ} (f : Germ.PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : Germ.PS T.V n d, MvPowerSeries.map (algebraMap T.V T.Fr) g = f := by
  constructor
  · intro h
    choose g hg using h
    exact ⟨g, MvPowerSeries.ext fun m => hg m⟩
  · rintro ⟨g, rfl⟩ m
    exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem isIntPS_boxSer {n d : ℕ} (f : Fin n → Germ.PS T.Fr 1 d) (hf : ∀ b, IsIntPS T (f b)) :
    IsIntPS T (boxSer f) := by
  choose g hg using fun b => (isIntPS_iff T (f b)).1 (hf b)
  refine (isIntPS_iff T _).2 ⟨boxSer g, ?_⟩
  unfold boxSer
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← hg b, MvPowerSeries.rename_map]

end Val

section Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def colVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  ∑ mo ∈ P.support, P.coeff mo *
    ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1)

theorem chartVal_boxSer (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Fin n → Germ.PS T.Fr 1 (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : chartVal C k (boxSer f) P = colVal C k f P := by
  letI := io.toAlgebra
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv (E →+* ℂ) Dw.mult n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv _ _ n).surjective P
  unfold chartVal colVal
  rw [nabValN_boxSer T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 (const_eq_zero C.ch.gauge) k n f _ _
    (letterEquiv (E →+* ℂ) Dw.mult n) _ C.ch.uvec _ (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename (letterEquiv (E →+* ℂ) Dw.mult n) (fun mo =>
      ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))]
  refine Finset.sum_congr rfl fun mo _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hc : colM mo b = colOf (Finsupp.mapDomain (letterEquiv (E →+* ℂ) Dw.mult n) mo) b := by
    ext ℓ
    exact (Finsupp.mapDomain_apply_of_injective (letterEquiv (E →+* ℂ) Dw.mult n).injective mo (ℓ, b)).symm
  rw [hc]

theorem bound_all_iff_bound_prod (C : IntegralChartA3 Xo c T io y) (e k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) T.Fr)
    (r : EReal) :
    (∀ f : Germ.PS T.Fr n (chD C.ch), IsIntPS T f → r ≤ nval T.V e (chartVal C k f P)) ↔
      ∀ f : Fin n → Germ.PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → r ≤ nval T.V e (colVal C k f P) := by
  letI := io.toAlgebra
  constructor
  · intro h f hf
    rw [← chartVal_boxSer]
    exact h _ (isIntPS_boxSer T f hf)
  · intro h f hf
    obtain ⟨S, hS⟩ := exists_jet P.totalDegree f
    have h1 : chartVal C k f P = ∑ j : S, MvPowerSeries.coeff j.1 f *
        chartVal C k (MvPowerSeries.monomial j.1 1) P := by
      unfold chartVal
      rw [(nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).1 _ _ _ hS,
        (nabJet T.Fr _ _ C.ch.B T.Fr C.ch.h H.w0 k n _ _ _).2.1]
    rw [h1]
    refine le_nval_int_comb T e _ _ _ r (fun j => hf j.1) fun j => ?_
    rw [monomial_eq_boxSer, chartVal_boxSer]
    refine h _ fun b => (isIntPS_iff T _).2 ⟨∏ i, MvPowerSeries.X ((0 : Fin 1), i) ^ j.1 (b, i), ?_⟩
    simp only [map_prod, map_pow, MvPowerSeries.map_X]

end Values

section Lifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

end Lifts

end GlobalTheory.RamChartCmp
end
end
