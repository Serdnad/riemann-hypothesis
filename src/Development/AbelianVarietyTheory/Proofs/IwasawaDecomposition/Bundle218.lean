module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem lamS_succ_lt (R : Ranks) (P : HCParam R) (i j : Fin R.r) (hij : j.val = i.val + 1) :
    lamS R P j < lamS R P i := by
  have hk : R.m + 3 ≤ R.k := R.m_add_three_le_k
  have hm : 2 ≤ R.m := R.two_le_m
  have hjr : j.val < R.k + R.m - 1 := j.isLt
  have hu : ∀ a b : Fin R.k, a.val = b.val → P.u a = P.u b := fun a b h => by rw [Fin.ext h]
  have hb : ∀ a b : Fin R.m, a.val = b.val → P.b a = P.b b := fun a b h => by rw [Fin.ext h]
  unfold Formalism.MainNotions.S.lamS
  by_cases hj : j.val < R.k - 1
  · have hi : i.val < R.k - 1 := by omega
    rw [dite_eq_left hj, dite_eq_left hi]
    have key : P.v ⟨j.val, hj⟩ < P.v ⟨i.val, hi⟩ :=
      calc P.v ⟨j.val, hj⟩ < P.u ⟨j.val, by omega⟩ := P.u_gt_v ⟨j.val, hj⟩
        _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp [hij])
        _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
    exact_mod_cast key
  · by_cases hi : i.val < R.k - 1
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      rw [dite_eq_right hj, dite_eq_left hj0, dite_eq_left hi]
      have key : -P.b ⟨j.val - (R.k - 1), hj0⟩ < P.v ⟨i.val, hi⟩ :=
        calc -P.b ⟨j.val - (R.k - 1), hj0⟩ = -P.b ⟨0, by omega⟩ :=
            congrArg (fun x => -x) (hb _ _ (show j.val - (R.k - 1) = 0 by omega))
          _ < P.u ⟨R.k - 1, by omega⟩ := P.u_last_gt (by omega) (by omega)
          _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp; omega)
          _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
      have := (Rat.cast_lt (K := ℝ)).mpr key
      push_cast at this
      exact this
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      have hi0 : i.val - (R.k - 1) < R.m := by omega
      have hi1 : i.val - (R.k - 1) + 1 < R.m := by omega
      rw [dite_eq_right hj, dite_eq_left hj0, dite_eq_right hi, dite_eq_left hi0]
      have h1 := P.gap_be ⟨i.val - (R.k - 1), hi0⟩
      have h2 := P.gap_eb ⟨i.val - (R.k - 1), hi0⟩ hi1
      have h3 : P.b ⟨i.val - (R.k - 1) + 1, hi1⟩ = P.b ⟨j.val - (R.k - 1), hj0⟩ := hb _ _ (by simp; omega)
      have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
      have key : P.b ⟨i.val - (R.k - 1), hi0⟩ < P.b ⟨j.val - (R.k - 1), hj0⟩ := by
        rw [← h3]; linarith
      have := (Rat.cast_lt (K := ℝ)).mpr key
      linarith

theorem lamS_int (R : Ranks) (P : HCParam R) (i : Fin R.r) : ∃ z : ℤ, lamS R P i = (z : ℝ) := by
  unfold Formalism.MainNotions.S.lamS
  split_ifs with h h'
  · obtain ⟨z, hz⟩ := P.v_int ⟨i.val, h⟩
    exact ⟨z, by rw [hz, Rat.cast_intCast]⟩
  · obtain ⟨z, hz⟩ := P.b_int ⟨i.val - (R.k - 1), h'⟩
    exact ⟨-z, by rw [hz, Rat.cast_intCast]; push_cast; ring⟩
  · exact ⟨0, by simp⟩

theorem lamSH_isHCParam (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (lamSH R P) := by
  refine ⟨?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact lamS_succ_lt R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) (Fin.castSucc i))
      (Fin.cast (Formalism.MainNotions.S.dimS_eq R) i.succ) (by simp)
  · intro a
    obtain ⟨z, hz⟩ := lamS_int R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a)
    obtain ⟨w, hw⟩ := R.k_even
    have hk : (R.k : ℝ) = 2 * w := by rw [hw]; push_cast; ring
    refine ⟨z - R.rS - w, ?_⟩
    show lamS R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a) - _ = _
    rw [hz]
    push_cast
    rw [hk]
    ring

theorem fdegHC_pos_of_injective {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  apply GlobalTheory.BesselNorm.fdegHC_pos <;> assumption

theorem lamSH_isHCParam_and_trueDsig_pos :
    ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  intro R P
  refine ⟨lamSH_isHCParam R P, ?_⟩
  exact fdegHC_pos_of_injective _ (lamSH_isHCParam R P).1.injective

end GlobalTheory.Mem.Vol
end

section

namespace GlobalTheory.PrimeInHeightOneSpectrum

theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by
  apply GlobalTheory.PlaceInt.LocBasis.exists_prime_mem <;> assumption

theorem exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)

theorem target : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v :=
  fun v => exists_prime_mem_heightOneSpectrum v

end GlobalTheory.PrimeInHeightOneSpectrum
end

section

open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.PoinLen

theorem mem_castLE_iff {n a : ℕ} (ha : a ≤ n) (k : Fin n) :
    k ∈ Finset.univ.map (Fin.castLEEmb ha) ↔ k.val < a := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 h
    simp
  · intro h
    exact Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem gnorm_poincareGram_single {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) :
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a z) (Pi.single k 1) =
      √(if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (z k) ^ 2)) else 1 / 2) := by
  rw [GlobalTheory.HermFrame.gnorm, GlobalTheory.HermFrame.form_single, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram, diagonal_apply_eq]
  simp only [Complex.ofReal_re]

theorem sqrt_two_mul_pi_le : √(2 * Real.pi ^ 2) ≤ 5 := by
  rw [show (5:ℝ) = √(5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

theorem gnorm_mul_poinWt_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
    v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n,
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) *
      GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  intro n a ha ρ hρ v hv k
  rw [gnorm_poincareGram_single, GlobalTheory.GoodMetric.poinWt]
  by_cases hk : k.val < a
  · rw [if_pos hk, if_pos ((mem_castLE_iff ha k).2 hk)]
    have h0 : v.ofLp k ≠ 0 := by
      have := hv.2 ⟨k.val, hk⟩
      simpa [Fin.castLE] using this
    have h1 : ‖v.ofLp k‖ < 1 := lt_of_lt_of_le (hv.1 k) (by linarith)
    have ht := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos h0 h1
    have hx : 0 < ‖v.ofLp k‖ := norm_pos_iff.2 h0
    have hlog : |Real.log ‖v.ofLp k‖| = 2 * Real.pi * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) := by
      rw [abs_of_neg (Real.log_neg hx h1), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
      field_simp
    change √(1 / (2 * (‖v.ofLp k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) ^ 2))) *
      (‖v.ofLp k‖ * |Real.log ‖v.ofLp k‖|) ≤ 5
    rw [hlog]
    set x := ‖v.ofLp k‖
    set t := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k)
    have hB : 0 ≤ x * (2 * Real.pi * t) := by positivity
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (by positivity)]
    convert sqrt_two_mul_pi_le using 2
    field_simp
  · rw [if_neg hk, if_neg (fun h => hk ((mem_castLE_iff ha k).1 h)), mul_one]
    calc √(1 / 2 : ℝ) ≤ √1 := Real.sqrt_le_sqrt (by norm_num)
      _ ≤ 5 := by rw [Real.sqrt_one]; norm_num

end GlobalTheory.PoinLen
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

variable {D : D7}

def lift {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S)) (𝓕 : Set (GA D S))
    (Φ : GA D S → WO S T → ℂ) : GA D T → ℂ :=
  fun g => ∫ h in 𝓕, thetaKO om h g (Φ h) ∂ν

def along (S T : HSp D) (ξ : Fin T.rank → D.host.E) (a : Fin S.rank → AE D) : WO S T :=
  Matrix.vecMulVec (fun i => incA D (ξ i)) a


open Classical in
def KEquiv (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) : Prop :=
  ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (e : ∀ τ', lowT M τ') (w : lowT M τ),
    ((w : M.sm τ) : M.H τ) = M.σ τ k ((e τ : M.sm τ) : M.H τ) →
      U (Function.update e τ w) = rTr V (atTau θ V τ ((M.fr τ)⁻¹ * k * M.fr τ)) (U e)

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem eq_top_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (τ : D.what₂.Tau) (N : Submodule ℂ (lowT M τ))
    (v : lowT M τ) (hv : v ≠ 0)
    (hN : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ u : lowT M τ,
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v : M.sm τ) : M.H τ) → u ∈ N) : N = ⊤ := by
  have hU := (M.ds τ).2.2.1
  let P : Submodule ℂ (M.H τ) := Submodule.span ℂ {y | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), y = M.σ τ k ((v : M.sm τ) : M.H τ)}
  have hvL : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := v.2
  have hPle : P ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact (h2 τ).2.1 k hk _ hvL)
  have hmul : ∀ a ∈ Formalism.REAL.Kset (M.ε τ), ∀ b ∈ Formalism.REAL.Kset (M.ε τ), a * b ∈ Formalism.REAL.Kset (M.ε τ) := by
    intro a ha b hb
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hone : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := ⟨one_mem _, by simp⟩
  have hst : IsKStableOn (M.ε τ) (M.σ τ) P := by
    intro g hg y hy
    refine Submodule.span_induction (p := fun y _ => M.σ τ g y ∈ P) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨k, hk, rfl⟩
      refine Submodule.subset_span ⟨g * k, hmul g hg k hk, ?_⟩
      rw [hU.1.2 _ (kset_uj hg) _ (kset_uj hk)]
      rfl
    · rw [map_zero]; exact P.zero_mem
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact P.add_mem hx hy
    · intro a x _ hx; rw [map_smul]; exact P.smul_mem a hx
  have hP : P = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
    refine ((h2 τ).2.2.1 P hPle hst).resolve_left fun h0 => hv ?_
    have : M.σ τ 1 ((v : M.sm τ) : M.H τ) ∈ P := Submodule.subset_span ⟨1, hone, rfl⟩
    rw [h0, hU.1.1] at this
    exact Subtype.ext (Subtype.ext this)
  rw [eq_top_iff]
  intro u _
  have hu : ((u : M.sm τ) : M.H τ) ∈ P := hP ▸ u.2
  have key : ∀ y (hy : y ∈ P), (⟨⟨y, h1 τ (hPle hy)⟩, hPle hy⟩ : lowT M τ) ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, e⟩ := hy
      exact hN k hk _ e
    | zero => exact N.zero_mem
    | add x y _ _ hx hy => exact N.add_mem hx hy
    | smul a x _ hx => exact N.smul_mem a hx
  exact key _ hu


open Classical in
theorem mem_of_translates (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (B : MultilinearMap (RingHom.id ℂ) (fun τ => lowT M τ) Y) (N : Submodule ℂ Y) (v₀ : ∀ τ, lowT M τ) (h0 : ∀ τ, v₀ τ ≠ 0)
    (hB : B v₀ ∈ N)
    (hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → B v ∈ N → B (Function.update v τ u) ∈ N)
    (v : ∀ τ, lowT M τ) : B v ∈ N := by
  have key : ∀ s : Finset D.what₂.Tau, B (s.piecewise v v₀) ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hB
    | insert τ s hτ ih =>
      have e0 : s.piecewise v v₀ τ = v₀ τ := Finset.piecewise_eq_of_notMem _ _ _ hτ
      have := eq_top_of_translates h1 h2 τ (N.comap (B.toLinearMap (s.piecewise v v₀) τ)) (v₀ τ) (h0 τ)
        fun k hk u hu => hK τ k hk _ u (by rw [e0]; exact hu) ih
      rw [Finset.piecewise_insert]
      exact (this.ge Submodule.mem_top : v τ ∈ N.comap (B.toLinearMap (s.piecewise v v₀) τ))
  simpa using key Finset.univ

end GlobalTheory.DefLift

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_concretePeriodDatum_padicFiniteExtension : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l), ∃ PD, IsRealPD C K PD := by
  first | exact @GlobalTheory.MemLoc.PdEx.exists_realPD | exact GlobalTheory.MemLoc.PdEx.exists_realPD | (intros; apply GlobalTheory.MemLoc.PdEx.exists_realPD <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix

namespace GlobalTheory.GoodMetric

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]


omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem contDiffAt_aeval_int {σ : Type} {k : WithTop ℕ∞} {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ k (fun x => f x s) z) (P : MvPolynomial σ ℤ) :
    ContDiffAt ℝ k (fun x => aeval (f x) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, aeval_X]; exact hp.mul (hf s)

theorem del_aeval_int {σ : Type} [Fintype σ] {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ 1 (fun x => f x s) z) (P : MvPolynomial σ ℤ) (ξ : E) :
    del (fun x => aeval (f x) P) z ξ = ∑ s, aeval (f z) (pderiv s P) * del (fun x => f x s) z ξ := by
  classical
  have hd : ∀ Q : MvPolynomial σ ℤ, DifferentiableAt ℝ (fun x => aeval (f x) Q) z :=
    fun Q => (contDiffAt_aeval_int hf Q).differentiableAt one_ne_zero
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, pderiv_C, del_const]; simp
  | add p q hp hq =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    rw [del_add (hd p) (hd q)]; rfl
  | mul_X p s hp =>
    simp only [map_mul, aeval_X]
    rw [del_mul (hd p) ((hf s).differentiableAt one_ne_zero), hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), map_mul, aeval_X, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, Pi.single_apply]
    congr 1
    · rw [Finset.sum_eq_single s] <;> simp +contextual [eq_comm]
    · exact Finset.sum_congr rfl fun _ _ => by ring

variable {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m)

theorem PolyRep.conn_ev {G : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => G w τ) u)
    (hu : ∀ τ, (G u τ).det ≠ 0) (ξ : E) :
    conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  set B : Mat m ℂ := (fun τ => (G u τ)ᵀ)⁻¹ with hB
  have hBu : B * (fun τ => (G u τ)ᵀ) = 1 := Mat.inv_mul fun τ => by rw [Matrix.det_transpose]; exact hu τ
  have hev : ∀ w, ρ.ev (B * fun τ => (G w τ)ᵀ) = ρ.ev B * (ρ.ev (G w))ᵀ := fun w => by
    rw [PolyRep.ev, ρ.mul, ρ.transp]; rfl
  have hinv : (ρ.ev (G u))ᵀ⁻¹ = ρ.ev B :=
    Matrix.inv_eq_left_inv (by rw [← hev, hBu]; exact ρ.one ℂ)
  have hρ : MContDiffAt 1 (fun w => ρ.ev (G w)) u := fun i j =>
    contDiffAt_aeval_int (f := fun w (v : EntIx m) => G w v.1 v.2.1 v.2.2) (fun v => h v.1 v.2.1 v.2.2) _
  have hK : ∀ τ, MContDiffAt 1 (fun w => B τ * (G w τ)ᵀ) u := fun τ =>
    (mContDiffAt_const _).mul (h τ).transpose
  have e1 : conn (fun w => ρ.ev (G w)) u ξ = mdel (fun w => ρ.ev (B * fun τ => (G w τ)ᵀ)) u ξ := by
    simp only [hev]
    rw [mdel_mul (mContDiffAt_const _) hρ.transpose, mdel_const, Matrix.zero_mul, add_zero, conn, hinv]
    rfl
  have e2 : ∀ τ, conn (fun w => G w τ) u ξ = mdel (fun w => B τ * (G w τ)ᵀ) u ξ := fun τ => by
    rw [mdel_mul (mContDiffAt_const _) (h τ).transpose, mdel_const, Matrix.zero_mul, add_zero, conn]
    rfl
  rw [e1]
  simp only [e2]
  ext i j
  refine (del_aeval_int (f := fun w (v : EntIx m) => (B * fun τ => (G w τ)ᵀ : Mat m ℂ) v.1 v.2.1 v.2.2)
    (fun v => hK v.1 v.2.1 v.2.2) (ρ.ent i j) ξ).trans ?_
  rw [hBu]
  rfl

theorem PolyRep.mdbar_lie {A : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => A w τ) u) (η : E) :
    mdbar (fun w => ρ.lie (A w)) u η = ρ.lie (fun τ => mdbar (fun w => A w τ) u η) := by
  ext i j
  simp only [mdbar_apply, PolyRep.lie, Matrix.of_apply]
  rw [dbar_sum fun v _ => (differentiableAt_const _).fun_mul ((h v.1).diff v.2.1 v.2.2),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h v.1).diff v.2.1 v.2.2)]
  simp

theorem PolyRep.eventually_conn_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) :
    ∀ᶠ u in 𝓝 v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  filter_upwards [eventually_all.2 fun τ => (h τ).eventually_two,
    eventually_all.2 fun τ => (h τ).eventually_isUnit (hv τ).isUnit] with u h1 h2 ξ
  exact ρ.conn_ev (fun τ => (h1 τ).of_le one_le_two) (fun τ => (h2 τ).ne_zero) ξ

theorem PolyRep.curv_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) (ξ η : E) :
    curv (fun w => ρ.ev (G w)) v ξ η = ρ.lie (fun τ => curv (fun w => G w τ) v ξ η) := by
  rw [curv, mdbar_congr ((ρ.eventually_conn_ev h hv).mono fun u hu => hu ξ),
    ρ.mdbar_lie (A := fun u τ => conn (fun w => G w τ) u ξ)
      (fun τ => (h τ).conn (hv τ).isUnit (by norm_num) ξ)]
  ext i j
  simp [PolyRep.lie, curv]

end General

theorem PolyRep.lie_sum_C_mul_X {ι κ : Type} [Fintype ι] [Fintype κ] {m : ι → ℕ} (ρ : PolyRep m)
    (F : κ → κ → Mat m ℂ) :
    (Matrix.of fun i j => ∑ a, ∑ b, C (ρ.lie (F a b) i j) * X (a, b) : Matrix _ _ (MvPolynomial (κ × κ) ℂ)) =
      ρ.lie fun τ => Matrix.of fun i j => ∑ a, ∑ b, C (F a b τ i j) * X (a, b) := by
  have hc : ∀ (S : Type) [CommRing S] (φ : ℂ →+* S) (P : MvPolynomial (EntIx m) ℤ),
      aeval (fun w : EntIx m => (1 : Mat m S) w.1 w.2.1 w.2.2) P =
        φ (aeval (fun w : EntIx m => (1 : Mat m ℂ) w.1 w.2.1 w.2.2) P) := fun S _ φ P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [aeval_C, aeval_C, eq_intCast, eq_intCast, map_intCast]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, Pi.one_apply, Pi.one_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
  refine Matrix.ext fun i j => ?_
  have key : ∀ (c : EntIx m → ℂ) (f : κ → κ → EntIx m → ℂ),
      (∑ a, ∑ b, C (∑ v, c v * f a b v) * X (a, b) : MvPolynomial (κ × κ) ℂ) =
        ∑ v, C (c v) * ∑ a, ∑ b, C (f a b v) * X (a, b) := fun c f => by

    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [eq_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  simp only [PolyRep.lie, Matrix.of_apply]
  rw [key]
  exact Finset.sum_congr rfl fun v _ => by rw [hc _ C]

theorem conn_curvPoly_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n),
    (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) →
    (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧
      curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  intro ι _ m ρ n G v h hv
  refine ⟨ρ.eventually_conn_ev h hv, ?_⟩
  simp only [curvPoly, ρ.curv_ev h hv]
  exact ρ.lie_sum_C_mul_X fun a b τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)

end GlobalTheory.GoodMetric

end
end
