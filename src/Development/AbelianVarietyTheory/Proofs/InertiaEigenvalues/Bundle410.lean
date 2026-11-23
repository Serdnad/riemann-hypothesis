module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle382
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDuality
public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle395
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle398
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.local_invariants_killed_alt : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  first | exact @GlobalTheory.NewPrime.LocInv.local_invariants_killed | exact GlobalTheory.NewPrime.LocInv.local_invariants_killed | (intros; apply GlobalTheory.NewPrime.LocInv.local_invariants_killed <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ExpImage.TaylorEps

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open Polynomial
open scoped Formalism.Per

section poly
variable (K : Type) [Field K] [CharZero K]

def logT (M : ℕ) : K[X] := ∑ k ∈ Finset.range M, C ((-1) ^ k * ((k + 1 : ℕ) : K)⁻¹) * X ^ (k + 1)

theorem logT_deriv (M : ℕ) : (1 + X) * derivative (logT K M) = 1 - (-X) ^ M := by
  induction M with
  | zero => simp [logT]
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have e : derivative (C ((-1) ^ M * ((M + 1 : ℕ) : K)⁻¹) * X ^ (M + 1) : K[X]) = (-X) ^ M := by
      rw [derivative_C_mul, derivative_X_pow, ← mul_assoc, ← C_mul, mul_assoc, inv_mul_cancel₀ h,
        mul_one, neg_pow (X : K[X])]
      simp
    rw [logT, Finset.sum_range_succ, derivative_add, e, mul_add, ← logT, ih]
    ring

theorem X_dvd_logT (M : ℕ) : X ∣ logT K M :=
  Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (dvd_pow_self _ k.succ_ne_zero) _

theorem expT_deriv (L : K[X]) (M : ℕ) :
    derivative (∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j) =
      derivative L * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have h' : ((M.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
    have e : (((M + 1).factorial : ℕ) : K)⁻¹ * ((M + 1 : ℕ) : K) = ((M.factorial : ℕ) : K)⁻¹ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
    rw [Finset.sum_range_succ, derivative_add, ih, Finset.sum_range_succ _ M, derivative_C_mul,
      derivative_pow, ← e, C_mul]
    simp only [Nat.add_sub_cancel]
    ring

theorem exp_log_dvd (M : ℕ) :
    X ^ M ∣ 1 + X - ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * logT K M ^ j := by
  rcases M with _ | M
  · simp
  set L := logT K (M + 1) with hL
  set D := 1 + X - ∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j with hD
  have h1 : X ^ M ∣ X * derivative D + derivative D - D := by
    have e : X * derivative D + derivative D - D = C ((M.factorial : K)⁻¹) * L ^ M +
        (-X) ^ (M + 1) * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
      have := logT_deriv K (M + 1)
      rw [← hL] at this
      rw [hD, derivative_sub, expT_deriv, Finset.sum_range_succ]
      simp only [derivative_add, derivative_one, derivative_X]
      linear_combination (-∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j) * this
    rw [e]
    refine dvd_add (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (X_dvd_logT K _) M) _)
      (Dvd.dvd.mul_right ?_ _)
    rw [neg_pow, pow_succ X]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have h0 : D.coeff 0 = 0 := by
    have hL0 : L.eval 0 = 0 := by
      rw [← coeff_zero_eq_eval_zero]; exact X_dvd_iff.1 (X_dvd_logT K _)
    rw [coeff_zero_eq_eval_zero, hD, Finset.sum_range_succ']
    simp [Polynomial.eval_finsetSum, hL0]
  rw [X_pow_dvd_iff] at h1 ⊢
  intro d
  induction d with
  | zero => exact fun _ => h0
  | succ d ih =>
    intro hd
    have a := ih (by omega)
    have b := h1 d (by omega)
    have c : (X * derivative D).coeff d = 0 := by
      rcases d with _ | d
      · simp
      · rw [coeff_X_mul, coeff_derivative, a, zero_mul]
    rw [coeff_sub, coeff_add, c, a, coeff_derivative, zero_add, sub_zero] at b
    exact (mul_eq_zero.1 b).resolve_right (by exact_mod_cast d.succ_ne_zero)

end poly

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem aeval_mem {x : P.R.BdR} (hx : x ∈ FilB P 0) (f : ℚ_[l][X]) : aeval x f ∈ FilB P 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact qB_mul_mem a (by simpa using FilB_pow hx n)

theorem io_eq (T : LocTied l P AI) (a : Ainf l) :
    T.eD (io AI a) = algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l a) := GlobalTheory.ThetaTie.eD_ιA T a

theorem mu_mem (T : LocTied l P AI) : io AI (mu AI.ε) ∈ FilB P 1 := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : io AI (mu AI.ε) - tD P ∈ FilB P ((2 : ℕ) : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T 2 _).2 ⟨_, GlobalTheory.ThetaTie.log_mu (GlobalTheory.ThetaTie.isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, io_eq]
  have := add_mem (FilB_anti (a := 1) (by norm_num) h) (tD_mem (P := P))
  simpa using this

theorem t_sub_log (T : LocTied l P AI) (M : ℕ) :
    tD P - aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) ∈ FilB P (M : ℤ) := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : (M.factorial : P.R.BdR) * tD P - ∑ k ∈ Finset.range M,
      (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : P.R.BdR) * io AI (mu AI.ε) ^ (k + 1) ∈
        FilB P (M : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T M _).2 ⟨(M.factorial : _root_.Formalism.Per.BdRp l) * y -
      algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) (∑ k ∈ Finset.range M,
        (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : _root_.Formalism.Per.AinfP l) *
          (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.tm AI.ε - 1)) ^ (k + 1)), ?_, ?_⟩
    · refine (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l M _).2 ?_
      rw [map_sub, GlobalTheory.ThetaTie.ev_alg, map_mul, map_natCast,
        GlobalTheory.CrisIncl.factorial_mul_ev l _ y (GlobalTheory.ThetaTie.isEps AI).1 hy M, sub_self]

    · simp only [map_sub, map_mul, map_natCast, map_sum, map_pow, map_neg, e, io_eq]
      simp only [map_one]
      simp only [aDp, mu, RingHom.comp_apply, map_sub, map_one]
  have h0 : ((M.factorial : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
  have := qB_mul_mem ((M.factorial : ℕ) : ℚ_[l])⁻¹ h
  convert this using 1

  rw [mul_sub, ← mul_assoc, ← map_natCast (qB P), ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul,
  logT, map_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ∣ M.factorial := Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk)
  have h1 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have e1 : ((k + 1 : ℕ) : ℚ_[l])⁻¹ =
      ((M.factorial : ℕ) : ℚ_[l])⁻¹ * ((M.factorial / (k + 1) : ℕ) : ℚ_[l]) := by
    rw [Nat.cast_div hk' h1]
    field_simp
  rw [map_mul, aeval_C, map_pow, aeval_X, e1]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

theorem eps_sub_exp (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (M : ℕ) : io AI (WittVector.teichmuller l AI.ε) -
      ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hm := mu_mem T
  have hm0 := FilB_anti (a := 0) (by norm_num) hm
  have hL := aeval_mem hm0 (logT ℚ_[l] M)
  have ht := FilB_anti (a := 0) (by norm_num) (tD_mem (P := P))
  have hd := t_sub_log T M
  obtain ⟨Q, hQ⟩ := exp_log_dvd ℚ_[l] M
  have h1 := congrArg (aeval (io AI (mu AI.ε))) hQ

  simp only [map_sub, map_add (f := _), map_one, aeval_X, map_sum, map_mul, aeval_C, map_pow] at h1
  have h2 := FilB_zero_mul (aeval_mem hm0 Q) (FilB_pow hm M)
  rw [mul_one, mul_comm, ← h1] at h2
  generalize aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) = L at hL hd h2
  have h3 : ∀ j : ℕ, tD P ^ j - L ^ j ∈ FilB P (M : ℤ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := add_mem (FilB_zero_mul ht ih)
        (FilB_zero_mul (x := L ^ j) (by simpa using FilB_pow hL j) hd)
      convert this using 1
      ring
  have h4 := Submodule.sum_mem (FilB P (M : ℤ)) (t := Finset.range M)
    fun j _ => qB_mul_mem ((j.factorial : ℚ_[l])⁻¹) (h3 j)
  have e : io AI (WittVector.teichmuller l AI.ε) = 1 + io AI (mu AI.ε) := by
    rw [mu, map_sub, map_one, add_sub_cancel]
  have := sub_mem h2 h4
  rw [e]
  convert this using 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.ExpImage.TaylorEps
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LtCharCont

open GlobalTheory.ExpImage Filter Topology Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (w : Om l) :
    oB P w ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om w
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem norm_th_le_of_mem_Lat {P : LocPrime l} {AI : LocAinf l P} (Θ : ThetaL P AI) {n : ℕ}
    {y : P.R.BdR} (hy : y ∈ Lat AI 1 n) : ‖Θ.θ y‖ ≤ ‖(l : ℚ_[l])‖ ^ n := by
  obtain ⟨a, ha⟩ := hy
  have hy0 : y ∈ FilB P 0 := Lat_mem_zero AI ⟨a, ha⟩
  have hi0 : io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := io_mem AI _
  have hd0 : y - io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := sub_mem hy0 hi0
  have h1 : Θ.θ (y - io AI (((l : ℕ) : Ainf l) ^ n * a)) = 0 :=
    (Θ.θ_ker _ hd0).2 (by simpa using ha)
  have h2 : Θ.θ y = Θ.θ (io AI (((l : ℕ) : Ainf l) ^ n * a)) := by
    have := Θ.θ_add _ hd0 _ hi0
    rw [sub_add_cancel, h1, zero_add] at this
    exact this
  have e : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    rw [map_mul, map_pow, map_natCast, map_pow, map_natCast]
  rw [h2, e, Θ.θ_mul _ (qB_mem _) _ (io_mem AI a), norm_mul]
  have e2 : qB P ((l : ℚ_[l]) ^ n) = oB P (algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)) :=
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR _
  rw [e2, Θ.θ_Om, PadicComplex.norm_extends]
  have e3 : ‖algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
    rw [← norm_pow]; exact PadicAlgCl.norm_extends (p := l) _
  rw [e3]
  have := Θ.θ_int a
  rw [← io_apply AI a] at this
  calc _ ≤ ‖(l : ℚ_[l])‖ ^ n * 1 := by gcongr
    _ = _ := mul_one _

theorem continuous_char_of_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → P.ιB x ∈ (P.PD K).Fil 1 →
    P.ιB x ∉ (P.PD K).Fil 2 → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ,
    (∀ g : ↥(GK K), P.actQ (g : GQ l) x =
      algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) →
    Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) := by
  intro l _ P AI T K x _hxu hx1 hx2 c hc
  let Θ := GlobalTheory.ThetaTie.thetaL T
  have hF : ∀ (a : ℤ) (y : P.R.BdR), y ∈ (P.PD K).Fil a ↔ y ∈ FilB P a := fun a y =>
    Set.ext_iff.1 (P.PD_Fil K (botExt l) a) y
  have hX1 : P.ιB x ∈ FilB P 1 := (hF 1 _).1 hx1
  have hX2 : P.ιB x ∉ FilB P 2 := fun h => hx2 ((hF 2 _).2 h)
  obtain ⟨s, hs, hts⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  have hb0 : s * P.ιB x ∈ FilB P 0 := by
    have := FilB_mul hs hX1
    simpa using this
  have hθb : Θ.θ (s * P.ιB x) ≠ 0 := by
    intro h0
    have h1 : s * P.ιB x ∈ FilB P 1 := (Θ.θ_ker _ hb0).1 h0
    apply hX2
    have := FilB_mul (tD_mem (P := P)) h1
    have e : tD P * (s * P.ιB x) = P.ιB x := by
      rw [← mul_assoc]
      change P.ιB P.tB * s * P.ιB x = P.ιB x
      rw [hts, one_mul]
    rw [e] at this
    simpa using this
  let cv : ↥(GK K) → Om l := fun g => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)
  let χv : ↥(GK K) → Om l := fun g => algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])
  let uv : ↥(GK K) → Om l := fun g => cv g * (χv g)⁻¹
  have hK0 : ∀ z : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B z) = oB P (z : Om l) := fun z =>
    GlobalTheory.LocIota.ιB_algebraMap_Kur P (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) z)
  have hqo : ∀ z : ℚ_[l], qB P z = oB P (algebraMap ℚ_[l] (Om l) z) := fun z =>
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z
  have hact : ∀ g : ↥(GK K), P.actQdR (g : GQ l) (s * P.ιB x) = oB P (uv g) * (s * P.ιB x) := by
    intro g
    have hX : P.actQdR (g : GQ l) (P.ιB x) = oB P (cv g) * P.ιB x := by
      rw [← ιB_act, hc g, map_mul, hK0]
    have ht := act_tD (P := P) (g : GQ l)
    have h1 : P.actQdR (g : GQ l) (tD P) * P.actQdR (g : GQ l) s = 1 := by
      rw [← map_mul]
      change P.actQdR (g : GQ l) (P.ιB P.tB * s) = 1
      rw [hts, map_one]
    have h2 : qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * qB P (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one]
    have hts' : tD P * s = 1 := hts
    rw [ht] at h1
    have hs' : P.actQdR (g : GQ l) s = qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s := by
      linear_combination (qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s) * h1
        - P.actQdR (g : GQ l) s * h2
        - (P.actQdR (g : GQ l) s * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹
            * qB P (P.χQ (g : GQ l) : ℚ_[l])) * hts'
    have hu : oB P (uv g) = oB P (cv g) * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ := by
      rw [hqo, map_inv₀]
      change oB P (cv g * (χv g)⁻¹) = _
      rw [map_mul]
    rw [map_mul, hs', hX, hu]
    ring
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hθpos : 0 < ‖Θ.θ (s * P.ιB x)‖ := norm_pos_iff.2 hθb
  have htv : Tendsto (fun g : ↥(GK K) => (g : GQ l)) (𝓝 1) (𝓝 1) := by
    simpa using continuous_subtype_val.tendsto (1 : ↥(GK K))
  have huv : Tendsto uv (𝓝 1) (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hθpos) hl
    have hev := (bounded_and_eventually_sub_mem_Lat l P AI T _ hb0 1 n).2
    filter_upwards [htv.eventually hev] with g hg
    rw [hact g] at hg
    have e : oB P (uv g) * (s * P.ιB x) - s * P.ιB x = oB P (uv g - 1) * (s * P.ιB x) := by
      rw [map_sub, map_one]; ring
    rw [e] at hg
    have h3 := norm_th_le_of_mem_Lat Θ hg
    rw [Θ.θ_mul _ (oB_mem T _) _ hb0, Θ.θ_Om, norm_mul, PadicComplex.norm_extends] at h3
    rw [dist_eq_norm]
    have h4 : ‖uv g - 1‖ * ‖Θ.θ (s * P.ιB x)‖ < ε * ‖Θ.θ (s * P.ιB x)‖ := h3.trans_lt hn
    exact lt_of_mul_lt_mul_right h4 hθpos.le
  have hqc : Continuous (algebraMap ℚ_[l] (Om l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (Om l))
      (fun z => PadicAlgCl.norm_extends (p := l) z)).continuous
  have hχ : Tendsto χv (𝓝 1) (𝓝 1) := by
    have hcont : Continuous χv :=
      hqc.comp ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
    simpa [χv] using hcont.tendsto 1
  have hcv1 : Tendsto cv (𝓝 1) (𝓝 1) := by
    have := huv.mul hχ
    rw [mul_one] at this
    refine this.congr fun g => ?_
    have hne : χv g ≠ 0 := by
      simp only [χv, ne_eq, map_eq_zero]
      exact Units.ne_zero _
    exact inv_mul_cancel_right₀ hne (cv g)
  have hmul : ∀ g h : ↥(GK K), cv (g * h) = cv g * cv h := by
    intro g h
    simp [cv, map_mul]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have t1 : Tendsto (fun g : ↥(GK K) => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_const_mul g₀⁻¹).tendsto g₀
  have t2 := (hcv1.comp t1).const_mul (cv g₀)
  rw [mul_one] at t2
  refine t2.congr fun g => ?_
  change cv g₀ * cv (g₀⁻¹ * g) = cv g
  rw [← hmul, mul_inv_cancel_left]

end GlobalTheory.LtCharCont
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  first | exact @GlobalTheory.CuspGeneric.good_of_isCuspForm | exact GlobalTheory.CuspGeneric.good_of_isCuspForm | (intros; apply GlobalTheory.CuspGeneric.good_of_isCuspForm <;> assumption)
end

section

open NumberField Matrix GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.iteratedColumnTransform_eq_globalWhittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  first | exact @GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | exact GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | (intros; apply GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.columnWhittakerTransform_keeps_later_law : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ k, m + 1 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  first | exact @GlobalTheory.CuspGeneric.colT_law_of_good | exact GlobalTheory.CuspGeneric.colT_law_of_good | (intros; apply GlobalTheory.CuspGeneric.colT_law_of_good <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ), (∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) → ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  first | exact @GlobalTheory.CuspGeneric.tri_law | exact GlobalTheory.CuspGeneric.tri_law | (intros; apply GlobalTheory.CuspGeneric.tri_law <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published

namespace GlobalTheory.HeckeAboveBridge

theorem heckeLAdicCharacterAbove_of_potSemistable :
    HeckeLAdicCharacterDeRham → HeckeLAdicCharacterCrystalline → DeRhamPotSemistable →
      HeckeLAdicCharacterAbove := by
  intro hdR hcr hpst
  rw [heckeLAdicCharacterAbove_iff]
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hl w A hA O _ _ _ Bw hB
  have h1 := hdR E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB
  exact ⟨h1.1, GlobalTheory.PotCrysRankOne.isPotCrystalline_of_deRham_character hpst E Ω l P AI hT μ hμ A O Bw hB h1.1,
    hcr E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB, h1.2⟩

end GlobalTheory.HeckeAboveBridge

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.IntegralDuality (P.PD K) → bkBCore (P.PD K) := by
  first | exact @GlobalTheory.BKIntDescent.bkBCore_of_integralDuality | exact GlobalTheory.BKIntDescent.bkBCore_of_integralDuality | (intros; apply GlobalTheory.BKIntDescent.bkBCore_of_integralDuality <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.tateFinitenessAll_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.FinAll D := by
  first | exact @GlobalTheory.finAll_of_localTateDuality | exact GlobalTheory.finAll_of_localTateDuality | (intros; apply GlobalTheory.finAll_of_localTateDuality <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_detecting_characters_congr_filtration : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → ℂ_[l]) (a : ι → ↥(GK K) → ℤ_[l]), (∀ i, ∀ σ ∈ N k, ‖Formalism.Per.σC (σ : GQ l) (x i) - x i - algebraMap ℚ_[l] ℂ_[l] (a i σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ ∈ N k, (∀ i, (l : ℤ_[l]) ^ r ∣ a i σ) → σ ∈ N (k + r) := by
  first | exact @GlobalTheory.congrFiltration_detectingCharacters_coboundary | exact GlobalTheory.congrFiltration_detectingCharacters_coboundary | (intros; apply GlobalTheory.congrFiltration_detectingCharacters_coboundary <;> assumption)
end
