module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle721
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle749
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle748
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Formalism.PeriodIntegrals.Bundle019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.KisinFF

theorem exists_of_inclW_eq_pow_mul {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → ∃ a', a = (l : Ainf l) ^ n * a' ∧ inclW l a' = w := by
  induction n with
  | zero => intro a w h; exact ⟨a, by simp, by simpa using h⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨a', ha', hw'⟩ := ih a₁ w ha₁
    refine ⟨a', ?_, hw'⟩
    have h1 : a = (l : Ainf l) * a₁ := by
      apply GlobalTheory.HWL.TensorWitt.inclW_injective
      rw [map_mul, map_natCast, ha₁, h]; ring
    rw [h1, ha']; ring

theorem scalar {l : ℕ} [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (M : ℕ)
    (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : inclW l a = inclW l τ ^ M * w) :
    ∃ s : bk.S, bk.evW s = w := by
  classical
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB M
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  obtain ⟨v, -, hv⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : bk.S, s₀ = c.sum fun i μ => μ * TB.c i a := ⟨_, rfl⟩
  have hev : ∀ t : bk.S, inclW l (bk.ev t) = bk.evW t := fun t => rfl
  have key : ∀ n : ℕ, (l : WCb l) ^ n ∣ bk.evW s₀ - (l : WCb l) ^ r * w := by
    intro n
    obtain ⟨m, s, y, h⟩ := hw n
    have hz : inclW l (bk.ev X ^ m * a - τ ^ M * bk.ev s) = (l : WCb l) ^ n * (inclW l τ ^ M * y) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, hev, hev, ha]
      linear_combination (inclW l τ ^ M) * h
    obtain ⟨z', hz', -⟩ := exists_of_inclW_eq_pow_mul n _ _ hz
    have hci : ∀ i, X ^ m * TB.c i a - s * TB.c i (τ ^ M) = (l : bk.S) ^ n * TB.c i z' := by
      intro i
      have := congrArg (TB.c i) hz'
      rw [map_sub, show bk.ev X ^ m = bk.ev (X ^ m) from (map_pow _ _ _).symm, TB.c_mul, mul_comm (τ ^ M) (bk.ev s), TB.c_mul,
        show ((l : Ainf l) ^ n) = bk.ev ((l : bk.S) ^ n) by simp, TB.c_mul] at this
      exact this
    obtain ⟨t, ht⟩ : ∃ t : bk.S, t = c.sum fun i μ => μ * TB.c i z' := ⟨_, rfl⟩
    have hS : X ^ m * s₀ - s * (l : bk.S) ^ r = (l : bk.S) ^ n * t := by
      rw [← hc, hs₀, ht]
      simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by linear_combination c i * hci i
    have hW := congrArg bk.evW hS
    simp only [map_sub, map_mul, map_pow, map_natCast] at hW
    have hv' : bk.evW X ^ m * v ^ m = 1 := by rw [← mul_pow, hv, one_pow]
    refine ⟨v ^ m * (bk.evW t - (l : WCb l) ^ r * y), ?_⟩
    linear_combination v ^ m * hW - (l : WCb l) ^ r * v ^ m * h - (bk.evW s₀ - (l : WCb l) ^ r * w) * hv'
  have hd : bk.evW s₀ - (l : WCb l) ^ r * w = 0 := by
    refine IsHausdorff.haus' (I := Ideal.span {(l : WCb l)}) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact key n
  obtain ⟨a', -, ha'⟩ := exists_of_inclW_eq_pow_mul r (bk.ev s₀) w (by rw [hev]; linear_combination hd)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.integral_witt_element_of_evaluation l K bk w hw a' ha'.symm
  exact ⟨s', by rw [← hev, ← hs', ha']⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  intro l _ K bk τ hτ d d' M X x hX hx
  have he : ∀ i j, inclW l (x i j) = inclW l τ ^ M * X i j := fun i j => by
    have := congrFun (congrFun hx i) j
    simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
  choose Y hY using fun i j => scalar K bk τ hτ M (X i j) (hX i j) (x i j) (he i j)
  exact ⟨Y, Matrix.ext fun i j => hY i j⟩

end GlobalTheory.BSP.KisinFF
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem GlobalTheory.LimVec.invertible_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  intro l _ K bk d d' R h1 h2 h3
  have lnu : ¬ IsUnit ((l : ℕ) : WCb l) := by
    intro h
    obtain ⟨u, hu⟩ := h
    have h1 := congrArg (fun x : WCb l => x.coeff 0) u.mul_inv
    simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
    rw [hu, WittVector.coeff_p_zero, zero_mul] at h1
    exact zero_ne_one h1
  have evW_mem : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨hOEsat, ⟨wX, -, hwX⟩, -, hOEdec, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨-, hOEcl, -⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have cU : IsUnit (bk.evW X) := ⟨⟨_, wX, hwX, by rw [mul_comm]; exact hwX⟩, rfl⟩
  set π := Ideal.Quotient.mk (Ideal.span {((l : ℕ) : WCb l)}) with hπ
  have hdvd : ∀ x : WCb l, ((l : ℕ) : WCb l) ∣ x ↔ π x = 0 := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have πl : π ((l : ℕ) : WCb l) = 0 := (hdvd _).1 dvd_rfl
  have hdvd' : ∀ x y : WCb l, ((l : ℕ) : WCb l) ∣ x - y → π x = π y := fun x y h => by
    rw [← sub_eq_zero, ← map_sub]; exact (hdvd _).1 h
  obtain ⟨m, hm1, hm⟩ := h2 1
  obtain ⟨R', hR'OE, hRR'⟩ := h1 m
  choose k s y hk using fun a j => hR'OE a j 1
  set N := Finset.univ.sup (fun p : Fin (d' m) × Fin d => k p.1 p.2) with hN
  have hkN : ∀ a j, k a j ≤ N := fun a j =>
    Finset.le_sup (f := fun p : Fin (d' m) × Fin d => k p.1 p.2) (Finset.mem_univ (a, j))
  let σ : Fin (d' m) → Fin d → bk.S := fun a j => X ^ (N - k a j) * s a j
  have hσ : ∀ a j, π (bk.evW (σ a j)) = π (bk.evW X ^ N * R' a j) := by
    intro a j
    have e : bk.evW X ^ N * R' a j = bk.evW (σ a j) + (l : WCb l) * (bk.evW X ^ (N - k a j) * y a j) := by
      have hk' := hk a j
      rw [pow_one] at hk'
      have hp : bk.evW X ^ N = bk.evW X ^ (N - k a j) * bk.evW X ^ k a j := by
        rw [← pow_add, Nat.sub_add_cancel (hkN a j)]
      simp only [σ, map_mul, map_pow]
      rw [hp, mul_assoc, hk']
      ring
    rw [e, map_add (f := _), (hdvd _).1 (dvd_mul_right _ _), add_zero]
  choose v hv1 hvlim using fun j => hm (fun a => σ a j)
  let V : Matrix (Fin d) (Fin d) (WCb l) := Matrix.of fun i j => v j i
  have hVmem : ∀ i j, V i j ∈ bk.OE := by
    intro i j
    apply hOEcl
    intro n
    obtain ⟨s', hs'⟩ := hvlim j n
    refine ⟨(R n *ᵥ fun a => bk.evW (s' a)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (h3 n i a) (evW_mem _)
  have hπV : π.mapMatrix V = π (bk.evW X ^ N) • (1 : Matrix (Fin d) (Fin d) (WCb l ⧸ Ideal.span {((l : ℕ) : WCb l)})) := by
    ext i j
    have e1 := hdvd' _ _ (by simpa [pow_one] using hv1 j i)
    have e2 : π ((R m * R') i j) = π ((1 : Matrix (Fin d) (Fin d) (WCb l)) i j) :=
      hdvd' _ _ (dvd_trans (dvd_pow_self ((l : ℕ) : WCb l) (show m ≠ 0 by omega)) (by simpa [Matrix.sub_apply] using hRR' i j))
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, V, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [e1]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
    rw [Matrix.mul_apply] at e2

    rw [map_sum] at e2
    simp only [map_mul] at e2
    calc ∑ x, π (R m i x) * (π (bk.evW X ^ N) * π (R' x j)) = π (bk.evW X ^ N) * ∑ x, π (R m i x) * π (R' x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e2]
          by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hdet : π V.det = π ((bk.evW X ^ N) ^ d) := by
    rw [RingHom.map_det, hπV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    simp only [map_pow]
  have ndvd : ¬ ((l : ℕ) : WCb l) ∣ V.det := by
    intro h
    rw [hdvd, hdet, ← hdvd] at h
    obtain ⟨a, ha⟩ := h
    exact lnu (isUnit_of_mul_isUnit_left (ha ▸ (cU.pow N).pow d))
  let V0 : Matrix (Fin d) (Fin d) ↥bk.OE := Matrix.of fun i j => ⟨V i j, hVmem i j⟩
  have hV0 : bk.OE.subtype.mapMatrix V0 = V := by ext i j; rfl
  have hdetmem : V.det ∈ bk.OE := by
    rw [← hV0, ← RingHom.map_det]; exact (V0.det).2
  have hadj : ∀ i j, V.adjugate i j ∈ bk.OE := by
    intro i j
    rw [← hV0, ← RingHom.map_adjugate]; exact (V0.adjugate i j).2
  have hne : V.det ≠ 0 := fun h => ndvd (h ▸ dvd_zero _)
  obtain ⟨e, u, u', hu, hu', huu', hdec⟩ := hOEdec _ hdetmem hne
  have he : e = 0 := by
    by_contra he
    apply ndvd
    rw [hdec]
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero _)) _
  rw [he, pow_zero, one_mul] at hdec
  refine ⟨V, u' • V.adjugate, hVmem, fun i j => ?_, ?_, fun j k' => hvlim j k'⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ hu' (hadj i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, hdec, smul_smul, mul_comm, huu', one_smul]
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem invariant_phi_solution_approx (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (c : κ → κ → WCb l) (hc : ∀ i j, c i j ∈ bk.OE) (n : ℕ) :
    ∀ (x b : κ → WCb l), (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) →
      (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) →
      ∀ j, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ x j - v := by
  induction n with
  | zero => exact fun x b _ _ _ j => ⟨0, bk.OE.zero_mem, by simp⟩
  | succ n ih =>
    intro x b hb hx hg j
    obtain ⟨v, x', b', hv, hb', hxv, hx', hg'⟩ := GlobalTheory.T.ladic_descent_step_to_OE l K bk κ x b c hc hb hx hg
    obtain ⟨v', hv', y, hy⟩ := ih x' b' hb' hx' hg' j
    refine ⟨v j + ((l : ℕ) : WCb l) * v', bk.OE.add_mem (hv j) (bk.OE.mul_mem (natCast_mem bk.OE l) hv'), y, ?_⟩
    rw [hxv j]
    linear_combination ((l : ℕ) : WCb l) * hy

theorem invariant_phi_solution_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (x : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j) →
    (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∀ j, x j ∈ bk.OE := by
  intro l _ K bk κ _ x c hc hx hg j
  refine (GlobalTheory.T.breuilKisin_OE_stability_properties l K bk).2.1 (x j) fun n => ?_
  exact invariant_phi_solution_approx l K bk κ c hc n x (fun _ => 0) (fun _ => bk.OE.zero_mem)
    (fun j => by rw [add_zero]; exact hx j) hg j

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SatInvUnit

theorem perfectRing_tilt_fraction_field (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ l fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
  obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
  exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
    simp [frobenius_def, div_pow, map_pow]⟩

theorem constantCoeff_frobW (l : ℕ) [Fact l.Prime] (x : WCb l) :
    WittVector.constantCoeff (frobW l x) = frobenius (Cb l) l (WittVector.constantCoeff x) :=
  WittVector.map_coeff (frobenius (Cb l) l) x 0

theorem constantCoeff_galW (l : ℕ) [Fact l.Prime] (g : GQ l) (x : WCb l) :
    WittVector.constantCoeff (galW l g x) = autCb l (galTilt l g) (WittVector.constantCoeff x) :=
  WittVector.map_coeff (autCb l (galTilt l g)).toRingHom x 0

end GlobalTheory.SatInvUnit

namespace GlobalTheory.SatInvUnit

theorem isUnit_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (Y A : Matrix (Fin d) (Fin d) (WCb l)), Y.det ≠ 0 → (∀ i j, A i j ∈ bk.OE) → Y.map (frobW l) = Y * A →
    (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧ R * Y.map (galW l (g : GQ l)) = Y) →
    (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → (∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i) → ∀ i, ((l : ℕ) : WCb l) ∣ v i) →
    IsUnit Y := by
  intro l _ K bk d Y A hY hA hφ hg hsat
  haveI : PerfectRing (Cb l) l := perfectRing_tilt_fraction_field l
  set c : WCb l →+* Cb l := WittVector.constantCoeff (p := l) (R := Cb l) with hc

  have hdetA : IsUnit A.det := by
    obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y.det hY
    have h1 : frobW l Y.det = Y.det * A.det := by
      rw [← Matrix.det_mul, ← hφ]
      simpa using RingHom.map_det (frobW l).toRingHom Y
    have hlm : ((l : WCb l)) ^ m ≠ 0 := left_ne_zero_of_mul (hu ▸ hY)
    rw [hu, map_mul, map_pow, map_natCast, mul_assoc] at h1
    have h2 := mul_left_cancel₀ hlm h1
    have hfu : IsUnit (frobW l (u : WCb l)) := u.isUnit.map (frobW l)
    rw [h2] at hfu
    exact isUnit_of_mul_isUnit_right hfu
  have hcA : (A.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdetA.map c).ne_zero
  by_cases h0 : (Y.map c).det = 0
  · exfalso
    have hAm : ∀ i j, (A.map c) i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) :=
      fun i j => Subring.mem_map.2 ⟨A i j, hA i j, rfl⟩
    have hφ' : (Y.map c).map (frobenius (Cb l) l) = Y.map c * A.map c := by
      have : (Y.map (frobW l)).map c = (Y.map c).map (frobenius (Cb l) l) := by
        ext i j
        exact constantCoeff_frobW l (Y i j)
      rw [← this, hφ, Matrix.map_mul]
    have hg' : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧
        R * (Y.map c).map (autCb l (galTilt l (g : GQ l))) = Y.map c := by
      intro g hfix
      obtain ⟨R, hR, hRY⟩ := hg g hfix
      refine ⟨R.map c, hR.map c.mapMatrix, ?_⟩
      have : (Y.map (galW l (g : GQ l))).map c = (Y.map c).map (autCb l (galTilt l (g : GQ l))) := by
        ext i j
        exact constantCoeff_galW l (g : GQ l) (Y i j)
      rw [← this, ← Matrix.map_mul, hRY]
    obtain ⟨vb, hv0, hvm, hYv⟩ := GlobalTheory.T.exists_kernel_vector_mem_OE_of_frobenius_stable l K bk d (Y.map c) (A.map c) hcA hAm hφ' hg' h0
    choose v hv hvc using fun i => Subring.mem_map.1 (hvm i)
    have hdiv : ∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i := by
      intro i
      rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
      change c (Y.mulVec v i) = 0
      rw [RingHom.map_mulVec]
      have : (c ∘ v) = vb := funext fun j => hvc j
      rw [this, hYv]
      rfl
    apply hv0
    funext i
    obtain ⟨r, hr⟩ := hsat v hv hdiv i
    rw [← hvc i, hr, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
    rfl
  · have hu : IsUnit Y.det := by
      apply WittVector.isUnit_of_coeff_zero_ne_zero
      intro h
      apply h0
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact h
    exact (Matrix.isUnit_iff_isUnit_det Y).2 hu

end GlobalTheory.SatInvUnit
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mreal_hom_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f _ Y hY
  set L := bk.evW with hL
  set Φ : WCb l →+* WCb l := (frobW l).toRingHom with hΦ
  have hc : ∀ x, L (frobS l bk.a x) = Φ (L x) := by
    intro x
    simp only [hL, hΦ, BK.evW, RingHom.comp_apply, bk.ev_frob, AlgHom.coe_toRingHom]
    exact (frobW_inclW _).symm
  have hsm : ∀ {m n : Type} (c : bk.S) (M : Matrix m n bk.S), (c • M).map L = L c • M.map L := by
    intro m n c M; ext i j; simp [Matrix.map_apply, Matrix.smul_apply]
  have hTΦ : ∀ {m n : Type} (M : Matrix m n (WCb l)), M.map (frobW l) = M.map Φ := fun _ => rfl
  have hz : (zW f).map Φ = zW f := by
    ext i j; simp [zW, hΦ, Matrix.map_apply]
  have hYΦ : (Y.map (frobS l bk.a)).map L = (Y.map L).map Φ := by
    refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply]; exact hc _
  have φT := hT.φ
  have φT' := hT'.φ
  rw [hTΦ] at φT φT'
  have hYf : T'.map Φ * (Y.map L).map Φ = zW f * T.map Φ := by
    rw [← Matrix.map_mul, hY, Matrix.map_mul, hz]
  have key : T' * (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L =
      T' * (bk.E ^ S'.a • (Y * S.A)).map L := by
    rw [hsm, hsm, Matrix.map_mul, Matrix.map_mul, hYΦ, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← φT', map_pow, map_pow, Matrix.smul_mul, smul_smul, hYf, hY, Matrix.mul_assoc,
      ← φT, Matrix.mul_smul, smul_smul, mul_comm]
  obtain ⟨u, hu⟩ := hT'.unit
  have key2 : (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L = (bk.E ^ S'.a • (Y * S.A)).map L := by
    have := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) key
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    exact this
  have hinj := (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.1
  refine Matrix.ext fun i j => ?_
  exact hinj (congrFun (congrFun key2 i) j)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DivTransfer

theorem div_transfer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), aDp l (bk.ev bk.E) ≠ 0 ∧
    ∀ (m : ℕ) (s : bk.S), aDp l (bk.ev bk.E) ^ m ∣ aDp l (bk.ev s) → bk.E ^ m ∣ s := by
  intro l _ K bk

  have hF := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1
  have hS := fun m => (GlobalTheory.AinfEPow.ePow_facts l K bk m).2.1
  refine ⟨fun h0 => ?_, fun m s hd => ?_⟩
  · have h2 : bk.ev bk.E ^ 2 ∣ bk.ev bk.E := (hF 2 (bk.ev bk.E)).1 (by rw [h0]; exact Ideal.zero_mem _)
    obtain ⟨c, hc⟩ := hS 2 bk.E h2
    have h1 : bk.E * 1 = bk.E * (bk.E * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
    have hu : bk.E * c = 1 := (mul_left_cancel₀ bk.E_ne_zero h1).symm
    have hmem : (1 : Ainf l) ∈ RingHom.ker (Per.θ l) := by
      rw [← bk.span_ev, ← map_one bk.ev, ← hu, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [RingHom.mem_ker, map_one] at hmem
    exact one_ne_zero hmem
  · apply hS m s
    apply (hF m _).1
    obtain ⟨c, hc⟩ := hd
    rw [hc, ← map_pow, ← map_pow]
    exact Ideal.mul_mem_right _ _ ((hF m _).2 (by rw [map_pow]))

end GlobalTheory.BSP.DivTransfer
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem GlobalTheory.ChangeEtaleBasis.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  intro l _ K bk d ρ T0 Wm Wm' A0 A0' hT0 hA0 hA0' hfr hAA hW hW' hWW
  have hO := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → Wm.map (galW l (g : GQ l)) = Wm := by
    intro g hg
    exact Matrix.ext fun i j => by
      simp only [Matrix.map_apply]
      exact hO.2.2.2.2.2.1 g hg _ (hW i j)
  have hfrob : ∀ M : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → ∀ i j, M.map (frobW l) i j ∈ bk.OE := by
    intro M hM i j
    exact hO.2.2.2.2.2.2 _ (hM i j)
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → (∀ i j, N i j ∈ bk.OE) → ∀ i j, (M * N) i j ∈ bk.OE := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ (fun k _ => Subring.mul_mem _ (hM i k) (hN k j))
  have hW'W : Wm' * Wm = 1 := mul_eq_one_comm.mp hWW
  refine ⟨?_, Wm' * A0 * Wm.map (frobW l), Wm'.map (frobW l) * A0' * Wm, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hmap : (T0 * Wm).map (galW l (g : GQ l)) = T0.map (galW l (g : GQ l)) * Wm.map (galW l (g : GQ l)) :=
      Matrix.map_mul (f := ((galW l (g : GQ l)) : WCb l →+* WCb l))
    rw [hmap, hgal g hg, ← Matrix.mul_assoc, hT0 g hg]
  · exact hmul _ _ (hmul _ _ hW' hA0) (hfrob _ hW)
  · exact hmul _ _ (hmul _ _ (hfrob _ hW') hA0') hW
  · have hmap : (T0 * Wm).map (frobW l) = T0.map (frobW l) * Wm.map (frobW l) :=
      Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
    rw [hmap, hfr]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wm Wm', hWW, Matrix.one_mul]
  · have hφ : Wm.map (frobW l) * Wm'.map (frobW l) = 1 := by
      have e : (Wm * Wm').map (frobW l) = Wm.map (frobW l) * Wm'.map (frobW l) :=
        Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
      rw [← e, hWW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    calc Wm' * A0 * Wm.map (frobW l) * (Wm'.map (frobW l) * A0' * Wm)
        = Wm' * A0 * (Wm.map (frobW l) * Wm'.map (frobW l)) * A0' * Wm := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hφ, Matrix.mul_one, Matrix.mul_assoc Wm', hAA, Matrix.mul_one, hW'W]
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_phiContraction_disc_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  first | exact @GlobalTheory.BSP.exists_discStep | exact GlobalTheory.BSP.exists_discStep | (intros; apply GlobalTheory.BSP.exists_discStep <;> assumption)
end
