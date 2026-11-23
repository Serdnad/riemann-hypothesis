module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoWindowsOfMatrixCongrModTau
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Mathlib.RingTheory.Trace.Defs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGamma
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle638
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FLam

theorem exists_fixed {B : Type} [CommRing B] (q : B) [h : IsAdicComplete (Ideal.span {q}) B]
    (σ : B →+* B) (hσ : σ q = q) (w : B) : ∃ c : B, c = -w + q * σ c := by
  first
  | exact @_root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | (apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed ..)

theorem one_add_pow_of_sq {B : Type} [CommRing B] (x : B) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (n : B) * hx

theorem frobenius_mu (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = (Sandwich.mu ε + 1) ^ p - 1 := by
  unfold Sandwich.mu
  rw [WittVector.frobenius_eq_map_frobenius, map_sub, map_one, WittVector.map_teichmuller,
    frobenius_def, map_pow]
  ring

theorem σ_τ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε) :
    F.σ F.τ = p * F.τ := by
  apply GlobalTheory.WindowIso.σ_τ <;> assumption

end GlobalTheory.FLam


open GlobalTheory.FLam in
theorem GlobalTheory.FLam.exists_lam : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ u : F.B, F.τ ∣ u - 1 → ∃ l : F.B, F.τ ∣ l - 1 ∧ F.σ l = u * l := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F u hu
  obtain ⟨w, hw⟩ := hu
  haveI : IsAdicComplete (Ideal.span {(p : F.B)}) F.B := F.frame.complete
  obtain ⟨c, hc⟩ := exists_fixed (p : F.B) F.σ (map_natCast F.σ p) w
  refine ⟨1 + F.τ * c, ⟨c, by ring⟩, ?_⟩
  have hu' : u = 1 + F.τ * w := by rw [← hw]; ring
  rw [map_add (f := _), map_one, map_mul, σ_τ, hu']
  have hτ := F.τ_sq
  linear_combination (-(w * c)) * hτ - F.τ * hc
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TauUniq

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε)

theorem p_cancel {b c : F.B} (h : (p : F.B) * b = p * c) : b = c := by
  have h1 := congrArg (algebraMap F.B F.Q) h
  simp only [map_mul, map_natCast] at h1
  exact F.frame.inj (F.frame.unit_p.mul_left_cancel h1)

theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem sigma_tau : F.σ F.τ = p * F.τ := by
  apply GlobalTheory.WindowIso.σ_τ <;> assumption

theorem theta_tau [IsDomain O] : F.θ F.τ = 0 :=
  mul_self_eq_zero.1 (by rw [← map_mul, F.τ_sq, map_zero])

theorem dvd_tau {b : F.B} (h : F.τ ∣ b) : ∃ x, b = F.τ * F.a x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨x, y, rfl⟩ := F.gen c
  exact ⟨x, by rw [mul_add, ← mul_assoc, F.τ_sq, zero_mul, add_zero]⟩

theorem lift_exists {ι : Type} (M : Matrix ι ι F.B) :
    ∃ m : Matrix ι ι (Ainf p O), ∀ i j, F.τ ∣ M i j - F.a (m i j) := by
  choose x y h using fun i j => F.gen (M i j)
  exact ⟨Matrix.of x, fun i j => ⟨F.a (y i j), by rw [h i j, Matrix.of_apply]; ring⟩⟩

theorem step {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (u : ι → F.B) (u' : ι → Ainf p O)
    (hu : ∀ j, F.τ ∣ u j - F.a (u' j)) (i : ι) :
    F.τ ∣ M.mulVec (fun j => F.σ (u j)) i -
      F.a (m.mulVec (fun j => WittVector.frobenius (u' j)) i) := by
  have hI : Ideal.span {F.τ} ≤ (Ideal.span {F.τ}).comap F.σ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, sigma_tau]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  simp only [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hm hu ⊢
  have hs : ∀ j, Ideal.Quotient.mk (Ideal.span {F.τ}) (F.σ (u j)) =
      Ideal.Quotient.mk (Ideal.span {F.τ}) (F.a (WittVector.frobenius (u' j))) := by
    intro j
    rw [← F.σ_a, ← Ideal.quotientMap_mk (H := hI), hu j, Ideal.quotientMap_mk]

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hm i j, hs j]

theorem iter {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (w : ι → Ainf p O) (n : ℕ) (i : ι) :
    F.τ ∣ (fun v : ι → F.B => M.mulVec fun j => F.σ (v j))^[n] (fun j => F.a (w j)) i -
      F.a ((fun v : ι → Ainf p O => m.mulVec fun j => WittVector.frobenius (v j))^[n] w i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step F M m hm _ _ ih i

theorem nil_lift [IsDomain O] {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (hM : IsNil F.θ F.σ M) :
    IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) m := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun w i hu => hN (fun j => F.a (w j)) i ?_⟩
  obtain ⟨c, hc⟩ := iter F M m hm w N i
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add (f := _), map_mul, theta_tau, zero_mul, zero_add, F.θ_a]
  exact hu

theorem core (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    [Algebra O C] [IsDomain O] (hv : v.Integers O) (hε : IsPrimitiveSystem ε) {ι : Type} [Fintype ι]
    (M : Matrix ι ι F.B) (hM : IsNil F.θ F.σ M) (z : ι → Ainf p O)
    (hz : ∀ i, F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i) (i : ι) :
    F.τ * F.a (z i) = 0 := by
  obtain ⟨m, hm⟩ := lift_exists F M
  have key : ∀ i, Sandwich.mu ε ∣ z i - m.mulVec (fun j => WittVector.frobenius (z j)) i := by
    intro i
    rw [← F.τ_mul, map_sub, mul_sub, hz i]
    obtain ⟨c, hc⟩ := step F M m hm (fun j => F.a (z j)) z (fun j => by simp) i
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, mul_add, ← mul_assoc, F.τ_sq, zero_mul, zero_add, sub_self]
  exact (F.τ_mul _).2 ((GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι m (nil_lift F M m hm hM)).2 z key i)

theorem vec_eq {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (g : ι → F.B) (z : ι → Ainf p O)
    (hz : ∀ i, g i = F.τ * F.a (z i))
    (hg : ∀ i, M.mulVec (fun j => F.σ (g j)) i = (p : F.B) * g i) (i : ι) :
    F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i := by
  apply p_cancel F
  have e := hg i
  simp only [Matrix.mulVec, dotProduct, hz, map_mul, sigma_tau F] at e
  rw [← e]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem blk_mul_blk (d k : ℕ) (R : Type) [CommRing R] (u : R) :
    blk d k 1 u * blk d k u 1 = u • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) := by
  rw [blk, blk, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U hU hN1 hN2
  have hdet : IsUnit U.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det U).1 hU
  refine ⟨fun Y hY hdiv => ?_, fun g hg hdiv => ?_⟩
  · choose z hz using fun i c => dvd_tau F (hdiv i c)
    have hM : U.transpose⁻¹ * blk d k 1 (p : F.B) * Y.map F.σ = (p : F.B) • Y := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc (blk d k 1 (p : F.B)),
        ← Matrix.mul_assoc (blk d k 1 (p : F.B)), blk_mul_blk, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mul]
    ext i c
    rw [hz i c, Matrix.zero_apply]
    refine core F C v hv hε _ hN1 (fun j => z j c)
      (vec_eq F _ (fun j => Y j c) (fun j => z j c) (fun j => hz j c) (fun i => ?_)) i
    have e := congrArg (fun X => X i c) hM
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using e
  · choose z hz using fun i => dvd_tau F (hdiv i)
    funext i
    rw [hz i, Pi.zero_apply]
    exact core F C v hv hε _ hN2 z
      (vec_eq F _ g z hz (fun i => by simpa using congrFun hg i)) i

end GlobalTheory.TauUniq
end
end

section

namespace GlobalTheory.TraceMulVanishing

theorem trace_mul_eq_zero_imp {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [IsReduced A] (x : A)
    (h : ∀ z : A, (Algebra.trace F A : A → F) (x * z) = (0 : F)) : x = 0 := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero <;> assumption

end GlobalTheory.TraceMulVanishing
end

section

set_option autoImplicit false

namespace GlobalTheory.ConjugateNegativeSquare

open NumberField

theorem conj_eq_neg_of_sq_eq_neg_nat (z : ℂ) (d : ℕ) (h : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.conj_eq_neg_of_sq_eq_neg_natCast <;> assumption

theorem conjugate_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (σ : E →+* ℂ) :
    (ComplexEmbedding.conjugate σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) =
      -(σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) := by
  obtain ⟨d, _, _, rt, hrt, _, _, _, _, _, _, _⟩ := H
  change ComplexEmbedding.conjugate σ (rt : E) = -σ (rt : E)
  rw [ComplexEmbedding.conjugate_coe_eq]
  apply conj_eq_neg_of_sq_eq_neg_nat _ d
  have h1 : (rt : E) ^ 2 = -(d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hrt
    simpa using this
  rw [← map_pow, h1, map_neg, map_natCast]

end GlobalTheory.ConjugateNegativeSquare
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U, iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  first | exact @GlobalTheory.HoloWirt.iterD_eq_wirtWord | exact GlobalTheory.HoloWirt.iterD_eq_wirtWord | (intros; apply GlobalTheory.HoloWirt.iterD_eq_wirtWord <;> assumption)
end

section

noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellinOne

theorem hmon_eq_mul (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    GlobalTheory.HeckeTheta.hmon n z = ((‖z‖ : ℝ) : ℂ) ^ n.natAbs * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have hc : starRingEnd ℂ z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [Int.toNat_natCast, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
    linear_combination hc
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -n = m := ⟨(-n).toNat, by omega⟩
    have hm' : n.natAbs = m := by omega
    rw [hm, hm', Int.toNat_natCast, zpow_natCast, ← mul_pow]
    congr 1
    field_simp

theorem ofReal_prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w = ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem real_factor (r σ a G : ℝ) (k : ℕ) (hr : 0 < r) (hk : (k : ℝ) = a) :
    r ^ k * G * (2 * Real.pi * r ^ 2) ^ (-(σ + a / 2)) =
      (2 * Real.pi) ^ (-(σ + a / 2)) * G * (r ^ 2) ^ (-σ) := by
  subst hk
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos h2π, Real.rpow_def_of_pos (by positivity),
    Real.log_mul h2π.ne' (by positivity), Real.log_pow, ← Real.exp_log (pow_pos hr k), Real.log_pow]
  have key : Real.exp (k * Real.log r) * Real.exp ((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log r) * -(σ + k / 2)) =
      Real.exp (Real.log (2 * Real.pi) * -(σ + k / 2)) * Real.exp ((2 : ℕ) * Real.log r * -σ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  linear_combination G * key

theorem complex_factor (z : ℂ) (hz : z ≠ 0) (n : ℤ) (s G : ℂ) :
    2 * (GlobalTheory.HeckeTheta.hmon n z * G *
      ((2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n| : ℤ) : ℂ) / 2))) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n| : ℤ) : ℂ) / 2)) * G *
        ((z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2π : 0 < 2 * Real.pi := by positivity
  have e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hk : ((n.natAbs : ℕ) : ℂ) = ((|n| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  rw [hmon_eq_mul n hz, e2, ← Complex.cpow_natCast,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi * ‖z‖ ^ 2).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast h2π.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < ‖z‖ ^ 2).ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log h2π.le,
    ← Complex.ofReal_log (by positivity), Real.log_mul h2π.ne' (by positivity), Real.log_pow, hk]
  have key : Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) * ((|n| : ℤ) : ℂ)) *
      Complex.exp (((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) *
      Complex.exp ((((2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (2 * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * G) * key

end GlobalTheory.HeckeMellinOne

namespace GlobalTheory.HeckeMellinOne

theorem real_prod_rpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℝ) :
    (∏ j ∈ t, f j) ^ w = ∏ j ∈ t, f j ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem mellin_term : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  intro K _ _ _ I _ φ hφ n s hs α hα
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  have hv : ∀ i, GlobalTheory.HeckeTheta.emb φ (α : K) i ≠ 0 := fun i => (map_ne_zero (φ i)).2 hαK
  obtain ⟨hint, hI, hN⟩ := GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma I n s hs _ hv
  have hnorm := GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span K I φ hφ α
  refine ⟨hint, ?_, ?_⟩
  · rw [hI, ← Complex.ofReal_natCast, ← hnorm, ofReal_prod_cpow _ _ (fun i => by positivity),
      ← Finset.card_univ, Finset.pow_card_mul_prod]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor GlobalTheory.HeckeStrip.wt
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [complex_factor _ (hv i)]
    simp only [GlobalTheory.HeckeTheta.emb]
    ring
  · rw [hN, ← hnorm, real_prod_rpow _ _ (fun i => by positivity), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact real_factor _ _ _ _ _ (norm_pos_iff.2 (hv i)) (by rw [Nat.cast_natAbs, Int.cast_abs])

end GlobalTheory.HeckeMellinOne
end
end

section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

namespace GlobalTheory.ClassMeanDisc

theorem classMean_log_norm_disc : ∀ (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → discr K = -(D.host.d : ℤ) → 4 < D.host.d → ∀ (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair), (∀ c, ClassGroup.mk K (rep c) = c) → (∀ c, IsLatOf φK (rep c : FractionalIdeal (𝓞 K)⁰ K) (L c)) → (∑ c, Real.log (nrm (rep c : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (L c)‖)) / (classNumber K : ℝ) = 12 * Real.log (2 * Real.pi) - 6 * Real.log D.host.d + 6 * Real.eulerMascheroniConstant - 6 * Formalism.BasicNotions.dlogL D 1 := by
  intro D K _ _ φK h2 hD hd rep L hrep hL
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd3 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hχ : IsKroneckerChar (Formalism.BasicNotions.chiK D) := isKroneckerChar_quadraticChar hd3
  have key := chowla_selberg_discriminant h2 hD hd hχ φK hrep hL
  have hre := congrArg Complex.re key
  simp only [Complex.ofReal_re, Complex.sub_re] at hre
  unfold Formalism.BasicNotions.dlogL nrm latDisc
  rw [hre]
  simp [Complex.mul_re]

end GlobalTheory.ClassMeanDisc
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A]

def tri (n : ℤ) : ℤ := (n * n + n) / 2

def mix (L : LB A.left) (a b : ℤ) : LB A.left :=
  LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![a, b]

def NV (P : LB A.left) (j : ℕ) : Prop :=
  ∃ (κ : Type) (_ : LinearOrder κ) (_ : Fintype κ) (W : κ → A.left.Opens),
    (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = ⊤ ∧ ¬ (GlobalTheory.AbLaw.cechLB A.hom P W).ExactAt j

end GlobalTheory.AmpleGen
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem exists_perm_transport_families (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S]
    (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ)
    (ω₀ ω₁ : ℂ) (hN : 0 < N) (hact : ActBij act) (hf : ∀ s, IsFam act (m s) (f s))
    (hc : ∀ s i, QConj g N (f s i) (f' s i))
    (h4 : g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4) (h6 : g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6) :
    ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_perm_of_sum_monomial_eq' ι S (fun i s => g (f s i τ₀ / ω₀ ^ m s))
    (fun i s => f' s i τ₁ / ω₁ ^ m s)
    (GlobalTheory.T.transport_power_sums_modular_families g ι S act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hf hc h4 h6)
  exact ⟨ρ, fun s i => congrFun (hρ i) s⟩

end GlobalTheory.QFam
end
