module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.scaled_form_den_eq_one_on_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (u w : VQ D), u ∈ X.lat → w ∈ X.lat → (X.s * X.B u w).den = 1 := by
  intro p _ D X u w hu hw
  have hu' : u ∈ X.M ∧ X.r u ∈ LaHat D := by
    unfold UpperTheory.Gal.W2.Wit.Sys.lat at hu
    simpa only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] using hu
  have hw' : w ∈ X.M ∧ X.r w ∈ LaHat D := by
    unfold UpperTheory.Gal.W2.Wit.Sys.lat at hw
    simpa only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] using hw
  have hint : IsIntAf (algebraMap ℚ (AfP p) (X.s * X.B u w)) := by
    rw [X.form u w]
    exact AdelicSim.isInt_mul X.ε_int (AdelicSim.formInt D hu'.2 hw'.2)
  have hcop : (X.s * X.B u w).den.Coprime p := (X.perf u).mp hu'.1 w hw'.1
  obtain ⟨r, z, hz⟩ := UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p _ hint
  set q : ℚ := X.s * X.B u w with hq
  have e : ((p : ℤ) ^ r * q.num : ℤ) = z * q.den := by
    have h : ((p : ℚ) ^ r * q.num : ℚ) = z * q.den := by
      rw [← hz, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast h
  have hdvd : (q.den : ℤ) ∣ (p : ℤ) ^ r * q.num := ⟨z, by rw [e]; ring⟩
  rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  have h2 : q.den ∣ p ^ r := (Nat.Coprime.symm q.reduced).dvd_of_dvd_mul_right hdvd
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right r hcop) h2
end

section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_lattice_approx_mod_n_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (n : ℕ), 0 < n → n.Coprime p → ∀ a : D.La, ∃ u ∈ X.lat, ∃ e ∈ LaHat D, X.r u = inAf D a + n • e := by
  intro p hp D X n hn hnp a
  obtain ⟨w, e₀, he₀, h⟩ := X.dense n hn (inAf D a)
  rw [← X.r_apply] at h
  have hrw : X.r w ∈ LaHat D := by
    have h2 : X.r w = inAf D a - n • e₀ := eq_sub_of_add_eq h.symm
    rw [h2]
    exact sub_mem (GlobalTheory.LKGeo.DenEnd.inAf_mem D a) (AddSubgroup.nsmul_mem _ he₀ n)
  obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
  have hphi : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmod : (p ^ Nat.totient n) ^ k ≡ 1 [MOD n] := by
    simpa using (Nat.ModEq.pow_totient hnp.symm).pow k
  have hle : k ≤ Nat.totient n * k := Nat.le_mul_of_pos_left k hphi
  have ht1 : 1 ≤ p ^ (Nat.totient n * k) := Nat.one_le_pow _ _ hp0
  obtain ⟨q, hq⟩ : n ∣ p ^ (Nat.totient n * k) - 1 :=
    (Nat.modEq_iff_dvd' ht1).1 (by rw [pow_mul]; exact hmod.symm)
  have ht : p ^ (Nat.totient n * k) = 1 + n * q := by omega
  have hM : p ^ (Nat.totient n * k) • w ∈ X.M := by
    have h3 : p ^ (Nat.totient n * k) = p ^ (Nat.totient n * k - k) * p ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [h3, mul_smul]
    exact AddSubgroup.nsmul_mem _ hk _
  have hr : X.r (p ^ (Nat.totient n * k) • w) = inAf D a + n • (q • X.r w - e₀) := by
    rw [map_nsmul, ht, add_smul, one_smul, mul_smul, smul_sub, h]
    generalize n • q • X.r w = y
    generalize n • e₀ = z
    abel
  refine ⟨p ^ (Nat.totient n * k) • w, ?_, q • X.r w - e₀, ?_, hr⟩
  · refine X.mem_lat.2 ⟨hM, ?_⟩
    rw [hr]
    exact add_mem (GlobalTheory.LKGeo.DenEnd.inAf_mem D a)
      (AddSubgroup.nsmul_mem _ (sub_mem (AddSubgroup.nsmul_mem _ hrw q) he₀) n)
  · exact sub_mem (AddSubgroup.nsmul_mem _ hrw q) he₀
end

section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.lattice_saturated_at_p_and_prime_to_p :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), (∀ w : VQ D, X.r w ∈ LaHat D → ∃ k : ℕ, p ^ k • w ∈ X.lat) ∧ (∀ w ∈ X.M, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • w ∈ X.lat) ∧ ∀ w : VQ D, ∃ m : ℕ, m ≠ 0 ∧ m • w ∈ X.lat := by
  intro p hp D X
  have hpp : p.Prime := hp.out
  have h2 : ∀ w ∈ X.M, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • w ∈ X.lat := by
    intro w hw
    obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D (X.r w)
    refine ⟨t, ht0, htc, nsmul_mem hw t, ?_⟩
    rw [map_nsmul]
    exact ht
  refine ⟨?_, h2, ?_⟩
  · intro w hw
    obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
    refine ⟨k, hk, ?_⟩
    rw [map_nsmul]
    exact nsmul_mem hw _
  · intro w
    obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
    obtain ⟨t, ht0, -, ht⟩ := h2 _ hk
    refine ⟨t * p ^ k, Nat.mul_ne_zero ht0.ne' (pow_ne_zero _ hpp.ne_zero), ?_⟩
    rw [mul_smul]
    exact ht
end
