module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ScalarComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle004
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

@[expose] public section

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem ofE_mul_local_orbit_counts {K : Type} [Field K] (Δ τ : K) (z w : Etau K τ) :
    ofE Δ (z * w) = ofE Δ z * ofE Δ w := by
  ext <;> simp [ofE.eq_1] <;> ring

private theorem ofE_one' {K : Type} [Field K] (Δ τ : K) : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE.eq_1]

private theorem sigL_ofE_local_orbit_counts {K : Type} [Field K] (Δ τ : K) (z : Etau K τ) : sigL (ofE Δ z) = ofE Δ z := by
  ext <;> simp [ofE.eq_1, sigL.eq_1]

private theorem mul_ofE_mul_star_sigL_eq_norm_smul {K : Type} [Field K] (Δ τ : K) (m : EL Δ τ) (z : Etau K τ) :
    m * ofE Δ z * star (sigL (ofE Δ z)) = (QuadraticAlgebra.norm z : K) • m := by
  ext <;> simp [ofE.eq_1, sigL.eq_1, QuadraticAlgebra.norm_def] <;> ring

theorem UpperTheory.V.Z.Sym.Loc.lcountNorm : UpperTheory.V.Z.Sym.Loc.LcountNorm := by
  unfold LcountNorm
  intro O K _ _ _ _ _ Δ τ _ c d m _ t ht
  rw [NE.eq_1] at ht
  obtain ⟨u, rfl⟩ := ht
  let y : (EL Δ τ)ˣ :=
    ⟨ofE Δ (u : Etau K τ), ofE Δ (↑u⁻¹ : Etau K τ),
      by rw [← ofE_mul_local_orbit_counts, u.mul_inv, ofE_one'],
      by rw [← ofE_mul_local_orbit_counts, u.inv_mul, ofE_one']⟩
  have hI : DatIso := datIso
  unfold DatIso at hI
  have h := (hI O K Δ τ c d m y).1
  have hy : (y : EL Δ τ) = ofE Δ (u : Etau K τ) := rfl
  have e1 : d * sigL (y : EL Δ τ) * ↑y⁻¹ = d := by
    rw [show sigL (y : EL Δ τ) = (y : EL Δ τ) by rw [hy, sigL_ofE_local_orbit_counts]]
    exact Units.mul_inv_cancel_right d y
  have e2 : m * ↑y * star (sigL (y : EL Δ τ)) = ((Units.map QuadraticAlgebra.norm u : Kˣ) : K) • m := by
    rw [hy, Units.coe_map, mul_ofE_mul_star_sigL_eq_norm_smul]
  rw [e1, e2] at h
  exact h.symm
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem cyc {K : Type} [Field K] {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (hj : (j ω).trace = τ) :
    ∃ g : GL (Fin 2) K, j ω * g = g * !![0, -1; 1, τ] := by
  have hd := j_det_omega j hj
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two] at hj
  by_cases hc : j ω 1 0 ≠ 0
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, j ω 0 0; 0, j ω 1 0]
      (by simpa [Matrix.det_fin_two] using hc), ?_⟩
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination (j ω 0 0) * hj - hd | linear_combination (j ω 1 0) * hj | linear_combination (j ω 0 1) * hj | linear_combination (j ω 1 1) * hj - hd
  · push_neg at hc
    by_cases hb : j ω 0 1 ≠ 0
    · simp only [hc, mul_zero, sub_zero] at hd
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, j ω 0 1; 1, j ω 1 1]
        (by simpa [Matrix.det_fin_two] using hb), ?_⟩
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;> first | ring1 | linear_combination (j ω 0 0) * hj - hd | linear_combination (j ω 1 0) * hj | linear_combination (j ω 0 1) * hj | linear_combination (j ω 1 1) * hj - hd
    · push_neg at hb
      simp only [hb, hc, mul_zero, sub_zero] at hd
      have hne : j ω 1 1 - j ω 0 0 ≠ 0 := by
        intro h; apply hτ; rw [← hj]
        linear_combination (j ω 1 1 - j ω 0 0) * h + 4 * hd
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, j ω 0 0; 1, j ω 1 1]
        (by simpa [Matrix.det_fin_two] using hne), ?_⟩
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb, hc] <;> first | ring1 | linear_combination (j ω 0 0) * hj - hd | linear_combination (j ω 1 0) * hj | linear_combination (j ω 0 1) * hj | linear_combination (j ω 1 1) * hj - hd

theorem UpperTheory.V.Z.Sym.Loc.gConj : UpperTheory.V.Z.Sym.Loc.GConj := by
  intro O K _ _ _ _ _ Δ τ hL hτ j j' hj hj'
  obtain ⟨g1, hg1⟩ := cyc hτ j hj
  obtain ⟨g2, hg2⟩ := cyc hτ j' hj'
  have e1 : ((g1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j ω * g1 = !![0, -1; 1, τ] := by
    rw [mul_assoc, hg1, ← mul_assoc, Units.inv_mul, one_mul]
  have e2 : j' ω = (g2 : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, τ] *
      ((g2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hg2, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) K, g = g1 * g2⁻¹ := ⟨_, rfl⟩
  have hM : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * j ω * g = j' ω := by
    rw [hg, e2, ← e1]; simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]
  have hconj : ∀ z : (Etau K τ)ˣ, jU j' z = g⁻¹ * jU j z * g := by
    intro z; ext1
    simp only [jU, Units.coe_map, Units.val_mul, MonoidHom.coe_coe]
    rw [j_apply j', j_apply j, ← hM]
    simp [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  refine ⟨⟨g, hconj⟩, fun χ hχ z => ?_⟩
  unfold gOrb
  refine orb_congr _ _ _ _ _ _ _ _ _ _ _ (Equiv.mulLeft g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro t y; simp only [Equiv.coe_mulLeft]; rw [hconj t]; simp [mul_assoc]
  · intro y y'; simp [mul_assoc]
  · intro y; simp only [Equiv.coe_mulLeft, MonoidHom.id_apply]; rw [hconj z]; simp [mul_assoc]
  · intro y y' hyy
    simp only [MonoidHom.id_apply]
    rw [← fZK_conj hL hχ hyy]; congr 1; group
  · intro t; simp only [MonoidHom.id_apply]
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm t⁻¹ z, mul_assoc, inv_mul_cancel, mul_one]
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.rootEx : UpperTheory.V.Z.Sym.Loc.RootEx := by
  intro O K _ _ _ _ _ Δ τ hL τ₀ e hτ hm
  subst hτ
  have h2 : IsUnit (2 : O) := hL.two
  have eZ : ((e : ℤ)) * (e : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have he : ((e : ℤ) : O) * ((e : ℤ) : O) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : O)) eZ
  have eK : ((e : ℤ) : K) * ((e : ℤ) : K) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : K)) eZ
  obtain ⟨s, hs, hs2⟩ := sqrtO O K Δ hL (((e : ℤ) : O) * (τ₀ + 2 * ((e : ℤ) : O))) 2 h2 (by
    have hrw : ((e : ℤ) : O) * (τ₀ + 2 * ((e : ℤ) : O)) - 2 ^ 2
        = ((e : ℤ) : O) * (τ₀ - 2 * ((e : ℤ) : O)) := by
      linear_combination (4 : O) * he
    rw [hrw]
    exact Ideal.mul_mem_left _ _ hm)
  have hsu : IsUnit s := by
    by_contra hn
    have hsm : s ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal s).2 ((mem_nonunits_iff).2 hn)
    have h2m : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hsm hs2
      rwa [sub_sub_cancel] at this
    exact ((mem_nonunits_iff).1 ((IsLocalRing.mem_maximalIdeal _).1 h2m)) h2
  set y : O := ((hsu.unit⁻¹ : Oˣ) : O) with hydef
  have hy : s * y = 1 := hsu.mul_val_inv
  have key : (τ₀ + 2 * ((e : ℤ) : O)) * y ^ 2 = ((e : ℤ) : O) := by
    linear_combination (-(τ₀ + 2 * ((e : ℤ) : O)) * y ^ 2) * he
      + (-((e : ℤ) : O) * y ^ 2) * hs + ((e : ℤ) : O) * (s * y + 1) * hy
  have kK : ((algebraMap O K) τ₀ + 2 * ((e : ℤ) : K)) * ((algebraMap O K) y) ^ 2
      = ((e : ℤ) : K) := by
    have := congrArg (algebraMap O K) key
    simpa [map_mul, map_add (f := _), map_pow, map_intCast, map_ofNat] using this
  refine ⟨((e : ℤ) : O) * y, y, Units.isUnit _, ?_, ?_⟩
  · rw [sq]
    ext
    · simp [map_mul, map_intCast]
      linear_combination ((algebraMap O K) y) ^ 2 * eK
    · simp [map_mul, map_intCast]
      linear_combination kK
  · rw [QuadraticAlgebra.norm_def]
    simp only [map_mul, map_intCast]
    linear_combination ((e : ℤ) : K) * kK + (1 - ((algebraMap O K) y) ^ 2) * eK
end
