module

public import Formalism.PeriodIntegrals.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.FiltLenFMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDifferentGenerators.DiffExistsMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalLattice.ExistsSmulMemOfLocal
public import Formalism.PeriodIntegrals.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KernelSplitting.IsIntegralHalf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult
public import Formalism.PeriodIntegrals.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalResidueCharacter.ResCharEq
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

theorem compactBounded : PI.AdCpctDen := PI.adCpctDen
end

section

theorem filtration_length_bound : PI.FiltLenF := PI.FiltrationLength.filtLenF_main
end

section

theorem diffExists {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : PI.DiffGenLoc.DiffExists v :=
  PI.DiffGenLoc.UnitaryGroupMassFormula.diffExists_main v
end

section

theorem latLocGlob : PI.LatLocGlob.LatLocGlob := PI.LatLocGlob.Proof.latLocGlob_core
end

section

theorem kernel_split_of_jacobi : PI.KerIso.SplitOfJacobi := by
  intro K E _ _ _ _ _ cj d p s hd hs hcj hp hJ
  by_cases h2 : p = 2
  · subst h2
    exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two cj d s hd hs hcj
  · exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd cj d p s hs hcj hp h2 (hJ.resolve_left h2)
end

section

open PI.FoldMult.UnitaryGroupMassFormula

theorem overlapMultiplicityProperties : PI.FoldMult.FoldMult := by
  intro G _ _ _ _ _ _ _ Γ hΓ Ω hΩ h1
  exact ⟨fun x => one_le_mult Γ Ω h1 x, fun x => mult_lt_top Γ Ω hΩ x,
    fun γ hγ x => mult_mul_left Γ Ω γ hγ x, measurable_mult Γ Ω hΩ⟩
end

section

private theorem exists_pow_mul_add_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a + b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a + b) = q ^ j * (q ^ i * a) + q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.add_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

private theorem exists_pow_mul_sub_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a - b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a - b) = q ^ j * (q ^ i * a) - q ^ i * (q ^ j * b) := by ring
  rw [e]
  exact S.sub_mem (S.mul_mem (S.pow_mem hq _) hi) (S.mul_mem (S.pow_mem hq _) hj)

private theorem exists_pow_mul_mul_mem_subring {R : Type*} [CommRing R] (S : Subring R) {q a b : R}
    (ha : ∃ k : ℕ, q ^ k * a ∈ S) (hb : ∃ k : ℕ, q ^ k * b ∈ S) : ∃ k : ℕ, q ^ k * (a * b) ∈ S := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  have e : q ^ (i + j) * (a * b) = (q ^ i * a) * (q ^ j * b) := by ring
  rw [e]
  exact S.mul_mem hi hj

private theorem exists_pow_mul_finset_sum_mem_subring {R : Type*} [CommRing R] (S : Subring R) (q : R) (hq : q ∈ S) {ι : Type*}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, ∃ k : ℕ, q ^ k * f i ∈ S) :
    ∃ k : ℕ, q ^ k * ∑ i ∈ s, f i ∈ S := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ⟨0, by simp⟩) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha]
  exact exists_pow_mul_add_mem_subring S q hq (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem witt_ring_structure : PI.WfRing := by
  classical
  intro p _ σ f g hf hg
  delta PI.CoefWf PI.InWf at hf hg ⊢
  have hq : (p : ℂ_[p]) ∈ PI.Wp p := natCast_mem (PI.Wp p) p
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun c hc n => ?_⟩
  · rw [map_add (f := _)]
    exact exists_pow_mul_add_mem_subring _ _ hq (hf n) (hg n)
  · rw [map_sub]
    exact exists_pow_mul_sub_mem_subring _ _ hq (hf n) (hg n)
  · rw [MvPowerSeries.coeff_mul]
    exact exists_pow_mul_finset_sum_mem_subring _ _ hq _ _ fun x _ => exists_pow_mul_mul_mem_subring _ (hf x.1) (hg x.2)
  · rw [MvPowerSeries.coeff_C_mul]
    exact exists_pow_mul_mul_mem_subring _ hc (hf n)
end

section

theorem prime_quotient_unit : PI.PinHostLoc.Target := by
  intro F E _ _ _ _ _ sig p A g hg hne i hin hnot
  have hres := PI.PinHostLoc.UnitaryGroupMassFormula.resChar_eq p (hg i) hin
  have hi0 : ((g i : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (hg i).ne_zero
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact PI.PinHostLoc.UnitaryGroupMassFormula.irr A (hg i).ne_zero hin hnot
  · obtain ⟨j, hgij, hj⟩ : ∃ j : Fin 2, g i ≠ g j ∧
        ((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F) = ((g j : ℕ) : F) := by
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
      · exact ⟨1, hne, mul_div_cancel_left₀ _ hi0⟩
      · exact ⟨0, hne.symm, mul_div_cancel_right₀ _ hi0⟩
    have hjp : ((g j : ℕ) : NumberField.RingOfIntegers F) ∉ p.asIdeal := by
      intro hjin
      have hcop : IsCoprime ((g i : ℕ) : ℤ) ((g j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hg i) (hg j)).mpr hgij)
      obtain ⟨a, b, hab⟩ := hcop
      have h1 : (1 : NumberField.RingOfIntegers F) ∈ p.asIdeal := by
        have h2 := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers F) hab
        push_cast at h2
        rw [← h2]
        exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hin) (p.asIdeal.mul_mem_left _ hjin)
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨u, hu, hu'⟩ := PI.PinHostLoc.UnitaryGroupMassFormula.unit A hjp
    exact ⟨u, hu, by rw [hu', hj]⟩
end
