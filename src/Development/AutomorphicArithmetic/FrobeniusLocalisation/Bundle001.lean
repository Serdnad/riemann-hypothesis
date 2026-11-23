module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.DirichletDensity.DirichletDensityProofs.Bundle001
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Prime
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

theorem UpperTheory.HF.frobG_spec :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔ H.galE σ = H.frobG p) ∧
      (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧ (((H.frobG p).1.1 : ℤˣ) : ℤ) = H.psAt p ∧
      (H.frobG p ∉ φ.Psi ↔ H.Inert p) ∧ (H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
      ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.frobG p).2 = hcl φ.e v := by
  intro φ H p hpr hnd
  have hp : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hpr.out).2 hnd
  have hodd : p % 2 = 1 := H.odd_of_coprime hp
  set u := ZMod.unitOfCoprime p hp with hu
  have hval : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hp
  have hF : H.frobG p = H.art u := H.frobG_of_coprime hp
  have hjac : (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p := by
    rw [hF, H.der.art_ch u, jacobi_neg_recip H.d_mod_four hodd]
    exact jacobi_congr (hval.of_dvd H.d_dvd_condN)
  have hne : jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by
    rw [← hjac]
    rcases Int.units_eq_one_or ((H.frobG p).1.2) with h | h <;> simp [h]
  have hpsi : H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1 := by
    rw [Frame.mem_Psi_iff, ← hjac]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Units.ext h
  refine ⟨?_, hjac, ?_, ?_, hpsi, ?_⟩
  · intro P _ _ σ
    rw [hF]
    exact H.frob_iff p hp P σ
  · rw [hF, H.psAt_of_coprime hp]
  · rw [hpsi]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.Inert
    constructor
    · intro h
      refine ⟨hpr.out, ?_⟩
      rcases hne with h1 | h1
      · exact absurd h1 h
      · exact h1
    · rintro ⟨-, h⟩
      rw [h]
      decide
  · have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.coprime_dvd_right H.tower_dvd_condN hp
    refine ⟨ZMod.unitOfCoprime p hc2, by simp, ?_⟩
    rw [hF]
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime]
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 (hval.of_dvd H.tower_dvd_condN)).symm
end

section

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem rd_lower_num (e : ℕ) (he : 2 ≤ e) :
    (6.7 : ℝ) < (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by
  have he' : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have h1 : (2 : ℝ) ^ (-(e : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ ((11 : ℝ) / 4) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [he', h1])
  refine lt_of_lt_of_le ?_ h3
  have h4 : ((2 : ℝ) ^ ((11 : ℝ) / 4)) ^ (4 : ℕ) = 2 ^ (11 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    norm_num
  refine lt_of_pow_lt_pow_left₀ 4 (by positivity) ?_
  rw [h4]; norm_num

theorem UpperTheory.HF.rd_lower :
    ∀ {φ : Frame} (H : HostAx φ), (6.7 : ℝ) < (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ∧ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ≤ H.rd / Real.sqrt H.d ∧ 8 < H.rd / 2 ∧ 2 * 2 ^ φ.e ≤ 2 * φ.ord ∧ 2 * φ.ord ≤ 2 * φ.o * 2 ^ φ.e := by
  intro φ H
  have h1 := rd_lower_num φ.e H.two_le_e
  have h2 := H.der.rd_ge
  have hd : 7 ≤ H.d := by have := H.d_mod_sixteen; omega
  have hd' : (7 : ℝ) ≤ (H.d : ℝ) := by exact_mod_cast hd
  have hs : (2.6 : ℝ) ≤ Real.sqrt H.d := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < Real.sqrt H.d := by linarith
  refine ⟨h1, (le_div_iff₀ hs0).2 h2, ?_, Nat.mul_le_mul_left 2 φ.two_pow_le_ord, ?_⟩
  · have h3 : (6.7 : ℝ) * 2.6 ≤ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d :=
      mul_le_mul h1.le hs (by norm_num) (by positivity)
    linarith
  · rw [mul_assoc]
    exact Nat.mul_le_mul_left 2 φ.ord_le_o_mul_two_pow
end

section

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Polynomial

private theorem diffQuadK (K : Type) [Field K] [NumberField K] (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤)
    (hrank : Module.finrank ℚ K = 2) (β : 𝓞 K) (hβ : (β : K) = x) :
    discr K = -(d : ℤ) ∧ differentIdeal ℤ (𝓞 K) = span {β} := by
  have hdisc : discr K = -(d : ℤ) :=
    Formalism.HF.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj
      ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)
  refine ⟨hdisc, ?_⟩
  have hN : (differentIdeal ℤ (𝓞 K)).absNorm = d := by
    rw [absNorm_differentIdeal K, hdisc]; simp
  have hβ2 : β ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.ext
    have : ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2 := by push_cast; rfl
    rw [this, hβ, hx]
    push_cast; rfl
  have hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤ := by
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1
    rw [hadj] at h2
    show Algebra.adjoin ℚ {(β : K)} = ⊤
    rw [hβ, ← h2]
    rfl
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ))
    (by simp [hβ2])
  have h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K) := by
    have := congrArg (fun p => aeval β (derivative p)) hr
    simp only [derivative_X_pow, derivative_C, derivative_mul, map_add (f := _), map_mul,
      minpoly.aeval, zero_mul, add_zero] at this
    have e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r := by
      rw [← this]; simp [map_ofNat]
    rw [e]
    exact Ideal.mul_mem_right _ _ hmem
  have hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    have := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))
    rwa [hN] at this
  have hβmem : β ∈ differentIdeal ℤ (𝓞 K) := by
    have e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β) := by
      have h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1 := by
        have : d = 2 * (d / 2) + 1 := by omega
        exact_mod_cast this
      linear_combination (-β) * h
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)
  have hle : span {β} ≤ differentIdeal ℤ (𝓞 K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hβmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hNβ : (span {β}).absNorm ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]
    have : (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ)) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
    simp [Int.natAbs_pow]
  have hNβ' : (span {β}).absNorm = d := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) hNβ
  have hC1 : C.absNorm = 1 := by
    have := congrArg Ideal.absNorm hC
    rw [map_mul, hNβ', hN] at this
    exact Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)
  rw [Ideal.absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]

end

theorem UpperTheory.HF.discr_K :
    ∀ {φ : Frame} (H : HostAx φ), (discr H.K).natAbs = H.d ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = span {s} ∧ differentIdeal ℤ (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) * span {s} := by
  intro φ H
  let x : H.K := ⟨H.sqd, H.sqd_mem_K⟩
  have hx : x ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [x] using H.sqd_sq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast H.d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    have h' : IntermediateField.lift (@IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {x}) =
        IntermediateField.lift (⊤ : @IntermediateField ℚ H.K _ _ H.K.algebra') := by
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_singleton]
      rfl
    have key := IntermediateField.lift_injective H.K h'
    convert key <;> exact Subsingleton.elim _ _
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 H.K, (β : H.K) = x := ⟨⟨x, hint⟩, rfl⟩
  obtain ⟨hd, hK⟩ := diffQuadK H.K H.d H.d_prime H.d_mod_four x hx hadj H.finrank_K β hβ
  have hmap : (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) =
      span {algebraMap (𝓞 H.K) (𝓞 H.E) β} := by
    rw [hK, Ideal.map_span, Set.image_singleton]
  refine ⟨by rw [hd]; simp, algebraMap (𝓞 H.K) (𝓞 H.E) β, ?_, hmap, ?_⟩
  · show ((β : H.K) : H.E) = H.sqd
    rw [hβ]
  · rw [← hmap]
    exact differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H.K) (𝓞 H.E)
end
