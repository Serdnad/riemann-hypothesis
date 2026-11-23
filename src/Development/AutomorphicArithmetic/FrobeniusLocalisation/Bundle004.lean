module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle003
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle002
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DvdDiscrOfInertia
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem card_eq_of_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : ∀ g, g ∈ A ↔ e g ∈ B) : Nat.card A = Nat.card B :=
  Nat.card_congr (e.toEquiv.subtypeEquiv h)

theorem UpperTheory.HF.grp_bridge :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l) ∧ (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l) ∧ P.ramificationIdx ℤ = H.el l ∧ P.inertiaDeg ℤ = H.nw l ∧ Nat.card (H.decG l) = H.el l * H.nw l ∧ (primesOver (span {(l : ℤ)}) (𝓞 H.E)).ncard * (H.el l * H.nw l) = 4 * φ.ord := by
  intro φ H l hl P _ _
  haveI : Fact l.Prime := ⟨hl⟩
  haveI := H.galois
  haveI hmax : (span {(l : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have hI : ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l := fun σ =>
    (H.der.inertia l P σ).trans (H.mem_inertG l _).symm
  have hD : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l := fun σ =>
    (H.der.decomp l P σ).trans ((UpperTheory.HF.artL_spec H.toHostRaw hl).2.2 _).symm
  have hcI : Nat.card (P.inertia Gal(H.E/ℚ)) = H.el l :=
    card_eq_of_iff H.gal (fun σ => AddSubgroup.mem_inertia.trans (hI σ))
  have hcD : Nat.card (MulAction.stabilizer Gal(H.E/ℚ) P) = Nat.card (H.decG l) :=
    card_eq_of_iff H.gal hD
  have hle : H.inertG l ≤ H.decG l := le_sup_left
  have hmul : Nat.card (H.decG l) = H.el l * H.nw l := by
    rw [← ((H.inertG l).subgroupOf (H.decG l)).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    rfl
  have he : (span {(l : ℤ)}).ramificationIdxIn (𝓞 H.E) = H.el l := by
    rw [← hcI, card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P]
  have hf : (span {(l : ℤ)}).inertiaDegIn (𝓞 H.E) = H.nw l := by
    have h := card_stabilizer_eq (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P
    rw [hcD, hmul, he] at h
    exact (Nat.eq_of_mul_eq_mul_left (H.el_pos l) h).symm
  refine ⟨hI, hD, ?_, ?_, hmul, ?_⟩
  · rw [← he, ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← hf, inertiaDegIn_eq_inertiaDeg (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← he, ← hf, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(l : ℤ)}) (𝓞 H.E) Gal(H.E/ℚ),
      IsGalois.card_aut_eq_finrank, H.der.finrank_E]
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.condE_spec :
    ∀ {φ : Frame} (H : HostRaw φ), H.condE ∣ H.condN ∧ 0 < H.condE ∧ ∀ f : ℕ, f ∣ H.condN → (H.imgOne f = ⊥ ↔ H.condE ∣ f) := by
  intro φ H
  have hN0 : H.condN ≠ 0 := H.condN_ne_zero
  have hN : H.imgOne H.condN = ⊥ := by
    rw [H.imgOne_eq_bot_iff dvd_rfl]
    intro u hu
    have h1 : u = 1 := by
      haveI : NeZero H.condN := ⟨hN0⟩
      apply Units.ext
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 hu
      rw [ZMod.natCast_zmod_val, Nat.cast_one] at h2
      exact h2
    rw [h1, map_one]
  have hmem : H.condE ∣ H.condN ∧ H.imgOne H.condE = ⊥ :=
    Nat.sInf_mem (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}) ⟨H.condN, dvd_rfl, hN⟩
  have hpos : 0 < H.condE := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hN0)
  refine ⟨hmem.1, hpos, fun f hf => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hg : H.imgOne (Nat.gcd H.condE f) = ⊥ := by
      rw [UpperTheory.HF.imgOne_gcd H hmem.1 hf, hmem.2, h, sup_bot_eq]
    have hle : H.condE ≤ Nat.gcd H.condE f :=
      Nat.sInf_le (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥})
        ⟨(Nat.gcd_dvd_right _ _).trans hf, hg⟩
    have heq : Nat.gcd H.condE f = H.condE := le_antisymm (Nat.gcd_le_left _ hpos) hle
    rw [← heq]
    exact Nat.gcd_dvd_right _ _
  · exact le_bot_iff.1 (hmem.2 ▸ H.imgOne_anti h hf)
end

section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem regroup {N : ℕ} (hN : N ≠ 0) (f : ℕ → ℝ) :
    ∑ m ∈ N.divisors, ArithmeticFunction.vonMangoldt m * f (N / m) =
      ∑ l ∈ N.primeFactors, (∑ j ∈ Finset.range (N.factorization l), f (ordCompl[l] N * l ^ j)) * Real.log l := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma', ← Finset.sum_filter_add_sum_filter_not N.divisors IsPrimePow,
    Finset.sum_eq_zero (s := N.divisors.filter fun m => ¬ IsPrimePow m) (fun m hm => by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (Finset.mem_filter.1 hm).2, zero_mul]), add_zero]
  symm
  refine Finset.sum_bij (fun x _ => x.1 ^ (N.factorization x.1 - x.2)) ?_ ?_ ?_ ?_
  · rintro ⟨l, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨?_, hN⟩, ?_⟩
    · exact (pow_dvd_pow l (Nat.sub_le _ _)).trans (Nat.ordProj_dvd N l)
    · exact hx.1.1.isPrimePow.pow (by dsimp only; omega)
  · rintro ⟨l, j⟩ hx ⟨l', j'⟩ hy h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx hy
    dsimp only at h
    have h1 : l = l' := by
      refine (Nat.prime_dvd_prime_iff_eq hx.1.1 hy.1.1).1 (hx.1.1.dvd_of_dvd_pow (n := N.factorization l' - j') ?_)
      rw [← h]; exact dvd_pow_self l (by omega)
    subst h1
    have h2 := Nat.pow_right_injective hx.1.1.two_le h
    obtain rfl : j = j' := by omega
    rfl
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 hm2
    have hd := Nat.dvd_of_mem_divisors hm1
    have hle : k ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN).1 hd
    refine ⟨⟨p, N.factorization p - k⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors]
      exact ⟨⟨hp, (dvd_pow_self p hk.ne').trans hd, hN⟩, by omega⟩
    · dsimp only
      congr 1; omega
  · rintro ⟨l, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_primeFactors] at hx
    dsimp only
    have hl := hx.1.1
    have h4 : N / l ^ (N.factorization l - j) = ordCompl[l] N * l ^ j := by
      refine Nat.div_eq_of_eq_mul_right (pow_pos hl.pos _) ?_
      rw [mul_comm (ordCompl[l] N), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hx.2.le]
      exact (Nat.ordProj_mul_ordCompl_eq_self N l).symm
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hl, h4, mul_comm]

theorem UpperTheory.HF.vd_formula :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l = ∑ j ∈ Finset.range (H.condN.factorization l), (1 - 1 / (Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) : ℝ)) := by
  intro φ H l hl
  have hN : H.condN ≠ 0 := NeZero.ne _
  obtain ⟨-, h2, h3, -⟩ := UpperTheory.HF.log_rd_sum H
  by_cases hlN : l ∈ H.condN.primeFactors
  · have h4 := Formalism.HC.Der.Rd.log_rd_eq H.toHostRaw
    rw [Formalism.HC.Der.Rd.SS, regroup hN (Formalism.HC.Der.Rd.rho H.art.ker), h2] at h4
    let a : ℕ → ℚ := fun p => (padicValNat p (NumberField.discr H.E).natAbs : ℚ) / (Module.finrank ℚ H.E : ℚ)
    let b : ℕ → ℚ := fun p => ∑ j ∈ Finset.range (H.condN.factorization p),
      (1 - 1 / (Nat.card (H.imgOne (ordCompl[p] H.condN * p ^ j)) : ℚ))
    have ha : ∀ p, (a p : ℝ) = H.vdH p := fun p => by
      simp only [a, HostRaw.vdH]; push_cast; rfl
    have hb : ∀ p, (b p : ℝ) = ∑ j ∈ Finset.range (H.condN.factorization p),
        (1 - 1 / (Nat.card (H.imgOne (ordCompl[p] H.condN * p ^ j)) : ℝ)) := fun p => by
      simp only [b]; push_cast; rfl
    have h5 := UpperTheory.HF.log_prime_indep H.condN.primeFactors a b (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (by
        simp_rw [ha, hb]
        rw [h4]
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        refine UpperTheory.HF.rho_art H.toHostRaw ?_
        conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self H.condN p, mul_comm]
        exact mul_dvd_mul_left _ (pow_dvd_pow p (Finset.mem_range.1 hj).le)) l hlN
    rw [← ha, ← hb, h5]
  · have h6 : H.condN.factorization l = 0 := by
      rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hlN
    have h7 : ¬ l ∣ (NumberField.discr H.E).natAbs := fun hd =>
      hlN (h3 (Nat.mem_primeFactors.2 ⟨hl, hd, Int.natAbs_ne_zero.2 (discr_ne_zero H.E)⟩))
    rw [h6, Finset.sum_range_zero, HostRaw.vdH, Nat.padicValNat_def,
      multiplicity_eq_zero_of_not_dvd h7, Nat.cast_zero, zero_div]
end
