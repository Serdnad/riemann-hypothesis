module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle062
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.TorsionReduceInjective
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
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

open NumberField KStar.Tree

private theorem UpperTheory.Mu.exists_aut_pow (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) (hM : M ≠ 0)
    (a : ℕ) (ha : a.Coprime M) : ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ t : Ω, t ^ M = 1 → σ t = t ^ a := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hξ' : IsPrimitiveRoot (ξ ^ a) M := hξ.pow_of_coprime a ha
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  have hc : IsConjRoot ℚ (ξ ^ a) ξ := by
    unfold IsConjRoot
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hξ hpos, ← Polynomial.cyclotomic_eq_minpoly_rat hξ' hpos]
  obtain ⟨σ, hσ⟩ := hc.exists_algEquiv
  refine ⟨σ, fun t ht => ?_⟩
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one ht
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

private theorem UpperTheory.Mu.dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

theorem UpperTheory.Mu.autApprox :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ), N ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (v : (ZMod N)ˣ) (u : ℤ_[l]ˣ), (l : ℤ_[l]) ^ N.factorization l ∣ (u : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) → ∀ k : ℕ, ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ (v : ZMod N).val ∧ (l : ℤ_[l]) ^ k ∣ ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
  intro l hl Ω _ _ _ N hN ζ hζ v u huv k
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp : l.Prime := hl.out
  set s := N.factorization l with hs
  set N' := N / l ^ s with hN'
  have hNN : l ^ s * N' = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hcop : Nat.Coprime l N' := Nat.coprime_ordCompl hp hN
  have hcP : Nat.Coprime N' (l ^ (s + k)) := hcop.symm.pow_right _
  have hN'0 : N' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hNN
    exact hN hNN.symm
  have hP0 : l ^ (s + k) ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (l ^ (s + k)) := ⟨hP0⟩
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcP (v : ZMod N).val
    (PadicInt.toZModPow (s + k) (u : ℤ_[l])).val
  have hau : ((a : ℕ) : ZMod (l ^ (s + k))) = PadicInt.toZModPow (s + k) (u : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val]
  have hcoP : a.Coprime (l ^ (s + k)) := by
    rw [← ZMod.isUnit_iff_coprime, hau]
    exact (Units.isUnit u).map _
  have hcoN' : a.Coprime N' := by
    have h1 : (v : ZMod N).val.Coprime N' :=
      (ZMod.val_coe_unit_coprime v).coprime_dvd_right (Dvd.intro_left _ hNN)
    unfold Nat.Coprime at h1 ⊢
    rw [ha1.gcd_eq, h1]
  have hdu : (l : ℤ_[l]) ^ (s + k) ∣ (u : ℤ_[l]) - (a : ℤ_[l]) := by
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, hau]
  have has : a ≡ (v : ZMod N).val [MOD l ^ s] := by
    have h1 : (l : ℤ_[l]) ^ s ∣ (a : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) := by
      have h2 := dvd_sub huv ((pow_dvd_pow _ (Nat.le_add_right s k)).trans hdu)
      convert h2 using 1
      ring
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, map_natCast] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  have haN : a ≡ (v : ZMod N).val [MOD N] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul (hcop.pow_left s)).1 ⟨has, ha1⟩
    rwa [hNN] at this
  obtain ⟨σ, hσ⟩ := UpperTheory.Mu.exists_aut_pow Ω (N' * l ^ (s + k)) (mul_ne_zero hN'0 hP0) a
    (Nat.Coprime.mul_right hcoN' hcoP)
  refine ⟨σ, ?_, ?_⟩
  · have h1 : ζ ^ (N' * l ^ (s + k)) = 1 := by
      have : N' * l ^ (s + k) = N * l ^ k := by rw [← hNN]; ring
      rw [this, pow_mul, hζ.pow_eq_one, one_pow]
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hN, hζ.pow_eq_one⟩
    rw [hσ ζ h1, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
    exact haN
  · refine (pow_dvd_pow _ (Nat.le_add_left k s)).trans ?_
    rw [UpperTheory.Mu.dvd_sub_iff, ← hau]
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (s + k))
    haveI (i : ℕ) : HasEnoughRootsOfUnity Ω (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    have h1 := cyclotomicCharacter.spec l (n := s + k) (σ : Ω ≃+* Ω) η hη.pow_eq_one
    have h2 : σ η = η ^ a := hσ η (by rw [mul_comm, pow_mul, hη.pow_eq_one, one_pow])
    have h3 : η ^ (PadicInt.toZModPow (s + k) ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l])).val = η ^ a :=
      h1.symm.trans h2
    have hfin : IsOfFinOrder η := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hP0, hη.pow_eq_one⟩
    rw [hfin.pow_eq_pow_iff_modEq, ← hη.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at h3
    exact h3
end

section

namespace UpperTheory.Mu

theorem numeric_bound {ι : Type} [Fintype ι] {w : ℕ} (f n r : ℕ) (hcard : Fintype.card ι = f) (L' dmax mass dim idx nrm E dO dS : ℝ)
    (H dk J deg : ι → ℝ) (h8 : 8 ≤ n) (h2 : 2 * r ≤ n) (h1 : 1 ≤ r) (hf : 1 ≤ f) (hL : (5.5 : ℝ) ≤ L') (hn : Real.log n ≤ L')
    (hd0 : 0 ≤ dmax) (hd : Real.log (dmax + 2) ≤ 2 * L') (hw0 : 0 < w) (hw : w ≤ 8 * f ^ 2)
    (hm : 1 / ((w : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass) (hdim : 1 ≤ dim)
    (hidx : idx * nrm = dS⁻¹) (hE : Real.exp (-(r * (2 * f))) ≤ E) (hO : 0 < dO ∧ dO ≤ Real.exp (2 * (r * (2 * f))))
    (hS : 0 < dS ∧ dS ≤ Real.exp (2 * (r * (2 * f)))) (hH : ∀ ρ, 0 < H ρ) (hk : ∀ ρ, 1 ≤ dk ρ) (hJ : ∀ ρ, 0 < J ρ)
    (hdeg : ∀ ρ, 0 ≤ deg ρ ∧ deg ρ ≤ dmax)
    (hJb : ∀ ρ, Real.log (J ρ)⁻¹ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (deg ρ + 2))) :
    0 < (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E ∧
      ∑ ρ, Real.log (H ρ) - 8 * f * (n : ℝ) ^ 2 * L' ≤
        Real.log ((∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E) := by
  obtain ⟨e⟩ : Nonempty (Fin f ≃ ι) := ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  have hw1 : (0 : ℝ) < w := by exact_mod_cast hw0
  have hc : 0 < ((w : ℝ) / 2) ^ n := by positivity
  have hm' : 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ ((w : ℝ) / 2) ^ n * mass := by
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hm hc.le)
    have : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_pow]
    field_simp
  have hm0 : 0 < mass := lt_of_lt_of_le (by positivity) hm
  have hE0 : 0 < E := lt_of_lt_of_le (Real.exp_pos _) hE
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast h1
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast h8
  have hrn : 2 * (r : ℝ) ≤ n := by exact_mod_cast h2
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hs : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have key := GlobalTheory.lamLow_numerical_end f n r L' dmax (((w : ℝ) / 2) ^ n * mass * dim) 1 _ (fun a => H (e a)) (fun _ => 1) (fun a => dk (e a))
    (fun a => (J (e a))⁻¹) h8 h2 h1 hf hL hn hd0 hd (hm'.trans (le_mul_of_one_le_right (mul_pos hc hm0).le hdim)) one_pos
    (by rw [Real.log_one, abs_zero]; positivity)
    (fun a => ⟨hH _, le_rfl, hk _, inv_pos.2 (hJ _), (hJb _).trans (by
      have := (hdeg (e a)).1
      have := (hdeg (e a)).2
      gcongr
      linarith)⟩) rfl
  rw [e.sum_comp fun ρ => Real.log (H ρ), e.prod_comp fun ρ => H ρ * 1 * dk ρ / (J ρ)⁻¹] at key
  have hP : 0 < mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹ := by
    refine mul_pos (by positivity) (Finset.prod_pos fun ρ _ => ?_)
    have := hH ρ; have := hk ρ; have := hJ ρ
    positivity
  have hlw : Real.log (((w : ℝ) / 2) ^ n) ≤ 4 * (n * f) := by
    have b0 : (w : ℝ) / 2 ≤ (2 * f) ^ 2 := by
      have : (w : ℝ) ≤ 8 * (f : ℝ) ^ 2 := by exact_mod_cast hw
      linarith
    have b1 := Real.log_le_log (by positivity) b0
    have b2 := Real.log_le_sub_one_of_pos (x := 2 * (f : ℝ)) (by positivity)
    rw [Real.log_pow] at b1 ⊢
    push_cast at b1
    have : Real.log ((w : ℝ) / 2) ≤ 4 * f := by linarith only [b1, b2]
    linarith only [mul_le_mul_of_nonneg_left this (Nat.cast_nonneg (α := ℝ) n)]
  rw [show ((w : ℝ) / 2) ^ n * mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹ =
    ((w : ℝ) / 2) ^ n * (mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹) by ring, Real.log_mul hc.ne' hP.ne'] at key
  have e1 : (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E =
      (mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹) * (E / (dO * dS)) := by
    simp only [div_inv_eq_mul, mul_one, Finset.prod_mul_distrib]
    have : idx * nrm * dS = 1 := by rw [hidx, inv_mul_cancel₀ hS.1.ne']
    have h3 := hO.1.ne'
    have h4 := hS.1.ne'
    field_simp
    linear_combination ((∏ ρ, dk ρ) * (∏ ρ, H ρ) * (∏ ρ, J ρ)) * this
  have hq : 0 < E / (dO * dS) := div_pos hE0 (mul_pos hO.1 hS.1)
  rw [e1]
  refine ⟨mul_pos hP hq, ?_⟩
  rw [Real.log_mul hP.ne' hq.ne', Real.log_div hE0.ne' (mul_pos hO.1 hS.1).ne', Real.log_mul hO.1.ne' hS.1.ne']
  have a1 := (Real.le_log_iff_exp_le hE0).2 hE
  have a2 := (Real.log_le_iff_le_exp hO.1).2 hO.2
  have a3 := (Real.log_le_iff_le_exp hS.1).2 hS.2
  have a4 : 10 * ((r : ℝ) * f) + 4 * (n * f) ≤ 6 * (f * (n : ℝ) ^ 2 * L') := by
    have b0 : (0 : ℝ) ≤ f := Nat.cast_nonneg _
    have b1 : (r : ℝ) * f ≤ n * f := mul_le_mul_of_nonneg_right (by linarith only [hrn, hr]) b0
    have b2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn8]
    have b3 : (n : ℝ) * f ≤ (n : ℝ) ^ 2 * f := mul_le_mul_of_nonneg_right b2 b0
    have b4 : (n : ℝ) ^ 2 * f * 5.5 ≤ (n : ℝ) ^ 2 * f * L' := mul_le_mul_of_nonneg_left hL (by positivity)
    have b5 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
    linarith only [b1, b3, b4, b5]
  linarith only [key, hlw, a1, a2, a3, a4]

end UpperTheory.Mu
end

section

open NumberField IsDedekindDomain

namespace UpperTheory.Mu

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem tame_ext_prime {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    (ε : (𝓞 L)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) = ε ζ := by
  have hv' : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have hpos := Units.torsionOrder_pos L
  have hn : ((Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal := by
    intro hn
    have hcop : Nat.Coprime (Units.torsionOrder L) p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd hpos hd
      omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((Units.torsionOrder L : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((p : ℕ) : 𝓞 L) := by
      have := congrArg (Int.cast : ℤ → 𝓞 L) hab
      push_cast at this
      exact this.symm
    apply hv'
    rw [Ideal.eq_top_iff_one, h1]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hn) (v.asIdeal.mul_mem_left _ hv)
  have hN : Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal := by
    have hd : Ideal.absNorm v.asIdeal ∣ p ^ Module.finrank ℤ (𝓞 L) := by
      have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hv)
      rwa [Ideal.absNorm_span_singleton, show ((p : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (p : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hv' (Ideal.absNorm_eq_one_iff.1 (by simpa using hk))
    rw [hk]
    exact lt_of_lt_of_le hw (Nat.le_self_pow hk0 p)
  obtain ⟨θ, hθ, hθε⟩ := tame_ext L v hn hN (ε.comp (Units.torsion L).subtype)
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  obtain ⟨m, hm, hζm⟩ := hζ
  have hmem : ζ ∈ Units.torsion L := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨m, hm, ?_⟩
    apply Units.ext
    apply RingOfIntegers.ext
    simpa using hζm
  exact hθε ⟨ζ, hmem⟩

theorem tame_par {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    {I : Type} [Fintype I] (φ : I → L →+* ℂ) (e : I → ℤ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      (∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i) * ((θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
  classical
  let f : I → (𝓞 L)ˣ →* ℂˣ := fun i =>
    (zpowGroupHom (e i)).comp (Units.map ((φ i).toMonoidHom.comp (algebraMap (𝓞 L) L).toMonoidHom))
  obtain ⟨θ, hθ, hθε⟩ := tame_ext_prime v hp hw hv (∏ i, f i)⁻¹
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  have hf : (((∏ i, f i ζ : ℂˣ)) : ℂ) = ∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [f, Units.val_zpow_eq_zpow_val]
  rw [hθε ζ hζ, MonoidHom.inv_apply, MonoidHom.finsetProd_apply, ← hf]
  exact Units.mul_inv _

theorem exists_unit_of_root {z : L} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∃ ζ : (𝓞 L)ˣ, ((ζ : 𝓞 L) : L) = z := by
  obtain ⟨m, hm, hzm⟩ := hz
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow hm ?_
    rw [hzm]
    exact isIntegral_one
  let y : 𝓞 L := ⟨z, hint⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    push_cast
    exact hzm
  exact ⟨(IsUnit.of_pow_eq_one hy hm.ne').unit, rfl⟩

end UpperTheory.Mu
end
