module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
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
public import Mathlib.Algebra.CharP.Quotient
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

noncomputable section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col.Interp

variable {R : Type} [CommRing R]

theorem coeff_one_add_X_pow (n k : ℕ) : coeff k ((1 + X : PowerSeries R) ^ n) = (n.choose k : R) := by
  have : ((1 + X : PowerSeries R) ^ n) = (((1 + Polynomial.X : Polynomial R) ^ n : Polynomial R) : PowerSeries R) := by
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem one_add_X_pow_sub_one_ne_zero [Nontrivial R] (N : ℕ) (hN : 1 ≤ N) :
    ((1 + X : PowerSeries R) ^ N - 1) ≠ 0 := by
  intro h
  have := congrArg (coeff N) h
  rw [map_sub, coeff_one_add_X_pow, Nat.choose_self, coeff_one, if_neg (by omega)] at this
  simp at this

theorem cyc_succ (p n : ℕ) (hp : p.Prime) :
    cyc R p (n + 1) = ∑ i ∈ Finset.range p, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ i := by
  unfold cyc
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
  simp [Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow, Polynomial.eval₂_X]

theorem om_succ (p n : ℕ) (hp : p.Prime) :
    (1 + X : PowerSeries R) ^ (p ^ (n + 1)) - 1 = cyc R p (n + 1) * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  rw [cyc_succ p n hp, geom_sum_mul, ← pow_mul, ← pow_succ]

theorem cyc_sub_p (p n : ℕ) (hp : p.Prime) :
    ∃ u : PowerSeries R, cyc R p (n + 1) - (p : PowerSeries R) = u * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  refine ⟨∑ i ∈ Finset.range p, ∑ l ∈ Finset.range i, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ l, ?_⟩
  rw [cyc_succ p n hp, Finset.sum_mul]
  have : (p : PowerSeries R) = ∑ i ∈ Finset.range p, (1 : PowerSeries R) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [geom_sum_mul]

theorem cancel_prime [IsDomain R] {q : R} (hq : Prime q) {f : PowerSeries R}
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) f ≠ 0)
    {B s t : PowerSeries R} (m : ℕ)
    (h : C q * B = C q ^ (m + 1) * s + f * t) : ∃ t', B = C q ^ m * s + f * t' := by
  haveI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq
  have hCq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) (C q) = 0 := by
    rw [PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self q), map_zero]
  have ht : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) t = 0 := by
    have h2 : f * t = C q * (B - C q ^ m * s) := by rw [mul_sub, ← mul_assoc, ← pow_succ', h]; ring
    have h3 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q}))) h2
    rw [map_mul, map_mul, hCq, zero_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left hf
  have hd : ∀ n, ∃ a, coeff n t = q * a := by
    intro n
    have := congrArg (coeff n) ht
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose a ha using hd
  have ht' : t = C q * PowerSeries.mk a := by
    ext n; rw [coeff_C_mul, coeff_mk, ha]
  refine ⟨PowerSeries.mk a, ?_⟩
  have hq0 : (C q : PowerSeries R) ≠ 0 := by
    intro h0; exact hq.ne_zero (by simpa using congrArg (constantCoeff) h0)
  apply mul_left_cancel₀ hq0
  rw [h, ht']; ring

end GlobalTheory.Col.Interp

namespace GlobalTheory.Col


open Interp in
theorem X_mul_mem_span_of_levels (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (hR : IsDomain R)
    (hpR : Prime (p : R)) (_hc : IsAdicComplete (Ideal.span {(p : R)}) R)
    (h : PowerSeries R) (k c : ℕ)
    (hyp : ∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) :
    ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  intro j
  induction j with
  | zero =>
    intro _ _
    refine Ideal.mem_span_pair.2 ⟨0, h, ?_⟩
    simp [mul_comm]
  | succ n ih =>
    intro hk hcn
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.1 (ih (by omega) (by omega))
    obtain ⟨y, hy⟩ := hyp (n + 1) (by omega) hk
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hy)
    obtain ⟨u, hu⟩ := cyc_sub_p (R := R) p n hp.out
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 + n := ⟨c - (n + 1), by omega⟩
    have e1 : m + 1 + n - n = m + 1 := by omega
    have e2 : m + 1 + n - (n + 1) = m := by omega
    rw [e1] at hAB
    rw [e2]
    set P : PowerSeries R := (p : PowerSeries R) with hP
    set om : PowerSeries R := (1 + X : PowerSeries R) ^ (p ^ n) - 1 with hom
    have key : C (p : R) * B = C (p : R) ^ (m + 1) * (u * A - u * X * P ^ n * y)
        + cyc R p (n + 1) * (B - u * X * g) := by
      rw [map_natCast]
      linear_combination (-B) * hu - u * hAB + (u * X) * hg
    have hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (cyc R p (n + 1)) ≠ 0 := by
      haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpR.ne_zero).2 hpR
      intro h0
      have h1 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))) (om_succ (R := R) p n hp.out)
      rw [map_mul, h0, zero_mul] at h1
      refine one_add_X_pow_sub_one_ne_zero (R := R ⧸ Ideal.span {(p : R)}) (p ^ (n + 1))
        (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_
      simpa using h1
    obtain ⟨t', ht'⟩ := cancel_prime hpR hf m key
    rw [map_natCast] at ht'
    refine Ideal.mem_span_pair.2 ⟨A * P + (u * A - u * X * P ^ n * y) * om, t', ?_⟩
    rw [om_succ (R := R) p n hp.out]
    linear_combination hAB - om * ht'

end GlobalTheory.Col
end
end

section

open GlobalTheory.Col PowerSeries

noncomputable section
namespace GlobalTheory.Col.NormFrob

theorem ringHom_ext_of_poly {R S : Type} [CommRing R] [CommRing S] (f g : PowerSeries R →+* PowerSeries S)
    (hfg : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom)
    (hf : X ∣ f X) (hg : X ∣ g X) : f = g := by
  ext1 h
  ext n
  set P : Polynomial R := trunc (n + 1) h
  have hd : X ^ (n + 1) ∣ h - (P : PowerSeries R) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [P, Polynomial.coeff_coe, coeff_trunc, hm]
  obtain ⟨q, hq⟩ := hd
  have hh : h = (P : PowerSeries R) + X ^ (n + 1) * q := by rw [← hq]; ring
  have hP : f (P : PowerSeries R) = g (P : PowerSeries R) := by
    have := congrArg (fun F => F P) hfg
    simpa using this
  have key : ∀ F : PowerSeries R →+* PowerSeries S, X ∣ F X → coeff n (F (X ^ (n + 1) * q)) = 0 := by
    intro F hF
    have : X ^ (n + 1) ∣ F (X ^ (n + 1) * q) := by
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hF _) _
    exact (X_pow_dvd_iff.1 this) n (Nat.lt_succ_self n)
  rw [hh, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hP, key f hf, key g hg]

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev red : PowerSeries R →+* PowerSeries (R ⧸ Ideal.span {(p : R)}) :=
  PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))

theorem exists_of_red_eq_zero (D : PowerSeries R) (hD : red p D = 0) :
    ∃ g : PowerSeries R, D = (p : PowerSeries R) * g := by
  have hc : ∀ n, ∃ c : R, coeff n D = (p : R) * c := by
    intro n
    have h1 : coeff n (red p D) = 0 := by rw [hD, map_zero]
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [hc n, show (p : PowerSeries R) = C (p : R) from (map_natCast C p).symm, coeff_C_mul, coeff_mk]

theorem red_pow_eq (σ : R ≃+* R) (hfl : FrobLift R p σ) (h : PowerSeries R) :
    red p h ^ p = red p (phi (R := R) p hp.out.pos (smap σ h)) := by
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  have hX1 : ((frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p)) X = X ^ p := by
    simp [frobenius_def]
  have hX2 : ((red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ))) X = X ^ p := by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smap, map_X, phi_X, map_sub, map_pow,
      map_add, map_one]
    rw [add_pow_char, one_pow, add_sub_cancel_left]
  suffices H : (frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p) =
      (red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ)) by
    have := congrArg (fun F => F h) H
    simpa [frobenius_def] using this
  apply ringHom_ext_of_poly
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, smap, map_C, frobenius_def, ← map_pow]
      have h1 : (phi (R := R) p hp.out.pos) (C (σ a)) = C (σ a) := (phi (R := R) p hp.out.pos).commutes (σ a)
      have h2 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ a) = (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) ^ p := by
        rw [← map_pow]; exact Ideal.Quotient.eq.2 (hfl.frob a)
      rw [h1, map_C, h2, map_pow]
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      rw [RingHom.comp_apply] at hX1 hX2
      rw [hX1, RingHom.comp_apply] at *
      rw [hX2]
  · rw [hX1]; exact dvd_pow_self _ hp.out.ne_zero
  · rw [hX2]; exact dvd_pow_self _ hp.out.ne_zero

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

theorem normOp_eq_smap_add (σ : R ≃+* R) (hfl : FrobLift R p σ)
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule)) (h : PowerSeries R) :
    ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  haveI := hfl.dom
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hfl.prime.ne_zero).2 hfl.prime
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI : Module (PowerSeries R) (PowerSeries R) := Algebra.toModule
  haveI : Module.Free (PowerSeries R) (PowerSeries R) := Module.Free.of_basis b
  have hrank : Module.finrank (PowerSeries R) (PowerSeries R) = p := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hred0 : red p (p : PowerSeries R) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p

  have hcong : ∀ x g : PowerSeries R,
      red p (Algebra.norm (PowerSeries R) (x + (p : PowerSeries R) * g)) = red p (Algebra.norm (PowerSeries R) x) := by
    intro x g
    rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, RingHom.map_det, RingHom.map_det, map_add (f := _),
      map_mul, map_natCast, map_add, map_mul, map_natCast]
    have hz : ((p : ℕ) : Matrix (Fin p) (Fin p) (PowerSeries (R ⧸ Ideal.span {(p : R)}))) = 0 := by
      ext i j
      rw [Matrix.natCast_apply]
      split_ifs <;> simp [CharP.cast_eq_zero]
    rw [hz, zero_mul, add_zero]
  obtain ⟨g, hg⟩ := exists_of_red_eq_zero p (h ^ p - phi (R := R) p hp.out.pos (smap σ h)) (by
    rw [map_sub, map_pow, red_pow_eq p σ hfl h, sub_self])
  have hpow : red p (normOp p h) ^ p = red p (smap σ h) ^ p := by
    have e1 : h ^ p = phi (R := R) p hp.out.pos (smap σ h) + (p : PowerSeries R) * g := by rw [← hg]; ring
    have e2 : Algebra.norm (PowerSeries R) (phi (R := R) p hp.out.pos (smap σ h)) = (smap σ h) ^ p := by
      have := Algebra.norm_algebraMap (S := PowerSeries R) (smap σ h)
      rw [hrank] at this; exact this
    unfold normOp
    rw [← map_pow, ← map_pow (Algebra.norm _), e1, hcong, e2, map_pow]
  have hinj := frobenius_inj (PowerSeries (R ⧸ Ideal.span {(p : R)})) p
  have heq : red p (normOp p h) = red p (smap σ h) := hinj (by simpa [frobenius_def] using hpow)
  obtain ⟨r, hr⟩ := exists_of_red_eq_zero p (normOp p h - smap σ h) (by rw [map_sub, heq, sub_self])
  exact ⟨r, by rw [← hr]; ring⟩

end GlobalTheory.Col.NormFrob
end
end

section

noncomputable section
open PowerSeries

namespace GlobalTheory.Col

variable {R : Type} [CommRing R]

theorem cyc_eq_coe_taylor (p m : ℕ) :
    cyc R p m = ((Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R) : Polynomial R) : PowerSeries R) := by
  unfold cyc
  rw [Polynomial.taylor_apply, Polynomial.comp, ← Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.hom_eval₂]
  have h1 : (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* PowerSeries R).comp Polynomial.C = PowerSeries.C := by
    ext a; simp
  have h2 : (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* PowerSeries R) (Polynomial.X + Polynomial.C 1) = 1 + PowerSeries.X := by
    simp [add_comm]
  rw [h1, h2]

theorem taylor_cyclotomic_dist (p m : ℕ) [hp : Fact p.Prime] :
    (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)).IsDistinguishedAt (Ideal.span {(p : R)}) := by
  have hmap : Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)
      = (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) ℤ)).map (Int.castRingHom R) := by
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.map_comp, Polynomial.map_cyclotomic]
    simp
  have hW : (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) ℤ)).IsWeaklyEisensteinAt (Ideal.span {(p : ℤ)}) := by
    rcases m with _ | n
    · refine ⟨fun {k} hk => ?_⟩
      simp only [pow_zero, Polynomial.cyclotomic_one, Polynomial.taylor_apply, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.one_comp] at hk ⊢
      have : (Polynomial.X + Polynomial.C (1 : ℤ) - 1) = Polynomial.X := by simp
      rw [this] at hk ⊢
      simp at hk
      subst hk
      simp
    · exact (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).isWeaklyEisensteinAt
  have hW' := hW.map (Int.castRingHom R)
  rw [Ideal.map_span, Set.image_singleton, map_natCast, ← hmap] at hW'
  refine { toIsWeaklyEisensteinAt := hW', monic := ?_ }
  rw [Polynomial.taylor_apply]
  exact (Polynomial.cyclotomic.monic _ R).comp_X_add_C 1

def levEquiv (p m : ℕ) [hp : Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    AdjoinRoot (Polynomial.cyclotomic (p ^ m) R) ≃ₐ[R] lev R p m :=
  (Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)).trans
    ((taylor_cyclotomic_dist (R := R) p m).algEquivQuotient.trans
      (Ideal.quotientEquivAlgOfEq R (by rw [cyc_eq_coe_taylor])))

theorem levEquiv_root (p m : ℕ) [hp : Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    levEquiv p m (AdjoinRoot.root (Polynomial.cyclotomic (p ^ m) R)) = ev R p m (1 + X) := by
  change levEquiv p m (Ideal.Quotient.mk _ Polynomial.X) = _
  have h1 : Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl) (Ideal.Quotient.mk _ Polynomial.X)
      = Ideal.Quotient.mk _ (Polynomial.X + Polynomial.C 1) := by
    rw [Ideal.quotientEquivAlg_mk]
    congr 1
    exact Polynomial.taylor_X 1
  have h : levEquiv p m (Ideal.Quotient.mk (Ideal.span {Polynomial.cyclotomic (p ^ m) R}) Polynomial.X)
      = (Ideal.quotientEquivAlgOfEq R (by rw [cyc_eq_coe_taylor]))
          ((taylor_cyclotomic_dist (R := R) p m).algEquivQuotient
            (Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl) (Ideal.Quotient.mk _ Polynomial.X))) := rfl
  rw [h, h1, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk]
  simp [add_comm]

theorem lev_basis : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R →
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ m))) R (lev R p m), ∀ i, b i = ev R p m ((1 + X) ^ (i : ℕ)) := by
  intro R _ p m hp hc
  rcases subsingleton_or_nontrivial R with hs | hs
  · haveI : Subsingleton (lev R p m) := Module.subsingleton R _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun i => Subsingleton.elim _ _⟩
  let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic (p ^ m) R)
  have hd : pb.dim = Nat.totient (p ^ m) := by
    simp [pb, Polynomial.natDegree_cyclotomic]
  refine ⟨(pb.basis.map (levEquiv p m).toLinearEquiv).reindex (finCongr hd), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, PowerBasis.coe_basis]
  simp [pb, levEquiv_root]

end GlobalTheory.Col
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5

noncomputable section

namespace GlobalTheory.Glue.EvTwist

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def part (N i : ℤ) (a : Lau p) : Lau p where
  coeff r := if r % N = i then a.coeff r else 0
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))

theorem part_coeff (N i : ℤ) (a : Lau p) (r : ℤ) :
    (part N i a).coeff r = if r % N = i then a.coeff r else 0 := rfl

def contr (N : ℤ) (hN : 0 < N) (b : Lau p) : Lau p where
  coeff j := b.coeff (N * j)
  isPWO_support' := by
    refine Set.IsWF.isPWO (BddBelow.wellFoundedOn_lt ⟨-|b.order|, fun j hj => ?_⟩)
    have h : b.order ≤ N * j := HahnSeries.order_le_of_coeff_ne_zero hj
    have h1 := neg_abs_le b.order
    have h2 := abs_nonneg b.order
    by_contra hc
    push_neg at hc
    nlinarith

theorem sum_ite {M : Type} [AddCommMonoid M] (N : ℕ) (hN : 0 < N) (r : ℤ) (f : ℕ → M) :
    ∑ i : Fin N, (if r % (N : ℤ) = ((i : ℕ) : ℤ) then f i else 0) = f (r % (N : ℤ)).toNat := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg r hN'.ne'
  have h1 := Int.emod_lt_of_pos r hN'
  rw [Finset.sum_eq_single (⟨(r % (N : ℤ)).toNat, by omega⟩ : Fin N)]
  · rw [if_pos (by simp only; omega)]
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext (by simp only; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem isAlgZp_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsAlgZp (p := p) z :=
  ⟨Polynomial.X ^ N - 1, by simpa using Polynomial.X_pow_sub_C_ne_zero hN (1 : ℤ_[p]), by simp [h]⟩

theorem isInt_of_pow {z : Ω} {N : ℕ} (hN : 0 < N) (h : z ^ N = 1) : IsInt (p := p) z :=
  IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

end GlobalTheory.Glue.EvTwist
end
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mass_eq_sum_ite_union (g : ℕ) [Fact g.Prime] (N : ℕ) (A : (ZMod g)[X] → Prop) :
    mass g N A = ∑ f ∈ sqSet g N, if A f then ((torusCard g f : ℝ))⁻¹ else 0 := by
  unfold mass
  rw [Finset.sum_filter]

theorem mass_union_bounds : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ), (∀ A B : (ZMod g)[X] → Prop, (∀ f ∈ sqSet g N, A f → B f) → mass g N A ≤ mass g N B) ∧ (∀ A, 0 ≤ mass g N A) ∧ (∀ (κ : Type) (s : Finset κ) (A : (ZMod g)[X] → Prop) (B : κ → (ZMod g)[X] → Prop), (∀ f ∈ sqSet g N, A f → ∃ i ∈ s, B i f) → mass g N A ≤ ∑ i ∈ s, mass g N (B i)) ∧ ∀ A : (ZMod g)[X] → Prop, mass g N A + mass g N (fun f => ¬ A f) = mass g N fun _ => True := by
  intro g _ N
  have hw : ∀ f : (ZMod g)[X], (0 : ℝ) ≤ ((torusCard g f : ℝ))⁻¹ := fun f => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B h
    simp only [mass_eq_sum_ite_union]
    refine Finset.sum_le_sum fun f hf => ?_
    by_cases hA : A f
    · rw [if_pos hA, if_pos (h f hf hA)]
    · rw [if_neg hA]
      split_ifs
      · exact hw f
      · exact le_rfl
  · intro A
    exact Finset.sum_nonneg fun f _ => hw f
  · intro κ s A B h
    simp only [mass_eq_sum_ite_union]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun f hf => ?_
    have hn : ∀ i ∈ s, (0 : ℝ) ≤ if B i f then ((torusCard g f : ℝ))⁻¹ else 0 := by
      intro i _
      split_ifs
      · exact hw f
      · exact le_rfl
    by_cases hA : A f
    · obtain ⟨i, hi, hB⟩ := h f hf hA
      rw [if_pos hA]
      have := Finset.single_le_sum hn hi
      simpa only [if_pos hB] using this
    · rw [if_neg hA]
      exact Finset.sum_nonneg hn
  · intro A
    rw [mass_eq_sum_ite_union, mass_eq_sum_ite_union, mass_eq_sum_ite_union, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hA : A f <;> simp [hA]

end GlobalTheory.BadShare
end
