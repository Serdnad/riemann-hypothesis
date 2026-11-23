module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ

@[expose] public section

section

open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem GlobalTheory.KZ.ramified_divisible_of_unramified : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (v : Valuation Ω ℝ≥0) (ψ : O0 p →+* Ω) (E F : ℕ) (π : Ω) (κ : Fin F → Ω), 1 ≤ E → 0 < v (p : Ω) → v (p : Ω) < 1 → v π ^ E = v (p : Ω) → (∀ j, v (κ j) ≤ 1) → (∀ y, v (ψ y) ≤ 1) → (∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 → ∀ j, (p : Lau p) ∣ b j) → ∀ b : Fin F → Fin E → Lau p, v (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s := by
  intro p _ Ω _ _ v ψ E F π κ hE hp0 hp1 hπE hκ hψ hunr b htot
  classical
  set a := algebraMap (Lau p) (O0 p) with ha
  set Y : Fin E → Ω := fun s => ∑ j, κ j * ψ (a (b j s)) with hY
  have hsum : (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (a (b j s)))
      = ∑ s : Fin E, π ^ (s : ℕ) * Y s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hY, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum] at htot

  have hπpos : 0 < v π := by
    rcases eq_or_ne (v π) 0 with h | h
    · exfalso
      have : v π ^ E = 0 := by rw [h]; exact zero_pow (by omega)
      rw [hπE] at this; exact absurd this hp0.ne'
    · exact pos_iff_ne_zero.mpr h
  have hπ1 : v π < 1 := by
    by_contra h
    replace h := not_lt.mp h
    have : 1 ≤ v π ^ E := one_le_pow₀ h
    rw [hπE] at this
    exact absurd hp1 (not_lt.mpr this)
  have hπle : v π ≤ 1 := hπ1.le
  have hY1 : ∀ s, v (Y s) ≤ 1 := by
    intro s
    refine Valuation.map_sum_le v (fun j _ => ?_)
    rw [map_mul]
    calc v (κ j) * v (ψ (a (b j s))) ≤ 1 * 1 := mul_le_mul' (hκ j) (hψ _)
      _ = 1 := one_mul 1
  have hYp : ∀ s, (∀ j, (p : Lau p) ∣ b j s) → v (Y s) ≤ v (p : Ω) := by
    intro s hs
    refine Valuation.map_sum_le v (fun j _ => ?_)
    obtain ⟨c, hc⟩ := hs j
    rw [hc, map_mul, map_mul, map_natCast, map_mul, map_natCast, map_mul]
    calc v (κ j) * (v (p : Ω) * v (ψ (a c))) ≤ 1 * (v (p : Ω) * 1) :=
          mul_le_mul' (hκ j) (mul_le_mul' le_rfl (hψ _))
      _ = v (p : Ω) := by rw [one_mul, mul_one]
  have step : ∀ s : Fin E, (∀ s' : Fin E, s' < s → ∀ j, (p : Lau p) ∣ b j s') →
      ∀ j, (p : Lau p) ∣ b j s := by
    intro s ih
    have hsE : (s : ℕ) + 1 ≤ E := s.isLt
    have hpB : v (p : Ω) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [← hπE]; exact pow_le_pow_of_le_one zero_le hπle hsE
    have hrest : v (∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s') ≤ v π ^ ((s : ℕ) + 1) := by
      refine Valuation.map_sum_le v (fun s' hs' => ?_)
      have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
      rw [map_mul, map_pow]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · calc v π ^ (s' : ℕ) * v (Y s') ≤ 1 * v (p : Ω) :=
              mul_le_mul' (pow_le_one₀ zero_le hπle) (hYp s' (ih s' hlt))
          _ ≤ v π ^ ((s : ℕ) + 1) := by rw [one_mul]; exact hpB
      · have hgt' : (s : ℕ) + 1 ≤ (s' : ℕ) := hgt
        calc v π ^ (s' : ℕ) * v (Y s') ≤ v π ^ (s' : ℕ) * 1 := mul_le_mul' le_rfl (hY1 s')
          _ = v π ^ (s' : ℕ) := mul_one _
          _ ≤ v π ^ ((s : ℕ) + 1) := pow_le_pow_of_le_one zero_le hπle hgt'
    have hsplit : π ^ (s : ℕ) * Y s
        = (∑ s' : Fin E, π ^ (s' : ℕ) * Y s') - ∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s' := by
      rw [← Finset.add_sum_erase Finset.univ (fun s' : Fin E => π ^ (s' : ℕ) * Y s')
        (Finset.mem_univ s)]
      ring
    have hmain : v (π ^ (s : ℕ) * Y s) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [hsplit]
      refine (Valuation.map_sub v _ _).trans (max_le (htot.trans hpB) hrest)
    rw [map_mul, map_pow, pow_succ] at hmain
    have hYs : v (Y s) ≤ v π :=
      le_of_mul_le_mul_left hmain (pow_pos hπpos _)
    exact hunr (fun j => b j s) (lt_of_le_of_lt hYs hπ1)
  intro j s
  exact WellFoundedLT.induction s (fun s ih => step s ih) j
end

section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5

theorem exists_int_poly_root_mod_p : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) → v (p : Ωl) < 1 → ∀ (y : Ωl) (b : O0 p), IsAlgebraic ℤ y → v y ≤ 1 → v (y - algebraMap (O0 p) Ωl b) < 1 → ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
  intro p hpf Ωl _ _ hC v hv _ y b hy hyv hyb
  haveI : CharZero Ωl := Basic.charZero_of_isClo hC
  obtain ⟨P0, hP0, hP0y⟩ := hy
  have hprim : P0.primPart.IsPrimitive := Polynomial.isPrimitive_primPart P0
  have hPy : aeval y P0.primPart = 0 := by
    have e := P0.eq_C_content_mul_primPart
    have hc : P0.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
    rw [e, map_mul, aeval_C] at hP0y
    rcases mul_eq_zero.1 hP0y with h | h
    · exact absurd (by simpa using h) hc
    · exact h
  refine ⟨P0.primPart, ?_, ?_⟩
  · intro h0
    have hd : ∀ n, (p : ℤ) ∣ P0.primPart.coeff n := by
      intro n
      have := congrArg (fun Q => Q.coeff n) h0
      simp only [coeff_map, coeff_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    have hu := hprim (p : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).2 hd)
    have := Int.isUnit_iff.1 hu
    have h2 := hpf.out.two_le
    omega
  · set P := P0.primPart
    set b' := algebraMap (O0 p) Ωl b
    have hb' : v b' ≤ 1 := (hv b').2 isIntegral_algebraMap
    let yi : v.integer := ⟨y, hyv⟩
    let bi : v.integer := ⟨b', hb'⟩
    obtain ⟨d, hd⟩ := Polynomial.sub_dvd_eval_sub yi bi (P.map (Int.castRingHom v.integer))
    have hev : ∀ z : v.integer, v.integer.subtype ((P.map (Int.castRingHom v.integer)).eval z) = aeval (z : Ωl) P := by
      intro z
      rw [Polynomial.eval_map, aeval_def]
      have := Polynomial.hom_eval₂ P (Int.castRingHom v.integer) v.integer.subtype z
      rw [show v.integer.subtype.comp (Int.castRingHom v.integer) = algebraMap ℤ Ωl from RingHom.ext_int _ _] at this
      exact this
    have hd' := congrArg v.integer.subtype hd
    rw [map_sub, map_mul, map_sub, hev, hev] at hd'
    have hd'' : aeval y P - aeval b' P = (y - b') * (d : Ωl) := hd'
    have hkey : aeval b' P = -((y - b') * (d : Ωl)) := by
      rw [← hd'', hPy]; ring
    have hmap : algebraMap (O0 p) Ωl (aeval b P) = aeval b' P := by
      rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_int _ _
    have hlt : v (algebraMap (O0 p) Ωl (aeval b P)) < 1 := by
      rw [hmap, hkey, Valuation.map_neg, Valuation.map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hyb d.2
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have hnu : ¬ IsUnit (aeval b P) := by
      rintro ⟨u, hu⟩
      have h1 : v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) ≤ 1 := (hv _).2 isIntegral_algebraMap
      have h2 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, Valuation.map_one]
      have h3 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left zero_le' hlt h1
      rw [h2] at h3
      exact lt_irrefl _ h3
    have hm : aeval b P ∈ IsLocalRing.maximalIdeal (O0 p) := hnu
    rw [hmax, Ideal.mem_span_singleton] at hm
    exact hm

end GlobalTheory.K5
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5

theorem one_sub_p_div_zeta_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt (p := p) y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt (p := p) (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  intro p hp hp2 Ω _ _ _ T j hj y hy
  classical
  set A := integralClosure (O0 p) Ω
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.out.one_lt
  have hζ1 : T.ζ j ≠ 1 := (T.prim j).ne_one hpj
  have hτ0 : T.ζ j - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζint : IsIntegral (O0 p) (T.ζ j) := by
    refine IsIntegral.of_pow (n := p ^ j) (by omega) ?_
    rw [(T.prim j).pow_eq_one]; exact isIntegral_one
  have htot : 2 ≤ Nat.totient (p ^ j) := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    have : 3 ≤ p := by have := hp.out.two_le; omega
    have h1 : 1 ≤ p ^ (j - 1) := Nat.one_le_pow _ _ hp.out.pos
    calc 2 = 1 * 2 := by ring
      _ ≤ p ^ (j - 1) * (p - 1) := Nat.mul_le_mul h1 (by omega)
  have hdiv : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2) :=
    GlobalTheory.K5.PDiv.pdiv p Ω T j 2 hj htot
  have hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y) := hdiv.mul hy
  let ζ' : A := ⟨T.ζ j, hζint⟩
  let τ : A := ζ' - 1
  let w : A := ⟨_, hw⟩
  let u : A := 1 - τ * w
  have hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y := by
    simp only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
    field_simp
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr

  have hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M := by
    intro M hM
    have hc : (M.comap (algebraMap (O0 p) A)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hpM : (p : A) ∈ M := by
      have h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p) :=
        IsLocalRing.eq_maximalIdeal hc
      have h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A) := by
        rw [h1, hmax]; exact Ideal.mem_span_singleton_self _
      simpa using h2
    have : M.IsPrime := hM.isPrime
    have : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
    have : CharP (A ⧸ M) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM
    have hζp : ζ' ^ (p ^ j) = 1 := Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])
    have h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0 := by
      let q := Ideal.Quotient.mk M
      change (q (ζ' - 1)) ^ (p ^ j) = 0
      rw [q.map_sub, q.map_one, sub_pow_char_pow (p := p) (q ζ') 1 j,
        ← q.map_pow, hζp, q.map_one, one_pow, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact pow_eq_zero_iff (by omega) |>.1 h3
  have hunit : IsUnit u := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h1 : u ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : τ * w ∈ M := M.mul_mem_right _ (hτM M hM)
    have : (1 : A) ∈ M := by
      have := M.add_mem h1 h2; simpa [u] using this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨v, hv⟩ := hunit
  have hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  rw [← hu]
  refine ⟨left_ne_zero_of_mul_eq_one hval, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hval]
  exact ((v⁻¹ : Aˣ) : A).2

end GlobalTheory.K5
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt (p := p) y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt (p := p) (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  intro p hp hp2 Ω _ _ _ T j hj y hy
  classical
  set A := integralClosure (O0 p) Ω
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.out.one_lt
  have hζ1 : T.ζ j ≠ 1 := (T.prim j).ne_one hpj
  have hτ0 : T.ζ j - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζint : IsIntegral (O0 p) (T.ζ j) := by
    refine IsIntegral.of_pow (n := p ^ j) (by omega) ?_
    rw [(T.prim j).pow_eq_one]; exact isIntegral_one
  have htot : 2 ≤ Nat.totient (p ^ j) := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    have : 3 ≤ p := by have := hp.out.two_le; omega
    have h1 : 1 ≤ p ^ (j - 1) := Nat.one_le_pow _ _ hp.out.pos
    calc 2 = 1 * 2 := by ring
      _ ≤ p ^ (j - 1) * (p - 1) := Nat.mul_le_mul h1 (by omega)
  have hdiv : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2) :=
    GlobalTheory.K5.PDiv.pdiv p Ω T j 2 hj htot
  have hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y) := hdiv.mul hy
  let ζ' : A := ⟨T.ζ j, hζint⟩
  let τ : A := ζ' - 1
  let w : A := ⟨_, hw⟩
  let u : A := 1 - τ * w
  have hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y := by
    simp only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
    field_simp
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr

  have hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M := by
    intro M hM
    have hc : (M.comap (algebraMap (O0 p) A)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hpM : (p : A) ∈ M := by
      have h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p) :=
        IsLocalRing.eq_maximalIdeal hc
      have h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A) := by
        rw [h1, hmax]; exact Ideal.mem_span_singleton_self _
      simpa using h2
    have : M.IsPrime := hM.isPrime
    have : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
    have : CharP (A ⧸ M) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM
    have hζp : ζ' ^ (p ^ j) = 1 := Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])
    have h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0 := by
      let q := Ideal.Quotient.mk M
      change (q (ζ' - 1)) ^ (p ^ j) = 0
      rw [q.map_sub, q.map_one, sub_pow_char_pow (p := p) (q ζ') 1 j,
        ← q.map_pow, hζp, q.map_one, one_pow, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact pow_eq_zero_iff (by omega) |>.1 h3
  have hunit : IsUnit u := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h1 : u ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : τ * w ∈ M := M.mul_mem_right _ (hτM M hM)
    have : (1 : A) ∈ M := by
      have := M.add_mem h1 h2; simpa [u] using this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨v, hv⟩ := hunit
  have hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  rw [← hu]
  refine ⟨left_ne_zero_of_mul_eq_one hval, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hval]
  exact ((v⁻¹ : Aˣ) : A).2
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.ZetaNonvanishing₂

variable {Ω : Type} [Field Ω]

theorem valuation_sub_one_pow_sub_le (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (v : Valuation Ω ℝ≥0) (x : Ω) (hx : v x ≤ 1) :
    v ((x - 1) ^ p - (x ^ p - 1)) ≤ v (p : Ω) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨x, hx⟩ : v.integer) (-1)
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [hodd.neg_one_pow] at hr'
  have e : (x - 1) ^ p - (x ^ p - 1) = (p : Ω) * (-(x * (r : Ω))) := by
    rw [sub_eq_add_neg x 1, hr']; ring
  rw [e, v.map_mul, v.map_neg, v.map_mul]
  have hr1 : v (r : Ω) ≤ 1 := r.2
  calc v (p : Ω) * (v x * v (r : Ω)) ≤ v (p : Ω) * (1 * 1) := by gcongr
    _ = v (p : Ω) := by simp

theorem valuation_zeta_sub_one : ∀ (p : ℕ) [hpf : Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), v (p : Ω) < 1 → ∀ n : ℕ, 1 ≤ n → v (T.ζ n - 1) < 1 ∧ v (p : Ω) ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by
  intro p hpf Ω _ _ hp2 T v hvp
  have hp := hpf.out

  have hvz : ∀ n, v (T.ζ n) = 1 := by
    intro n
    have h1 : v (T.ζ n) ^ (p ^ n) = 1 := by
      rw [← v.map_pow, (T.prim n).pow_eq_one, v.map_one]
    exact (pow_eq_one_iff_of_nonneg (zero_le') (pow_ne_zero _ hp.ne_zero)).1 h1

  have hlt : ∀ n, v (T.ζ n - 1) < 1 := by
    intro n
    induction n with
    | zero =>
      have : T.ζ 0 = 1 := by
        have := T.prim 0
        rw [pow_zero] at this
        exact IsPrimitiveRoot.one_right_iff.1 this
      simp [this]
    | succ n ih =>
      have hb := valuation_sub_one_pow_sub_le p hp hp2 v (T.ζ (n + 1)) (hvz _).le
      rw [T.ζpow n] at hb
      have h2 : v ((T.ζ (n + 1) - 1) ^ p) < 1 := by
        have : (T.ζ (n + 1) - 1) ^ p = ((T.ζ (n + 1) - 1) ^ p - (T.ζ n - 1)) + (T.ζ n - 1) := by ring
        rw [this]
        exact lt_of_le_of_lt (v.map_add _ _) (max_lt (lt_of_le_of_lt hb hvp) ih)
      rw [v.map_pow] at h2
      by_contra hc
      push_neg at hc
      exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  intro n hn
  refine ⟨hlt n, ?_⟩

  have hge : v (T.ζ 1 - 1) ≤ v (T.ζ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hz : ∀ k, T.ζ (k + 1) ^ (p ^ k) = T.ζ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', pow_mul, T.ζpow, ih]
    have e : T.ζ 1 - 1 = (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) * (T.ζ (m + 1) - 1) := by
      rw [geom_sum_mul, hz m]
    rw [e, v.map_mul]
    have hs : v (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) ≤ 1 :=
      v.map_sum_le fun i _ => by rw [v.map_pow, hvz, one_pow]
    calc v (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) * v (T.ζ (m + 1) - 1)
        ≤ 1 * v (T.ζ (m + 1) - 1) := by gcongr
      _ = v (T.ζ (m + 1) - 1) := one_mul _
  have h1 := GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq Ω v p hp (T.ζ 1) (by simpa using T.prim 1)
  have ha1 : v (T.ζ 1 - 1) ≤ 1 := (hlt 1).le
  have hp3 : 2 ≤ p - 1 := by have := hp.two_le; omega
  rw [← h1]
  calc v (T.ζ 1 - 1) ^ (p - 1) ≤ v (T.ζ 1 - 1) ^ 2 := pow_le_pow_of_le_one (zero_le') ha1 hp3
    _ = v (T.ζ 1 - 1) * v (T.ζ 1 - 1) := sq _
    _ ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by gcongr

end GlobalTheory.K5.ZetaNonvanishing₂
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mem_sqSet_iff (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X]) :
    f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold sqSet
  rw [Finset.mem_filter, Finset.mem_image, ← and_assoc (a := f.Monic)]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, -, rfl⟩
    have hd : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hd, ?_⟩
    apply natDegree_eq_of_degree_eq_some
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]
    exact hm.as_sum.symm

end GlobalTheory.BadShare
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.TwoFactors

variable {g : ℕ} [Fact g.Prime]

def PairAt (d e : ℕ) (x y : AlgebraicClosure (ZMod g)) (f : (ZMod g)[X]) : Prop :=
  (minpoly (ZMod g) x).natDegree = d ∧ (minpoly (ZMod g) y).natDegree = e ∧ minpoly (ZMod g) x ≠ minpoly (ZMod g) y ∧
    minpoly (ZMod g) x ∣ f ∧ minpoly (ZMod g) y ∣ f

def PairFor (d e l : ℕ) (f : (ZMod g)[X]) : Prop :=
  ∃ x y : AlgebraicClosure (ZMod g), x ^ (g ^ d - 1) = 1 ∧ y ^ (g ^ e - 1) = 1 ∧ SamePart l x y ∧ PairAt d e x y f

end GlobalTheory.BadShare.TwoFactors
end
