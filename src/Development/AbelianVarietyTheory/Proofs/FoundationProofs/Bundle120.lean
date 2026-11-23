module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle101
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle102
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.KTExp

theorem exists_prim_root_of_isAlgClosed (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n : ℕ) (hn : 0 < n) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne')
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

theorem map_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  obtain ⟨ζ, hζ⟩ := exists_prim_root_of_isAlgClosed Ω x.den x.den_pos
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_eq_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x = 1 ↔ x.den = 1 := by
  have hε : Function.Injective ε := ε.injective
  rw [← hε.eq_iff, map_one, map_eOm, Complex.exp_eq_one_iff]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    have h3 : ((x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ hne
      push_cast
      rw [hn]; ring
    have : x = n := by exact_mod_cast h3
    rw [this]; rfl
  · intro h
    refine ⟨x.num, ?_⟩
    have : x = (x.num : ℚ) := by
      exact ((Rat.den_eq_one_iff x).1 h).symm
    rw [this]; push_cast; simp; ring

theorem ent_T_pow (L : ℕ) :
    ent (ofSL (ModularGroup.T ^ L)) 0 0 = 1 ∧ ent (ofSL (ModularGroup.T ^ L)) 0 1 = L ∧
    ent (ofSL (ModularGroup.T ^ L)) 1 0 = 0 ∧ ent (ofSL (ModularGroup.T ^ L)) 1 1 = 1 := by
  have h : ((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (L : ℤ); 0, 1] := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · change (((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) _ _ = _
    rw [h]; simp

end GlobalTheory.Glue.KTExp

namespace GlobalTheory.Glue.KTExp

theorem mem_KT_iff : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (L : ℕ), 0 < L → ∀ f : X.K, (f ∈ KT X L ↔ ∀ r : ℚ, (X.exp f).coeff r ≠ 0 → (r * L).den = 1) := by
  intro Ω _ _ _ ε X L _ f
  obtain ⟨h00, h01, h10, h11⟩ := ent_T_pow L
  have key : ∀ r : ℚ, (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = eOm ε (r * L) * (X.exp f).coeff r := by
    intro r
    have := X.exp_upper (ofSL (ModularGroup.T ^ L)) h10 f r
    rwa [h00, h01, h11, mul_one, div_one, div_one] at this
  have hmem : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := by
    unfold KT
    rw [RingHom.mem_eqLocusField]
    rfl
  rw [hmem]
  constructor
  · intro h r hr
    have k := key r
    rw [h] at k
    have h1 : eOm ε (r * L) = 1 := by
      have : (1 - eOm ε (r * L)) * (X.exp f).coeff r = 0 := by rw [sub_mul, one_mul, ← k, sub_self]
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hr)).symm
    exact (eOm_eq_one_iff ε _).1 h1
  · intro h
    apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
    ext r
    change (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = (X.exp f).coeff r
    rw [key r]
    by_cases hr : (X.exp f).coeff r = 0
    · rw [hr, mul_zero]
    · rw [(eOm_eq_one_iff ε _).2 (h r hr), one_mul]

end GlobalTheory.Glue.KTExp
end
end

section

noncomputable section

namespace GlobalTheory.Glue.Roots

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem eOm_pow (ε : Ω →+* ℂ) (x : ℚ) (n : ℕ) : eOm ε x ^ n = eOm ε (n * x) := by
  apply ε.injective
  rw [map_pow, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem isPrimitiveRoot_eOm_inv (ε : Ω →+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (eOm ε (1 / (n : ℚ))) n := by
  apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ ε.injective
  rw [eOm_spec ε ε.injective]
  convert Complex.isPrimitiveRoot_exp n hn using 2
  push_cast; ring

theorem isPrimitiveRoot_zt (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (zt ε l m) (l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (pow_ne_zero m hl)
  rwa [Nat.cast_pow] at h

theorem zt_add_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m k : ℕ) :
    zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  rw [zt, zt, eOm_pow]
  congr 1; push_cast; field_simp; ring

theorem zt_succ_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    zt ε l (m + 1) ^ l = zt ε l m := by
  simpa using zt_add_pow ε hl m 1

theorem eOm_level_pow (ε : Ω →+* ℂ) {N : ℕ} (hN : N ≠ 0) (l m : ℕ) :
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = zt ε l m := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  rw [zt, eOm_pow]
  congr 1
  rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN', one_mul]

theorem isPrimitiveRoot_eOm_level (ε : Ω →+* ℂ) {N l : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (mul_ne_zero hN (pow_ne_zero m hl))
  rwa [Nat.cast_mul, Nat.cast_pow] at h

theorem eOm_isPrimitiveRoot_compatible : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε →
    ∀ (l : ℕ), l.Prime → ∀ (N : ℕ), 0 < N → ∀ m : ℕ,
    IsPrimitiveRoot (eOm ε (1 / (l : ℚ) ^ m)) (l ^ m) ∧ eOm ε (1 / (l : ℚ) ^ (m + 1)) ^ l = eOm ε (1 / (l : ℚ) ^ m) ∧
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) ∧
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = eOm ε (1 / (l : ℚ) ^ m) := by
  intro Ω _ _ _ ε _ l hl N hN m
  have hl0 : l ≠ 0 := hl.ne_zero
  have hN0 : N ≠ 0 := hN.ne'
  exact ⟨isPrimitiveRoot_zt ε hl0 m, zt_succ_pow ε hl0 m, isPrimitiveRoot_eOm_level ε hN0 hl0 m, eOm_level_pow ε hN0 l m⟩

end GlobalTheory.Glue.Roots
end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem qO_pow_eq (p : ℕ) [Fact p.Prime] (j : ℕ) :
    qO p ^ j = algebraMap (Lau p) (O0 p) (HahnSeries.single (j : ℤ) (1 : ℤ_[p])) := by
  rw [qO, ← map_pow, HahnSeries.single_pow]
  simp

theorem exists_lau_add_p_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (f : Lau p) (z : O0 p), x = algebraMap (Lau p) (O0 p) f + (p : O0 p) * z := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (pI p) x)
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈
      RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [RingHom.mem_ker]
    show AdicCompletion.evalOneₐ (pI p) (x - algebraMap (Lau p) (O0 p) a) = 0
    rw [map_sub, (AdicCompletion.evalOneₐ (pI p)).commutes a]
    show _ - Ideal.Quotient.mk (pI p) a = 0
    rw [ha, sub_self]
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hker, hmap, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨a, z, by rw [← hz]; ring⟩

theorem exists_eq_sum_qO_pow_mul_pow_add_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  obtain ⟨f, z, rfl⟩ := exists_lau_add_p_mul p x
  obtain ⟨g, h, hf⟩ := GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination p f
  refine ⟨fun j => algebraMap (Lau p) (O0 p) (g j), algebraMap (Lau p) (O0 p) h + z, ?_⟩

  rw [hf, map_add (f := _), map_sum, map_mul, map_natCast]
  simp only [map_mul, map_pow, qO_pow_eq]
  ring

end GlobalTheory.K5
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5

theorem exists_valuationSubring_isInt_comap :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type)
      [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
      ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧ ∀ x, x ∈ B ↔ IsInt (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ hC j
  have hvaluation : ∃ v : Valuation Ωl NNReal,
      (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) ∧ v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      hirr.maximalIdeal_eq
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hmax]
      exact GlobalTheory.T.unramified_integers_adic_complete p
    have := hC.alg
    obtain ⟨v, hv⟩ :=
      GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ωl hC.inj
    have : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hle : v (p : Ωl) ≤ 1 := (hv _).2 (by
      simpa [IsInt] using GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ))
    refine ⟨v, hv, lt_of_le_of_ne hle ?_⟩
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hint : IsInt (p := p) ((p : Ωl)⁻¹) := (hv _).1 hi
    exact GlobalTheory.K5.Basic.not_cong_one_zero hC 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  obtain ⟨v, hv, hp1⟩ := hvaluation
  let w : Valuation Ω NNReal := v.comap j
  refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
      ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
    show v (j ((p : ℕ) : Ω)) < 1
    rw [map_natCast]
    exact hp1
  · rw [Valuation.mem_valuationSubring_iff]
    exact hv (j x)

end GlobalTheory.K5
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_valuationSubring_pullback_integral_elements :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
      (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
      ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧
        ∀ x, x ∈ B ↔ IsInt (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ hC j
  have existsValuation : ∃ v : Valuation Ωl NNReal,
      (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) ∧ v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hp⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hp.maximalIdeal_eq]
      exact GlobalTheory.T.unramified_integers_adic_complete p
    have := hC.alg
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
      (O0 p) Ωl hC.inj
    refine ⟨v, hv, ?_⟩
    have : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hle : v (p : Ωl) ≤ 1 := (hv _).2 (by
      have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ)
      simpa [IsInt] using this)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    exact GlobalTheory.K5.Basic.not_cong_one_zero hC 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  obtain ⟨v, hv, hp⟩ := existsValuation
  let w := v.comap j
  refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
      ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
    change v (j (p : Ω)) < 1
    rw [map_natCast]
    exact hp
  · rw [Valuation.mem_valuationSubring_iff]
    exact hv (j x)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N → (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  first | exact @GlobalTheory.BadShare.card_sqSet_ge | exact GlobalTheory.BadShare.card_sqSet_ge | (intros; apply GlobalTheory.BadShare.card_sqSet_ge <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  first | exact @GlobalTheory.BadShare.torusCard_bounds_mul | exact GlobalTheory.BadShare.torusCard_bounds_mul | (intros; apply GlobalTheory.BadShare.torusCard_bounds_mul <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.card_irreducible_samePrimeToPart_roots_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N d l : ℕ), 2 ≤ d → d ≤ N → l.Prime → ¬ BB g N l → (((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card : ℝ) ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) := by
  first | exact @GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le | exact GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le | (intros; apply GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le <;> assumption)
end

section

namespace GlobalTheory.DoubleCosetIndicatorSum

theorem mul_mem_doubleCoset {G : Type} [Group G] {K : Subgroup G} {a g k : G}
    (hg : g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G) := by
  obtain ⟨h, hh, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  exact DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k' * k, K.mul_mem hk' hk, mul_assoc _ _ _⟩

private theorem dosetInd_smul_eq_sum_filter {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {x : V} (hx : x ∈ GlobalTheory.PRep.fixed ρ K) {a : G} {R : Finset G}
    (hR : ∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G))
    (hU : ∀ g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K)
    [DecidableEq (G ⧸ K)] (c : G ⧸ K) :
    Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x =
      ∑ γ ∈ R.filter (fun γ : G => (γ : G ⧸ K) = c), ρ γ x := by
  have hfix : ∀ k ∈ K, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 hx

  have hmk : ∀ γ : G, ((γ : G ⧸ K) = c ↔ γ⁻¹ * Quotient.out c ∈ K) := by
    intro γ
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  by_cases hc : Quotient.out c ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)
  ·
    rw [Formalism.UG.P.dosetInd_of_mem ℂ K a _ hc, one_smul]
    obtain ⟨γ₀, ⟨hγ₀R, hγ₀K⟩, huniq⟩ := hU _ hc
    have hfil : R.filter (fun γ : G => (γ : G ⧸ K) = c) = {γ₀} := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_singleton, hmk]
      constructor
      · rintro ⟨hγR, hγK⟩
        exact huniq γ ⟨hγR, hγK⟩
      · rintro rfl
        exact ⟨hγ₀R, hγ₀K⟩
    rw [hfil, Finset.sum_singleton]
    calc ρ (Quotient.out c) x = ρ (γ₀ * (γ₀⁻¹ * Quotient.out c)) x := by rw [mul_inv_cancel_left]
      _ = ρ γ₀ (ρ (γ₀⁻¹ * Quotient.out c) x) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ γ₀ x := by rw [hfix _ hγ₀K]
  ·
    rw [Formalism.UG.P.dosetInd_of_not_mem ℂ K a _ hc, zero_smul]
    refine (Finset.sum_eq_zero fun γ hγ => ?_).symm
    rw [Finset.mem_filter, hmk] at hγ
    refine absurd ?_ hc
    have h := mul_mem_doubleCoset (hR γ hγ.1) hγ.2
    rwa [mul_inv_cancel_left] at h

theorem main : (let d1 : {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : Module ℂ V] → Representation ℂ G V → Subgroup G → (G → ℂ) → V → V := @(fun {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (x : V) ↦ ∑ᶠ (c : G ⧸ K), h (Quotient.out c) • ((ρ : G → V →ₗ[ℂ] V) (Quotient.out c) : V → V) x); ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}, x ∈ GlobalTheory.PRep.fixed ρ K → ∀ {a : G} {R : Finset G}, (∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G)) → (∀ g ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K) → d1 ρ K (Formalism.UG.dosetInd ℂ K a) x = ∑ γ ∈ R, ((ρ : G → V →ₗ[ℂ] V) γ : V → V) x) := by
  intro d1 G V _ _ _ ρ K x hx a R hR hU
  classical
  show ∑ᶠ c : G ⧸ K, Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x = ∑ γ ∈ R, ρ γ x
  rw [finsum_congr (dosetInd_smul_eq_sum_filter hx hR hU)]
  rw [finsum_eq_sum_of_support_subset (s := R.image fun γ : G => (γ : G ⧸ K))]
  · exact Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem _ hγ) _
  · intro c hc
    obtain ⟨γ, hγ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Function.mem_support.1 hc)
    rw [Finset.mem_filter] at hγ
    exact Finset.mem_image.2 ⟨γ, hγ.1, hγ.2⟩

end GlobalTheory.DoubleCosetIndicatorSum
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem prod_pow_sub_pow_eq (g N : ℕ) :
    ∏ i ∈ Finset.range N, (g ^ N - g ^ i)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  have h1 : ∀ i ∈ Finset.range N, g ^ N - g ^ i = g ^ i * (g ^ (N - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Finset.prod_range_reflect (fun i => g ^ (i + 1) - 1) N]

theorem card_GG_eq (g : ℕ) [Fact g.Prime] (N : ℕ) :
    Fintype.card (GG g N)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  rw [← prod_pow_sub_pow_eq, ← Nat.card_eq_fintype_card]
  have h := Matrix.card_GL_field (𝔽 := ZMod g) N
  rw [ZMod.card] at h
  rw [← Fin.prod_univ_eq_prod_range (fun i => g ^ N - g ^ i) N]
  exact h

end GlobalTheory.BadShare
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = lam (idx A B) • sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | exact GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq <;> assumption)
end
