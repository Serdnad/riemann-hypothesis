module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RepresentationTheory.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocCompCLit

open Matrix

section

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩

private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩

end

end GlobalTheory.LocCompCLit
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Glob

theorem symm_multiset_centre_unique : ∀ (s : Multiset ℤ) (x y : ℤ), s ≠ 0 → s = s.map (x - ·) → s = s.map (y - ·) → x = y := by
  intro s x y hs hx hy
  have key : ∀ z : ℤ, s = s.map (z - ·) → 2 * s.sum = (Multiset.card s : ℤ) * z := by
    intro z hz
    have h1 : (s.map (z - ·)).sum = (Multiset.card s : ℤ) * z - s.sum := by
      rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, Multiset.map_id']
      simp [nsmul_eq_mul]
    have h2 : s.sum = (Multiset.card s : ℤ) * z - s.sum := by
      conv_lhs => rw [hz]
      exact h1
    linarith
  have hc : (Multiset.card s : ℤ) ≠ 0 := by
    exact_mod_cast (mt Multiset.card_eq_zero.mp hs)
  have := (key x hx).symm.trans (key y hy)
  exact mul_left_cancel₀ hc this

end GlobalTheory.Glob
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.PrimesNegSquare

open Polynomial

theorem isSquare_neg_of_dvd (q : ℕ) [Fact q.Prime] (p : ℕ) (h : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) :
    IsSquare (-(p : ℚ_[q])) := by
  obtain ⟨c, hc⟩ := h
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have h2pos : 0 < ‖(2 : ℤ_[q])‖ := norm_pos_iff.mpr two_ne_zero
  have h2le : ‖(2 : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hcle : ‖((c : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hqn : ‖((q : ℕ) : ℤ_[q])‖ = (q : ℝ)⁻¹ := PadicInt.norm_p
  have key : ‖(((p : ℤ) + 1 : ℤ) : ℤ_[q])‖ < ‖(2 : ℤ_[q])‖ ^ 2 := by
    rw [hc]
    push_cast
    have e8 : (8 : ℤ_[q]) = 2 ^ 3 := by norm_num
    rw [e8, norm_mul, norm_mul, norm_pow, hqn]
    have hqinv : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    have hqinv0 : 0 < (q : ℝ)⁻¹ := by positivity
    calc ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ * ‖((c : ℤ) : ℤ_[q])‖
        ≤ ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ := by
          apply mul_le_of_le_one_right (by positivity) hcle
      _ < ‖(2 : ℤ_[q])‖ ^ 2 * 1 := by
          rw [pow_succ, mul_assoc]
          apply mul_lt_mul_of_pos_left _ (by positivity)
          calc ‖(2 : ℤ_[q])‖ * (q : ℝ)⁻¹ ≤ 1 * (q : ℝ)⁻¹ := by gcongr
            _ < 1 := by simpa using hqinv
      _ = ‖(2 : ℤ_[q])‖ ^ 2 := mul_one _
  let F : ℤ[X] := X ^ 2 + C (p : ℤ)
  have hF : ‖aeval (1 : ℤ_[q]) F‖ < ‖aeval (1 : ℤ_[q]) (derivative F)‖ ^ 2 := by
    have e1 : aeval (1 : ℤ_[q]) F = (((p : ℤ) + 1 : ℤ) : ℤ_[q]) := by
      simp [F]; ring
    have e2 : aeval (1 : ℤ_[q]) (derivative F) = 2 := by
      simp [F]
      exact map_ofNat _ 2
    rw [e1, e2]; exact key
  obtain ⟨z, hz, -⟩ := hensels_lemma hF
  have hz' : z ^ 2 + (p : ℤ_[q]) = 0 := by simpa [F] using hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + (p : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz']; simp
  push_cast at this
  linear_combination -this

theorem infinite_primes_neg_isSquare : ∀ (q : ℕ) [Fact q.Prime], {p : ℕ | p.Prime ∧ IsSquare (-(p : ℚ_[q]))}.Infinite := by
  intro q _
  have hq0 : (8 * q) ≠ 0 := by
    have := (Fact.out : q.Prime).pos; omega
  haveI : NeZero (8 * q) := ⟨hq0⟩
  have hu : IsUnit (-1 : ZMod (8 * q)) := isUnit_one.neg
  refine (Nat.infinite_setOfPred_prime_and_eq_mod hu).mono ?_
  rintro p ⟨hp, hpe⟩
  refine ⟨hp, GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q p ?_⟩
  have : (((p : ℤ) + 1 : ℤ) : ZMod (8 * q)) = 0 := by
    push_cast; rw [hpe]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

end GlobalTheory.RealGal.PrimesNegSquare
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SqFix

theorem exists_int_sq_approx (q : ℕ) [Fact q.Prime] (d : ℤ) (h : IsSquare (d : ℚ_[q])) (n : ℕ) :
    ∃ x : ℤ, ((q : ℤ) ^ n) ∣ d - x ^ 2 := by
  obtain ⟨y, hy⟩ := h
  have hy1 : ‖y‖ ≤ 1 := by
    have h1 : ‖y‖ * ‖y‖ ≤ 1 := by
      rw [← norm_mul, ← hy]; exact Padic.norm_int_le_one d
    nlinarith [norm_nonneg y]
  set y' : ℤ_[q] := ⟨y, hy1⟩ with hy'
  set x : ℤ := ((PadicInt.toZModPow n y').val : ℤ) with hx
  refine ⟨x, ?_⟩
  have hmem : y' - (x : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hx]
    simp
  have hd : ((d : ℤ) : ℤ_[q]) = y' * y' := by
    apply Subtype.ext
    simp [hy', hy]
    rfl
  have hmem2 : (((d - x ^ 2 : ℤ)) : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    have : (((d - x ^ 2 : ℤ)) : ℤ_[q]) = (y' - (x : ℤ_[q])) * (y' + (x : ℤ_[q])) := by
      push_cast; rw [hd]; ring
    rw [this]; exact Ideal.mul_mem_right _ _ hmem
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr hmem2
  exact_mod_cast (PadicInt.norm_int_le_pow_iff_dvd (p := q)).mp this

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

theorem valuation_apply_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (s : G F Ω) (hs : s ∈ Dec (F := F) A) (z w : Ω)
    (h : A.valuation z ≤ A.valuation w) : A.valuation (s z) ≤ A.valuation (s w) := by
  by_cases hw : w = 0
  · subst hw
    have hz : z = 0 := by
      have : A.valuation z = 0 := le_antisymm (by simpa using h) zero_le'
      simpa using this
    subst hz; simp
  · have hsw : s w ≠ 0 := (map_ne_zero_iff _ s.injective).mpr hw
    have h1 : A.valuation (z / w) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le'
    have h2 : s (z / w) ∈ A := (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hs _).mpr ((A.valuation_le_one_iff _).mp h1)
    rw [map_div₀] at h2
    have h3 := (A.valuation_le_one_iff _).mpr h2
    rw [map_div₀] at h3
    have hv : A.valuation (s w) ≠ 0 := by simpa using hsw
    exact (div_le_one₀ (zero_lt_iff.mpr hv)).mp h3

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

theorem sqrt_fixed_of_isSquare_padic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (q : ℕ) [Fact q.Prime], ((q : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ (d : ℤ) (δ : Ω), δ ^ 2 = (d : Ω) → IsSquare (d : ℚ_[q]) → ∀ s ∈ Dec (F := F) A, s δ = δ := by
  intro F Ω _ _ _ _ _ v A hA q _ hq d δ hδ hsq s hs
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsδ2 : s δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, map_intCast]
  by_cases hd : d = 0
  · subst hd
    have : δ = 0 := by simpa using hδ
    subst this; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsδ2 with h | h
  · exact h
  exfalso
  have hqv : A.valuation (q : Ω) < 1 := by
    have := (hA (q : 𝓞 F)).mpr hq
    simpa using this
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hN0 : (4 * d).natAbs ≠ 0 := by simp [hd]
  obtain ⟨k, u, hu, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 q (Fact.out : q.Prime).one_lt.ne'
  have hV4d : A.valuation (((4 * d : ℤ)) : Ω) = A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := by
    rcases Int.natAbs_eq (4 * d) with e | e
    · rw [e, hN]; push_cast; rw [map_mul, map_pow]
    · rw [e, hN]; push_cast; rw [Valuation.map_neg, map_mul, map_pow]
  have hu1 : 1 ≤ A.valuation (u : Ω) := by
    refine not_lt.mp fun hlt => ?_
    have hu' : ((u : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA (u : 𝓞 F)).mp (by simpa using hlt)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hu)
    have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have e := congrArg (Int.cast : ℤ → 𝓞 F) hab
      push_cast at e
      rw [← e]
      exact add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hu')
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨x, m, hm⟩ := exists_int_sq_approx q d hsq (k + 1)
  set a : Ω := δ - x with ha
  set b : Ω := δ + x with hb
  have hab : a * b = (q : Ω) ^ (k + 1) * (m : Ω) := by
    have e := congrArg (Int.cast : ℤ → Ω) hm
    push_cast at e
    rw [ha, hb, ← e, ← hδ]; ring
  have hsa : s a = -b := by rw [ha, hb, map_sub, map_intCast, h]; ring
  have hsb : s b = -a := by rw [ha, hb, map_add (f := _), map_intCast, h]; ring
  have hVab : A.valuation a = A.valuation b := by
    rcases le_total (A.valuation a) (A.valuation b) with e | e
    · refine le_antisymm e ?_
      have := valuation_apply_le A s hs a b e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
    · refine le_antisymm ?_ e
      have := valuation_apply_le A s hs b a e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
  have hm1 : A.valuation (m : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hVa : A.valuation a * A.valuation a ≤ A.valuation (q : Ω) ^ (k + 1) := by
    calc A.valuation a * A.valuation a = A.valuation (a * b) := by rw [map_mul, hVab]
      _ = A.valuation (q : Ω) ^ (k + 1) * A.valuation (m : Ω) := by rw [hab, map_mul, map_pow]
      _ ≤ A.valuation (q : Ω) ^ (k + 1) * 1 := mul_le_mul' le_rfl hm1
      _ = _ := mul_one _
  have h2δ : A.valuation (2 * δ) ≤ A.valuation a := by
    have e : 2 * δ = a + b := by rw [ha, hb]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [hVab, max_self]
  have h4d : A.valuation (((4 * d : ℤ)) : Ω) ≤ A.valuation (q : Ω) ^ (k + 1) := by
    have e : (((4 * d : ℤ)) : Ω) = (2 * δ) * (2 * δ) := by push_cast; rw [← hδ]; ring
    rw [e, map_mul]
    exact (mul_le_mul' h2δ h2δ).trans hVa
  have hqk : A.valuation (q : Ω) ^ k ≠ 0 := pow_ne_zero _ (by simpa using hq0)
  have key : A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (q : Ω) := by
    calc A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := mul_le_mul' le_rfl hu1
      _ = A.valuation (((4 * d : ℤ)) : Ω) := hV4d.symm
      _ ≤ A.valuation (q : Ω) ^ (k + 1) := h4d
      _ = _ := pow_succ _ _
  have h3 := mul_le_mul' (le_refl (A.valuation (q : Ω) ^ k)⁻¹) key
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hqk, one_mul, one_mul] at h3
  have := h3
  exact absurd hqv (not_lt.mpr this)

end GlobalTheory.SqFix
end
