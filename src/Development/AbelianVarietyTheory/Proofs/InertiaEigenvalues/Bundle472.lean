module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle460
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle461
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle438
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCocycleOfGeneratorAndFixing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem iter_tm {l : ℕ} [Fact l.Prime] (j : ℕ) (z : Fl l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[j] (algebraMap (Ainf l) (Acris l) (tm z)) =
      algebraMap (Ainf l) (Acris l) (tm (z ^ l ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, (GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    refine (GlobalTheory.RingIface.phiA_teich l (z ^ l ^ j)).trans ?_
    rw [← pow_mul, ← pow_succ]

theorem acris_cancel {l : ℕ} [Fact l.Prime] (k : ℕ) (u v : Acris l)
    (e : (l : Acris l) ^ k * u = (l : Acris l) ^ k * v) : u = v := by
  induction k with
  | zero => simpa using e
  | succ k ih =>
    apply ih
    rw [← sub_eq_zero]
    apply (GlobalTheory.MemLoc.acris_basic l).2.1
    linear_combination e

theorem series_acris : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  intro l _ h x h2 hx
  obtain ⟨-, -, -, hpw_comp, hpw_nat, -, -⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨c, hdvd, hc⟩ := GlobalTheory.T.acris_series_terms_mem_prime_pow l h x h2 hx
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  have hφl : ∀ (j : ℕ) (k : ℕ) (a : Acris l), (⇑(GlobalTheory.MemLoc.phiA l))^[j] ((l : Acris l) ^ k * a) =
      (l : Acris l) ^ k * (⇑(GlobalTheory.MemLoc.phiA l))^[j] a := by
    intro j k a
    rw [← RingHom.coe_pow, map_mul, map_pow, map_natCast]
  have hpwj : ∀ (n : ℤ) (j : ℕ), pw (n * h) x ^ l ^ j = pw (n * h + j) x := by
    intro n j
    rw [← hpw_nat, ← hpw_comp, add_comm]
  have shift : ∀ n : ℤ, (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n) = (l : Acris l) * c (n + 1) := by
    intro n
    apply acris_cancel (n.toNat + (n+1).toNat)
    have e1 := congrArg ((⇑(GlobalTheory.MemLoc.phiA l))^[h]) (hc n)
    rw [hφl, hφl, iter_tm, hpwj] at e1
    have e2 := hc (n + 1)
    have hh : (n + 1) * (h : ℤ) = n * h + h := by ring
    rw [hh] at e2
    calc (l : Acris l) ^ (n.toNat + (n+1).toNat) * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)
        = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ n.toNat * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)) := by ring
      _ = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ (-n).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by rw [e1]
      _ = (l : Acris l) ^ (n.toNat + 1) * ((l : Acris l) ^ (-(n+1)).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega
      _ = _ := by rw [← e2]; ring
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.T.twoSided_shift_series_hasSum l (Acris l) (GlobalTheory.MemLoc.phiA l) h c hdvd shift
  refine ⟨w, hw, fun Θ hΘ hΘt j => ?_⟩
  have hs := hsum (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (fun a => hΘ _)
  have hl : (l : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  have hterm : ∀ n : ℤ, (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (c n) =
      (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
    intro n
    have e := congrArg (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (hc n)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_pow, hφl, hφl, iter_tm, hpwj, map_mul,
      map_mul, map_pow, map_pow, map_natCast, hΘt] at e
    rw [RingHom.comp_apply, RingHom.coe_pow]
    have hn : -n = ((-n).toNat : ℤ) - (n.toNat : ℤ) := by omega
    have ha : (l : ℂ_[l]) ^ n.toNat ≠ 0 := pow_ne_zero _ hl
    rw [hn, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
    calc Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))
        = ((l : ℂ_[l]) ^ n.toNat)⁻¹ * ((l : ℂ_[l]) ^ n.toNat * Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))) := by
          rw [inv_mul_cancel_left₀ ha]
      _ = _ := by rw [e]; ring
  have hs' : HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x))
      ((Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) w) := by
    simpa only [hterm] using hs
  rw [lam, hs'.tsum_eq, RingHom.comp_apply, RingHom.coe_pow]

end GlobalTheory.PSer

end
end

section

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

lemma one_lt_natCast_of_prime : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

lemma prime_rpow_neg_mem_Ico_inv_one {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hL := one_lt_natCast_of_prime (l := l)
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

lemma logb_gaussNormAcrisRadius_convex {x : Formalism.Per.Acris l} (hx : x ≠ 0) {r₁ r₂ t : ℝ} (h1 : 0 < r₂) (h12 : r₂ ≤ r₁)
    (h2 : r₁ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x) ≤
      t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a1, b1⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) (by linarith : 0 < r₁) h2
  obtain ⟨a2, b2⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) h1 (by linarith)
  have hm0 : 0 < t * r₁ + (1 - t) * r₂ := by nlinarith
  have hm1 : t * r₁ + (1 - t) * r₂ ≤ 1 := by nlinarith
  obtain ⟨a0, b0⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hm0 hm1
  have hle : (l : ℝ) ^ (-r₁) ≤ (l : ℝ) ^ (-r₂) := Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have key := GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x _ _ t a1 hle b2 ht0 ht1
  have heq : ((l : ℝ) ^ (-r₁)) ^ t * ((l : ℝ) ^ (-r₂)) ^ (1 - t) = (l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂)) := by
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    congr 1; ring
  rw [heq] at key
  have p1 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a1 b1
  have p2 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a2 b2
  have p0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ a0 b0
  calc Real.logb l (gC l ((l : ℝ) ^ (-(t * r₁ + (1 - t) * r₂))) x)
      ≤ Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x ^ t * gC l ((l : ℝ) ^ (-r₂)) x ^ (1 - t)) :=
        Real.logb_le_logb_of_le hL p0 key
    _ = t * Real.logb l (gC l ((l : ℝ) ^ (-r₁)) x) + (1 - t) * Real.logb l (gC l ((l : ℝ) ^ (-r₂)) x) := by
        rw [Real.logb_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
          Real.logb_rpow_eq_mul_logb_of_pos p1, Real.logb_rpow_eq_mul_logb_of_pos p2]

theorem vr_concaveOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) := by
  refine ⟨convex_Ioc 0 1, ?_⟩
  intro r₁ hr₁ r₂ hr₂ a b ha hb hab
  simp only [vr, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  rcases le_total r₂ r₁ with h | h
  · have := logb_gaussNormAcrisRadius_convex hx hr₂.1 h hr₁.2 ha (by linarith)
    linarith
  · have := logb_gaussNormAcrisRadius_convex hx hr₁.1 h hr₂.2 (t := 1 - a) (by linarith) (by linarith)
    have e : (1 - a) * r₂ + (1 - (1 - a)) * r₁ = a * r₁ + (1 - a) * r₂ := by ring
    rw [e] at this
    linarith

theorem vr_continuousOn_Ioc {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) := by
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  have hmaps : Set.MapsTo (fun r : ℝ => (l : ℝ) ^ (-r)) (Set.Ioc 0 1) (Set.Ico (l : ℝ)⁻¹ 1) :=
    fun r hr => prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2
  have hc1 : Continuous (fun r : ℝ => (l : ℝ) ^ (-r)) :=
    Continuous.rpow continuous_const continuous_neg (fun _ => Or.inl hL0.ne')
  have hc2 : ContinuousOn (fun r : ℝ => gC l ((l : ℝ) ^ (-r)) x) (Set.Ioc 0 1) :=
    (GlobalTheory.T.continuousOn_gaussNormAcrisRadius_Ico l x).comp hc1.continuousOn hmaps
  have hpos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, gC l ((l : ℝ) ^ (-r)) x ≠ 0 := fun r hr =>
    (GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).1 (prime_rpow_neg_mem_Ico_inv_one hr.1 hr.2).2).ne'
  simp only [vr, Real.logb]
  exact ((hc2.log hpos).div_const _).neg

theorem vr_right_affine {x : Formalism.Per.Acris l} (hx : x ≠ 0) :
    ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
      ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) := by
  intro r hr
  have hL := one_lt_natCast_of_prime (l := l)
  have hL0 : (0 : ℝ) < l := by linarith
  obtain ⟨a, b⟩ := prime_rpow_neg_mem_Ico_inv_one (l := l) hr.1 hr.2.le
  have hlt : (l : ℝ)⁻¹ < (l : ℝ) ^ (-r) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt hL (by linarith [hr.2])
  obtain ⟨c, k, ρ₁, hc, hρ₁, hρ₁r, hmon⟩ := (GlobalTheory.T.gaussNormAcris_locally_monomial l x hx _ a b).2 hlt
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le (inv_pos.mpr hL0) hρ₁
  have hsr : r < -Real.logb l ρ₁ := by
    have := Real.logb_lt_logb hL hρ₁0 hρ₁r
    rw [Real.logb_rpow hL0 hL.ne'] at this
    linarith
  have hρs : ρ₁ = (l : ℝ) ^ (-(-Real.logb l ρ₁)) := by
    rw [neg_neg, Real.rpow_logb hL0 hL.ne' hρ₁0]
  have hlogl : Real.log l ≠ 0 := (Real.log_pos hL).ne'
  have formula : ∀ t, r ≤ t → t ≤ -Real.logb l ρ₁ → vr l t x = -Real.logb l c + k * t := by
    intro t ht1 ht2
    have hmem : (l : ℝ) ^ (-t) ∈ Set.Icc ρ₁ ((l : ℝ) ^ (-r)) := by
      constructor
      · rw [hρs]; exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
    simp only [vr]
    rw [hmon _ hmem]
    simp only [Real.logb]
    rw [Real.log_mul hc.ne' (zpow_ne_zero _ (Real.rpow_pos_of_pos hL0 _).ne'), Real.log_zpow,
      Real.log_rpow hL0]
    field_simp
    ring
  refine ⟨k, min (-Real.logb l ρ₁ - r) (1 - r), lt_min (by linarith) (by linarith [hr.2]),
    by linarith [min_le_right (-Real.logb l ρ₁ - r) (1 - r)], ?_⟩
  intro t ht
  have hs1 : r + min (-Real.logb l ρ₁ - r) (1 - r) ≤ -Real.logb l ρ₁ := by
    linarith [min_le_left (-Real.logb l ρ₁ - r) (1 - r)]
  rw [formula t ht.1 (ht.2.trans hs1), formula r le_rfl hsr.le]
  ring

theorem vr_concave_cont_rightSlope : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 →
    ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) ∧ ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) ∧
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧
        ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) :=
  fun _ _ _ hx => ⟨vr_concaveOn_Ioc hx, vr_continuousOn_Ioc hx, vr_right_affine hx⟩

end GlobalTheory.PMon.Gauss

end
end

section

noncomputable section

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

variable {g : ℕ} [Fact g.Prime]

theorem res_zero_left {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g 0) (y : Gn g d) :
    res 0 d χ h y = χ y := by
  unfold res
  have key : ∀ x : Gn g d, (InPar 0 (x : Mt g d) ∧ tl 0 (x : Mt g d) = (h : Mt g 0) ∧
      br 0 d (x : Mt g d) = (y : Mt g d)) ↔ x = y := by
    intro x
    constructor
    · rintro ⟨-, -, hb⟩
      apply Units.ext
      funext i j
      have := congrFun (congrFun hb i) j
      simpa [br, entN, i.isLt, j.isLt] using this
    · rintro rfl
      refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
      funext i j
      simp [br, entN, i.isLt, j.isLt]
  simp only [key, Nat.zero_mul, pow_zero, inv_one, one_mul]
  rw [Finset.sum_ite_eq' Finset.univ y]
  simp

theorem der_zero_one (ψ : AddChar (ZMod g) ℂ) {d : ℕ} (χ : Gn g d → ℂ) :
    der ψ 0 χ 1 = wh ψ χ := by
  unfold der
  have : res 0 (d - 0) χ 1 = χ := funext fun y => res_zero_left χ 1 y
  rw [this]

theorem der_cusp_eq_zero (ψ : AddChar (ZMod g) ℂ) {d m : ℕ} {χ : Gn g d → ℂ} (hχ : IsCusp χ)
    (h0 : 0 < m) (hm : m < d) (h : Gn g m) : der ψ m χ h = 0 := by
  unfold der wh tr
  have : res m (d - m) χ h = fun _ => 0 := funext fun y => res_cusp_eq_zero g d m χ hχ h0 hm h y
  rw [this]
  simp

theorem green_deg_ne_zero (d : ℕ) : ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : i ≠ 0 := by simp at hi; omega
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hlt : 1 < g ^ i := Nat.one_lt_pow hi1 hg
  intro h
  have h' : ((g ^ i : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact sub_eq_zero.mp h
  have := Nat.cast_injective h'
  omega

theorem wh_cusp_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  intro g _ ψ hψ d χ hχ hdeg
  have hd : 0 < d := hχ.1
  have hform := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (isClass_of_isIrr hχ.2.1)
  rw [Finset.sum_eq_single 0] at hform
  · rw [der_zero_one, zero_add, hdeg] at hform
    have hne := green_deg_ne_zero (g := g) d
    have : (wh ψ χ - 1) * ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) = 0 := by
      rw [sub_mul, ← hform]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  · intro m hm hm0
    rw [der_cusp_eq_zero ψ hχ (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm), zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hd) h

end GlobalTheory.GLq
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n → wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → ip χ (gg ψ n) = wh ψ χ := by
  first | exact @GlobalTheory.GLq.GGNorm.gg_norm | exact GlobalTheory.GLq.GGNorm.gg_norm | (intros; apply GlobalTheory.GLq.GGNorm.gg_norm <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d → ∀ x y, res a (d - a) χ x y = 0 := by
  first | exact @GlobalTheory.GLq.res_cusp_eq_zero | exact GlobalTheory.GLq.res_cusp_eq_zero | (intros; apply GlobalTheory.GLq.res_cusp_eq_zero <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.integral_cocycle_of_generator_and_fixing : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ α ∈ Ks K s, ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (qB (LT l) ((logChi LT g : ℤ_[l]) : ℚ_[l]) * (oB (LT l) α * tD (LT l) ^ e) + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (α) := by
  first | exact @GlobalTheory.ExpImage.integral_cocycle_of_gen | exact GlobalTheory.ExpImage.integral_cocycle_of_gen | (intros; apply GlobalTheory.ExpImage.integral_cocycle_of_gen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.continuous_galois_character_filtration_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  first | exact @GlobalTheory.LTChar.char_cont | exact GlobalTheory.LTChar.char_cont | (intros; apply GlobalTheory.LTChar.char_cont <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  first | exact @GlobalTheory.LamTie.CMType.phi_cmType | exact GlobalTheory.LamTie.CMType.phi_cmType | (intros; apply GlobalTheory.LamTie.CMType.phi_cmType <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TransportGL

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem map_map_symm (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g :=
  Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)

theorem det_map (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k) :
    GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom g) =
      Units.map i.toRingHom.toMonoidHom (GeneralLinearGroup.det g) := by
  ext
  simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem isCusp_cls {n : ℕ} (π : IrrRep (GL (Fin n) k)) : (cls π).IsCusp ↔ 0 < n ∧ IsCuspidal π.ρ :=
  and_congr Iff.rfl ⟨isCuspidal_of_equiv (equivRep π).symm, isCuspidal_of_equiv (equivRep π)⟩

def transEquiv (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    Representation.Equiv (π.ρ.comp (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) π'.ρ :=
  .mk e fun g => LinearMap.ext fun v => by
    show e (π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) v) = π'.ρ g (e v)
    rw [he, map_map_symm]

theorem symm_rel (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    ∀ g w, e.symm (π'.ρ g w) = π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) (e.symm w) := fun g w => by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply, map_map_symm]

theorem repRel_tw (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v))
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (hc : ∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) :
    RepRel i ((cls π).tw χ hχ) ((cls π').tw χ' hχ') := by
  refine ⟨n, irrTwist π _ hχ.detChar, irrTwist π' _ hχ'.detChar, e, congrArg (Sigma.mk n) (clTwist_cl π _ hχ.detChar),
    congrArg (Sigma.mk n) (clTwist_cl π' _ hχ'.detChar), fun g (v : π.V) => ?_⟩
  show e (_root_.GlobalTheory.SmGL.twist π.ρ (detChar _ χ) g v) = _root_.GlobalTheory.SmGL.twist π'.ρ (detChar _ χ') (GeneralLinearGroup.map i.toRingHom g) (e v)
  rw [_root_.GlobalTheory.SmGL.twist_apply, _root_.GlobalTheory.SmGL.twist_apply, map_smul, he, detChar_apply, detChar_apply, det_map, hc]

end GlobalTheory.LocLanglands.TransportGL


open GlobalTheory.LocLanglands.TransportGL in
theorem GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  have hs := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  refine ⟨fun x x' ⟨n, π, π', e, hx, hx', he⟩ => ?_, fun χ hχ χ' hχ' hc => ?_⟩
  · subst hx hx'
    refine ⟨?_, fun s => repRel_tw i π π' e he _ _ _ _ (hs.2.2.2.2 s)⟩
    rw [isCusp_cls, isCusp_cls]
    refine and_congr Iff.rfl ⟨fun h => isCuspidal_of_equiv (transEquiv i π π' e he)
      (isCuspidal_comp_generalLinearGroupMap i hs.1 _ h), fun h => isCuspidal_of_equiv
      (transEquiv i.symm π' π e.symm (symm_rel i π π' e he)) (isCuspidal_comp_generalLinearGroupMap i.symm hi _ h)⟩
  · refine ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ' hχ', LinearEquiv.refl ℂ ℂ, rfl, rfl, fun g (v : ℂ) => ?_⟩
    show _root_.GlobalTheory.SmGL.twist (Representation.trivial ℂ (GL (Fin 1) k) ℂ) (detChar (Fin 1) χ) g v =
      _root_.GlobalTheory.SmGL.twist (Representation.trivial ℂ (GL (Fin 1) k') ℂ) (detChar (Fin 1) χ') (GeneralLinearGroup.map i.toRingHom g) v
    rw [_root_.GlobalTheory.SmGL.twist_apply, _root_.GlobalTheory.SmGL.twist_apply, detChar_apply, detChar_apply, TransportGL.det_map, hc]
    rfl

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.segment_linked_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | exact GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | (intros; apply GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one <;> assumption)
end
