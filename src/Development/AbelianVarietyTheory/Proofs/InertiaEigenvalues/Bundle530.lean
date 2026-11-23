module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgebraProductIdentity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle163
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle376
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle504
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle460
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle515
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc.FilSeed

variable {l : ℕ} [Fact l.Prime]

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  obtain ⟨-, hone, -, -, -, -, hlast⟩ := filD_laws l
  have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (hlast 0 1).1 (by rw [map_one, Nat.cast_zero]; exact hone)
  simpa using Ideal.mul_mem_left _ y h1

theorem exists_unit (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ c : (Per.BdRp l)ˣ, aDp l ξ = (c : Per.BdRp l) * aDp l (xi C.ε) := by
  have hreg := (filtration_eq_xi_pow l C.ε (core_isEps l C)).2.1
  rw [C.ker_theta] at hξ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hξ ▸ Ideal.mem_span_singleton_self ξ :
    ξ ∈ Ideal.span {xi C.ε})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hξ.symm ▸ Ideal.mem_span_singleton_self (xi C.ε) :
    xi C.ε ∈ Ideal.span {ξ})
  have h1 : aDp l a * aDp l b = 1 := by
    have : aDp l (xi C.ε) * (aDp l a * aDp l b - 1) = 0 := by
      have e : aDp l (xi C.ε) = aDp l b * (aDp l a * aDp l (xi C.ε)) := by
        rw [← map_mul, ← map_mul, ha, hb]
      linear_combination -e
    exact sub_eq_zero.1 (hreg _ this)
  refine ⟨⟨aDp l a, aDp l b, h1, by rw [mul_comm, h1]⟩, ?_⟩
  rw [← ha, map_mul]

end GlobalTheory.MemLoc.FilSeed


open GlobalTheory.MemLoc.FilSeed in
theorem GlobalTheory.MemLoc.seed_fil : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → (∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n}) ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a) ∧ (∀ (n : ℕ) (z : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n ↔ z ∈ Per.FilP l n) ∧ (∀ x : Per.BdR l, ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ))) ∧ (∀ (a : ℤ) (n : ℕ) (x : Per.BdR l), algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ n * x ∈ Per.FilD l (a + n) ↔ x ∈ Per.FilD l a) ∧ Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  intro l _ C ξ hξ
  obtain ⟨hstep, hone, hmul, hex, -, -, hlast⟩ := filD_laws l
  obtain ⟨hP, hreg, -, -⟩ := filtration_eq_xi_pow l C.ε (core_isEps l C)
  obtain ⟨c, hc⟩ := exists_unit C ξ hξ
  have h1 : ∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n} := by
    intro n
    ext y
    rw [hP, Ideal.mem_span_singleton, hc, mul_pow, ← Units.val_pow_eq_pow_val,
      Units.mul_left_dvd]
  have hanti : ∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => exact le_rfl
    | succ b _ ih => exact (hstep b).trans ih
  refine ⟨h1, hmul, hanti, hlast, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := hex x
    exact ⟨(-a).toNat, hanti _ _ (by omega) ha⟩
  · intro a n x
    set w := algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) with hw
    have hwn : w ^ n ∈ Per.FilD l n := by
      rw [hw, ← map_pow, hlast, h1]
      exact Ideal.mem_span_singleton_self _

    have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hw0 : w ≠ 0 := by
      intro h
      have h0 : aDp l ξ = 0 := hinj (by rw [← hw, h, map_zero])
      rw [hc] at h0
      have h2 : aDp l (xi C.ε) = 0 := (Units.mul_right_eq_zero c).1 h0
      exact one_ne_zero (hreg 1 (by rw [h2, zero_mul]))
    haveI := hfr
    have hne : aDp l ξ ≠ 0 := fun h => hw0 (by rw [hw, h, map_zero])
    obtain ⟨u, hu⟩ : IsUnit w :=
      IsLocalization.map_units (Per.BdR l) (⟨aDp l ξ, mem_nonZeroDivisors_of_ne_zero hne⟩ : nonZeroDivisors _)
    have hv : ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ∈ Per.FilD l (-1) := by
      rw [mem_FilD_iff_xi_pow l C.ε (core_isEps l C)]
      refine ⟨((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l), ?_⟩
      have e1 : (- (-1 : ℤ)).toNat = 1 := by norm_num
      have e2 : (-1 : ℤ).toNat = 0 := by norm_num
      have e3 : aDp l (xi C.ε) = aDp l ξ * ((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) := by
        rw [hc, mul_comm (c : Per.BdRp l), mul_assoc, Units.mul_inv, mul_one]
      rw [e1, e2, pow_one, pow_zero, e3, map_mul (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l ξ), ← hw, ← hu,
        ← mul_assoc, Units.inv_mul, one_mul]
      simp
    have hvn : ∀ k : ℕ, ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ k ∈ Per.FilD l (-(k : ℤ)) := by
      intro k
      induction k with
      | zero => simpa using hone
      | succ k ih =>
        rw [pow_succ]
        have := hmul _ _ _ _ ih hv
        rwa [show -(k : ℤ) + -1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
    constructor
    · intro h
      have := hmul _ _ _ _ (hvn n) h
      rwa [← mul_assoc, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_mul,
        show -(n : ℤ) + (a + n) = a by ring] at this
    · intro h
      have := hmul _ _ _ _ hwn h
      rwa [add_comm] at this
  · have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    haveI := hfr
    have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hplus : Function.Injective C.jP := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).2.2
    have hloc : Function.Injective (algebraMap (Per.Acris l) (BcrisP l)) := by
      refine IsLocalization.injective (M := Submonoid.powers ((l : ℕ) : Per.Acris l)) (BcrisP l) ?_
      rw [Submonoid.powers_le, mem_nonZeroDivisors_iff]
      have ht := (acris_torsionFree_complete l).1
      exact ⟨ht, fun x hx => ht x (by rw [mul_comm]; exact hx)⟩
    intro x y hxy
    apply hloc
    apply hplus
    apply hinjD
    rw [C.jP_alg, C.jP_alg, ← C.ι_j, ← C.ι_j, hxy]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.JSW

theorem locL_conj_tendsto_one_and_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) →
    (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) →
    Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1)
      (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧
    locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  intro q A B hq hA hB
  set B' := B.map (Units.map (starRingEnd ℂ).toMonoidHom) with hB'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq

  have key : ∀ p ∈ A ×ˢ B', (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(1 : ℂ))) ≠ 0 := by
    intro p hp
    rw [Multiset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [hB', Multiset.mem_map] at h2
    obtain ⟨β, hβ, hpe⟩ := h2
    rw [← hpe]
    have ha := hA _ h1
    have hb := hB _ hβ
    have hnb : ‖((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ)‖ = ‖(β : ℂ)‖ := by
      simp [Units.coe_map]
    have hprod : ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ < q := by
      have h0 : 0 ≤ ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ := by positivity
      by_contra hc
      push_neg at hc
      have : (q : ℝ) * q ≤ (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) :=
        mul_le_mul hc hc (by positivity) h0
      have h3 : (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) = ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 := by ring
      have h4 : ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 < (q : ℝ) * q :=
        mul_lt_mul'' ha hb (by positivity) (by positivity)
      linarith
    intro h0
    have hz : (p.1 : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 : ℂ)) = 1 := by
      linear_combination -h0
    have hn := congrArg norm hz
    rw [Complex.cpow_neg_one, norm_mul, norm_mul, hnb, norm_inv, Complex.norm_natCast, norm_one] at hn
    have hqpos : (0 : ℝ) < q := by linarith
    rw [mul_inv_eq_one₀ hqpos.ne'] at hn
    linarith
  constructor
  · have hc : ∀ p ∈ A ×ˢ B', Tendsto (fun x : ℝ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹) (𝓝[>] 1)
        (𝓝 ((1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-((1 : ℝ) : ℂ)))⁻¹)) := by
      intro p hp
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      apply ContinuousAt.tendsto
      apply ContinuousAt.inv₀
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.const_cpow
        · exact (Complex.continuous_ofReal.neg).continuousAt
        · exact Or.inl hq0
      · simpa using key p hp
    have := tendsto_multiset_prod (A ×ˢ B') hc
    simpa [locL] using this
  · unfold locL
    apply Multiset.prod_ne_zero
    rw [Multiset.mem_map]
    rintro ⟨p, hp, h⟩
    exact inv_ne_zero (key p hp) h
end GlobalTheory.JSW
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DefiniteType

theorem adForms_mul {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (f : G → W) (hf : f ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ)
    (h : G) (k : G) (hk : k ∈ J) : f (h * k) = (χ ⟨k, hk⟩ : ℂ) • f h := by
  have h1 : f (ι 1 * h * k) = (χ ⟨k, hk⟩ : ℂ) • ρ 1 (f h) := hf 1 h ⟨k, hk⟩
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at h1

theorem fin_mem {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).J :=
  hκ.2

theorem chi_eq {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (κ : GA D V) (hk : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J) :
    (((levEnv V β L).χ ⟨_, hk⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ :=
  rfl

theorem ext_mul {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (f : Formalism.IndefR.Bridge.Gf V → c.W) (κ : GA D V) (hκ : κ ∈ GfC V) (h : GA D V)
    (z : ℂ) (hz : f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict κ) = z • f ((finHom V).rangeRestrict h)) :
    c.ext f (h * κ) = z • c.ext f h := by
  have h3 : c.ρ κ⁻¹ = 1 := hc.1 _ ((GfC V).inv_mem hκ)
  have h4 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ := by
    rw [_root_.mul_inv_rev, c.ρ.map_mul, h3, one_mul]
  have h5 : f ((finHom V).rangeRestrict (h * κ)) = z • f ((finHom V).rangeRestrict h) :=
    (congrArg f ((finHom V).rangeRestrict.map_mul h κ)).trans hz
  show c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) = z • c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  rw [h4, h5, map_smul]

theorem ext_mul_lev {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (f : Formalism.IndefR.Bridge.Gf V → c.W)
    (hf : f ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (h : GA D V) :
    c.ext f (h * κ) = levChi V β (flag1L L) κ • c.ext f h :=
  ext_mul c hc f κ hκ.1 h _ (chi_eq β L κ (fin_mem β L κ hκ) ▸
    adForms_mul (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ f hf _ _ (fin_mem β L κ hκ))

theorem hasType_extV : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ),
      HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i t y l κ hκ h
  have hm := (hc.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have h1 := ext_mul_lev (R.cV i) (hc.models.cV i) (R.βV i) (R.datVt i t) ((R.HV i t).e y) hm κ hκ h
  exact (congrArg l h1).trans (map_smul l _ _)

end GlobalTheory.DefiniteType

end
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.involutive_algebra_product_identity : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → (∃ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A), e * e = e ∧ e + (B₁.prod B₂).σ e = 1) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.Swap.identity_of_swap | exact GlobalTheory.UnitLemma.Swap.identity_of_swap | (intros; apply GlobalTheory.UnitLemma.Swap.identity_of_swap <;> assumption)
end

section




open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpVec

theorem exists_letter_of_jump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  intro D HW l _ K s LL h T hC i ζ τ hPt a hJ
  obtain ⟨-, hemb, ι, hComp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hPt
  obtain ⟨-, -, -, hc, hc0⟩ := GlobalTheory.NL.Points.points D HW l K s LL h
  have hC3 := (GlobalTheory.NL.CompD.component_tied (D.locT l) K LL T hc hc0 hC τ ι hComp.2.2 _ hemb).2.2.1
  have hlt : FildR ((D.loc l).PD K) T.ρ τ (a + 1) < FildR ((D.loc l).PD K) T.ρ τ a :=
    lt_of_le_of_ne (GlobalTheory.DeRhamCompare.FildR_succ_le _ _ τ a) hJ
  obtain ⟨w, hwa, hwa1⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd, hdw⟩ := hC3 w hwa.1
  refine ⟨d, hd, ?_, ?_⟩
  · have : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
        w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hwa hdw
  · intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hdis := GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE ((D.loc l).PD K) T.ρ τ
    have hD : w - y ∈ DdRE ((D.loc l).PD K) T.ρ τ := Submodule.sub_mem _ hwa.1 hy.1
    have hS : w - y ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ' := by
      have : w - y = z - (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by
        rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hz hdw
    have h0 : w - y = 0 := Submodule.disjoint_def.1 hdis _ hD hS
    have : w = y := sub_eq_zero.1 h0
    exact hwa1 (this ▸ hy)

end GlobalTheory.NL.JumpVec
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.etalePhiMatrix_decompletion_to_wach : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (r : ℕ) (F : Matrix (Fin r) (Fin r) (RW LL)), IsUnit F → (∀ i j, FixH AI K (F i j)) → ∃ (V : Matrix (Fin r) (Fin r) (RW LL)) (F' : Matrix (Fin r) (Fin r) R.EE), IsUnit V ∧ (∀ i j, FixH AI K (V i j)) ∧ F * V.map (φRW LL) = V * F'.map I.ioE := by
  first | exact @GlobalTheory.HWL.MatDecompl.decompletion | exact GlobalTheory.HWL.MatDecompl.decompletion | (intros; apply GlobalTheory.HWL.MatDecompl.decompletion <;> assumption)
end

section

noncomputable section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.CoreOrth

theorem core (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [IsAlgClosed F] [CharP F l] [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l])
    (hn : ∀ z, ‖tsh z‖ = ‖z‖) (hs : ∀ x, tsh (ι x) = sh x) (hon : ∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z)
    (h : ℕ) (μ : Fin h → ℂ_[l]) (h2 : 2 ≤ h) (hμ : ∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1)
    (hanti : Antitone (fun i => ‖μ i‖)) (hratio : ∀ i j, ‖μ i‖ < l * ‖μ j‖)
    (horth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) :
    ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧
      (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧
      ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  obtain ⟨-, -, -, -, -, hsurj, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hnι : ∀ x, ‖ι x‖ = ‖sh x‖ := fun x => by rw [← hn, hs]
  choose m hm using fun j => hsurj (μ j) (hμ j).2
  obtain ⟨w, hw⟩ := hsurj (l : ℂ_[l]) (by rw [GlobalTheory.PSer.Laws.norm_l]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  set ϖ : F := ι w with hϖdef
  have hϖ : ‖ϖ‖ = (l : ℝ)⁻¹ := by rw [hnι, hw, GlobalTheory.PSer.Laws.norm_l]
  have hϖs : tsh ϖ = l := by rw [hs, hw]
  set lamF : Fin h → F := fun j => ι (m j) with hlamF
  have hnl : ∀ j, ‖lamF j‖ = ‖μ j‖ := fun j => by simp only [lamF, hnι, hm]
  have hmu : ∀ j, sh (m j) = μ j := hm
  have horthF : GlobalTheory.PMonE.Orth l lamF := by
    intro c j hc
    have := GlobalTheory.T.norm_sh_le_sh_int_sum_of_orthogonal l h m (fun i j => by rw [hmu, hmu]; exact hratio i j) (fun c j => by simp only [hmu]; exact horth c j) c j hc
    have e : (∑ i, (c i : F) * lamF i) = ι (∑ i, (c i : Fl l) * m i) := by simp [lamF, map_sum]
    rw [e, hnι, hnι]; exact this
  have hpos : 0 < h := by omega
  obtain ⟨ρ, τ, K, hρ, hτ, hW1, hW2, hW3⟩ := GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero F l h ϖ hpos hϖ lamF
    (fun j => by rw [← norm_pos_iff, hnl]; exact norm_pos_iff.2 (hμ j).1)
    (fun i j hij => by simp only [hnl]; exact hanti hij) horthF (fun i j => by simp only [hnl]; exact hratio i j)
  set S : Set (Fin h → Fl l) := {x | ∀ j, ‖sh (x j)‖ ≤ ρ j} with hSdef
  let η : (Fin h → Fl l) → Fin h → ℂ_[l] := fun x i => ∑ j, sh (m j) * lam h i (x j)
  have hE : ∀ x ∈ S, ∀ i, ‖η x i - tsh (GlobalTheory.PMonE.rowT l ϖ lamF K (fun j => ι (x j)) i)‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro x hx i
    exact GlobalTheory.T.tiltedSeriesRow_sub_untilt_truncatedAdditiveRow l F ι tsh hn hs hon h m x ϖ K τ i (by omega) hϖs (fun j => (hx j).trans_lt (hρ j).2)
      (fun j n => hW1 (fun j => ι (x j)) (fun j => by rw [hnι]; exact hx j) i j n)
  have hpre : ∀ z : Fin h → F, (∀ j, ‖z j‖ ≤ ρ j) → ∃ x ∈ S, (fun j => ι (x j)) = z := by
    intro z hz
    choose x hx using fun j => hon (z j) ((hz j).trans (hρ j).2.le)
    refine ⟨x, fun j => ?_, funext hx⟩
    rw [← hnι, hx]; exact hz j
  have hL1 : ∀ t : Fin h → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro t ht
    choose b hb using fun i => GlobalTheory.T.tiltUntilt_multiplicative_extension_surjective l F ι tsh hn hs hon (t i)
    obtain ⟨z, hz, hrow⟩ := hW2 b (fun i => by rw [← hn, hb]; exact ht i)
    obtain ⟨x, hxS, hxz⟩ := hpre z hz
    refine ⟨x, hxS, fun i => ?_⟩
    have := hE x hxS i
    rwa [hxz, hrow, hb] at this
  obtain ⟨z0, hz0, ⟨j0, hj0⟩, hrow0⟩ := hW3
  obtain ⟨x0, hx0S, hx0z⟩ := hpre z0 hz0
  have hL2 : ∀ i, ‖η x0 i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro i
    have := hE x0 hx0S i
    rwa [hx0z, hrow0, map_zero, sub_zero] at this
  obtain ⟨y, hy0, hyS, hysum⟩ := GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime l (Fin h → Fl l) (Fin h) η τ S hL1 x0 hx0S hL2
  haveI : Nonempty (Fin h) := ⟨⟨0, hpos⟩⟩
  set R : ℝ := Finset.univ.sup' Finset.univ_nonempty ρ with hRdef
  have hρR : ∀ j, ρ j ≤ R := fun j => Finset.le_sup' ρ (Finset.mem_univ j)
  have hR1 : R < 1 := (Finset.sup'_lt_iff _).2 fun j _ => (hρ j).2
  refine ⟨fun j k => y k j, j0, ρ j0, R, (hρ j0).1.le, (hρ j0).2, hR1,
    fun a k => (hyS k a).trans (hρR a), fun k => hyS k j0, ?_, ?_⟩
  · show ρ j0 ^ l ^ h < ‖sh (y 0 j0)‖
    rw [hy0, ← hnι]
    have := congrFun hx0z j0
    rw [this]; exact hj0
  · intro i
    refine GlobalTheory.T.sum_mul_untiltFrobeniusDoubleSeries_eq_zero l h μ i y R (by omega) hR1 (fun k j => (hyS k j).trans (hρR j)) ?_
    have := hysum i
    simpa [η, hmu] using this

end GlobalTheory.CoreOrth

namespace GlobalTheory.CoreOrth

theorem residue_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → (∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1) → Antitone (fun i => ‖μ i‖) → (∀ i j, ‖μ i‖ < l * ‖μ j‖) → (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) → ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧ (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧ ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  intro l _ h μ h2 hμ hanti hratio horth
  obtain ⟨hac, ι, hs, hon⟩ := GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall l
  haveI := hac
  exact core l _ ι (GroundTheory.PAdicHodge.tiltSharp ℂ_[l] l) (fun z => GroundTheory.PAdicHodge.norm_tiltSharp z) hs hon
    h μ h2 hμ hanti hratio horth
end GlobalTheory.CoreOrth

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem potDRL_of_tied : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → PotDRL L := by
  intro L A hT l _ K K' LL h R hc
  obtain ⟨T⟩ := hT l
  exact (GlobalTheory.T.restrict_crystalline_deRham_finiteExt l (L l) (A l) T K K' LL h R.V R.ρ).2.2
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (L l) (A l) T K' LL R.V _ hc).1

end GlobalTheory.Pass
end
