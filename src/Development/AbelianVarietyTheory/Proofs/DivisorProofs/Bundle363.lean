module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle284
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import GroundTheory.LocalFields.Bundle001
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

@[expose] public section

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fderiv_prod_coord {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℂ → ℂ) (L : ι → ℂ →L[ℝ] ℂ) (z : ι → ℂ)
    (hg : ∀ i, HasFDerivAt (g i) (L i) (z i)) :
    DifferentiableAt ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z ∧
    ∀ (j : ι) (v : ℂ), fderiv ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z (Pi.single j v) =
      L j v * ∏ i ∈ Finset.univ.erase j, g i (z i) := by
  have h1 : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun w : ι → ℂ => g i (w i))
      ((L i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i)) z := fun i _ =>
    (hg i).comp z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt
  have h2 := HasFDerivAt.finsetProd h1
  refine ⟨h2.differentiableAt, fun j v => ?_⟩
  rw [h2.fderiv, ContinuousLinearMap.sum_apply, Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem hasFDerivAt_factor (c : ℂ) (a β : ℝ) (h : ℝ → ℂ) (h' : ℂ) (w : ℂ) (hh : HasDerivAt h h' (β * w.im)) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun u : ℂ => Complex.exp (c * ((a * u.re : ℝ) : ℂ)) * h (β * u.im)) L w ∧
      L 1 = c * (a : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h (β * w.im)) ∧
      L I = (β : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h') := by
  have e1 : HasFDerivAt (fun u : ℂ => ((a * u.re : ℝ) : ℂ)) (Complex.ofRealCLM.comp (a • Complex.reCLM)) w :=
    (Complex.ofRealCLM.comp (a • Complex.reCLM)).hasFDerivAt
  have e2 := (e1.const_mul c).cexp
  have e3 : HasFDerivAt (fun u : ℂ => β * u.im) (β • Complex.imCLM) w := (β • Complex.imCLM).hasFDerivAt
  have e4 := hh.hasFDerivAt.comp w e3
  refine ⟨_, e2.mul e4, ?_, ?_⟩
  · simp; ring
  · simp; ring

theorem termQ_fderiv : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  intro F _ _ b ν hb H σ hσ q z hz τ₀
  have hne : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ =>
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  choose L hL hL1 hLI using fun τ : Emb F => hasFDerivAt_factor (2 * (Real.pi : ℂ) * I) (τ ν * τ b) (τ b)
    (iteratedDeriv (q τ) (hTrans σ (τ ν))) _ (z τ) ((H (τ ν) (q τ) _ (hne τ)).1 σ hσ)
  obtain ⟨hd, hf⟩ := fderiv_prod_coord _ L z hL
  refine ⟨hd, ?_, ?_⟩
  · refine (hf τ₀ 1).trans ?_
    unfold termQ
    rw [hL1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀)]
    ring
  · refine (hf τ₀ I).trans ?_
    unfold termQ
    rw [hLI, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), mul_assoc]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun τ hτ => ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hτ)]

end GlobalTheory.HeckeTwo
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem iteratedDeriv_hTrans_eq_sum
    (h1 : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y)
    (n : ℝ) (k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ → ℂ) (ab : ι → ℕ × ℕ),
      (∀ i, Differentiable ℂ (c i)) ∧ (∀ i, 2 ≤ (ab i).1 + (ab i).2) ∧
      ∀ σ ∈ halfPlane, ∀ y : ℝ, y ≠ 0 →
        iteratedDeriv k (hTrans σ n) y = ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y := by
  induction k with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => (2, 0), fun _ => by fun_prop,
      fun _ => by simp, fun σ _ y _ => ?_⟩
    simp [hTransAB_two_zero]
  | succ k ih =>
    obtain ⟨ι, _, c, ab, hc, hab, h⟩ := ih
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i σ => c i σ * (I * (-((ab i).1 : ℂ) - σ)))
        (fun i σ => c i σ * (I * (((ab i).2 : ℂ) + σ))),
      Sum.elim (fun i => ((ab i).1 + 1, (ab i).2)) (fun i => ((ab i).1, (ab i).2 + 1)),
      ?_, ?_, ?_⟩
    · rintro (i | i)
      · have := hc i
        simp only [Sum.elim_inl]; fun_prop
      · have := hc i
        simp only [Sum.elim_inr]; fun_prop
    · rintro (i | i)
      · have := hab i
        simp only [Sum.elim_inl]; omega
      · have := hab i
        simp only [Sum.elim_inr]; omega
    · intro σ hσ y hy
      have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
          fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
        filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
      have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
      rw [iteratedDeriv_succ, hd.deriv, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      ring

theorem iteratedDeriv_hTrans_jet :
    (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  intro h1 h2 n k y hy
  obtain ⟨ι, _, c, ab, hc, hab, h⟩ := iteratedDeriv_hTrans_eq_sum h1 n k
  refine ⟨fun σ hσ => ?_, ?_⟩
  · have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
        fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
      filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
    have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
    rw [iteratedDeriv_succ]
    exact hd.differentiableAt.hasDerivAt
  · refine DifferentiableOn.congr
      (f := fun σ => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y) ?_ (fun σ hσ => h σ hσ y hy)
    exact DifferentiableOn.fun_sum fun i _ =>
      (hc i).differentiableOn.mul (h2 _ _ n y (hab i) hy)

end GlobalTheory.HeckeTwo
end

section

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_v_le {c : L}
    (hc : ∀ m : ℕ, Valued.v c ≤ ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    c = 0 := by
  by_contra h0
  have hv : Valued.v c ≠ 0 := (_root_.map_ne_zero _).2 h0
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.1 hv
  have := hc (1 - Multiplicative.toAdd g).toNat
  rw [← hg, WithZero.coe_le_coe] at this
  have h2 : Multiplicative.toAdd g ≤ -(((1 - Multiplicative.toAdd g).toNat : ℕ) : ℤ) := by
    have := Multiplicative.toAdd_le.2 this
    simpa using this
  omega

theorem int_eq_zero_of_forall_dvd {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c : intL L}
    (hc : ∀ m : ℕ, piO h ^ m ∣ c) : c = 0 := by
  refine Subtype.ext (eq_zero_of_forall_v_le fun m => ?_)
  obtain ⟨d, hd⟩ := hc m
  have hd' : (c : L) = ϖ ^ m * (d : L) := by
    rw [hd]; simp
  have hdv : Valued.v (d : L) ≤ 1 := d.2
  rw [hd', map_mul, map_pow, h.2.2.2.1]
  calc ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * Valued.v (d : L)
      ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * 1 := by gcongr
    _ = _ := by
      rw [mul_one, ← WithZero.coe_pow, ← ofAdd_nsmul]
      congr 2
      simp

theorem eq_zero_of_forall_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P) (ha : ∀ m, a ∈ piPow h P m) : a = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_dvd h fun m => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (ha m)
  refine ⟨(GlobalTheory.UTr.powBasis P).repr b i, ?_⟩
  have he : b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m =
      (piO h ^ m) • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  change b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m = a at hb
  rw [← hb, he, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem sep : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ)
    (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P),
    (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 :=
  fun _ _ _ _ _ _ h P a ha => eq_zero_of_forall_mem_piPow h P a ha

end GlobalTheory.NormEq
end
end

section

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

theorem exists_norm_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  intro L _ _ σ ϖ q h P m hm x hx hxm
  obtain ⟨x₀, hx₀, hv⟩ := h.2.2.2.2.1
  have hve : Valued.v (x₀ - σ x₀) = 1 := by rw [← Valuation.map_neg, neg_sub]; exact hv
  have he : x₀ - σ x₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hve; exact zero_ne_one hve
  have hcO : x₀ * (x₀ - σ x₀)⁻¹ ∈ intL L := by
    change Valued.v (x₀ * (x₀ - σ x₀)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, hve, inv_one, mul_one]; exact hx₀
  let cO : intL L := ⟨_, hcO⟩
  have hcs : cO + sigO σ h.2.1 cO = 1 := by
    apply Subtype.ext
    change x₀ * (x₀ - σ x₀)⁻¹ + σ (x₀ * (x₀ - σ x₀)⁻¹) = 1
    have e2 : σ x₀ - x₀ = -(x₀ - σ x₀) := by ring
    rw [map_mul, map_inv₀, map_sub, h.1, e2, inv_neg]
    field_simp
    ring
  set ι := algebraMap (intL L) (GlobalTheory.UTr.Alg P) with hι
  set πA := ι (piO h) with hπA
  have hconjπ : GlobalTheory.UTr.conj P πA = πA := by
    rw [hπA, GlobalTheory.UTr.conj_algebraMap]; congr 1; exact Subtype.ext h.2.2.1
  have hconjc : GlobalTheory.UTr.conj P (ι cO) + ι cO = 1 := by
    have := congrArg ι hcs
    rw [map_add (f := _), map_one] at this
    rw [hι, GlobalTheory.UTr.conj_algebraMap]; rw [← this]; ring
  have h1 : (x : GlobalTheory.UTr.Alg P) - 1 ∈ Ideal.span {πA ^ m} := hxm
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hxc : GlobalTheory.UTr.conj P (x : GlobalTheory.UTr.Alg P) = x := (GlobalTheory.UTr.mem_plus (P := P)).1 hx
  have hca : πA ^ m * GlobalTheory.UTr.conj P a = πA ^ m * a := by
    have := congrArg (GlobalTheory.UTr.conj P) ha
    rw [map_mul, map_pow, hconjπ, map_sub, map_one, hxc] at this
    rw [mul_comm, this, ← ha, mul_comm]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hu1 : (1 + πA ^ (k + 1) * (ι cO * a)) - 1 ∈ GlobalTheory.NormEq.piPow h P (k + 1) := by
    rw [add_sub_cancel_left]; exact Ideal.mem_span_singleton'.2 ⟨ι cO * a, mul_comm _ _⟩
  refine ⟨(GlobalTheory.NormEq.isUnit_of_sub_one_mem h P hm hu1).unit, hu1, ?_⟩
  change (x : GlobalTheory.UTr.Alg P) - (1 + πA ^ (k + 1) * (ι cO * a)) *
    GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) ∈ Ideal.span {πA ^ (k + 1 + 1)}
  have e1 : GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) =
      1 + πA ^ (k + 1) * (GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a) := by
    rw [map_add (f := _), map_one, map_mul, map_pow, hconjπ, map_mul]
  rw [e1, Ideal.mem_span_singleton']
  refine ⟨-(πA ^ k * ι cO * a * GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a), ?_⟩
  linear_combination ha + GlobalTheory.UTr.conj P (ι cO) * hca + πA ^ (k + 1) * a * hconjc

end GlobalTheory.NormEq
end
end

section

open Polynomial Matrix Formalism.UG

noncomputable section

open Filter Topology

namespace GlobalTheory.NormEq.Cmpl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_pow_lt {w γ : WithZero (Multiplicative ℤ)}
    (hw : w = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (hγ : γ ≠ 0) :
    ∃ N : ℕ, w ^ N < γ := by
  subst hw
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hγ
  refine ⟨(-Multiplicative.toAdd g).toNat + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe, ← ofAdd_toAdd g, ← ofAdd_nsmul, Multiplicative.ofAdd_lt]
  simp only [toAdd_ofAdd, smul_neg, nsmul_eq_mul, mul_one]
  omega

theorem ball_mem_nhds_of_ne {x c : L} (hc : c ≠ 0) : {y | Valued.v (y - x) < Valued.v c} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c ≠ 0 := by simp [hc]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem exists_lim_of_cauchy [CompleteSpace L] {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (s : ℕ → L) (hsO : ∀ n, Valued.v (s n) ≤ 1)
    (hs : ∀ N : ℕ, ∃ M, ∀ m ≥ M, ∀ n ≥ M, Valued.v (s n - s m) ≤ Valued.v ϖ ^ N) :
    ∃ ℓ, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) ≤ Valued.v ϖ ^ N := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hcs : CauchySeq s := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) γ.1
    have hc' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c = γ.1 := hc
    have hc0 : Valued.v c ≠ 0 := by
      intro h0
      rw [(Valued.v).zero_iff.mp h0, map_zero] at hc'
      exact γ.ne_zero hc'.symm
    obtain ⟨N, hN⟩ := exists_pow_lt hϖ hc0
    obtain ⟨M, hM⟩ := hs N
    refine ⟨M, fun m hm n hn => ?_⟩
    change (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict (s n - s m) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact lt_of_le_of_lt (hM m hm n hn) hN
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  have hev : ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) < Valued.v ϖ ^ N := fun N => by
    have := hℓ (ball_mem_nhds_of_ne (x := ℓ) (pow_ne_zero N hϖ0))
    simpa [map_pow] using this
  refine ⟨ℓ, ?_, fun N => (hev N).mono fun n hn => hn.le⟩
  obtain ⟨n, hn⟩ := (hev 0).exists
  rw [pow_zero] at hn
  have e : ℓ = s n - (s n - ℓ) := by ring
  rw [e]
  exact (Valued.v.map_sub _ _).trans (max_le (hsO n) hn.le)

variable {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1))

theorem mem_piPow_iff {N : ℕ} {a : GlobalTheory.UTr.Alg P} :
    a ∈ piPow h P N ↔ ∀ i, Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : intL L) : L) ≤ Valued.v ϖ ^ N := by
  with_unfolding_all
    unfold GlobalTheory.UTr.Alg at *
    have hϖ0 : ϖ ≠ 0 := fun h0 => by
      have := h.2.2.2.1; rw [h0, map_zero] at this; exact WithZero.zero_ne_coe this
    constructor
    · intro ha i
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      set_option backward.isDefEq.respectTransparency false in
        rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Subring.coe_mul,
        SubmonoidClass.coe_pow, coe_piO, map_mul, map_pow]
      calc _ ≤ Valued.v ϖ ^ N * 1 := mul_le_mul' le_rfl (((GlobalTheory.UTr.powBasis P).repr c i).2)
        _ = _ := mul_one _
    · intro ha
      have hϖN : ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ0
      let d : Fin P.1.natDegree → intL L := fun i => ⟨((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N, by
        change Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N) ≤ 1
        rw [map_div₀, map_pow]
        exact (div_le_one₀ (zero_lt_iff.mpr (pow_ne_zero _ ((Valued.v).ne_zero_iff.mpr hϖ0)))).mpr (ha i)⟩
      refine Ideal.mem_span_singleton'.mpr ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm d, ?_⟩
      refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
      have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm d) i = d i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      set_option backward.isDefEq.respectTransparency false in
        rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hd]
      apply Subtype.ext
      rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_piO]
      exact mul_div_cancel₀ _ hϖN

theorem eq_zero_of_forall_mem_piPow {z : GlobalTheory.UTr.Alg P} (hz : ∀ N, z ∈ piPow h P N) : z = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hne
  have hne' : (((GlobalTheory.UTr.powBasis P).repr z i : intL L) : L) ≠ 0 := fun h0 => hne (Subtype.ext h0)
  obtain ⟨N, hN⟩ := exists_pow_lt h.2.2.2.1 ((Valued.v).ne_zero_iff.mpr hne')
  exact absurd ((mem_piPow_iff h P).mp (hz N) i) (not_le.mpr hN)

theorem exists_lim_alg [CompleteSpace L] (a : ℕ → GlobalTheory.UTr.Alg P)
    (ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, a n - a m ∈ piPow h P N) :
    ∃ y, ∀ N, ∀ᶠ n in atTop, a n - y ∈ piPow h P N := by
  have hco : ∀ i, ∃ ℓ : L, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop,
      Valued.v ((((GlobalTheory.UTr.powBasis P).repr (a n) i : intL L) : L) - ℓ) ≤ Valued.v ϖ ^ N := by
    intro i
    refine exists_lim_of_cauchy h.2.2.2.1 _ (fun n => ((GlobalTheory.UTr.powBasis P).repr (a n) i).2) fun N => ?_
    obtain ⟨M, hM⟩ := ha N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := (mem_piPow_iff h P).mp (hM m hm n hn) i
    rwa [map_sub, Finsupp.sub_apply, AddSubgroupClass.coe_sub] at this
  choose ℓ hℓO hℓ using hco
  refine ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩), fun N => ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => hℓ i N)] with n hn
  rw [mem_piPow_iff]
  intro i
  have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩)) i =
      ⟨ℓ i, hℓO i⟩ := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, hd, AddSubgroupClass.coe_sub]
  exact hn i

end GlobalTheory.NormEq.Cmpl

namespace GlobalTheory.NormEq


open Cmpl in
theorem filtrationComplete_filt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  with_unfolding_all
    intro L _ _ _ σ ϖ q h P x hx
    have ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, (((x n).val : (AdjoinRoot P.1)) - (x m).val) ∈ piPow h P N := by
      intro N
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 : ((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1 ∈ piPow h P N := hM m hm n hn
      have e : ((x n).val : (AdjoinRoot P.1)) - x m = ((x m).val : (AdjoinRoot P.1)) * (((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1) := by
        rw [div_eq_mul_inv, Units.val_mul]
        linear_combination (-((x n).val : (AdjoinRoot P.1))) * (x m).mul_inv
      rw [e]; exact Ideal.mul_mem_left _ _ h1
    have hb : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M,
        (((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - ((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) ∈ piPow h P N := by
      intro N
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 : ((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1 ∈ piPow h P N := hM m hm n hn
      have e : (((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - ((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) =
          -(((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) * (((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1) := by
        rw [div_eq_mul_inv, Units.val_mul]
        linear_combination (((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) * (x n).inv_mul
      rw [e]; exact Ideal.mul_mem_left _ _ h1
    obtain ⟨y, hy⟩ := exists_lim_alg h P _ ha
    obtain ⟨y', hy'⟩ := exists_lim_alg h P _ hb
    unfold GlobalTheory.UTr.Alg at y y' hy hy'
    have hyy : y * y' = 1 := by
      rw [← sub_eq_zero]
      refine GlobalTheory.NormEq.Cmpl.eq_zero_of_forall_mem_piPow h P fun N => ?_
      obtain ⟨n, hn1, hn2⟩ := ((hy N).and (hy' N)).exists
      have e : y * y' - 1 = -(((x n).val : (AdjoinRoot P.1)) - y) * y' -
          ((x n).val : (AdjoinRoot P.1)) * ((((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - y') := by
        linear_combination (x n).mul_inv
      rw [e]
      exact (piPow h P N).sub_mem ((piPow h P N).mul_mem_right _ ((piPow h P N).neg_mem hn1))
        ((piPow h P N).mul_mem_left _ hn2)
    refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, fun N => ?_⟩
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hy N)
    refine ⟨M, fun n hn => ?_⟩
    rw [mem_filt, div_eq_mul_inv, Units.val_mul, Units.inv_mk, Units.val_mk]
    have e : ((x n).val : (AdjoinRoot P.1)) * y' - 1 = (((x n).val : (AdjoinRoot P.1)) - y) * y' := by
      linear_combination hyy
    rw [e]
    exact (piPow h P N).mul_mem_right _ (hM n hn)

end GlobalTheory.NormEq
end
end
