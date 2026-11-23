module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.MvPolynomial.Tower

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < WithZero.exp m) :
    a ≤ WithZero.exp (m - 1) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem relIndex_hiUnits_succ_le :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ),
      w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) →
      (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧
        (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  intro K _ w π R n hπ hR
  have hπn : w (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hπn0 : w (π ^ n) ≠ 0 := by rw [hπn]; exact WithZero.exp_ne_zero
  have hπn0' : π ^ n ≠ 0 := by
    intro h; rw [h] at hπn0; simp at hπn0
  have hex : ∀ x : hiUnits w n, ∃ r : R, w ((((x : Kˣ) : K) - 1) / π ^ n - r) < 1 := by
    intro x
    have hx : w (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := x.2.2
    obtain ⟨r, hr, h⟩ := hR ((((x : Kˣ) : K) - 1) / π ^ n) (by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hπn0), hπn]; exact hx)
    exact ⟨⟨r, hr⟩, h⟩
  choose f hf using hex
  have key : ∀ x y : hiUnits w n, f x = f y →
      x⁻¹ * y ∈ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) := by
    intro x y hxy
    have hx1 : w ((x : Kˣ) : K) = 1 := x.2.1
    have hy1 : w ((y : Kˣ) : K) = 1 := y.2.1
    have h1 := hf x
    have h2 := hf y
    rw [← hxy] at h2
    have h3 := w.map_sub_lt h2 h1
    have h4 : (((y : Kˣ) : K) - 1) / π ^ n - (f x : K) -
        ((((x : Kˣ) : K) - 1) / π ^ n - (f x : K)) =
        (((y : Kˣ) : K) - ((x : Kˣ) : K)) / π ^ n := by ring
    rw [h4, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hπn0), hπn] at h3
    have h5 := le_exp_sub_one_of_lt_exp h3
    rw [Subgroup.mem_subgroupOf]
    have hv : ((((x⁻¹ * y : hiUnits w n) : Kˣ)) : K) =
        ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) := by simp
    refine ⟨by rw [hv, map_mul, map_inv₀, hx1, hy1]; simp, ?_⟩
    have hx0 : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h6 : ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) - 1 =
        ((x : Kˣ) : K)⁻¹ * (((y : Kˣ) : K) - ((x : Kˣ) : K)) := by
      field_simp
    rw [hv, h6, map_mul, map_inv₀, hx1, inv_one, one_mul]
    refine h5.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hinj : Function.Injective
      (fun q : hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) => f q.out) := by
    intro p q hpq
    have := key _ _ hpq
    rw [← QuotientGroup.eq] at this
    simpa using this
  have hfin : Finite (hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n)) :=
    Finite.of_injective _ hinj
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := R), Fintype.card_coe] at this
    exact this

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
theorem _root_.GlobalTheory.QNorm.IsQuad.coord_indep
    (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (a b : F)
    (hab : algebraMap F E a + algebraMap F E b * θ = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply h.nonsq
    refine ⟨-a / b, (algebraMap F E).injective ?_⟩
    have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
    have hθ : θ = -algebraMap F E a / algebraMap F E b := by
      field_simp
      linear_combination hab
    rw [← h.sq, hθ]
    simp [map_div₀, map_neg]
    ring
  subst hb
  refine ⟨(algebraMap F E).injective ?_, rfl⟩
  simpa using hab

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
theorem _root_.GlobalTheory.QNorm.IsQuad.root_ne_zero (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) :
    θ ≠ 0 := by
  intro hθ
  apply h.nonsq
  refine ⟨0, (algebraMap F E).injective ?_⟩
  rw [← h.sq, hθ]
  simp

end


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.isQuad_basic : ∀ (F E : Type) [Field F] [CharZero F] [Field E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧
    (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧
    (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧
    (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧
    (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧
    Module.finrank F E = 2 := by
  intro F E _ _ _ _ δ θ σ h
  have t1 := h.coord_indep
  have hθ := h.root_ne_zero
  have hc := h.conj
  have hs := h.sq
  refine ⟨?_, ?_, t1, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    simp [AlgEquiv.commutes, hc]
  · intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc] at hx
    have := t1 0 (2 * b) (by simp only [map_zero, map_mul, map_ofNat]; linear_combination -hx)
    have hb : b = 0 := by simpa using this.2
    exact ⟨a, by simp [hb]⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    refine ⟨a, b, ?_⟩
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc, map_sub, map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hs
  · intro x hx
    by_cases h1 : x = -1
    · refine ⟨θ, hθ, ?_⟩
      rw [hc, h1, div_neg, div_self hθ]
    · have hy : (1 + x) ≠ 0 := fun h0 => h1 (by linear_combination h0)
      have hσy : σ (1 + x) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ σ.injective]
      refine ⟨1 + x, hy, ?_⟩
      rw [eq_div_iff hσy, map_add (f := _), map_one]
      linear_combination hx
  · rintro u ⟨y, hy⟩
    obtain ⟨a, b, rfl⟩ := h.span y
    have := t1 (u - a ^ 2 - b ^ 2 * δ) (-(2 * a * b)) (by
      simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat]
      linear_combination hy + (algebraMap F E b) ^ 2 * hs)
    have h2 : a * b = 0 := by
      have h3 := this.2
      have h4 : (2 : F) * (a * b) = 0 := by linear_combination -h3
      simpa using h4
    have hu : u = a ^ 2 + b ^ 2 * δ := by linear_combination this.1
    rcases mul_eq_zero.1 h2 with ha | hb
    · right; exact ⟨b * δ, by rw [hu, ha]; ring⟩
    · left; exact ⟨a, by rw [hu, hb]; ring⟩
  · have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply t1
      simpa [Algebra.smul_def] using hst
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ]) := by
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Matrix.range_cons_cons_empty]
      refine Submodule.mem_span_pair.2 ⟨a, b, ?_⟩
      simp [Algebra.smul_def]
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma idempotent_corner_part_mul {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) :
    (E * g * E + (1 - E) * g * (1 - E)) * (E * h * E + (1 - E) * h * (1 - E)) =
      E * (g * h) * E + (1 - E) * (g * h) * (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, h2, sub_zero]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * (g * h) * E = E * g * E * h * E := by
    calc E * (g * h) * E = E * g * (E + F) * h * E := by rw [hs]; noncomm_ring
      _ = E * g * E * h * E + E * g * (F * h * E) := by noncomm_ring
      _ = _ := by rw [hh, mul_zero, add_zero]
  have a2 : F * (g * h) * F = F * g * F * h * F := by
    calc F * (g * h) * F = F * g * (E + F) * h * F := by rw [hs]; noncomm_ring
      _ = (F * g * E) * h * F + F * g * F * h * F := by noncomm_ring
      _ = _ := by rw [hg, zero_mul, zero_mul, zero_add]
  rw [a1, a2]
  calc _ = E * g * (E * E) * h * E + E * g * (E * F) * h * F + F * g * (F * E) * h * E
        + F * g * (F * F) * h * F := by noncomm_ring
    _ = _ := by rw [hE, h1, h2, h3]; noncomm_ring

private lemma idempotent_corner_sum_one {A : Type} [Ring A] (E : A) (hE : E * E = E) :
    E * 1 * E + (1 - E) * 1 * (1 - E) = 1 := by
  have : E * 1 * E + (1 - E) * 1 * (1 - E) = 1 + 2 * (E * E - E) := by noncomm_ring
  rw [this, hE, sub_self, mul_zero, add_zero]

private lemma idempotent_corner_part_inv {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) (hgh : g * h = 1) :
    g * (E * h * E + (1 - E) * h * (1 - E)) = 1 + E * (-(g * E * h) * (1 - E)) := by
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * g * E = g * E := by
    calc E * g * E = E * g * E + F * g * E := by rw [hg, add_zero]
      _ = (E + F) * g * E := by noncomm_ring
      _ = _ := by rw [hs, one_mul]
  have a2 : h = (E * h * E + F * h * F) + E * h * F := by
    calc h = (E + F) * h * (E + F) := by rw [hs, one_mul, mul_one]
      _ = (E * h * E + F * h * F) + E * h * F + F * h * E := by noncomm_ring
      _ = _ := by rw [hh, add_zero]
  have a3 : g * (E * h * E + F * h * F) + g * (E * h * F) = 1 := by
    rw [← mul_add, ← a2, hgh]
  calc g * (E * h * E + F * h * F) = 1 - g * E * h * F := by
        rw [← a3]; noncomm_ring
    _ = 1 - E * g * E * h * F := by rw [a1]
    _ = _ := by noncomm_ring

theorem isPre_blk_image :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsPre Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → IsPre (blk e '' Γ) := by
  intro ι _ _ Γ e hΓ he htri
  have hE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, he]
  have hmul : ∀ g ∈ Γ, ∀ h ∈ Γ, blk e g * blk e h = blk e (g * h) := fun g hg h hh =>
    idempotent_corner_part_mul _ g h hE (htri g hg) (htri h hh)
  have hone : blk e (1 : Matrix ι ι ℂ) = 1 := idempotent_corner_sum_one _ hE
  have hga : ∀ g ∈ Γ, g * g.adjugate = 1 := fun g hg => by
    rw [Matrix.mul_adjugate, hΓ.det_eq g hg, one_smul]
  have hinv : ∀ g ∈ Γ, blk e g * blk e g.adjugate = 1 := fun g hg => by
    rw [hmul g hg _ (hΓ.adj_mem g hg), hga g hg, hone]
  have hdet : ∀ g ∈ Γ, (blk e g).det = 1 := fun g hg => by
    have h1 := idempotent_corner_part_inv _ g g.adjugate hE (htri g hg) (htri _ (hΓ.adj_mem g hg)) (hga g hg)
    have h2 : (g * blk e g.adjugate).det = 1 := by
      unfold blk
      rw [h1, Matrix.det_one_add_mul_comm, mul_assoc, sub_mul, one_mul, hE, sub_self, mul_zero,
        add_zero, Matrix.det_one]
    rw [Matrix.det_mul, hΓ.det_eq g hg, one_mul] at h2
    have h3 := congrArg Matrix.det (hinv g hg)
    rwa [Matrix.det_mul, h2, mul_one, Matrix.det_one] at h3
  refine ⟨⟨1, hΓ.one_mem, hone⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g * h, hΓ.mul_mem g hg h hh, (hmul g hg h hh).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨g.adjugate, hΓ.adj_mem g hg, ?_⟩
    calc blk e g.adjugate = ((blk e g).adjugate * blk e g) * blk e g.adjugate := by
          rw [Matrix.adjugate_mul, hdet g hg, one_smul, one_mul]
      _ = _ := by rw [mul_assoc, hinv g hg, mul_one]
  · rintro _ ⟨g, hg, rfl⟩
    exact hdet g hg
  · rintro σ _ ⟨g, hg, rfl⟩
    refine ⟨g.map σ, hΓ.aut_mem σ g hg, ?_⟩
    have hσ : (σ : ℂ →+* ℂ).mapMatrix (e.map (algebraMap ℚ ℂ)) = e.map (algebraMap ℚ ℂ) := by
      ext i j
      simp
    change _ = (σ : ℂ →+* ℂ).mapMatrix (blk e g)
    unfold blk
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, map_sub, map_one, hσ]
    rfl

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem peirce_block_decomposition {A : Type*} [Ring A] (E F : A) (hE : E * E = E) (hF : F * F = F) (hEF : E * F = 0)
    (hFE : F * E = 0) (h1 : E + F = 1) :
    E * 1 * E + F * 1 * F = 1 ∧
    (∀ x y : A, F * x * E = 0 → F * y * E = 0 →
      E * (x * y) * E + F * (x * y) * F = (E * x * E + F * x * F) * (E * y * E + F * y * F) ∧
        F * (x * y) * E = 0) ∧
    (∀ x : A, F * x * E = 0 → x = (E * x * E + F * x * F) + E * x * F) ∧
    (∀ x : A, E * (E * x * E + F * x * F) * E + F * (E * x * E + F * x * F) * F = E * x * E + F * x * F) := by
  have hE' : ∀ z, E * (E * z) = E * z := fun z => by rw [← mul_assoc, hE]
  have hF' : ∀ z, F * (F * z) = F * z := fun z => by rw [← mul_assoc, hF]
  have hEF' : ∀ z, E * (F * z) = 0 := fun z => by rw [← mul_assoc, hEF, zero_mul]
  have hFE' : ∀ z, F * (E * z) = 0 := fun z => by rw [← mul_assoc, hFE, zero_mul]
  refine ⟨by rw [mul_one, mul_one, hE, hF, h1], ?_, ?_, ?_⟩
  · intro x y hx hy
    have hxy : x * y = x * (E + F) * y := by rw [h1, mul_one]
    have hx' : ∀ z, F * (x * (E * z)) = 0 := fun z => by
      rw [← mul_assoc, ← mul_assoc, hx, zero_mul]
    have hy' : F * (y * E) = 0 := by rw [← mul_assoc, hy]
    rw [hxy]
    constructor
    · simp only [mul_add, add_mul, mul_assoc, hE', hF', hEF', hFE', hx', hy', mul_zero, add_zero, zero_add]
    · simp only [mul_add, add_mul, mul_assoc, hx', hy', mul_zero, zero_mul, add_zero]
  · intro x hx
    calc x = (E + F) * x * (E + F) := by rw [h1, one_mul, mul_one]
      _ = E * x * E + F * x * F + E * x * F + F * x * E := by noncomm_ring
      _ = _ := by rw [hx, add_zero]
  · intro x
    simp only [mul_add, add_mul, mul_assoc, hE', hF', hEF', hFE', hE, hF, add_zero, zero_add]

theorem blk_mul_of_triangular : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R], e * e = e → blk e (1 : Matrix ι ι R) = 1 ∧ (∀ x y : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → (1 - e.map (algebraMap ℚ R)) * y * e.map (algebraMap ℚ R) = 0 → blk e (x * y) = blk e x * blk e y ∧ (1 - e.map (algebraMap ℚ R)) * (x * y) * e.map (algebraMap ℚ R) = 0) ∧ (∀ x : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → x = blk e x + e.map (algebraMap ℚ R) * x * (1 - e.map (algebraMap ℚ R))) ∧ (∀ x : Matrix ι ι R, blk e (blk e x) = blk e x) ∧ ∀ γ : Matrix ι ι ℚ, blk e (γ.map (algebraMap ℚ R)) = (blk e γ).map (algebraMap ℚ R) := by
  intro ι _ _ e R _ _ he
  have hE : e.map (algebraMap ℚ R) * e.map (algebraMap ℚ R) = e.map (algebraMap ℚ R) := by
    rw [← Matrix.map_mul, he]
  obtain ⟨h1, h2, h3, h4⟩ := peirce_block_decomposition (e.map (algebraMap ℚ R)) (1 - e.map (algebraMap ℚ R)) hE
    (by rw [sub_mul, mul_sub, mul_sub, hE]; simp) (by rw [mul_sub, hE]; simp)
    (by rw [sub_mul, hE]; simp) (by simp)
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro γ
  have hid : e.map (algebraMap ℚ ℚ) = e := by
    ext i j
    simp
  change _ = (algebraMap ℚ R).mapMatrix (blk e γ)
  unfold blk
  rw [hid]
  simp only [map_add (f := _), map_mul, map_sub, map_one, RingHom.mapMatrix_apply]

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_exp_two_mul_of_eq_sq {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {u y : K}
    (hy : y ≠ 0) (h : w u = w (y ^ 2)) : ∃ n : ℤ, w u = WithZero.exp (2 * n) := by
  refine ⟨WithZero.log (w y), ?_⟩
  rw [h, map_pow, two_mul, WithZero.exp_add, WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hy),
    sq]


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.evenNorms_one_add_four_mul :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 →
      (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) →
        _root_.GlobalTheory.QNorm.EvenNorms w (1 + 4 * ρ) := by
  intro K _ w ρ h2 hρ hroot a b hab
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr rfl)
    exact exists_exp_two_mul_of_eq_sq w ha (by congr 1; ring)
  · set t := (a - b) / (2 * b) with ht_def
    have hfac : a ^ 2 - (1 + 4 * ρ) * b ^ 2 = (2 * b) ^ 2 * (t ^ 2 + t - ρ) := by
      rw [ht_def]
      field_simp
      ring
    by_cases ht : w t ≤ 1
    · exact exists_exp_two_mul_of_eq_sq w (mul_ne_zero h2 hb)
        (by rw [hfac, map_mul, hroot t ht, mul_one])
    · push_neg at ht
      have ht0 : t ≠ 0 := by
        rintro h
        rw [h, map_zero] at ht
        exact not_lt_of_ge zero_le' ht
      have hlt : w (t - ρ) < w (t ^ 2) := by
        calc w (t - ρ) ≤ max (w t) (w ρ) := Valuation.map_sub w t ρ
          _ = w t := max_eq_left (hρ.trans ht.le)
          _ < w t * w t := lt_mul_self ht
          _ = w (t ^ 2) := by rw [map_pow, sq]
      have hval : w (t ^ 2 + t - ρ) = w (t ^ 2) := by
        rw [add_sub_assoc]
        exact Valuation.map_add_eq_of_lt_left w hlt
      refine exists_exp_two_mul_of_eq_sq w (y := 2 * b * t) (mul_ne_zero (mul_ne_zero h2 hb) ht0) ?_
      rw [hfac, map_mul, hval, ← map_mul]
      congr 1
      ring

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatPts


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
lemma _root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap {ι R : Type} [CommRing R] [Algebra ℚ R]
    (f : MvPolynomial (ι × ι) ℚ) (γ : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.ev f (γ.map (algebraMap ℚ R)) = algebraMap ℚ R (_root_.GlobalTheory.ClassFin.ev f γ) := by
  unfold _root_.GlobalTheory.ClassFin.ev
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
  intro ι _ _ Γ
  refine ⟨fun γ hγ => ?_, fun R _ _ γ hγ => ?_⟩
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq]
    intro f hf
    have h := hf _ hγ
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap] at h
    exact (algebraMap ℚ ℂ).injective (by rw [h, map_zero])
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq] at hγ ⊢
    intro f hf
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap, hγ f hf, map_zero]

end GlobalTheory.ClassFin.RatPts
end
