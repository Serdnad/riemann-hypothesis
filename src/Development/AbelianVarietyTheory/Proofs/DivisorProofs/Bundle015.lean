module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

section

open IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.FinRingNorm

theorem field_case (F : Type) [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (d s : F) (hd : d ≠ 0) :
    ∃ a b : F, a ^ 2 - d * b ^ 2 = s := by
  classical
  cases nonempty_fintype F
  have hc : ringChar F ≠ 2 := by
    intro h; apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this; exact_mod_cast this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F) (f := X ^ 2)
    (g := -(C d * X ^ 2) - C s) (by simp) (by compute_degree!) (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  simp only [eval_pow, eval_X, eval_sub, eval_neg, eval_mul, eval_C] at hab
  linear_combination hab

theorem reduced_case (S : Type) [CommRing S] [Finite S] [IsReduced S] (h2 : IsUnit (2 : S))
    (d s : S) (hd : IsUnit d) : ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  classical
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 - (Ideal.Quotient.mk I.asIdeal d) * b ^ 2 = Ideal.Quotient.mk I.asIdeal s := by
    intro I
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    have h2' : (2 : S ⧸ I.asIdeal) ≠ 0 := by
      have := (h2.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
      rwa [map_ofNat] at this
    exact field_case _ h2' _ _ (hd.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
  choose A B hAB using key
  refine ⟨(IsArtinianRing.equivPi S).symm A, (IsArtinianRing.equivPi S).symm B, ?_⟩
  apply (IsArtinianRing.equivPi S).injective
  funext I
  simp only [map_sub, map_mul, map_pow, AlgEquiv.apply_symm_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.pow_apply]
  exact hAB I

theorem finiteRing_sq_sub_mul_sq_eq_of_card (n : ℕ) : ∀ (S : Type) [CommRing S] [Finite S], Nat.card S = n → IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn h2 d s hd hs
  by_cases hred : IsReduced S
  · exact reduced_case S h2 d s hd

  obtain ⟨x, hx0, hx2⟩ : ∃ x : S, x ≠ 0 ∧ x ^ 2 = 0 := by
    rw [isReduced_iff] at hred
    push_neg at hred
    obtain ⟨y, ⟨k, hk⟩, hy⟩ := hred
    classical
    have hex : ∃ m, y ^ m = 0 := ⟨k, hk⟩
    let m := Nat.find hex
    have hm : y ^ m = 0 := Nat.find_spec hex
    have hm0 : m ≠ 0 := by
      intro h
      have : y ^ m = 1 := by rw [h, pow_zero]
      apply hy
      rw [← mul_one y, ← this, hm, mul_zero]
    have hm1 : m ≠ 1 := by
      intro h; apply hy; rw [← pow_one y, ← h, hm]
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨y ^ j, ?_, ?_⟩
    · exact Nat.find_min hex (by omega)
    · rw [← pow_mul]
      obtain ⟨t, ht⟩ : ∃ t, j * 2 = m + t := ⟨j * 2 - m, by omega⟩
      rw [ht, pow_add, hm, zero_mul]
  set I : Ideal S := Ideal.span {x} with hI
  have hlt : Nat.card (S ⧸ I) < n := by
    rw [← hn]
    classical
    cases nonempty_fintype S
    haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    cases nonempty_fintype (S ⧸ I)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_surjective_not_injective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    intro hinj
    apply hx0
    apply hinj
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨a', b', hab'⟩ := ih _ hlt (S ⧸ I) rfl (h2.map (Ideal.Quotient.mk I)) _ _
    (hd.map (Ideal.Quotient.mk I)) (hs.map (Ideal.Quotient.mk I))
  obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have hmem : a0 ^ 2 - d * b0 ^ 2 - s ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    rw [hab', sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  obtain ⟨t, ht⟩ := hs.exists_right_inv
  set iv := t - t ^ 2 * r * x with hiv
  have hv : (s + r * x) * iv - 1 = 0 := by
    rw [hiv]; linear_combination (1 - t * r * x) * ht - t ^ 2 * r ^ 2 * hx2
  refine ⟨a0 - r * a0 * iv * u * x, b0 - r * b0 * iv * u * x, ?_⟩
  linear_combination (1 - r * x * 2 * u * iv) * hr.symm - r * x * 2 * u * hv - r * x * hu + (r * iv * u) ^ 2 * (a0 ^ 2 - d * b0 ^ 2) * hx2

theorem exists_sq_sub_mul_sq_eq : ∀ (S : Type) [CommRing S] [Finite S], IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s :=
  fun S _ _ h2 d s hd hs => finiteRing_sq_sub_mul_sq_eq_of_card _ S rfl h2 d s hd hs

end GlobalTheory.FinRingNorm
end

section

noncomputable section

open Matrix

namespace GlobalTheory.HeisLatVac


open Classical in
def vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K) : (κ → K) → ℂ := by
  classical
  exact fun x => if h : ∃ u ∈ Λ, x = x₀ + u.1 then
    χ h.choose * ψ₀ (-(x₀ ⬝ᵥ h.choose.2) - ⅟(2 : K) * (h.choose.1 ⬝ᵥ h.choose.2)) else 0

end GlobalTheory.HeisLatVac
end
end

section

open ComplexConjugate Finset

namespace GlobalTheory

namespace GaussUnits

variable {R : Type} [CommRing R] [Fintype R]

theorem sum_ideal_of_exists (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (b : R) (hb : ∃ x ∈ I, b * x ≠ 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
  obtain ⟨x₀, hx₀I, hx₀⟩ := hb
  have hne : ¬ ∀ r, ψ (b * x₀ * r) = 1 := fun h => hx₀ (hψ _ h)
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  have hyI : x₀ * r ∈ I := I.mul_mem_right r hx₀I
  have hby : ψ (b * (x₀ * r)) ≠ 1 := by rwa [← mul_assoc]
  have hshift := Fintype.sum_equiv (Equiv.addRight (x₀ * r))
    (fun x => if x + x₀ * r ∈ I then ψ (b * (x + x₀ * r)) else 0)
    (fun x => if x ∈ I then ψ (b * x) else 0) (fun _ => rfl)
  have hS : ∑ x, (if x ∈ I then ψ (b * x) else 0)
      = ψ (b * (x₀ * r)) * ∑ x, (if x ∈ I then ψ (b * x) else 0) := by
    conv_lhs => rw [← hshift]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ I
    · have h' : x + x₀ * r ∈ I := I.add_mem hx hyI
      rw [if_pos h', if_pos hx, mul_add, AddChar.map_add_eq_mul, mul_comm]
    · have h' : x + x₀ * r ∉ I := fun h => hx (by simpa using I.sub_mem h hyI)
      rw [if_neg h', if_neg hx, mul_zero]
  have h1 : (1 - ψ (b * (x₀ * r))) * ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hby
  · exact h

theorem sum_ideal_of_forall (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ) (b : R)
    (hb : ∀ x ∈ I, b * x = 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = ((univ.filter (· ∈ I)).card : ℂ) := by
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_filter] at hx
  rw [hb x hx.2, AddChar.map_zero_eq_one, Nat.cast_one]

theorem sum_units_eq (m : Ideal R) [DecidablePred (· ∈ m)] [Fintype Rˣ]
    (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (f : R → ℂ) :
    ∑ u : Rˣ, f u = ∑ x, f x - ∑ x, (if x ∈ m then f x else 0) := by
  have h : ∑ u : Rˣ, f u = ∑ x ∈ univ.filter (fun x => ¬ x ∈ m), f x := by
    refine Finset.sum_bij (fun u _ => (u : R)) ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter]
      exact ⟨mem_univ _, (hm u).mp u.isUnit⟩
    · intro a _ b _ h
      exact Units.ext h
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨((hm x).mpr hx.2).unit, mem_univ _, rfl⟩
    · intro u _
      rfl
  rw [h, eq_sub_iff_add_eq, ← Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]

end GaussUnits


open GaussUnits in
theorem gauss_units_norm_sq : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [Fintype Rˣ]
    (m : Ideal R), (∀ x : R, IsUnit x ↔ x ∉ m) → ∀ (ψ : AddChar R ℂ),
    (∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) → ∀ (χ : Rˣ → ℂ), (∀ u v, χ (u * v) = χ u * χ v) →
    (∀ u, ‖χ u‖ = 1) → ∀ (t₀ : Rˣ), (∀ x ∈ m, ((t₀ : R) - 1) * x = 0) → χ t₀ ≠ 1 →
    ‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 = Fintype.card R := by
  intro R _ _ _ _ m hm ψ hψ χ hχ hχn t₀ ht₀ hχt₀
  classical
  have hχ0 : ∀ u, χ u ≠ 0 := fun u h => by simpa [h] using hχn u
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1
    rw [mul_one] at h
    have h2 : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (hχ0 1)
    · exact sub_eq_zero.mp h3
  have hconj : conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u) = ∑ z : Rˣ, χ z * ψ (-(z : R)) := by

    rw [map_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [map_mul, Complex.inv_eq_conj (hχn z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  have hexp : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = ∑ t : Rˣ, (χ t)⁻¹ * ∑ z : Rˣ, ψ (((t : R) - 1) * z) := by
    rw [hconj, Finset.sum_mul_sum, Finset.sum_comm]
    have hz : ∀ z : Rˣ, ∑ y : Rˣ, (χ y)⁻¹ * ψ y * (χ z * ψ (-(z : R)))
        = ∑ t : Rˣ, (χ t)⁻¹ * ψ (((t : R) - 1) * z) := by
      intro z
      refine Fintype.sum_equiv (Equiv.mulRight z⁻¹) _ _ (fun y => ?_)
      have hzinv : χ z⁻¹ = (χ z)⁻¹ := by
        have h := hχ z z⁻¹
        rw [mul_inv_cancel, hχ1] at h
        exact eq_inv_of_mul_eq_one_right h.symm
      have harg : (((y * z⁻¹ : Rˣ) : R) - 1) * (z : R) = (y : R) + -(z : R) := by
        rw [sub_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          mul_one, one_mul, sub_eq_add_neg]
      simp only [Equiv.coe_mulRight]
      rw [harg, AddChar.map_add_eq_mul, hχ, hzinv, mul_inv, inv_inv]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hz z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  have hinner : ∀ t : Rˣ, ∑ z : Rˣ, ψ (((t : R) - 1) * z) =
      (if t = 1 then (Fintype.card R : ℂ) else 0) -
      (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then ((univ.filter (· ∈ m)).card : ℂ) else 0) := by
    intro t
    rw [sum_units_eq m hm (fun x => ψ (((t : R) - 1) * x))]
    congr 1
    · have htop : ∑ x, ψ (((t : R) - 1) * x)
          = ∑ x, (if x ∈ (⊤ : Ideal R) then ψ (((t : R) - 1) * x) else 0) := by simp
      rw [htop]
      split_ifs with h
      · subst h
        rw [sum_ideal_of_forall ⊤ ψ _ (by simp)]
        simp
      · apply sum_ideal_of_exists ⊤ ψ hψ
        refine ⟨1, Submodule.mem_top, ?_⟩
        rw [mul_one, sub_ne_zero]
        exact fun h' => h (Units.val_eq_one.mp h')
    · split_ifs with h
      · exact sum_ideal_of_forall m ψ _ h
      · push_neg at h
        exact sum_ideal_of_exists m ψ hψ _ h
  have hcond : ∀ t : Rˣ, (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) ↔
      (∀ x ∈ m, ((t : R) - 1) * x = 0) := by
    intro t
    constructor
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul] at h1
      have h3 : (t₀ : R) * (((t : R) - 1) * x) = 0 := by linear_combination h1 - h2
      exact t₀.isUnit.mul_right_eq_zero.mp h3
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul]
      linear_combination (t₀ : R) * h1 + h2
  have hS : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
    have e := Fintype.sum_equiv (Equiv.mulLeft t₀)
      (fun t => if (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) then (χ (t₀ * t))⁻¹ else 0)
      (fun t => if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) (fun _ => rfl)
    have hS' : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)
        = (χ t₀)⁻¹ * ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) := by
      conv_lhs => rw [← e]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [hcond t, hχ, mul_inv, mul_ite, mul_zero]
    have hne : (χ t₀)⁻¹ ≠ 1 := fun h => hχt₀ (inv_eq_one.mp h)
    have h1 : (1 - (χ t₀)⁻¹) *
        ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
      rw [sub_mul, one_mul, ← hS', sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hmain : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = (Fintype.card R : ℂ) := by
    rw [hexp]
    simp_rw [hinner, mul_sub, mul_ite, mul_zero]
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then
        (χ t)⁻¹ * ((univ.filter (· ∈ m)).card : ℂ) else 0)
        = (∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)) *
          ((univ.filter (· ∈ m)).card : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> simp
    rw [h2, hS, zero_mul, sub_zero]
    simp [hχ1]
  have hn : ((‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 : ℝ) : ℂ) = (Fintype.card R : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hmain]
  exact_mod_cast hn

end GlobalTheory
end

section

open Matrix Topology

namespace GlobalTheory.JSW

theorem isCompact_charAnnihilator_of_mem_nhds_zero {F : Type} [NormedField F] [ProperSpace F] (ψ : AddChar F ℂ)
    (hlc : IsLocallyConstant ψ) (hψ : ψ ≠ 1) {ι : Type} [Fintype ι] (L : Set (ι → F))
    (hL : L ∈ nhds (0 : ι → F)) :
    IsCompact {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hψ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hL
  have hcont : Continuous (fun x : F => ψ x) := hlc.continuous
  have hclosed : IsClosed {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
    have : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} = ⋂ y ∈ L, {r : ι → F | ψ (r ⬝ᵥ y) = 1} := by
      ext r; simp
    rw [this]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    refine hcont.comp ?_
    simp only [dotProduct]
    fun_prop
  have hR : 0 ≤ ‖t‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hsub : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} ⊆ Metric.closedBall 0 (‖t‖ / ε) := by
    intro r hr
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro i
    by_contra hlt
    push_neg at hlt
    have hri : r i ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hlt; linarith
    have hpos : 0 < ‖r i‖ := norm_pos_iff.2 hri
    have hy : Pi.single i (t / r i) ∈ L := by
      apply hball
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, norm_div, div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hε] at hlt
        linarith
      · rw [Pi.single_eq_of_ne hj, norm_zero]; exact hε
    have := hr _ hy
    rw [dotProduct_single, mul_div_cancel₀ _ hri] at this
    exact ht this
  exact (isCompact_closedBall 0 (‖t‖ / ε)).of_isClosed_subset hclosed hsub

end GlobalTheory.JSW
end

section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem addChar_neg_eq_one {A : Type} [AddGroup A] (ψ : AddChar A ℂ) {x : A} (h : ψ x = 1) : ψ (-x) = 1 := by
  have e := AddChar.map_add_eq_mul ψ (-x) x
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at e
  exact e.symm

variable {k : Type} [Field k] [ValuativeRel k]

def latt (ψ0 : AddChar k ℂ) (n d : ℕ) (s : k) : AddSubgroup (Matrix (Fin n) (Fin d) k) where
  carrier := {Y | ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1}
  add_mem' := by
    intro a b ha hb i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.add_apply, mul_add, AddChar.map_add_eq_mul] at *
    rw [ha i j o ho, hb i j o ho, one_mul]
  zero_mem' := by
    intro i j o _
    simp
  neg_mem' := by
    intro a ha i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.neg_apply, mul_neg] at *
    exact addChar_neg_eq_one ψ0 (ha i j o ho)

theorem mem_latt {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k} {Y : Matrix (Fin n) (Fin d) k} :
    Y ∈ latt ψ0 n d s ↔ ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1 := Iff.rfl


open Classical in
def cind {X : Type} [AddGroup X] (L : AddSubgroup X) (y : X) : X → ℂ := by
  classical
  exact fun Y => if Y - y ∈ L then 1 else 0

end GlobalTheory.LinSchur
end
end

section

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

def krylov {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => Matrix.mulVec (y ^ (j : ℕ)) e i

theorem krylov_apply {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) (i j : Fin r) :
    krylov y e i j = Matrix.mulVec (y ^ (j : ℕ)) e i := rfl

end GlobalTheory.LeviDesc.Krylov
end
end
