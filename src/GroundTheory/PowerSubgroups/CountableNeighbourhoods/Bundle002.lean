module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
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
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

section

namespace GroundTheory.Variant₂.N1

open NumberField

section Splitting

variable {G P : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup P] [TopologicalSpace P]

def centralSplitting (φ : G →* P) (hφ : Continuous φ) (s : P →* G) (hs : Continuous s)
    (hsφ : ∀ p, φ (s p) = p) (hc : ∀ p g, s p * g = g * s p) (H : Subgroup G)
    (hH : ∀ g, g ∈ H ↔ φ g = 1) : G ≃ₜ* H × P where
  toFun g := (⟨g * (s (φ g))⁻¹, (hH _).2 (by rw [map_mul, map_inv, hsφ, mul_inv_cancel])⟩, φ g)
  invFun x := (x.1 : G) * s x.2
  left_inv g := by simp
  right_inv x := by
    obtain ⟨⟨h, hh⟩, p⟩ := x
    have h1 : φ h = 1 := (hH h).1 hh
    have h2 : φ (h * s p) = p := by rw [map_mul, h1, hsφ, one_mul]
    refine Prod.ext (Subtype.ext ?_) h2
    simp [h2]
  map_mul' g g' := by
    have hci : ∀ p g, (s p)⁻¹ * g = g * (s p)⁻¹ := fun p g => by
      rw [← map_inv]; exact hc p⁻¹ g
    refine Prod.ext (Subtype.ext ?_) (map_mul φ g g')
    simp only [map_mul, mul_inv_rev]
    rw [hci (φ g') (s (φ g))⁻¹]
    calc g * g' * ((s (φ g))⁻¹ * (s (φ g'))⁻¹)
        = g * (g' * (s (φ g))⁻¹) * (s (φ g'))⁻¹ := by simp only [mul_assoc]
      _ = g * ((s (φ g))⁻¹ * g') * (s (φ g'))⁻¹ := by rw [hci]
      _ = g * (s (φ g))⁻¹ * (g' * (s (φ g'))⁻¹) := by simp only [mul_assoc]
  continuous_toFun :=
    (Continuous.subtype_mk (continuous_id.mul ((hs.comp hφ).inv)) _).prodMk hφ
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)

end Splitting

section Section

variable {K : Type*} [Field K]


variable [NumberField K]





end Section

end GroundTheory.Variant₂.N1
end

section

namespace GroundTheory.Variant₂.N1

open IsLocalRing

theorem exists_eq_unit_mul_pow_adicCompletion {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : AdicCompletion (maximalIdeal R) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (maximalIdeal R) R)ˣ),
      x = ↑u * (algebraMap R (AdicCompletion (maximalIdeal R) R)) ϖ ^ n := by

  have hM : maximalIdeal (AdicCompletion (maximalIdeal R) R) =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ} := by
    have e := congrArg (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      hϖ.maximalIdeal_eq
    rw [AdicCompletion.maximalIdeal_eq_map, e, Ideal.map_span, Set.image_singleton]
  have hMpow : ∀ k : ℕ, maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ ^ k} := fun k => by
    rw [hM, Ideal.span_singleton_pow]

  have hex : ∃ k : ℕ, x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k := by
    by_contra h
    push Not at h
    apply hx
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff
      (I := maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (M := AdicCompletion (maximalIdeal R) R)) x
    intro k
    simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero] using h k
  classical
  have hk : x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ Nat.find hex :=
    Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hk
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hxn : x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
    have := Nat.find_min hex (show n < Nat.find hex by omega)
    simpa using this
  rw [hMpow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hyu : IsUnit y := by
    rw [← notMem_maximalIdeal]
    intro hyM
    apply hk
    rw [hn, hMpow, Ideal.mem_span_singleton']
    rw [hM, Ideal.mem_span_singleton'] at hyM
    obtain ⟨z, hz⟩ := hyM
    exact ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩

end GroundTheory.Variant₂.N1
end

section

namespace GroundTheory.Variant₂.N1

theorem mem_span_singleton_pow_smul_top_iff {A : Type*} [CommRing A] (a x : A) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule A A) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_sum_pow_mul {A : Type*} [CommRing A] {a : A}
    [IsPrecomplete (Ideal.span {a}) A] (b : ℕ → A) :
    ∃ L : A, ∀ n : ℕ, a ^ n ∣ (∑ k ∈ Finset.range n, a ^ k * b k) - L := by
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (Ideal.span {a}) A).prec'
    (fun n => ∑ k ∈ Finset.range n, a ^ k * b k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff,
        ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow a (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun n => (mem_span_singleton_pow_smul_top_iff a _ n).1 ((SModEq.sub_mem).1 (hL n))⟩

theorem exists_eq_add_mul_of_forall' {A : Type*} {R : Type*} {ι : Type*} [CommRing A]
    [CommRing R] {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) :
    f a = r →
      ∀ (X : R) (ψ : ι → R),
        (∀ (y : ι), ∃ (b : A) (s : R) (y' : ι), ψ y = f b + X * s + r * ψ y') →
          ∀ (y : ι), ∃ (b : A) (s : R), ψ y = f b + X * s := by
  intro hfa X ψ h
  choose b s nx hstep using h
  intro y
  obtain ⟨B, hB⟩ := exists_limit_sum_pow_mul (a := a) (fun k => b (nx^[k] y))
  obtain ⟨S, hS⟩ := exists_limit_sum_pow_mul (a := r) (fun k => s (nx^[k] y))
  refine ⟨B, S, ?_⟩
  have key : ∀ n : ℕ, ψ y = f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) +
      X * (∑ k ∈ Finset.range n, r ^ k * s (nx^[k] y)) + r ^ n * ψ (nx^[n] y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hstep (nx^[n] y)
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [map_add (f := _), map_mul, map_pow, hfa] at ih ⊢
      linear_combination ih + r ^ n * h1
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {r}) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff]
  obtain ⟨c, hc⟩ := hB n
  obtain ⟨d, hd⟩ := hS n
  have hfB : f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) = f B + r ^ n * f c := by
    rw [← hfa, ← map_pow, ← map_mul, ← map_add (f := _)]
    congr 1
    linear_combination hc
  exact ⟨f c + X * d + ψ (nx^[n] y), by linear_combination key n + hfB + X * hd⟩

end GroundTheory.Variant₂.N1
end
