module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.RingTheory.Nilpotent.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory

section CancelSummand

variable {R M M' P : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup P] [Module R P]

theorem linearEquiv_of_prod_corner_bijective (e : (M × P) ≃ₗ[R] (M' × P))
    (hd : Function.Bijective ((LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P)) :
    Nonempty (M ≃ₗ[R] M') := by
  set d : P →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  let dE : P ≃ₗ[R] P := LinearEquiv.ofBijective d hd
  let c : M →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inl R M P
  let φ : M →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      (LinearMap.prod LinearMap.id (-((dE.symm : P →ₗ[R] P) ∘ₗ c)))
  let ψ : M' →ₗ[R] M := (LinearMap.fst R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  have hsplit : ∀ x : M × P, (e x).2 = c x.1 + d x.2 := by
    intro x
    have hx : x = ((x.1, 0) : M × P) + (0, x.2) := by simp
    conv_lhs => rw [hx]
    rw [map_add (f := _)]
    rfl
  have hdd : ∀ p : P, d (dE.symm p) = p := fun p => dE.apply_symm_apply p
  have key : ∀ m : M, e (m, -dE.symm (c m)) = (φ m, 0) := by
    intro m
    ext
    · rfl
    · rw [hsplit]
      simp only [map_neg, hdd]
      simp
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · apply LinearMap.ext
    intro m'
    set x := e.symm (m', 0) with hx
    have hex : e x = (m', 0) := by simp [hx]
    have hp : -dE.symm (c x.1) = x.2 := by
      have h0 := hsplit x
      rw [hex] at h0
      have h1 : d x.2 = -c x.1 := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0.symm
      have h2 : dE.symm (d x.2) = x.2 := dE.symm_apply_apply x.2
      rw [h1, map_neg] at h2
      exact h2
    have hk := key x.1
    rw [hp] at hk
    have hψ : ψ m' = x.1 := rfl
    show φ (ψ m') = m'
    rw [hψ]
    have h3 : ((φ x.1, (0 : P)) : M' × P) = (m', 0) := by rw [← hk]; exact hex
    exact congrArg Prod.fst h3
  · apply LinearMap.ext
    intro m
    show ψ (φ m) = m
    have h : ψ (φ m) = (e.symm (φ m, 0)).1 := rfl
    rw [h, ← key m, LinearEquiv.symm_apply_apply]

theorem linearEquiv_cancel_of_nilpotent_or_bijective
    (hP : ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f)
    (e : (M × P) ≃ₗ[R] (M' × P)) : Nonempty (M ≃ₗ[R] M') := by
  set d : Module.End R P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  by_cases hd : Function.Bijective d
  · exact linearEquiv_of_prod_corner_bijective e hd
  let b : P →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P
  let c' : M' →ₗ[R] P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  let d' : Module.End R P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inr R M' P
  have hsum : c' ∘ₗ b = 1 - d' * d := by
    apply LinearMap.ext
    intro p
    have h : e (0, p) = ((b p, 0) : M' × P) + (0, d p) := by
      ext
      · simp; rfl
      · simp; rfl
    have h2 := congrArg Prod.snd (e.symm_apply_apply (0, p))
    rw [h, map_add (f := _)] at h2
    show c' (b p) = p - d' (d p)
    rw [eq_sub_iff_add_eq]
    exact h2
  have hnil : IsNilpotent (d' * d) := by
    rcases hP (d' * d) with h | h
    · exact h
    · exfalso
      apply hd
      have hinj : Function.Injective d := fun x y hxy => h.1 (by
        show d' (d x) = d' (d y)
        rw [hxy])
      rcases hP d with ⟨n, hn⟩ | h2
      · have hsub : ∀ x : P, x = 0 := by
          intro x
          apply hinj.iterate n
          have h3 : (d ^ n) x = (d ^ n) 0 := by rw [hn]; simp
          simpa [Module.End.pow_apply] using h3
        exact ⟨hinj, fun y => ⟨0, by rw [map_zero, hsub y]⟩⟩
      · exact h2
  have hw : IsUnit (c' ∘ₗ b : Module.End R P) := by
    rw [hsum]; exact hnil.isUnit_one_sub
  let winv : Module.End R P := ↑(hw.unit⁻¹)
  let g : M' →ₗ[R] P := ((1 - d) * winv) ∘ₗ c'
  let τ : (M' × P) ≃ₗ[R] (M' × P) :=
    LinearEquiv.skewProd (LinearEquiv.refl R M') (LinearEquiv.refl R P) g
  have hcorner : (LinearMap.snd R M' P) ∘ₗ ((e.trans τ : (M × P) ≃ₗ[R] (M' × P)) :
      (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P = LinearMap.id := by
    apply LinearMap.ext
    intro p
    have h1 : g (b p) = p - d p := by
      have h4 : (winv * (c' ∘ₗ b : Module.End R P)) p = p := by
        rw [hw.val_inv_mul]; rfl
      show ((1 - d) * winv) (c' (b p)) = p - d p
      change (1 - d) ((winv * (c' ∘ₗ b : Module.End R P)) p) = p - d p
      rw [h4]
      simp
    show (e (0, p)).2 + g ((e (0, p)).1) = p
    change d p + g (b p) = p
    rw [h1]
    abel
  exact linearEquiv_of_prod_corner_bijective (e.trans τ) (by rw [hcorner]; exact Function.bijective_id)

end CancelSummand

theorem cancel_summand_nilpotent_or_bijective : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P],
    (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) →
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ hP he
  obtain ⟨e⟩ := he
  exact linearEquiv_cancel_of_nilpotent_or_bijective hP e

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.NilpotentOfTracePowers

theorem trace_mul_aeval {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) (p : K[X]) :
    LinearMap.trace K V (f * aeval f p) = 0 := by

  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, map_smul, ← pow_succ', h (i + 1) (by omega), smul_zero]

theorem exists_pow_eq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    ∃ (m : ℕ) (g : K[X]), f ^ m = f ^ m * aeval f (X * g) := by
  have hp : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f.charpoly hp 0
  set m := rootMultiplicity 0 f.charpoly
  have hc : q.coeff 0 ≠ 0 := by
    intro h0
    apply hnd
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h0
  have h0 : aeval f f.charpoly = 0 := f.aeval_self_charpoly
  have hpoly : (X : K[X]) ^ m = X ^ m * (X * (C (-(q.coeff 0)⁻¹) * q.divX))
      + C (q.coeff 0)⁻¹ * f.charpoly := by
    have h1 : X * q.divX + C (q.coeff 0) = q := X_mul_divX_add q
    have h2 : C (q.coeff 0)⁻¹ * C (q.coeff 0) = (1 : K[X]) := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    rw [map_zero, sub_zero] at hq
    rw [map_neg]
    linear_combination (-C (q.coeff 0)⁻¹) * hq + (C (q.coeff 0)⁻¹ * X ^ m) * h1 - X ^ m * h2
  refine ⟨m, C (-(q.coeff 0)⁻¹) * q.divX, ?_⟩
  have := congrArg (aeval f) hpoly
  rw [map_add (f := _), map_mul (aeval f) _ f.charpoly, h0, mul_zero, add_zero, map_mul, map_pow,
    aeval_X] at this
  exact this

theorem isNilpotent_of_trace_pow {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  obtain ⟨m, g, hm⟩ := exists_pow_eq f
  have hiter : ∀ j : ℕ, f ^ m = f ^ m * aeval f ((X * g) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', map_mul, ← mul_assoc, ← hm, ← ih]
  set e : Module.End K V := aeval f ((X * g) ^ (m + 1)) with he
  have he1 : e = aeval f (X * g ^ (m + 1)) * f ^ m := by
    have : (X * g) ^ (m + 1) = (X * g ^ (m + 1)) * X ^ m := by ring
    rw [he, this, map_mul (aeval f) _ (X ^ m), map_pow, aeval_X]
  have hid : IsIdempotentElem e := by
    unfold IsIdempotentElem
    conv_lhs => enter [1]; rw [he1]
    rw [mul_assoc, ← hiter (m + 1), ← he1]
  have htr : LinearMap.trace K V e = 0 := by
    have : (X * g) ^ (m + 1) = X * (g ^ (m + 1) * X ^ m) := by ring
    rw [he, this, map_mul, aeval_X]
    exact trace_mul_aeval f h _
  have hproj : LinearMap.IsProj (LinearMap.range e) e :=
    { map_mem := fun x => LinearMap.mem_range_self e x
      map_id := by
        rintro _ ⟨x, rfl⟩
        exact LinearMap.congr_fun hid x }
  have hrk : Module.finrank K (LinearMap.range e) = 0 := by
    have := hproj.trace
    rw [htr] at this
    exact_mod_cast this.symm
  have he0 : e = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hrk)
  exact ⟨m, by rw [hiter (m + 1), ← he, he0, mul_zero]⟩

end GlobalTheory.NilpotentOfTracePowers
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

open NumberField in
private theorem exists_integral_generator_common_denom_of_finrank_two
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra! hx
    have htop : (⊤ : IntermediateField F E) = ⊥ := by
      ext x
      simp only [IntermediateField.mem_top, true_iff]
      exact IntermediateField.mem_bot.mpr (hx x)
    have h1 := IntermediateField.finrank_eq_one_iff.mpr htop
    rw [IntermediateField.finrank_top'] at h1
    omega
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have hint : IsIntegral ℤ (n • x) := hnx x (Finset.mem_singleton_self x)
  obtain ⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x :=
    ⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hθ : (θ : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hx
    refine ⟨a / n, ?_⟩
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
    rw [map_div₀, map_intCast, ha, hθx]
    field_simp
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  obtain ⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Fin.sum_univ_two, hb1]
    simp [Algebra.smul_def]
  set B := RingOfIntegers.basis E
  obtain ⟨d, hd, hdint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 =>
      b.repr (B p.1 : E) p.2)
  have hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k) := fun i k =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  refine ⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩
  let M : Submodule ℤ (𝓞 E) :=
    { carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ}
      add_mem' := by
        rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
        exact ⟨u + u', v + v', by simp only [map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨u, v, rfl⟩
        exact ⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }
  have hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M := by
    intro y
    have hspan : y ∈ Submodule.span ℤ (Set.range B) := by rw [B.span_eq]; trivial
    induction hspan using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩
      rw [RingOfIntegers.ext_iff]
      have e := hb (B i : E)
      have key : algebraMap F E (d : F) * (B i : E) =
          algebraMap F E (d • b.repr (B i : E) 0) +
            algebraMap F E (d • b.repr (B i : E) 1) * θ := by
        simp only [zsmul_eq_mul, map_mul, map_intCast]
        linear_combination (d : E) * e
      exact key
    | zero => simpa using M.zero_mem
    | add z w _ _ hz hw => rw [mul_add]; exact M.add_mem hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact M.smul_mem c hz
  intro y
  obtain ⟨u, v, huv⟩ := hall y
  exact ⟨u, v, huv⟩


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  intro F E _ _ _ _ _ h
  obtain ⟨θ, -, D, hD, hy⟩ := exists_integral_generator_common_denom_of_finrank_two F E h
  exact ⟨θ, D, hD, hy⟩

end GlobalTheory
end

section

namespace GlobalTheory.FiniteIndexSubgroup

open NumberField

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    ∀ x ∈ Submodule.span E (L : Set (Fin n → E)), ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hbz)
  | smul c x _ hx =>
    obtain ⟨ν, hν, hνx⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap (RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hsc : algebraMap (RingOfIntegers E) E (b * ν) * c = algebraMap (RingOfIntegers E) E (a * ν) := by
      rw [← hab, map_mul, map_mul]
      field_simp
    refine ⟨b * ν, mul_ne_zero hb0 hν, ?_⟩
    have : (b * ν) • (c • x) = a • (ν • x) := by
      calc (b * ν) • (c • x) = (algebraMap (RingOfIntegers E) E (b * ν)) • (c • x) :=
            (algebraMap_smul E _ _).symm
        _ = (algebraMap (RingOfIntegers E) E (b * ν) * c) • x := smul_smul _ _ _
        _ = (algebraMap (RingOfIntegers E) E (a * ν)) • x := by rw [hsc]
        _ = (a * ν) • x := algebraMap_smul E _ _
        _ = a • (ν • x) := mul_smul _ _ _
    rw [this]
    exact L.smul_mem a hνx

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E), ∃ (ν : NumberField.RingOfIntegers E), ν ≠ (0 : NumberField.RingOfIntegers E) ∧ ν • y ∈ L := by
  intro E _ _ n L hL y
  exact exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

end GlobalTheory.FiniteIndexSubgroup
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_pow_valuation_div_sub_one_le :
    ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 →
      ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N →
        v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  intro E _ _ v c hc n
  set e : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he
  have hval : v.valuation E (c : E) = WithZero.exp (-(e : ℤ)) := by
    have h := HeightOneSpectrum.valuation_of_algebraMap (K := E) v c
    have h' : v.valuation E (c : E) = v.intValuation c := h
    rw [h', v.intValuation_if_neg hc]
  have hcE : (c : E) ≠ 0 := by
    simpa using hc
  refine ⟨n + e, fun k hk => ?_⟩
  have hle : v.intValuation (k - c) ≤ WithZero.exp (-((n + e : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem (k - c) (n + e)).2 hk
  have hdiff : v.valuation E (((k - c : 𝓞 E)) : E) = v.intValuation (k - c) :=
    HeightOneSpectrum.valuation_of_algebraMap (K := E) v (k - c)
  have heq : (k : E) / (c : E) - 1 = (((k - c : 𝓞 E)) : E) / (c : E) := by
    push_cast
    field_simp
  rw [heq, map_div₀, hval, hdiff]
  have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-(e : ℤ)) := WithZero.exp_pos
  rw [div_le_iff₀ hpos, ← WithZero.exp_add]
  have hexp : -(n : ℤ) + -(e : ℤ) = -((n + e : ℕ) : ℤ) := by
    push_cast
    ring
  rwa [hexp]

end GlobalTheory
end

section

namespace GlobalTheory.PolynomialNormBound

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {j m : ℕ}, j ≠ (0 : ℕ) → ¬l ^ m ∣ j →
    ∃ (c : ℤ_[l]), (↑j : ℤ_[l]) * c = (↑l : ℤ_[l]) ^ (m - (1 : ℕ)) := by
  intro l inst j m hj hdvd
  have hl : l.Prime := inst.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj l hl.ne_one
  have hvm : v < m := by
    by_contra h
    exact hdvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow l (not_lt.mp h)) u)
  have hunit : IsUnit (u : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).mpr hu
  obtain ⟨w, hw⟩ := hunit
  refine ⟨(↑w⁻¹ : ℤ_[l]) * (l : ℤ_[l]) ^ (m - 1 - v), ?_⟩
  have hsplit : (l : ℤ_[l]) ^ (m - 1) = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  rw [← hw]
  calc (l : ℤ_[l]) ^ v * ↑w * (↑w⁻¹ * (l : ℤ_[l]) ^ (m - 1 - v))
      = (l : ℤ_[l]) ^ v * ((↑w * ↑w⁻¹) * (l : ℤ_[l]) ^ (m - 1 - v)) := by ring
    _ = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by rw [Units.mul_inv, one_mul]

end GlobalTheory.PolynomialNormBound
end
