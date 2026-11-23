module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_order_containing_integers : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  first | (exact @GlobalTheory.exists_order_integers_mul_finite_index) | (exact GlobalTheory.exists_order_integers_mul_finite_index) | (intros; apply GlobalTheory.exists_order_integers_mul_finite_index  <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.finrank_dvd_of_ringOfIntegers_to_int_matrix : ∀ (E : Type) [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  first | exact @GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | exact GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | (intros; apply GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix <;> assumption)
end

section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.normClassFinite_of_reduced_rat_algebra : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e) →
  ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e := by
  first | (exact @GlobalTheory.normClassFinite_of_reduced) | (exact GlobalTheory.normClassFinite_of_reduced) | (intros; apply GlobalTheory.normClassFinite_of_reduced  <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem exists_pos_nat_smul_mem_of_fg_of_span_eq_top :
    ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)),
      Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
        ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistence.main
  | exact _root_.GlobalTheory.DenominatorExistence.main
  | (apply _root_.GlobalTheory.DenominatorExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistence.main ..)

end GlobalTheory
end

section

open NumberField

theorem _root_.GlobalTheory.T.colon_pow_mul_cancel_fg_fractional : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  first | exact @GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | exact GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | (intros; apply GlobalTheory.ColonPowCancel.colon_pow_mul_cancel <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_global_uniformizer_above_prime : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F], ∃ ϖ z : 𝓞 F, ϖ * z - (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ∧ (∃ n : ℕ, ϖ ^ n ∈ Ideal.span {(p : 𝓞 F)}) ∧ IsReduced (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
  first | exact @GlobalTheory.exists_global_uniformiser_above_prime | exact GlobalTheory.exists_global_uniformiser_above_prime | (intros; apply GlobalTheory.exists_global_uniformiser_above_prime <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.isTorsionFree_ringOfIntegers_of_isTorsionFree_int' : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N], Module.IsTorsionFree (𝓞 E) N := by
  first | exact @GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int | exact GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int | (intros; apply GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.mem_of_mem_span_ringOfIntegers_map_numberField : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  first | exact @GlobalTheory.FlatDescent.mem_of_mem_span_map | exact GlobalTheory.FlatDescent.mem_of_mem_span_map | (intros; apply GlobalTheory.FlatDescent.mem_of_mem_span_map <;> assumption)
end

section

open NumberField

namespace GlobalTheory

theorem span_inf_span_eq_span_inf_of_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (n : ℕ)
      (M : Submodule (𝓞 K) (Fin n → K)) (W : Submodule K (Fin n → K)),
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))) ⊓
        (Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))).restrictScalars (𝓞 L) =
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) ''
        ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  intro K L _ _ _ _ _ n M W
  obtain ⟨m, ω, η, hη, hsum⟩ := exists_trace_dual_system K L
  let F : Fin m → (Fin n → L) → (Fin n → K) := fun i y j => Algebra.trace K L (η i * y j)
  have Fadd : ∀ i y z, F i (y + z) = F i y + F i z := by
    intro i y z; funext j; simp [F, mul_add, map_add (f := _)]
  have Fzero : ∀ i, F i 0 = 0 := by intro i; funext j; simp [F]
  have hint : ∀ i (a : 𝓞 L), ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Algebra.trace K L (η i * a) := by
    intro i a
    have h := (Submodule.mem_traceDual.mp (hη i)) (a : L) (Submodule.mem_one.mpr ⟨a, rfl⟩)
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hc, Algebra.traceForm_apply]⟩
  have Ftr : ∀ i (c : L) (x : Fin n → K),
      F i (c • (fun j => algebraMap K L (x j))) = Algebra.trace K L (η i * c) • x := by
    intro i c x; funext j
    simp only [F, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm _ (algebraMap K L (x j)), ← Algebra.smul_def, LinearMap.map_smul,
      smul_eq_mul, mul_comm]
  have hsm : ∀ (a : 𝓞 L) (v : Fin n → L), a • v = (a : L) • v := by
    intro a v; funext j; rfl
  have hM : ∀ y ∈ Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))),
      ∀ i (a : 𝓞 L), F i (a • y) ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      obtain ⟨c, hc⟩ := hint i a
      rw [hsm, Ftr, ← hc, algebraMap_smul]
      exact M.smul_mem c hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact M.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact M.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  have hW : ∀ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))),
      ∀ i (a : L), F i (a • y) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      rw [Ftr]
      exact W.smul_mem _ hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact W.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact W.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  apply le_antisymm
  · rintro y ⟨hy1, hy2⟩
    have hy2' : y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))) :=
      hy2
    have hdec : y = ∑ i, ω i • (fun j => algebraMap K L (F i y j)) := by
      funext j
      rw [Finset.sum_apply, hsum (y j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ = (ω i : L) * _
      rw [mul_comm]
    rw [hdec]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i y, ?_, rfl⟩)
    refine ⟨?_, ?_⟩
    · simpa using hM y hy1 i 1
    · simpa using hW y hy2' i 1
  · refine le_inf (Submodule.span_mono (Set.image_mono fun x hx => hx.1)) ?_
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx.2, rfl⟩

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CongW.PlaceEmb

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_isIntegral_int {x : PadicAlgCl p} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := PadicAlgCl p)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl p))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_int_le (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : ‖σ (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int σ (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (σ : K →+* PadicAlgCl p) : Ideal (𝓞 K) where
  carrier := {y | ‖σ (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : σ ((a + b : 𝓞 K) : K) = σ (a : K) + σ (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : σ ((c • a : 𝓞 K) : K) = σ (c : K) * σ (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le σ c
    nlinarith [norm_nonneg (σ (c : K)), norm_nonneg (σ (a : K))]

theorem mem_smallIdeal (σ : K →+* PadicAlgCl p) (y : 𝓞 K) : y ∈ smallIdeal σ ↔ ‖σ (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (σ : K →+* PadicAlgCl p) : (smallIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : σ ((a * b : 𝓞 K) : K) = σ (a : K) * σ (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  have h : ‖algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ := norm_algebraMap' _ _
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h, map_natCast] at h2
  exact h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* PadicAlgCl p, w.asIdeal = smallIdeal σ := by
  by_contra hcon
  push_neg at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, ¬ w.asIdeal ≤ smallIdeal (σ : K →+* PadicAlgCl p) := by
    intro σ hle
    exact hcon (σ : K →+* PadicAlgCl p) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] PadicAlgCl p)) : Set (K →ₐ[ℚ] PadicAlgCl p)),
        (smallIdeal (σ : K →+* PadicAlgCl p) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] PadicAlgCl p, 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = ∏ σ : K →ₐ[ℚ] PadicAlgCl p, σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ (PadicAlgCl p) (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : PadicAlgCl p)‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : PadicAlgCl p) = (p : PadicAlgCl p) * ((m : ℤ) : PadicAlgCl p) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : PadicAlgCl p)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : PadicAlgCl p), norm_nonneg ((m : ℤ) : PadicAlgCl p)]

end GlobalTheory.CongW.PlaceEmb

namespace GlobalTheory.CongW

open Formalism.ConjugateSelfDual

end GlobalTheory.CongW
end
end

section

open GlobalTheory.LKTrip

namespace GlobalTheory

theorem padic_tensor_numberField_isReduced :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F],
      IsReduced (TensorProduct ℚ ℚ_[p] F) := by
  intro p _ F _ _
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℚ_[p] (TensorProduct ℚ ℚ_[p] F) :=
    Algebra.FormallyUnramified.base_change ℚ_[p]
  exact Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] (TensorProduct ℚ ℚ_[p] F)

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_common_denominator_conj_localCoords_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), (∀ x, w.valuation E (σ x) = w.valuation E x) → (∀ a : E, w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r) → ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → ∀ (X : Matrix (Fin n) (Fin n) E), (∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r := by
  first | exact @GlobalTheory.ConjCoordDenom.exists_common_denom_conj_coords | exact GlobalTheory.ConjCoordDenom.exists_common_denom_conj_coords | (intros; apply GlobalTheory.ConjCoordDenom.exists_common_denom_conj_coords <;> assumption)
end
