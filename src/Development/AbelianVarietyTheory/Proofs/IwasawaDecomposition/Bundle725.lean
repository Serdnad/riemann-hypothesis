module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle713
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle712
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.FaceCutCell

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]


omit [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] in
theorem apply_eq_sum_of_toReal {m : ℕ} {β : LinearMap.BilinForm ℤ X} {u : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hβ : toReal β = ∑ i, c i • toReal (u i)) (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (F β : ℝ) = ∑ i, c i * (F (u i) : ℝ) := by
  have h := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) Function.injective_id F
    (β := Fin.cons β u) (c := Fin.cons (-1) c) (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_smul, one_smul, hβ, neg_add_cancel])
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  linarith

theorem est_at {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hstr : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i)
    (hle : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β ≤ ℓ β)
    (hγ : ∀ j, 0 ≤ h (γ j)) {C : ℕ} (hC : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β)
    {u : LinearMap.BilinForm ℤ X} (hu : u ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ u y y) (n : ℤ) (hn : ψ.evalZ u = n)
    {B0 L : ℝ} (hb : N * ψ.evalZ u ≤ B0) (hB0 : 0 ≤ B0) (hL : C * (B0 + 1) + C ≤ L) :
    L * (N * ψ.evalZ u) ≤ L * ℓ u + h u := by
  by_cases he : (N : ℝ) * ψ.evalZ u = ℓ u
  · obtain ⟨k, c, hk, hc⟩ := hstr u hu hp he
    have e3 : h (k • u) = ∑ i, (c i : ℤ) * h (γ i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have h2 : 0 ≤ ∑ i, (c i : ℤ) * h (γ i) := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hγ i)
    rw [← e3, map_nsmul, nsmul_eq_mul] at h2
    have h3 : 0 ≤ h u := by
      by_contra hneg
      push_neg at hneg
      have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) hneg
      linarith
    have h4 : (0 : ℝ) ≤ h u := by exact_mod_cast h3
    rw [he]
    linarith
  · have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne (hle u hu hp) he
    rw [hn] at hlt hb ⊢
    have h1 : (N : ℤ) * n < ℓ u := by exact_mod_cast hlt
    have h2 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u := h1
    have h3 : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast h2
    have h5 := hC u hu hp
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hLC : (0 : ℝ) ≤ L - C := by nlinarith [mul_nonneg hC0 hB0]
    nlinarith [mul_nonneg hLC (show (0 : ℝ) ≤ ℓ u - N * n - 1 by linarith),
      mul_nonneg hC0 (show (0 : ℝ) ≤ B0 - N * n by linarith), mul_nonneg hC0 hB0]

theorem isCell_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], IsPolyFanOn H.bar ψ X → Dominates H.bar X →
    ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i)) := by
  intro E _ _ _ H ψ X _ _ _ hP hD m m' γ s h hγ hf
  refine ⟨fun i => hγ.mem _, fun i y => hγ.nonneg _ y, linearOn_comp hγ.linear s, ?_⟩
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have e3 : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) e2) e1
    exact_mod_cast e3
  obtain ⟨C, hC⟩ := hD ℓ (-h) hpos
  have hC' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β := fun β hβ hp => by
    have e1 := hC β hβ hp
    simp only [LinearMap.neg_apply] at e1
    exact_mod_cast e1
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨B1, hB1⟩ := (hS.image fun τ => (N : ℝ) * ψ.evalZ τ).bddAbove
  set B0 := max B1 0 with hB0def
  have hB0nn : (0 : ℝ) ≤ B0 := le_max_right _ _
  have hB0 : ∀ τ ∈ S, (N : ℝ) * ψ.evalZ τ ≤ B0 := fun τ hτ => (hB1 ⟨τ, hτ, rfl⟩).trans (le_max_left _ _)
  have est : ∀ L : ℝ, C * (B0 + 1) + C ≤ L → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      L * (N * ψ.evalZ β) ≤ L * ℓ β + h β := by
    intro L hL β hβ hp
    have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
      have e1 := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1]
        (fun i => by fin_cases i; simpa using hβ) (fun i y => by fin_cases i; simpa using hp y)
        (fun i => by fin_cases i; simp)
      simpa using e1
    obtain ⟨e, k, τ, c, hτ, hτS, hc, hdec⟩ := hcov _ hmem
    let u : Fin k → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (τ i)
    have hu : IsCell H.bar ψ u := isCell_pull_equiv hτ e.symm
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have e1 := LinearMap.congr_fun₂ hdec (e.symm a) (e.symm b)
      simpa [u, LinearMap.sum_apply] using e1
    have hψ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu]
      exact (linearOn_iff ψ u).1 hu.linear c hc
    have hℓ := apply_eq_sum_of_toReal hβu ℓ
    have hh := apply_eq_sum_of_toReal hβu h
    have hterm : ∀ i, L * (N * ψ.evalZ (u i)) ≤ L * ℓ (u i) + h (u i) := fun i => by
      obtain ⟨n, hn⟩ := hP.integral _ (hu.mem i) (hu.nonneg i)
      refine est_at h3 h2 hf.1 hC' (hu.mem i) (hu.nonneg i) n hn ?_ hB0nn hL
      rw [show ψ.evalZ (u i) = ψ.evalZ (τ i) from evalZ_pull ψ e.symm.surjective _]
      exact hB0 _ (hτS i)
    rw [hψ, hℓ, hh]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have e1 := mul_le_mul_of_nonneg_left (hterm i) (hc i)
    convert e1 using 1 <;> ring
  obtain ⟨K, hK⟩ := exists_nat_ge (C * (B0 + 1) + C + 1 : ℝ)
  have hK1 : C * (B0 + 1) + C ≤ (K : ℝ) - 1 := by linarith
  have hK0 : C * (B0 + 1) + C ≤ (K : ℝ) := by linarith
  have hCB : (0 : ℝ) ≤ C * (B0 + 1) + C :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < K by linarith)
  refine ⟨K * N, (K : ℤ) • ℓ + h, Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · have h0 : h (γ (s i)) = 0 := (hf.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, h0, add_zero, smul_eq_mul]
    push_cast
    rw [h1]
    ring
  · have e1 := est K hK0 β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    linarith
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at he
    push_cast at he
    have e1 := est (K - 1) hK1 β hβ hp
    have e2 := h2 β hβ hp
    have heq : (N : ℝ) * ψ.evalZ β = ℓ β := by nlinarith
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp heq
    have hh0 : h β = 0 := by
      have e4 : (h β : ℝ) = 0 := by nlinarith
      exact_mod_cast e4
    have e3 : h (k • β) = ∑ i, (c i : ℤ) * h (γ i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have hsum : ∑ i, (c i : ℤ) * h (γ i) = 0 := by
      rw [← e3, map_nsmul, hh0, smul_zero]
    have hz : ∀ j, (c j : ℤ) * h (γ j) = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hf.1 i)).1 hsum j
        (Finset.mem_univ _)
    refine ⟨k, fun i => c (s i), hk, hc.trans ?_⟩
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) fun i => rfl).symm
    have hne : h (γ j) ≠ 0 := fun h0 => hj ((hf.2 j).1 h0)
    have hcj : c j = 0 := by
      rcases mul_eq_zero.1 (hz j) with h' | h'
      · exact_mod_cast h'
      · exact absurd h' hne
    simp [hcj]

end GlobalTheory.PolFan.FaceCutCell
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem exists_rescale_prim : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  intro O _ _ bar φ X _ _ _ m δ hδ hli
  choose n u hmem hn hu hprim using fun i => exists_prim (bar := bar) (hδ.mem i) (hli.ne_zero i)
  have hcu : IsCell bar φ u := cell_rescale hδ n hn hu hmem
  refine ⟨u, hcu, linearIndependent_of_smul hli n hn hu, fun i => hprim i, ?_⟩
  rintro β ⟨c, hc, hβ⟩
  refine ⟨fun i => c i * n i, fun i => mul_nonneg (hc i) (Nat.cast_nonneg _), ?_⟩
  rw [hβ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : toReal (δ i) = (n i : ℝ) • toReal (u i) := by
    rw [hu i]; exact LinearMap.ext₂ fun x y => by simp
  rw [e, smul_smul]

end GlobalTheory.PolFan.SmoothEnd
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellClass

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁]

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ γ) (e : X ≃ₗ[O] X₁) : IsCell bar φ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pull r : LinearMap.BilinForm ℤ X₁ → LinearMap.BilinForm ℤ X) := by
  intro β β' h
  refine LinearMap.ext₂ fun a b => ?_
  obtain ⟨a, rfl⟩ := hr a
  obtain ⟨b, rfl⟩ := hr b
  exact LinearMap.congr_fun₂ h a b

theorem linearIndependent_pull_equiv {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁} (h : LinearIndependent ℤ γ)
    (e : X ≃ₗ[O] X₁) : LinearIndependent ℤ fun i => pull e.toLinearMap (γ i) :=
  h.map' (pullLin e.toLinearMap) (LinearMap.ker_eq_bot.2 (pull_injective e.surjective))

theorem isPrim_pull_equiv (e : X ≃ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (hβ : β ∈ balForms bar X₁)
    (h : IsPrim bar (⟨β, hβ⟩ : balForms bar X₁)) :
    IsPrim bar (⟨pull e.toLinearMap β, pull_mem _ hβ⟩ : balForms bar X) := by
  intro k β' hk
  refine h k ⟨pull e.symm.toLinearMap β'.1, pull_mem _ β'.2⟩ (Subtype.ext (LinearMap.ext₂ fun a b => ?_))
  have := LinearMap.congr_fun₂ (congrArg Subtype.val hk) (e.symm a) (e.symm b)
  simpa using this

end Transport

theorem perModule {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hX : IsPolyFanOn H.bar φ X) :
    ∃ T : Set (LinearMap.BilinForm ℤ X), T.Finite ∧ ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (h : IsCell H.bar φ δ), LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      ∃ e : X ≃ₗ[𝓞 E] X, ∀ i, pull e.toLinearMap (δ i) ∈ T := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  let U : LinearMap.BilinForm ℤ X → Set (LinearMap.BilinForm ℤ X) := fun s =>
    {t | ∃ ht : t ∈ balForms H.bar X, IsPrim H.bar (⟨t, ht⟩ : balForms H.bar X) ∧
      ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ p • t = r • s}
  have hU : ∀ s, (U s).Subsingleton := by
    rintro s t ⟨ht, hpt, p, r, hp, hr, he⟩ t' ⟨ht', hpt', p', r', hp', hr', he'⟩
    have key : (r' * p) • t = (r * p') • t' := by
      rw [mul_smul, he, mul_smul, he', smul_comm]
    have := GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray H.bar ⟨t, ht⟩ ⟨t', ht'⟩ (r' * p) (r * p') hpt hpt' (by positivity) (by positivity)
      (Subtype.ext (by simpa using key))
    exact congrArg Subtype.val this
  refine ⟨⋃ s ∈ S, U s, hS.biUnion fun s _ => (hU s).finite, fun m δ h hli hprim => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone (bar := H.bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X m δ (fun _ => 1) h.mem h.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell H.bar φ γ' := isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  refine ⟨e, fun i => ?_⟩
  obtain ⟨k, a, hk, hka⟩ := GlobalTheory.T.cell_generators_smul_mem_other_cellCone H.bar φ δ γ' c h hγ' hc hsum' i
  obtain ⟨j, p, r, hp, hr, hpr⟩ :=
    GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' δ γ' i k a hli hk hka (GlobalTheory.T.cell_generator_mem_cone_of_smul_combination H.bar φ δ γ' i k a h hγ' hk hka)
  refine Set.mem_biUnion (hγS j) ⟨pull_mem _ (h.mem i), isPrim_pull_equiv e (h.mem i) (hprim i), p, r, hp, hr, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hpr (e y) (e z)
  simpa [γ'] using this

theorem multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  intro E _ _ _ H q φ hφ M
  classical
  obtain ⟨n, R, hR, hcls⟩ := GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField E q
  have key : ∀ k, letI := (hR k).1; ∃ T : Set (LinearMap.BilinForm ℤ (R k)), T.Finite ∧
      ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)) (h : IsCell H.bar φ δ), LinearIndependent ℤ δ →
        (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar (R k))) →
        ∃ e : (R k) ≃ₗ[𝓞 E] (R k), ∀ i, pull e.toLinearMap (δ i) ∈ T := fun k => by
    letI := (hR k).1
    haveI := (hR k).2.1
    exact perModule H φ (R k) (hφ (R k) (hR k).2.2)
  choose T hTfin hT using key
  haveI : ∀ k, Finite (T k) := fun k => (hTfin k).to_subtype
  let D := Σ k : Fin n, Σ m : Fin (Nat.card (T k) + 1), (Fin m → T k)
  let g : D → FormFamily (𝓞 E) := fun d => ⟨R d.1, d.2.1, fun i => (d.2.2 i : LinearMap.BilinForm ℤ (R d.1))⟩
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin D
  refine ⟨N, fun k' => g (eq.symm k'), fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨hcell, hli, hprim, -⟩ := hδ
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  letI := (hR k).1
  let δ' : Fin m → LinearMap.BilinForm ℤ (R k) := fun i => pull f.symm.toLinearMap (δ i)
  have hcell' : IsCell H.bar φ δ' := isCell_pull_equiv hcell f.symm
  have hli' : LinearIndependent ℤ δ' := linearIndependent_pull_equiv hli f.symm
  have hprim' : ∀ i, IsPrim H.bar (⟨δ' i, hcell'.mem i⟩ : balForms H.bar (R k)) := fun i =>
    isPrim_pull_equiv f.symm (hcell.mem i) (hprim i)
  obtain ⟨e, he⟩ := hT k m δ' hcell' hli' hprim'
  let t : Fin m → T k := fun i => ⟨_, he i⟩
  have ht : Function.Injective t := fun i j hij =>
    hli'.injective (pull_injective e.surjective (congrArg Subtype.val hij))
  have hm : m < Nat.card (T k) + 1 := by
    have := Nat.card_le_card_of_injective t ht
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨eq ⟨k, ⟨m, hm⟩, t⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨f.trans e.symm, Equiv.refl (Fin m), fun i => LinearMap.ext₂ fun y z => ?_⟩
  simp [g, t, δ']

end GlobalTheory.PolFan.CellClass
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark


theorem _root_.GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone : ∀ (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), ψ.LinearOn v → ∀ β x : LinearMap.BilinForm ℤ X, InRCone v β → InRCone v x → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  first | exact @GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | exact GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | (intros; apply GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_linForm_cut_face_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (γ' : Fin p → LinearMap.BilinForm ℤ X)
    (h₂ h₁ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    (∀ i, δ i ∈ balForms bar X) → (∀ i y, 0 ≤ δ i y y) → (∀ j, InRCone γ (γ' j)) →
    (∀ i, 0 ≤ h₂ (δ i)) → (∀ k, h₂ (γ k) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h₂ β = 0 → InRCone γ β) →
    (∀ k, 0 ≤ h₁ (γ k)) → (∀ j, h₁ (γ' j) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h₁ β = 0 → InRCone γ' β) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (δ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h β = 0 → InRCone γ' β := by
  intro O _ bar X _ _ m n p δ γ γ' h₂ h₁ hδb hδp hγ' h2δ h2γ hf2 h1γ h1γ' hf1
  set K : ℤ := 1 + ∑ i, |h₁ (δ i)| with hK
  have hKi : ∀ i, |h₁ (δ i)| < K := fun i => by
    have := Finset.single_le_sum (f := fun i => |h₁ (δ i)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hK0 : 0 ≤ K := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (h₁ (δ i)))
    linarith
  have happ : ∀ x, (K • h₂ + h₁) x = K * h₂ x + h₁ x := fun x => by simp
  have hpos : ∀ i, 0 < h₂ (δ i) → 0 < (K • h₂ + h₁) (δ i) := fun i hi => by
    rw [happ]
    have h1 : K ≤ K * h₂ (δ i) := by nlinarith
    have := neg_abs_le (h₁ (δ i))
    linarith [hKi i]
  have hnn : ∀ i, 0 ≤ (K • h₂ + h₁) (δ i) := fun i => by
    rcases (h2δ i).lt_or_eq with hi | hi
    · exact (hpos i hi).le
    · rw [happ, ← hi, mul_zero, zero_add]
      exact InRCone.apply_nonneg (hf2 _ (hδb i) (hδp i) (inRCone_self δ i) hi.symm) h₁ h1γ
  have h2γ' : ∀ j, h₂ (γ' j) = 0 := fun j => le_antisymm (by
      have := InRCone.apply_nonneg (hγ' j) (-h₂) (fun k => by simp [h2γ k])
      simpa using this)
    (InRCone.apply_nonneg (hγ' j) h₂ (fun k => (h2γ k).ge))
  refine ⟨K • h₂ + h₁, hnn, fun j => by rw [happ, h2γ' j, h1γ' j]; ring, ?_⟩
  intro β hb hp hc hz
  have h2β : h₂ β = 0 := by
    obtain ⟨c, hc0, e⟩ := hc
    have eh := apply_eq_of_toReal_eq e (K • h₂ + h₁)
    have e2 := apply_eq_of_toReal_eq e h₂
    rw [hz, Int.cast_zero] at eh
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ c i * ((K • h₂ + h₁) (δ i) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hnn i)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 eh.symm
    have hs : ∑ i, c i * (h₂ (δ i) : ℝ) = 0 := Finset.sum_eq_zero fun i _ => by
      rcases (h2δ i).lt_or_eq with hi | hi
      · have h0 := hall i (Finset.mem_univ _)
        have hp' : (0 : ℝ) < (K • h₂ + h₁) (δ i) := by exact_mod_cast hpos i hi
        rw [(mul_eq_zero.1 h0).resolve_right hp'.ne', zero_mul]
      · rw [← hi]; simp
    exact_mod_cast e2.trans hs
  have hγβ := hf2 β hb hp hc h2β
  refine hf1 β hb hp hγβ ?_
  have := happ β
  rw [hz, h2β] at this
  linarith

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan

theorem genRank_le_of_inRCone_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → (∀ j, v j ∈ balForms bar X) → (∀ j y, 0 ≤ v j y y) → (∀ j, InRCone γ (v j)) →
    genRank v ≤ genRank γ := by
  intro O _ bar ψ X _ _ _ m n γ v hγ hbal hnn hcone
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hk : ∀ j, ∃ k : ℕ, 0 < k ∧ ((k : ℤ) • v j) ∈ Submodule.span ℤ (Set.range γ) := by
    intro j
    obtain ⟨c, hc, e⟩ := hcone j
    have hl := apply_eq_of_toReal_eq e ℓ
    have hlin := (linearOn_iff ψ γ).1 hγ.linear c hc
    rw [← e, evalR_toReal] at hlin
    have heq : (N : ℝ) * ψ.evalZ (v j) = ℓ (v j) := by
      rw [hl, hlin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i]; ring
    obtain ⟨k, c', hk, hc'⟩ := h3 (v j) (hbal j) (hnn j) heq
    refine ⟨k, hk, ?_⟩
    rw [natCast_zsmul, hc']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose k hkpos hkmem using hk
  set K : ℕ := ∏ j, k j with hKdef
  have hK : 0 < K := Finset.prod_pos fun j _ => hkpos j
  set S := Submodule.span ℤ (Set.range γ) with hS
  have hle : Submodule.span ℤ (Set.range v) ≤ S.comap ((K : ℤ) • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr⟩ : k j ∣ K := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show ((K : ℤ) • LinearMap.id) (v j) ∈ S
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [hr, Nat.cast_mul, mul_comm, mul_smul]
    exact S.smul_mem _ (hkmem j)
  let f : Submodule.span ℤ (Set.range v) →ₗ[ℤ] S :=
    (((K : ℤ) • LinearMap.id).comp (Submodule.span ℤ (Set.range v)).subtype).codRestrict S fun x => hle x.2
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    apply Subtype.ext
    refine LinearMap.ext₂ fun a b => ?_
    have e2 := LinearMap.congr_fun₂ e a b
    simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul] at e2
    exact mul_left_cancel₀ (by exact_mod_cast hK.ne') e2
  haveI : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  exact LinearMap.finrank_le_finrank_of_injective hf

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.polFanCarrierDimension_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  first | exact @GlobalTheory.PolFan.carrierDim_bounded | exact GlobalTheory.PolFan.carrierDim_bounded | (intros; apply GlobalTheory.PolFan.carrierDim_bounded <;> assumption)
end
