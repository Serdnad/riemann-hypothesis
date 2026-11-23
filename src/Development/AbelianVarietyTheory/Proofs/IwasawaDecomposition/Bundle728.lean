module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle717
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

namespace StarUpper

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone_cell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he


omit [Module O X] [Module.Finite O X] in
theorem sum_mem_rcone {p : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (d : Fin m → ℕ), 0 < k ∧ k • δ i = ∑ j, d j • γ j) :
    ∑ i, x i • toReal (δ i) ∈ rcone γ := by
  classical
  have hi : ∀ i, ∃ g : Fin m → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (γ j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨k, d, hk, hkd⟩ := h i h0
    have hxi := hx i
    refine ⟨fun j => x i / k * d j, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
    have e := LinearMap.congr_fun₂ hkd a b
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at e
    have e' : (k : ℝ) * (δ i a b : ℝ) = ∑ j, (d j : ℝ) * (γ j a b : ℝ) := by exact_mod_cast e
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    calc x i * (δ i a b : ℝ) = x i / k * ((k : ℝ) * (δ i a b : ℝ)) := by field_simp
      _ = _ := by rw [e', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

end StarUpper


open StarUpper in
theorem evalR_starDepth_le : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s : ℝ),
    IsCell bar ψ γ → B ∈ rcone γ → 0 ≤ s → (∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v →
      ∀ t : ℝ, 0 < t → B - t • toReal v ∈ rcone γ → t ≤ s) → evalR (starDepth bar ψ w) B ≤ s := by
  intro O _ bar ψ w X _ _ _ m γ B s hγ hB hs H
  obtain ⟨c, hc, hBc⟩ := hB
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' O X
  show (starDepth bar ψ w).eval X (fun a b => B a b) ≤ s
  rw [InvFun.eval_eq _ hq]
  refine Real.sSup_le (fun t ht => ?_) hs
  obtain ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB₁, ht0, m₁, γ₁, v₁, hγ₁, hv₁, hv₁p, hwv₁, ⟨e, he, hev⟩, -,
    ⟨d, hd, hdv⟩⟩ := ht
  rcases ht0.eq_or_lt with rfl | htpos
  · exact hs

  have hker : LinearMap.ker q ≤ LinearMap.ker ρ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hrad _ fun y => ?_
    obtain ⟨y', rfl⟩ := hρ y
    have h1 := hB₁ x y'
    simp only [hx, map_zero, LinearMap.zero_apply] at h1
    exact h1.symm
  let ρ' : X →ₗ[O] X₁ := (LinearMap.ker q).liftQ ρ hker ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hρ' : ∀ a, ρ' (q a) = ρ a := fun a => by
    have : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hρs : Function.Surjective ρ' := fun x => by
    obtain ⟨a, rfl⟩ := hρ x
    exact ⟨q a, hρ' a⟩
  have hBB : ∀ x y, B x y = B₁ (ρ' x) (ρ' y) := fun x y => by
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [hρ', hρ']
    exact hB₁ a b

  set δ : Fin m₁ → LinearMap.BilinForm ℤ X := fun i => pull ρ' (γ₁ i) with hδ
  set v : LinearMap.BilinForm ℤ X := pull ρ' v₁ with hv
  have hv_eq : toReal v = ∑ i, e i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hev (ρ' a) (ρ' b)
    simpa [hδ, hv, LinearMap.sum_apply] using this
  have hd_eq : B - t • toReal v = ∑ i, d i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hdv (ρ' a) (ρ' b)
    simpa [hδ, hv, hBB, LinearMap.sum_apply] using this
  have hrel : ∑ i, (d i + t * e i) • toReal (δ i) = ∑ j, c j • toReal (γ j) := by
    rw [← hBc]
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := LinearMap.congr_fun₂ hd_eq a b
    have h2 := LinearMap.congr_fun₂ hv_eq a b
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at h1 h2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← h1, ← h2]
    ring
  have hnn : ∀ i, 0 ≤ d i + t * e i := fun i => add_nonneg (hd i) (mul_nonneg ht0 (he i))
  have hlin : evalR ψ (∑ i, (d i + t * e i) • toReal (δ i)) = ∑ i, (d i + t * e i) * ψ.evalZ (δ i) :=
    (linearOn_iff ψ δ).1 ((linearOn_pull_iff hρs).2 hγ₁.linear) _ hnn
  have hcone := inCone_cell hγ (fun i => pull_mem ρ' (hγ₁.mem i)) (fun i y => hγ₁.nonneg i _) hnn hc hlin hrel
  have hInR : InRCone γ v := by
    obtain ⟨c', hc', h'⟩ := sum_mem_rcone e he fun i hi => hcone i
      (add_pos_of_nonneg_of_pos (hd i) (mul_pos htpos (lt_of_le_of_ne (he i) (Ne.symm hi)))).ne'
    exact ⟨c', hc', hv_eq.trans h'⟩
  have hBt : B - t • toReal v ∈ rcone γ := by
    rw [hd_eq]
    exact sum_mem_rcone d hd fun i hi => hcone i
      (add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hd i) (Ne.symm hi)) (mul_nonneg ht0 (he i))).ne'
  exact H v (pull_mem ρ' hv₁) (fun y => hv₁p _) (by rw [hv, evalZ_pull w hρs]; exact hwv₁) hInR t htpos hBt

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

namespace DepthBdd

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone_of_strict {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hstr : IsStrict bar φ γ')
    (hlin' : φ.LinearOn γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstr
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hlin' b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

theorem zero_mem_rcone (u : Fin m → LinearMap.BilinForm ℤ X) : (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ rcone u :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem add_mem_rcone {u : Fin m → LinearMap.BilinForm ℤ X} {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone u)
    (h' : B' ∈ rcone u) : B + B' ∈ rcone u := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨t', ht', rfl⟩ := h'
  exact ⟨t + t', fun i => add_nonneg (ht i) (ht' i), by simp [add_smul, Finset.sum_add_distrib]⟩

theorem smul_mem_rcone {u : Fin m → LinearMap.BilinForm ℤ X} {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone u) {s : ℝ}
    (hs : 0 ≤ s) : s • B ∈ rcone u := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨s • t, fun i => mul_nonneg hs (ht i), by simp [Finset.smul_sum, smul_smul]⟩

theorem finsum_mem_rcone {u : Fin m → LinearMap.BilinForm ℤ X} {ι : Type} (s : Finset ι)
    (f : ι → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (h : ∀ i ∈ s, f i ∈ rcone u) : ∑ i ∈ s, f i ∈ rcone u :=
  Finset.sum_induction f (· ∈ rcone u) (fun _ _ => add_mem_rcone) (zero_mem_rcone u) h

end DepthBdd

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan


open DepthBdd in
theorem depthSet_bddAbove_of_unique_centre : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X →
    (∀ y, 0 ≤ v y y) → v ≠ 0 →
    (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) →
    ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X), Function.Surjective π →
      BddAbove (depthSet bar ψ w n (fun a b => B (π a) (π b))) := by
  intro O _ bar ψ w X _ _ _ m γ B v hγ hB hv hvp hv0 huniq n π hπ
  obtain ⟨y₀, hy₀⟩ : ∃ y, 0 < v y y := by
    by_contra hc
    push_neg at hc
    apply hv0
    have hz : ∀ y, v y y = 0 := fun y => le_antisymm (hc y) (hvp y)
    refine LinearMap.ext₂ fun x y => ?_
    have h := hz (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, hz x, hz y, hv.1 y x] at h
    simp only [LinearMap.zero_apply]
    omega
  have hy₀' : (0 : ℝ) < v y₀ y₀ := by exact_mod_cast hy₀
  refine ⟨max (B y₀ y₀ / v y₀ y₀) 0, ?_⟩
  rintro t ⟨X₂, i1, i2, i3, ρ, B₂, hρ, hrad, hB2, ht, m₂, δ₂, v₂, hδ₂, hv₂, hv₂p, hw, ⟨e, he, hev⟩, -, ⟨d, hd, hdB⟩⟩
  rcases ht.eq_or_lt with rfl | htpos
  · exact le_max_right _ _
  refine le_max_of_le_left ?_
  have hker : LinearMap.ker π ≤ LinearMap.ker ρ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hrad _ fun y => ?_
    obtain ⟨y', rfl⟩ := hρ y
    have h1 := hB2 x y'
    simp only [hx, map_zero, LinearMap.zero_apply] at h1
    exact h1.symm
  let ρ' : X →ₗ[O] X₂ :=
    (LinearMap.ker π).liftQ ρ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hρ' : ∀ a, ρ' (π a) = ρ a := fun a => by
    have : (π.quotKerEquivOfSurjective hπ).symm (π a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hρs : Function.Surjective ρ' := fun x => by
    obtain ⟨a, rfl⟩ := hρ x
    exact ⟨π a, hρ' a⟩
  have hBB : ∀ x y, B x y = B₂ (ρ' x) (ρ' y) := fun x y => by
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨b, rfl⟩ := hπ y
    rw [hρ', hρ']
    exact hB2 a b
  have hev' : ∀ p q, (v₂ p q : ℝ) = ∑ i, e i * (δ₂ i p q : ℝ) := fun p q => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hev p q
  have hdB' : ∀ p q, B₂ p q - t * (v₂ p q : ℝ) = ∑ i, d i * (δ₂ i p q : ℝ) := fun p q => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hdB p q
  set δ : Fin m₂ → LinearMap.BilinForm ℤ X := fun i => pull ρ' (δ₂ i) with hδdef
  set v' : LinearMap.BilinForm ℤ X := pull ρ' v₂ with hv'def
  set a : Fin m₂ → ℝ := fun i => d i + t * e i with hadef
  have ha : ∀ i, 0 ≤ a i := fun i => add_nonneg (hd i) (mul_nonneg htpos.le (he i))
  have hsumB : B = ∑ i, a i • toReal (δ i) := LinearMap.ext₂ fun x y => by
    have h1 := hdB' (ρ' x) (ρ' y)
    have h2 := hev' (ρ' x) (ρ' y)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul, hBB, δ, a, add_mul,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ← h2, ← h1]
    ring
  have hv'sum : toReal v' = ∑ i, e i • toReal (δ i) := LinearMap.ext₂ fun x y => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul, δ, v']
    exact hev' _ _
  have hBv' : B - t • toReal v' = ∑ i, d i • toReal (δ i) := LinearMap.ext₂ fun x y => by
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul, δ,
      v', hBB]
    exact hdB' _ _
  obtain ⟨b, hb, hBb⟩ := hB
  have hlinδ : ψ.LinearOn δ := (linearOn_pull_iff hρs).2 hδ₂.linear
  have key : ∀ i, a i ≠ 0 → toReal (δ i) ∈ rcone γ := fun i hai => by
    obtain ⟨k, c, hk, hkc⟩ := inCone_of_strict hγ.strict hγ.linear (fun i => pull_mem ρ' (hδ₂.mem i))
      (fun i y => hδ₂.nonneg i (ρ' y)) ha hb ((linearOn_iff ψ δ).1 hlinδ a ha) (hsumB.symm.trans hBb) i hai
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨fun j => (c j : ℝ) / k, fun j => by positivity, LinearMap.ext₂ fun x y => ?_⟩
    have h := LinearMap.congr_fun₂ hkc x y
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h
    have h' : (k : ℝ) * (δ i x y : ℝ) = ∑ j, (c j : ℝ) * (γ j x y : ℝ) := by exact_mod_cast h
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
    rw [show ∑ j, (c j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (c j : ℝ) * (γ j x y : ℝ)) / k by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring, ← h']
    field_simp
  have hterm : ∀ s : Fin m₂ → ℝ, (∀ i, 0 ≤ s i) → (∀ i, 0 < s i → 0 < a i) → ∑ i, s i • toReal (δ i) ∈ rcone γ :=
    fun s hs hsa => finsum_mem_rcone _ _ fun i _ => by
      rcases (hs i).eq_or_lt with h | h
      · rw [← h, zero_smul]; exact zero_mem_rcone γ
      · exact smul_mem_rcone (key i (hsa i h).ne') (hs i)
  have hv'in : InRCone γ v' := by
    show toReal v' ∈ rcone γ
    rw [hv'sum]
    exact hterm e he fun i h => by have := hd i; simp only [a]; nlinarith
  have hBin : B - t • toReal v' ∈ rcone γ := by
    rw [hBv']
    exact hterm d hd fun i h => by have := he i; simp only [a]; nlinarith
  have hvv : v' = v := huniq v' (pull_mem ρ' hv₂) (fun y => hv₂p (ρ' y))
    (by rw [evalZ_pull w hρs]; exact hw) hv'in
  rw [hvv] at hBin
  obtain ⟨s, hs, hsB⟩ := hBin
  have h0 := LinearMap.congr_fun₂ hsB y₀ y₀
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul] at h0
  have hnn : 0 ≤ ∑ j, s j * (γ j y₀ y₀ : ℝ) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hs j) (by exact_mod_cast hγ.nonneg j y₀)
  rw [le_div_iff₀ hy₀']
  linarith

end GlobalTheory.PolFan
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameGood
open ReciprocityTheory.L2DbarEstimates (V)

theorem goodBound_submatrix {n : ℕ} {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : K ≃ L) {S : Finset (Fin n)} {c : ℝ} {N : ℕ} {G : V n → Matrix L L ℂ} {v : V n}
    (h : GoodBound S c N G v) : GoodBound S c N (fun u => (G u).submatrix e e) v := by
  refine ⟨fun i j => h.entry (e i) (e j), ?_, ?_, ?_, ?_⟩
  · simpa only [det_submatrix_equiv_self] using h.det
  · intro a i j
    simpa only [GlobalTheory.HermFrame.conn_submatrix_equiv, Matrix.submatrix_apply]
      using h.form a (e i) (e j)
  · intro a b i j
    simpa only [GlobalTheory.HermFrame.curv_submatrix_equiv, Matrix.submatrix_apply]
      using h.dbar a b (e i) (e j)
  · intro a b i j
    have h1 : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn (fun x => (G x).submatrix e e) u ξ) =
        fun u => (GlobalTheory.HermFrame.conn G u ξ).submatrix e e :=
      fun ξ => funext fun u => GlobalTheory.HermFrame.conn_submatrix_equiv G e u ξ
    simp only [h1]
    exact h.del a b (e i) (e j)

theorem frame_summands_goodBound : ∀ (n g : ℕ) (S : Finset (Fin n)) (W : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin g) ℂ) (r : ℝ), IsOpen W → 0 < r → (∀ τ i k, DifferentiableOn ℂ (fun u => Q τ u i k) (Metric.ball 0 r)) → Fintype.card (Σ τ, Fin (m τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (m τ) => Q p.1 0 p.2) → (∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c N G₀ v) → (∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q τ v * G₀ v * (Q τ' v)ᴴ = 0) → ∃ r' : ℝ, 0 < r' ∧ ∃ (c' : ℝ) (N' : ℕ), ∀ v ∈ W, ‖v‖ < r' → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (fun u => Q τ u * G₀ u * (Q τ u)ᴴ) v := by
  intro n g S W G₀ c N ι _ _ m Q r hW hr hQ hcard hind hG₀ horth
  let K := Σ τ, Fin (m τ)
  let e : K ≃ Fin g := Fintype.equivFinOfCardEq hcard
  let P : V n → Matrix K K ℂ := fun u => Matrix.of fun p k => Q p.1 u p.2 (e k)
  let G₁ : V n → Matrix K K ℂ := fun u => (G₀ u).submatrix e e
  have hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r) := fun i k => hQ i.1 i.2 (e k)
  have hP0 : IsUnit (P 0).det := by
    rw [← isUnit_iff_isUnit_det, ← linearIndependent_row_iff_isUnit]
    have h2 := hind.map' _ (LinearEquiv.ker (LinearEquiv.funCongrLeft ℂ ℂ e))
    have h3 : (P 0).row = ⇑(LinearEquiv.funCongrLeft ℂ ℂ e) ∘ fun p => Q p.1 0 p.2 := by
      funext p k; rfl
    rw [h3]; exact h2
  have hG₁ : ∀ v ∈ W, (G₁ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₁ u i k) v) ∧
      GoodBound S c N G₁ v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hG₀ v hv
    exact ⟨by simpa [G₁, det_submatrix_equiv_self] using h1, fun i k => h2 (e i) (e k),
      goodBound_submatrix e h3⟩
  obtain ⟨r₁, hr₁, -, B, hB⟩ := GlobalTheory.T.holomorphicFrameChange_local_bounds n K P r hr hP hP0
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.mumfordGoodGrowthBound_holomorphic_frameChange n K S c N B
  let Gb : V n → Matrix K K ℂ := fun u => blockDiagonal' fun τ => Q τ u * G₀ u * (Q τ u)ᴴ
  obtain ⟨c', N', h3⟩ := GlobalTheory.T.mumfordGoodGrowthBound_blocks_of_blockDiagonal n S ι m (fun τ u => Q τ u * G₀ u * (Q τ u)ᴴ) c₁ N
  refine ⟨min r₁ (1 / 2), by positivity, c', N', fun v hv hvr τ => ?_⟩
  have hv1 : ‖v‖ < r₁ := hvr.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ < 1 / 2 := hvr.trans_le (min_le_right _ _)
  obtain ⟨hPu, hPc, hPd, hPb, hPib, hPdb, hPddb⟩ := hB v hv1
  obtain ⟨hdet, hC, hgb⟩ := hG₁ v hv
  obtain ⟨d1, c1, g1⟩ := hc₁ G₁ P v (by linarith) hdet hC hPc hPd hPu hPb hPib hPdb hPddb hgb
  have heq : ∀ u ∈ W, P u * G₁ u * (P u)ᴴ = Gb u := by
    intro u hu
    ext ⟨τ, i⟩ ⟨τ', j⟩
    have key : (P u * G₁ u * (P u)ᴴ) ⟨τ, i⟩ ⟨τ', j⟩ = (Q τ u * G₀ u * (Q τ' u)ᴴ) i j := by
      simp only [P, G₁, Matrix.mul_apply, conjTranspose_apply, of_apply, submatrix_apply]
      exact Fintype.sum_equiv e _ _ fun l => by
        congr 1
        exact Fintype.sum_equiv e _ _ fun k => rfl
    by_cases hτ : τ = τ'
    · subst hτ
      rw [key]
      simp only [Gb, blockDiagonal'_apply_eq]
    · rw [key, horth u hu τ τ' hτ]
      simp only [Gb, blockDiagonal'_apply_ne _ _ _ hτ, Matrix.zero_apply]
  have hev : (fun u => P u * G₁ u * (P u)ᴴ) =ᶠ[𝓝 v] Gb :=
    Filter.eventually_of_mem (hW.mem_nhds hv) heq
  refine h3 v (fun a _ => (PiLp.norm_apply_le v a).trans_lt hv2) ?_ ?_ ?_ τ
  · change (Gb v).det ≠ 0
    rw [← heq v hv]; exact d1
  · intro p q
    exact (c1 p q).congr_of_eventuallyEq (hev.mono fun u hu => by
      exact (congrFun (congrFun hu p) q).symm)
  · exact GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram n K S c₁ N _ Gb v hev g1

end GlobalTheory.FrameGood
end
end
