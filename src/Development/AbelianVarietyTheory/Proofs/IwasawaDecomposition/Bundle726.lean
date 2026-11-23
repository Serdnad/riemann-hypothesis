module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle717
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntFormDominatingPolFanBaseClassMinMeans
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem carrierDim_le_of_add_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  intro O _ bar q ψ lab hlab X _ _ _ _ hX b v hv β₀ hβ₀ hp₀ β hβ hp hin c₀ c hc₀ hc hrel
  obtain ⟨e, he, he'⟩ := hin
  have hw : ∀ k, 0 ≤ c₀ * e k + c k := fun k => add_nonneg (mul_nonneg hc₀.le (he k)) (hc k)
  have hcomb : toReal β = ∑ k, (c₀ * e k + c k) • toReal (v k) := by
    rw [hrel, he', Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, add_smul]
  have hβv : InRCone v β := ⟨_, hw, hcomb⟩
  have hne : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}).Nonempty := ⟨_, b, v, hv, hβv, rfl⟩
  obtain ⟨m, τ, hτ, hβτ, hrank⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hτ.strict
  have hψτ : ((ℓ β : ℤ) : ℝ) = N * ψ.evalZ β := by
    obtain ⟨d, hd, hde⟩ := hβτ
    rw [apply_eq_of_toReal_eq hde ℓ]
    have A := (linearOn_iff ψ τ).1 hτ.linear d hd
    rw [← hde, evalR_toReal] at A
    rw [A, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring
  have hψv : ψ.evalZ β = c₀ * ψ.evalZ β₀ + ∑ k, c k * ψ.evalZ (v k) := by
    have A := (linearOn_iff ψ v).1 hv.linear _ hw
    rw [← hcomb, evalR_toReal] at A
    have B := (linearOn_iff ψ v).1 hv.linear e he
    rw [← he', evalR_toReal] at B
    rw [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hℓv : ((ℓ β : ℤ) : ℝ) = c₀ * ℓ β₀ + ∑ k, c k * ℓ (v k) := by
    rw [apply_eq_of_toReal_eq hcomb ℓ, apply_eq_of_toReal_eq he' ℓ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k, (N : ℝ) * ψ.evalZ (v k) ≤ ℓ (v k) := fun k => h2 _ (hv.mem k) (hv.nonneg k)
  have h0 : (N : ℝ) * ψ.evalZ β₀ ≤ ℓ β₀ := h2 _ hβ₀ hp₀
  have heq : (N : ℝ) * ψ.evalZ β₀ = ℓ β₀ := by
    have hsum : ∑ k, c k * (N * ψ.evalZ (v k)) ≤ ∑ k, c k * (ℓ (v k) : ℝ) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hc k)
    have E : c₀ * (ℓ β₀ : ℝ) + ∑ k, c k * (ℓ (v k) : ℝ) = c₀ * (N * ψ.evalZ β₀) + ∑ k, c k * (N * ψ.evalZ (v k)) := by
      rw [← hℓv, hψτ, hψv, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    by_contra hne'
    have hlt : (N : ℝ) * ψ.evalZ β₀ < ℓ β₀ := lt_of_le_of_ne h0 hne'
    have := mul_lt_mul_of_pos_left hlt hc₀
    linarith
  obtain ⟨kk, d, hkk, hd⟩ := h3 β₀ hβ₀ hp₀ heq
  have hβ₀τ : InRCone τ β₀ := by
    refine ⟨fun i => (d i : ℝ) / kk, fun i => by positivity, LinearMap.ext₂ fun a b' => ?_⟩
    have h := LinearMap.congr_fun₂ hd a b'
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h
    have hR : (kk : ℝ) * (β₀ a b' : ℝ) = ∑ i, (d i : ℝ) * (τ i a b' : ℝ) := by exact_mod_cast h
    have hkR : (kk : ℝ) ≠ 0 := by positivity
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    calc (β₀ a b' : ℝ) = ((kk : ℝ) * (β₀ a b' : ℝ)) / kk := by field_simp
      _ = _ := by rw [hR, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have hle := Nat.sInf_le (s := {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β₀ ∧ genRank γ = k}) ⟨m, τ, hτ, hβ₀τ, rfl⟩
  rw [hlab X hX β hβ hp, hlab X hX β₀ hβ₀ hp₀]
  exact_mod_cast hle.trans hrank.le

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_of_inRCone_cell {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (hlin : φ.LinearOn G) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (G i) : ℝ) = N * φ.evalZ (G i))
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone G β) : (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff φ G).1 hlin c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring

theorem inRCone_of_nat_rel {X : Type} [AddCommGroup X] {n : ℕ} {δ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin n → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • δ i) : InRCone δ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * δ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * (β a b : ℝ) = ∑ i, (c i : ℝ) * (δ i a b : ℝ) := by exact_mod_cast h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ i, (c i : ℝ) * (δ i a b : ℝ)) / k from by rw [← h2]; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_cut_of_cell_le : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ,
      (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := by
  intro O _ bar φ X _ _ _ m n G δ hG hδ hin
  obtain ⟨NG, ℓG, hNG, g1, -, -⟩ := hG.strict
  obtain ⟨Nδ, ℓδ, hNδ, d1, d2, d3⟩ := hδ.strict
  have hNG' : (0 : ℝ) < NG := by exact_mod_cast hNG
  have key : ∀ β : LinearMap.BilinForm ℤ X, InRCone G β → (ℓG β : ℝ) = NG * φ.evalZ β :=
    fun β hβ => apply_eq_of_inRCone_cell hG.linear g1 hβ
  have hval : ∀ β : LinearMap.BilinForm ℤ X, (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) β : ℤ)) : ℝ) = NG * ℓδ β - Nδ * ℓG β :=
    fun β => by simp
  refine ⟨(NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG, fun j => ?_, fun k => ?_, fun β hβ hp hc h0 => ?_⟩
  · have h1 : (0 : ℝ) ≤ (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (G j) : ℤ)) : ℝ) := by
      rw [hval, g1 j]
      have := d2 (G j) (hG.mem j) (hG.nonneg j)
      nlinarith
    exact_mod_cast h1
  · have h1 : (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (δ k) : ℤ)) : ℝ) = 0 := by
      rw [hval, key _ (hin k), d1 k]; ring
    exact_mod_cast h1
  · have h1 := hval β
    rw [h0, key β hc] at h1
    have h2 : (Nδ : ℝ) * φ.evalZ β = ℓδ β := by
      have : (NG : ℝ) * ((Nδ : ℝ) * φ.evalZ β - ℓδ β) = 0 := by push_cast at h1; linarith
      have := (mul_eq_zero.1 this).resolve_left hNG'.ne'
      linarith
    obtain ⟨k, c, hk, e⟩ := d3 β hβ hp h2
    exact inRCone_of_nat_rel hk e

end GlobalTheory.PolFan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem inRCone_of_interior_linearOn {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m k : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X) (hγ : IsCell bar φ γ)
    (hmem : ∀ i, γ' i ∈ balForms bar X) (hpos : ∀ i y, 0 ≤ γ' i y y) (hlin : φ.LinearOn γ')
    (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ i, 0 < b i)
    (e1 : toReal β = ∑ j, a j • toReal (γ j)) (e2 : toReal β = ∑ i, b i • toReal (γ' i)) (i : Fin k) :
    InRCone γ (γ' i) := by
  have hev : ∀ {p : ℕ} (δ : Fin p → LinearMap.BilinForm ℤ X) (c : Fin p → ℝ), (∀ j, 0 ≤ c j) → φ.LinearOn δ →
      toReal β = ∑ j, c j • toReal (δ j) → φ.evalZ β = ∑ j, c j * φ.evalZ (δ j) := by
    intro p δ c hc hl e
    rw [← hl c hc]
    unfold InvFun.evalZ
    congr 1
    funext x y
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ e x y
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have ea := hev γ a ha hγ.linear e1
  have eb := hev γ' b (fun i => (hb i).le) hlin e2
  have la := apply_eq_of_toReal_eq e1 ℓ
  have lb := apply_eq_of_toReal_eq e2 ℓ
  have hsum : ∑ i, b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← lb, sub_eq_zero, la]
    have e3 : ∑ i, b i * ((N : ℝ) * φ.evalZ (γ' i)) = N * φ.evalZ β := by
      rw [eb, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e3, ea, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [h1 j]; ring
  have hnn : ∀ i, 0 ≤ b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) := fun i =>
    mul_nonneg (hb i).le (sub_nonneg.2 (h2 _ (hmem i) (hpos i)))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hsum i (Finset.mem_univ _)
  have heq : (N : ℝ) * φ.evalZ (γ' i) = ℓ (γ' i) := by
    have := (mul_eq_zero.1 hz).resolve_left (hb i).ne'
    linarith
  obtain ⟨kk, c, hk, hc⟩ := h3 _ (hmem i) (hpos i) heq
  have hkR : (kk : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun j => (c j : ℝ) / kk, fun j => by positivity, LinearMap.ext₂ fun x y => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc x y
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h4
  have h5 : (kk : ℝ) * (γ' i x y : ℝ) = ∑ j, (c j : ℝ) * (γ j x y : ℝ) := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have h6 : (γ' i x y : ℝ) = (∑ j, (c j : ℝ) * (γ j x y : ℝ)) / kk := by
    rw [eq_div_iff hkR, ← h5]; ring
  rw [h6, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem inRCone_of_interior_linearOn' : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m k : ℕ}
  (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X), IsCell bar φ γ → (∀ i, γ' i ∈ balForms bar X) →
  (∀ i y, 0 ≤ γ' i y y) → φ.LinearOn γ' →
  ∀ (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ), (∀ j, 0 ≤ a j) → (∀ i, 0 < b i) →
    toReal β = ∑ j, a j • toReal (γ j) → toReal β = ∑ i, b i • toReal (γ' i) → ∀ i, InRCone γ (γ' i) := by
  intro O _ bar φ X _ _ _ m k γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i
  exact inRCone_of_interior_linearOn bar φ γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i

end GlobalTheory.PolFan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

theorem inRCone_of_evalZ_sum_le (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγ : IsCell bar ψ γ) (k : ℕ)
    (u : Fin k → LinearMap.BilinForm ℤ X) (hu : ∀ j, u j ∈ balForms bar X) (hp : ∀ j y, 0 ≤ u j y y)
    (hs : InRCone γ (∑ j, u j)) (hle : ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j)) : ∀ j, InRCone γ (u j) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨c, hc, e⟩ := hs
  have hsum : ψ.evalZ (∑ j, u j) = ∑ i, c i * ψ.evalZ (γ i) := by
    rw [← hγ.linear c hc]
    unfold InvFun.evalZ
    congr 1
    funext a b
    have := LinearMap.congr_fun₂ e a b
    simpa [LinearMap.sum_apply] using this
  have hℓ : (ℓ (∑ j, u j) : ℝ) = N * ψ.evalZ (∑ j, u j) := by
    rw [apply_eq_of_toReal_eq e ℓ, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]; ring
  have hd : ∀ j, 0 ≤ (ℓ (u j) : ℝ) - N * ψ.evalZ (u j) := fun j => sub_nonneg.2 (h2 _ (hu j) (hp j))
  have hz : ∑ j, ((ℓ (u j) : ℝ) - N * ψ.evalZ (u j)) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun j _ => hd j)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 : (∑ j, (ℓ (u j) : ℝ)) = ℓ (∑ j, u j) := by rw [map_sum]; push_cast; rfl
    rw [e1, hℓ]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left hle h0]
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hd j).1 hz j (Finset.mem_univ _)
  obtain ⟨n, c', hn, hc'⟩ := h3 _ (hu j) (hp j) (by linarith)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i => (c' i : ℝ) / n, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc' a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h4
  have h5 : (n : ℝ) * u j a b = ∑ i, (c' i : ℝ) * γ i a b := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show ∑ i, (c' i : ℝ) / n * (γ i a b : ℝ) = (∑ i, (c' i : ℝ) * γ i a b) / n by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, ← h5]
  field_simp

end GlobalTheory.PolFan.Mark
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace ConeMatch

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem coef_eq {n : ℕ} {P : Fin n → V} (hP : LinearIndependent ℝ P) {a b : Fin n → ℝ}
    (h : ∑ i, a i • P i = ∑ i, b i • P i) : a = b := by
  have := Fintype.linearIndependent_iff.1 hP (a - b) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i; exact sub_eq_zero.1 (this i)

theorem exists_pos_of_sum_eq_one {n : ℕ} (f : Fin n → ℝ) (h : ∑ i, f i = 1) : ∃ i, 0 < f i := by
  by_contra hc
  push_neg at hc
  have : ∑ i, f i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
  linarith

theorem match_vec {k m : ℕ} (P : Fin k → V) (Q : Fin m → V) (hP : LinearIndependent ℝ P)
    (hQ : LinearIndependent ℝ Q) (t : Fin k → ℝ) (c : Fin m → ℝ) (ht : ∀ i, 0 < t i) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ i, t i • P i = ∑ j, c j • Q j)
    (hPQ : ∀ i, ∃ a : Fin m → ℝ, (∀ j, 0 ≤ a j) ∧ P i = ∑ j, a j • Q j)
    (hQP : ∀ j, 0 < c j → ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ Q j = ∑ l, b l • P l) :
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ P i = d • Q j) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ P i = d • Q j ∧ c j = t i * d) := by
  choose D hD0 hD using hPQ
  have hQP' : ∀ j, ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ (0 < c j → Q j = ∑ l, b l • P l) := fun j => by
    by_cases h : 0 < c j
    · obtain ⟨b, hb, e⟩ := hQP j h
      exact ⟨b, hb, fun _ => e⟩
    · exact ⟨0, fun _ => le_rfl, fun h' => absurd h' h⟩
  choose E hE0 hE using hQP'

  have hcD : ∀ j, c j = ∑ i, t i * D i j := by
    have h1 : ∑ j, c j • Q j = ∑ j, (∑ i, t i * D i j) • Q j := by
      rw [← hsum]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (coef_eq hQ h1)
  have hDz : ∀ i j, ¬ 0 < c j → D i j = 0 := fun i j h => by
    have h0 : c j = 0 := le_antisymm (not_lt.1 h) (hc j)
    rw [hcD j] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (ht i).le (hD0 i j)).1 h0 i
      (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (ht i).ne'
  have hDQ : ∀ i j, D i j • Q j = D i j • ∑ l, E j l • P l := fun i j => by
    by_cases h : 0 < c j
    · rw [← hE j h]
    · simp [hDz i j h]
  have hDE : ∀ i l, ∑ j, D i j * E j l = if i = l then 1 else 0 := by
    intro i l
    have h1 : ∑ l, (if i = l then (1 : ℝ) else 0) • P l = ∑ l, (∑ j, D i j * E j l) • P l := by
      rw [show ∑ l, (if i = l then (1 : ℝ) else 0) • P l = P i by simp [ite_smul]]
      conv_lhs => rw [hD i]
      simp only [hDQ, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hP h1) l).symm
  have hED : ∀ j, 0 < c j → ∀ j', ∑ l, E j l * D l j' = if j = j' then 1 else 0 := by
    intro j hj j'
    have h1 : ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = ∑ j', (∑ l, E j l * D l j') • Q j' := by
      rw [show ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = Q j by simp [ite_smul]]
      conv_lhs => rw [hE j hj]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hQ h1) j').symm
  have single : ∀ i j, 0 < D i j * E j i → 0 < c j ∧ 0 < D i j ∧ P i = D i j • Q j := by
    intro i j hpos
    have hcj : 0 < c j := by
      by_contra h
      rw [hDz i j h, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hEne : E j i ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    have hDpos : 0 < D i j := lt_of_le_of_ne (hD0 i j) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl _ hpos
    have hoff : ∀ j', j' ≠ j → D i j' = 0 := fun j' hj' => by
      have hle : E j i * D i j' ≤ ∑ l, E j l * D l j' :=
        Finset.single_le_sum (f := fun l => E j l * D l j') (fun l _ => mul_nonneg (hE0 j l) (hD0 l j'))
          (Finset.mem_univ i)
      rw [hED j hcj j', if_neg (Ne.symm hj')] at hle
      have h0 : E j i * D i j' = 0 := le_antisymm hle (mul_nonneg (hE0 j i) (hD0 i j'))
      exact (mul_eq_zero.1 h0).resolve_left hEne
    refine ⟨hcj, hDpos, ?_⟩
    rw [hD i, Finset.sum_eq_single j (fun j' _ hj' => by rw [hoff j' hj', zero_smul])
      (fun h => absurd (Finset.mem_univ j) h)]
  refine ⟨fun i => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj⟩ := exists_pos_of_sum_eq_one _ ((hDE i i).trans (if_pos rfl))
    obtain ⟨hcj, hd, e⟩ := single i j hj
    exact ⟨j, hcj, D i j, hd, e⟩
  · obtain ⟨l, hl⟩ := exists_pos_of_sum_eq_one _ ((hED j hj j).trans (if_pos rfl))
    have hl' : 0 < D l j * E j l := by rw [mul_comm]; exact hl
    obtain ⟨-, hd, e⟩ := single l j hl'
    have hEne : E j l ≠ 0 := fun h => by rw [h, zero_mul] at hl; exact lt_irrefl _ hl
    have hoff : ∀ i, i ≠ l → D i j = 0 := fun i hi => by
      have hle : D i j * E j l ≤ ∑ j'', D i j'' * E j'' l :=
        Finset.single_le_sum (f := fun j'' => D i j'' * E j'' l) (fun j'' _ => mul_nonneg (hD0 i j'') (hE0 j'' l))
          (Finset.mem_univ j)
      rw [hDE i l, if_neg hi] at hle
      have h0 : D i j * E j l = 0 := le_antisymm hle (mul_nonneg (hD0 i j) (hE0 j l))
      exact (mul_eq_zero.1 h0).resolve_right hEne
    refine ⟨l, D l j, hd, e, ?_⟩
    rw [hcD j, Finset.sum_eq_single l (fun i _ hi => by rw [hoff i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ l) h)]

end ConeMatch

section Forms

variable {X : Type} [AddCommGroup X]

theorem linearIndependent_toReal {n : ℕ} {p : Fin n → LinearMap.BilinForm ℤ X} (hp : LinearIndependent ℤ p) :
    LinearIndependent ℝ fun i => toReal (p i) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin n → ℤ), ∑ j, c j • p j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c h => by
    funext i
    exact Fintype.linearIndependent_iff.1 hp c (by simpa using h) i
  have := eq_zero_of_toReal_rel (u := p) (v := (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X)) hind
    (r := g) (s := 0) (by simpa using hg)
  exact fun i => congrFun this i

theorem cone_match_rays {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X)
    (δ : Fin m → LinearMap.BilinForm ℤ X) :
    LinearIndependent ℤ p → LinearIndependent ℤ δ →
    ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) →
      ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
      (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
      (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
      (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) :=
  fun hp hδ t c ht hc hsum hpδ hδp =>
    ConeMatch.match_vec (fun i => toReal (p i)) (fun j => toReal (δ j)) (linearIndependent_toReal hp)
      (linearIndependent_toReal hδ) t c ht hc hsum hpδ hδp

end Forms

end GlobalTheory.PolFan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem inRCone_of_apply_eq_zero {X : Type} [AddCommGroup X] {m p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X) (hnn : ∀ i, 0 ≤ h (δ i))
    (hz : ∀ i, h (δ i) = 0 → i ∈ Set.range e) (hβ : InRCone δ β) (hβ0 : h β = 0) :
    InRCone (fun k => δ (e k)) β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have happ := apply_eq_of_toReal_eq hsum h
  rw [hβ0, Int.cast_zero] at happ
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)), c i * (h (δ i) : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hnn i)).1 happ.symm
  have hvan : ∀ i, i ∉ Set.range e → c i = 0 := by
    intro i hi
    rcases mul_eq_zero.1 (hterm i (Finset.mem_univ i)) with h1 | h1
    · exact h1
    · exact absurd (hz i (by exact_mod_cast h1)) hi
  refine ⟨fun k => c (e k), fun k => hc (e k), ?_⟩
  rw [hsum, ← Finset.sum_map Finset.univ e (fun i => c i • toReal (δ i))]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have : i ∉ Set.range e := by
    rintro ⟨k, rfl⟩
    exact hi (Finset.mem_map_of_mem e (Finset.mem_univ k))
  rw [hvan i this, zero_smul]

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.exists_cell_of_contactSet_intInequalities : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)), A.Finite → 0 < K → (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → (∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β)) → (∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) → (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → ∑ i, t i • toReal (u i) ∈ realForms bar X → (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  first | exact @GlobalTheory.PolCell.exists_isCell_of_contact | exact GlobalTheory.PolCell.exists_isCell_of_contact | (intros; apply GlobalTheory.PolCell.exists_isCell_of_contact <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.exists_intForm_dominating_polFanBase_classMinMeans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
  first | exact @GlobalTheory.PolCell.exists_contact_baseFun_lamW | exact GlobalTheory.PolCell.exists_contact_baseFun_lamW | (intros; apply GlobalTheory.PolCell.exists_contact_baseFun_lamW <;> assumption)
end
