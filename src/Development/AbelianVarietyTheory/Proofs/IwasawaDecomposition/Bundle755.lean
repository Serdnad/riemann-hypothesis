module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle714
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle728
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle729
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle752
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle727
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle713
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle709
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx


theorem _root_.GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) = ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
  first | exact @GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart | exact GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart | (intros; apply GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey.OffCell

theorem lin_eq_sum {X : Type} [AddCommGroup X] {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    {t : Fin n → ℝ} (hsum : toReal β = ∑ i, t i • toReal (u i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, t i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) t : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem inRCone_of_sum {X : Type} [AddCommGroup X] {n m : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hsum : toReal β = ∑ i, t i • toReal (u i)) (h : ∀ i, t i ≠ 0 → InRCone γ (u i)) : InRCone γ β := by
  have h' : ∀ i, ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ t i • toReal (u i) = ∑ j, c j • toReal (γ j) := fun i => by
    by_cases h0 : t i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    · obtain ⟨c, hc, e⟩ := h i h0
      refine ⟨fun j => t i * c j, fun j => mul_nonneg (ht i) (hc j), ?_⟩
      rw [e, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  choose c hc e using h'
  refine ⟨fun j => ∑ i, c i j, fun j => Finset.sum_nonneg fun i _ => hc i j, ?_⟩
  rw [hsum, Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem inRCone_of_nsmul {X : Type} [AddCommGroup X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin m → ℕ} (hk : 0 < k) (e : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun i => c i / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := congrArg (fun B : LinearMap.BilinForm ℤ X => ((B a b : ℤ) : ℝ)) e
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h1
  push_cast at h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hk'.ne'
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem arith {K N C b h₀ f ps h l p : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hb : 0 ≤ b) (hh₀ : 1 ≤ h₀) (hf : 1 ≤ f)
    (hfe : f = l - N * p) (hp : p ≤ b) (hps : ps ≤ 1) (hh : -h ≤ C * l) (hK : N + N * C + N ^ 2 * C * b + 1 ≤ K) :
    N * h₀ * ps - N * h < K * h₀ * (l - N * p) := by
  rw [← hfe]
  have hl : l = f + N * p := by linarith
  have hhf : 1 ≤ h₀ * f := by nlinarith
  have a1 : (N + N * C + N ^ 2 * C * b + 1) * (h₀ * f) ≤ K * (h₀ * f) := by gcongr
  have a2 : N * h₀ * ps ≤ N * (h₀ * f) := by
    rw [mul_assoc]; gcongr; linarith
  have a3 : N * C * f ≤ N * C * (h₀ * f) := by
    gcongr; nlinarith
  have a4 : N ^ 2 * C * b ≤ N ^ 2 * C * b * (h₀ * f) := le_mul_of_one_le_right (by positivity) hhf
  have a5 : N * (-h) ≤ N * (C * l) := by gcongr
  have a6 : N ^ 2 * C * p ≤ N ^ 2 * C * b := by gcongr
  rw [hl] at a5
  nlinarith

theorem off_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (b : ℕ), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  intro E _ _ _ H q ψ w b hψ hw X _ _ _ _ hX hgen m γ N ℓ hγ hN hsw β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos C hC K hK β hβ hβn
    hoff
  have hon := (GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hw X hX m γ hγ β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos).1
  obtain ⟨n, u, hu, hun, hlψ, hlp, hub, hu1, t, ht, hsum⟩ := hgen β hβ hβn
  have hh₀ : (1 : ℝ) ≤ h β₀ := by exact_mod_cast hpos
  have hoffu : ∀ i, ¬ InRCone γ (u i) → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) <
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i hi => by
    obtain ⟨z, hz⟩ := (hψ X hX).integral (u i) (hu i) (hun i)
    have hle := hsw.2.1 (u i) (hu i) (hun i)
    have hne : (N : ℝ) * ψ.evalZ (u i) ≠ ℓ (u i) := fun e => by
      obtain ⟨k, c, hk, e'⟩ := hsw.2.2 (u i) (hu i) (hun i) e
      exact hi (inRCone_of_nsmul hk e')
    have hlt : (N : ℤ) * z < ℓ (u i) := by
      have := lt_of_le_of_ne hle hne
      rw [hz] at this
      exact_mod_cast this
    have hf : (1 : ℝ) ≤ ℓ (u i) - N * ψ.evalZ (u i) := by
      rw [hz]
      have : (1 : ℤ) ≤ ℓ (u i) - N * z := by omega
      exact_mod_cast this
    refine arith (C := C) (b := b) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh₀ hf rfl (hub i) (hu1 i) ?_ ?_
    · exact_mod_cast hC (u i) (hu i) (hun i)
    · exact_mod_cast hK
  have hall : ∀ i, (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) ≤
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i => by
    by_cases hi : InRCone γ (u i)
    · rw [ell_eq_of_inRCone hγ.linear hsw hi, sub_self, mul_zero, mul_assoc, ← mul_sub]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.2 (hon _ (hu i) (hun i) hi))
    · exact (hoffu i hi).le
  obtain ⟨i₀, hi₀, hi₀'⟩ : ∃ i, t i ≠ 0 ∧ ¬ InRCone γ (u i) := by
    by_contra hcon
    exact hoff (inRCone_of_sum ht hsum fun i hi => by_contra fun h' => hcon ⟨i, hi, h'⟩)
  have e1 : ψ.evalZ β = ∑ i, t i * ψ.evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff ψ u).1 hlψ t ht
  have e2 : (starDepth H.bar ψ w).evalZ β = ∑ i, t i * (starDepth H.bar ψ w).evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff _ u).1 hlp t ht
  have key : ∑ i, t i * ((N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i)) <
      ∑ i, t i * (K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i))) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hall i) (ht i))
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hoffu i₀ hi₀') (lt_of_le_of_ne (ht i₀) hi₀.symm)⟩
  rw [e1, e2, lin_eq_sum hsum h, lin_eq_sum hsum ℓ]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  convert key using 2 with i _ i _ <;> ring

end GlobalTheory.PolFan.StarKey.OffCell
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarGens

section General

variable {O : Type} [CommRing O] {bar : O → O} {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  [AddCommGroup Y] [Module O Y] [Module.Finite O Y]

theorem transport {φ χ : InvFun O} {b : ℕ} (e : X ≃ₗ[O] Y) {β : LinearMap.BilinForm ℤ Y}
    (h : ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧
      InRCone u (pull e.toLinearMap β)) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ Y), (∀ i, u i ∈ balForms bar Y) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨n, u, h1, h2, h3, h4, h5, h6, c, hc, h7⟩ := h
  refine ⟨n, fun i => pull e.symm.toLinearMap (u i), fun i => pull_mem _ (h1 i), fun i y => h2 i _,
    (linearOn_pull_iff e.symm.surjective).2 h3, (linearOn_pull_iff e.symm.surjective).2 h4,
    fun i => by rw [evalZ_pull φ e.symm.surjective]; exact h5 i,
    fun i => by rw [evalZ_pull χ e.symm.surjective]; exact h6 i, c, hc, LinearMap.ext₂ fun x y => ?_⟩
  have := LinearMap.congr_fun₂ h7 (e.symm x) (e.symm y)
  simpa [LinearMap.sum_apply] using this

theorem linearOn_starDepth {ψ w : InvFun O} {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    (h : (starFun bar ψ w 0 1).LinearOn u) : (starDepth bar ψ w).LinearOn u := by
  rw [linearOn_iff] at h ⊢
  intro c hc
  simpa [starFun_evalR, starFun_evalZ] using h c hc


omit [Module O X] [Module.Finite O X] in
theorem mul_le_of_sub_mem_rcone {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hγ : ∀ i, 0 ≤ h (γ i)) {β v : LinearMap.BilinForm ℤ X} {t : ℝ} (hm : toReal β - t • toReal v ∈ rcone γ) :
    t * (h v : ℝ) ≤ h β := by
  obtain ⟨g, hg, hBg⟩ := hm
  have key := apply_eq_of_toReal_eq (β := β) (γ := Fin.cons v γ) (c := Fin.cons t g) (by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← hBg]; abel) h
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at key
  have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hγ i)
  linarith

theorem exists_nat_bound {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) : ∃ b : ℕ, ∀ x ∈ S, f x ≤ b := by
  obtain ⟨r, hr⟩ := (hS.image f).bddAbove
  exact ⟨⌈r⌉₊, fun x hx => (hr ⟨x, hx, rfl⟩).trans (Nat.le_ceil r)⟩

end General

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {q : ℕ} {ψ w : InvFun (𝓞 E)}

theorem centres_finite (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q)
    {S : Set (LinearMap.BilinForm ℤ X)} (hS : S.Finite) :
    {v | v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell H.bar ψ γ ∧ (∀ i, γ i ∈ S) ∧ InRCone γ v}.Finite := by
  refine (hS.finite_subsets.biUnion (t := fun T => {v | v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧ InRCone γ v})
    fun T _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩ v' ⟨b1, b2, b3, m', γ', -, b5, b6⟩
    refine (hw X hX).2.2 m γ a4 v a1 a2 v' b1 b2 a3 b3 a6 (inRCone_trans (fun j => ?_) b6)
    obtain ⟨i, hi⟩ : γ' j ∈ Set.range γ := by rw [a5, ← b5]; exact ⟨j, rfl⟩
    rw [← hi]; exact inRCone_self γ i
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩
    exact Set.mem_biUnion (x := Set.range γ) (by rintro _ ⟨i, rfl⟩; exact a5 i) ⟨a1, a2, a3, m, γ, a4, rfl, a6⟩

theorem of_cell (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {b m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell H.bar ψ γ) (hb : ∀ i, ψ.evalZ (γ i) ≤ b)
    (hb' : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → ψ.evalZ v ≤ b)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨hC1, hC2, hC3⟩ := hw X hX
  obtain ⟨lin1, lin2⟩ := GlobalTheory.T.starSubdivision_function_linearOn_cells E H q ψ w 0 1 hw
  by_cases hc : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hv, hvp, hvw, hvin⟩ := hc
    have hne : v ≠ 0 := by
      rintro rfl
      have := hC2 0 hv hvp hvw 2 0 (by simp)
      norm_num at this
    obtain ⟨m', s, h, hcut, hh, hin⟩ := GlobalTheory.StarCover.star_cover X m γ v (toReal β) (fun i => (hγ.mem i).1)
      hγ.nonneg hne hvin hβ
    have hh' : (0 : ℝ) < h v := by exact_mod_cast hh
    have hmem : ∀ j, InRCone γ ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) := fun j =>
      Fin.cases (by simpa using hvin) (fun k => by simpa using inRCone_self γ (s k)) j
    have hle : ∀ j, (h ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) : ℝ) ≤ h v := fun j =>
      Fin.cases (by simp) (fun k => by
        simp only [Fin.cons_succ]; rw [(hcut.2 (s k)).2 ⟨k, rfl⟩]; simpa using hh.le) j
    refine ⟨m' + 1, Fin.cons v fun j => γ (s j), fun j => Fin.cases hv (fun k => hγ.mem (s k)) j,
      fun j => Fin.cases hvp (fun k => hγ.nonneg (s k)) j, linearOn_of_forall_inRCone ψ hγ.linear hmem,
      linearOn_starDepth (lin2 X hX m γ hγ v hv hvp hvw hvin m' s h hcut hh),
      fun j => Fin.cases (hb' v hv hvp hvw hvin) (fun k => hb (s k)) j, fun j => ?_, hin⟩
    rw [← evalR_toReal]
    refine evalR_starDepth_le _ H.bar ψ w X m γ _ 1 hγ (hmem j) zero_le_one fun v' a1 a2 a3 a4 t _ ht => ?_
    rw [hC3 m γ hγ v' a1 a2 v hv hvp a3 hvw a4 hvin] at ht
    have := (mul_le_of_sub_mem_rcone hcut.1 ht).trans (hle j)
    nlinarith
  · have hno : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0 := fun v a1 a2 a3 =>
      (hC1 v a1 a2).resolve_right fun a4 => hc ⟨v, a1, a2, a4, a3⟩
    refine ⟨m, γ, hγ.mem, hγ.nonneg, hγ.linear, linearOn_starDepth (lin1 X hX m γ hγ hno), hb, fun j => ?_, hβ⟩
    rw [← evalR_toReal]
    exact evalR_starDepth_le _ H.bar ψ w X m γ _ 1 hγ (inRCone_self γ j) zero_le_one fun v' a1 a2 a3 a4 _ _ _ =>
      (hc ⟨v', a1, a2, a3, a4⟩).elim

theorem per_module (hψ : IsPolyFan H.bar q ψ) (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) :
    ∃ b : ℕ, ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨b, hb⟩ := exists_nat_bound (hS.union (centres_finite H hw X hX hS)) fun v => ψ.evalZ v
  refine ⟨b, fun β hβ hp => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hsum⟩ := hcov _ (toReal_mem_psdCone_of_nonneg E H X β hβ hp)
  refine transport e (of_cell H hw X hX hγ (fun i => hb _ (Or.inl (hγS i)))
    (fun v a1 a2 a3 a4 => hb _ (Or.inr ⟨a1, a2, a3, m, γ, hγ, hγS, a4⟩)) ⟨c, hc, ?_⟩)
  rw [← hsum]
  exact LinearMap.ext₂ fun x y => by simp

end CM

theorem exists_bounded_gens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ b : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  intro E _ _ _ H q ψ w hψ hw
  obtain ⟨n, R, hR, hiso⟩ := GlobalTheory.exists_fin_reps_projective_finrank_le E q
  have key := fun k => @per_module E _ _ _ H q ψ w hψ hw (R k) _ _ (hR k).1 (hR k).2.1 (hR k).2.2
  choose b hb using key
  refine ⟨Finset.univ.sup b, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hiso X hX
  haveI := (hR k).1
  obtain ⟨m, u, h1, h2, h3, h4, h5, h6, h7⟩ := hb k (pull f.symm.toLinearMap β) (pull_mem _ hβ) fun y => hp _
  have hk : (b k : ℝ) ≤ (Finset.univ.sup b : ℕ) := by exact_mod_cast Finset.le_sup (f := b) (Finset.mem_univ k)
  exact transport f.symm ⟨m, u, h1, h2, h3, h4, fun i => (h5 i).trans hk, h6, h7⟩

end GlobalTheory.PolFan.StarGens
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem orbMark_coord_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro E _ _ _ H φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms H.bar (δ j) (h.mem j) (hprim j)
    have hd1 := (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory
end
