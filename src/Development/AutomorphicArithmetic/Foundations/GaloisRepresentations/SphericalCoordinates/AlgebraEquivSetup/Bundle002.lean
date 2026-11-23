module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfMulL :
    TfAdm → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulL := by
  intro hAdm hAc hIff X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g₀
  set Φ : X → ℂ := fun y => T.tf r (y⁻¹ * g₀) with hΦ
  have hTy : T.IsTy Φ := by
    intro k hk g
    have hki : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [hΦ, mul_inv_rev, mul_assoc]
    rw [((hAdm X M T r hr).2 k⁻¹ hki (g⁻¹ * g₀)).1, smul_eq_mul]
    congr 2
    have e : (⟨T.L.pr k⁻¹, T.fact.2 _ hki⟩ : T.J) = (⟨T.L.pr k, T.fact.2 _ hk⟩ : T.J)⁻¹ :=
      Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
  have key := hAc X M M' T L' Kw hF hAp t 1 ⟨fun g => by group, map_one _⟩ ℂ Φ hTy 1
  have lhs : conv T.K₀ (T.tf (L'.loc t)) (T.tf r) g₀ = Formalism.UG.hAct T.K₀ (T.tf (L'.loc t * 1)) Φ 1 := by
    simp [conv, Formalism.UG.hAct, hΦ, smul_eq_mul]
  rw [lhs, key]
  have memKrK : ∀ y, y ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K → L'.pr y ∈ Kw := by
    intro y hy
    rw [DoubleCoset.mem_doubleCoset] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    simp only [map_mul, hr', mul_one]
    exact Kw.mul_mem (hF.2 a ha) (hF.2 b hb)
  simp only [hΦ, one_mul, smul_eq_mul]
  rw [finsum_eq_single _ ((L'.pr g₀ : M' ⧸ Kw)) ?_]
  · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr g₀)
    rw [hw]
    have h1 : (L'.pr g₀ * w ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw) ↔
        L'.pr g₀ ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨a, ha, b * (w : M')⁻¹, Kw.mul_mem hb (Kw.inv_mem w.2), ?_⟩
        calc L'.pr g₀ = L'.pr g₀ * w * (w : M')⁻¹ := by group
          _ = a * t * b * (w : M')⁻¹ := by rw [e]
          _ = a * t * (b * (w : M')⁻¹) := by group
      · rintro ⟨a, ha, b, hb, e⟩
        exact ⟨a, ha, b * w, Kw.mul_mem hb w.2, by rw [e]; group⟩
    have h2 : ((L'.loc (L'.pr g₀ * w))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K) ↔
        (L'.loc (L'.pr g₀))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      have hwK : L'.loc w ∈ T.K := hF.1 w w.2
      have e : (L'.loc (L'.pr g₀ * w))⁻¹ * g₀ = (L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀) := by
        rw [map_mul, mul_inv_rev, mul_assoc]
      rw [e]
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e2⟩
        refine ⟨L'.loc w * a, T.K.mul_mem hwK ha, b, hb, ?_⟩
        calc (L'.loc (L'.pr g₀))⁻¹ * g₀
            = L'.loc w * ((L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀)) := by group
          _ = L'.loc w * (a * r * b) := by rw [e2]
          _ = L'.loc w * a * r * b := by group
      · rintro ⟨a, ha, b, hb, e2⟩
        exact ⟨(L'.loc w)⁻¹ * a, T.K.mul_mem (T.K.inv_mem hwK) ha, b, hb, by rw [e2]; group⟩
    have hprm : ∀ m, T.L.pr ((L'.loc m)⁻¹ * g₀) = T.L.pr g₀ := by
      intro m
      rw [map_mul, map_inv, hAp.1, inv_one, one_mul]
    simp only [TyLev.tf, dosetInd, Set.indicator_apply, Pi.one_apply, hprm, h1, h2,
      hIff X M' L' T.K Kw hF t r hr' g₀]
    split_ifs <;> simp_all
  · intro x hx
    have hy : (L'.loc (Quotient.out x))⁻¹ * g₀ ∉ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      intro hm
      apply hx
      have hh := memKrK _ hm
      rw [map_mul, map_inv, L'.pr_loc] at hh
      rw [← QuotientGroup.out_eq' x]
      exact QuotientGroup.eq.2 hh
    simp [TyLev.tf, dosetInd, Set.indicator_apply, hy]
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem mul_mem_doubleCoset_iff_of_mem {X : Type} [Group X] (K : Subgroup X) (a g k : X) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set X) K ↔ g ∈ DoubleCoset.doubleCoset a (K : Set X) K := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k⁻¹, K.mul_mem hy (K.inv_mem hk), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k, K.mul_mem hy hk, by rw [h, mul_assoc]⟩

private theorem loc_mem_doubleCoset_loc_iff {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw) (t z : M') :
    L'.loc z ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K ↔
      z ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    refine ⟨L'.pr x, hF.2 x hx, L'.pr y, hF.2 y hy, ?_⟩
    have h' := congrArg L'.pr h
    simpa [map_mul, L'.pr_loc] using h'
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨L'.loc x, hF.1 x hx, L'.loc y, hF.1 y hy, by rw [h, map_mul, map_mul]⟩

theorem UpperTheory.Gal.W2.Seed.pDosetCosets :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
  intro X M' _ _ L' K Kw hF t V _ _ Ψ hΨ
  set f : X ⧸ K → V := fun y => dosetInd ℂ K (L'.loc t) y.out • Ψ y.out with hf
  let φ : M' ⧸ Kw → X ⧸ K := fun x => ((L'.loc x.out : X) : X ⧸ K)
  have hφ : Function.Injective φ := by
    intro x x' h
    simp only [φ, QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x', QuotientGroup.eq]
    have h2 := hF.2 _ h
    simpa [map_mul, map_inv, L'.pr_loc] using h2
  have hφf : ∀ x, f (φ x) = dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (L'.loc x.out)
    simp only [hf, φ, hk]
    rw [hΨ k k.2]
    simp only [dosetInd, Set.indicator, mul_mem_doubleCoset_iff_of_mem K _ _ _ k.2, loc_mem_doubleCoset_loc_iff L' K Kw hF,
      Pi.one_apply]
  have hsupp : Function.support f ⊆ Set.range φ := by
    intro y hy
    rw [Function.mem_support] at hy
    have hmem : y.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
      by_contra hn
      apply hy
      simp [hf, dosetInd, hn]
    rw [DoubleCoset.mem_doubleCoset] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    refine ⟨((L'.pr a * t : M') : M' ⧸ Kw), ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr a * t)
    simp only [φ, hk]
    rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
    set n := a * (L'.loc (L'.pr a))⁻¹ with hn
    have hn1 : L'.pr n = 1 := by simp [hn, L'.pr_loc]
    have hnK : n ∈ K := K.mul_mem ha (K.inv_mem (hF.1 _ (hF.2 a ha)))
    have hy' : y.out = L'.loc (L'.pr a * t) * (n * b) := by
      calc y.out = a * L'.loc t * b := hab
        _ = n * L'.loc (L'.pr a * t) * b := by simp [hn, map_mul, mul_assoc]
        _ = L'.loc (L'.pr a * t) * n * b := by rw [L'.comm _ n hn1]
        _ = _ := mul_assoc _ _ _
    rw [hy', map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact K.mul_mem (K.inv_mem (hF.1 _ k.2)) (K.mul_mem hnK hb)
  calc ∑ᶠ y : X ⧸ K, f y = ∑ᶠ y ∈ Set.range φ, f y := by
        rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp]
    _ = ∑ᶠ x, f (φ x) := finsum_mem_range hφ
    _ = _ := finsum_congr hφf
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfLoc :
    TfAdm → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfLoc := by
  intro hAdm hAc hDec X M M' _ _ _ T L' Kw hF hAp t t' g
  set Φ : X → ℂ := fun y => T.tf (L'.loc t') (y⁻¹ * g) with hΦ
  have key : ∀ (a b : T.J), (a : M) = (b : M)⁻¹ → (((T.ψ a)⁻¹ : ℂˣ) : ℂ) = (T.ψ b : ℂ) := by
    intro a b hab
    have hab' : a = b⁻¹ := Subtype.ext (by simpa using hab)
    subst hab'
    simp
  have hTy : T.IsTy Φ := by
    intro k hk y
    have hp : T.L.pr (L'.loc t') = 1 := hAp.1 t'
    have h1 := ((hAdm X M T (L'.loc t') hp).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1
    simp only [hΦ, smul_eq_mul, mul_inv_rev, mul_assoc]
    rw [h1]
    congr 1
    exact key _ _ (by simp)
  have hsum := hAc X M M' T L' Kw hF hAp t 1 (by simp [TyLev.Cen]) ℂ Φ hTy 1
  have hL : conv T.K₀ (T.tf (L'.loc t)) (T.tf (L'.loc t')) g = hAct T.K₀ (T.tf (L'.loc t * 1)) Φ 1 := by
    simp only [conv, hAct, mul_one, one_mul, smul_eq_mul, hΦ]
  have hpt : ∀ m : M', Φ (L'.loc m) = T.tf 1 (g * (L'.loc (L'.pr g))⁻¹) * dosetInd ℂ Kw t' (m⁻¹ * L'.pr g) := by
    intro m
    have e1 : T.L.pr ((L'.loc m)⁻¹ * g) = T.L.pr g := by simp [hAp.1 m]
    have e2 : T.L.pr ((L'.loc (L'.pr g))⁻¹ * g) = T.L.pr g := by simp [hAp.1]
    have hu : g * (L'.loc (L'.pr g))⁻¹ = (L'.loc (L'.pr g))⁻¹ * g := by
      have h0 : L'.pr ((L'.loc (L'.pr g))⁻¹ * g) = 1 := by simp [L'.pr_loc]
      have hc := L'.comm (L'.pr g) _ h0
      calc g * (L'.loc (L'.pr g))⁻¹
          = (L'.loc (L'.pr g) * ((L'.loc (L'.pr g))⁻¹ * g)) * (L'.loc (L'.pr g))⁻¹ := by simp
        _ = (((L'.loc (L'.pr g))⁻¹ * g) * L'.loc (L'.pr g)) * (L'.loc (L'.pr g))⁻¹ := by rw [hc]
        _ = (L'.loc (L'.pr g))⁻¹ * g := by simp
    have hmem : (L'.loc m)⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t') (T.K : Set X) T.K ↔
        m⁻¹ * L'.pr g ∈ DoubleCoset.doubleCoset t' (Kw : Set M') Kw ∧
          (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset 1 (T.K : Set X) T.K := by
      have h3 : L'.pr ((L'.loc m)⁻¹ * g) = m⁻¹ * L'.pr g := by simp [L'.pr_loc]
      have h4 : (L'.loc (m⁻¹ * L'.pr g))⁻¹ * ((L'.loc m)⁻¹ * g) = (L'.loc (L'.pr g))⁻¹ * g := by
        simp [mul_assoc]
      have hd := hDec X M' L' T.K Kw hF t' 1 (map_one _) ((L'.loc m)⁻¹ * g)
      rw [mul_one, h3, h4] at hd
      exact hd
    simp only [hΦ, TyLev.tf]
    rw [hu, e1, e2]
    simp only [dosetInd, Set.indicator_apply, hmem, Pi.one_apply]
    by_cases ha : m⁻¹ * L'.pr g ∈ DoubleCoset.doubleCoset t' (Kw : Set M') Kw <;>
      by_cases hb : (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset 1 (T.K : Set X) T.K <;>
      simp [ha, hb]
  rw [hL, hsum]
  simp only [one_mul, smul_eq_mul, hpt, conv]
  rw [mul_finsum]
  congr 1
  ext x
  ring
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pExtP :
    ExtP := by
  intro Γ X X₂ V _ _ _ _ _ ι K K₂ ξ φ h1 h2
  let F : X × X₂ → V := fun p =>
    if h : ∃ γ : Γ, (ι γ).2⁻¹ * p.2 ∈ K₂ then ξ h.choose (φ ((ι h.choose).1⁻¹ * p.1)) else 0
  have key : ∀ (γ : Γ) (g : X) (g₂ : X₂), (ι γ).2⁻¹ * g₂ ∈ K₂ →
      F (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g)) := by
    intro γ g g₂ hγ
    have h : ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂ := ⟨γ, hγ⟩
    dsimp only [F]
    rw [dite_eq_left h]
    have hδ := h.choose_spec
    generalize h.choose = δ at hδ ⊢
    have hε : (ι (δ⁻¹ * γ)).2 ∈ K₂ := by
      have e : (ι (δ⁻¹ * γ)).2 = ((ι δ).2⁻¹ * g₂) * ((ι γ).2⁻¹ * g₂)⁻¹ := by
        simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]
        group
      rw [e]
      exact K₂.mul_mem hδ (K₂.inv_mem hγ)
    have e2 : (ι (δ⁻¹ * γ)).1 * ((ι γ).1⁻¹ * g) = (ι δ).1⁻¹ * g := by
      simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv]
      group
    rw [← e2, h1 _ hε, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have zero : ∀ (g : X) (g₂ : X₂), (¬ ∃ γ : Γ, (ι γ).2⁻¹ * g₂ ∈ K₂) → F (g, g₂) = 0 := by
    intro g g₂ h
    dsimp only [F]
    rw [dite_eq_right h]
  have mem : F ∈ forms ι (K.prod K₂) ξ := by
    refine ⟨fun γ p => ?_, fun k hk p => ?_⟩
    · obtain ⟨g, g₂⟩ := p
      have e : ι γ * (g, g₂) = ((ι γ).1 * g, (ι γ).2 * g₂) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι (γ * δ)).2⁻¹ * ((ι γ).2 * g₂) ∈ K₂ := by
          simpa [map_mul, mul_assoc] using hδ
        rw [key δ g g₂ hδ, key (γ * δ) _ _ hs, ← Module.End.mul_apply, ← map_mul]
        congr 2
        simp [mul_assoc]
      · rw [zero g g₂ h, map_zero]
        apply zero
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨γ⁻¹ * δ, ?_⟩
        simpa [map_mul, mul_assoc] using hδ
    · obtain ⟨g, g₂⟩ := p
      obtain ⟨k1, k2⟩ := k
      rw [Subgroup.mem_prod] at hk
      have hk1 : k1 ∈ K := hk.1
      have hk2 : k2 ∈ K₂ := hk.2
      have e : (g, g₂) * (k1, k2) = (g * k1, g₂ * k2) := rfl
      rw [e]
      by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
      · obtain ⟨δ, hδ⟩ := h
        have hs : (ι δ).2⁻¹ * (g₂ * k2) ∈ K₂ := by
          rw [← mul_assoc]
          exact K₂.mul_mem hδ hk2
        rw [key δ g g₂ hδ, key δ (g * k1) (g₂ * k2) hs, ← mul_assoc, h2 k1 hk1]
      · rw [zero g g₂ h, zero]
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ, ?_⟩
        have := K₂.mul_mem hδ (K₂.inv_mem hk2)
        simpa [mul_assoc] using this
  refine ⟨⟨F, mem⟩, fun g => ?_, fun g₂ => ?_⟩
  · show F (g, 1) = φ g
    rw [key 1 g 1 (by simp)]
    simp
  · by_cases h : ∃ δ : Γ, (ι δ).2⁻¹ * g₂ ∈ K₂
    · obtain ⟨δ, hδ⟩ := h
      exact Or.inr ⟨δ, fun g => key δ g g₂ hδ⟩
    · exact Or.inl fun g => zero g g₂ h
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem loc_split {X M' : Type} [Group X] [Group M'] (L' : Loc X M') {K : Subgroup X} {Kw : Subgroup M'}
    (hF : L'.Fact K Kw) {k : X} (hk : k ∈ K) :
    ∃ a ∈ Kw, ∃ k₀ ∈ K, L'.pr k₀ = 1 ∧ k = L'.loc a * k₀ := by
  refine ⟨L'.pr k, hF.2 k hk, (L'.loc (L'.pr k))⁻¹ * k, K.mul_mem (K.inv_mem (hF.1 _ (hF.2 k hk))) hk, ?_, by group⟩
  simp [L'.pr_loc]

private theorem loc_key {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (a t b : M') {k₀ r k₁ : X}
    (h₀ : L'.pr k₀ = 1) (hr : L'.pr r = 1) (h₁ : L'.pr k₁ = 1) :
    L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b) = L'.loc (a * t * b) * (k₀ * r * k₁) := by
  have hprod : L'.pr (k₀ * r * k₁) = 1 := by simp [map_mul, h₀, hr, h₁]
  have e1 := L'.comm t k₀ h₀
  have e2 := L'.comm b (k₀ * r * k₁) hprod
  rw [map_mul, map_mul]
  calc L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b)
      = L'.loc a * (k₀ * L'.loc t) * r * k₁ * L'.loc b := by group
    _ = L'.loc a * (L'.loc t * k₀) * r * k₁ * L'.loc b := by rw [e1]
    _ = L'.loc a * L'.loc t * ((k₀ * r * k₁) * L'.loc b) := by group
    _ = L'.loc a * L'.loc t * L'.loc b * (k₀ * r * k₁) := by rw [← e2]; group

theorem UpperTheory.Gal.W2.Seed.pDosetIff :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K := by
  intro X M' _ _ L' K Kw hF t r hr g
  constructor
  · intro hg
    rw [DoubleCoset.mem_doubleCoset] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    obtain ⟨a, ha, k₀, hk₀, h₀, rfl⟩ := loc_split L' hF hx
    obtain ⟨b, hb, k₁, hk₁, h₁, rfl⟩ := loc_split L' hF hy
    have hc : L'.loc b * k₁ = k₁ * L'.loc b := L'.comm b k₁ h₁
    rw [hc, loc_key L' a t b h₀ hr h₁]
    have hpr : L'.pr (L'.loc (a * t * b) * (k₀ * r * k₁)) = a * t * b := by
      simp [map_mul, h₀, hr, h₁, L'.pr_loc]
    rw [hpr]
    refine ⟨?_, ?_⟩
    · rw [DoubleCoset.mem_doubleCoset]
      exact ⟨a, ha, b, hb, rfl⟩
    · rw [DoubleCoset.mem_doubleCoset, inv_mul_cancel_left]
      exact ⟨k₀, hk₀, k₁, hk₁, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [DoubleCoset.mem_doubleCoset] at h1 h2 ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    obtain ⟨k₀, hk₀, k₁, hk₁, hk⟩ := h2
    have hg : g = L'.loc (L'.pr g) * (k₀ * r * k₁) := by
      rw [← hk]
      group
    have hpg := congrArg L'.pr hg
    simp only [map_mul, L'.pr_loc, hr, mul_one] at hpg
    have hpk : L'.pr k₀ * L'.pr k₁ = 1 := by
      calc L'.pr k₀ * L'.pr k₁ = (L'.pr g)⁻¹ * (L'.pr g * (L'.pr k₀ * L'.pr k₁)) := by group
        _ = 1 := by rw [← hpg]; group
    have hcr := L'.comm (L'.pr k₀) r hr
    have hk0 : L'.pr (k₀ * (L'.loc (L'.pr k₀))⁻¹) = 1 := by
      simp [map_mul, map_inv, L'.pr_loc]
    have hk1 : L'.pr (L'.loc (L'.pr k₀) * k₁) = 1 := by
      rw [map_mul, L'.pr_loc, hpk]
    have hsplit : k₀ * r * k₁ =
        k₀ * (L'.loc (L'.pr k₀))⁻¹ * r * (L'.loc (L'.pr k₀) * k₁) := by
      calc k₀ * r * k₁ = k₀ * (L'.loc (L'.pr k₀))⁻¹ * (L'.loc (L'.pr k₀) * r) * k₁ := by group
        _ = _ := by rw [hcr]; group
    refine ⟨L'.loc a * (k₀ * (L'.loc (L'.pr k₀))⁻¹), ?_, L'.loc (L'.pr k₀) * k₁ * L'.loc b, ?_, ?_⟩
    · exact K.mul_mem (hF.1 a ha) (K.mul_mem hk₀ (K.inv_mem (hF.1 _ (hF.2 _ hk₀))))
    · exact K.mul_mem (K.mul_mem (hF.1 _ (hF.2 _ hk₀)) hk₁) (hF.1 b hb)
    · rw [loc_key L' a t b hk0 hr hk1, ← hab, ← hsplit]
      exact hg
end

section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem UpperTheory.Gal.W2.Seed.tf_mul_cen_apply {X M : Type} [Group X] [Group M] (T : TyLev X M)
    (h z : X) (hz : T.Cen z) (g : X) : T.tf (h * z) g = T.tf h (z⁻¹ * g) := by
  have hzc := hz.1
  have hpr : T.L.pr (z⁻¹ * g) = T.L.pr g := by
    rw [map_mul, map_inv, hz.2, inv_one, one_mul]
  have key : ∀ a b : X, a * (h * z) * b = z * (a * h * b) := by
    intro a b
    calc a * (h * z) * b = a * h * (z * b) := by group
      _ = a * h * (b * z) := by rw [hzc b]
      _ = (a * h * b) * z := by group
      _ = z * (a * h * b) := (hzc _).symm
  have hmem : g ∈ DoubleCoset.doubleCoset (h * z) (T.K : Set X) T.K ↔
      z⁻¹ * g ∈ DoubleCoset.doubleCoset h (T.K : Set X) T.K := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [key]; group⟩
    · rintro ⟨a, ha, b, hb, he⟩
      refine ⟨a, ha, b, hb, ?_⟩
      rw [key, ← he]
      group
  simp only [TyLev.tf, dosetInd, hpr, Set.indicator_apply, hmem, Pi.one_apply]

theorem UpperTheory.Gal.W2.Seed.pTfMulCen :
    TfAdm → TfCen → TfIdem → TfMulCen := by
  intro hAdm hCen hIdem X M _ _ T h z hh hz
  have hzc : ∀ y : X, z⁻¹ * y = y * z⁻¹ := fun y => (Commute.inv_left (hz.1 y : Commute z y)).eq
  refine ⟨?_, ?_⟩
  · funext g
    have hty : T.IsTy (V := ℂ) (fun y : X => T.tf h (y⁻¹ * g)) := by
      intro k hk y
      have e := ((hAdm X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1
      simp only [mul_inv_rev, mul_assoc]
      rw [e]
      simp only [map_inv, smul_eq_mul]
      congr 1
      rw [← map_inv]
      exact congrArg (fun u => ((T.ψ u : ℂˣ) : ℂ)) (Subtype.ext (inv_inv _))
    have e := hCen X M T z hz ℂ (fun y => T.tf h (y⁻¹ * g)) hty 1
    simp only [hAct, one_mul, smul_eq_mul] at e
    simp only [conv]
    rw [e, tf_mul_cen_apply T h z hz g]
  · funext g
    have e1 : conv T.K₀ (T.tf h) (T.tf z) g = conv T.K₀ (T.tf h) (T.tf 1) (z⁻¹ * g) := by
      simp only [conv]
      refine finsum_congr fun x => ?_
      congr 1
      have e := tf_mul_cen_apply T 1 z hz (x.out⁻¹ * g)
      rw [one_mul] at e
      rw [e, ← mul_assoc, ← mul_assoc, hzc]
    rw [e1, (hIdem X M T h hh).2.1, tf_mul_cen_apply T h z hz g]
end
