module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pointwise_sum_bound {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (F : (X.Ψ → Fin 2 → Fin 2 → ℂ) → Frame X.Ψ r → ℂ) (T : (X.Ψ → Fin 2 → Fin 2 → ℂ) → ℝ)
    (w S1 : ℝ) (hS10 : 0 ≤ S1) (z0 : Frame X.Ψ r)
    (hexp : ∀ z ∈ X.dom, Summable (fun χ => ‖F χ z‖) → HasSum (fun χ => F χ z) (Q z))
    (hpt : ∀ χ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (F χ) z ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1)
    (hsum : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => Real.exp (-Real.pi * T j.1))) :
    ∀ z ∈ X.dom, X.SameFlag z0 z → X.pnorm la Q z ≤
      2 ^ (w / 2) * (∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1)) * S1 := by
  intro z hz hfl
  have hN := X.pointNorm_nonneg la (fun _ => (1 : ℂ)) z
  have hC : 0 ≤ (2 : ℝ) ^ (w / 2) := by positivity
  have htn : 0 ≤ ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  rw [X.pointNorm_eq_norm_mul la Q z]
  rcases hN.eq_or_lt with hN0 | hNpos
  · rw [← hN0, mul_zero]
    exact mul_nonneg (mul_nonneg hC htn) hS10
  have hpt' : ∀ χ, ‖F χ z‖ * X.pnorm la (fun _ => (1 : ℂ)) z ≤
      2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1 := fun χ => by
    rw [← X.pointNorm_eq_norm_mul la (F χ) z]; exact hpt χ z hz hfl
  have hb : ∀ χ, ‖F χ z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T χ) := by
    intro χ
    rw [div_mul_eq_mul_div, le_div_iff₀ hNpos]
    linarith [hpt' χ]
  have hzero : ∀ χ, χ ∉ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} → F χ z = 0 := fun χ hχ => by
    by_contra h; exact hχ ⟨z, hz, h⟩
  have hsupp : Function.support (fun χ => ‖F χ z‖) ⊆ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} := by
    intro χ hχ
    by_contra h
    exact hχ (by simp only [hzero χ h, norm_zero])
  have hsumS : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => ‖F j.1 z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hb j.1) (hsum.mul_left _)
  have hsumAll : Summable (fun χ => ‖F χ z‖) := by
    refine (Function.Injective.summable_iff Subtype.val_injective fun χ hχ => ?_).1 hsumS
    rw [norm_eq_zero]
    exact hzero χ fun h => hχ ⟨⟨χ, h⟩, rfl⟩
  have hQ := hexp z hz hsumAll
  have hnorm : ‖Q z‖ ≤ ∑' χ, ‖F χ z‖ := by
    rw [← hQ.tsum_eq]; exact norm_tsum_le_tsum_norm hsumAll
  rw [← tsum_subtype_eq_of_support_subset hsupp] at hnorm
  have hsum2 : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} =>
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T j.1)) :=
    hsum.mul_left _
  have hle : ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, ‖F j.1 z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z *
        ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) := by
    rw [← tsum_mul_left]
    exact hsumS.tsum_le_tsum (fun j => hb j.1) hsum2
  have hm := mul_le_mul_of_nonneg_right (hnorm.trans hle) hN
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hNpos.ne', mul_one] at hm
  linarith

private theorem herm_swap_eq_cc_of_conj_symm {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin r → E) : herm G y x = cc (herm G x y) := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG

  simp only [herm, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG' a b]
  ring

private theorem herm_add_smul_self_expand {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (c : E) :
    herm G (x + c • y) (x + c • y) =
      herm G x x + c * herm G y x + cc c * herm G x y + c * cc c * herm G y y := by
  simp only [herm, cc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem shortVectorBound_of_coefficient_bounds (h3 : FourierCoefficientProperties (E := E)) (h3q : CuspCoefficientBound (E := E)) (h6p : FlowCoefficientDecay (E := E))
    (h7 : CoefficientIndexLowerBound (E := E)) (h8 : CoefficientHeightBound (E := E)) (h9 : CountingExponentialSum)
    (h10 : IsotropicOutsideLine (E := E)) : ShortVectorBound (E := E) := by
  intro r X la P ξ ν c1 w z0 hH x hxL hxξ hxE
  have hH0 := hH
  obtain ⟨-, hSS, hiso, hc1, -, -, hw1, -, hχ, hz0, hsup⟩ := hH
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨hep_pos, hep_le, hep_spec⟩ := epsilonZero_spec X c1 w hc1 hw1
  obtain ⟨hxx, α, hx'L, hx'ξ, hucomp, -, hmajNC⟩ :=
    h10 r X ξ hiso z0 hz0 x hxL hxξ hxE fun τ => lt_of_lt_of_le (hcon τ) hep_le
  set x' := x + ((X.NA : E) * (α : E)) • ξ with hx'
  have hx'E : ∀ e : E, x' ≠ e • ξ := by
    intro e he
    exact hxE (e - (X.NA : E) * (α : E)) (by rw [sub_smul, ← he, hx']; abel)
  have hx'x' : herm X.Gm x' x' = 0 := by
    rw [hx', herm_add_smul_self_expand, herm_swap_eq_cc_of_conj_symm X.Gm X.Gm_herm x ξ, hxξ, hiso.2.1, hxx]
    simp [cc]
  obtain ⟨a, hset⟩ := short_vector_setting_exists X hH0 hx'L hx'ξ hx'x' hx'E
  obtain ⟨hpair, hmem⟩ := isotropic_pair_in_lattice X hiso hx'L hx'ξ hx'x' hx'E
  obtain ⟨ε, hε0, hεlt, hεmaj⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧
      ∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x') τ) ≤ ε := by
    let s : Finset ℝ := (Finset.univ.image fun τ => X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ∪
      {flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w / 2}
    have hs : s.Nonempty := ⟨_, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
    refine ⟨s.max' hs, lt_of_lt_of_le (half_pos hep_pos)
      (s.le_max' _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))), ?_, fun τ => ?_⟩
    · have hm := s.max'_mem hs
      rcases Finset.mem_union.1 hm with h | h
      · obtain ⟨τ, -, hτ⟩ := Finset.mem_image.1 h
        rw [← hτ]; exact hcon τ
      · rw [Finset.mem_singleton.1 h]; linarith
    · rw [hucomp]
      exact s.le_max' _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ τ)))
  obtain ⟨hQd, hQb, hQz⟩ := h3q r X ![ξ, (X.NC : E) • x'] hpair hmem la P hSS hχ ν
  have hL3 := h3 r X.toData ![ξ, (X.NC : E) • x'] X.g hpair X.g_pos la (X.fj la ξ ν P) hQd hQb hQz
  have hK : 1 ≤ 1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
      (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by
    have h1 : 0 < 2 * c1 + 1 := by linarith
    have h2 : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
      (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := mul_nonneg (by positivity) h1.le
    linarith
  have hN : (1 : ℝ) ≤ ((4 * fdeg E : ℕ) : ℝ) := by
    have := one_le_field_half_degree (E := E)
    push_cast
    linarith
  have hlow : ∀ j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
      X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0},
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) *
        ((4 * fdeg E : ℕ) : ℝ)) + ((4 * fdeg E : ℕ) : ℝ) + 2 <
      2 * ∑ τ, (X.chiAt j.1 a τ).re := fun j =>
    lt_of_lt_of_le (hep_spec ε hε0 hεlt) (h7 r X la P ξ ν c1 w z0 x' a ε hset hε0 hεmaj j.1 j.2)
  have hcount : ∀ t0 : ℝ, 1 ≤ t0 →
      {j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0}.Finite ∧
      ({j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0}.ncard : ℝ) ≤
        ((1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
          (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * t0) ^ ((4 * fdeg E : ℕ) : ℝ) := by
    intro t0 ht0
    obtain ⟨hfin, hcard⟩ := h8 r X la P ξ ν c1 w z0 x' a hset hmajNC t0 ht0
    have hpre : {j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0} =
        Subtype.val ⁻¹' {χ | (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0) ∧
          2 * ∑ τ, (X.chiAt χ a τ).re ≤ t0} := by
      ext j
      exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
    rw [hpre]
    refine ⟨hfin.preimage Subtype.val_injective.injOn, ?_⟩
    rw [Set.ncard_preimage_of_injective_subset_range
      (f := (Subtype.val : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} → _))
      (s := {χ : X.Ψ → Fin 2 → Fin 2 → ℂ | (∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0) ∧
        2 * ∑ τ, (X.chiAt χ a τ).re ≤ t0}) Subtype.val_injective
      (fun χ hχ => ⟨⟨χ, hχ.1⟩, rfl⟩), Real.rpow_natCast]
    exact hcard
  have hw0 : 0 ≤ w := le_trans zero_le_one hw1
  obtain ⟨hsumT, hlt⟩ := h9 _ _ w hK hN hw0 ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
      X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0}
    (fun j => 2 * ∑ τ, (X.chiAt j.1 a τ).re) hlow hcount
  have hS10 : 0 ≤ sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} :=
    Real.sSup_nonneg fun t ⟨y, _, ht⟩ => ht ▸ X.hatNorm_nonneg la _ y
  have hbound := pointwise_sum_bound X.toData la (X.fj la ξ ν P)
    (fun χ => X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P))
    (fun χ => 2 * ∑ τ, (X.chiAt χ a τ).re) w _ hS10 z0 (hL3 0).2.2
    (fun χ z hz hfl => h6p r X la P ξ ν c1 w z0 x' a hset χ z hz hfl) hsumT
  have hhat : X.hatN la (X.fj la ξ ν P) z0 ≤ 2 ^ (w / 2) *
      (∑' j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0},
        Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt j.1 a τ).re))) *
      sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} := by
    unfold Data.hatN
    refine csSup_le ⟨_, z0, hz0.1, fun τ => rfl, rfl⟩ ?_
    rintro t ⟨z, hz, hfl, rfl⟩
    exact hbound z hz hfl
  have hm := mul_le_mul_of_nonneg_right hlt.le hS10
  linarith only [hsup, hhat, hm]

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def NonvanishingNearHalfMax : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 x0 : Frame X.Ψ r) (w : ℝ),
    X.IsSec la P → z0 ∈ X.dom → X.IsOrtho x0 → (∃ b ∈ Bor X.Ψ r, x0 = rmul z0 b) →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r →
    ∀ Z : X.Coord, X.zN Z ≤ frameRadius w r / 5 → P (X.xZ x0 Z) ≠ 0

def FrameAtHalfMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (z0 : Frame X.Ψ r) (laStar w : ℝ),
    X.IsSec la P → z0 ∈ X.dom →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    (∑ τ, X.spread la τ) ≤ w → 1 ≤ w → 0 < r → 0 < laStar → laStar ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (x : Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.dom ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar (3 * frameRadius w r / 5)) x lam ∧
      P x ≠ 0 ∧ ∀ τ v, X.maj x τ v ≤ 2 * X.maj z0 τ v

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace QuadraticLatticeForms

open Matrix NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  unfold Data.c
  exact mul_pos two_pos (norm_pos_iff.mpr h)

noncomputable def ip (u w : X.Ψ → Fin r → ℂ) : ℝ := ∑ τ, X.c τ * (∑ a, u τ a * conj (w τ a)).re

theorem ip_add_left (u u' w : X.Ψ → Fin r → ℂ) : ip X (u + u') w = ip X u w + ip X u' w := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re, mul_add]

theorem ip_add_right (u w w' : X.Ψ → Fin r → ℂ) : ip X u (w + w') = ip X u w + ip X u w' := by
  simp only [ip, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem ip_smul_left (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X (k • u) w = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, (k • u) τ a * conj (w τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

theorem ip_smul_right (k : ℝ) (u w : X.Ψ → Fin r → ℂ) : ip X u (k • w) = k * ip X u w := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h : (∑ a, u τ a * conj ((k • w) τ a)) = (k : ℂ) * ∑ a, u τ a * conj (w τ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  rw [h, Complex.re_ofReal_mul]
  ring

noncomputable def ipB : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (ip X) (ip_add_left X) (ip_smul_left X) (ip_add_right X) (ip_smul_right X)

theorem ipB_apply (u w : X.Ψ → Fin r → ℂ) : ipB X u w = ip X u w := rfl

theorem ip_comm (u w : X.Ψ → Fin r → ℂ) : ip X u w = ip X w u := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem ip_self (u : X.Ψ → Fin r → ℂ) : ip X u u = ∑ τ, X.c τ * ∑ a, ‖u τ a‖ ^ 2 := by
  unfold ip
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem ip_pos {u : X.Ψ → Fin r → ℂ} (hu : u ≠ 0) : 0 < ip X u u := by
  rw [ip_self]
  obtain ⟨τ, hτ⟩ : ∃ τ, u τ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ : ∃ a, u τ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hτ (funext h)
  apply Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X i).le
    (Finset.sum_nonneg fun b _ => sq_nonneg _))
  refine ⟨τ, Finset.mem_univ _, mul_pos (c_pos X τ) ?_⟩
  apply Finset.sum_pos' (fun b _ => sq_nonneg _)
  exact ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩

noncomputable def Ly (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) :
    (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ := (y τ)⁻¹ *ᵥ u τ
  map_add' u w := by funext τ; simp [Matrix.mulVec_add]
  map_smul' k u := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, Complex.real_smul]

noncomputable def Sg : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ a := ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a
  map_add' u w := by funext τ a; simp [mul_add]
  map_smul' k u := by funext τ a; simp [Complex.real_smul]; ring

noncomputable def Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) : ℝ :=
  ∑ τ, X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 v) a‖ ^ 2

theorem ip_Ly_self (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ip X (Ly X y (X.embV v)) (Ly X y (X.embV v)) = Qy X y v := by
  rw [ip_self]
  rfl

theorem Qy_nonneg (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) : 0 ≤ Qy X y v := by
  unfold Qy
  exact Finset.sum_nonneg fun τ _ => mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => sq_nonneg _)

theorem embV_sum {ι : Type} (s : Finset ι) (w : ι → Fin r → E) :
    X.embV (∑ i ∈ s, w i) = ∑ i ∈ s, X.embV (w i) := by
  funext τ a

  simp only [Data.embV, Data.emb, Finset.sum_apply, map_sum]

theorem embV_zsmul (n : ℤ) (w : Fin r → E) : X.embV (n • w) = (n : ℝ) • X.embV w := by
  funext τ a
  simp only [Data.embV, Data.emb, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast,
    Complex.real_smul, Complex.ofReal_intCast]

theorem Ly_injective (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) :
    Function.Injective (Ly X y) := by
  intro u u' h
  funext τ
  have h1 : (y τ)⁻¹ *ᵥ u τ = (y τ)⁻¹ *ᵥ u' τ := congrFun h τ
  have hu : IsUnit (y τ).det := isUnit_iff_ne_zero.mpr (hy τ)
  have h2 := congrArg (fun v => y τ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2
  exact h2

theorem Ly_surjective (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) :
    Function.Surjective (Ly X y) := by
  intro v
  refine ⟨fun τ => y τ *ᵥ v τ, ?_⟩
  funext τ
  change (y τ)⁻¹ *ᵥ (y τ *ᵥ v τ) = v τ
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hy τ)), Matrix.one_mulVec]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def Am (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ip X (Ly X y (X.embV (g i : Fin r → E))) (Ly X y (X.embV (g j : Fin r → E)))

noncomputable def Bm (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ τ, X.c τ * (τ.1 (herm X.Gm (g i : Fin r → E) (g j : Fin r → E))).re

theorem quad_eq (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℝ) :
    x ⬝ᵥ (Am X y g *ᵥ x) = ip X (Ly X y (∑ i, x i • X.embV (g i : Fin r → E)))
      (Ly X y (∑ i, x i • X.embV (g i : Fin r → E))) := by
  have hL : Ly X y (∑ i, x i • X.embV (g i : Fin r → E)) =
      ∑ i, x i • Ly X y (X.embV (g i : Fin r → E)) := by

    simp only [map_sum, map_smul]
  rw [hL, ← ipB_apply]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ipB_apply]
  simp only [dotProduct, Matrix.mulVec, Am, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ip_comm X (Ly X y (X.embV (g j : Fin r → E)))]
  ring

theorem quad_int (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℤ) :
    (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) =
      Qy X y (∑ i, x i • (g i : Fin r → E)) := by
  rw [quad_eq, ← ip_Ly_self, embV_sum]
  simp only [embV_zsmul]

theorem Am_posDef (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, (y τ).det ≠ 0)
    (g : Basis ι ℤ X.Λ) : (Am X y g).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp only [conjTranspose_apply, star_trivial, Am, of_apply]
    exact ip_comm X _ _
  · rw [star_trivial, quad_eq]
    refine ip_pos X fun h0 => hx ?_
    have h1 : ∑ i, x i • X.embV (g i : Fin r → E) = 0 := Ly_injective X y hy (by rw [h0, map_zero])
    exact funext (Fintype.linearIndependent_iff.mp (RealPlaceEmbeddings.linIndR X g) x h1)

end QuadraticLatticeForms

end ReciprocityTheory.ChartRestriction.G.FD
end
