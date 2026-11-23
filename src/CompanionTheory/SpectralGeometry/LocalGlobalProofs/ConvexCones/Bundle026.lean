module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle009
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle763
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle734
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle735
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle022
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

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision

theorem baryStep : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab φ : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], _root_.GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → IsTwG w0 φ → IsBaryStage bar q ψ lab φ (i + 1) → ∃ φ' : InvFun O, IsTwG w0 φ' ∧ IsBaryStage bar q ψ lab φ' i := by
  intro O _ _ _ _ bar w0 hO q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := GlobalTheory.T.exists_marking_centre_function O bar w0 hO q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_star_subdivision O bar w0 hO q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell bar φ (Fin.append v u) → IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact GlobalTheory.T.starSubdivision_barycentre_cell_next_stage O bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => GlobalTheory.T.cell_face_restriction O bar hO q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        GlobalTheory.T.carrierDim_le_of_add_cell_generators O bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells

theorem exists_star_drop_multCells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], _root_.GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → MultCellsAmong bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧
      Subordinate bar q φ' φ ∧ maxMult bar q φ' ≤ M ∧ MultCellsAmong bar q φ' M n := by
  intro O _ _ _ _ bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M n hM hmax hcells
  obtain ⟨R, hR⟩ := hcells
  obtain ⟨w, hwtw, hwc, hcov, hdrop⟩ := GlobalTheory.T.exists_twisted_centre_set O bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M hM hmax (R 0)
  obtain ⟨ψ', hψ', hψ'tw, hsub, hstar⟩ := GlobalTheory.T.exists_star_subdivision O bar w0 hb q φ w hDom hφ hφtw hwtw hwc
  obtain ⟨lab', hlab'tw, hsl'⟩ := GlobalTheory.T.exists_twisted_simplicial_star_label O bar w0 hb q φ lab w ψ' hDom hφ hlabtw hsl hwtw hwc hψ' hsub hstar
  obtain ⟨hmax', hc'⟩ := GlobalTheory.T.star_subdivision_mult_le O bar hb q φ lab w ψ' hDom hφ hsl hwc hdrop hψ' hsub hstar M hmax
  refine ⟨ψ', lab', hψ', hψ'tw, hlab'tw, hsl', hsub, hmax', fun k => R k.succ, ?_⟩
  intro X _ _ _ _ hX m δ hδ
  obtain ⟨hδφ, hnoc⟩ := hc' X hX m δ hδ
  obtain ⟨k, hk⟩ := hR X hX m δ hδφ
  induction k using Fin.cases with
  | zero =>
    obtain ⟨β, hβ, hp, hw1, hin⟩ := hcov X hX m δ hδφ hk
    exact absurd hw1 (hnoc β hβ hp hin)
  | succ k => exact ⟨k, hk⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells
end
