module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

theorem _root_.GlobalTheory.T.holomorphic_section_moderate_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens), IsAffineOpen V → V ≤ B.U i → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)) (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.continuous_section_polynomial_growth_of_isProper | exact GlobalTheory.CompanionTheory.Gaga.continuous_section_polynomial_growth_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Gaga.continuous_section_polynomial_growth_of_isProper <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ChartGlue

variable {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {D : ℕ}

theorem valAt'_eq_ev (U : X.Opens) (f : Γ(X, U)) (y : CxPts s (RingHom.id ℂ)) :
    valAt' y.1 U f = ev s (RingHom.id ℂ) U f y := rfl

theorem comp_eq_id (y : CxPts s (RingHom.id ℂ)) : y.1 ≫ s = 𝟙 _ := by
  rw [y.2]
  simp [spMap]

theorem isHolTo_chart (c : AlgChart s (RingHom.id ℂ) D) (W : X.Opens)
    (ψ : (Fin D → ℂ) ≃L[ℂ] V D) :
    IsHolTo (ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W))
      (fun b => (c.e.symm (ψ b)).1) := by
  intro U f
  have hset : ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' (ptsIn s (RingHom.id ℂ) W ∩ ptsIn s (RingHom.id ℂ) U)) =
      {b | b ∈ ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W) ∧
        ⊤ ≤ (Opens.map (c.e.symm (ψ b)).1.base).obj U} := by
    ext b
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  refine ⟨?_, ?_⟩
  · have ho := (c.e.isOpen_inter_preimage_symm
      ((isOpen_ptsIn (p := s) (σ := RingHom.id ℂ) W).inter (isOpen_ptsIn U))).preimage ψ.continuous
    rw [hset] at ho
    exact ho
  · have hd := (c.holo U f).comp
      (ψ.differentiableOn : DifferentiableOn ℂ ψ {b | b ∈ ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W) ∧
        ⊤ ≤ (Opens.map (c.e.symm (ψ b)).1.base).obj U})
      (fun b hb => ⟨hb.1.1, hb.2⟩)
    refine hd.congr ?_
    intro b _
    exact valAt'_eq_ev U f _

theorem exists_mem_holSec : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (R : AnRead s (RingHom.id ℂ) D), ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ ∈ R.holSec L, ∀ (i : L.ι), ∀ y ∈ ptsIn s (RingHom.id ℂ) (L.U i), σ i y = h i y.1 := by
  intro X s D _ R L _ h hhol hcoc
  classical
  obtain ⟨ψ⟩ : Nonempty ((Fin D → ℂ) ≃L[ℂ] V D) := ⟨(EuclideanSpace.equiv (Fin D) ℂ).symm⟩
  refine ⟨fun i y => if y ∈ ptsIn s (RingHom.id ℂ) (L.U i) then h i y.1 else 0, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j y hi hj
      have hij : y ∈ ptsIn s (RingHom.id ℂ) (L.U i ⊓ L.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      simp only [if_pos hi, if_pos hj]
      rw [hcoc i j y.1 (comp_eq_id y) hij, valAt'_eq_ev]
      rfl
    · intro i y hy
      simp only [if_neg hy]
    · intro i k
      have hB : IsOpen (ψ ⁻¹' ((R.chart k).e.target ∩
          (R.chart k).e.symm ⁻¹' ptsIn s (RingHom.id ℂ) (L.U i))) :=
        ((R.chart k).e.isOpen_inter_preimage_symm (isOpen_ptsIn _)).preimage ψ.continuous
      have hd := hhol i D _ (fun b => ((R.chart k).e.symm (ψ b)).1) hB
        (isHolTo_chart (R.chart k) (L.U i) ψ) (fun b hb => ⟨comp_eq_id _, hb.2⟩)
      have hd2 := hd.comp ψ.symm.differentiableOn (fun v hv => by
        show ψ (ψ.symm v) ∈ (R.chart k).e.target ∩
          (R.chart k).e.symm ⁻¹' ptsIn s (RingHom.id ℂ) (L.U i)
        rw [ψ.apply_symm_apply]
        exact hv)
      refine hd2.congr ?_
      intro v hv
      have hv2 : (R.chart k).e.symm v ∈ ptsIn s (RingHom.id ℂ) (L.U i) := hv.2
      simp [Function.comp, hv2]
  · intro i y hy
    simp only [if_pos hy]

end GlobalTheory.CompanionTheory.Gaga
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem stage (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ)
    (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (k : ℕ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | -(k : ℝ) < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = ∑' m, (w m : ℂ) * coneTerm a b s m) ∧
      ∀ p : ℕ, p < k → (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
        ∃ q : ℚ, G (-(p : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨Q, x, cs, u, hu, hcs, hsum⟩ := GlobalTheory.T.weight_sum_as_finite_differences r l (Fintype.card ι * k + 2) w hl hw
  refine ⟨fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m, ?_, ?_, ?_⟩
  · have h : ∀ q ∈ (Finset.univ : Finset Q), DifferentiableOn ℂ
        (fun s => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) {s : ℂ | -(k : ℝ) < s.re} :=
      fun q _ => GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb k (Fintype.card ι * k + 2) (cs q) (u q) le_rfl (hu q) (hcs q)
    have h2 := DifferentiableOn.sum h
    have h3 : (fun s : ℂ => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) =
        ∑ q, fun s : ℂ => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m := by
      funext s
      simp [Finset.sum_apply]
    rw [h3]
    exact h2
  · intro s hs
    exact (hsum (coneTerm a b s) (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)).symm
  · intro p hp hrat
    have hN : Fintype.card ι * p < Fintype.card ι * k + 2 := by
      have := Nat.mul_le_mul_left (Fintype.card ι) hp.le
      omega
    choose q hq using fun t => GlobalTheory.T.shintani_values_negative_integers_rational ι r a b (u t) (cs t) (Fintype.card ι * k + 2) p hN (hcs t) hrat
    refine ⟨∑ t, q t, ?_⟩
    simp only [Rat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => hq t

theorem abelContinuation : AbelContinuation := by
  intro ι _ r l a b w hr hl ha hb hw
  choose G hG hGeq hGrat using fun k : ℕ => stage ι r l a b w hr hl ha hb hw k
  obtain ⟨T, hT, hTG⟩ := GlobalTheory.T.analytic_continuation_from_strips (fun s => ∑' m, (w m : ℂ) * coneTerm a b s m) G hG hGeq
  refine ⟨T, hT, ?_, ?_⟩
  · intro s hs
    have hs0 : -((0 : ℕ) : ℝ) < s.re := by
      rw [Nat.cast_zero, neg_zero]
      linarith
    rw [hTG 0 s hs0, hGeq 0 s hs]
    have hper : ∀ (i : Fin r) (m : Fin r → ℕ), w (m + Pi.single i l) = w m := by
      obtain ⟨h1, -⟩ := hw
      exact fun i m => h1 m i
    obtain ⟨C, hC⟩ := GlobalTheory.T.periodic_weight_bounded r l w hl hper
    have hcone := GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs
    refine Summable.hasSum (Summable.of_norm ?_)
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hcone.norm.mul_left C)
    have hwm : ‖(w m : ℂ)‖ ≤ C := by simpa using hC m
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hwm (norm_nonneg _)
  · intro p hrat
    have hp : -((p + 1 : ℕ) : ℝ) < (-(p : ℂ)).re := by norm_num
    rw [hTG (p + 1) _ hp]
    exact hGrat (p + 1) p (Nat.lt_succ_self p) hrat

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem _root_.GlobalTheory.T.exists_shintani_cone_domain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain <;> assumption)
end
