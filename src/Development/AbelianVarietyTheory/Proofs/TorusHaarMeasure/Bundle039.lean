module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle029
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle007
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle014
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), X.p0 = 0 → Nonempty X.Ψ → (∀ x, Xa.ps0 x = 0) → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → Margins X Xa := by
  intro E _ _ _ r X Xa h0 _ hps _ hgap
  have hA : ∀ (m : ℝ) x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun m x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a _ => hgap τ i j a) (fun τ i j _ b => hgap τ i j b)
      (fun τ i j a _ => absurd a (by omega)) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le
  have hP : ∀ x0 z ξ, leviO X x0 Xa.ps0 z ξ = 0 := fun x0 z ξ => by
    simp only [leviO, leviM, hps]
    rw [RgC.leviV_const, Complex.zero_re]
  refine ⟨⟨_, _, lt_add_one _, lt_add_one _, fun t _ x0 ho z hz ξ => ?_⟩,
    ⟨_, _, lt_add_one _, lt_add_one _, fun x0 ho z hz ξ => ?_⟩, hB, ⟨0, fun x _ => (hps x).le⟩,
    fun k P hP => ⟨hP, fun ξ hξ =>
      (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite X (Or.inl h0) ξ hξ).elim⟩⟩
  · rw [hP, mul_zero, add_zero]
    exact hA _ x0 ho z hz ξ
  · exact (hA _ x0 ho z hz ξ).trans
      (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (hB x0 ho z hz ξ)))

end GlobalTheory.Shares
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem exists_submodule_finrank_eq_of_le {K : Type} [Field K] {r i : ℕ} (h : i ≤ r) :
    ∃ W : Submodule K (Fin r → K), Module.finrank K W = i := by

  have hli : LinearIndependent K ((Pi.basisFun K (Fin r)) ∘ Fin.castLE h) :=
    (Pi.basisFun K (Fin r)).linearIndependent.comp _ (Fin.castLE_injective h)
  exact ⟨_, (finrank_span_eq_card hli).trans (Fintype.card_fin i)⟩

theorem exists_isLUB_height_rpow_lowerSemicontinuousOn : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ δ : ℝ, 0 < δ → ∃ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) ∧ ∀ i ≤ r, LowerSemicontinuousOn (α i) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd δ hδ
  set s := {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0} with hs

  have hbdd : ∀ x ∈ s, ∀ i : ℕ, BddAbove ((fun W => d x W ^ (-δ)) ''
      {W : Submodule E (Fin r → E) | Module.finrank E W = i}) := by
    intro x hx i
    obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x hx
    refine ⟨m ^ (-δ), ?_⟩
    rintro _ ⟨W, -, rfl⟩
    exact Real.rpow_le_rpow_of_nonpos hm (hmW W) (by linarith)
  refine ⟨fun i x => sSup ((fun W => d x W ^ (-δ)) ''
      {W : Submodule E (Fin r → E) | Module.finrank E W = i}), ?_, ?_⟩
  · intro i hi x hx
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    exact isLUB_csSup (Set.Nonempty.image _ (⟨W, hW⟩ : Set.Nonempty {W : Submodule E (Fin r → E) | Module.finrank E W = i})) (hbdd x hx i)
  ·
    intro i hi x hx y hy
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image _ (⟨W, hW⟩ : Set.Nonempty {W : Submodule E (Fin r → E) | Module.finrank E W = i})) hy
    have hpos : ∀ x' ∈ s, 0 < d x' V := fun x' hx' => by
      obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x' hx'
      exact hm.trans_le (hmW V)
    have hcont : ContinuousOn (fun x' => d x' V ^ (-δ)) s :=
      (GlobalTheory.T.latticeHeight_continuousOn_frames r X d hd V).rpow_const fun x' hx' => Or.inl (hpos x' hx').ne'
    have hev : ∀ᶠ x' in 𝓝[s] x, y < d x' V ^ (-δ) := (hcont x hx).eventually (lt_mem_nhds hyV)
    filter_upwards [hev, self_mem_nhdsWithin] with x' h1 h2
    exact h1.trans_le (le_csSup (hbdd x' h2 i) ⟨V, hV, rfl⟩)

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.heightSup_invariant_under_hermitianLattice_aut : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  first | exact @GlobalTheory.height_sup_lact_invariant | exact GlobalTheory.height_sup_lact_invariant | (intros; apply GlobalTheory.height_sup_lact_invariant <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem rpow_neg_le_of_le_mul {p q ω δ : ℝ} (hp : 0 < p) (hq : 0 < q) (hω : 0 < ω) (hδ : 0 ≤ δ)
    (h : q ≤ ω * p) : p ^ (-δ) ≤ ω ^ δ * q ^ (-δ) := by
  have h1 : (ω * p) ^ (-δ) ≤ q ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hq h (by linarith)
  rw [Real.mul_rpow hω.le hp.le] at h1
  have h2 : ω ^ δ * ω ^ (-δ) = 1 := by
    rw [← Real.rpow_add hω]; simp
  have h3 : 0 < ω ^ δ := Real.rpow_pos_of_pos hω δ
  calc p ^ (-δ) = ω ^ δ * (ω ^ (-δ) * p ^ (-δ)) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ ω ^ δ * q ^ (-δ) := mul_le_mul_of_nonneg_left h1 h3.le

theorem height_rpow_neg_distortion_contraction : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c Ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ Ω ∧ ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ W, (∀ a ∈ S, d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ) ≤ Ω * d x W ^ (-δ) ∧ d x W ^ (-δ) ≤ Ω * d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ)) ∧ (W ≠ ⊥ → W ≠ ⊤ → ∑ a ∈ S, d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ) ≤ S.card * (c * d x W ^ (-δ)))) := by
  intro r X d hd τ0 S hS hirr
  obtain ⟨δ, c, ω, hδ, hc0, hc1, hω, H⟩ := GlobalTheory.T.gramDet_inequalities_closed_forms.2.2.1 r S hS hirr
  refine ⟨δ, c, ω ^ δ, hδ, hc0, hc1, Real.one_le_rpow hω hδ.le, ?_⟩
  intro x hx W
  obtain ⟨m, hm, hmd⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x hx
  have hD : 0 < d x W := lt_of_lt_of_le hm (hmd W)
  obtain ⟨M, hM, hstep⟩ := GlobalTheory.T.latticeHeight_update_frameComponent r X d hd x hx τ0 W
  obtain ⟨H1, H2⟩ := H _ M hM
  have hω0 : 0 < ω := by linarith
  have hpos : ∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re := by
    intro a ha
    have := lt_of_lt_of_le hM (H1 a ha).2
    exact (mul_pos_iff_of_pos_left hω0).mp this
  refine ⟨fun a ha => ?_, fun hb ht => ?_⟩
  · rw [hstep a (hS a ha).2.1]
    obtain ⟨h1, h2⟩ := H1 a ha
    have hp := hpos a ha
    generalize ((a * M)ᴴ * (a * M)).det.re = A at h1 h2 hp
    generalize (Mᴴ * M).det.re = B at h1 h2 hM
    have hq : 0 < d x W * (A / B) := mul_pos hD (div_pos hp hM)
    refine ⟨rpow_neg_le_of_le_mul hq hD hω0 hδ.le ?_, rpow_neg_le_of_le_mul hD hq hω0 hδ.le ?_⟩
    · have : 1 ≤ ω * (A / B) := by
        rw [← mul_div_assoc, le_div_iff₀ hM]; linarith
      nlinarith
    · have : A / B ≤ ω := by rw [div_le_iff₀ hM]; exact h1
      nlinarith
  · have h0 : 0 < Module.finrank E W := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      exact hb (Submodule.finrank_eq_zero.mp h)
    have hr : Module.finrank E W < r := by
      have := Submodule.finrank_lt ht
      simpa using this
    have H3 := H2 h0 hr
    have hDp : 0 < d x W ^ (-δ) := Real.rpow_pos_of_pos hD _
    calc _ = ∑ a ∈ S, d x W ^ (-δ) *
          (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) ^ (-δ) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [hstep a (hS a ha).2.1, Real.mul_rpow hD.le (div_pos (hpos a ha) hM).le]
      _ = d x W ^ (-δ) * ∑ a ∈ S,
          (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) ^ (-δ) := by rw [Finset.mul_sum]
      _ ≤ d x W ^ (-δ) * (S.card * c) := mul_le_mul_of_nonneg_left H3 hDp.le
      _ = _ := by ring

end GlobalTheory
end
