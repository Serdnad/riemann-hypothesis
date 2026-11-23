module

public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle140
public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle040
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle002
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle007
public import Development.WeilBound.CoreStatements.VolumeEquality.Pieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

section

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

namespace Pot

theorem log_norm_an {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀)
    (h0 : F t₀ ≠ 0) : ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, Real.log ‖F t‖ = (G t).re := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have e1 : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
  refine ⟨fun t => Complex.log (F t / F t₀) + (Real.log ‖F t₀‖ : ℂ), (hH.clog e1).add analyticAt_const, ?_⟩
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 ht) (norm_ne_zero_iff.2 h0)]
  ring

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem val_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) {a : Ω} {r : ℂ} (h : ValAt ξ (z t₀) a r) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u t₀ ∧ ∀ᶠ t in 𝓝 t₀, ValAt ξ (z t) a (u t) := by
  obtain ⟨h0, s, rfl, -⟩ := h
  obtain ⟨U, hU, f, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : centre ξ ∈ U := h0.mem_open U.isOpen hU
  have hn : {b ∈ B | ⊤ ≤ z b ⁻¹ᵁ U} ∈ 𝓝 t₀ := (hz U f).1.mem_nhds ⟨ht, (SheetDecomposition.CovSch.top_le_iff _ _).2 hU⟩
  refine ⟨fun b => valAt' (z b) U f, GlobalTheory.SCV.analyticAt_of_differentiableOn (hz U f).2 hn, ?_⟩
  filter_upwards [hn] with t h1
  have h2 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h1.2
  rw [SheetDecomposition.CovSch.valAt'_eq _ _ h2, SheetDecomposition.CovSch.genMap_germ' ⟨centre (z t₀), h0⟩ U hU hg f]
  exact SheetDecomposition.CovSch.valAt_sec (hall _) U h2 hg f

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem coords_orbit {z : Sp ℂ ⟶ X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt ξ y z w') (hs : SameOrbit w w') :
    CoordsAt ξ y z w := by
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨fun k => (h.1 k).imp fun i hi => (IsUnit.mk0 _ (ha k)).mul hi, fun k i hi => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 k i (isUnit_of_mul_isUnit_right hi)
  refine ⟨h1, fun j => (h2 j).imp fun r hr => ⟨hr.1, ?_⟩⟩
  show a k * w' ⟨k, j⟩ = r * (a k * w' ⟨k, i⟩)
  rw [hr.2]
  ring

theorem log_h_smul (A : HermLine J) (a : K → ℂ) (ha : ∀ k, a k ≠ 0) {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => a p.1 * w p) = ∑ k, (A.a k : ℝ) * Real.log ‖a k‖ + Real.log (A.h w) := by
  have h1 : ∀ k, ‖a k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (ha k))
  rw [A.smul a w ha, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => h1 k) (A.pos w hw).ne',
    Real.log_prod fun k _ => h1 k]
  simp only [Real.log_zpow]

theorem log_orbit {I : Type} (s : Finset I) (A : HermLine J) (B : I → HermLine J) (hd : A.a = -∑ i ∈ s, (B i).a)
    {w w' : (Σ k, J k) → ℂ} (hs : SameOrbit w w') (hw : ∀ k, ∃ i, w' ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ i ∈ s, Real.log ((B i).h w) = Real.log (A.h w') + ∑ i ∈ s, Real.log ((B i).h w') := by
  obtain ⟨a, ha, rfl⟩ := hs
  simp only [log_h_smul _ a ha hw, hd, Finset.sum_add_distrib, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem log_h_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) (A : HermLine J) (e₀ T : Ω)
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hγ : ∀ p, AnalyticAt ℂ (fun t => γ t p) t₀) {ν : (Fin n → ℂ) → ℝ}
    (hν : ∀ᶠ t in 𝓝 t₀, 0 < ν t ∧ SecNorm ξ y A e₀ (z t) (γ t) T (ν t)) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, -Real.log (A.h (γ t)) = Real.log (ν t) + (G t).re := by
  obtain ⟨p0, h0⟩ := hν.self_of_nhds
  obtain ⟨c, hc⟩ := h0.exists_chart
  obtain ⟨u₀, hu₀, e0⟩ := h0.2.2 c hc
  obtain ⟨u, hu, hue⟩ := val_an hz hall ht hu₀
  let F : (Fin n → ℂ) → ℂ := fun t => u t * ∏ k, γ t ⟨k, c k⟩ ^ A.a k
  have hF : AnalyticAt ℂ F t₀ := hu.mul (Finset.analyticAt_fun_prod _ fun k _ => (hγ _).zpow (hc k))
  have hcn : ∀ᶠ t in 𝓝 t₀, ∀ k, γ t ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hγ _).continuousAt.eventually_ne (hc k)
  have hev : ∀ᶠ t in 𝓝 t₀, ν t * A.h (γ t) = ‖F t‖ := by
    filter_upwards [hν, hue, hcn] with t h1 h2 h3
    obtain ⟨u', hu', e⟩ := h1.2.2.2 c h3
    rw [e, CxVal.unique hu' h2]
    simp only [F, norm_mul, norm_prod, norm_zpow]
  have hF0 : F t₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, ← hev.self_of_nhds]
    exact (mul_pos p0 (A.pos _ fun k => ⟨c k, hc k⟩)).ne'
  obtain ⟨G, hG, hGe⟩ := log_norm_an hF hF0
  refine ⟨fun t => -G t, hG.neg, ?_⟩
  filter_upwards [hν, hev, hcn, hGe] with t h1 h2 h3 h4
  rw [Complex.neg_re, ← h4, ← h2, Real.log_mul h1.1.ne' (A.pos _ fun k => ⟨c k, h3 k⟩).ne']
  ring

theorem holo_comp {e e' : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {A : FinHolAtlas e M}
    {B : FinHolAtlas e' N} {ψ : M → N} (hψ : HoloMap A B ψ) (k : Fin A.n) {t : Fin e → ℂ} (ht : t ∈ (A.chart k).target)
    {W : Set N} {f : N → ℂ} (hf : B.HoloOn W f) (hW : ψ ((A.chart k).symm t) ∈ W) :
    AnalyticAt ℂ (fun t' => f (ψ ((A.chart k).symm t'))) t := by
  obtain ⟨j, hj⟩ := B.cover (ψ ((A.chart k).symm t))
  have h1 := hψ.2 k j t ⟨ht, hj⟩
  have h2 := hf j (B.chart j (ψ ((A.chart k).symm t))) ⟨(B.chart j).map_source hj, by
    show (B.chart j).symm _ ∈ W
    rwa [(B.chart j).left_inv hj]⟩
  have h3 := AnalyticAt.comp (f := B.chart j ∘ ψ ∘ (A.chart k).symm) (x := t) h2 h1
  refine h3.congr ?_
  have hc : ContinuousAt (fun t' => ψ ((A.chart k).symm t')) t :=
    hψ.1.continuousAt.comp ((A.chart k).continuousAt_symm ht)
  filter_upwards [hc.eventually_mem ((B.chart j).open_source.mem_nhds hj)] with t' h
  simp only [Function.comp_apply, (B.chart j).left_inv h]

end Pot

open Pot in
theorem potLoc : PotLoc := by
  intro E _ _ _ H D l Xo c Y S RM Sys Fx Or ψ k V z tr ν hψ hπ hV hVt hpt t₁ ht₁ p
  classical
  obtain ⟨τ, i⟩ := p
  let w : _ → Or.Re.R.X := fun t => ψ ((Sys.A.chart k).symm t)
  let γ : _ → (Σ k, RM.ι k) → ℂ := fun t => Or.Re.R.lift (w t₁) (w t)
  have hwc : ∀ t ∈ V, ContinuousAt w t := fun t ht =>
    hψ.1.continuousAt.comp ((Sys.A.chart k).continuousAt_symm (hVt ht))
  let B := V ∩ w ⁻¹' Or.Re.R.U (w t₁)
  have hB : IsOpen B := (continuousOn_of_forall_continuousAt hwc).isOpen_inter_preimage hV (Or.Re.R.isOpen_U _)
  have ht₁B : t₁ ∈ B := ⟨ht₁, Or.Re.R.mem_U _⟩
  have hγ : ∀ t ∈ B, ∀ q, AnalyticAt ℂ (fun t => γ t q) t := fun t ht q =>
    holo_comp hψ k (hVt ht.1) (Or.Re.R.holo (w t₁) q) ht.2
  have horb : ∀ t ∈ B, SameOrbit (γ t) (Or.Re.R.lift (w t) (w t)) := fun t ht => Or.Re.R.compat _ _ _ ⟨ht.2, Or.Re.R.mem_U _⟩
  have hco : ∀ t ∈ B, CoordsAt Or.𝔐.ξ RM.y (z t) (γ t) := fun t ht => coords_orbit (hpt t ht.1).2.1 (horb t ht)
  have hz : IsHolTo B z := GlobalTheory.T.holomorphic_coords_of_generic_point _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie Or.𝔐.all _ B γ z hB
    (differentiableOn_pi.2 fun q t ht => (hγ t ht q).differentiableAt.differentiableWithinAt) hco
  have hop : ∀ t ∈ V, Or.Re.π (w t) ∈ Sys.open' := fun t ht => by
    rw [hπ]
    exact (hpt t ht).1
  have hin : ∀ t ∈ V, Or.𝔐.Interior (z t) := fun t ht => (Or.interior (w t) (z t) (hpt t ht).2.1).2 (hop t ht)
  have hroot : ∀ r : RootIx D, ∃ G : _ → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
      -Real.log ((Or.sing r).h (γ t)) = Real.log (ν r t ^ HodgeCpt.rootSgn D r) + (G t).re := fun r => by
    refine log_h_an (y := RM.y) hz Or.𝔐.all ht₁B (Or.sing r) (Or.e r) (tr r ^ HodgeCpt.rootSgn D r) (hγ t₁ ht₁B) ?_
    filter_upwards [hB.mem_nhds ht₁B] with t ht
    exact ⟨zpow_pos ((hpt t ht.1).2.2 r).pos _, Or.hodge r (z t) (γ t) (hco t ht) (hin t ht.1) _ _ ((hpt t ht.1).2.2 r)⟩
  choose G hG hGe using hroot
  obtain ⟨W, hW, hwW, G₀, hG₀, e₀⟩ := Or.Re.ref_pot (some (τ, i)) (w t₁) trivial
  have hG₀a : AnalyticAt ℂ (fun t => G₀ (w t)) t₁ := holo_comp hψ k (hVt ht₁) hG₀ hwW
  refine ⟨fun t => ∑ j ∈ Finset.Iic i, G (τ, j) t - G₀ (w t),
    (Finset.analyticAt_fun_sum _ fun j _ => hG _).sub hG₀a, ?_⟩
  filter_upwards [hB.mem_nhds ht₁B, (hwc t₁ ht₁).eventually_mem (hW.mem_nhds hwW),
    (Filter.eventually_all_finset (Finset.Iic i)).2 fun j _ => hGe (τ, j)] with t ht htW h3
  have e1 : Real.log ((Or.Re.ref (some (τ, i))).h (γ t)) -
      (Sys.th (some (τ, i))).φ (Or.Re.π (w t₁)) (Or.Re.π (w t)) = (G₀ (w t)).re := e₀ (w t) htW
  have e2 := Or.fund_sing τ i (w t) (hop t ht.1)
  have e3 := log_orbit (Finset.Iic i) (Or.Re.ref (some (τ, i))) (fun j => Or.sing (τ, j))
    (by rw [Or.fund_deg]; simp only [Or.sing_deg]) (horb t ht) (Or.Re.R.mem _ _ (Or.Re.R.mem_U _)).1
  have e4 : ∑ j ∈ Finset.Iic i, -Real.log ((Or.sing (τ, j)).h (γ t)) =
      ∑ j ∈ Finset.Iic i, ((HodgeCpt.rootSgn D (τ, j) : ℝ) * Real.log (ν (τ, j) t) + (G (τ, j) t).re) :=
    Finset.sum_congr rfl fun j hj => by rw [h3 j hj, Real.log_zpow]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at e4
  simp only [w, hπ] at e1 e2
  show (Sys.th (some (τ, i))).φ _ _ + Sys.ph (some (τ, i)) _ = _
  rw [Complex.sub_re, Complex.re_sum]
  simp only [w] at e3 ⊢
  linarith

end RootFieldNumerics
end
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

noncomputable section

namespace RootFieldNumerics

open PC

namespace PC

theorem coeff_an {n m g : ℕ} {V : Set (Fin n → ℂ)} (hV : IsOpen V) (x : Fin m → (Fin n → ℂ) → Fin g → ℂ)
    (y : (Fin n → ℂ) → Fin g → ℂ) (hx : ∀ i, AnalyticOnNhd ℂ (x i) V) (hy : DifferentiableOn ℂ y V)
    (hli : ∀ t ∈ V, LinearIndependent ℂ fun i => x i t) (hm : ∀ t ∈ V, y t ∈ Submodule.span ℂ (Set.range fun i => x i t)) :
    ∃ w : (Fin n → ℂ) → Fin m → ℂ, (∀ i, AnalyticOnNhd ℂ (fun t => w t i) V) ∧ ∀ t ∈ V, y t = ∑ i, w t i • x i t := by
  have h : ∀ t, ∃ w : Fin m → ℂ, t ∈ V → y t = ∑ i, w i • x i t := fun t => by
    by_cases ht : t ∈ V
    · obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hm t ht)
      exact ⟨w, fun _ => hw.symm⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose w hw using h
  have hd := GlobalTheory.T.holomorphic_coefficients_in_frame n m g V x y w hV (fun i => (hx i).differentiableOn) hy hli hw
  exact ⟨w, fun i => GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hV (differentiableOn_pi.1 hd i), hw⟩

end PC

theorem perCoord : PerCoord := by
  intro E _ _ _ Ψ _ g n p q Λ _ _ V R σ x x' hV hR hσ ⟨hxa, hxa', hfr⟩
  classical
  rcases V.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · exact ⟨0, 0, 0, fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ h => h.elim⟩
  have := (R t₀).free
  have := (R t₀).fin
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ (R t₀).rank
  have hrk : ∀ t ∈ V, ∀ τ, Module.finrank ℂ (eigSp (R t).B (σ τ)) = p ∧
      Module.finrank ℂ (eigSp (R t).B ((starRingEnd ℂ).comp (σ τ))) = q := fun t ht τ => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hfr t ht τ
    rw [← h2, ← h4, finrank_span_eq_card h1, finrank_span_eq_card h3]
    simp
  choose e he heo hes using fun τ => exists_onb (R t₀) _ (hrk t₀ ht₀ τ).1
  choose e' he' heo' hes' using fun τ => exists_onb (R t₀) _ (hrk t₀ ht₀ τ).2
  let u : Ψ → Fin (p + q) → Fin g → ℂ := fun τ a =>
    if h : (a : ℕ) < q then 0 else e τ ⟨a - q, by have := a.2; omega⟩
  let u' : Ψ → Fin (p + q) → Fin g → ℂ := fun τ a => if h : (a : ℕ) < q then e' τ ⟨a, h⟩ else 0
  have hu : ∀ τ a, u τ a ∈ eigSp (R t₀).B (σ τ) := fun τ a => by
    simp only [u]
    split_ifs
    exacts [Submodule.zero_mem _, he _ _]
  have hu' : ∀ τ a, u' τ a ∈ eigSp (R t₀).B ((starRingEnd ℂ).comp (σ τ)) := fun τ a => by
    simp only [u']
    split_ifs
    exacts [he' _ _, Submodule.zero_mem _]
  choose η hη hη' using fun τ a => exists_pair b (R t₀) (u τ a) (u' τ a)
  have hact : ∀ τ a r, act b r (η τ a) = σ τ r • η τ a := fun τ a r => by
    refine ext_pair b (R t₀) ?_ ?_
    · rw [Pc_act, map_smul, hη, mem_eig.1 (hu τ a)]
    · rw [star_act, Pc_act, star_smul, map_smul, hη', mem_eig.1 (hu' τ a)]
      rfl
  have hPd : ∀ ξ, DifferentiableOn ℂ (fun t => Pc b (R t) ξ) V := fun ξ => by
    simp only [Pc_apply]
    exact DifferentiableOn.fun_sum fun k _ => (hR.2 (b k)).fun_const_smul (ξ k)
  choose m hma hm using fun τ a => coeff_an hV (x τ) (fun t => Pc b (R t) (η τ a)) (hxa τ) (hPd _)
    (fun t ht => (hfr t ht τ).1.1) fun t ht => by
      rw [(hfr t ht τ).1.2]
      exact mem_eig.2 fun r => by rw [← Pc_act, hact, map_smul]
  choose m' hma' hm' using fun τ a => coeff_an hV (x' τ) (fun t => Pc b (R t) (star (η τ a))) (hxa' τ) (hPd _)
    (fun t ht => (hfr t ht τ).2.1) fun t ht => by
      rw [(hfr t ht τ).2.2]
      exact mem_eig.2 fun r => by
        rw [← Pc_act, ← star_act, hact, star_smul, map_smul]
        rfl
  have hspan : Submodule.span ℂ (Set.range (Sum.elim (fun a : Ψ × Fin (p + q) => u a.1 a.2)
      fun a : Ψ × Fin (p + q) => u' a.1 a.2)) = ⊤ := by
    refine mem_of_eig (R t₀).B hσ _ (fun τ z hz => ?_) fun τ z hz => ?_
    · obtain ⟨α, rfl⟩ := hes τ z hz
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨.inl (τ, ⟨q + i, by have := i.2; omega⟩), ?_⟩)
      simp [u]
    · obtain ⟨α, rfl⟩ := hes' τ z hz
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨.inr (τ, ⟨i, by have := i.2; omega⟩), ?_⟩)
      simp [u']
  have hcc : ∀ a : Λ, ∃ c : Ψ → Fin (p + q) → ℂ, io b a = ∑ τ, ∑ k, (c τ k • η τ k + star (c τ k) • star (η τ k)) := fun a => by
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan ▸ Submodule.mem_top (x := (R t₀).P a))
    let c : Ψ → Fin (p + q) → ℂ := fun τ k => if (k : ℕ) < q then star (α (.inr (τ, k))) else α (.inl (τ, k))
    have h1 : Pc b (R t₀) (io b a) = Pc b (R t₀) (∑ τ, ∑ k, (c τ k • η τ k + star (c τ k) • star (η τ k))) := by
      rw [Pc_io, ← hα, Fintype.sum_sum_type, ← Finset.sum_add_distrib, Fintype.sum_prod_type]

      simp only [map_sum, map_add (f := _), map_smul, hη, hη', Sum.elim_inl, Sum.elim_inr]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases h : (k : ℕ) < q <;> simp [u, u', c, h]
    refine ⟨c, ext_pair b (R t₀) h1 ?_⟩
    rw [star_io, h1]
    simp only [star_sum, star_add, star_smul, star_star, add_comm]
  choose cc hcc using hcc
  refine ⟨fun τ t => Matrix.of fun i a => m τ a t i, fun τ t => Matrix.of fun i a => m' τ a t i, fun τ a => cc a τ,
    fun τ i a => hma τ a i, fun τ i a => hma' τ a i, fun t ht => ⟨fun τ => ?_, fun a => ?_, ?_⟩⟩
  · ext a a'
    have h1 := psi_eq b (R t) (η τ a) (η τ a')
    rw [hR.1 t ht t₀ ht₀, ← psi_eq b (R t₀), hη, hη, hη', hη', hm τ a t ht, hm τ a' t ht, hm' τ a t ht, hm' τ a' t ht,
      ip_sum, ip_sum] at h1
    have h2 : (R t₀).ip (u τ a) (u τ a') - (R t₀).ip (u' τ a') (u' τ a) =
        diagonal (fun a => (sigForm (p + q) p a : ℂ)) a a' := by
      have ha := a.2
      have ha' := a'.2
      by_cases h : (a : ℕ) < q <;> by_cases h' : (a' : ℕ) < q <;>
        simp only [u, u', h, h', dif_pos, dif_neg, not_false_eq_true, ip_zero_left, ip_zero_right, heo, heo', diagonal_apply,
          sigForm, Nat.add_sub_cancel_left, Fin.ext_iff, if_true, if_false] <;> split_ifs <;> first | omega | simp
    rw [← h2, ← h1]
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, transpose_apply, map_apply, of_apply, RiemLat.gram,
      Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [Complex.star_def]; ring
  · rw [← Pc_io b, hcc a]

    simp only [map_sum, map_add (f := _), map_smul, fun τ k => hm τ k t ht, fun τ k => hm' τ k t ht, Finset.sum_add_distrib]
    simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, of_apply, Finset.sum_smul, Pi.star_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun τ _ => ?_ <;> rw [Finset.sum_comm] <;> simp only [mul_comm]
  · have hs : Submodule.span ℂ (Set.range (Sum.elim (fun a : Ψ × Fin p => x a.1 a.2 t)
        fun a : Ψ × Fin q => x' a.1 a.2 t)) = ⊤ := by
      refine mem_of_eig (R t).B hσ _ (fun τ => ?_) fun τ => ?_
      · rw [← (hfr t ht τ).1.2]
        exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨.inl (τ, i), rfl⟩)
      · rw [← (hfr t ht τ).2.2]
        exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨.inr (τ, i), rfl⟩)
    refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hs.ge ?_, hs⟩
    have hg := GlobalTheory.T.genus_eq_card_mul_signature E Ψ g q p (R t).B σ hσ (hrk t ht)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Module.finrank_fin_fun]
    rw [hg]
    ring

end RootFieldNumerics
end
end

section

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

namespace Pts

theorem isHolTo_of_local {X : Scheme.{0}} {n : ℕ} {T : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)}
    (h : ∀ t ∈ T, ∃ B, B ⊆ T ∧ t ∈ B ∧ IsHolTo B y) : IsHolTo T y := by
  intro U f
  have key : ∀ t ∈ {b ∈ T | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ T | ⊤ ≤ y b ⁻¹ᵁ U} ∈ 𝓝 t ∧
      DifferentiableAt ℂ (fun b => valAt' (y b) U f) t := by
    rintro t ⟨ht, hU⟩
    obtain ⟨B, hBT, htB, hB⟩ := h t ht
    have hn := (hB U f).1.mem_nhds (show t ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} from ⟨htB, hU⟩)
    exact ⟨mem_of_superset hn fun b hb => ⟨hBT hb.1, hb.2⟩, (hB U f).2.differentiableAt hn⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun t ht => (key t ht).1, fun t ht => (key t ht).2.differentiableWithinAt⟩

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (w : (Σ k, ι k) → ℂ) :
    w ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  simpa using h.2 1 trivial

theorem sat_iff {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {w w' : (Σ k, ι k) → ℂ} :
    w ∈ torusSat {w'} ↔ SameOrbit w w' :=
  ⟨fun ⟨_, e, a, ha, h⟩ => ⟨a, ha, by rw [h, Set.mem_singleton_iff.1 e]; rfl⟩, fun ⟨a, ha, h⟩ => ⟨w', rfl, a, ha, h⟩⟩

theorem analyticAt_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : FinHolAtlas e X}
    {B : FinHolAtlas e Y} {ψ : X → Y} (hψ : HoloMap A B ψ) {U : Set Y} {f : Y → ℂ} (hf : B.HoloOn U f)
    (k : Fin A.n) {t : Fin e → ℂ} (ht : t ∈ (A.chart k).target) (htU : ψ ((A.chart k).symm t) ∈ U) :
    AnalyticAt ℂ (fun s => f (ψ ((A.chart k).symm s))) t := by
  obtain ⟨j, hj⟩ := B.cover (ψ ((A.chart k).symm t))
  have h1 : AnalyticAt ℂ (B.chart j ∘ ψ ∘ (A.chart k).symm) t := hψ.2 k j t ⟨ht, hj⟩
  have h2 : AnalyticAt ℂ (f ∘ (B.chart j).symm) ((B.chart j ∘ ψ ∘ (A.chart k).symm) t) :=
    hf j _ ⟨(B.chart j).map_source hj, by
      show (B.chart j).symm (B.chart j (ψ ((A.chart k).symm t))) ∈ U
      rwa [(B.chart j).left_inv hj]⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (fun s => ψ ((A.chart k).symm s)) t :=
    hψ.1.continuousAt.comp ((A.chart k).continuousAt_symm ht)
  filter_upwards [hc.eventually ((B.chart j).open_source.mem_nhds hj)] with s hs
  show f ((B.chart j).symm (B.chart j (ψ ((A.chart k).symm s)))) = _
  rw [(B.chart j).left_inv hs]

end Pts

open Pts

theorem ptsFam : PtsFam := by
  intro E _ _ _ H D l Xo c Y S RM Sys Fx Or ψ hJ hψ hπψ hψπ
  have hnJ : ∀ w, w ∉ mcPts Or.Re.J := fun w => by rw [hJ]; exact not_mem_top w
  choose z hz using fun x : Sys.X =>
    SheetDecomposition.exists_pt Or.𝔐 (Or.Re.R.mem (ψ x) (ψ x) (Or.Re.R.mem_U (ψ x)))
  have hol : ∀ k, IsHolTo (Sys.A.chart k).target fun t => z ((Sys.A.chart k).symm t) := fun k => by
    refine isHolTo_of_local fun t₀ ht₀ => ?_
    let w₀ := ψ ((Sys.A.chart k).symm t₀)
    have hB : IsOpen ((Sys.A.chart k).target ∩ (Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' Or.Re.R.U w₀)) :=
      (Sys.A.chart k).symm.isOpen_inter_preimage ((Or.Re.R.isOpen_U w₀).preimage hψ.1)
    refine ⟨(Sys.A.chart k).target ∩ (Sys.A.chart k).symm ⁻¹' (ψ ⁻¹' Or.Re.R.U w₀), Set.inter_subset_left,
      ⟨ht₀, Or.Re.R.mem_U w₀⟩, ?_⟩
    refine GlobalTheory.T.holomorphic_coords_of_generic_point _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie Or.𝔐.all _ _
      (fun t => Or.Re.R.lift w₀ (ψ ((Sys.A.chart k).symm t))) _ hB ?_ ?_
    · refine differentiableOn_pi.2 fun p t ht => ?_
      exact (analyticAt_comp hψ (Or.Re.R.holo w₀ p) k ht.1 ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      exact SheetDecomposition.coords_of_sat Or.𝔐 (hz _) (sat_iff.2 (Or.Re.R.compat _ _ _ ⟨ht.2, Or.Re.R.mem_U _⟩))
  refine ⟨z, fun x x' e => ?_, hz, hol, fun U hU => ?_⟩
  · have h := sat_iff.1 (SheetDecomposition.sat_of_coords Or.𝔐 (hz x') (e ▸ hz x))
    rw [← hπψ x, Or.Re.R.inj _ _ (hnJ _) h, hπψ]
  · obtain ⟨g, hg, hgU⟩ := SheetDecomposition.ChartForm.exists_form Or.𝔐.tie U hU
    obtain ⟨w, hw, hwg⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts (J := Ideal.span {g}) RM.arith
      (fun h => hg (h (Ideal.subset_span rfl)))
    have hg0 : MvPolynomial.aeval w g ≠ 0 := fun h0 => hwg ⟨hw.1, fun f hf => by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hf
      have : MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by
        rw [MvPolynomial.eval_map]
        exact h0
      rw [map_mul, map_mul, this, mul_zero]⟩
    obtain ⟨w₁, hw₁⟩ := Or.Re.R.surj w hw (hnJ w)
    have hsym : SameOrbit w (Or.Re.R.lift w₁ w₁) := by
      obtain ⟨a, ha, h⟩ := hw₁
      refine ⟨fun k => (a k)⁻¹, fun k => inv_ne_zero (ha k), funext fun p => ?_⟩
      rw [h]
      simp only [inv_mul_cancel_left₀ (ha _)]
    have hc : CoordsAt Or.𝔐.ξ RM.y (z (Or.Re.π w₁)) w :=
      SheetDecomposition.coords_of_sat Or.𝔐 (hz _) (sat_iff.2 (by rw [hψπ]; exact hsym))
    have hx₀ : centre (z (Or.Re.π w₁)) ∈ U := hgU _ _ (Or.𝔐.all _) hc hg0
    obtain ⟨k, hk⟩ := Sys.A.cover (Or.Re.π w₁)
    have hopen := (Sys.A.chart k).isOpen_inter_preimage (hol k U 0).1
    have hd := (GlobalTheory.T.section_boundary_closed_and_codense _ _ Sys.A Sys.L Sys.s Sys.nb Sys.m Sys.W Sys.sec Sys.snc).2
    obtain ⟨x, ⟨hxs, -, hxU⟩, hxo⟩ := hd.inter_open_nonempty _ hopen ⟨Or.Re.π w₁, hk, (Sys.A.chart k).map_source hk, by
      show ⊤ ≤ z ((Sys.A.chart k).symm (Sys.A.chart k _)) ⁻¹ᵁ U
      rw [(Sys.A.chart k).left_inv hk]
      exact (SheetDecomposition.top_le_iff_pt _ _ _).2 hx₀⟩
    refine ⟨x, hxo, ?_⟩
    have h2 : ⊤ ≤ z ((Sys.A.chart k).symm (Sys.A.chart k x)) ⁻¹ᵁ U := hxU
    rw [(Sys.A.chart k).left_inv hxs] at h2
    exact (SheetDecomposition.top_le_iff_pt _ _ _).1 h2

end RootFieldNumerics
end
end
