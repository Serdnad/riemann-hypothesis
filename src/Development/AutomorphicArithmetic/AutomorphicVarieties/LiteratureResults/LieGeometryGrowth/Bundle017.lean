module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianGaussianMomentBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpacePointLogEstimate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle010
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RealLieGroupChartsSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormPosDefOfTotallyReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevD
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle014
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmHom
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

private theorem trF_smul {E : Type} [Field E] [NumberField E] {a : ℕ} (s : ℝ) (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X (s • Y) = s * trF X Y := by
  simp [trF, Finset.mul_sum]

theorem UpperTheory.V.Lit.Geo.stepEx :
    StepEx := by
  intro E _ _ _ a ha U hU
  obtain ⟨L, hL, hUL⟩ := UpperTheory.unitaryGroup_lieAlgebra_eq_skewHermitian E a U hU
  obtain ⟨ε₁, C₁, hε₁, hroot⟩ := UpperTheory.unitarySimilitudeGroup_isSmooth_cmDatum E a
  obtain ⟨hI1, hI2, hI3⟩ := UpperTheory.lattice_point_count_bound E a ha L
  have hK := UpperTheory.hermitian_gaussian_moment_bound E a ha L hL
  obtain ⟨hT, hM⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  obtain ⟨hS1, φ, hφ, hS2⟩ := UpperTheory.realLieGroup_charts_smooth E a ha L hL
  obtain ⟨hB1, hB2⟩ := UpperTheory.lieDerivative_isDerivation_smoothFunctions E a {f | ∃ P ∈ poly E a, f = mean L P} (by
    rintro _ ⟨P, hP, rfl⟩
    exact ⟨(hM P hP).2, hS1 P hP⟩)
  obtain ⟨hD1, ⟨B, hB, hD2⟩, hD3⟩ := UpperTheory.hermitian_trace_form_estimate E a ha L hL
  obtain ⟨C₂, ε₂, hC₂, hε₂, hTay⟩ := UpperTheory.hermitian_trace_form_entry_estimate E a ha L hL
  obtain ⟨C₃, hC₃⟩ := UpperTheory.hermitian_space_log_estimate E a ha L hL
  obtain ⟨C₄, hC₄⟩ := UpperTheory.hermitian_space_point_log_estimate E a ha L hL
  obtain ⟨c₀, f₀, hc₀, hG⟩ := UpperTheory.traceForm_posDef_of_totallyReal E a ha L hL
  obtain ⟨δ, hδ, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * B ≤ ε₁ ∧ δ * B ≤ ε₂ ∧ C₂ * (δ * B) ^ 2 ≤ δ * c₀ := by
    have hp : 0 < C₂ * B ^ 2 + 1 := by positivity
    refine ⟨min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1)), by positivity, ?_, ?_, ?_⟩
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_left _ _))
    · exact (le_div_iff₀ hB).1 ((min_le_left _ _).trans (min_le_right _ _))
    · set d := min (min (ε₁ / B) (ε₂ / B)) (c₀ / (C₂ * B ^ 2 + 1))
      have h0 : 0 < d := by positivity
      have h1 : d * (C₂ * B ^ 2 + 1) ≤ c₀ := (le_div_iff₀ hp).1 (min_le_right _ _)
      nlinarith
  have hf0 : ∀ g, 0 ≤ fn L g := fun g => Real.log_nonneg (hT g).1
  have hq0 : ∀ g : GA E a, 0 ≤ Real.log (qht g) := fun g => Real.log_nonneg
    (le_ciInf fun _ => GroundTheory.Automorphic.AutomorphicForm.one_le_height _)
  have hn : ∀ g (t : ℝ), |t| ≤ 1 → ‖toL (t • ((-δ) • dev L g).1)‖ ≤ δ * B := fun g t ht => by
    change ‖t • (-δ) • toL (dev L g).1‖ ≤ _
    rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ]
    have h1 := mul_le_mul_of_nonneg_left (hD2 g).2.1 hδ.le
    have h2 : 0 ≤ δ * ‖toL (dev L g).1‖ := by positivity
    nlinarith
  have key : ∀ g (t : ℝ) (h : GL (Fin a) (Cinf E)), |t| ≤ 1 → h.val * star h.val = 1 + t • ((-δ) • dev L g).1 →
      |fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ δ * c₀ := fun g t h ht hh => by
    have h0 : ell E a (toL (t • ((-δ) • dev L g).1)) = 0 := by
      change ell E a (t • (-δ) • toL (dev L g).1) = 0
      rw [map_smul, map_smul, (hD3 g).1, smul_zero, smul_zero]
    have h1 := hTay g _ h h0 ((hn g t ht).trans hδ2) hh
    have h2 : trF (mom L g).1 (t • ((-δ) • dev L g).1) = -(t * δ * trF (dev L g).1 (dev L g).1) := by
      change trF (mom L g).1 (t • (-δ) • (dev L g).1) = _
      rw [trF_smul, trF_smul, (hD3 g).2]
      ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn g t ht) 2) hC₂
    refine le_trans (le_of_eq ?_) (h1.trans (h3.trans hδ3))
    congr 1
    ring
  have hπ : 0 ≤ Real.pi - 2 := by linarith [Real.pi_gt_three]
  refine ⟨fn L, fun g => (-δ) • dev L g, max (max C₁ (Real.pi * δ * B + δ * c₀)) (max C₃ C₄), δ * c₀, f₀,
    ⟨mul_pos hδ hc₀, ⟨φ, hφ, hB2 φ hS2⟩, fun γ t g => (hI1 γ t g).1, fun k g => ?_, fun u hu g => (hI2 U hU hUL u hu g).1,
      hf0, fun g => ?_, fun g => ?_, fun i j w => ?_, fun γ t g => ?_, fun k g => ?_, fun u hu g => ?_, fun g t ht => ?_,
      fun g h hg hh => ?_, fun g h hg hh => ?_, fun g t h ht hh => ?_⟩⟩
  · rw [fn, hI3, fn]
  · exact (hC₃ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (by linarith [hq0 g]))
  · exact (hC₄ g).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by linarith [hf0 g]))
  · obtain ⟨ψ, h1, h2⟩ := hB1 _ (Subalgebra.smul_mem _ (hD1 i j w) ((-δ : ℝ) : ℂ))
    exact ⟨ψ, fun g => by rw [h1]; rfl, h2⟩
  · rw [(hI1 γ t g).2]
  · rw [← hK k g]
    exact Subtype.ext (by simp [adHerm])
  · rw [(hI2 U hU hUL u hu g).2]
  · obtain ⟨h, h1, h2, h3⟩ := hroot (t • (-δ) • dev L g) ((hn g t ht).trans hδ1)
    exact ⟨h, h1, h2.trans (le_max_of_le_left (le_max_left _ _)), h3.trans (le_max_of_le_left (le_max_left _ _))⟩
  · have h1 := (abs_le.1 (key g 1 h (by simp) (by rwa [one_smul]))).1
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · have h1 := (abs_le.1 (key g (-1) h (by simp) (by rwa [neg_one_smul, ← sub_eq_add_neg]))).2
    have h2 := mul_le_mul_of_nonneg_left (hG g hg) hδ.le
    have h3 := mul_pos hδ hc₀
    nlinarith
  · refine le_max_of_le_left (le_max_of_le_right ?_)
    have h1 := key g t h ht hh
    have h2 : |Real.pi * t * δ * trF (dev L g).1 (dev L g).1| ≤ Real.pi * δ * B := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hδ]
      have := (hD2 g).2.2
      calc Real.pi * |t| * δ * |trF (dev L g).1 (dev L g).1| ≤ Real.pi * 1 * δ * B := by
            have := Real.pi_pos
            gcongr
        _ = _ := by ring
    have h3 := abs_add_le (fn L (g * infGL E a h) - fn L g - Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
      (Real.pi * t * δ * trF (dev L g).1 (dev L g).1)
    rw [sub_add_cancel] at h3
    linarith
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem cone_open (E : Type) [Field E] [NumberField E] (a : ℕ) : IsOpen (cone E a) :=
  isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := UpperTheory.V.Lit.Dr.locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩

private theorem homOm_zero {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (q : ℕ) : homOm G W (0 : G.Om (q + 1)) = 0 := by
  have e : (fun s => hom (W s) ((0 : G.Om (q + 1)).1 s)) = fun _ _ => 0 := by
    funext s p
    have : (fun t => hk (W s) t ((0 : G.Om (q + 1)).1 s) p) = fun _ => 0 := by
      funext t
      ext v
      simp [hk_apply]
    rw [hom, this, intervalIntegral.integral_zero]
  rw [homOm, e]
  refine Subtype.ext (funext fun s => funext fun p => ?_)
  by_cases hp : p ∈ G.Y
  · rw [toOm_apply G (fun _ => contDiffOn_const) s hp]
    rfl
  · rw [((toOm G _).2 s).2 p hp]
    rfl

private theorem d_step {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
    (G : UpperTheory.V.Lit.Dr.Geo Γ V S d) (W : S → V → V) (hF : IsFlow G W) (q : ℕ) (w : G.Om q) :
    G.dOm q (pbOm G W w - homOm G W (G.dOm q w)) = G.dOm q w := by
  have hH := omHom _ _ _ _ G W hF
  have e := hH.2.2.2 q (G.dOm q w)
  rw [hH.2.1, homOm_zero, add_zero, sub_eq_iff_eq_add] at e
  rw [map_sub, hH.1, e, add_sub_cancel_left]

private theorem corr_sub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} {α β : Co Ξ q} {w w' : (geo ho U Ξ).Om q}
    (h : Corr U Ξ α w.1) (h' : Corr U Ξ β w'.1) : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← h g x X, ← h' g x X]
  rfl

theorem UpperTheory.V.Lit.Geo.oneStep :
    OneStep := by
  intro E _ _ _ a U Ξ Y C hY q
  have ho := cone_open E a
  obtain ⟨W, hW⟩ := fieldDef E a U Y C hY
  have hF := (fieldFlow E a ho U Ξ Y C hY W hW).1
  obtain ⟨B₁, hB₁, h₁⟩ := pbBd E a ho U Ξ Y C hY W hW q
  obtain ⟨B₂, hB₂, h₂⟩ := homBd E a ho U Ξ Y C hY W hW q
  refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun η hη => ?_⟩
  obtain ⟨w, hw, hg⟩ := (levGood E a ho U Ξ q).1 η hη
  have hO := omGood _ _ _ _ _ W hF q
  obtain ⟨gP, gD⟩ := hO.1 w hg
  have gH := hO.2.2 _ gD
  obtain ⟨α, cα, lα⟩ := (levGood E a ho U Ξ q).2 _ gP
  obtain ⟨β, cβ, lβ⟩ := (levGood E a ho U Ξ q).2 _ gH
  have cd := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q η w hw
  refine ⟨α - β, (levD E a U Ξ q α lα).2 β lβ, ?_, fun g M M' hM hM' H H' => ?_⟩
  · have c := UpperTheory.V.Lit.Dr.corrD E a ho U Ξ q _ _ (corr_sub ho U Ξ cα cβ)
    rw [d_step _ W hF] at c
    exact (UpperTheory.V.Lit.Dr.corrUniq E a ho U Ξ (q + 1)).1 _ _ _ c cd
  · refine ((h₁ η α w hη hw cα g M hM H).sub
      (h₂ _ β _ (levD E a U Ξ q η hη).1 cd cβ g M' hM' H')).mono ?_
    nlinarith [mul_nonneg hB₁ hM', mul_nonneg hB₂ hM]
end
