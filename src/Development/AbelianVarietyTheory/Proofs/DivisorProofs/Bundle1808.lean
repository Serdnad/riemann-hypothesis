module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeAtNearbyIndices
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsOrbitalTermEq
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_mono_radius {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (P : Pair p) (a b : ℤ) {R R' : ℝ} (h : R ≤ R') : P.lc a b R ≤ P.lc a b R' := by
  have hsub : P.Bl a b R ⊆ P.Bl a b R' := fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h⟩
  have hfin : (P.Bl a b R').Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P a b R'
  have hle : (P.Bl a b R).ncard ≤ (P.Bl a b R').ncard := Set.ncard_le_ncard hsub hfin
  unfold VolBr.Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl a b R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle)

theorem lc_nearby_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b c : ℕ), 0 < b → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
      P.lc 0 (b * M + (M / n : ℕ) - c) 2 ≤ P.lc 0 (b * M - c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b c hb hR ε hε
  obtain ⟨α, β, hαβ⟩ := hR
  refine GlobalTheory.eventually_le_at_nearby_indices (D + 1) b c
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 j 2) (fun j => P.lc 0 j 1) α β
    (Nat.succ_pos D) hb hαβ ?_ ?_ ε hε
  · intro j
    simp
  · intro η hη
    have ht : Tendsto (fun j : ℕ => Real.exp (η * j)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hη tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (eventually_ge_atTop 2)] with j hj
    exact lc_mono_radius hX P 0 (j : ℤ) hj

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (M : HermLB p), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → ∀ (ρ : ℕ) (t₁ : ℝ), (∀ m : ℕ, 0 < m → ∃ v : Fin (ρ * m ^ D) → X.functionField, LinearIndependent ℤ v ∧ ∀ s, v s ∈ P.Bl (m * a) (m * b) (Real.exp (t₁ * m))) → (D.factorial : ℝ) * ρ ≤ gdeg M D := by
  intro hA hHS k _ X _ p D hX P a b M hRep hAmp hSemi ρ t₁ hv
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => M).1
  have hα : M.IsSelfInter (Φ (MvPolynomial.X PUnit.unit ^ (D + 1))) :=
    ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, hlim⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hHS k X p D hX P a b 0 0 M _ hRep hAmp hSemi hα
  have key := GlobalTheory.T.le_slope_of_tendsto_div_pow_of_log_lower_bound D (fun t m => P.lc (m * a) (m * b) (Real.exp (t * m)))
    (Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / ((D + 1).factorial : ℝ))
    (((D : ℝ) + 1) * gdeg M D / ((D + 1).factorial : ℝ)) ρ t₀ t₁ (Nat.cast_nonneg _) ?_ ?_
  · have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * (D.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
    have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [hf, mul_div_mul_left _ _ hD1.ne', le_div_iff₀ hD] at key
    linarith
  · intro t ht
    simpa using hlim t ht
  · intro t m Q hm hQ hle
    obtain ⟨v, hli, hvB⟩ := hv m hm
    have hB := GlobalTheory.VolBr.Pair.isBallFam k X p P (m * a) (m * b)
    have hcard := GlobalTheory.T.seminormBallFamily_pow_le_encard_of_linearIndependent _ _ _ hB (ρ * m ^ D) Q (Real.exp (t₁ * m)) v (Real.exp_pos _).le hli hvB
    have hsub : P.Bl (m * a) (m * b) (((ρ * m ^ D : ℕ) : ℝ) * Q * Real.exp (t₁ * m)) ⊆
        P.Bl (m * a) (m * b) (Real.exp (t * m)) :=
      (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ hB).1 _ _ (by push_cast; linarith)
    have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P (m * a) (m * b) (Real.exp (t * m))
    have h1 : ((Q ^ (ρ * m ^ D) : ℕ) : ℕ∞) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard :=
      hcard.trans (Set.encard_le_encard hsub)
    rw [← hfin.cast_ncard_eq] at h1
    have hn : Q ^ (ρ * m ^ D) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard := by exact_mod_cast h1
    show _ ≤ Real.log _
    have hQ' : (0 : ℝ) < ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by positivity
    calc (ρ : ℝ) * (m : ℝ) ^ D * Real.log Q = Real.log ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      _ ≤ Real.log ((P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard : ℝ) :=
          Real.log_le_log hQ' (by exact_mod_cast hn)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem eventually_poly_mul_pow_le_exp (c C t : ℝ) (n : ℕ) (hC : 1 ≤ C) (ht : Real.log C < t) :
    ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ^ n * C ^ m ≤ Real.exp (t * m) := by
  have hδ : 0 < t - Real.log C := sub_pos.2 ht
  have hc1 : 0 < |c| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop n hδ).bound (c := 1 / (|c| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  have hCpos : 0 < C := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hm
  have hexp : Real.exp (t * m) = Real.exp ((t - Real.log C) * m) * C ^ m := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCpos, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hmn : (0 : ℝ) ≤ (m : ℝ) ^ n := by positivity
  have hle : c * (m : ℝ) ^ n ≤ Real.exp ((t - Real.log C) * m) := by
    calc c * (m : ℝ) ^ n ≤ (|c| + 1) * (m : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hmn
      _ ≤ (|c| + 1) * (1 / (|c| + 1) * Real.exp ((t - Real.log C) * m)) :=
          mul_le_mul_of_nonneg_left hm hc1.le
      _ = _ := by field_simp
  exact mul_le_mul_of_nonneg_right hle (by positivity)

theorem count_ball_asymp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → ∀ g : ℝ, Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g) → ∀ C : ℝ, 1 ≤ C → (∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m))) → ∀ t : ℝ, Real.log C < t → Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (Real.exp (t * m))).ncard : ℝ) - (r m * (t * m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 + Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  intro k _ X _ p D hX hS P hP ω r f hf hli g hg C hC hball t ht
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hρ := fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hS P.L hP σ (ω σ)
  choose ρ hρr hρ0 _ using hρ
  have hbd : ∀ σ, ∃ b : ℝ, ∀ y, ρ σ y ≤ b := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨b, hb⟩ := (isCompact_range (hρr σ).1).bddAbove
    exact ⟨b, fun y => hb ⟨y, rfl⟩⟩
  choose b hb using hbd
  set B : ℝ := ∑ σ, |b σ| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρB : ∀ σ y, ρ σ y ≤ B := fun σ y => (hb σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |b σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set K : ℝ := B / D.factorial + 1 with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ B / D.factorial := by positivity
    linarith
  set V : ℝ := max 1 (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) with hVdef
  have hV : 1 ≤ V := le_max_left _ _
  have hmorse := GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hS P hP ω ρ hρr 1 one_pos
  have hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ (g + 1) * (m : ℝ) ^ D := by
    filter_upwards [hg.eventually (gt_mem_nhds (lt_add_one g)), eventually_ge_atTop 1] with m hm h1
    have h0 : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast h1) D
    exact ((div_lt_iff₀ h0).1 hm).le
  have hexp := eventually_poly_mul_pow_le_exp (2 * (g + 1) * K * V) C t (2 * D) hC ht
  refine squeeze_zero_norm' (a := fun m : ℕ =>
    2 * ((r m : ℝ) / (m : ℝ) ^ D) * ((Real.log (2 * K * V) + D * Real.log m) / m)) ?_ ?_
  · filter_upwards [hmorse, hr, hexp, eventually_ge_atTop 1] with m hm hrm hem h1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hm0 : (0 : ℝ) < m := by linarith
    have hmD : (0 : ℝ) < (m : ℝ) ^ D := pow_pos hm0 D
    have hM : 1 ≤ K * (m : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm1)
    have hcmb : ∀ (c : Fin (r m) → ℂ) σ y, cmb (vals P m 1 (f m)) c σ y ≤
        K * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c := by
      intro c σ y
      have h := hm (Fin (r m)) (f m) (hf m) c σ y
      have hl2 : 0 ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c :=
        finsum_nonneg fun σ => integral_nonneg fun y => by unfold cmb; positivity
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hmD.le) hl2)
      have : ρ σ y / D.factorial ≤ B / D.factorial :=
        div_le_div_of_nonneg_right (hρB σ y) (by positivity)
      linarith
    have hR : 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V) ≤ Real.exp (t * m) := by
      calc 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V)
          ≤ 2 * ((g + 1) * (m : ℝ) ^ D) * C ^ m * (K * (m : ℝ) ^ D * V) := by
            have : 0 ≤ C ^ m * (K * (m : ℝ) ^ D * V) := by
              have : 0 ≤ C := by linarith
              positivity
            nlinarith
        _ = 2 * (g + 1) * K * V * (m : ℝ) ^ (2 * D) * C ^ m := by ring
        _ ≤ _ := hem
    have key := GlobalTheory.T.abs_log_card_ballIn_sub_gramVolume_le k X p D hX hS P ω (m : ℤ) 1 (r m) (f m) (hf m) (hli m) (K * (m : ℝ) ^ D) V (C ^ m)
      (Real.exp (t * m)) hM hV (le_max_right _ _) (by positivity) (Real.exp_pos _) hcmb (hball m h1) hR
    rw [Real.log_exp] at key
    have hlog : Real.log (2 * (K * (m : ℝ) ^ D * V)) = Real.log (2 * K * V) + D * Real.log m := by
      have e : 2 * (K * (m : ℝ) ^ D * V) = (2 * K * V) * (m : ℝ) ^ D := by ring
      rw [e, Real.log_mul (by positivity) hmD.ne', Real.log_pow]
    have hmD1 : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hmD1, div_le_iff₀ hmD1]
    refine key.trans (le_of_eq ?_)
    rw [hlog, pow_succ]
    field_simp
  · have h1 : Tendsto (fun m : ℕ => 2 * ((r m : ℝ) / (m : ℝ) ^ D)) atTop (𝓝 (2 * g)) := hg.const_mul 2
    have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun m : ℕ => (Real.log (2 * K * V) + D * Real.log m) / m) atTop (𝓝 0) := by
      have := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (2 * K * V))).add
        ((hl.comp tendsto_natCast_atTop_atTop).const_mul (D : ℝ))
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      ring
    simpa using h1.mul h2

end GlobalTheory.HSAmp
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem gram_det_up_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (ε : ℝ), 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re ≤ (chInt P.L D u.u / D.factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX hG P hL ω r f hf hli hr u ε hε
  have hcomp : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hcont : ∀ σ, Continuous (u.u σ) := fun σ =>
    continuous_iff_continuousAt.2 fun y => (u.cInf σ y).continuousAt
  have hT := GlobalTheory.T.tendsto_bergmanMeasure_chernForm_pow k X p D hX hG P hL ω r f hf hli hr u.u hcont
  have hev : ∀ᶠ m : ℕ in atTop, (∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      / (m : ℝ) ^ D < chInt P.L D u.u / D.factorial + ε :=
    hT (Iio_mem_nhds (by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  obtain ⟨hF, hPD, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  haveI : Finite (k →+* ℂ) := hF.finite
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  have hB : ∀ σ, ∃ C : ℝ, ∀ y, |u.u σ y| ≤ C := fun σ => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont σ).continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  choose C hC using hB
  set w : ∀ σ, CxPts p σ → ℝ := fun σ y => (((m : ℤ) : ℝ)) * u.u σ y with hw
  have hwm : ∀ σ, Measurable (w σ) := fun σ => (continuous_const.mul (hcont σ)).measurable
  have hwb : ∀ σ y, |w σ y| ≤ (m : ℝ) * ∑ τ, |C τ| := fun σ y => by
    simp only [hw, Int.cast_natCast, abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
    exact (hC σ y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun τ => |C τ|) (fun τ _ => abs_nonneg _) (Finset.mem_univ σ)))
  obtain ⟨-, -, hJ⟩ := GlobalTheory.T.gramDeterminant_jensen_change_of_weight (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m)) (fun σ => (ω σ).meas)
    (vals P m 1 (f m)) hF hPD w _ hwm hwb
  have hnew : (fun σ y i => vals P m 1 (f m) σ y i * ((Real.exp (-(w σ y) / 2) : ℝ) : ℂ))
      = vals (upperParabolic P u) m 1 (f m) := by
    funext σ y i
    simp only [vals, hw]
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y (f m i)).1]
  rw [hnew] at hJ
  have hsum : (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      = (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by
    rw [mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hw, Int.cast_natCast]
    ring
  rw [hsum] at hJ
  have hmpos : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast hm1) D
  rw [div_lt_iff₀ hmpos] at hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 := mul_le_mul_of_nonneg_left hm.le hm0
  calc _ ≤ (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by linarith
    _ ≤ _ := h2
    _ = _ := by ring

end GlobalTheory.HSAmp
end
end

section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.PolRangeD

open GlobalTheory.RealLift.PolRangePf

theorem tensD_top {ι : Type} [Fintype ι] [DecidableEq ι] {σ : ι → Type}
    (N : Submodule ℂ (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : MvPolynomial (σ w) ℂ)) ∈ N)
    (hX : ∀ (w : ι) (l : σ w), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial (σ w) ℂ)) T ∈ N) :
    N = ⊤ := by
  have key : ∀ s : Finset ι, ∀ f : ∀ w, MvPolynomial (σ w) ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun w => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial (σ w₀) ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : (∀ w : ι, MvPolynomial (σ w) ℂ) →ₘₗ[ℂ]
          (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial (σ w₀) ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ w₀), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [GlobalTheory.RealLift.atPl_tprod] at this
        simpa using this
      have htop := GlobalTheory.RealLift.mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

theorem tensD_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (N : Submodule ℂ (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w) c) T ∈ N) : N = ⊤ := by
  refine tensD_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

theorem sumPlD_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))
      = Complex.I • sumPl (fun w => heisOp (c w))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, GlobalTheory.RealLift.atPl_tprod, GlobalTheory.RealLift.heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

theorem polRangeD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (P Q R S : InfinitePlace F → ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm (P w) (Q w)) →
    (∀ w, W.θ w * C w = C w * Jm (R w) (S w)) → IsFockMapD ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hL := GlobalTheory.RealLift.actsLaws
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (e : ℂ),
      A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm (R w) (S w) * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ
          = e • ((A w * Jm (P w) (Q w)) * c * (Jm (R w) (S w) * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm (P w) (Q w) * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm (R w) (S w))) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPlD_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tensD_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update
          (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w')) T = atPl w (heisOp c) T := by
        rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
        · simp
        · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
        · simp
      have := pol_der u hu _ hT _ (der u hu _ hu' T)
      rwa [hs] at this
    have : T ∈ (M.Pol ψ τ).comap Φ := htop ▸ Submodule.mem_top
    exact this
  · unfold Model.Pol
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
    · obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := GlobalTheory.T.fock_vacuum_line_placewise_signatures F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end GlobalTheory.HoweD.PolRangeD

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.related_pairs_orbital_term_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Q Q' : DPair G), Q.Rel Q' → Q.pol = Q'.pol ∧ Q.c = Q'.c ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → Q.term Kf f r K φ = Q'.term Kf f r K φ := by
  first | exact @GlobalTheory.LKDef.DPair.rel_pol_c_term | exact GlobalTheory.LKDef.DPair.rel_pol_c_term | (intros; apply GlobalTheory.LKDef.DPair.rel_pol_c_term <;> assumption)
end
