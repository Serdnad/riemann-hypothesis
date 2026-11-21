import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.charsA
import Development.AutomorphicArithmetic.PrimitiveCosets.GmAEq
import Development.AutomorphicArithmetic.PrimitiveCosets.SigALe
import Development.AutomorphicArithmetic.PrimitiveCosets.hostFactsS
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/-- The final lower-order contribution can be absorbed into any positive power of `x`. -/
theorem UpperTheory.Comparison₂.core_gm_with_slack (δ : ℝ) (hδ : 0 < δ) :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * eps + δ) := by
  intro Λ eD eL K cHH eK C eps heps
  have ho : (0 : ℝ) ≤ Λ.o := Nat.cast_nonneg _
  have hc : |(3 * (Λ.o : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨x₁, hx₁⟩ := Deduction.ch_core (max (eD + eL) 0 + 3) eps C (koOf Λ) (3 * (Λ.o : ℝ) + 1)⁻¹ (4 * (Λ.o : ℝ))
    (by positivity) heps hc
  obtain ⟨x₂, hx₂⟩ := large_x_eventually eps K cHH eK heps
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop (1 + 4 * (Λ.o : ℝ)))
  refine ⟨max x₁ (max x₂ x₃), fun x hx φ H TT hE hCore => ?_⟩
  have g1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have g2 : x₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g3 : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨U0, i0, tr, W, i4, i5, Top, i6, m, f, Dd, Cc, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ,
    hell, hxx, hε, heD, heL, hcHH, hcov, hId, hLed, hWin, hBN, hSz, hThin, hCost, hRest, hT2⟩ := hCore
  subst hxx hε
  have hLX := hx₂ _ g2
  have hWin' := hWin
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC
  have hLX' : LargeX Dd.x Dd.ε K Cc.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)
  have hb : 0 < Dd.b := by linarith
  have hx0 : 0 < Dd.x := by linarith
  have hk : 0 < Dd.k := by linarith
  have ha : 0 ≤ Dd.a := le_trans (by positivity) w5
  have hE0 : 0 ≤ eD + eL := by linarith
  rw [max_eq_left hE0] at hx₁
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card φ.A) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  have hExp : Dd.x ^ (CErr Cc * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε) := by
    refine Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)
    unfold CErr
    linarith
  have hmain := hx₁ _ g1 φ.A m (arith H.toHostRaw) _ ell N TT T2 a w Dd.b Dd.b' Dd.k Dd.a η X' θ φ.A0
    (keptA Λ H.toHostRaw) (hostFactsS φ H) hb ha hk w7 w8 hSz hThin hCost hRest hT2
    (charsA Λ φ H TT _ _ C ell hx0 hE hell) (fun u hu => by
      obtain ⟨v, rfl⟩ := hcov u hu
      exact le_trans (Deduction.ch_top Dd tr Cc Xpp eK K _ ell N TT T2 a w eT eP hId hLed hWin hBN hLX' v)
        (mul_le_mul_of_nonneg_right hExp hBr))
  rw [gmA_eq Λ φ H TT _ _ C ell hE hell] at hmain
  have hs := sigA_le Λ φ H TT _ _ C ell hx0 hE hell
  let β : ℝ := 1 / 2 + (eD + eL + 3 + 3) * Dd.ε
  have hErr : Dd.x ^ ((1 : ℝ) / 2 + Dd.ε) ≤ Dd.x ^ β :=
    Real.rpow_le_rpow_of_exponent_le w1 (by dsimp [β]; nlinarith)
  calc
    Λ.Gm Dd.x ≤ Dd.x ^ β + 4 * (Λ.o : ℝ) * Dd.x ^ β :=
      hmain.trans (add_le_add le_rfl (hs.trans (mul_le_mul_of_nonneg_left hErr (by positivity))))
    _ = (1 + 4 * (Λ.o : ℝ)) * Dd.x ^ β := by ring
    _ ≤ Dd.x ^ δ * Dd.x ^ β :=
      mul_le_mul_of_nonneg_right (hx₃ _ g3) (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; dsimp [β]; ring

theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
  intro Λ eD eL K cHH eK C eps heps
  simpa only [show (1 : ℝ) / 2 + (eD + eL + 6) * eps + eps =
    1 / 2 + (eD + eL + 7) * eps by ring] using
    UpperTheory.Comparison₂.core_gm_with_slack eps heps Λ eD eL K cHH eK C eps heps

/-- A large point in the window only needs one host to supply both pointwise bounds. -/
theorem UpperTheory.Comparison₂.window_bound_of_pointwise_hosts {Λ : Level} {S : Set ℝ}
    {x0 eD eL K cHH eK C eps : ℝ} (heps : 0 < eps)
    (hosts : ∀ x ≥ x0, x ∈ S → ∃ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C ∧ CoreAtH H.toHostRaw TT eD eL K cHH eK eps x) :
    ∃ x1 : ℝ, ∀ x ≥ x1, x ∈ S → Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
  obtain ⟨y, bound⟩ := UpperTheory.Comparison₂.core_gm Λ eD eL K cHH eK C eps heps
  refine ⟨max x0 y, fun x hx hw => ?_⟩
  obtain ⟨φ, H, TT, hE, hCore⟩ := hosts x (le_of_max_le_left hx) hw
  exact bound x (le_of_max_le_right hx) φ H TT hE hCore
