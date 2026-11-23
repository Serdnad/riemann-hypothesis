module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle018
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Algebra.Polynomial
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimitiveFormSheetedPointsNear.exists_root (n : ℕ) (hn : n ≠ 0) (c : Fin n → ℂ) :
    ∃ τ : ℂ, τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0 := by
  set p : Polynomial ℂ := Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hp
  have hlt : (∑ j : Fin n, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).degree < (Polynomial.X ^ n : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j _ => ?_
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 j.isLt)
  have hdeg : p.degree = n := by
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  obtain ⟨τ, hτ⟩ := Complex.exists_root (f := p) (by rw [hdeg]; exact_mod_cast Nat.pos_of_ne_zero hn)
  exact ⟨τ, by simpa [p, Polynomial.eval_finsetSum] using hτ⟩

theorem PrimitiveFormSheetedPointsNear.derivative_ne_zero (n : ℕ) (c : Fin n → ℂ) (τ : ℂ)
    (hs : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hτ : τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0) :
    (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 := by
  have h0 : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).eval τ = 0 := by
    simpa [Polynomial.eval_finsetSum] using hτ
  exact hs.eval₂_derivative_ne_zero (RingHom.id ℂ) h0

theorem PrimitiveFormSheetedPointsNear.proof (hmin : PrimitiveFormMinimalFactorPoints.Statement)
    (hbr : AnalyticSimpleRootBranch.Statement) : PrimitiveFormSheetedPointsNear.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel U hU
  obtain ⟨n, b, hb, hm, hsepm, hpts⟩ :=
    hmin σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel
  have hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (z ∈ X → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) := by
    filter_upwards [hU, hP, eventually_all.2 hrel] with z h1 h2 h3 using ⟨h1, h2, fun hz i => h3 i hz⟩
  obtain ⟨U₁, hU₁sub, hU₁o, hwU₁⟩ := mem_nhds_iff.1 hgood
  have hn : n ≠ 0 := by
    rintro rfl
    simpa using hm.self_of_nhds hirr.1
  have hE : ∀ᶠ y in 𝓝 (A w), (δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
        (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U₁ ∧
          A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
          ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ) ∧
      (δ y ≠ 0 → (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (δ y ≠ 0 → (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (∀ j, AnalyticAt ℂ (a j) y) ∧ (∀ j, AnalyticAt ℂ (b j) y) ∧ AnalyticAt ℂ δ y ∧
      (∀ i j, AnalyticAt ℂ (q i j) y) := by
    filter_upwards [hpts U₁ (hU₁o.mem_nhds hwU₁), hsepm, hsepP,
      eventually_all.2 fun j => (ha j).eventually_analyticAt, eventually_all.2 fun j => (hb j).eventually_analyticAt,
      hδ.eventually_analyticAt, eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt]
      with y h1 h2 h3 h4 h5 h6 h7 using ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨y, hyE, hyδ⟩ := (hE.eventually_nhds.and_frequently (not_eventually.1 hδ0)).exists
  obtain ⟨E, hEsub, hEo, hyE⟩ := mem_nhds_iff.1 hyE
  obtain ⟨hptsy, hsepmy, hsepPy, hay, hby, -, -⟩ := hEsub hyE
  obtain ⟨τ, hτ⟩ := PrimitiveFormSheetedPointsNear.exists_root n hn (fun j => b j y)
  obtain ⟨⟨hzX, hzU₁⟩, hAz, hℓz⟩ := hptsy hyδ τ hτ
  set z : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hz
  have hPτ : τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 := by
    simpa [hAz, hℓz] using (hU₁sub hzU₁).2.1 hzX
  obtain ⟨OP, BP, ψP, hOPo, hyOP, hBPo, hτBP, -, -, hψP⟩ :=
    hbr d N a y τ hay hPτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero N (fun j => a j y) τ (hsepPy hyδ) hPτ)
  obtain ⟨Om, Bm, ψm, hOmo, hyOm, -, -, hψman, hψmy, hψm⟩ :=
    hbr d n b y τ hby hτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero n (fun j => b j y) τ (hsepmy hyδ) hτ)
  have hδc : ContinuousOn δ E := fun t ht => (hEsub ht).2.2.2.2.2.1.continuousAt.continuousWithinAt
  set O : Set (Fin d → ℂ) := (Om ∩ ψm ⁻¹' BP) ∩ OP ∩ (E ∩ δ ⁻¹' {0}ᶜ) with hO
  have hOo : IsOpen O := ((hψman.continuousOn.isOpen_inter_preimage hOmo hBPo).inter hOPo).inter
    (hδc.isOpen_inter_preimage hEo isOpen_compl_singleton)
  set g : (Fin d → ℂ) → σ → ℂ := fun t i => (∑ j, q i j t * ψm t ^ (j : ℕ)) / δ t with hg
  have key : ∀ t ∈ O, g t ∈ X ∩ U₁ ∧ A (g t) = t ∧ ℓ (g t) = ψm t := fun t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩ =>
    (hEsub htE).1 htδ (ψm t) (((hψm t htm).2 (ψm t) (hψm t htm).1).2 rfl)
  have hPψ : ∀ t ∈ O, ψm t = ψP t := fun t ht => by
    obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
    have h := (hU₁sub hgU).2.1 hgX
    rw [hgA, hgℓ] at h
    exact ((hψP t ht.1.2).2 (ψm t) ht.1.1.2).1 h
  set V : Set (σ → ℂ) := U₁ ∩ A ⁻¹' O ∩ ℓ ⁻¹' BP with hV
  refine ⟨z, ⟨hzX, (hU₁sub hzU₁).1⟩, by rw [hAz]; exact hyδ, O, V, g, hOo,
    (hU₁o.inter (hOo.preimage A.continuous)).inter (hBPo.preimage ℓ.continuous),
    ⟨⟨hzU₁, by rw [Set.mem_preimage, hAz]; exact ⟨⟨⟨hyOm, by rw [Set.mem_preimage, hψmy]; exact hτBP⟩, hyOP⟩, hyE, hyδ⟩⟩,
      by rw [Set.mem_preimage, hℓz]; exact hτBP⟩, ?_, fun t ht => (key t ht).2.1, ?_⟩
  · rintro t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩
    obtain ⟨-, -, -, -, -, -, hqt⟩ := hEsub htE
    have hδt : AnalyticAt ℂ δ t := (hEsub htE).2.2.2.2.2.1
    refine AnalyticAt.pi fun i => AnalyticAt.fun_div ?_ hδt htδ
    exact Finset.analyticAt_fun_sum _ fun j _ => (hqt i j).mul ((hψman t htm).pow _)
  · ext z'
    constructor
    · rintro ⟨hz'X, ⟨hz'U, hz'O⟩, hz'B⟩
      refine ⟨A z', hz'O, ?_⟩
      have hs : ℓ z' = ψm (A z') := by
        rw [hPψ _ hz'O]; exact ((hψP _ hz'O.1.2).2 _ hz'B).1 ((hU₁sub hz'U).2.1 hz'X)
      have hδt : δ (A z') ≠ 0 := hz'O.2.2
      funext i
      rw [hg, div_eq_iff hδt, ← hs, ← (hU₁sub hz'U).2.2 hz'X i, mul_comm]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
      exact ⟨hgX, ⟨hgU, by rw [Set.mem_preimage, hgA]; exact ht⟩, by rw [Set.mem_preimage, hgℓ]; exact ht.1.1.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

theorem polynomial_dvd_of_eval_eq_mul_near_roots {U : Set ℂ} (hU : IsOpen U) :
    ∀ (n : ℕ) (W P : ℂ[X]) (g : ℂ → ℂ), W.Monic → W.natDegree = n → ContinuousOn g U →
      (∀ t ∈ U, P.eval t = g t * W.eval t) → (∀ t, W.IsRoot t → t ∈ U) → W ∣ P := by
  intro n
  induction n with
  | zero =>
    intro W P g hW hn _ _ _
    rw [hW.natDegree_eq_zero.1 hn]
    exact one_dvd P
  | succ n ih =>
    intro W P g hW hn hg hPW hroots
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root W (by
      rw [degree_eq_natDegree hW.ne_zero, hn]; exact_mod_cast Nat.succ_ne_zero n)
    have hαU : α ∈ U := hroots α hα
    have hPα : P.IsRoot α := by
      show P.eval α = 0
      rw [hPW α hαU, show W.eval α = 0 from hα, mul_zero]
    have hW₁ : (X - C α) * (W /ₘ (X - C α)) = W := mul_divByMonic_eq_iff_isRoot.2 hα
    have hP₁ : (X - C α) * (P /ₘ (X - C α)) = P := mul_divByMonic_eq_iff_isRoot.2 hPα
    have hW₁m : (W /ₘ (X - C α)).Monic := (monic_X_sub_C α).of_mul_monic_left (by rw [hW₁]; exact hW)
    have hW₁n : (W /ₘ (X - C α)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C α), hn, natDegree_X_sub_C]; rfl
    have hcont : ContinuousOn (fun t => g t * (W /ₘ (X - C α)).eval t) U :=
      hg.mul (W /ₘ (X - C α)).continuous.continuousOn
    have hoff : ∀ s ∈ U, s ≠ α → (P /ₘ (X - C α)).eval s = g s * (W /ₘ (X - C α)).eval s := by
      intro s hsU hs
      have h := hPW s hsU
      rw [← hP₁, ← hW₁, eval_mul, eval_mul] at h
      have hne : (X - C α).eval s ≠ 0 := by
        simp only [eval_sub, eval_X, eval_C]; exact sub_ne_zero.2 hs
      exact mul_left_cancel₀ hne (by rw [h]; ring)
    have hP₁eq : ∀ t ∈ U, (P /ₘ (X - C α)).eval t = g t * (W /ₘ (X - C α)).eval t := by
      intro t ht
      by_cases htα : t = α
      · have h1 : Tendsto (fun s => (P /ₘ (X - C α)).eval s) (𝓝[≠] t) (𝓝 ((P /ₘ (X - C α)).eval t)) :=
          (P /ₘ (X - C α)).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun s => g s * (W /ₘ (X - C α)).eval s) (𝓝[≠] t)
            (𝓝 (g t * (W /ₘ (X - C α)).eval t)) :=
          (hcont.continuousAt (hU.mem_nhds ht)).tendsto.mono_left nhdsWithin_le_nhds
        refine tendsto_nhds_unique (h1.congr' ?_) h2
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds ht)] with s hs hsU
        exact hoff s hsU (htα ▸ hs)
      · exact hoff t ht htα
    have hdvd := ih _ _ g hW₁m hW₁n hg hP₁eq (fun t ht => hroots t (by
      rw [← hW₁]; show ((X - C α) * (W /ₘ (X - C α))).eval t = 0
      rw [eval_mul, show (W /ₘ (X - C α)).eval t = 0 from ht, mul_zero]))
    rw [← hW₁, ← hP₁]
    exact mul_dvd_mul_left _ hdvd

theorem norm_lt_of_monic_root_small_coeffs {d : ℕ} (b : Fin d → ℂ) {r η : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hη : (d : ℝ) * η < r ^ d) (hb : ∀ j, ‖b j‖ ≤ η) (t : ℂ)
    (ht : t ^ d + ∑ j : Fin d, b j * t ^ (j : ℕ) = 0) : ‖t‖ < r := by
  by_contra h
  push Not at h
  have hT : 0 < ‖t‖ ^ d := pow_pos (lt_of_lt_of_le hr0 h) d
  have hR : 0 < r ^ d := pow_pos hr0 d
  have htd : t ^ d = -∑ j : Fin d, b j * t ^ (j : ℕ) := eq_neg_of_add_eq_zero_left ht
  have hsum : ‖t‖ ^ d ≤ ∑ _j : Fin d, η * (‖t‖ ^ d / r ^ d) := by
    calc ‖t‖ ^ d = ‖t ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ j : Fin d, b j * t ^ (j : ℕ)‖ := by rw [htd, norm_neg]
      _ ≤ ∑ j : Fin d, ‖b j * t ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul, norm_pow]
          refine mul_le_mul (hb j) ?_ (by positivity) (le_trans (norm_nonneg _) (hb j))
          rw [le_div_iff₀ hR]
          calc ‖t‖ ^ (j : ℕ) * r ^ d ≤ ‖t‖ ^ (j : ℕ) * r ^ (d - j) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1 (Nat.sub_le d j)) (by positivity)
            _ ≤ ‖t‖ ^ (j : ℕ) * ‖t‖ ^ (d - j) := by gcongr
            _ = ‖t‖ ^ d := by rw [← pow_add, Nat.add_sub_cancel' j.2.le]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hlt : (d : ℝ) * (η * (‖t‖ ^ d / r ^ d)) < ‖t‖ ^ d := by
    rw [show (d : ℝ) * (η * (‖t‖ ^ d / r ^ d)) = ((d : ℝ) * η / r ^ d) * ‖t‖ ^ d by ring]
    exact mul_lt_of_lt_one_left hT ((div_lt_one hR).2 hη)
  linarith

theorem continuous_pointWithLast {σ : Type} (z : σ → ℂ) : Continuous (fun t : ℂ => pointWithLast z t) := by
  refine continuous_pi fun o => ?_
  cases o with
  | none => exact continuous_id
  | some i => exact continuous_const

theorem weierstrass_remainder_eq_zero {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, ContinuousAt (c j) 0) (hc0 : ∀ j, c j 0 = 0) (a : Fin d → (σ → ℂ) → ℂ)
    (q : (Option σ → ℂ) → ℂ) (hq : AnalyticAt ℂ q 0)
    (h : ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
      ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ) = q x * weierstrassPolynomial c x) :
    ∀ j, ∀ᶠ z in 𝓝 (0 : σ → ℂ), a j z = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and hq.eventually_analyticAt)
  have hr0 : 0 < min ε 1 := lt_min hε one_pos
  have hrε : min ε 1 ≤ ε := min_le_left _ _
  have hR : 0 < (min ε 1) ^ d := pow_pos hr0 d
  have hηpos : 0 < (min ε 1) ^ d / (d + 1) := by positivity
  have hη : (d : ℝ) * ((min ε 1) ^ d / (d + 1)) < (min ε 1) ^ d := by
    rw [show (d : ℝ) * ((min ε 1) ^ d / (d + 1)) = (min ε 1) ^ d * (d / (d + 1)) by ring]
    exact mul_lt_of_lt_one_right hR ((div_lt_one (by positivity)).2 (by linarith))
  have hsmall : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ‖z‖ < min ε 1 ∧ ∀ j, ‖c j z‖ ≤ (min ε 1) ^ d / (d + 1) := by
    refine ((continuous_norm.tendsto' (0 : σ → ℂ) 0 norm_zero).eventually (eventually_lt_nhds hr0)).and
      (Filter.eventually_all.2 fun j => ?_)
    have ht : Tendsto (fun z => ‖c j z‖) (𝓝 (0 : σ → ℂ)) (𝓝 0) := by
      simpa [hc0 j] using (hc j).norm.tendsto
    exact (ht.eventually (eventually_lt_nhds hηpos)).mono fun z hz => hz.le
  intro j
  filter_upwards [hsmall] with z hz
  obtain ⟨hzr, hcz⟩ := hz
  have hpt : ∀ t : ℂ, ‖t‖ < min ε 1 → pointWithLast z t ∈ Metric.ball (0 : Option σ → ℂ) ε := by
    intro t ht
    rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
    intro o
    cases o with
    | none => exact lt_of_lt_of_le ht hrε
    | some i => exact lt_of_le_of_lt (norm_le_pi_norm z i) (lt_of_lt_of_le hzr hrε)
  have hdeg : (∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) := degree_sum_fin_lt _
  have hWm : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).Monic := monic_X_pow_add hdeg
  have hWn : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).natDegree = d := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hevW : ∀ t : ℂ, (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).eval t =
      weierstrassPolynomial c (pointWithLast z t) := by
    intro t
    simp only [eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum, eval_mul, eval_C, weierstrassPolynomial]
    rfl
  have hevP : ∀ t : ℂ, (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)).eval t =
      ∑ i : Fin d, a i (fun k => pointWithLast z t (some k)) * pointWithLast z t none ^ (i : ℕ) := by
    intro t
    simp only [Polynomial.eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rfl
  have hdvd := polynomial_dvd_of_eval_eq_mul_near_roots (Metric.isOpen_ball (x := (0 : ℂ)) (ε := min ε 1)) d
    _ (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)) (fun t => q (pointWithLast z t)) hWm hWn
    (fun t ht => ((hball _ (hpt t (mem_ball_zero_iff.1 ht))).2.continuousAt.comp
      (continuous_pointWithLast z).continuousAt).continuousWithinAt)
    (fun t ht => by
      rw [hevP, hevW]
      exact (hball _ (hpt t (mem_ball_zero_iff.1 ht))).1)
    (fun t ht => by
      rw [mem_ball_zero_iff]
      refine norm_lt_of_monic_root_small_coeffs (fun i => c i z) hr0 (min_le_right _ _) hη hcz t ?_
      have h0 : (X ^ d + ∑ i : Fin d, C (c i z) * X ^ (i : ℕ)).eval t = 0 := ht
      simpa only [eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum, eval_mul, eval_C] using h0)
  have hP0 : (∑ i : Fin d, C (a i z) * X ^ (i : ℕ)) = 0 :=
    eq_zero_of_dvd_of_degree_lt hdvd (by rw [degree_eq_natDegree hWm.ne_zero, hWn]; exact degree_sum_fin_lt _)
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (j : ℕ)) hP0
  simpa [Polynomial.finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using hcoeff

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

theorem monic_root_branch_eventuallyEq {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (s : Fin d → ℂ)
    (u v : (Fin d → ℂ) → ℂ) (ha : ∀ j, ContinuousAt (a j) s) (hu : ContinuousAt u s)
    (hv : ContinuousAt v s) (huv : u s = v s)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hru : ∀ᶠ t in 𝓝 s, u t ^ N + ∑ j, a j t * u t ^ (j : ℕ) = 0)
    (hrv : ∀ᶠ t in 𝓝 s, v t ^ N + ∑ j, a j t * v t ^ (j : ℕ) = 0) : u =ᶠ[𝓝 s] v := by
  set Q : (Fin d → ℂ) → ℂ → ℂ → ℂ := fun t x y =>
    ∑ i ∈ Finset.range N, x ^ i * y ^ (N - 1 - i) +
      ∑ j : Fin N, a j t * ∑ i ∈ Finset.range j, x ^ i * y ^ ((j : ℕ) - 1 - i) with hQdef
  have hQ : ∀ t x y, (x ^ N + ∑ j, a j t * x ^ (j : ℕ)) - (y ^ N + ∑ j, a j t * y ^ (j : ℕ)) =
      Q t x y * (x - y) := by
    intro t x y
    rw [hQdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hQs : Q s (u s) (u s) ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := u s)
      (by simpa [Polynomial.eval₂_id, Polynomial.eval_finsetSum] using hru.self_of_nhds)
    convert h using 1
    simp [hQdef, Polynomial.eval₂_id, Polynomial.eval_finsetSum, geom_sum₂_self, Polynomial.derivative_X_pow]
  have hc : ContinuousAt (fun t => Q t (u t) (v t)) s := by
    simp only [hQdef]
    fun_prop
  have hne : ∀ᶠ t in 𝓝 s, Q t (u t) (v t) ≠ 0 := hc.eventually_ne (by rw [← huv]; exact hQs)
  filter_upwards [hru, hrv, hne] with t h1 h2 h3
  have h := hQ t (u t) (v t)
  rw [h1, h2, sub_self] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left h3)

theorem PrimitiveFormFullBranchConstant.proof : PrimitiveFormFullBranchConstant.Statement := by
  intro σ _ X W N' k f d A ℓ N a δ q B O r hW hN' hWN' hf hXN' hXW hP hB ha hδ hq hO hOc hOB hδO hsep hr hrO
  set G : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hGdef
  set P : (Fin d → ℂ) → Prop := fun u => G u ∈ X ∩ W ∧ A (G u) = u ∧ ℓ (G u) = r u with hPdef
  have hG : AnalyticOnNhd ℂ G O := fun u hu => analyticAt_pi_iff.2 fun i =>
    (Finset.analyticAt_fun_sum _ fun j _ => (hq i j u (hOB hu)).mul ((hr u hu).pow _)).div
      (hδ u (hOB hu)) (hδO u hu)

  have hfull : ∀ s ∈ O, (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ ∀ᶠ u in 𝓝 s, P u) := by
    intro s hs
    constructor
    · rintro ⟨O', r', hO', hsO', hr', hrs, hw⟩
      have hroot' : ∀ᶠ u in 𝓝 s, r' u ^ N + ∑ j, a j u * r' u ^ (j : ℕ) = 0 := by
        filter_upwards [hO'.mem_nhds hsO'] with u hu
        obtain ⟨hX, hA, hℓ⟩ := hw u hu
        have h := hP _ hX
        rwa [hA, hℓ] at h
      have heq : r' =ᶠ[𝓝 s] r := monic_root_branch_eventuallyEq a s r' r
        (fun j => (ha j s (hOB hs)).continuousAt) (hr' s hsO').continuousAt (hr s hs).continuousAt hrs
        (hsep s hs) hroot' (Filter.mem_of_superset (hO.mem_nhds hs) hrO)
      filter_upwards [hO'.mem_nhds hsO', heq] with u hu hru
      have h := hw u hu
      simp only [hru] at h
      exact h
    · intro hev
      obtain ⟨U, hUs, hUo, hsU⟩ := mem_nhds_iff.1 hev
      exact ⟨U ∩ O, r, hUo.inter hO, ⟨hsU, hs⟩, hr.mono Set.inter_subset_right, rfl, fun u hu => hUs hu.1⟩

  set S : Set (Fin d → ℂ) := {s | ∀ᶠ u in 𝓝 s, P u} with hSdef
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : closure S ∩ O ⊆ S := by
    rintro s ⟨hsc, hs⟩
    have hGs : ContinuousAt G s := (hG s hs).continuousAt
    have hGW : G s ∈ closure W := closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hu.self_of_nhds.1.2)
      (mem_closure_image hGs hsc)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      (Filter.inter_mem (hO.mem_nhds hs) (hGs.preimage_mem_nhds (hN'.mem_nhds (hWN' hGW))))

    set Φ : (Fin d → ℂ) → (Fin k → ℂ) × (Fin d → ℂ) × ℂ :=
      fun u => (fun i => f i (G u), A (G u) - u, ℓ (G u) - r u) with hΦdef
    have hΦ : AnalyticOnNhd ℂ Φ (Metric.ball s ε) := fun u hu => by
      have hu' := hball hu
      exact (analyticAt_pi_iff.2 fun i => (hf i _ hu'.2).comp (hG u hu'.1)).prod
        ((((A.analyticAt _).comp (hG u hu'.1)).sub analyticAt_id).prod
          (((ℓ.analyticAt _).comp (hG u hu'.1)).sub (hr u hu'.1)))
    obtain ⟨u₀, hu₀U, hu₀S⟩ := mem_closure_iff.1 hsc _ Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hΦ0 : Set.EqOn Φ 0 (Metric.ball s ε) :=
      hΦ.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball s ε).isPreconnected hu₀U (by
        filter_upwards [hu₀S] with u hu
        obtain ⟨⟨hX, hWu⟩, hA, hℓ⟩ := hu
        have hXN : G u ∈ X ∩ N' := ⟨hX, hWN' (subset_closure hWu)⟩
        rw [hXN'] at hXN
        simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, hA, hℓ, sub_self, and_true]
        exact funext fun i => hXN.2 i)
    have hU : ∀ u ∈ Metric.ball s ε, G u ∈ X ∧ A (G u) = u ∧ ℓ (G u) = r u := by
      intro u hu
      have h := hΦ0 hu
      simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, sub_eq_zero] at h
      refine ⟨?_, h.2.1, h.2.2⟩
      have hXN : G u ∈ X ∩ N' := by rw [hXN']; exact ⟨(hball hu).2, fun i => congr_fun h.1 i⟩
      exact hXN.1
    obtain ⟨hXs, hAs, -⟩ := hU s (Metric.mem_ball_self hε)
    have hGsW : G s ∈ W := hXW _ ⟨hXs, hGW⟩ (by rw [hAs]; exact hOB hs)
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε),
      hGs.preimage_mem_nhds (hW.mem_nhds hGsW)] with u hu hu'
    obtain ⟨h1, h2, h3⟩ := hU u hu
    exact ⟨⟨h1, hu'⟩, h2, h3⟩

  have key : ∀ s ∈ O, ∀ s' ∈ O, PrimitiveFormRootFull X W A ℓ δ q s (r s) →
      PrimitiveFormRootFull X W A ℓ δ q s' (r s') := by
    intro s hs s' hs' h
    have hsub : O ⊆ S := hOc.subset_of_closure_inter_subset hSo ⟨s, hs, (hfull s hs).1 h⟩ hSc
    exact (hfull s' hs').2 (hsub hs')
  intro s hs s' hs'
  exact ⟨key s hs s' hs', key s' hs' s hs⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

theorem nonempty_normalModel_of_presentation {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type)
    [CommRing R] [IsDomain R] [Algebra ℂ R] (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J) : Nonempty (NormalModel J) :=
  _root_.UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation J R π hπ hker

theorem NormalModelExists.proof : NormalModelExists.Statement := by
  intro n J hJ
  exact nonempty_normalModel_of_presentation J (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mkₐ ℂ J)
    (Ideal.Quotient.mkₐ_surjective ℂ J) (Ideal.Quotient.mkₐ_ker ℂ J)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsIntegrallyClosed.Statement : Prop :=
  ∀ (d : ℕ) (y : Fin d → ℂ), IsDomain (holGerms y) ∧ IsIntegrallyClosed (holGerms y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
