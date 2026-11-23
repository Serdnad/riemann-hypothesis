module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003

@[expose] public section

section

namespace GlobalTheory.FlatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hf_pos (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < hf X ξ x τ := by
  unfold hf
  refine mul_pos (IsotropicThreshold.c_pos X τ) (X.maj_pos hx τ ?_)
  intro h0
  apply hξ
  funext a
  have h1 := congrFun h0 a
  simpa [Data.emb] using h1

theorem guard_iff (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    hf X ξ x τ ≤ 1 ↔ 1 ≤ X.tt ξ x τ := by
  rw [tt_eq X ξ x τ, one_le_div (hf_pos X hξ hx τ)]

theorem logTerm_nonneg (X : Data E r) (x : Frame X.Ψ r) : 0 ≤ Real.log (1 + 1 / X.la1 x) := by
  apply Real.log_nonneg
  have h1 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  linarith

theorem exists_short (X : Data E r) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, 0 < X.firstMinimumSq x → X.firstMinimumSq x < ε →
    ∃ v, X.IsIso v ∧ (∀ τ, 1 ≤ X.tt v x τ) ∧ ∀ τ, 1 / (2 * X.firstMinimumSq x) ≤ X.tt v x τ := by
  obtain ⟨δ0, hδ0, hiso⟩ := IsotropicThreshold.iso_threshold X
  refine ⟨min (δ0 / 2) (1 / 2), lt_min (by linarith) (by norm_num), fun x hx hpos hsmall => ?_⟩
  have hmin1 := min_le_left (δ0 / 2) (1 / 2)
  have hmin2 := min_le_right (δ0 / 2) (1 / 2)
  have hne : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : X.firstMinimumSq x = 0 := by rw [Data.firstMinimumSq, hemp, Real.sInf_empty]
    linarith
  obtain ⟨t, ⟨v, hvΛ, hv0, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt hne (show X.firstMinimumSq x < 2 * X.firstMinimumSq x by linarith)
  have hsum_lt : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 := by linarith
  have hherm := hiso x hx v hvΛ hsum_lt
  have hterm : ∀ τ, hf X v x τ ≤ ∑ τ', X.c τ' * X.maj x τ' (Data.emb τ'.1 v) := fun τ =>
    Finset.single_le_sum (f := fun τ' => X.c τ' * X.maj x τ' (Data.emb τ'.1 v))
      (fun τ' _ => (hf_pos X hv0 hx τ').le) (Finset.mem_univ τ)
  refine ⟨v, ⟨hvΛ, hherm, hv0⟩, fun τ => ?_, fun τ => ?_⟩
  · rw [← guard_iff X hv0 hx τ]
    linarith [hterm τ]
  · rw [tt_eq X v x τ]
    exact one_div_le_one_div_of_le (hf_pos X hv0 hx τ) (by linarith [hterm τ])

theorem bdd_add_log (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) (ha : 0 < a)
    (K : ℝ) : ∃ B : ℝ, ∀ x ∈ X.dom, ps x + K * Real.log (1 + 1 / X.la1 x) ≤ B := by
  obtain ⟨⟨C1, A1, h1⟩, h2⟩ := h
  obtain ⟨C2, A2, h2'⟩ := h2 (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨ε, hε, hshort⟩ := exists_short X
  have hM : 0 ≤ |A1| + |K| + |A2| := by positivity
  have hpa : 0 < 8 * Real.pi * a := by positivity
  refine ⟨max (C1 + (|A1| + |K| + |A2|) / Real.sqrt ε)
    (C2 + (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a)), fun x hx => ?_⟩
  have hL0 := logTerm_nonneg X x
  have hy0 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hLy : Real.log (1 + 1 / X.la1 x) ≤ 1 / X.la1 x := by
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / X.la1 x by linarith)
    linarith
  have hK := mul_le_mul_of_nonneg_right (le_abs_self K) hL0
  have hA1 := mul_le_mul_of_nonneg_right (le_abs_self A1) hL0
  have hA2 := mul_le_mul_of_nonneg_right (le_abs_self A2) hL0
  have hA1' := mul_nonneg (abs_nonneg A1) hL0
  have hA2' := mul_nonneg (abs_nonneg A2) hL0
  by_cases hs : 0 < X.firstMinimumSq x ∧ X.firstMinimumSq x < ε
  · obtain ⟨v, hv, hv1, hv2⟩ := hshort x hx hs.1 hs.2
    have hb := h2' x hx v hv hv1
    have := nonempty_cmType X
    have hinf : 1 / (2 * X.firstMinimumSq x) ≤ ⨅ τ, X.tt v x τ := le_ciInf hv2
    have hla : X.la1 x ^ 2 = X.firstMinimumSq x := Real.sq_sqrt hs.1.le
    have hyy : 1 / (2 * X.firstMinimumSq x) = (1 / X.la1 x) ^ 2 / 2 := by
      rw [div_pow, one_pow, hla]; ring
    rw [hyy] at hinf
    have hcoef : (0 : ℝ) ≤ 8 * Real.pi * (1 - 2 * (1 / 4)) * a := by nlinarith [Real.pi_pos]
    have hI := mul_le_mul_of_nonneg_left hinf hcoef
    have hMy := mul_le_mul_of_nonneg_left hLy hM
    have hq : (|A1| + |K| + |A2|) * (1 / X.la1 x) - 2 * Real.pi * a * (1 / X.la1 x) ^ 2 ≤
        (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a) := by
      rw [le_div_iff₀ hpa]
      nlinarith [sq_nonneg (4 * Real.pi * a * (1 / X.la1 x) - (|A1| + |K| + |A2|))]
    refine le_trans ?_ (le_max_right _ _)
    linarith
  · have hLe : Real.log (1 + 1 / X.la1 x) ≤ 1 / Real.sqrt ε := by
      rcases le_or_gt (X.firstMinimumSq x) 0 with h0 | h0
      · have hz : X.la1 x = 0 := Real.sqrt_eq_zero'.2 h0
        rw [hz, div_zero, add_zero, Real.log_one]
        positivity
      · have hge : ε ≤ X.firstMinimumSq x := by
          by_contra hlt
          exact hs ⟨h0, not_le.1 hlt⟩
        exact hLy.trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 hε) (Real.sqrt_le_sqrt hge))
    have hb := h1 x hx
    have hMe := mul_le_mul_of_nonneg_left hLe hM
    have he : (|A1| + |K| + |A2|) * (1 / Real.sqrt ε) = (|A1| + |K| + |A2|) / Real.sqrt ε := by ring
    refine le_trans ?_ (le_max_left _ _)
    linarith

theorem cfwM_of_extraBounds (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : ExtraBounds X ps a) :
    cfwM X ps a := by
  obtain ⟨A, h1, C, h2⟩ := h
  refine ⟨⟨C, A, h2⟩, fun η hη _ => ?_⟩
  obtain ⟨C', hC'⟩ := h1 η hη
  exact ⟨C', A, fun x hx ξ hξ htt => hC' x hx ξ hξ fun τ => (guard_iff X hξ.2.2 hx τ).2 (htt τ)⟩

theorem extraBounds_of_cfwM (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : cfwM X ps a) : ExtraBounds X ps a := by
  rcases ha.eq_or_lt with ha0 | hapos
  · subst ha0
    obtain ⟨⟨C, A, hC⟩, -⟩ := h
    refine ⟨A, fun η _ => ⟨C, fun x hx ξ _ _ => ?_⟩, C, hC⟩
    have h1 := hC x hx
    simp only [mul_zero, zero_mul, sub_zero]
    exact h1
  · obtain ⟨B0, hB0⟩ := bdd_add_log X h hapos 0
    have := nonempty_cmType X
    refine ⟨0, fun η hη => ?_, B0, fun x hx => by linarith [hB0 x hx]⟩
    rcases lt_or_ge η (1 / 2) with hη2 | hη2
    · obtain ⟨C', A', hC'⟩ := h.2 (η / 2) (by linarith) (by linarith)
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - 2 * η) / (1 - η) := ⟨_, rfl⟩
      have h1η : 0 < 1 - η := by linarith
      have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) h1η
      have hθ1 : θ < 1 := by rw [hθ, div_lt_one h1η]; linarith
      have hθη : θ * (1 - η) = 1 - 2 * η := by rw [hθ]; field_simp
      obtain ⟨K, hK⟩ : ∃ K : ℝ, (1 - θ) * K = θ * |A'| :=
        ⟨θ * |A'| / (1 - θ), by field_simp [(sub_pos.2 hθ1).ne']⟩
      obtain ⟨BK, hBK⟩ := bdd_add_log X h hapos K
      refine ⟨θ * C' + (1 - θ) * BK, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hL0 := logTerm_nonneg X x
      have e1 := mul_le_mul_of_nonneg_left (hC' x hx ξ hξ htt) hθ0.le
      have e2 := mul_le_mul_of_nonneg_left (hBK x hx) (sub_pos.2 hθ1).le
      have hKL : (1 - θ) * K * Real.log (1 + 1 / X.la1 x) =
          θ * |A'| * Real.log (1 + 1 / X.la1 x) := by rw [hK]
      have hA : θ * A' * Real.log (1 + 1 / X.la1 x) ≤ θ * |A'| * Real.log (1 + 1 / X.la1 x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self A') hθ0.le) hL0
      have h3 : θ * (8 * Real.pi * (1 - 2 * (η / 2)) * a * ⨅ τ, X.tt ξ x τ) =
          8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ := by
        rw [← hθη]; ring
      linarith
    · refine ⟨B0, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hI : 1 ≤ ⨅ τ, X.tt ξ x τ := le_ciInf htt
      have h2 := hB0 x hx
      have hpI : 0 ≤ 8 * Real.pi * a * ⨅ τ, X.tt ξ x τ :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith

theorem extraBounds_iff (X : Data E r) (ps : Frame X.Ψ r → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ExtraBounds X ps a ↔ cfwM X ps a := ⟨fun h => cfwM_of_extraBounds X h, extraBounds_of_cfwM X ha⟩

end

end GlobalTheory.FlatCompare
end

section

open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix

namespace GlobalTheory.LeviRank

theorem exists_select_forms {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n N : ℕ} (hn : Module.finrank K M = n)
    (φ : Fin N → Module.Dual K M) (hφ : ∀ x, (∀ k, φ k x = 0) → x = 0) :
    ∃ jj : Fin n → Fin N, ∀ x, (∀ k, φ (jj k) x = 0) → x = 0 := by
  classical
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    have : x = 0 := hφ x (fun k => by simpa using (Submodule.mem_iInf _).1 hx k)
    simp [this]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K φ
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    have h := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_top, Subspace.dual_finrank_eq, hn] at h
    exact h.symm
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => a (e.symm k), fun x hx => hφ x fun k => ?_⟩
  have hk : φ k ∈ Submodule.span K (Set.range (φ ∘ a)) := by rw [hsp, hspan]; trivial
  refine Submodule.span_induction (p := fun f _ => f x = 0) ?_ ?_ ?_ ?_ hk
  · rintro _ ⟨i, rfl⟩
    simpa using hx (e i)
  · simp
  · intro f g _ _ hf hg; simp [hf, hg]
  · intro c f _ hf; simp [hf]

theorem wJac_mulVec {n N : ℕ} (w : Fin N → V n → ℂ) (x : V n)
    (hw : ∀ k, DifferentiableAt ℂ (w k) x) (ξ : V n) (k : Fin N) :
    (wJac n N w x *ᵥ ξ.ofLp) k = fderiv ℂ (w k) x ξ := by
  have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
    ext i
    simp [bas, Pi.single_apply]
  conv_rhs => rw [hξ]

  simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hw k), map_sum, map_smul,
  smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem main : ∀ (n N : ℕ) (w : Fin N → V n → ℂ) (U : Set (V n)), IsOpen U → (0 : V n) ∈ U →
    (∀ k, DifferentiableOn ℂ (w k) U) → (∃ k, w k 0 ≠ 0) →
    (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re) →
    ∃ (j0 : Fin N) (jj : Fin n → Fin N), w j0 0 ≠ 0 ∧
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0).det ≠ 0 := by
  intro n N w U hU h0 hw ⟨j0, hj0⟩ hL
  have hC : ∀ k, ContDiffAt ℂ 2 (w k) 0 := fun k =>
    ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).contDiffAt (hU.mem_nhds h0)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hD : ∀ k, DifferentiableAt ℂ (w k) 0 := fun k => (hw k).differentiableAt (hU.mem_nhds h0)
  have hne : (fun i => w i 0) ≠ 0 := fun h => hj0 (congrFun h j0)
  have hQ : ∀ k, DifferentiableAt ℂ (fun z => w k z / w j0 z) 0 := fun k => by
    simp only [div_eq_mul_inv]
    exact (hD k).mul ((differentiableAt_inv hj0).comp (0 : V n) (hD j0))
  have hker : ∀ x : V n, (∀ k, fderiv ℂ (fun z => w k z / w j0 z) 0 x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hξ : x.ofLp ≠ 0 := fun h => hx0 (by ext i; simpa using congrFun h i)
    have h1 := hL _ hξ
    have e1 : (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) =
        fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
      funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
    rw [e1, leviLogNormSq n N w 0 x.ofLp hC hne] at h1
    have hJ : wJac n N w 0 *ᵥ x.ofLp = (fderiv ℂ (w j0) 0 x / w j0 0) • fun i => w i 0 := by
      funext k
      rw [wJac_mulVec w 0 hD]
      have hev : w k =ᶠ[𝓝 0] fun z => (w k z / w j0 z) * w j0 z := by
        filter_upwards [(hD j0).continuousAt.eventually_ne hj0] with z hz
        rw [div_mul_cancel₀ _ hz]
      rw [hev.fderiv_eq, fderiv_fun_mul (hQ k) (hD j0)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hx k, smul_eq_mul,
        Pi.smul_apply]
      ring
    have hs : ((sqNorm (fun i => w i 0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (sqNorm_pos hne).ne'
    have hP : projPerp (fun i => w i 0) *ᵥ (fun i => w i 0) = 0 := by
      rw [projPerp_mulVec, star_dotProduct_self, inv_mul_cancel₀ hs, one_smul, sub_self]
    rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at h1
    simp [sqNorm] at h1
  obtain ⟨jj, hjj⟩ := exists_select_forms (K := ℂ) (M := V n) (n := n) (by simp)
    (fun k => (fderiv ℂ (fun z => w k z / w j0 z) 0 : V n →L[ℂ] ℂ).toLinearMap) hker
  refine ⟨j0, jj, hj0, ?_⟩
  have hF : DifferentiableAt ℂ
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 :=
    differentiableAt_euclidean.2 fun k => hQ (jj k)
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot']
  intro x hx
  refine hjj x fun k => ?_
  have h2 := ((EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ).hasFDerivAt.comp (0 : V n)
    hF.hasFDerivAt).fderiv
  have h3 : (fun z => w (jj k) z / w j0 z) = (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) ∘
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) := rfl
  change fderiv ℂ (fun z => w (jj k) z / w j0 z) 0 x = 0
  rw [h3, h2, ContinuousLinearMap.comp_apply]
  change (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) (((fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) x) = 0
  rw [hx, map_zero]

end GlobalTheory.LeviRank
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LineHeight

theorem gramDet_column {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (((A * (Matrix.of fun k (_ : Unit) => u k))ᴴ * (A * (Matrix.of fun k (_ : Unit) => u k))).det.re)
      = ∑ a, ‖(A.mulVec u) a‖ ^ 2 := by
  rw [Matrix.det_unique, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (A * Matrix.of fun k (_ : Unit) => u k) a default = A.mulVec u a := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [Matrix.conjTranspose_apply, h, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem exists_min_le_of_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (m : ℝ) (hm : m ≤ ∏ i, f i) : ∃ i, min 1 m ≤ f i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i0⟩ := ‹Nonempty ι›
  by_cases hm0 : m ≤ 0
  · exact absurd ((min_le_right _ _).trans (hm0.trans (hf i0))) (not_le.mpr (hcon i0))
  · have h1 : ∀ i, f i ≤ 1 := fun i => ((hcon i).trans_le (min_le_left _ _)).le
    have hp : ∏ i, f i ≤ f i0 := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0)]
      exact mul_le_of_le_one_right (hf i0) (Finset.prod_le_one₀ (fun i _ => hf i) fun i _ => h1 i)
    have h2 : f i0 < m := (hcon i0).trans_le (min_le_right _ _)
    linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nonempty_cmType {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, not_not.mp (mt (X.cmType τ).2 h)⟩⟩

theorem c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ :=
  mul_pos two_pos (norm_pos_iff.mpr ((map_ne_zero τ.1).mpr X.ξ0_ne))

theorem exists_la1_lower_bound_of_line_heights : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → 0 < r → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → ε ≤ X.la1 x) := by
  intro r X d hd hr m hm
  have := nonempty_cmType X
  obtain ⟨τ0, -, hτ0⟩ := (Finset.univ : Finset X.Ψ).exists_min_image X.c Finset.univ_nonempty
  have hmin : 0 < min 1 m := lt_min one_pos hm
  have hδ : 0 < X.c τ0 * min 1 m := mul_pos (c_pos X τ0) hmin
  refine ⟨Real.sqrt (X.c τ0 * min 1 m), Real.sqrt_pos.2 hδ, fun x hx hW => ?_⟩
  obtain ⟨hdet, hmaj⟩ := GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx
  have key : ∀ v ∈ X.Λ, v ≠ 0 →
      X.c τ0 * min 1 m ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have hli : LinearIndependent E (fun _ : Unit => v) := linearIndependent_unique_iff.mpr hv0
    have hfin : Module.finrank E (Submodule.span E (Set.range fun _ : Unit => v)) = 1 := by
      rw [Set.range_const]
      exact finrank_span_singleton hv0
    have hg : ∀ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k (_ : Unit) => τ.1 (v k))).det.re =
          X.maj x τ (Data.emb τ.1 v) :=
      fun τ => (gramDet_column _ _).trans (hmaj τ _).symm
    have hmaj0 : ∀ τ, 0 ≤ X.maj x τ (Data.emb τ.1 v) := fun τ => by
      rw [hmaj]
      positivity
    have hidx := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X Unit (fun _ => v) hli fun _ => hv
    have h1 := hW _ hfin
    rw [hd x hdet Unit (fun _ => v) hli (fun _ => hv)] at h1
    simp only [hg] at h1
    have h2 : m ≤ ∏ τ, X.maj x τ (Data.emb τ.1 v) :=
      h1.trans (div_le_self (Finset.prod_nonneg fun τ _ => hmaj0 τ)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hidx))
    obtain ⟨τ, hτ⟩ := exists_min_le_of_le_prod _ hmaj0 m h2
    calc X.c τ0 * min 1 m ≤ X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          mul_le_mul (hτ0 τ (Finset.mem_univ _)) hτ hmin.le (c_pos X τ).le
      _ ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) :=
          Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v))
            (fun τ _ => mul_nonneg (c_pos X τ).le (hmaj0 τ)) (Finset.mem_univ τ)
  have hne : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ :=
      Submodule.span_eq_bot.mpr fun v hv => hcon v hv
    rw [X.Λ_span] at hbot
    have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact top_ne_bot hbot
  obtain ⟨v0, hv0, hv00⟩ := hne
  unfold Data.la1
  refine Real.sqrt_le_sqrt ?_
  unfold Data.firstMinimumSq
  refine le_csInf ⟨_, v0, hv0, hv00, rfl⟩ ?_
  rintro t ⟨v, hv, hv0', rfl⟩
  exact key v hv hv0'

end GlobalTheory.LineHeight
end
