module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpan
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle064
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle043
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsProportionalOfSqLaw
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle063
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle013
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.ae_exists_flat_datum_linearCombination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  first | exact @GlobalTheory.GenericFlat.ae_exists_flat | exact GlobalTheory.GenericFlat.ae_exists_flat | (intros; apply GlobalTheory.GenericFlat.ae_exists_flat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

theorem _root_.GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → ∀ la, InBasis G la ↔ (LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (G.th' i))) ∧ G.del = δ) := by
  first | exact @GlobalTheory.Shares.inBasis_iff_vals | exact GlobalTheory.Shares.inBasis_iff_vals | (intros; apply GlobalTheory.Shares.inBasis_iff_vals <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem half_sup_at_ortho_frame : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hrows hL2 hn hlast σ hσ f hf hsup
  have hfs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf
  have hRS := (hL.unf j hj σ hσ).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f hfs
  unfold Formalism.L2.Pj.supN at hsup ⊢
  have hStop : Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≠ ⊤ := by
    intro h
    rw [h] at hsup
    simp at hsup
  have hSpos : 0 < Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) :=
    (ENNReal.toReal_pos_iff.mp hsup).1
  have hhalf := ENNReal.half_lt_self hSpos.ne' hStop
  have hhalf' := hhalf
  unfold Formalism.L2.Pj.supE at hhalf'
  obtain ⟨⟨k, x, hx⟩, hp⟩ := lt_iSup_iff.mp hhalf'
  have hB := (hRS k).2.1
  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((T.U j σ).X k) hx
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((T.U j σ).X k) hx hb
  have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((T.U j σ).X k) hx
  have hpn := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
    (rdU (T.U j σ) f k) hB x hx _ hb
  have hu1 : ∀ τ i, ‖dmin ((T.U j σ).X k).Gm
      (rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((T.U j σ).X k) x)) τ i‖ = 1 :=
    fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((T.U j σ).X k) ho τ i
  have hpu := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((T.U j σ).X k)
    (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) hu1
  have hrd := Formalism.L2.Pj.rdU_mem (T.U j σ) f k hy
  have hlt := (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hStop two_ne_zero)
    ENNReal.ofReal_ne_top).mpr hp
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal'] at hlt
  have hlt' : (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal / 2 <
      max (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x) 0 := by
    simpa using hlt
  have hm : 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x := by
    rcases lt_max_iff.mp (lt_trans (half_pos hsup) hlt') with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  rw [max_eq_left hm.le] at hlt'
  have hle : ∀ z ∈ ((T.U j σ).X k).dom,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z ≤
        (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal := by
    intro z hz
    have h1 : ENNReal.ofReal (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z) ≤
        Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le (⟨k, ⟨z, hz⟩⟩ : Formalism.L2.Pj.FPt (T.U j σ).X) le_rfl
    exact (ENNReal.ofReal_le_iff_le_toReal hStop).mp h1
  refine ⟨k, ⟨_, hy⟩, hu1, ho, ?_, ?_⟩
  · rw [← hrd, ← hpu, hpn]
    linarith
  · exact GlobalTheory.T.firstMinimum_bound_at_halfSupremum_cuspForm D T hL hG large₂ j hj w hrows hL2 hn σ hσ f hf k _ hy
      (fun z hz => by rw [hpn]; linarith [hle z hz]) (by rw [hpn]; exact hm)

end GlobalTheory.RunIn
end

section

open NumberField Matrix Complex
open scoped ComplexConjugate Real
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd hermForm)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory.CanTh (canTh canMult translConst)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  (idx : Fin g ≃ X.Ψ × Fin r)

section Coord

variable (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

end Coord

section Series

variable {idx} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ}

theorem polyDeriv_prod_canFn_eq_mul (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {a b a' b' : Fin n → Fin g → ℝ} {c : Fin n → ℂ}
    (h : ∀ k z, canFn X bas' idx (a' k) (b' k) x z = c k * canFn X bas idx (a k) (b k) x z)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hr idx) (fun z => ∏ k, canFn X bas' idx (a' k) (b' k) x (z k)) 0 =
      (∏ k, c k) *
        _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hr idx) (fun z => ∏ k, canFn X bas idx (a k) (b k) x (z k)) 0 := by
  have hF : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas' idx (a' k) (b' k) x (z k)) =
      fun z => (∏ k, c k) * ∏ k, canFn X bas idx (a k) (b k) x (z k) := by
    funext z
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => h k (z k)
  have hd : Differentiable ℂ
      (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) := by
    have he : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) =
        ∏ k, fun z : Fin n → Fin g → ℂ => canFn X bas idx (a k) (b k) x (z k) := by
      funext z; simp [Finset.prod_apply]
    rw [he]
    exact Finset.prod_induction _ (fun f => Differentiable ℂ f) (fun f1 f2 h1 h2 => h1.mul h2)
      (differentiable_const 1)
      fun k _ => (canFn_entire idx hs hx (a k) (b k)).comp (differentiable_apply k)
  rw [hF]
  exact GlobalTheory.CanTh.polyDeriv_const_mul P _ isOpen_univ hd.differentiableOn _ (Set.mem_univ _)

variable (hs : IsSympl X bas) (hs' : IsSympl X bas') (hn : Even n)
include hs hs' hn

theorem IsProportional.thFr_eq {κ : ℂ} {a₀ b₀ a₀' b₀' : Fin g → ℝ}
    (h : IsProportional X idx κ bas a₀ b₀ bas' a₀' b₀') {u u' : Fin n → Fin g ⊕ Fin g → ℝ}
    (hu : ∀ k, IsSamePt X bas bas' (u k) (u' k)) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    thFr X hr bas' idx n (fun k => a₀' + u' k ∘ Sum.inr) (fun k => b₀' + u' k ∘ Sum.inl) P x =
      κ ^ (n / 2) * (∏ k, translConst b₀ (u k ∘ Sum.inr) (u k ∘ Sum.inl) /
        translConst b₀' (u' k ∘ Sum.inr) (u' k ∘ Sum.inl)) *
      thFr X hr bas idx n (fun k => a₀ + u k ∘ Sum.inr) (fun k => b₀ + u k ∘ Sum.inl) P x := by
  obtain ⟨μ, hμ, hμz⟩ := h x hx
  have hc : ∀ k z, canFn X bas' idx (a₀' + u' k ∘ Sum.inr) (b₀' + u' k ∘ Sum.inl) x z =
      (translConst b₀ (u k ∘ Sum.inr) (u k ∘ Sum.inl) /
        translConst b₀' (u' k ∘ Sum.inr) (u' k ∘ Sum.inl) * μ) *
        canFn X bas idx (a₀ + u k ∘ Sum.inr) (b₀ + u k ∘ Sum.inl) x z := fun k z =>
    canFn_translate_eq_mul hs hs' hx hμz (hu k) z
  have halg : ∀ {A B D : ℂ} (t : Fin n → ℂ), μ ^ 2 * A = κ * B →
      A ^ (n / 2) * ((∏ k, (t k * μ)) * D) = κ ^ (n / 2) * (∏ k, t k) * (B ^ (n / 2) * D) := by
    intro A B D t hAB
    obtain ⟨m, rfl⟩ := hn
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (m + m) / 2 = m by omega]
    have key : (μ ^ 2 * A) ^ m = (κ * B) ^ m := by rw [hAB]
    linear_combination (∏ k, t k) * D * key
  simp only [thFr]
  rw [polyDeriv_prod_canFn_eq_mul hr hs hx hc P]
  exact halg _ hμ


omit hs hs' hn in
theorem norm_pow_mul_prod_translConst {κ : ℂ} (hκ : ‖κ‖ = 1) (j : ℕ) (b b' : Fin g → ℝ)
    (s t s' t' : Fin n → Fin g → ℝ) :
    ‖κ ^ j * ∏ k, translConst b (s k) (t k) / translConst b' (s' k) (t' k)‖ = 1 := by
  rw [norm_mul, norm_pow, hκ, one_pow, one_mul, norm_prod]
  exact Finset.prod_eq_one fun k _ => by
    rw [norm_div, GlobalTheory.CanTh.norm_translConst, GlobalTheory.CanTh.norm_translConst, div_one]


variable (idx) in
theorem exists_thFr_eq_mul (a b : Fin n → Fin g → ℝ) :
    ∃ (a' b' : Fin n → Fin g → ℝ) (c : ℂ), ‖c‖ = 1 ∧
      ((∀ k i, a k i ∈ Set.range (Rat.cast : ℚ → ℝ)) → (∀ k i, b k i ∈ Set.range (Rat.cast : ℚ → ℝ)) →
        (∀ k i, a' k i ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
          ∀ k i, b' k i ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
      ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), ∀ x ∈ X.dom,
        thFr X hr bas idx n a b P x = c * thFr X hr bas' idx n a' b' P x := by
  obtain ⟨k, k', hk⟩ := exists_isProportional idx hs' hs
  obtain ⟨κ, hκ, hprop⟩ := hk 0 0 (Matrix.mulVec_zero _).symm
  set w' : Fin n → Fin g ⊕ Fin g → ℝ := fun j =>
    Sum.elim (b j - fun i => (k' i : ℝ) / 2) (a j - fun i => (k i : ℝ) / 2) with hw'
  set w : Fin n → Fin g ⊕ Fin g → ℝ := fun j =>
    (chgMat X bas' bas).map (Int.cast : ℤ → ℝ) *ᵥ w' j with hw
  have hu : ∀ j, IsSamePt X bas' bas (w j) (w' j) := fun j => rfl
  refine ⟨fun j => (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inr + w j ∘ Sum.inr,
    fun j => (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl + w j ∘ Sum.inl,
    κ ^ (n / 2) * ∏ j, translConst ((0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl) (w j ∘ Sum.inr)
      (w j ∘ Sum.inl) / translConst ((fun i => (k' i : ℝ) / 2) + (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl)
      (w' j ∘ Sum.inr) (w' j ∘ Sum.inl),
    norm_pow_mul_prod_translConst hκ _ _ _ _ _ _ _, ?_, ?_⟩
  · intro ha hb
    have hw'r : ∀ j s, w' j s ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      intro j s
      rcases s with i | i
      · obtain ⟨q, hq⟩ := hb j i
        exact ⟨q - (k' i : ℚ) / 2, by simp [hw', hq]⟩
      · obtain ⟨q, hq⟩ := ha j i
        exact ⟨q - (k i : ℚ) / 2, by simp [hw', hq]⟩
    have hwr : ∀ j s, w j s ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      intro j s
      choose q hq using hw'r j
      refine ⟨((chgMat X bas' bas).map (Int.cast : ℤ → ℚ) *ᵥ q) s, ?_⟩
      simp [hw, Matrix.mulVec, dotProduct, hq]
    exact ⟨fun j i => by simpa using hwr j (Sum.inr i), fun j i => by simpa using hwr j (Sum.inl i)⟩
  · intro P x hx
    have h := IsProportional.thFr_eq hr hs' hs hn hprop hu P hx
    convert h using 2 <;> funext j <;> simp [hw']

end Series

end

end GlobalTheory.ThFr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (Dom a n → Dw.p + Dw.q ≤ n → ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P.IsHomogeneous (Formalism.L2.Pj.DF Dw a) := by
  first | exact @GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous | exact GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous | (intros; apply GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous <;> assumption)
end
