module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gc_arith (f r L A n s lam lp a b M : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hs : A + f * r * n + 1 ≤ s) (hlam : 0 ≤ lam) (hlp : 0 ≤ lp) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : a + b ≤ M) :
    (140 * r * L * A + 10 * L * A + 200 * f * r * n * L ≤ 400 * (f * r * L) * s) ∧
    (2 * (lam + 2 * lp) * s + 400 * (f * r * L) * s + lam * s ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) ∧
    ((lam + 2 * lp) * s + (400 * (f * r * L) * s + 3 * f * r * n * L + 5 * a + b + 2) ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) := by
  have hfr : 12 ≤ f * r := by nlinarith
  have hrf : r ≤ f * r := by nlinarith
  obtain ⟨F, hF⟩ : ∃ F, F = f * r := ⟨_, rfl⟩
  rw [← hF] at hfr hrf hs
  have hFn : F ≤ F * n := by nlinarith
  have hnF : n ≤ F * n := by nlinarith
  have hs3 : 13 ≤ s := by linarith
  have hAs : A ≤ s := by linarith
  have hns : n ≤ s := by linarith
  have hFns : F * n ≤ s := by linarith
  have hZ : 24 ≤ F * L := by nlinarith
  have hLZ : L ≤ F * L := by nlinarith
  have hrL : r * L ≤ F * L := by nlinarith
  have hZs : 24 ≤ F * L * s := by nlinarith
  have h1 : r * L * A ≤ F * L * s := mul_le_mul hrL hAs hA (by linarith)
  have h2 : L * A ≤ F * L * s := mul_le_mul hLZ hAs hA (by linarith)
  have h3 : F * L * n ≤ F * L * s := mul_le_mul_of_nonneg_left hns (by linarith)
  have hLs : 0 ≤ L * s := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hMs : M * 13 ≤ M * s := mul_le_mul_of_nonneg_left hs3 hM0
  have hlams : 0 ≤ lam * s := by positivity
  have hlps : 0 ≤ lp * s := by positivity
  have h4 : 12 * (lam * s) ≤ F * (lam * s) := mul_le_mul_of_nonneg_right hfr hlams
  have h5 : 12 * (lp * s) ≤ F * (lp * s) := mul_le_mul_of_nonneg_right hfr hlps
  have e : (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s =
      1040 * (F * L * s) + 3 * (L * s) + 2 * (M * s) + 2 * (F * (lam * s)) + 4 * (F * (lp * s)) := by
    rw [hF]; ring
  have e1 : 400 * (f * r * L) * s = 400 * (F * L * s) := by rw [hF]; ring
  have e2 : 200 * f * r * n * L = 200 * (F * L * n) := by rw [hF]; ring
  have e3 : 3 * f * r * n * L = 3 * (F * L * n) := by rw [hF]; ring
  have e4 : 140 * r * L * A = 140 * (r * L * A) := by ring
  have e5 : 10 * L * A = 10 * (L * A) := by ring
  have e6 : 2 * (lam + 2 * lp) * s = 2 * (lam * s) + 4 * (lp * s) := by ring
  have e7 : (lam + 2 * lp) * s = lam * s + 2 * (lp * s) := by ring
  rw [e, e1, e2, e3, e4, e5, e6, e7]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem lamStar_nonneg_nat (D : D7) : 0 ≤ lamStar D := by
  unfold lamStar
  have h1 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    have := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    simpa only [Nat.cast_mul] using this
  have h2 : 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    have := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d =
        ((D.R.f ^ 2 * D.host.q * D.host.d : ℕ) : ℝ) := by push_cast; ring
    rw [e]; exact this
  linarith

theorem sup_bounds_le_Gc : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  intro D B large₂ j w p hL hn
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos
      omega
    exact_mod_cast this
  have hr : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by
      unfold Ranks.r
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hA : 0 ≤ absA w := by unfold absA; positivity
  have hn' : (1 : ℝ) ≤ w.n := by exact_mod_cast hn
  have hs : absA w + (D.R.f : ℝ) * D.R.r * w.n + 1 ≤ w.size := by
    unfold WeightFamilies.Wt.size absA
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
    have : (D.R.f : ℝ) * D.R.r * w.n ≤
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hm h0]
    linarith
  have hb : 0 ≤ Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [Real.log_abs]
    exact Real.log_intCast_nonneg _
  unfold WeightAlgebra.Gc Zb
  exact gc_arith _ _ _ _ _ _ _ _ _ _ _ hf hr hL hA hn' hs (lamStar_nonneg_nat D)
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg _) hb (le_max_left _ _)

end GlobalTheory.RunIn
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.AuxiliaryWeightsExistence

theorem antitone_nonneg_of_gaps {p : ℕ} (g : Fin p → ℤ)
    (hg : ∀ (i : Fin p) (h : i.1 + 1 < p), g ⟨i.1 + 1, h⟩ ≤ g i)
    (hl : ∀ i : Fin p, i.1 + 1 = p → 0 ≤ g i) : Antitone g ∧ ∀ i, 0 ≤ g i := by

  have walk : ∀ k : ℕ, ∀ i j : Fin p, j.1 = i.1 + k → g j ≤ g i := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have : j = i := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro i j hij
      have hm : i.1 + k < p := by have := j.2; omega
      have hstep := hg ⟨i.1 + k, hm⟩ (by have := j.2; simp only; omega)
      have hj : (⟨i.1 + k + 1, by have := j.2; omega⟩ : Fin p) = j := Fin.ext (by simp only; omega)
      rw [hj] at hstep
      exact le_trans hstep (ih i ⟨i.1 + k, hm⟩ rfl)
  refine ⟨fun i j hij => walk (j.1 - i.1) i j (by have : i.1 ≤ j.1 := hij; omega), fun i => ?_⟩
  have hp : p - 1 < p := by have := i.2; omega
  exact le_trans (hl ⟨p - 1, hp⟩ (by simp only; have := i.2; omega))
    (walk (p - 1 - i.1) i ⟨p - 1, hp⟩ (by simp only; have := i.2; omega))

theorem gap_key (c cL T' r : ℤ) (hT : 0 < T') (hr : 0 ≤ r) (hc : T' * (T' + 2 * r) ≤ c + 2)
    (hL : cL = Int.fdiv (c + 2) T') : c ≤ (T' + 2) * cL := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hT.le] at hL
  have hdm := Int.mul_ediv_add_emod (c + 2) T'
  have hlt := Int.emod_lt_of_pos (c + 2) hT
  have hge := Int.emod_nonneg (c + 2) hT.ne'
  rw [← hL] at hdm

  have hq : T' + 2 * r ≤ cL := by
    by_contra hcon
    rw [not_le] at hcon
    have : T' * (cL + 1) ≤ T' * (T' + 2 * r) := by
      apply mul_le_mul_of_nonneg_left _ hT.le; omega
    nlinarith
  nlinarith

theorem exists_block {p : ℕ} (a l f : Fin p → ℕ) (T Dm r T' : ℕ) (hT' : T' = T + Dm + 2)
    (hf : ∀ i, (f i : ℤ) = a i - T * l i)
    (hgap : ∀ i : Fin p, i.1 + 1 < p → ((T' * (T' + 2 * r) : ℕ) : ℤ) ≤ gapZ a i + 2)
    (hL : ∀ i : Fin p, i.1 + 1 < p → gapZ l i = Int.fdiv (gapZ a i + 2) T')
    (hlast : ∀ i : Fin p, i.1 + 1 = p → (a i : ℤ) ≤ ((T : ℤ) + Dm + 4) * l i) :
    ∃ w : Fin p → ℕ, Antitone w ∧ ∀ i, w i + f i = (Dm + 4) * l i := by

  have hT'z : (T' : ℤ) = T + Dm + 2 := by rw [hT']; push_cast; ring
  have hg := antitone_nonneg_of_gaps (fun i => ((T : ℤ) + Dm + 4) * l i - a i) ?_ ?_
  · refine ⟨fun i => (((T : ℤ) + Dm + 4) * l i - a i).toNat,
      fun i j hij => Int.toNat_le_toNat (hg.1 hij), fun i => ?_⟩
    have h0 := hg.2 i
    have hfi := hf i
    dsimp only at h0 ⊢
    zify
    rw [Int.toNat_of_nonneg h0]
    linarith
  · intro i h
    have hk := gap_key (gapZ a i) (gapZ l i) T' r (by omega) (by positivity)
      (by exact_mod_cast hgap i h) (hL i h)
    unfold gapZ at hk
    rw [dite_eq_left h, dite_eq_left h, hT'z] at hk
    nlinarith
  · intro i h
    have := hlast i h
    linarith

private theorem le_mul_fdiv_sub_of_sq_le (a c T Dm : ℤ) (hD : 0 ≤ Dm) (h40 : 40 * (Dm + 2) ≤ T)
    (hc : c ≤ T) (ha : 2 * T ^ 2 ≤ a) :
    a ≤ (T + Dm + 4) * Int.fdiv (a - c) (T + Dm + 2) := by
  have hT : 0 < T + Dm + 2 := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hT.le]
  have hdm := Int.mul_ediv_add_emod (a - c) (T + Dm + 2)
  have hlt := Int.emod_lt_of_pos (a - c) hT
  have hge := Int.emod_nonneg (a - c) hT.ne'
  set q := (a - c) / (T + Dm + 2) with hq
  set m := (a - c) % (T + Dm + 2) with hm

  have h2q : c + T + Dm + 2 ≤ 2 * q := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (T + Dm + 2) * (2 * q) ≤ (T + Dm + 2) * (2 * T + Dm + 1) := by
      apply mul_le_mul_of_nonneg_left _ hT.le
      omega
    have hT0 : (0 : ℤ) ≤ T := by omega
    nlinarith [mul_le_mul_of_nonneg_right h40 hT0, mul_le_mul_of_nonneg_right h40 hD,
      mul_nonneg hD hT0, mul_nonneg hD hD]
  nlinarith

theorem exists_auxiliaryWeights_at_runWeights : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 →
      (∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2) ∧ ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, hgP, hgM, hh0, -, hlP, hlM, -, hnP, -, hPW, -, -, -, hL, hF, -, -, -, h40, hcT, h40W,
    -, -, -, -⟩ := hS
  obtain ⟨hLn, hLP, hLM⟩ := hL
  obtain ⟨hFn, hFP, hFM⟩ := hF
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = Tn + WeightFamilies.dimY D j + 2 := by unfold Tp; push_cast; ring
  have h40z : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40

  have hbigP : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      2 * (Tn : ℤ) ^ 2 ≤ ka.aP τ i := by
    intro τ i hi
    have h1 := hlP τ i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ ka.aP τ i := by linarith
    exact_mod_cast h2
  have hbigM : ∀ τ (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
      2 * (Tn : ℤ) ^ 2 ≤ ka.aM τ i := by
    intro τ i hi
    have h1 := hlM τ i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ ka.aM τ i := by linarith
    exact_mod_cast h2

  have blockP : ∀ τ, ∃ w : Fin (D.R.sigW j).1 → ℕ, Antitone w ∧
      ∀ i, w i + wF.aP τ i = (WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ
    refine exists_block (ka.aP τ) (wL.aP τ) (wF.aP τ) Tn (WeightFamilies.dimY D j) D.R.r (Tp D j Tn) rfl
      (hFP τ) (hgP τ) ?_ ?_
    · intro i hi
      have hl := hLP τ i
      rw [if_pos hi] at hl
      exact hl
    · intro i hi
      have hn : ¬ (i.1 + 1 < (D.R.sigW j).1) := by omega
      have hl := hLP τ i
      rw [if_neg hn] at hl
      unfold gapZ at hl
      rw [dite_eq_right hn] at hl
      have hk := le_mul_fdiv_sub_of_sq_le (ka.aP τ i) (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) Tn
        (WeightFamilies.dimY D j) (by positivity) h40z (by exact_mod_cast hcT) (hbigP τ i hi)
      have e : (ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r =
          ka.aP τ i - (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) := by ring
      rw [hl, e, hTp]
      exact hk
  have blockM : ∀ τ, ∃ w : Fin (D.R.sigW j).2 → ℕ, Antitone w ∧
      ∀ i, w i + wF.aM τ i = (WeightFamilies.dimY D j + 4) * wL.aM τ i := by
    intro τ
    refine exists_block (ka.aM τ) (wL.aM τ) (wF.aM τ) Tn (WeightFamilies.dimY D j) D.R.r (Tp D j Tn) rfl
      (hFM τ) (hgM τ) ?_ ?_
    · intro i hi
      have hl := hLM τ i
      rw [if_pos hi] at hl
      exact hl
    · intro i hi
      have hn : ¬ (i.1 + 1 < (D.R.sigW j).2) := by omega
      have hl := hLM τ i
      rw [if_neg hn] at hl
      unfold gapZ at hl
      rw [dite_eq_right hn] at hl
      have hk := le_mul_fdiv_sub_of_sq_le (ka.aM τ i) 0 Tn (WeightFamilies.dimY D j) (by positivity) h40z
        (by positivity) (hbigM τ i hi)
      rw [sub_zero] at hk
      rw [hl, hTp]
      exact hk
  choose bP hbPa hbPs using blockP
  choose bM hbMa hbMs using blockM
  have hnW : Even nW := hLn ▸ wL.n_even
  have hle : nP ≤ (WeightFamilies.dimY D j + 4) * nW := le_trans hPW (by nlinarith)
  have hn2 : Even ((WeightFamilies.dimY D j + 4) * nW - nP) :=
    (Nat.even_sub hle).2 ⟨fun _ => hnP, fun _ => hnW.mul_left _⟩
  have hP2 : ∀ τ, Antitone (fun i => 2 * wL.aP τ i) := fun τ a b h => by
    have := wL.aPlus_antitone τ h
    dsimp only
    omega
  have hM2 : ∀ τ, Antitone (fun i => 2 * wL.aM τ i) := fun τ a b h => by
    have := wL.aM_anti τ h
    dsimp only
    omega
  have hn1 : Even (2 * nW - 2) := ⟨nW - 1, by omega⟩
  refine ⟨⟨(⟨bP, bM, hbPa, hbMa, (WeightFamilies.dimY D j + 4) * nW - nP, hn2⟩ : WeightFamilies.Wt D j), ?_, hbPs, hbMs⟩,
    ⟨(⟨fun τ i => 2 * wL.aP τ i, fun τ i => 2 * wL.aM τ i, hP2, hM2, 2 * nW - 2, hn1⟩ : WeightFamilies.Wt D j),
      ?_, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · show (WeightFamilies.dimY D j + 4) * nW - nP + wF.n = (WeightFamilies.dimY D j + 4) * wL.n
    rw [hFn, hLn]
    exact Nat.sub_add_cancel hle
  · show 2 * nW - 2 + 2 = 2 * nW
    omega

end GlobalTheory.AuxiliaryWeightsExistence
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem exists_short_span_thetaTie_of_scalars : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (C1 A1 Gc : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), ScalB large₂ X C1 A1 S ka wL wF Tn → EtaleWeightGaps.GrowthConstantBound large₂ B Gc → ∃ Sh : Finset (B.Cusp j wF), Submodule.span B.KO (Sh : Set (B.Cusp j wF)) = ⊤ ∧ (∀ g ∈ Sh, g ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B g ≤ Gc * wF.size) ∧ ∀ G : EtaleWeightGaps.GlobalFamilyData X ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh S Gc := by
  intro D B P j X large₂ C1 A1 Gc S ka wL wF Tn hS hG
  obtain ⟨-, -, -, -, -, po, hpo, -, PLam, hPLam, -, ⟨Sh, hSub, hSpan, hMean⟩, -, -⟩ := hS

  have hconst : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po ≤ Gc := by
    refine le_trans ?_ (hG po hpo)
    unfold Formalism.MainNotions.WeightAlgebra.Gc
    linarith
  have hbound : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po * wF.size ≤ Gc * wF.size :=
    mul_le_mul_of_nonneg_right hconst (le_trans zero_le_one wF.one_le_size)
  refine ⟨Sh, hSpan, fun g hg => ⟨hSub hg, (hMean g hg).trans hbound⟩, fun G hG' i => ?_⟩
  exact ⟨hSub (hG' i), (hMean _ (hG' i)).trans hbound⟩

end GlobalTheory
end
