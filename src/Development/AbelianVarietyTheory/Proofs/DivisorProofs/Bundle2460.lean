module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReduction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftGaps

theorem antitone_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_le_mk] at hab
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) (by omega))
    · obtain rfl : a = n + 1 := by omega
      exact le_rfl

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

section Pt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem nCol_le (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    GlobalTheory.RefSum.nCol (dat p i) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
  obtain ⟨-, -, s3⟩ := hw.sig
  have hcard : Fintype.card (Lt1 (dat p i)) = D.R.f * D.R.r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [GlobalTheory.RefSum.sum_mult, hh.deg, s3]
    simp
  have hmult : ∀ τ, (dat p i).mult τ ≤ D.R.r := fun τ => by
    rw [← s3]; unfold Datum.mult; split_ifs <;> omega
  have hsum : ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 (dat p i)) * (2 * D.R.r) := by
    rw [← smul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have := GlobalTheory.FactorDepth.rk_le f
    have := hmult f.1
    omega
  rw [hcard] at hsum
  unfold GlobalTheory.RefSum.nCol
  have h8 : 8 * ((∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f) / 8) ≤ ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f :=
    Nat.mul_div_le _ _
  rw [hcard]
  have : D.R.f * D.R.r * (2 * D.R.r) = 2 * D.R.r * (D.R.f * D.R.r) := by ring
  omega

theorem cols_le_len (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    (GlobalTheory.RefSum.nCol (dat p i) + 1) * (CompHt.dimFlag (dat p i) + 3) ≤ lenT p i PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hr6 : 6 ≤ D.R.r := by omega
  have hf8 := hh.f8
  have hn := nCol_le p i PP A M hw hh
  have hZ : (40 : ℝ) ≤ zBase L := by
    unfold zBase
    have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
    have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    have a4 : (10 : ℝ) ≤ L.sc.L := hh.big.2.1
    nlinarith
  have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
  have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [hw.dim]; push_cast [Nat.cast_choose_two]; ring
  set Dd : ℝ := ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) with hDd
  have F8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have R6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
  have FR : (48 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hDd1 : (1 : ℝ) ≤ Dd := by rw [hD]; nlinarith
  have hn' : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1 ≤ 17 * Dd := by
    have : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
      exact_mod_cast hn
    rw [hD]
    have h13 : (45 : ℝ) ≤ 13 * D.R.r - 33 := by linarith
    have : (48 : ℝ) * 45 ≤ ((D.R.f : ℝ) * D.R.r) * (13 * D.R.r - 33) := mul_le_mul FR h13 (by norm_num) (by linarith)
    nlinarith
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hT : 1600 * Dd ^ 2 ≤ (lenT p i PP : ℝ) := by
    have h1 : 1600 * Dd ^ 2 ≤ PP ^ 2 * Dd ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [le_div_iff₀ hm0]
      have c5 : (1600 : ℝ) ≤ PP ^ 2 := by nlinarith
      have c6 : (0 : ℝ) ≤ Dd ^ 2 := by positivity
      calc 1600 * Dd ^ 2 * D.R.m ≤ PP ^ 2 * Dd ^ 2 * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) hm0.le
        _ ≤ PP ^ 2 * Dd ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm (by positivity)
    exact h1.trans (Nat.le_ceil _)
  have hmain : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (lenT p i PP : ℝ) := by
    have e1 : Dd + 3 ≤ 4 * Dd := by linarith
    have : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (17 * Dd) * (4 * Dd) :=
      mul_le_mul hn' e1 (by linarith) (by linarith)
    nlinarith
  rw [hDd] at hmain
  exact_mod_cast hmain

theorem gapsAt (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁,
      (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))),
      (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p →
        (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  obtain ⟨s1, s2, s3⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have hcl := cols_le_len p i PP A M hw hh
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, -, hH⟩ := hw.hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hdiv
  have hT1 := hW.h1
  simp only [wtsAt] at G hT1

  have gin : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → 0 ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb
    obtain ⟨g1, g2, -⟩ := G τ a b hb
    by_cases hbp : (b : ℕ) = (dat p i).p
    · have g := (g2 hbp).1
      have hT0 : (0 : ℤ) < 2 * (lenT p i PP : ℤ) := by omega
      by_contra hc
      push_neg at hc
      have := mul_neg_of_pos_of_neg hT0 hc
      nlinarith
    · have g := g1 hbp
      have : (0 : ℤ) ≤ (lenT p i PP : ℤ) + CompHt.dimFlag (dat p i) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
        positivity
      omega
  have gbar : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb hbp
    obtain ⟨-, g2, -⟩ := G τ a b hb
    have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by omega
    have hle : (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    have : (0 : ℤ) ≤ (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
    linarith

  have gub : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      P.ub τ a - P.ub τ b = (P.u₁ τ a - P.u₁ τ b) / ((dimFlag (dat p i) : ℤ) + 3) := by
    intro τ a b hb
    have hb' : (a : ℕ) + 1 < (dat p i).p + (dat p i).q := hb ▸ b.2
    rw [← CompHS.gap_eq (P.ub τ) hb, P.gap_ub τ hb', CompHS.gap_eq (P.u₁ τ) hb]
  have hcl' : ((GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1) * ((dimFlag (dat p i) : ℤ) + 3) ≤ (lenT p i PP : ℤ) := by
    rw [← dimFlag_eq]; exact_mod_cast hcl
  have hD0 : (0 : ℤ) < (dimFlag (dat p i) : ℤ) + 3 := by positivity
  have hD1 : (1 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 3 := by omega
  have hnT : (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ (lenT p i PP : ℤ) := by
    have : (0 : ℤ) ≤ (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 := by positivity
    nlinarith
  refine ⟨by omega, fun la hla => ?_⟩
  rcases hla with rfl | hla
  · refine ⟨fun τ => antitone_of_step fun a b hb => by have := gin τ a b hb; omega, fun τ a b ha hb => ?_⟩
    exact hnT.trans (gbar τ a b (by omega) hb)
  · rw [Set.mem_singleton_iff] at hla
    subst hla
    refine ⟨fun τ => antitone_of_step fun a b hb => ?_, fun τ a b ha hb => ?_⟩
    · have e := gub τ a b hb
      have := Int.ediv_nonneg (gin τ a b hb) hD0.le
      omega
    · rw [gub τ a b (by omega)]
      exact Int.le_ediv_of_mul_le hD0 (hcl'.trans (gbar τ a b (by omega) hb))

end Pt

end GlobalTheory.LiftGaps
end
end

section



noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem laOf_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℝ) = entR D i t n := by
  rw [← ent_cast, ← laOf_read p i τ t ht n, Rat.cast_intCast]

theorem anchor_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) = entR D i t (D.R.k - 1 - 1) := by
  have h : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by
    have := D.R.m_add_three_le_k
    rw [dat_p]; omega
  unfold anchor
  rw [dite_eq_left h, laOf_real p i τ t ht]

theorem uW_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (uW p i τ n : ℝ) = entR D i t n - entR D i t (D.R.k - 1 - 1) := by
  rw [← laOf_real p i τ t ht n, ← anchor_real p i τ t ht, ← Int.cast_sub]
  rfl

theorem h0_eq : LevelStarExponents.h0 L = (p.h0 : ℝ) := by
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast p.hm
  unfold LevelStarExponents.h0
  rw [p.hh0]
  field_simp

theorem wtNum_at (P : ParameterChoice' D L) (T : ParamsT D L P) (hS : SizesAt L) (hx8 : 8 ≤ L.sc.x)
    (hy : 3 ≤ L.sc.x ^ (L.sc.eps / 4)) : WtNum p i T.PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have e1 := dat_p p i
  have e2 := dat_q p i
  have e3 := dat_rank p i
  have hD : dimFlag (dat p i) = T.Dp := (dim_eq p i).trans T.Dp_eq.symm
  have hlx : 2 ≤ Real.log L.sc.x := by
    have h1 : Real.log 8 ≤ Real.log L.sc.x := Real.log_le_log (by norm_num) hx8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  have hL3 : 3 ≤ L.sc.L :=
    hy.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [L.sc.eps_pos]))
  have hwin := size_window D L hS hlx ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have hP := forty_le_PP T
  have hPt := (parameterPrecision_le_length_and_rank D L P T (by linarith) (one_le_nWn D L P T)).2
  have hwid := mul_widths_le D L T.PP (by linarith) hS (by linarith) hy
  have hS0 := L.Sc_pos
  have hη0 := L.etaSz_pos
  have h40 : 40 * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n := le_trans (mul_le_mul_of_nonneg_right hP (by linarith)) hwid
  have hrη : (D.R.r : ℝ) ≤ L.etaSz := by
    refine le_trans ?_ P.t_le_eta
    exact_mod_cast (by have := D.R.rank_add_five_le; omega : D.R.r ≤ D.R.t)
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hD]; exact Nat.ceil_le.2 (len_le D L P T)
  have hlen' : 4 * T.Dp + 4 ≤ lenT p i T.PP := by
    unfold lenT; rw [hD]; exact len_ge T
  obtain ⟨s1, s2, s3⟩ := spacing_ge T ((i : ℕ) + 1) _ hlen
  obtain ⟨q1, q2, q3⟩ := prod_bounds T _ hlen
  obtain ⟨g1, g2⟩ := gap_le D L P T (lenT p i T.PP) (Nat.cast_nonneg _) (by exact_mod_cast hlen)
  have hh : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0.le (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  have hstep : ∀ t a, a + 1 < D.R.r → ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) + 1 ≤
      sgR D t a - sgR D t (a + 1) := fun t a ha =>
    sgR_step D L P t _ g1 g2
      (fun hm => le_trans g2 (minimalGap_le_first_lowerRowParameter D L P _ (Nat.le_add_left _ _) i.2 t (hwin t).1 hm)) a ha
  have hstep1 : ∀ t a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1) := fun t a ha =>
    le_trans (le_add_of_nonneg_left (by positivity)) (hstep t a ha)
  have hent : ∀ t n, n < D.R.r → |entR D i t n| ≤ 3 * L.sc.b := by
    intro t n hn
    obtain ⟨w1, w2⟩ := hwin t
    by_cases h : n < D.R.k - 1
    · obtain ⟨a1, a2⟩ := entR_cloud L i t n h
      rw [abs_le]; constructor <;> linarith
    · have := entR_node L i t n (by omega) hn
      linarith
  have hanc : ∀ t, L.sc.w'' D.R.n - D.R.r ≤ entR D i t (D.R.k - 1 - 1) := fun t => by
    have := (entR_cloud L i t (D.R.k - 1 - 1) (by omega)).1
    linarith [(hwin t).1]
  have hc0 : (0 : ℝ) ≤ cZeroN D ((i : ℕ) + 1) := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ lenT p i T.PP := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [e3]
  have eZ : ((((dat p i).p + (dat p i).q : ℕ)) : ℤ) = D.R.r := by rw [e3]
  refine ⟨⟨e1, e2, e3⟩, card_psi p, dim_eq p i, cols_eq p i, dom_wtA _, unit_eq p, ?_, ?_, ?_, ?_, fun him => ?_⟩
  · rw [ofRecord_logOm]; exact abs_logOm_le hS hL3
  · intro τ n
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [laOf_real p i τ t ht]
    have := hent t n (e3 ▸ n.2)
    have := abs_nonneg (entR D i t n)
    linarith
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [anchor_real p i τ t ht]
    linarith [hanc t]
  · rw [hD]; exact ⟨q2, q3⟩
  rw [h0_eq p] at s1 s2 s3 q1 hh
  refine ⟨p.h0, L.Sc, L.etaSz, hS0.le, hη0.le, by linarith, by exact_mod_cast s3, by rw [hD]; exact_mod_cast q1, fun u1 => ?_⟩
  refine ⟨show 1 ≤ D.R.k - 1 by omega, show D.R.k - 1 < (dat p i).p by omega, show (dat p i).p < _ by omega,
    show _ - (dat p i).p < (dat p i).p by omega, Int.natCast_nonneg _, fun τ a ha => uWt_anchor _ _ _ _ τ a ha,
    show 4 * dimFlag (dat p i) + 4 ≤ lenT p i T.PP by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 4 * ((cZeroN D ((i : ℕ) + 1) : ℤ) + 2 * ((dat p i).p + (dat p i).q : ℕ) + lenT p i T.PP + dimFlag (dat p i) + 1) ≤ p.h0 ∧
      24 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) * lenT p i T.PP ≤ p.h0
    rw [hD, eZ]
    exact ⟨by exact_mod_cast s1, by exact_mod_cast s2⟩
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ) + (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| ≤
      L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)
    rw [uW_real p i τ t ht, anchor_real p i τ t ht, sub_add_cancel, eN]
    have := entR_node L i t a ha (e3 ▸ a.2)
    linarith
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 0 ≤ uW p i τ a ∧ (uW p i τ a : ℝ) ≤ L.Sc
    obtain ⟨a1, a2⟩ := entR_cloud_sub L i t (hstep1 t) a ha
    rw [← uW_real p i τ t ht] at a1 a2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 4 * ((L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)) + L.Sc + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * ((dat p i).p + (dat p i).q : ℕ)) + 20 * ((dat p i).p + (dat p i).q : ℕ) * (lenT p i T.PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
    rw [anchor_real p i τ t ht, eN, Int.cast_natCast]
    have := hanc t
    have h5 : 0 ≤ (D.R.r : ℝ) * lenT p i T.PP := by positivity
    nlinarith
  · intro τ a b hab
    obtain ⟨t, ht⟩ := exists_tau p τ
    have hb := b.2
    have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) =
        sgR D t a - sgR D t (a + 1) - 1 + if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
      rw [Int.cast_sub, uW_real p i τ t ht, uW_real p i τ t ht, hab, ← entR_step]; ring
    have hge : sgR D t a - sgR D t (a + 1) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
      rw [hd]; split_ifs <;> linarith
    refine ⟨fun _ => ?_, fun ha => ?_, fun hp => ?_⟩
    · show ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2) *
        ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ)) ≤ uW p i τ a - uW p i τ b + 2
      rw [hD, eZ]
      have := hstep t a (by omega)
      have h2 : ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        ((uW p i τ a - uW p i τ b : ℤ) : ℝ) + 2 := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) - 1 ≤ uW p i τ a - uW p i τ b
      have := sgR_step_low D L P t a ha (by omega)
      rw [h0_eq p] at this
      have h2 : (p.h0 : ℝ) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) ≤ uW p i τ a - uW p i τ b
      have hp' : (b : ℕ) = (dat p i).p := hp
      have := sgR_step_low D L P t a (by omega) (by omega)
      rw [h0_eq p] at this
      rw [if_pos (by omega)] at hd
      have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
      have h2 : (p.h0 : ℝ) ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
  · intro τ a
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ)| + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) + 4 * ((dat p i).p + (dat p i).q : ℕ) ≤ 2 * (4 * L.sc.b)
    rw [uW_real p i τ t ht, eN, Int.cast_natCast]
    have a1 := hent t a (e3 ▸ a.2)
    have a2 := hent t (D.R.k - 1 - 1) (by omega)
    have a3 := abs_sub (entR D i t a) (entR D i t (D.R.k - 1 - 1))
    obtain ⟨w1, w2⟩ := hwin t
    linarith

theorem wtN : WtN := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, le_rfl, max 8 ((3 : ℝ) ^ (4 / eps)), fun x hx hle ι p _ i => ?_⟩⟩⟩
  refine wtNum_at p i (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) ?_ ?_
  · rw [Fm.L_x x ι hx]; exact (le_max_left _ _).trans hle
  · rw [Fm.L_x x ι hx, Fm.L_eps x ι]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hle) (by positivity)

end GlobalTheory.CovTop.WtShape

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ → ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm → Embeds O N lam mu ϖ Gm → ∀ τ, (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) = ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  first | exact @GlobalTheory.CapelliLink.linkage | exact GlobalTheory.CapelliLink.linkage | (intros; apply GlobalTheory.CapelliLink.linkage <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.exists_primeDivisor_over_target_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective | exact GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.ord_functionField_pullback_primeDivisor_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g := by
  first | exact @GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective | exact GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective | (intros; apply GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.primeDivisorCentre_through_image : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ y : Y, E'.Through y → E.Through (s y) := by
  first | exact @GlobalTheory.Discrepancy.DivOver.Over.through_image | exact GlobalTheory.Discrepancy.DivOver.Over.through_image | (intros; apply GlobalTheory.Discrepancy.DivOver.Over.through_image <;> assumption)
end
