module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.TreeLeafParameterArithmeticOfBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle346
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.BigTop.Fun.LeafMMTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Spread

open GlobalTheory.SignedHC

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

theorem weightX_zero_bounds {x : ℚ} (hx : x ∈ (num D C τ).weightX 0) :
    ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ x ∧ x ≤ (num D C τ).a 0 := by
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg : (0 : ℚ) ≤ (num D C τ).ga := by positivity
  have v_le_two {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) :
      ((num D C τ).v i : ℚ) ≤ (num D C τ).v 2 := by
    rcases h1.eq_or_lt with rfl | h
    · exact le_rfl
    · exact_mod_cast ((num D C τ).v_anti 2 i le_rfl h h2).le
  have a_le {i j : ℕ} (h : i ≤ j) : (num D C τ).a j ≤ (num D C τ).a i := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := num D C τ) h]
  have hvk := v_le_two hk le_rfl
  have ham : (num D C τ).a (num D C τ).m = (num D C τ).v 2 + (num D C τ).ga + 1 / 2 := (num D C τ).a_m
  have hlow : ∀ i, i ≤ D.R.m → ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ (num D C τ).a i := fun i hi => by
    have := a_le hi
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  have h0 : ((num D C τ).v 2 : ℚ) + 1 / 2 ≤ (num D C τ).a 0 := by
    have h1 := a_le (Nat.zero_le D.R.m)
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, -⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    exact ⟨hlow i hi, a_le (Nat.zero_le i)⟩
  · obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 h
    have hi := v_le_two h1 h2
    have hik : ((num D C τ).v D.R.k : ℚ) ≤ (num D C τ).v i := by
      rcases h2.eq_or_lt with e | e
      · rw [e]; exact le_rfl
      · exact_mod_cast ((num D C τ).v_anti i D.R.k h1 e le_rfl).le
    simp only [GridData.vHalf]
    constructor <;> linarith
  · have hb := blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 h
    have hp := (num D C τ).a_pred h1
    have hq := a_le (Nat.zero_le (i - 1))
    exact ⟨(hlow i h2).trans hb.1.le, by linarith [hb.2]⟩
  · omega

theorem La_sub_le (i j : Fin (rankP D D.R.m)) :
    (((La D C τ).w i - (La D C τ).w j : ℤ) : ℚ) ≤
      (((num D C τ).v 2 - (num D C τ).v D.R.k : ℤ) : ℚ) + 1 + ((D.R.m : ℚ) + 1) * (gap D C : ℚ) + (rankP D D.R.m : ℚ) := by
  push_cast
  rw [La_cast, La_cast]
  simp only [highestWeight]
  have hi := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) i)
  have hj := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) j)
  have ea : (num D C τ).a 0 = (num D C τ).v 2 + 1 / 2 + ((D.R.m : ℚ) + 1 - ((0 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have hi' : ((i : ℕ) : ℚ) ≤ (rankP D D.R.m : ℚ) := by exact_mod_cast i.2.le
  have hj' : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := by positivity
  rw [ea] at hi hj
  push_cast at hi hj
  linarith [hi.1, hi.2, hj.1, hj.2]

end Spread

section Leaf

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem np_eq {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) : ((rankP D D.R.m : ℕ) : ℝ) = d.O.np := by
  have hm := D.R.two_le_m
  have e1 : D.R.r + 6 - 1 = D.R.k + D.R.m + 4 := by unfold Ranks.r; omega
  have e2 : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; omega
  have e : rankP D D.R.m = (D.R.k + D.R.m) + D.R.m * (D.R.k + D.R.m + 4) := by
    unfold rankP nRk sLen
    rw [e1, e2]
  rw [e]
  show _ = ((D.R.k : ℝ) + D.R.m - 1 + 1) + D.R.m * (((D.R.k : ℝ) + D.R.m - 1) + 5)
  push_cast
  ring

theorem leafMM_of_test {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieTest d a) {C : ℝ}
    (hC : 1 ≤ C) : Formalism.L2.Indef.Tree.LeafMM d.O C := by
  obtain ⟨v₀, hv⟩ := (GlobalTheory.ptField_main D).2.1
  have hga : (gap D 1 : ℝ) ≤ d.O.ga C := by
    rw [← GlobalTheory.BigTop.Fun.Model.ga_eq d 1]
    exact_mod_cast GlobalTheory.SizeLeafCheck.ga_mono _ hC
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) + 1 := by positivity
  have hRp : d.O.Rp C = ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) + d.O.Lc + d.O.np := rfl
  have hnp : (0 : ℝ) ≤ d.O.np := by rw [← np_eq d]; positivity
  have hR1 : 1 ≤ d.O.Rp C := by
    rw [hRp]
    have : (1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) + 1 := by linarith [(Nat.cast_nonneg D.R.m : (0 : ℝ) ≤ D.R.m)]
      have h2 : (1 : ℝ) ≤ (d.O.ga C : ℝ) + 1 := by linarith [(Nat.cast_nonneg (d.O.ga C) : (0 : ℝ) ≤ d.O.ga C)]
      nlinarith
    have : (0 : ℝ) ≤ d.O.Lc := Nat.cast_nonneg _
    linarith
  have hSp : GlobalTheory.TestLat.SpreadLe (LaP d.G) (d.O.Rp C) := by
    intro τ i j
    show (((La D 1 τ).w (Fin.cast (rank_Xp d.G) i) - (La D 1 τ).w (Fin.cast (rank_Xp d.G) j) : ℤ) : ℝ) ≤ _
    have hq := La_sub_le D 1 τ (Fin.cast (rank_Xp d.G) i) (Fin.cast (rank_Xp d.G) j)
    have hr := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at hr
    have hL : ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat ≤ cloudLen D :=
      Finset.le_sup (f := fun τ => ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 -
        (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat) (Finset.mem_univ τ)
    have hL' : (((num D 1 τ).v 2 : ℝ) - (num D 1 τ).v D.R.k) ≤ d.O.Lc := by
      rw [GlobalTheory.BigTop.Fun.Model.Lc_eq d]
      have h1 := Int.self_le_toNat ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k)
      have h2 : (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k : ℤ) : ℝ) ≤ (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℤ) := by
        exact_mod_cast h1
      have h3 : ((((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℕ) : ℝ) ≤ (cloudLen D : ℝ) := by exact_mod_cast hL
      push_cast at h2
      linarith
    have hmul := mul_le_mul_of_nonneg_left (by linarith : (gap D 1 : ℝ) + 1 ≤ (d.O.ga C : ℝ) + 1) hm0
    have hexp : ((D.R.m : ℝ) + 1) * ((gap D 1 : ℝ) + 1) = ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) + ((D.R.m : ℝ) + 1) := by ring
    have hm1 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    rw [hRp, ← np_eq d]
    push_cast
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := IsTestLat.gridTestLattice_largestSlope_bound GlobalTheory.TestLat.slope_holds.2 hv hR1 hSp h
  refine ⟨h1, h2, h3, h4.trans (le_of_eq ?_)⟩
  unfold GlobalTheory.TestLat.bound Formalism.L2.Indef.Tree.FunData.EMM
  rw [rank_Xp, np_eq d, D.what₂.card_Tau]
  rfl

end Leaf

end GlobalTheory.BigTop.Fun.LeafMMTie
end
end

section

set_option autoImplicit false


noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.MeanTop

namespace GlobalTheory.RefSum.DivWt

section Free

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (h : W.Hyp) (hd : W.IsDiv)
include h hd


omit [Fintype ι] in
theorem antitone (τ : ι) : Antitone (W.u1 τ) := fun a b hab => by
  have hab' : (a : ℕ) ≤ b := hab
  have := (W.div_gap_sum h hd τ (b - a) a b (by omega)).1
  linarith

theorem mul_abs_le (τ : ι) (a : Fin N) : (W.T : ℝ) * |(W.u1 τ a : ℝ)| ≤ 2 * W.b := by
  have h1 := (divided_entries ι N W h hd τ a).1
  have h2 : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h3 := h.h5 τ a
  have h4 : 0 ≤ ((W.Dd : ℝ) + 1) * |(W.u1 τ a : ℝ)| := by positivity
  linarith


omit [Fintype ι] in
theorem mul_cloud_le (τ : ι) (a : Fin N) (ha : (a : ℕ) < W.kc) : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ W.S + 2 * N := by
  have hk := h.kc_lt
  have hp := h.p_lt
  let c : Fin N := ⟨W.kc - 1, by omega⟩
  have hc : (c : ℕ) + 1 = W.kc := by simp only [c]; omega
  obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (c - a) a c (by omega)
  have h3 : (((c : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
  rw [(hd τ).1 c hc, sub_zero] at h1 h2
  rw [h.anchor τ c hc] at h2
  have h4 : 0 ≤ ((W.Dd : ℤ) + 1) * W.u1 τ a := by positivity
  have h5 : (W.T : ℤ) * W.u1 τ a ≤ W.u τ a + 2 * N := by linarith
  have h6 : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ (W.u τ a : ℝ) + 2 * N := by exact_mod_cast h5
  linarith [(h.h3cloud τ a ha).2]

end Free

theorem nCol_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    nCol Dw ≤ Module.finrank ℚ E * (Dw.p + Dw.q) * (2 * (Dw.p + Dw.q) + 8) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := rk_le f
    have : Dw.mult f.1 ≤ Dw.p + Dw.q := by rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q) + 8) (card_Lt1_le_finrank_mul (Dw := Dw))
  rw [mul_add (Fintype.card (Lt1 Dw))] at h2
  unfold nCol
  omega

theorem gap_num {PP T X h g f r : ℝ} (hT : 0 < T) (hX : 60 ≤ X) (hf : 1 ≤ f) (hr : 1 ≤ r) (hP : f * r ^ 2 ≤ PP)
    (h1 : PP * X * T ≤ h) (h2 : h ≤ 2 * T * g) : 2 * f * r * (2 * r + 8) + 8 + 1 ≤ g := by
  have a : PP * X ≤ 2 * g := le_of_mul_le_mul_right (by linarith) hT
  have b1 : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have b2 : f * r ≤ f * r ^ 2 := by nlinarith
  have c : PP * 60 ≤ PP * X := mul_le_mul_of_nonneg_left hX (by linarith)
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem wtAt_of_wtNum {PP : ℝ} (h : WtNum p i PP) (hP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : GlobalTheory.AllWt.Weight (dat p i)) (hq : Quo p i PP u1) : WtAt p i PP 802 u1 := by
  obtain ⟨h0, S, eta, hS, he, hSe, -, hh0, hH⟩ := h.hyp hi
  have H := hH u1
  have hd := (quo_iff p i PP h0 S eta u1).1 hq
  obtain ⟨hp, hq', hr⟩ := h.sig
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hf : 2 ≤ D.R.f := D.R.two_le_m.trans D.R.m_le_f
  simp only [Ranks.sigW] at hp hq'
  have hT1 : 4 * GlobalTheory.CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP := H.h1
  have hD : 1 ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by
    rw [h.dim]; exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨τ0⟩ : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [h.card]; omega)).1
  have han : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) ≤ 4 * L.sc.b := by
    unfold anchor
    rw [dite_eq_left (by omega)]
    exact (le_abs_self _).trans (h.up τ0 _)
  have hlow := h.low τ0
  have hw : 4 * ((eta + S + (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + S + ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + 20 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) := H.h3w τ0
  have hc0 : (0 : ℝ) ≤ ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) := by exact_mod_cast (cZero_spec D _).2.1
  have hrows := h.what₂.1
  have e1 : ∀ τ a, (lenT p i PP : ℝ) * |(u1 τ a : ℝ)| ≤ 2 * (4 * L.sc.b) := mul_abs_le _ H hd
  have e2 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) < D.R.k - 1 →
      (lenT p i PP : ℝ) * (u1 τ a : ℝ) ≤ S + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) := mul_cloud_le _ H hd
  have e3 : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := fun τ a b hab hb =>
    ((divided_gaps _ _ _ H hd τ a b hab).2.1 hb).1
  have e4 : ∀ τ, Antitone (u1 τ) := antitone _ H hd
  have e5 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = D.R.k - 1 → u1 τ a = 0 := fun τ => (hd τ).1
  have hn := nCol_le (dat p i)
  rw [GlobalTheory.PinNum.finrank_host D, hr] at hn
  rw [hr] at hw
  simp only [hr] at e2
  unfold WtAt
  clear H hd hH hq h
  have hT : (1 : ℝ) ≤ lenT p i PP := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hT' : 1 ≤ lenT p i PP := by omega
  generalize lenT p i PP = T at *
  generalize (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) = w at *
  generalize ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) = c at *
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hD' : (1 : ℝ) ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by exact_mod_cast hD
  have hkP : (D.R.k : ℝ) ≤ PP := by nlinarith
  have hTb : (T : ℝ) ≤ 4 * L.sc.b := by nlinarith
  have hb : 0 ≤ L.sc.b := by linarith
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, GlobalTheory.PinNum.finrank_host D⟩, by omega,
    ⌊8 * L.sc.b / T⌋₊, D.R.k * (S + 2 * D.R.r) / T, ⟨e4, fun τ a ha => e5 τ a (by omega), fun τ a b ha hb' => ?_,
      fun τ a => ?_, fun τ => ?_⟩, ?_, ?_, hT'⟩
  · have g1 : (h0 : ℝ) ≤ 2 * (T : ℝ) * ((u1 τ a - u1 τ b : ℤ) : ℝ) := by exact_mod_cast e3 τ a b (by omega) hb'
    have hX : (60 : ℝ) ≤ D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * GlobalTheory.CompHt.dimFlag (dat p i) := by
      calc (60 : ℝ) ≤ 5 * 2 ^ 2 * 2 ^ 2 * 5 * 1 := by norm_num
        _ ≤ _ := by gcongr; linarith
    have g2 := gap_num (by linarith) hX (by linarith) (by linarith) hP (le_of_eq_of_le (by ring) hh0) g1
    have g3 : ((nCol (dat p i) : ℕ) : ℝ) ≤ 2 * D.R.f * D.R.r * (2 * D.R.r + 8) + 8 := by exact_mod_cast hn
    have g4 : ((nCol (dat p i) : ℕ) : ℝ) + 1 ≤ ((u1 τ a - u1 τ b : ℤ) : ℝ) := by linarith
    exact_mod_cast g4
  · have g1 : ((|u1 τ a|.toNat : ℕ) : ℝ) = |(u1 τ a : ℝ)| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg _), Int.cast_abs]
    have g2 : |u1 τ a|.toNat ≤ ⌊8 * L.sc.b / T⌋₊ := by
      refine Nat.le_floor ?_
      rw [g1, le_div_iff₀ (by linarith)]
      linarith [e1 τ a]
    exact Int.toNat_le.1 g2
  · rw [le_div_iff₀ (by linarith), Finset.sum_mul]
    refine (Finset.sum_le_card_nsmul _ _ (S + 2 * D.R.r) fun a ha => ?_).trans ?_
    · have := (Finset.mem_filter.1 ha).2
      linarith [e2 τ a (by omega)]
    · rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : (Finset.univ.filter (fun a : Fin ((dat p i).p + (dat p i).q) => (a : ℕ) + 2 < D.R.k)).card ≤
          (Finset.range D.R.k).card :=
        Finset.card_le_card_of_injOn (fun a => (a : ℕ))
          (fun a ha => by have := (Finset.mem_filter.1 ha).2; simp only [Finset.coe_range, Set.mem_Iio]; omega)
          (fun a _ b _ e => Fin.ext e)
      rw [Finset.card_range] at this
      exact_mod_cast this
  · have g1 : ((⌊8 * L.sc.b / T⌋₊ : ℕ) : ℝ) ≤ 8 * L.sc.b / T := Nat.floor_le (by positivity)
    rw [le_div_iff₀ (by linarith)] at g1
    linarith
  · rw [mul_div_cancel₀ _ (by linarith)]
    have g1 : (D.R.k : ℝ) * S ≤ PP * (S + eta) := mul_le_mul hkP (by linarith) hS (by linarith)
    have g2 : (D.R.r : ℝ) * D.R.k ≤ L.sc.b := by
      refine le_trans ?_ hrows
      calc (D.R.r : ℝ) * D.R.k = 1 ^ 2 * D.R.r * 1 * D.R.k * 1 ^ 3 := by ring
        _ ≤ _ := by gcongr <;> linarith
    linarith

theorem le_PP {P : ParameterChoice' D L} (T : ParamsT D L P) : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ T.PP := by
  have h1 : D.R.f * D.R.r ^ 2 ≤ T.nWn := le_trans (by nlinarith [Nat.zero_le (D.R.f * D.R.r)]) T.nW_lo.1
  exact le_trans (by exact_mod_cast h1) T.nW_le

end GlobalTheory.RefSum.DivWt

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem fnMap_pullbackBijective12_of_acyclic {C : Type 1} [Category.{0} C] (K : Cx C)
    (h1 : K.M1.Ac0 ∧ K.M1.Ac1 ∧ K.M1.Ac2) (h2 : K.M2.Ac0 ∧ K.M2.Ac1 ∧ K.M2.Ac2) (h3 : K.M3.Ac0 ∧ K.M3.Ac1 ∧ K.M3.Ac2) :
    K.fnMap.PullbackBijectiveDegreesOneTwo :=
  And.intro (GlobalTheory.T.forget_positive_h1_bijective C K h1.1 h1.2.1 h2.1) (GlobalTheory.T.forget_positive_h2_bijective C K h1.2.1 h1.2.2 h2.1 h2.2.1 h3.1)

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem top_le_preimage_of_hom {T T' : Thick κ t} (f : T ⟶ T') (U : Y.Opens) (h : ⊤ ≤ (T.x ≫ i) ⁻¹ᵁ U) :
    ⊤ ≤ (T'.x ≫ i) ⁻¹ᵁ U := by
  intro p _
  rw [← f.pt, Category.assoc]
  exact h (Set.mem_univ ((spMap f.φ₀).base p))

variable (κ t i)

def liftE (S : Thick κ t ⥤ Thick κ t) (u : 𝟭 _ ⟶ S) : EE κ t i ⥤ EE κ t i where
  obj a := ⟨⟨S.obj a.obj.T, a.obj.U, a.obj.hU, top_le_preimage_of_hom (u.app a.obj.T) a.obj.U a.obj.mem⟩, a.property⟩
  map f := ⟨⟨S.map f.hom.1, f.hom.2⟩⟩
  map_id a := ObjectProperty.hom_ext _ (Subtype.ext (S.map_id a.obj.T))
  map_comp f g := ObjectProperty.hom_ext _ (Subtype.ext (S.map_comp f.hom.1 g.hom.1))

def liftT (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S) : 𝟭 (EE κ t i) ⟶ liftE κ t i S u where
  app a := ⟨⟨v.app a.obj.T, le_rfl⟩⟩
  naturality a b f := ObjectProperty.hom_ext _ (Subtype.ext (v.naturality f.hom.1))

variable {κ t i}

theorem acyc_res_pE (M : Coef (Thick κ t)) (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (h : (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x)) ∧
      (∀ T x, r T (M.map (u.app T) x) = 0) ∧ (∀ T x, r T (M.map (v.app T) x) = x)) :
    (M.res (pE κ t i)).Ac0 ∧ (M.res (pE κ t i)).Ac1 ∧ (M.res (pE κ t i)).Ac2 :=
  GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ (M.res (pE κ t i)) (liftE κ t i S u) (liftT κ t i S u u) (liftT κ t i S u v) (fun a ↦ r a.obj.T)
    (fun a b f x ↦ h.1 a.obj.T b.obj.T f.hom.1 x) (fun a x ↦ h.2.1 a.obj.T x) (fun a x ↦ h.2.2 a.obj.T x)

theorem crystalline_forget_forms_bijective_site_and_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i
  obtain ⟨S, u, v, r1, r2, r3, h1, h2, h3a, h3b, h3c⟩ := GlobalTheory.T.exists_diagonal_firstNeighbourhood_retraction_forms R I κ X t
  have h3 := And.intro h3a (And.intro h3b h3c)
  exact ⟨fnMap_pullbackBijective12_of_acyclic _ (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r1 h1.1 h1.2.1 h1.2.2)
      (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r2 h2.1 h2.2.1 h2.2.2) (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r3 h3a h3b h3c),
    fnMap_pullbackBijective12_of_acyclic _ (acyc_res_pE (i := i) _ S u v r1 h1) (acyc_res_pE (i := i) _ S u v r2 h2)
      (acyc_res_pE (i := i) _ S u v r3 h3)⟩

end GlobalTheory.PDForm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_quasiInverse_isogeny : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    ∃ (n : ℕ) (g : B ⟶ A), 0 < n ∧ IsIsogeny g ∧ f ≫ g = n • 𝟙 A ∧ g ≫ f = n • 𝟙 B := by
  intro K _ A B f hf
  obtain ⟨hdim, -, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨n, hn, hker⟩ := GlobalTheory.T.abelianVariety_finiteHom_kernel_killed_by_nat K A B f hf.1
  have hB := B.smooth
  have hA := A.smooth
  rw [hdim] at hA
  obtain ⟨h, hh, hfh, hhf⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A.X B.X B.dim A.ab B.ab hA hB
    f.hom inferInstance n hn hker
  let g : B ⟶ A := Hom.mk (A := B) (B := A) h (h := hh)
  have e1 : f ≫ g = n • 𝟙 A := by
    apply Subtype.ext
    change (f ≫ g).hom = (n • 𝟙 A).hom
    simp [g, hfh]
  have e2 : g ≫ f = n • 𝟙 B := by
    apply Subtype.ext
    change (g ≫ f).hom = (n • 𝟙 B).hom
    simp [g, hhf]
  refine ⟨n, g, hn, ?_, e1, e2⟩
  have hm : IsIsogeny ((n : ℤ) • 𝟙 B) := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K B n (by exact_mod_cast hn.ne')).1
  rw [natCast_zsmul, ← e2] at hm
  exact (((GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K B A B g f hdim.symm hdim).1).mp hm).1

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

theorem _root_.GlobalTheory.T.hilbertSamuel_component_short_basis_bound : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), ∀ Λ₀ : ℝ, GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ → HSClaimS 26 P.T (CompHt.dimFlag Dw) f₁.n 1 k.abelian₂ k.beta k.LamD k.LamT (Real.log Λ₀) (CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0)) (CompHt.compHeight U x V dict Z (AllWt.wtOf Dw P.u₁ 0)) (Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0))) (AllWt.degOn U x V dict Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  first | exact @GlobalTheory.HSShort.hsClaimS_component_geo | exact GlobalTheory.HSShort.hsClaimS_component_geo | (intros; apply GlobalTheory.HSShort.hsClaimS_component_geo <;> assumption)
end
