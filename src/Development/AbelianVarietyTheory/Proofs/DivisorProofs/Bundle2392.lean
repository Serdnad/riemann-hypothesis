module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle976
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle130
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LowCover

theorem numeric {M E b K C1 muB mu0 : ℝ} (hb : 0 ≤ b) (hbE : b ≤ E) (hbK : b ≤ K) (hMK : |M| ≤ K) (hC1 : 0 ≤ C1)
    (h : (-M - C1 * E - 2 * b) - b / K * (|-M - C1 * E - 2 * b| + 2 * K) ≤ muB) (hR : muB - 2 * b ≤ mu0) :
    -M - (2 * C1 + 9) * E ≤ mu0 := by
  have hK : 0 < K ∨ b = 0 := by
    rcases eq_or_lt_of_le hb with h0 | h0
    · exact Or.inr h0.symm
    · exact Or.inl (h0.trans_le hbK)
  have hE : 0 ≤ E := hb.trans hbE
  have hC1E : 0 ≤ C1 * E := mul_nonneg hC1 hE
  have ht : |-M - C1 * E - 2 * b| ≤ |M| + C1 * E + 2 * b := by
    have := abs_sub (-M - C1 * E) (2 * b)
    have h2 := abs_sub (-M) (C1 * E)
    rw [abs_neg] at h2
    rw [abs_of_nonneg hC1E] at h2
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * b)] at this
    linarith
  rcases hK with hK | hb0
  · set ε := b / K with hε
    have hε0 : 0 ≤ ε := div_nonneg hb hK.le
    have hε1 : ε ≤ 1 := (div_le_one hK).2 hbK
    have hεK : ε * K = b := div_mul_cancel₀ b hK.ne'
    have h1 : ε * |-M - C1 * E - 2 * b| ≤ ε * |M| + ε * (C1 * E + 2 * b) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hε0
    have h2 : ε * |M| ≤ b := hεK ▸ mul_le_mul_of_nonneg_left hMK hε0
    have h3 : ε * (C1 * E + 2 * b) ≤ C1 * E + 2 * b := by
      have : 0 ≤ C1 * E + 2 * b := by linarith
      nlinarith
    have h4 : ε * (|-M - C1 * E - 2 * b| + 2 * K) = ε * |-M - C1 * E - 2 * b| + 2 * b := by
      rw [mul_add, ← hεK]; ring
    rw [h4] at h
    nlinarith
  · subst hb0
    simp only [zero_div, zero_mul, sub_zero, mul_zero] at h hR
    nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rkK_bot' {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] :
    Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
  simp [Formalism.HN.rkK]

theorem lowAt_mono {p : PtAt ex Csz} {i : Fin D.R.m} {C C' : ℝ} (h : LowAt p i C) (hC : C ≤ C') (hE : 0 ≤ unitE p) :
    LowAt p i C' := by
  unfold LowAt at *
  nlinarith [mul_le_mul_of_nonneg_right hC hE]

theorem lowAt_of_cover (p : PtAt ex Csz) (i : Fin D.R.m) (PP CS CF CU : ℝ) (hCF : 0 ≤ CF) (hCU : 0 ≤ CU)
    (hS : SizeAt p i PP CS) (Y : Cov p i) (hG : DeepGoodAt p i Y) (hR : RingAt p i Y) (hM : MapsAt p i Y)
    (hK : RkAt p i Y PP) (hGm : GminAt p i Y PP) (hF : FlatAt p i Y CF) (hU : UAt p i Y CU) :
    LowAt p i (2 * (CF + CU) + 9) := by
  obtain ⟨hb1, hbE, -, -, hMK, hbK, -⟩ := hS
  obtain ⟨hGk, hGm', -, -, hrk0, -, -, -⟩ := hG
  obtain ⟨n, φ, hint, hinj, hnorm, hrk⟩ := hM
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hKpos : 0 < PP * kap p i := by linarith
  have hBle : latDeep p i Y ≤ latW Y.U (Gk p i) := inf_le_left
  have hBfg : (latDeep p i Y).FG := GlobalTheory.HalfRankSub.fg_of_le_fg hGk.2.1 hBle
  have hA0 : latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1)))) ≠ ⊥ := by
    intro h
    change 0 < Formalism.HN.rkK (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) at hrk0
    rw [h] at hrk0
    rw [rkK_bot'] at hrk0
    exact lt_irrefl _ hrk0
  have hrkR : (n : ℝ) * Formalism.HN.rkK (latDeep p i Y) ≤
      (1 + L.sc.b / (PP * kap p i)) * Formalism.HN.rkK (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) := by
    have h1 : ((n * Formalism.HN.rkK (latDeep p i Y) : ℕ) : ℝ) ≤ (Y.rk (Gs p i (cZero D ((i : ℕ) + 1))) : ℝ) := by
      exact_mod_cast hrk
    push_cast at h1
    exact h1.trans hK
  have hmu : Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1)))) =
      slope_sq (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) := rfl
  have ht : -mainT p i - (CF + CU) * unitE p - 2 * L.sc.b ≤
      slope_sq (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) -
        2 * L.sc.b := by
    unfold FlatAt at hF
    unfold UAt at hU
    rw [← hmu]
    nlinarith
  have hd := GlobalTheory.DescentFamily.descent Y.d.c₂.F _ _ (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (Y.nrm (Gk p i))
    (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latDeep p i Y) n φ L.sc.b (PP * kap p i)
    (L.sc.b / (PP * kap p i)) (-mainT p i - (CF + CU) * unitE p - 2 * L.sc.b) hGm'.1 hGk.1 hGm'.2.1 hBfg hA0
    hint hinj hnorm hGm hKpos.le (div_nonneg (by linarith) hKpos.le) hrkR ht
  unfold LowAt
  unfold RingAt at hR
  exact numeric (by linarith) hbE hbK hMK (by linarith) hd hR

end GlobalTheory.CovTop.LowCover
end
end

section



noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology

namespace GlobalTheory.CovTop.Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tendsto_exp_mul_rpow {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-(x ^ c)) * x ^ A) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / c) 1 one_pos).comp (tendsto_rpow_atTop hc)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ hc.ne', mul_comm, neg_mul, one_mul]

theorem exists_loss_le {c : ℝ} (hc : 0 < c) (A B C : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 12 * Real.exp (-(x ^ c)) * (x ^ A + x ^ B + C) ≤ 1 := by
  have h := ((((tendsto_exp_mul_rpow hc A).add (tendsto_exp_mul_rpow hc B)).add
    ((tendsto_exp_mul_rpow hc 0).mul_const C)).const_mul 12)
  have h1 : (12 : ℝ) * (0 + 0 + 0 * C) < 1 := by norm_num
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds h1))
  refine ⟨x0, fun x hx => ?_⟩
  have := hx0 x hx
  simp only [Real.rpow_zero] at this
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem lcv_le {A B PP C1 C2 : ℝ} (hx : 0 < L.sc.x) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2)
    (hs : 12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) ≤ 1)
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i) (hB : BadAt p i) (hL : LamAt p i A) (hS : SizeAt p i PP B)
    (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤ mainT p i + (C1 + C2 + 1) * unitE p := by
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  obtain ⟨g1, g2, g3, -⟩ := hG
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, -, s4, -⟩ := hS
  unfold RecAt at hR
  unfold LamAt at hL
  unfold CoreAt at hK
  unfold LowAt at hW
  have hA := Real.rpow_pos_of_pos hx A
  have hB' := Real.rpow_pos_of_pos hx B
  have hδ := Real.exp_pos (-(L.sc.x ^ (L.sc.ez / 7)))
  have hm := (abs_le.1 s4).2
  have key := GlobalTheory.CutNum.slope_good_ge D.what₂.LL _ (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i)
    (latAll p.R.toRealDat i) (eGood p.R.toRealDat i) (Fintype.card p.P.Gp) (Real.exp (-(L.sc.x ^ (L.sc.ez / 7))))
    ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) g1 g2 inf_le_left
    (fun h => g3 (le_bot_iff.1 (h ▸ latGood_le p.R.toRealDat p.F.lv2 i))) c1 c2 Fintype.card_pos c3 hδ.le
  have key' : slope_sq (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i) -
      12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) ≤
      slope_sq (nrmR p.R.toRealDat i) (latGood p.R.toRealDat p.F.lv2 i) := by
    refine key ?_ hB ?_ ?_ ?_
    all_goals
      clear key hR
      generalize Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) = δ at *
      generalize L.sc.x ^ A = a at *
      generalize L.sc.x ^ B = b at *
      generalize unitE p = E at *
      have hE : 0 ≤ E := by linarith
      have ea := mul_le_mul_of_nonneg_left s2 hA.le
      have eb := mul_le_mul_of_nonneg_left s2 hB'.le
      have e1 := mul_nonneg h1 hE
      have e2 := mul_nonneg h2 hE
      have e3 := mul_nonneg hA.le hE
      have e4 := mul_nonneg hB'.le hE
    · nlinarith [mul_nonneg hδ.le hA.le, mul_nonneg hδ.le hB'.le, mul_nonneg hδ.le h1, mul_nonneg hδ.le h2]
    · linarith
    · linarith
    · linarith
  have hE : 0 ≤ unitE p := by linarith
  have := mul_le_mul_of_nonneg_right hs hE
  rw [mul_assoc] at this
  linarith

end GlobalTheory.CovTop.Assembly

end
end

section



noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

theorem toNat_floor_cast {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem eQ_succ (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) : DV.eQ D ((i : ℕ) + 1) t = (D.hc t).e i := by
  unfold DV.eQ
  rw [dite_eq_left ⟨Nat.le_add_left _ _, i.2⟩]
  rfl

theorem lamAt_eq (D : D7) (t : D.what₂.Tau) (n : ℕ) : Formalism.L2.NTheta.lamAt (D.hc t) n = DV.sigPar D t n := rfl

theorem aPl_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) t n : ℚ) =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k : ℚ) + i) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have e : DV.aPlusQ D ((i : ℕ) + 1) t n =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
    rw [DV.aPlusQ_eq, eQ_succ]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aPlusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t ⟨n, hn⟩
  have h2 := DV.aPlusQ_int D ((i : ℕ) + 1) t n
  unfold aPl
  rw [if_pos hn, lamAt_eq, ← e, toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem aMi_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (c : ℕ) (hc : (i : ℕ) + 1 + c < D.R.m) :
    (aMi D i (D.R.k + i) (D.R.m - ((i : ℕ) + 1)) t (D.R.m - ((i : ℕ) + 1) - 1 - c) : ℚ) =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have e0 : D.R.m - ((i : ℕ) + 1) - (D.R.m - ((i : ℕ) + 1) - 1 - c) = c + 1 := by omega
  have e1 : DV.sigPar D t (D.R.k + i + c) = -(D.hc t).b ⟨(i : ℕ) + 1 + c, hc⟩ := by
    unfold DV.sigPar
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 3
    omega
  have e : DV.aMinusQ D ((i : ℕ) + 1) t c =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
    unfold DV.aMinusQ
    rw [dite_eq_left hc, eQ_succ, e1]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aMinusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) t c hc
  have h2 := DV.aMinusQ_int D ((i : ℕ) + 1) t c
  unfold aMi
  rw [if_pos (by omega), e0, lamAt_eq, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, ← e,
    toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem nV_half (R : Ranks) : ((R.nV / 2 : ℕ) : ℚ) = ((R.r : ℚ) + R.t) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hm := R.two_le_m
  have h1 : R.r + R.t = 2 * (R.nV / 2) := by unfold Ranks.nV Ranks.r; omega
  have h2 : (R.r : ℚ) + R.t = 2 * ((R.nV / 2 : ℕ) : ℚ) := by exact_mod_cast h1
  linarith

def ent (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℚ :=
  DV.sigPar D t n + (D.hc t).e i + n - ((D.R.k : ℚ) + i) + ((D.R.r : ℚ) + 1) / 2 - if n < D.R.k + i then 0 else (D.R.r : ℚ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem inR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

theorem dat_p : (dat p i).p = D.R.k + i := (p.fw.laws.pins.2.2.2 _ (inR i)).1

theorem dat_q : (dat p i).q = D.R.m - ((i : ℕ) + 1) := (p.fw.laws.pins.2.2.2 _ (inR i)).2.1

theorem dat_rank : (dat p i).p + (dat p i).q = D.R.r := by
  have := i.2
  rw [dat_p, dat_q]; unfold Ranks.r; omega

theorem exists_tau (τ : Psi p.T.Q.H) : ∃ t, τ.1 = DV.tauEmb D t :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q p.fw.laws.pins.1 τ.1 τ.2

theorem card_psi : Nat.card (Psi p.T.Q.H) = D.R.f := by
  have hp := p.fw.laws.pins.1
  have hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hp.2.2.2 t⟩ : Psi p.T.Q.H)) :=
    ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => by
      obtain ⟨t, ht⟩ := exists_tau p τ
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]

theorem dim_eq : dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  unfold dimFlag Formalism.DegreeFormula.dimFl
  rw [dat_rank, ← Nat.card_eq_fintype_card, card_psi, Nat.choose_two_right]

theorem cols_eq : (p.κ i).n = D.R.nV := by
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega)
  obtain ⟨t⟩ := hne
  exact (p.fw.kap i t).2.2

theorem unit_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem laOf_read (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℚ) = ent D i t n := by
  have hp := p.fw.laws.pins.1
  have hs : (Wc D i).sig (TH.tauE D t) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨k1, k2, -⟩ := p.fw.kap i t
  rw [hs] at k1 k2
  have s1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have s2 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - ((i : ℕ) + 1) := rfl
  have hn := n.2
  have e1 := dat_p p i
  have e2 := dat_q p i
  have hh := nV_half D.R
  unfold laOf weightOf ent
  rw [cols_eq, ht]
  beta_reduce
  by_cases h : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h, GlobalTheory.WeightExponents.wtA_tauEmb hp, ext0, dite_eq_left (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), k1]
    have := aPl_cast D i t n h
    simp only [Int.cast_add, Int.cast_natCast, s1]
    rw [this, hh]; ring
  · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + c := ⟨n - (D.R.k + i), by omega⟩
    have e3 : (dat p i).q - 1 - ((n : ℕ) - (dat p i).p) = D.R.m - ((i : ℕ) + 1) - 1 - c := by omega
    rw [if_neg (by omega), if_neg h, e3, conjEmb, GlobalTheory.WeightExponents.conjEmb_eq, GlobalTheory.WeightExponents.wtA_conj hp, ext0,
      dite_eq_left (show D.R.m - ((i : ℕ) + 1) - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 by omega), k2]
    have := aMi_cast D i t c (by omega)
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, s1, s2]
    rw [this, hh, hc]; push_cast; ring

end GlobalTheory.CovTop.WtShape

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PosThrough

theorem one_le_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → ∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed k Z (fun _ : Fin e => N) := by
  intro hNN k _ X q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x hNef ha hcls hamp hN₂ Z e hZ hx he hdim
  have hBig : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q →
      letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X),
      IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N :=
    GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN
  have hAmp : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
      AmpleAt N (π x) → AmpleAt (N.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ
  set q' := redι Z ≫ q with hq'
  letI := algebraΓOfHom q'
  have hi : ∀ r : k, (redι Z).appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver q' := by
    obtain ⟨n, f, hf, hs⟩ := hq
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  obtain ⟨w, rfl⟩ : x ∈ Set.range (redι Z) := by rw [range_redι]; exact hx
  have hb := hBig k _ q' hpq (N.pull (redι Z)) (N₁.pull (redι Z)) (N₂.pull (redι Z))
    (LB.isLB_pull hN _) (LB.isLB_pull h₁ _) (LB.isLB_pull h₂ _) a w
    (hNef.pull_of_isClosedImmersion _ hi) ha
    (by rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add (f := _)])
    (hAmp _ _ _ N₁ h₁ w hamp) (hN₂.pull_of_isClosedImmersion _ hi)
  have hstr : strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = q' :=
    strHom_eq (f := q') fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = e :=
    (topologicalKrullDim_red Z).trans hdim
  have hpos := ((hNN.2.2.isBig_iff (hstr ▸ hpq) hD (hNef.pull_of_isClosedImmersion _ hi)).1 hb)
  have heq : interNumRed k Z (fun _ : Fin e => N) = topSelfIntersection k (N.pull (redι Z)) e :=
    interNumOn_const_eq_topSelf hi hN e
  omega

end GlobalTheory.PosThrough
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    A.dim = B.dim → B.dim = C.dim →
      (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hAB hBC
  have hleft : (f ≫ g).hom.left = f.hom.left ≫ g.hom.left := by
    rw [comp_hom, Over.comp_left]
  have key : IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g := by
    constructor
    · rintro ⟨hfin, hsurj⟩
      have hs2 : Surjective (f.hom.left ≫ g.hom.left) := by rw [← hleft]; exact hsurj
      have hgs : Surjective g.hom.left := Surjective.of_comp f.hom.left g.hom.left
      have hgf : IsFinite g.hom.left := GlobalTheory.T.isFinite_of_surjective_of_dim_eq' K B C g hBC hgs
      have hker : Finite (ptMap (f ≫ g)).ker := (GlobalTheory.T.isFinite_iff_finite_ker' K A C (f ≫ g)).1 hfin
      have hle : (ptMap f).ker ≤ (ptMap (f ≫ g)).ker := by
        intro x hx
        rw [MonoidHom.mem_ker] at hx ⊢
        have hx' : x ≫ f.hom = 1 := hx
        show x ≫ (f ≫ g).hom = 1
        rw [comp_hom, ← Category.assoc, hx', MonObj.one_comp]
      have hfk : Finite (ptMap f).ker :=
        Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      have hff : IsFinite f.hom.left := (GlobalTheory.T.isFinite_iff_finite_ker' K A B f).2 hfk
      exact ⟨⟨hff, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f hAB hff⟩, ⟨hgf, hgs⟩⟩
    · rintro ⟨hf, hg⟩
      exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g hf hg).1
  refine ⟨key, ?_⟩
  by_cases h : IsIsogeny f ∧ IsIsogeny g
  · exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g h.1 h.2).2
  · have h0 : deg (f ≫ g) = 0 := by
      unfold deg; rw [if_neg (fun h' => h (key.1 h'))]
    rw [h0]
    rcases not_and_or.1 h with hf | hg
    · have : deg f = 0 := by unfold deg; rw [if_neg hf]
      rw [this, zero_mul]
    · have : deg g = 0 := by unfold deg; rw [if_neg hg]
      rw [this, mul_zero]
end
