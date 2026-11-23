module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw

namespace GlobalTheory.FlatSplit

section Congr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

theorem lieFacZ_congr (x : ℝ) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : lieFacZ Dw x G = lieFacZ Dw x G' := by
  unfold lieFacZ
  congr 4
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun h (some ⟨τ, i⟩))

theorem lat_congr {C C' : Submodule c.F (Rul Xo c)} (hC : C = C') {N N' : (c.F →+* ℂ) → Rul Xo c → ℝ} (hN : N = N') :
    ((HasGram (fun σ (f : C) => N σ f) ∧ (supLat C).FG ∧ Submodule.span c.F (supLat C : Set C) = ⊤) ↔
      (HasGram (fun σ (f : C') => N' σ f) ∧ (supLat C').FG ∧ Submodule.span c.F (supLat C' : Set C') = ⊤)) ∧
    Formalism.HN.rkK (supLat C) = Formalism.HN.rkK (supLat C') ∧
    slope_sq (fun σ (f : C) => N σ f) (supLat C) = slope_sq (fun σ (f : C') => N' σ f) (supLat C') := by
  subst hC hN
  exact ⟨Iff.rfl, rfl, rfl⟩

theorem congr_exZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') :
    (GoodW U x V dict G ↔ GoodW U x V dict G') ∧ rankW U G = rankW U G' ∧
      slopeW_sq U x V dict G = slopeW_sq U x V dict G' := by
  have hC : cuspW Xo c U G = cuspW Xo c U G' := by
    ext f
    rw [mem_cuspW, mem_cuspW, h]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]
  have hP : petW U x V dict G = petW U x V dict G' := by
    funext σ f
    unfold petW petAt
    rw [lieFacZ_congr x h, modelWt_congr (U (goodOf c σ)) (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) h]
  exact lat_congr hC hP

end Congr

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)

theorem exZ_shift_neg (m kc : ℕ) (c0 : ℤ) :
    exZ Dw (shiftG Dw a (2 * m) (-c0)) =
      exZ Dw (wtOf Dw (uMinus Dw a (2 * m) kc c0 + parWt Dw (anchor Dw a (2 * m) kc)) ((0 : ℤ) + (m : ℤ))) := by
  rw [Model.exZ_shiftG, zero_add, exOf]
  congr 2
  simp only [uMinus, uWt, neg_smul]
  abel

end Weights

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

theorem twice_twist_ge {ι : Type} [Fintype ι] (w c1v : ι → ℝ) (pq q large₂ L b E mT CA lr m0 fr nV lS : ℝ)
    (hc1 : ∀ τ, |c1v τ + pq / 2 * large₂| ≤ 3 * q * L) (hA1 : |mT - ∑ τ, pq * w τ * large₂| ≤ CA * E)
    (hA2 : (∑ τ, |w τ|) * q * L ≤ CA * E) (hq : 0 ≤ q) (hlr : lr ≤ 2 * L) (hL : 10 ≤ L) (hm : 2 * m0 ≤ nV)
    (hm0 : 0 ≤ m0) (hfr : 0 ≤ fr) (hb : fr * nV * L ≤ b) (hbE : b ≤ E) (hLE : L ≤ E) (hlS : lS ≤ 40 * L) :
    -mT - (11 * CA + 83) * E ≤
      2 * ((∑ τ, w τ * c1v τ) - q * lr * (∑ τ, |w τ|) - m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) - lS) := by
  have e1 : ∀ τ ∈ Finset.univ, (-1 / 2) * (pq * w τ * large₂) - (3 * q * L) * |w τ| ≤ w τ * c1v τ := by
    intro τ _
    have h1 : |w τ * (c1v τ + pq / 2 * large₂)| ≤ |w τ| * (3 * q * L) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc1 τ) (abs_nonneg _)
    have h2 := neg_abs_le (w τ * (c1v τ + pq / 2 * large₂))
    have h3 : w τ * c1v τ = w τ * (c1v τ + pq / 2 * large₂) - pq * w τ * large₂ / 2 := by ring
    linarith
  have e2 := Finset.sum_le_sum e1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e2
  have hS2 : 0 ≤ ∑ τ, |w τ| := Finset.sum_nonneg fun τ _ => abs_nonneg _
  have a1 := (abs_le.1 hA1).1
  have a2 : q * lr * (∑ τ, |w τ|) ≤ q * (2 * L) * (∑ τ, |w τ|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlr hq) hS2
  have hpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hpi4 := Real.pi_le_four
  have a3 : Real.log (2 * Real.pi) / 2 + lr ≤ 3 * L := by linarith
  have a4 : m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) ≤ m0 * fr * (3 * L) :=
    mul_le_mul_of_nonneg_left a3 (mul_nonneg hm0 hfr)
  have a5 : 2 * m0 * (fr * (3 * L)) ≤ nV * (fr * (3 * L)) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hfr (by linarith))
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_le {PP A M : ℝ} (hH : HostNum D L PP A M) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have h1 := hH.disc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
  rw [rootDiscr_def]
  push_cast
  rw [Real.log_rpow hd, hH.deg]
  push_cast
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

end GlobalTheory.FlatSplit
end
end

section

set_option autoImplicit false


noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.SizeTZ

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem nCol_le (Dw : Datum H) :
    nCol Dw ≤ (2 * (Dw.p + Dw.q) + 8) * (Module.finrank ℚ E * (Dw.p + Dw.q)) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := GlobalTheory.FactorDepth.rk_le f
    have h' : Dw.mult f.1 ≤ Dw.p + Dw.q := by
      rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := card_Lt1_le_finrank_mul
  have h3 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q)) h2
  have h4 := Nat.mul_div_le (∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f) 8
  unfold nCol
  nlinarith

end Free

variable {D : D7}

theorem two_le_f (D : D7) : 2 ≤ D.R.f := by
  have : 0 < D.R.ord := D.R.ord_pos
  show 2 ≤ 2 * D.R.ord
  omega

theorem six_le_r (D : D7) : 6 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  unfold Ranks.r; omega

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_zBase (L : SizeData₂ D) : 1 ≤ zBase L := by
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by have := six_le_r D; omega : 1 ≤ D.R.r)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) (one_le_scL L)

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem pow_le_PP (T : ParamsT D L P) : zBase L ^ 12 ≤ T.PP := by
  have hZ := one_le_zBase L
  have h1 : zBase L ^ 12 ≤ zBase L ^ T.eP := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)
  rw [T.PP_eq]
  exact h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)

theorem ceil_le_TO (T : ParamsT D L P) :
    ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ ≤ T.TO := by
  refine Nat.ceil_le.2 (le_trans ?_ T.TO_ge)
  have hPP : 1 ≤ T.PP := (one_le_pow₀ (one_le_zBase L)).trans (pow_le_PP T)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hD : (1 : ℝ) ≤ T.Dp := by
    have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos (by have := six_le_r D; omega)
    have h2 : 0 < T.Dp := by rw [T.Dp_eq]; exact Nat.mul_pos (by have := two_le_f D; omega) h1
    exact_mod_cast h2
  have hx : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hd := L.thickDensity_pos
  refine div_le_div₀ (by positivity) ?_ (by positivity) (mul_le_of_le_one_right hm.le L.thickDensity_le_one)
  have e : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp =
      T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) * (T.PP ^ 2 * T.Dp * D.R.f * L.sc.x ^ T.Cp) := by ring
  rw [e]
  exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) hD) hf) hx)

theorem ceil_mul_le_b (T : ParamsT D L P) :
    (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) * zBase L ^ 12 ≤ L.sc.b := by
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (zero_le_one.trans (one_le_scL L))
  have hZ := one_le_zBase L
  have h1 : (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) ≤ T.TO := by exact_mod_cast ceil_le_TO T
  refine (mul_le_mul h1 (pow_le_PP T) (by positivity) (by positivity)).trans (T.TO_PP'.trans ?_)
  exact (Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (Real.rpow_one _).le

theorem lrd_le (P : ParameterChoice' D L) : lrd D.host.E ≤ 3 * L.sc.L := by
  have h := log_rdE_le_scL P
  have e : lrd D.host.E = Real.log D.host.rdE := by
    rw [lrd, rootDiscr_def, Formalism.BasicNotions.Host.rdE, one_div, Int.cast_abs]
  have := one_le_scL L
  rw [e]; linarith

theorem nCol_le_of_pins {T : Par D} (h : T.Pins) {j : ℕ} (hj : InR D j) :
    (nCol (T.Dw j) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h1 := nCol_le (T.Dw j)
  rw [hfr, (GlobalTheory.SlopeRec.sig_eq h hj).2.2] at h1
  have hf := two_le_f D
  have hr := six_le_r D
  have h2 : nCol (T.Dw j) ≤ 20 * D.R.f * D.R.r ^ 2 := by
    refine h1.trans ?_
    generalize D.R.f = f at *
    generalize D.R.r = r at *
    have a1 : f * r * 6 ≤ f * r * r := Nat.mul_le_mul_left _ hr
    have a2 : 2 * 6 ≤ f * r := Nat.mul_le_mul hf hr
    nlinarith
  exact_mod_cast h2

theorem lenT_mul_le_b {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
    (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * zBase L ^ 12 ≤ L.sc.b ∧ (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpin : p.T.Q.Pins := p.fw.laws.pins
  have hD : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := by
    rw [T.Dp_eq]
    refine (GlobalTheory.SlopeRec.dimFlag_eq hpin hj).trans ?_
    simp only [placeRankTwoOne.dimY, Nat.choose_two_right]
  refine ⟨?_, nCol_le_of_pins hpin hj⟩
  rw [lenT, hD]
  exact ceil_mul_le_b T

end GlobalTheory.RefSum.SizeTZ

end
end

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem totallyComplex_core : IsTotallyComplex p.T.Q.c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem goodOf_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have e : (starRingEnd ℂ).comp σ = ComplexEmbedding.conjugate σ := by
    ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [e]; exact _root_.GlobalTheory.CompHt.goodOf_conj (c := c) σ

theorem nrmK_conj (σ : p.T.Q.c.F →+* ℂ) (x : VK p.fw i) :
    nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := by
  simp only [nrmK, normW, petW]
  rw [goodOf_conj']

theorem slopeMax_all_le (Cm : ℝ) (hG : GramAt p i) (hM : MeasAt p i Cm) :
    slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) ≤
      slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) + 2 * (Cm * unitE p) := by
  haveI := totallyComplex_core p
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation D _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  choose c hc0 hcB hcE using hM
  have hAll : latAll p.R.toRealDat i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) : Set (VK p.fw i))) := by
    unfold latAll; rw [h3]
  have hne : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
    intro h0
    apply hG.2.2.1
    refine le_bot_iff.1 ((latGood_le _ _ _).trans ((inf_le_left : latType p.R.toRealDat p.F.lv2 i ≤ latAll p.R.toRealDat i).trans ?_))
    change latAll p.R.toRealDat i ≤ ⊥
    rw [hAll, h0]
    simp
  have key := GlobalTheory.T.maxSlope_sq_fieldExtension_le_comparable_norms p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL) (nrmK p.fw i)
    (nrmR p.R.toRealDat i) ι (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) c (Cm * unitE p) hG.2.2.2.1 hG.1 (nrmK_conj p i) h2
    hG.2.2.2.2.1 hne (fun σ => ⟨hc0 σ, hcB σ⟩) (fun σ x => by
      obtain ⟨h, e⟩ := h1 x
      rw [e]
      exact hcE σ ⟨x, h⟩)
  rw [hAll]
  exact key

theorem unitE_le {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    unitE p ≤ L.sc.x ^ (A + 1) * L.sc.b := by
  rw [hW.unit]
  have hX : 10 ≤ L.sc.x := hH.big.2.1.trans hH.big.2.2.1
  have hX0 : 0 < L.sc.x := by linarith
  have hL0 : 0 ≤ L.sc.L := by linarith [hH.big.2.1]
  have hb : 0 ≤ L.sc.b := le_trans (by positivity) hH.room
  have hlog : Real.log L.sc.x ≤ L.sc.x - 1 := Real.log_le_sub_one_of_pos hX0
  have hlogpos : 0 < Real.log L.sc.x := Real.log_pos (by linarith)
  have hll : Real.log (Real.log L.sc.x) ≤ L.sc.x := by
    have := Real.log_le_sub_one_of_pos hlogpos
    linarith
  have hll0 : 0 ≤ Real.log (Real.log L.sc.x) := by linarith [hH.big.2.2.2]
  have hmr : D.R.m ≤ D.R.r * D.R.nV := by
    have h1 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
    have h2 : 1 ≤ D.R.nV := by have := D.R.two_le_m; unfold Ranks.nV; omega
    exact h1.trans (Nat.le_mul_of_pos_right _ h2)
  have hmr' : (D.R.m : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by exact_mod_cast hmr
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hfm : (D.R.f : ℝ) * D.R.m * L.sc.L ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hmr' hf
    have := mul_le_mul_of_nonneg_right this hL0
    linarith
  have hpoly := hH.poly.2.2
  have hfm0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.L := by positivity
  calc (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
        = ((D.R.f : ℝ) * D.R.m * L.sc.L) * (L.sc.b * Real.log (Real.log L.sc.x)) := by ring
    _ ≤ L.sc.x ^ A * (L.sc.b * L.sc.x) :=
        mul_le_mul (hfm.trans hpoly) (mul_le_mul_of_nonneg_left hll hb) (by positivity) (by positivity)
    _ = L.sc.x ^ (A + 1) * L.sc.b := by rw [Real.rpow_add_one hX0.ne']; ring

theorem le_rpow_of_add {X b A1 A Cm u s : ℝ} (hX : 10 ≤ X) (hb : 0 ≤ b) (hA1 : 0 ≤ A1) (hA : 0 ≤ A) (hCm : 0 ≤ Cm)
    (hu : u ≤ X ^ (A + 1) * b) (hs : s ≤ X ^ A1 * b + 2 * (Cm * u)) :
    s ≤ X ^ (A1 + (A + 1) + (⌈2 * Cm⌉₊ : ℝ)) * b := by
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ X ^ A1 := Real.one_le_rpow (by linarith) hA1
  have hQ : 1 ≤ X ^ (A + 1) := Real.one_le_rpow (by linarith) (by linarith)
  have hK : 1 + 2 * Cm ≤ X ^ (⌈2 * Cm⌉₊ : ℝ) := by
    rw [Real.rpow_natCast]
    have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ X - 1 by linarith) ⌈2 * Cm⌉₊
    have h2 : 2 * Cm ≤ (⌈2 * Cm⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈2 * Cm⌉₊ : ℝ) ≤ (⌈2 * Cm⌉₊ : ℝ) * (X - 1) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
    have h4 : (1 : ℝ) + (X - 1) = X := by ring
    rw [h4] at h1
    linarith
  rw [Real.rpow_add hX0, Real.rpow_add hX0]
  set P := X ^ A1
  set Q := X ^ (A + 1)
  set K := X ^ (⌈2 * Cm⌉₊ : ℝ)
  have e1 : P * b ≤ P * Q * b := by
    have : P ≤ P * Q := le_mul_of_one_le_right (by linarith) hQ
    exact mul_le_mul_of_nonneg_right this hb
  have e2 : 2 * (Cm * u) ≤ 2 * Cm * (P * Q * b) := by
    have : u ≤ P * Q * b := hu.trans (by
      have : Q ≤ P * Q := le_mul_of_one_le_left (by linarith) hP
      exact mul_le_mul_of_nonneg_right this hb)
    nlinarith
  have e3 : P * Q * b * (1 + 2 * Cm) ≤ P * Q * b * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith

end GlobalTheory.CovTop.LamAll
end
end

section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem unitAt_functionFieldMap_of_unitAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.UnitAt (s y) f) :
    _root_.GlobalTheory.Cartier.UnitAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, hunit, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, hunit.map _, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩

set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem regAt_functionFieldMap_of_regAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.RegAt (s y) f) :
    _root_.GlobalTheory.Cartier.RegAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩


set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
theorem _root_.GlobalTheory.Discrepancy.pullCart_supp_and_eff : ∀ (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (D : _root_.GlobalTheory.Cartier.CartierDiv X),
    (∀ y : Y, y ∈ (_root_.GlobalTheory.Discrepancy.pullCart s D).supp →
      s y ∈ D.supp) ∧
    (D.Eff → (_root_.GlobalTheory.Discrepancy.pullCart s D).Eff) := by
  intro X Y _ _ s _ D
  refine ⟨fun y hy => ?_, fun hD => ?_⟩
  · obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hg' := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    rw [hg'.mem_supp_iff] at hy
    rw [hg.mem_supp_iff]
    intro hunit
    exact hy (unitAt_functionFieldMap_of_unitAt s hunit)
  · rw [_root_.GlobalTheory.Cartier.CartierDiv.eff_iff] at hD ⊢
    intro y g' hg'
    obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hpull := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    have hquot := (hpull.iff_unitAt).1 hg'
    have hreg : _root_.GlobalTheory.Cartier.RegAt y
        ((_root_.GlobalTheory.Discrepancy.fnPull s g : (Y.functionField)ˣ) : Y.functionField) :=
      regAt_functionFieldMap_of_regAt s (hD (s y) g hg)
    have hprod := hquot.regAt.mul hreg
    rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at hprod

end GlobalTheory.Discrepancy
end
