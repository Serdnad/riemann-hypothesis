module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle986
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.CovHt.GeomBound

theorem strictAnti_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) h')
    · subst h'
      exact h ⟨a, ha⟩ ⟨a + 1, hb⟩ rfl

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem quo_gaps {PP A M : ℝ} (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) :
    ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) ≤ u1 τ a - u1 τ b := by
  obtain ⟨hsig1, hsig2, hsigr⟩ := hw.sig
  obtain ⟨h0, S, eta, -, -, -, h4T, -, hHyp⟩ := hw.hyp hi
  have hdiv := (quo_iff p i PP h0 S eta u1).1 hu
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ (hHyp u1) hdiv
  simp only [wtsAt] at G
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hr2 : 2 ≤ D.R.r := by omega
  have hD1 : 1 ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact Nat.mul_pos (by have := hN.f8; omega) (Nat.choose_pos hr2)

  have hz : (4 : ℝ) ≤ zBase L := by
    unfold zBase
    have c1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
    have c2 : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr2
    have c3 : (10 : ℝ) ≤ L.sc.L := hN.big.2.1
    have : (8 : ℝ) * 2 * 10 ≤ D.R.f * D.R.r * L.sc.L := by gcongr
    linarith
  have hPP : (4 : ℝ) ≤ PP := hz.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hN.ppLow)
  have hT : 16 * dimFlag (dat p i) ^ 2 ≤ lenT p i PP := by
    have h1 : (16 * dimFlag (dat p i) ^ 2 : ℝ) ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      have c3 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      have c4 : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
      have c5 : (16 : ℝ) ≤ PP ^ 2 := by nlinarith
      rw [le_div_iff₀ c3]
      have c6 : (0 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := by positivity
      calc (16 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m ≤ (PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) c3.le
        _ ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k := mul_le_mul_of_nonneg_left c4 (by positivity)
    have h2 := h1.trans (Nat.le_ceil _)
    unfold lenT
    exact_mod_cast h2
  intro τ a b hb
  obtain ⟨g1, g2, -⟩ := G τ a b hb
  have hTz : (16 * (dimFlag (dat p i) : ℤ) ^ 2) ≤ (lenT p i PP : ℤ) := by exact_mod_cast hT
  have hD1z : (1 : ℤ) ≤ dimFlag (dat p i) := by exact_mod_cast hD1
  have hsq : (dimFlag (dat p i) : ℤ) ≤ (dimFlag (dat p i) : ℤ) ^ 2 := by nlinarith
  push_cast at G ⊢
  by_cases hbp : (b : ℕ) = (dat p i).p
  · have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by nlinarith
    have hle : (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    push_cast at hle
    linarith
  · have g := g1 hbp
    push_cast at g
    linarith

end Point

end GlobalTheory.CovHt.GeomBound

end
end

section



open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.ShortPf

theorem budget_arith {f r l b PP T d ρ s : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hP : (f * r * l) ^ 12 ≤ PP)
    (hd : 1 ≤ d) (hT : d ^ 2 * PP ≤ T) (hTb : T ≤ b) (hρ : 0 ≤ ρ) (hρ1 : d * ρ * PP ≤ 6 * r ^ 2) (hs : 0 ≤ s)
    (hs1 : T * s ≤ 8 * f * r * b) :
    ((f * r * l) ^ 3 * s + (f * r * l) ^ 5) * (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) ≤ 693 * (f * b) := by
  have hrZ : r ≤ f * r * l := by
    calc r = 1 * r * 1 := by ring
      _ ≤ _ := by gcongr
  generalize f * r * l = Z at *
  have hZ : 1 ≤ Z := hr.trans hrZ
  have h7 : Z ^ 7 ≤ PP := (pow_le_pow_right₀ hZ (by norm_num)).trans hP
  have hP0 : 0 < PP := lt_of_lt_of_le (by positivity) h7
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hb0 : 0 < b := hT0.trans_le hTb
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have e : T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = 7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ := by field_simp
  have hF : (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) * PP ≤ 77 * (r ^ 2 * T) := by
    rw [e]
    have a1 : d ≤ d ^ 2 := le_self_pow₀ hd (by norm_num)
    have a2 : ρ ≤ d * ρ := le_mul_of_one_le_left hρ hd
    have a3 : 6 * d + 10 + (7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ) ≤ 23 * d ^ 2 + 9 * T * (d * ρ) := by
      nlinarith [mul_le_mul_of_nonneg_left a2 hT0.le]
    have a4 := mul_le_mul_of_nonneg_right a3 hP0.le
    have a5 := mul_le_mul_of_nonneg_left hρ1 hT0.le
    have a6 : T ≤ r ^ 2 * T := le_mul_of_one_le_left hT0.le hr2
    nlinarith
  generalize 6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = F at hF ⊢
  refine le_of_mul_le_mul_right ?_ hP0
  have b1 : (Z ^ 3 * s + Z ^ 5) * (F * PP) ≤ (Z ^ 3 * s + Z ^ 5) * (77 * (r ^ 2 * T)) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have b2 : Z ^ 3 * r ^ 2 * (T * s) ≤ Z ^ 3 * r ^ 2 * (8 * f * r * b) := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have b3 : Z ^ 3 * r ^ 3 ≤ PP := by
    calc Z ^ 3 * r ^ 3 ≤ Z ^ 3 * Z ^ 4 :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by linarith) hrZ 3).trans (pow_le_pow_right₀ hZ (by norm_num)))
            (by positivity)
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b4 : Z ^ 5 * r ^ 2 ≤ PP := by
    calc Z ^ 5 * r ^ 2 ≤ Z ^ 5 * Z ^ 2 := by gcongr
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b5 : Z ^ 3 * r ^ 3 * (f * b) ≤ PP * (f * b) := mul_le_mul_of_nonneg_right b3 (by positivity)
  have b6 : Z ^ 5 * r ^ 2 * T ≤ PP * (f * b) :=
    mul_le_mul b4 (hTb.trans (le_mul_of_one_le_left hb0.le hf)) hT0.le hP0.le
  nlinarith

theorem len_mul_l1_le {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hW : W.Hyp) (hD : W.IsDiv) :
    (W.T : ℝ) * GlobalTheory.MeanTop.l1 W.u1 ≤ Fintype.card ι * (N * (2 * W.b)) := by
  refine (GlobalTheory.MeanTop.divided_weight_size _ _ W hW hD).1.trans ?_
  have h : ∑ τ, ∑ k, (|(W.u τ k : ℝ)| + W.c0 + 4 * N) ≤ ∑ _τ : ι, ∑ _k : Fin N, 2 * W.b :=
    Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.h5 τ k
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold GlobalTheory.MeanTop.l1
  linarith

theorem fieldSz_host {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) : fieldSz D.host.E ≤ 3 * L.sc.L := by
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8
  have hr : (2 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  unfold fieldSz
  rw [h.deg]
  push_cast
  have a1 : Real.log (2 * (D.R.f : ℝ)) ≤ Real.log ((D.R.f : ℝ) * D.R.r) := Real.log_le_log (by linarith) (by nlinarith)
  have a2 : Real.log |(discr D.host.E : ℝ)| / (2 * (D.R.f : ℝ)) ≤ 2 * L.sc.L := by
    rw [div_le_iff₀ (by linarith)]
    linarith [h.disc]
  linarith [h.logfr.1]

theorem log_level {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) :
    Real.log ((D.host.g 0 * D.host.g 1 * 15 ^ expL L.sc.L : ℕ) : ℝ) ≤ 30 * L.sc.L := by
  have hL := h.big.2.1
  have g0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have g1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have a1 : (expL L.sc.L : ℝ) * Real.log 3 ≤ 3 * L.sc.L :=
    (le_div_iff₀ l3).1 (Nat.floor_le (div_nonneg (by linarith) l3.le))
  have a2 : Real.log 15 ≤ 3 * Real.log 3 := by
    have : Real.log ((3 : ℝ) ^ 3) = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have a3 := mul_le_mul_of_nonneg_left a2 (Nat.cast_nonneg (α := ℝ) (expL L.sc.L))
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul g0.ne' g1.ne', Real.log_pow]
  linarith [h.logg 0, h.logg 1]

section Point

open _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)



theorem weight_rows {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ u1 τ a - u1 τ b) ∧
    Real.log (∑ τ, ∑ k, |(u1 τ k : ℝ)|) ≤ 10 * L.sc.L ∧
    (((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 5) *
      (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ 693 * unitE p := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hw.hyp hi
  have hW := hH u1
  have hD := (quo_iff p i PP h0 S eta u1).1 hq
  have m2 := D.R.two_le_m
  have k3 := D.R.m_add_three_le_k
  have f8 := h.f8
  have hL := h.big.2.1
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f8
  have hr : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hcard : Fintype.card (Psi p.T.Q.H) = D.R.f := by rw [← hw.card, Nat.card_eq_fintype_card]
  have hDd : (1 : ℝ) ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
  have hT : (1 : ℝ) ≤ lenT p i PP := by
    have : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hP : ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 12 ≤ PP := h.ppLow
  have hZ : (160 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * L.sc.L := by
    calc (160 : ℝ) = 8 * 2 * 10 := by norm_num
      _ ≤ _ := by gcongr
  have hP1 : 160 ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hP)
  have kp : (wtsAt p i PP h0 S eta u1).kc < (dat p i).p := hW.kc_lt
  have pq : (dat p i).p < (dat p i).p + (dat p i).q := hW.p_lt
  have s0 : 0 ≤ ∑ τ, ∑ k, |(u1 τ k : ℝ)| := by positivity
  have s1 : (lenT p i PP : ℝ) * ∑ τ, ∑ k, |(u1 τ k : ℝ)| ≤ 8 * D.R.f * D.R.r * L.sc.b := by
    have := len_mul_l1_le _ hW hD
    rw [hcard, show (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r by rw [hw.sig.2.2]] at this
    refine le_trans this (le_of_eq ?_)
    show (D.R.f : ℝ) * (D.R.r * (2 * (4 * L.sc.b))) = _
    ring
  have h1 : PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) ≤ h0 := by
    refine le_trans ?_ hh
    have a1 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have a2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := one_le_pow₀ hm
    calc _ = PP * lenT p i PP * D.R.r * D.R.f * 1 * 1 * dimFlag (dat p i) := by ring
      _ ≤ _ := by gcongr; linarith
  refine ⟨by omega, by omega, fun τ => (GlobalTheory.MeanTop.divided_strictAnti _ _ _ hW hD τ).1.antitone, fun τ a b hab hb' => ?_, ?_, ?_⟩
  · have g : h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := ((GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab).2.1 hb').1
    have g' : (h0 : ℝ) ≤ 2 * (lenT p i PP : ℝ) * ((u1 τ a : ℝ) - u1 τ b) := by exact_mod_cast g
    have a1 : 160 * lenT p i PP * D.R.r * D.R.f * 1 ≤ PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) := by gcongr
    have a2 : 80 * ((D.R.f : ℝ) * D.R.r) ≤ (u1 τ a : ℝ) - u1 τ b := by
      refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 2 * lenT p i PP by linarith)
      linarith
    have a3 : (16 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    have a4 : 8 * (D.R.f : ℝ) * D.R.r + 10 ≤ (u1 τ a : ℝ) - u1 τ b := by linarith
    exact_mod_cast a4
  · rcases s0.eq_or_lt with e | e
    · rw [← e, Real.log_zero]; linarith
    have a1 := Real.log_le_log e ((le_mul_of_one_le_left s0 hT).trans s1)
    rw [mul_assoc 8, Real.log_mul (by positivity) hb.ne', Real.log_mul (by norm_num) (by positivity),
      show Real.log L.sc.b = L.sc.L from Real.log_exp _] at a1
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num), h.logfr.1]
  · obtain ⟨r0, -, r2⟩ := GlobalTheory.CovTop.SizeRows.rho_bounds _ hW hD
    have er : rhoOf (wtsAt p i PP h0 S eta u1).u' (wtsAt p i PP h0 S eta u1).u1 = rhoB (dat p i) u1 := by
      unfold rhoB
      congr 1
      funext τ k
      rw [uPrime_apply]; rfl
    rw [er] at r0 r2
    have r3 : rhoB (dat p i) u1 * h0 ≤ 6 * D.R.f * (D.R.r : ℝ) ^ 3 * lenT p i PP := by
      rw [← hcard, ← hw.sig.2.2]; exact r2
    have r4 : dimFlag (dat p i) * rhoB (dat p i) u1 * PP ≤ 6 * (D.R.r : ℝ) ^ 2 := by
      refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < D.R.f * D.R.r * lenT p i PP by positivity)
      linarith [mul_le_mul_of_nonneg_left h1 r0]
    have hTl : (dimFlag (dat p i) : ℝ) ^ 2 * PP ≤ lenT p i PP := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ (by linarith), mul_comm _ PP]
      have : PP ≤ PP ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
      gcongr
    have hTb : (lenT p i PP : ℝ) ≤ L.sc.b := by
      refine le_trans ?_ hw.what₂.2
      have a2 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd
      calc (lenT p i PP : ℝ) = 1 * lenT p i PP * 1 * 1 := by ring
        _ ≤ _ := by gcongr <;> linarith
    refine (budget_arith (by linarith) (by linarith) (by linarith) hP hDd hTl hTb r0 r4 s0 s1).trans ?_
    rw [hw.unit]
    have hll := h.big.2.2.2
    calc 693 * ((D.R.f : ℝ) * L.sc.b) = 693 * (D.R.f * 1 * L.sc.b * 1 * 1) := by ring
      _ ≤ _ := by gcongr; linarith

end Point


end GlobalTheory.CovHt.ShortPf
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_lieBundle_frames_charts_change_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∃ f : ∀ M : GlobalTheory.Reg.MChart Y, Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), (∀ M, GlobalTheory.VB.IsFrame (f M)) ∧ ∀ (M M' : GlobalTheory.Reg.MChart Y) (j : Fin M'.n), GlobalTheory.Twist.resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) = ∑ i, GlobalTheory.FlagMod.chg M M' i j • GlobalTheory.Twist.resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i) := by
  first | exact @GlobalTheory.ChartLieFrame.exists_lieFrame | exact GlobalTheory.ChartLieFrame.exists_lieFrame | (intros; apply GlobalTheory.ChartLieFrame.exists_lieFrame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.primitive_hodge_to_omega_span_mod_maximal :
    GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ),
      IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
      (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ I : Ideal R, I.IsMaximal → LinearMap.range ψ ⊔ I • (⊤ : Submodule R G.omega) = ⊤ :=
  @GlobalTheory.PtExt.psi_sup_smul_top_eq_top
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm

namespace GlobalTheory.NefHodgeTateAt

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_of_cls_eq_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (h : cls N hN = cls A hA + cls B hB) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (N.pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have e2 (L : LB X) : topSelfIntersection κ (L.pull i) 1 = interNum κ (structureModule Z) ![L.pull i] := by
    rw [topSelf_def]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [e2, e2, e2]
  refine interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion i) hd (LB.isLB_pull hN i) (LB.isLB_pull hA i)
    (LB.isLB_pull hB i) ?_
  rw [cls_pull hN, cls_pull hA, cls_pull hB, h, map_add (f := _)]

theorem topSelf_pow (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_of_cls_eq_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_of_cls_eq_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring


end Curves

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Covers

open Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4
open scoped ENNReal Classical

end GlobalTheory.NefHodgeTateAt
end
end

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier
open ReciprocityTheory.AnForm.M

namespace GlobalTheory

theorem IsArithVar.finite_emb_and_topology : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D →
    Finite (k →+* ℂ) ∧ ∀ σ : k →+* ℂ, CompactSpace (CxPts p σ) ∧ T2Space (CxPts p σ) ∧
      SecondCountableTopology (CxPts p σ) := fun h =>
  ⟨h.finite_emb, fun σ => ⟨h.compactSpace σ, CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver,
    CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver⟩⟩

end GlobalTheory
end
