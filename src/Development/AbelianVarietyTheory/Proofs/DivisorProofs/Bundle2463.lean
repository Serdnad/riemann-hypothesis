module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.SigmaMonoInConstant
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle934
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.NumSizes

theorem r_log_div_le (r t q : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hq : 4 * t * r + 1 < q) :
    (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  set Q : ℝ := 4 * t * r + 2 with hQ
  have hqQ : Q ≤ q := by rw [hQ]; exact_mod_cast (by omega : 4 * t * r + 2 ≤ q)
  have hQ6 : (6:ℝ) ≤ Q := by rw [hQ]; nlinarith
  have he : Real.exp 1 ≤ Q := by have := Real.exp_one_lt_d9; linarith
  have hant : Real.log q / q ≤ Real.log Q / Q :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hqQ)) hqQ
  have hq0 : (0:ℝ) < q := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have s1 : (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ (r : ℝ) * Real.log q / ((q : ℝ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have s2 : (r : ℝ) * Real.log q / ((q : ℝ) / 2) = 2 * r * (Real.log q / q) := by
    field_simp
  have s3 : 2 * (r : ℝ) * (Real.log Q / Q) ≤ 2 * Real.log Q := by
    have hrQ : (r : ℝ) ≤ Q := by rw [hQ]; nlinarith
    have hQ0 : (0:ℝ) < Q := by linarith
    rw [mul_div_assoc', div_le_iff₀ hQ0]
    nlinarith
  have s4 : Real.log Q ≤ Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
    have h6 : Q ≤ 6 * ((r : ℝ) + t) ^ 2 := by rw [hQ]; nlinarith
    calc Real.log Q ≤ Real.log (6 * ((r : ℝ) + t) ^ 2) := Real.log_le_log (by linarith) h6
      _ = Real.log 6 + 2 * Real.log ((r : ℝ) + t) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  calc (r : ℝ) * Real.log q / ((q : ℝ) - 1) ≤ 2 * r * (Real.log q / q) := s1.trans s2.le
    _ ≤ 2 * r * (Real.log Q / Q) := mul_le_mul_of_nonneg_left hant (by positivity)
    _ ≤ 2 * Real.log Q := s3
    _ ≤ 2 * Real.log 6 + 4 * Real.log ((r : ℝ) + t) := by linarith

theorem sq_le_dim (f r m : ℕ) (hf : 2 ≤ f) (hr : 2 ≤ r) (hm : 2 ≤ m) : r ^ 2 ≤ m * (f * r.choose 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have h : (s + 2).choose 2 * 2 = (s + 2) * (s + 1) := by
    have := Nat.add_one_mul_choose_eq (s + 1) 1
    rw [Nat.choose_one_right] at this
    exact this.symm
  have h4 : 2 * (2 * (s + 2).choose 2) ≤ m * (f * (s + 2).choose 2) :=
    Nat.mul_le_mul hm (Nat.mul_le_mul hf le_rfl)
  nlinarith

variable {D : D7} {L : SizeData₂ D}

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem ranks_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    1 ≤ T.PP ∧ (D.R.f : ℝ) * D.R.r ≤ L.sc.b ∧ (D.R.r : ℝ) + D.R.t ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hL := one_le_L L.sc
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hZ : (D.R.f : ℝ) * D.R.r ≤ zBase L := le_mul_of_one_le_right (by positivity) hL
  have hZ1 : 1 ≤ zBase L := hfr.trans hZ
  have hZP : zBase L ≤ T.PP := by
    rw [T.PP_eq]
    have a : zBase L ≤ zBase L ^ T.eP := Real.self_le_rpow_of_one_le hZ1 (by linarith [T.eP_ge])
    exact a.trans (le_mul_of_one_le_left (by linarith) T.one_le_CP)
  have hPP : 1 ≤ T.PP := hZ1.trans hZP
  have hTO : (1 : ℝ) ≤ T.TO := by exact_mod_cast (by have := T.TO_40; omega : 1 ≤ T.TO)
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hs : (T.TO : ℝ) * T.PP ≤ L.sc.b := T.TO_PP'.trans (Real.rpow_le_self_of_one_le hb (by norm_num))
  have hP2 : T.PP ≤ (T.TO : ℝ) * T.PP := le_mul_of_one_le_left (by linarith) hTO
  refine ⟨hPP, by linarith, ?_⟩
  have e1 : (D.R.r : ℝ) + D.R.t = T.nP + T.TO * T.nWn := by exact_mod_cast T.split
  have e2 : (T.nP : ℝ) ≤ T.nWn := by exact_mod_cast T.nW_lo.2.2
  have e3 : (T.TO : ℝ) * T.nWn ≤ T.TO * T.PP := mul_le_mul_of_nonneg_left T.nW_le (by linarith)
  linarith [T.nW_le]

variable {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem unitE_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem dim_eq : GlobalTheory.CompHt.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  exact GlobalTheory.SlopeRec.dimFlag_eq p.fw.laws.pins ⟨Nat.le_add_left 1 i, i.2⟩

theorem lenT_mul_le {P : ParameterChoice' D L} (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3 ≤ 2 * L.sc.b := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; omega
  have hsq := sq_le_dim D.R.f D.R.r D.R.m (by unfold Ranks.f; omega) hr2 h1
  rw [← T.Dp_eq] at hsq
  have hD1 : 1 ≤ T.Dp := by
    rcases Nat.eq_zero_or_pos T.Dp with h | h
    · rw [h] at hsq; nlinarith
    · exact h
  have hsq' : (D.R.r : ℝ) ^ 2 ≤ D.R.m * T.Dp := by exact_mod_cast hsq
  have hD : (1 : ℝ) ≤ T.Dp := by exact_mod_cast hD1
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hPP := (ranks_le T).1
  have hW : (1 : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) (one_le_pow₀ hD)) hk
  have hlen : (lenT p i T.PP : ℝ) ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) := by
    unfold lenT
    rw [dim_eq, ← T.Dp_eq]
    have a := (Nat.ceil_lt_add_one (a := T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m) (by positivity)).le
    have b : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k := div_le_self (by linarith) hm
    linarith
  have hr3 : (D.R.r : ℝ) ^ 3 ≤ D.R.r * (D.R.m * T.Dp) := by
    rw [pow_succ']; exact mul_le_mul_of_nonneg_left hsq' (by positivity)
  have hb : (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 ≤ L.sc.b := by
    refine le_trans ?_ T.b_ge
    have : T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3 =
      T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) T.CbN_ge
  calc (lenT p i T.PP : ℝ) * (D.R.r : ℝ) ^ 3
      ≤ 2 * (T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k) * (D.R.r * (D.R.m * T.Dp)) :=
        mul_le_mul hlen hr3 (by positivity) (by linarith)
    _ = 2 * ((D.R.r : ℝ) * D.R.m * D.R.k * T.PP ^ 2 * (T.Dp : ℝ) ^ 3) := by ring
    _ ≤ 2 * L.sc.b := by linarith

theorem numAt {P : ParameterChoice' D L} (T : ParamsT D L P) (hll : 1 ≤ Real.log (Real.log L.sc.x)) :
    NumAt p i T.PP (|L.Ct| + 20) := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 := D.R.rank_add_five_le
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hL := one_le_L L.sc
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hC := abs_nonneg L.Ct
  obtain ⟨-, hfr, hrt⟩ := ranks_le T
  have hCL : 20 * L.sc.L ≤ (|L.Ct| + 20) * L.sc.L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hlr : Real.log D.R.r ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_left (by linarith) hf).trans hfr)
  have hlf : Real.log D.R.f ≤ L.sc.L :=
    hlb ▸ Real.log_le_log (by linarith) ((le_mul_of_one_le_right (by linarith) hr).trans hfr)
  refine ⟨hL, hb, by linarith, hll, ?_, ?_, by linarith, ?_, ?_, ?_⟩
  · rw [unitE_eq]
    refine le_mul_of_one_le_left ?_ (by linarith)
    have : 0 ≤ L.sc.L := by linarith
    have : 0 ≤ Real.log (Real.log L.sc.x) := by linarith
    positivity
  · have hx := L.sc.one_lt_alt
    have hlx : 0 < Real.log L.sc.x := Real.log_pos hx
    have hk : (2 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 2 ≤ D.R.k)
    have hkt : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
    have a : Real.log D.R.k ≤ L.Ct * Real.log L.sc.x := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (hkt.trans L.t_win.2)
    have b : Real.log D.R.k ≤ (|L.Ct| + 1) * Real.log L.sc.x :=
      a.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self L.Ct]) hlx.le)
    have c := Real.log_le_log (Real.log_pos (by linarith)) b
    rw [Real.log_mul (by linarith) hlx.ne'] at c
    have d := Real.log_le_sub_one_of_pos (by linarith : 0 < |L.Ct| + 1)
    nlinarith
  · have hQ : (D.host.QS : ℝ) ≤ (D.R.f : ℝ) ^ 2 := by
      have := D.host.QS_le
      exact_mod_cast this.trans (Nat.pow_le_pow_left (by unfold Ranks.f; omega) 2)
    have hQ0 : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
    have a := Real.log_le_log hQ0 hQ
    rw [Real.log_pow] at a
    push_cast at a
    have h2' := Real.log_two_gt_d9
    unfold Formalism.MainNotions.DIV.Cons.vd2
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  · exact (lenT_mul_le p i T).trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  · intro q hq
    have hq' : 4 * D.R.t * D.R.r + 1 < q := by
      rcases Finset.mem_insert.1 hq with h | h
      · exact h ▸ D.host.qd_big.1
      · exact (Finset.mem_singleton.1 h) ▸ D.host.qd_big.2
    have a := r_log_div_le D.R.r D.R.t q hr1 (by omega) hq'
    have b : Real.log ((D.R.r : ℝ) + D.R.t) ≤ Real.log 2 + L.sc.L := by
      rw [← hlb, ← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) hrt
    have c := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    have d := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have e : (|L.Ct| + 20) * L.sc.L ≤ (|L.Ct| + 20) * D.R.m * L.sc.L :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hm) (by linarith)
    linarith

end GlobalTheory.RefSum.NumSizes

end
end

section

namespace LeafFixedPointPairing
section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw matLat)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.IndefR.Datum Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_localization_of_smul_mem₂ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    (M : Submodule (𝓞 K) (Fin n → K)) (y : Fin n → K) (s : K) (hs : s ≠ 0) (δ : ℤ) (hv : vw w s ≤ δ) (h : s • y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
      (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-δ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) := by
  obtain ⟨t, ht, hc⟩ := unit_at_val w s hs
  have h1 : s • y ∈ Formalism.HermitianLatticesTheory.idealSmul
      (((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K) M := by
    refine Submodule.subset_span ⟨1, ?_, s • y, h, (one_smul _ _).symm⟩
    exact FractionalIdeal.mem_coe.mpr (FractionalIdeal.one_mem_one _)
  have hm := smulK_mem_idealSmul _ _ M _ hc h1
  rw [one_mul] at hm
  have e : (algebraMap (𝓞 K) K t * s⁻¹) • s • y = t • y := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one, algebraMap_smul]
  rw [e] at hm
  exact GlobalTheory.FinitePlacesCompare.scaledAt_anti w M (neg_le_neg hv)
    ((PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨t, ht, hm⟩)

variable {D : D7}

theorem absNorm_splitAuxiliaryPlace_eq_prime {T : Type} {Lc : LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) :
    Ideal.absNorm P.v0.asIdeal = GlobalTheory.ChiGrid.q0 D := by
  have hp := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  have h : (Ideal.primesOver (Ideal.span {((GlobalTheory.ChiGrid.q0 D : ℕ) : ℤ)}) (𝓞 D.host.E)).ncard =
      Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact Formalism.L2.Host.split_prime_splits_completely D
  have := P.v0.isPrime
  have := (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) (E := D.host.E) hp h P.v0.asIdeal P.basePlace_over_qZero).2
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact this

theorem one_le_b (s : Formalism.BasicNotions.Scale) : 1 ≤ s.b := by
  have h : 0 ≤ s.L := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  exact Real.one_le_exp h

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem sig_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hC : CF ≤ C) :
    sig d.G ≤ (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  refine le_trans (le_of_eq ?_) (GlobalTheory.FinitePlacesProbe.sigma_mono_in_constant _ hC hb)
  show _ = ∑ q ∈ d.G.pl.S0, ((d.O.ee CF p.Z.b q : ℕ) : ℝ) * Real.log (Ideal.absNorm q.asIdeal)
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [GlobalTheory.BigTop.Fun.Model.ee_eq d (absNorm_splitAuxiliaryPlace_eq_prime d.G.pl) v]

theorem local_clause {p : PtAt ex Csz} {CF : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a)
    {dl : GlobalTheory.SumSize.PlL D → ℝ} (hloc : ∀ X' M, IsTestLat a.ch.G a.ch.rp a.ch.n a.ch.e X' M →
      ∀ t w, Away a.ch.G t w → ∀ x ∈ (p.P.A3.A.fam.R t).Mt (p.P.A3.A.fam.lvl p.F.lv2.P0 p.F.lv2.ψ0), ∀ y : Fin a.ch.n → D.what₂.LL,
        (∀ i, D.what₂.embLL (y i) = vK a.ch t (formOf p.F.lv2 t x) i) → ∃ s : D.what₂.LL, s ≠ 0 ∧ (vw w s : ℝ) ≤ dl w ∧ s • y ∈ M)
    (hAw : AwayAt (R := p.R.toRealDat) a.ch) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) (w : GlobalTheory.SumSize.PlL D) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ((d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w)) ((Df p).Mt ((p.S false).μ w))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-((d.data (fun _ => 1) Tf dF).dF w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (d.data (fun _ => 1) Tf dF).M) := by
  intro z hz
  obtain ⟨s0, hs0, hz0⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hz
  obtain ⟨x, hx, hxz⟩ := Submodule.mem_map.mp hz0
  have e0 : (d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w) = d.V ((p.S false).μ w) := by
    show (1 : D.what₂.LL)⁻¹ • d.V _ = _
    simp
  simp only [LinearMap.coe_restrictScalars, e0] at hxz
  obtain ⟨s, hs, hv, hsM⟩ := hloc d.X' d.M hT.test ((p.S false).μ w) w (hAw w) x hx (d.V _ |>.mulVec x)
    (fun i => hT.sums _ (Or.inr ⟨w, rfl⟩) x i)
  have hy := mem_localization_of_smul_mem₂ w d.M _ s hs (dF w) (by rw [hF]; exact Int.le_floor.mpr hv) hsM
  obtain ⟨s1, hs1, h1⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hy
  refine (PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨s1 * s0, w.asIdeal.primeCompl.mul_mem hs1 hs0, ?_⟩
  rw [mul_smul, ← hxz]
  exact h1

theorem sum_clause {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) {dl : GlobalTheory.SumSize.PlL D → ℝ}
    (hsum : ∀ s : Finset (GlobalTheory.SumSize.PlL D), ∑ w ∈ s, lw w * dl w ≤ D.R.m * bOne d.G C p.Z.b / 2)
    (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) :
    2 * ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ (d.data (fun _ => 1) Tf dF).bFP C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  have hb0 : 0 ≤ p.Z.b := by linarith
  have hL : 0 ≤ Real.log p.Z.b := Real.log_nonneg hb
  have h1 : ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ ∑ w ∈ Tf, lw w * dl w := by
    refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (GlobalTheory.FinitePlacesCompare.lw_nonneg w)
    rw [hF]
    exact Int.floor_le _
  have h2 := hsum Tf
  have hS := sig_le d Tf dF hC
  have hS0 := Sig0_nonneg (d.data (fun _ => 1) Tf dF) C p.Z.b
  have hN : (d.data (fun _ => 1) Tf dF).N = bigN D := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bFP
  rw [hN]
  show _ ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * _) +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + _) * p.Z.b
  set S := (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b
  have h3 : 0 ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * S) := by
    positivity
  have h4 : (D.R.m : ℝ) * bOne d.G C p.Z.b ≤ C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + S) * p.Z.b := by
    unfold bOne
    have : (D.R.m : ℝ) * (C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b) =
        C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b := by ring
    rw [this]
    gcongr
  linarith

theorem leaf_at {p : PtAt ex Csz} {CF C : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a) (hC0 : 0 ≤ C) (hC : CF ≤ C)
    (hFin : FinAt p.F.lv2 a.ch C p.Z.b) (hAw : AwayAt (R := p.R.toRealDat) a.ch) :
    ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b := by
  classical
  obtain ⟨dl, ⟨-, hfin, hsum⟩, hloc⟩ := hFin
  refine ⟨hfin.toFinset, fun w => ⌊dl w⌋, ?_, fun w hw => ?_, ?_⟩
  · exact local_clause hT hloc hAw _ _ (fun _ => rfl)
  · have hw' : w ∉ hfin.toFinset := hw
    have : dl w = 0 := by simpa using hw'
    show ⌊dl w⌋ = 0
    simp [this]
  · exact sum_clause d hC0 hC hsum _ _ (fun _ => rfl)

end GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

end

end

end LeafFixedPointPairing
section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.DegPrime

theorem pow_comp_mon {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem pow_prime_pow {K : Type} [Field K] (l : ℕ) {A B : AbVar K} (f : A ⟶ B)
    (hf : ∀ x : A.Pt, x ^ l = 1 → x ≫ f.hom = 1 → x = 1) :
    ∀ (b : ℕ) (x : A.Pt), x ^ (l ^ b) = 1 → x ≫ f.hom = 1 → x = 1 := by
  intro b
  induction b with
  | zero => intro x hx _; simpa using hx
  | succ b ih =>
    intro x hx hxf
    apply ih x _ hxf
    apply hf (x ^ (l ^ b))
    · rw [← pow_mul, ← pow_succ]; exact hx
    · rw [pow_comp_mon, hxf, one_pow]

end GlobalTheory.AV.AbVar.DegPrime

theorem GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (h : A ⟶ B), IsIsogeny h → (∀ x : A.Pt, x ^ l = 1 → x ≫ h.hom = 1 → x = 1) →
      ¬ l ∣ deg h := by
  intro K _ l hl hlK A B h hh hker
  have hp : l.Prime := hl.out
  obtain ⟨hdim, -, -, -⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B h hh
  obtain ⟨N, hN, hkill⟩ := GlobalTheory.AV.KerKill.kernel_killed K A B h hh.1
  obtain ⟨b, m, hlm, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.ne_one
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hNm; omega
    · exact h0
  have hlb : ((l ^ b : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK
  have hpts := GlobalTheory.AV.TorsKer.pow_eq_one_of_points K A B h (l ^ b) 1 hlb
    (fun x hx hxf => by rw [pow_one]; exact GlobalTheory.AV.AbVar.DegPrime.pow_prime_pow l h hker b x hx hxf)
  have hkm : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ h.hom = 1 → x ^ m = 1 := by
    intro T x hx
    have h1 : (x ^ m) ^ (l ^ b) = 1 := by
      rw [← pow_mul, mul_comm, ← hNm]; exact hkill T x hx
    have h2 : (x ^ m) ≫ h.hom = 1 := by
      rw [GlobalTheory.AV.AbVar.DegPrime.pow_comp_mon, hx, one_pow]
    simpa using hpts T (x ^ m) h1 h2
  have hB := B.smooth
  have hA := A.smooth
  rw [hdim] at hA
  obtain ⟨h', hh', hhh', -⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A.X B.X B.dim A.ab B.ab hA hB
    h.hom inferInstance m hm hkm
  let g : B ⟶ A := Hom.mk (A := B) (B := A) h' (h := hh')
  have e1 : h ≫ g = ((m : ℤ)) • 𝟙 A := by
    apply Subtype.ext
    change h.hom ≫ h' = (𝟙 A.X) ^ (m : ℤ)
    simpa using hhh'
  obtain ⟨-, hdeg⟩ := GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A B A h g hdim hdim.symm
  obtain ⟨-, hdm⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A (m : ℤ) (by exact_mod_cast hm.ne')
  rw [e1, hdm, Int.natAbs_natCast] at hdeg
  intro hdvd
  have : l ∣ m ^ (2 * A.dim) := by rw [hdeg]; exact Dvd.dvd.mul_right hdvd _
  exact hlm (hp.dvd_of_dvd_pow this)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_torsionFree : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  intro K _ A B n f hn h
  have hs := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A n hn).1.2
  refine GlobalTheory.T.cancel_of_surjective_abelianVarietyHom K A A (n • 𝟙 A) hs B f 0 ?_
  rw [Preadditive.zsmul_comp, Category.id_comp, Limits.comp_zero, h]

end GlobalTheory.AV.AbVar
end
