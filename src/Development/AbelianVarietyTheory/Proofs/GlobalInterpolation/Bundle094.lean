module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle083
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_primes_conductor : SzRow (fun C D L => (L.sc.x ^ (2 * L.Ct + 5) < (D.host.q : ℝ) ∧ L.sc.x ^ (2 * L.Ct + 5) < (D.host.d : ℝ)) ∧ (L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q) ∧ (|L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps) ∧ ((condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b ^ ((1 : ℝ) / 2)) ∧ (Real.log D.host.pde ≤ L.sc.L ∧ Real.log D.host.pde' ≤ L.sc.L)) := by
  intro eps he he' C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨xh, hh⟩ := hostBounds eps C.P.Cpde he he' hC8
  obtain ⟨xa, ha⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 5) (2 * C.Ct + 5) 1 (1 / 2) 0
    le_rfl (by positivity) (by norm_num)
  obtain ⟨xb, hb⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 30) 0 1 1 0
    le_rfl (by positivity) (by norm_num)
  obtain ⟨xc, hc⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 0 222 (1 / 2) 2
    (by positivity) (by linarith) (by norm_num)
  obtain ⟨xd, hd⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 0 (2 * C.P.Cpde) 1 2
    (by positivity) (by linarith) (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max xh xa) (max xb xc)) (max xd (max (Real.exp 1) (Real.exp C.P.Cpde))), ?_⟩⟩⟩
  intro D L hLe hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hxh, hxa⟩, hxb, hxc⟩, hxd, hxe, hxC⟩ := hx
  obtain ⟨q1, q2, d1, -, hN, -, -, -, p1, p2⟩ := hh L.sc D.R D.host hLe hxh hV.ranks hV.host
  have ha := ha _ hxa
  have hb := hb _ hxb
  have hc := hc _ hxc
  have hd := hd _ hxd
  subst hLe
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hl1 : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hl2 : 1 ≤ Real.log L.sc.x ^ 2 := one_le_pow₀ hl1
  have hPl : L.sc.x ^ (L.sc.eps / 5) ≤ L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_pos_of_pos hx0 _).le hl2
  simp only [Real.rpow_zero, pow_zero, mul_one, one_mul, zero_mul, zero_add] at ha hb hc hd
  have hq0 : (0 : ℝ) < D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 0 < D.host.q)
  have hd0 : (0 : ℝ) < D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 0 < D.host.d)
  have hez : L.sc.eps / C.P.Cpde ≤ L.sc.ez := hostBounds_ez hV.host
  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hZ : 0 < L.sc.x ^ (L.sc.ez / 5) := Real.rpow_pos_of_pos hx0 _
  have ha' : L.sc.x ^ (L.sc.eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hb' : 2 ≤ L.sc.x ^ (L.sc.ez / 30) :=
    le_trans (by linarith) (Real.rpow_le_rpow_of_exponent_le hx1
      (show L.sc.eps / C.P.Cpde / 30 ≤ L.sc.ez / 30 by linarith))
  have hq6 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.ez / 5) / 2 := by
    have e : L.sc.x ^ (L.sc.ez / 5) = L.sc.x ^ (L.sc.ez / 6) * L.sc.x ^ (L.sc.ez / 30) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have h6 : 0 < L.sc.x ^ (L.sc.ez / 6) := Real.rpow_pos_of_pos hx0 _
    have := mul_le_mul_of_nonneg_left hb' h6.le
    linarith
  have hdl : L.sc.x ^ (L.sc.ez / 5) ≤ L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 :=
    le_mul_of_one_le_right hZ.le (one_le_pow₀ (hostBounds_one_le_log_div hV.host hxC))
  have key : ∀ y : ℝ, 0 < y → L.sc.x ^ (L.sc.ez / 5) / 2 ≤ Real.log y →
      L.sc.x ^ (2 * L.Ct + 5) < y := by
    intro y hy h
    rw [hV.Ct_eq, Real.rpow_def_of_pos hx0, ← Real.lt_log_iff_exp_lt hy]
    linarith
  refine ⟨⟨key _ hq0 q1, key _ hd0 (by linarith)⟩, hq6.trans q1, hV.dlog, ?_, ?_, ?_⟩
  · have hn : (1 : ℝ) ≤ D.R.n := by
      exact_mod_cast D.R.ord_pos
    have hk : 2 ≤ D.R.k := by
      have h1 : (1 : ℝ) < L.sc.x ^ (9 / 2 + 10 * L.sc.eps) :=
        Real.one_lt_rpow L.sc.one_lt_alt (by positivity)
      have h2 : (1 : ℝ) < D.R.k := lt_of_lt_of_le h1 hV.ranks.2.2.1.1
      exact_mod_cast h2
    have hr : 1 ≤ D.R.r := by
      unfold Ranks.r; omega
    have ht : D.R.t ≤ D.host.q := by
      have := D.host.qd_big.1
      nlinarith
    have ht' : (D.R.t : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 5)) :=
      le_trans (by exact_mod_cast ht) ((Real.log_le_iff_le_exp hq0).mp q2)
    have hE : (condE D : ℝ) ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) := by
      have hpos : (0 : ℝ) < (D.host.QS : ℝ) * D.host.q * D.host.d := by
        have hQ : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
        positivity
      have := (Real.log_le_iff_le_exp hpos).mp hN
      unfold condE; push_cast; exact this
    calc (condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150
        ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) ^ 36 *
          Real.exp (L.sc.x ^ (L.sc.eps / 5)) ^ 150 := by gcongr
      _ ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
        unfold Scale.b Scale.L
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_mul]
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
  · unfold Scale.L; linarith
  · unfold Scale.L; linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

abbrev baseOfParams {D : D7} (L : SizeData₂ D) : Arith.Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := L.Sc, eta := L.etaSz }

theorem kapISet_eq_loc {D : D7} (L : SizeData₂ D) (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = Arith.Loc.kapISet (baseOfParams L) K p n' TT a b := rfl

theorem sig_eq_loc {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (hk : G.KapIDef X K)
    (hb : ∀ h t, X.bs h t = Arith.bsH h t) (a b : G.HH D → ℤ) (p : ℕ) :
    G.Sig X K a b p =
      Arith.Loc.Sig (baseOfParams L) (Arith.ins (baseOfParams L) K 1) K a b (G.hP D p) p := by
  have hb' : X.bs = Arith.bsH := by funext h t; exact hb h t
  have hk' : X.kapI = (Arith.ins (baseOfParams L) K 1).kapI := by
    funext p n' TT a b
    rw [hk p n' TT a b, kapISet_eq_loc]; rfl
  unfold G.Sig G.goodReps G.reps G.kapv G.kapLoc
  rw [hb', hk']
  rfl

theorem wreq_of_wok : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) → WOK p.L.sc cD ch C.GK H a b → Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) := by
  intro C cD ch p R H a b M c u0 _ hV hF hC h0 hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, hw, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  have ha : G.aL p.L = a := by
    funext t
    unfold G.aL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).1
    · exact (h0 t (hTT' ▸ h)).1.symm
  have hb : G.bL p.L = b := by
    funext t
    unfold G.bL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).2
    · exact (h0 t (hTT' ▸ h)).2.symm
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
      p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
      (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
       open Classical in
       ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
        (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l then (1 : ℝ) else 0) +
          4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) →
      Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK a b := by
    intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6 hW
    obtain rfl : G.hP p.D = hf := funext e6
    subst e1 e2 e0 e3 e4 e5
    unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands
    simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1]
    exact hW
  rw [ha, hb]
  exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh' hW

end GlobalTheory.EX

end
end

section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem exists_weights_in_windows : ∀ (eps : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → ∃ x0 : ℝ,
    ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R →
      ∃ a b : R.A → ℤ, WinOK s C.GK H a b := by
  intro eps C h0 h1 hS
  have hLa : 1 ≤ C.GK.La := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, hN⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hP⟩ := GlobalTheory.scale_poly_comparison eps 17 1 h0 one_pos
  obtain ⟨x3, hR⟩ := GlobalTheory.EX.rank_basic_bounds eps h0 h1
  refine ⟨max x1 (max x2 x3), fun s R H he hx hRV => ?_⟩
  have hx1 : x1 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, hK⟩ := hN s he hx1
  have hLa1 := (hK C.GK hLa).1
  obtain ⟨-, -, hb, -, hb', -⟩ := hP s he hx2
  obtain ⟨-, -, hr, hkr, -⟩ := hR s R he hx3 hRV
  have hx1' : 1 ≤ s.x := s.one_lt_alt.le
  have hxp : 0 < s.x := lt_of_lt_of_le one_pos hx1'
  have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hk0 : (0 : ℝ) < R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < R.k)
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  rw [Real.rpow_one] at hb
  rw [sub_self, Real.rpow_zero, one_mul] at hb'
  have h17 : 0 < s.x ^ (17 : ℝ) := Real.rpow_pos_of_pos hxp _
  have hb17 : s.x ^ (17 : ℝ) ≤ s.b := le_trans (le_mul_of_one_le_right h17.le hX) hb
  have hA : 1 ≤ s.a / ((R.k : ℝ) * s.x ^ (Scale.A / 2)) := by
    have h13 : 0 < s.x ^ (Scale.A / 2) := Real.rpow_pos_of_pos hxp _
    rw [le_div_iff₀ (mul_pos hk0 h13), one_mul]
    calc (R.k : ℝ) * s.x ^ (Scale.A / 2) ≤ s.x ^ (5 : ℝ) * s.x ^ (Scale.A / 2) :=
          mul_le_mul_of_nonneg_right hk5 h13.le
      _ = s.x * s.x ^ (17 : ℝ) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_one_add' hxp.le (by norm_num)]
          congr 1
          unfold Scale.A
          norm_num
      _ ≤ s.a := mul_le_mul_of_nonneg_left hb17 hxp.le
  have hB : 1 ≤ 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (R.k : ℝ) := by
    rw [le_div_iff₀ hk0, one_mul]
    have hn : (1 : ℝ) ≤ R.n := by
      have : 1 ≤ R.n := R.ord_pos
      exact_mod_cast this
    have hd : 1 ≤ s.delta1 * s.x ^ s.eps := by
      unfold Scale.delta1
      rw [← Real.rpow_add hxp]
      exact Real.one_le_rpow hx1' (by have := s.eps_pos; linarith)
    have hL : 1 ≤ G.La C.GK s := le_trans (Real.one_le_rpow hx1' s.eps_pos.le) hLa1
    have hkb : (R.k : ℝ) ≤ s.b' :=
      le_trans hk5 (le_trans (Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)) hb')
    have h2 : (1 : ℝ) ≤ 2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hd) hL
    calc (R.k : ℝ) ≤ s.b' := hkb
      _ ≤ (2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s) * s.b' :=
          le_mul_of_one_le_left (le_trans hk0.le hkb) h2
      _ = _ := by ring
  refine ⟨fun _ => ⌈s.a⌉, fun _ => ⌈s.b'⌉, fun t _ => ⟨⟨Int.le_ceil _, ?_⟩, Int.le_ceil _, ?_⟩⟩
  · have := Int.ceil_lt_add_one s.a
    linarith
  · have := Int.ceil_lt_add_one s.b'
    linarith

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

noncomputable section

namespace GlobalTheory.KerRat

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem phiT_move {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (h : GLG (E := E) (n := a) (SG := SG)) (h' : GLG (E := E) (n := b) (SG := SG')) (x : HomE E a b) :
    phiT K (d.act γ h) (d'.act γ' h') (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) = phiT K d d' x := by
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun Q => ?_) rfl rfl
  have key : ∀ y, (y ∈ (d.act γ h).at Q.1 → (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y ∈ (d'.act γ' h').at Q.1 ∧
      (d'.act γ' h').f Q ((γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y) = (d.act γ h).f Q y) ↔
      (γ.symm y ∈ d.at Q.1 → x (γ.symm y) ∈ d'.at Q.1 ∧ d'.f Q (x (γ.symm y)) = d.f Q (γ.symm y)) := fun y => by
    show (y ∈ localization₂ _ (gmap γ d.N) → γ' (x (γ.symm y)) ∈ localization₂ _ (gmap γ' d'.N) ∧
      d'.f Q (γ'.symm (γ' (x (γ.symm y)))) = d.f Q (γ.symm y)) ↔ _
    rw [mem_localization_gmap, mem_localization_gmap, LinearEquiv.symm_apply_apply]
  refine ⟨fun H y => ?_, fun H y => (key y).2 (H _)⟩
  have := (key (γ y)).1 (H _)
  rwa [LinearEquiv.symm_apply_apply] at this

theorem kerOf_move {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (γ : UF E a) (γ' : UF E b)
    (N : Submodule (𝓞 E) (Sp E a)) (fr fr₂ : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' fr₂' : Frs E b SB)
    (Ξ Ξ₂ : HomE E a b → K)
    (hcong : ∀ x x', x - x' ∈ mulLat cB (homAt Sa N N') → th N fr N' fr' cB x = th N fr N' fr' cB x')
    (heq : ∀ x, th (gmap γ.1 N) fr₂ (gmap γ'.1 N') fr₂' cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (rho' γ') ∘ₗ (th N fr N' fr' cB x) ∘ₗ (rho γ⁻¹))
    (hΞ : ∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x)
    (hΞ₂ : ∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = Ξ x) :
    kerOf th Sa cA cB (gmap γ.1 N) fr₂ (gmap γ'.1 N') fr₂' Ξ₂ =
      (rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹) := by
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = φ _
    unfold latSum
    rw [φ.map_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hcong x x' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹
    rw [heq, hΞ₂, LinearMap.smul_comp, LinearMap.comp_smul]

omit [NumberField E] [StarRing E] in
theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c D : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat c M ≤ divLat D M := by
  rintro _ ⟨y, hy, rfl⟩
  show (D : 𝓞 E) • ((c : 𝓞 E) • y) ∈ M
  exact M.smul_mem _ (M.smul_mem _ hy)

end Gen

theorem thDistC_class {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
    (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (c : ℕ)
    (x x' : HomE X.E a b) (h : x - x' ∈ mulLat c (homAt Sa N N')) :
    thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x = thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x' := by
  have hL : A.IsLift Sa N N' c x = A.IsLift Sa N N' c x' := by
    funext s
    unfold Amb.IsLift
    have : s - x ∈ mulLat c (homAt Sa N N') ↔ s - x' ∈ mulLat c (homAt Sa N N') := by
      rw [show s - x' = (s - x) + (x - x') by abel]
      exact (Submodule.add_mem_iff_left _ h).symm
    rw [this]
  have hW : A.liftW Sa N N' c x = A.liftW Sa N N' c x' := by unfold Amb.liftW; rw [hL]
  have hT : A.thInd Sa N N' c x = A.thInd Sa N N' c x' := by unfold Amb.thInd; rw [hW]
  have hJ : A.jetK Sa N N' c x = A.jetK Sa N N' c x' := by funext m; unfold Amb.jetK; rw [hT]
  have hD : x ∈ divLat D (homAt Sa N N') ↔ x' ∈ divLat D (homAt Sa N N') := by
    rw [show x = x' + (x - x') by abel]
    exact Submodule.add_mem_iff_left _ (mulLat_le_divLat c D _ h)
  unfold thDistC
  rw [hJ]
  exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_congr_right fun _ => hD) rfl rfl

theorem ratTerm_of_ratStep : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → RatStep W Ch sel mu cst A u i (i + 1) → RatTerm W Ch sel mu cst A u i (i + 1) := by
  classical
  intro X Pr R W Ch sel S mu cst A u i _ hPr _ _ hR SG SG' d fr d' fr' Ξ₀ γ γ' hbox
  have hB : 0 < cBof sel mu cst u := by
    unfold cBof
    refine Nat.mul_pos (hPr.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
    exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)
  unfold term ker
  refine kerOf_move (stepT W Ch sel mu cst A u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i)))
    ((rhoVr X.emb (W.lamTrue u (i + 1))).comp (ufGL X.E (R.N (i + 1)))) γ γ' d.1.N fr (fun P => γ.1 * fr P) d'.1.N fr' (fun P => γ'.1 * fr' P)
    (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
    (fun x => phiT X.K (d.1.act γ.1 1) (d'.1.act γ'.1 1) x * Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) ?_ ?_ ?_ ?_
  · intro x x' h
    exact thDistC_class A _ _ _ _ _ _ _ _ _ _ _ _ _ _ x x' h
  · intro x
    by_cases hx : x ∈ divLat (cAof sel mu cst * cBof sel mu cst u) (homAt (Sall sel mu u) d.1.N d'.1.N)
    · exact hR γ γ' d.1.N fr d'.1.N fr' _ x ⟨⟨d.2.lat, d.2.uni⟩, ⟨d'.2.lat, d'.2.uni⟩, hB, Dvd.intro_left _ rfl, hx⟩
    · have hx2 := mt (mem_divLat_equiv_iff _ _ _ (homConjEquiv_mem_homAt (Sall sel mu u) γ.1 γ'.1 d.1.N d'.1.N)
        (cAof sel mu cst * cBof sel mu cst u) x).1 hx
      unfold stepT thDistC
      rw [if_neg fun h => hx2 h.2, if_neg fun h => hx h.2, LinearMap.zero_comp, LinearMap.comp_zero]
  · rintro x _ ⟨y₀, hy₀, rfl⟩
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.phiT_add _ _ d'.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
      have h1 : Pr.piT u ∈ P.1.asIdeal := by
        have h := P.2
        unfold Primes.vT divs at h
        split_ifs at h with hf
        · simpa using h
        · simp at h
      rw [cBof, Nat.cast_mul, ← hPr.piT_norm]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
    · exact hbox.2 x _ ⟨y₀, fun P hP => hy₀ P (Finset.mem_union_right _ hP), rfl⟩
  · intro x
    refine congrArg₂ (· * ·) (phiT_move d.1 d'.1 γ.1 γ'.1 1 1 x) (congrArg Ξ₀ ?_)
    ext y l
    simp

end GlobalTheory.KerRat
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomGood

theorem inOK_iff_mem_OK (d : ℕ) (z : ℂ) : GlobalTheory.MomOne.InOK d z ↔ z ∈ JMB.OK d := Iff.rfl

theorem lamA_eq_lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : JMB.lamA lam x = lamC lam x := rfl

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  intro D cc δ N N' L L' g S e p _ lam N₀ n hd hLa y hy
  obtain ⟨-, -, hOK, hconj, -⟩ := GlobalTheory.MomDict.main D
  unfold GlobalTheory.MomT.goodLifts at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, hκ, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.φ₀ ((κ : D.host.K) : D.host.E), ?_, ?_, e x, (hLa x).2 hx, ?_⟩
    · rw [hd]
      exact (inOK_iff_mem_OK _ _).1 ((hOK _).2 ⟨κ, rfl⟩)
    · rw [lamA_eq_lamC, ← hconj]
      exact hκ
    · exact map_smul e _ x
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.MomGood
end
