module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle223
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle188
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle222
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle043
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle209
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle191
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle165
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle219
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle224
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle060
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle202
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

open Classical

theorem uInv_zero_eq_self {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv (0 : ℂ) w x = x
  | [], _ => rfl
  | l :: w, x => by
    funext e
    have he : (Fin.cons (e 0) (fun a => e a.succ) : Wd.Ix (Fin (w.length + 1))) = e := Fin.cons_self_tail e
    unfold KB.uInv
    simp only [map_zero, ite_self, zero_smul, add_zero, uInv_zero_eq_self w]
    by_cases h0 : e 0 = 0
    · rw [ite_eq_left h0]
      conv_rhs => rw [← he]
      rw [h0]
    · have h1 : e 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
        · exact absurd h h0
        · exact h
      rw [ite_eq_right h0]
      conv_rhs => rw [← he]
      rw [h1]

theorem waveG_zero_eq_self {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp only [KB.waveG, uInv_zero_eq_self, P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_smul]

theorem psiL_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (c : ℂ) : KB.psiL S 0 c = 1 := by
  simp [KB.psiL]

theorem intB_of (hPS : StandardPairingDecay.PStdC) (hD : DecayUnif) : IntB := by
  intro Cb
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  obtain ⟨c7, h7⟩ := hD Cb
  refine ⟨max c1 c7, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n
  have hB7 := PBJoint.built_setting_to_model_place (le_max_right c1 c7) hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB
  have hgpos := PBL.g_pos_of_built hB
  have hcpt : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε) := by
    intro v ε hε
    obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
    refine (h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop cutN (by rw [hl0]; exact hInD)
      hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  intro v ε hε i hi1 hi2 w h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := Nat.le_of_succ_le_succ hi2
  have hsz1 : D.ptSize h = j := hsz.trans (Nat.add_sub_cancel j 1)
  have hsz1' : D.ptSize h' = j := hsz'.trans (Nat.add_sub_cancel j 1)
  rw [Nat.add_sub_cancel]
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := PBD.cutWord_of_adm S hGo hCI w v
  have hi2' : j + 1 ≤ S.G.r + 1 := Nat.succ_le_succ hj
  have hadm : D.AdmAt S v (w.1 v) := ⟨w, rfl⟩
  have h7' := h7 E Wp Wq S p f χ A₀ hB7 v ε hε (j + 1) hi1 hi2' (w.1 v) hadm h h' hsz hsz'
  refine h7'.elim fun Cd hC => ?_
  have hdec := (hC n).1
  have hloc_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.IsLocPt (H ++ [(1, c)]) (j + 1) → D.IsLocPt H j :=
    fun H c hH hl => ⟨fun b hb => hl.1 b (List.mem_append_left _ hb), hH⟩
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (PBL.stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (PBL.stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    have hPS' := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (cutSeq S p f χ n v ε) j hj (w.1 v)
      (PBL.stdS S h) (PBL.stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hcpt v ε hε) (by rw [hl0]; exact hw)
    refine hPS'.elim fun φ0 hφ0all => ?_
    obtain ⟨hφ0c, -, hφ0, -⟩ := hφ0all
    have hlam := PBL.lamS_pos S hgpos j
    set φ : ℂ → ℂ := fun c => ((StandardPairingDecay.Kg S j h h' : ℝ) : ℂ) * φ0 ((PBL.lamS S j : ℂ) * c) with hφdef
    have hφc : Continuous φ := continuous_const.mul (hφ0c.comp (continuous_const.mul continuous_id))
    have hφeq : ∀ c : ℂ, c ≠ 0 → φ c = (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
      intro c hc
      have hlc : (PBL.lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam.ne') hc
      rw [StandardPairingDecay.gramLoc_setC_app hB (cutSeq S p f χ n) v ε j hj (w.1 v) h h' hh.2 hh'.2 c hc, hφdef]
      simp only
      rw [hφ0 _ hlc]
      ring
    refine ⟨φ, hφc, hφeq, ⟨Cd, fun c => ?_⟩, ?_⟩
    · exact PBB.K8.bound_all hφc (fun c hc => by rw [hφeq c hc]; exact hdec c hc) c
    · have hae : (fun c => φ c) =ᵐ[volume] fun c => (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
          (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S 0 c := by
        filter_upwards [PBL.ae_ne_zero_complex] with c hc
        rw [psiL_zero, mul_one, hφeq c hc]
      rw [integral_congr_ae hae, StandardPairingDecay.int_gramLoc_setC hPS hB (cutSeq S p f χ n) v ε (hcpt v ε hε) j hj (w.1 v) hw 0
        h h' hh hh']
      have hs0 : PBL.sW S j 0 = 0 := by simp [PBL.sW]
      rw [hs0, waveG_zero_eq_self, ← PBL.rr_eq_form (p v) _ j hj (w.1 v) _ _ hH hH']
      erw [PBL.gramLoc_setC hB]
      have hsA := PBL.sizeAt_pos S hGo v (w.1 v) hadm
      have hk := PBL.kc_scal hB v j hj (w.1 v) h h'
      have hrd := PBD.rd_pos' E
      have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
      have hdl : 0 < KB.dlB S (j + 1) 1 := by unfold KB.dlB; exact div_pos (zpow_pos hrd _) hδ
      have key : StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| =
          KB.dlB S (j + 1) 1 * (√(PBL.nnS S h) * √(PBL.nnS S h') * (1 / (PBL.bS S h * PBL.bS S h' * PBL.ΓS S j))) := by
        unfold PBL.Kc PBL.dW at hk
        unfold StandardPairingDecay.Kg
        field_simp at hk ⊢
        linear_combination hk
      show ((StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * _ = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ) * _
      rw [key]
      push_cast
      ring
  · have hz : ∀ c : ℂ, (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro c
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      refine hloc ⟨hloc_app h c hsz1 ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1),
        hloc_app h' c hsz1' ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2)⟩
    have hz0 : (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε j (w.1 v) h h' = 0 := by
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      exact hloc ⟨(PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1, (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2⟩
    refine ⟨fun _ => 0, continuous_const, fun c _ => (hz c).symm, ⟨0, fun c => by simp⟩, ?_⟩
    rw [hz0, integral_zero, mul_zero]

def IntBOfParts : Prop := StandardPairingDecay.PStdC → DecayUnif → IntB

theorem intBOfParts : IntBOfParts := intB_of

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem integral_bound_of_parts : PBASM.IntBOfParts := PBASM.intBOfParts

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem topLocB : TopLocB := by
  intro hDT hVT hTR Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hC hB
  refine ⟨fun s hs2 hsr v => lamTop_thr hC hB s hs2 hsr v, fun F hF (v : Fin S.f) => ?_⟩
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGo, hGr, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  have hCI := PBCut.cutInside_of_built hB
  intro s hs2 hsr a ha haN
  have hsr' : s ≤ S.G.r + 1 := hsr
  have ha' : D.AdmAt S v a := ha
  have haN' : a.length + C.Kst ≤ S.Ntop := haN
  set d := S.G.r + 1 - s with hd
  have hds : d + s = S.G.r + 1 := by omega
  have hd2 : d ≤ 2 * S.G.r := by omega
  obtain ⟨-, grid, hinj, hbnd, hmem, hwords, hprob, -⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst d ha' haN' hd2
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a), hprob, ?_⟩
  intro ε hε t Y ht hY
  have hY' : ∀ P ∈ Y, D.ptSize P = d := fun P hP => by rw [hd]; exact hY P hP
  set Λ : ℝ := ∑ n : Fin C.Kst → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| with hΛ
  set C0 : ℝ := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (Real.sqrt (S.T * S.T'))⁻¹
    with hC0
  set τ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (s - 1) * t with hτ
  set c : ℂ := (((-1 : ℂ) ^ (s - 1) / τ) ^ C.Kst)⁻¹ with hc
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hC0nn : 0 ≤ C0 := mul_nonneg (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S hg hk v false))
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hPn : ∀ n : Fin C.Kst → Fin (d + 1), 0 < ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
    intro n
    refine List.prod_pos fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact abs_pos.2 ((hGo v).2.2.2.2.2 _ (Or.inl ⟨_, hmem b (n b)⟩)).2.2.1

  have hK1 := top_kernel (H := HV S v) (α := C.LPt) (Ea := Wd.Ix (Fin a.length)) (R := M.Ty (D.parOf S v))
    (N := Fin C.Kst → Fin (d + 1)) (Ew := fun n => Wd.Ix (Fin (KB.plusW (List.ofFn fun b => grid b (n b)) a).length))
    Y (fun n => KB.firstSt (List.ofFn fun b => grid b (n b))) (fun n => firstSt_inj _)
    (fun e ρ => vecT S p F v ε s t a e ρ)
    (fun n e' ρ => vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => del2 S p v a e ρ) (fun n e' ρ => del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => second_defect_nonneg S p v a e ρ) (fun n e' ρ => second_defect_nonneg S p v _ e' ρ)
    (fun n => ∏ b, F7.lagCo (grid b) (n b))
    (fun n => ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod) hPn c C0 C.Kst hC0nn
    (fun P hP e ρ => vecT_deg hDT hB F v ε (hF v ε hε) s hs2 t ht d hds a e ρ grid hinj
      (fun n => (hwords n).2.2.1) P (hY' P hP))
    (fun n e ρ => by
      have h := second_defect_plus_word_le S p v a e ρ C0 hC0nn (List.ofFn fun b => grid b (n b))
        (rhyp_nodes hTR hB hC v a ha' haN' grid hmem n (hwords n).2.2.1 e ρ)
      rwa [List.length_ofFn] at h)

  change Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
    (fun P Q => (((‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) : ℝ) : ℂ) *
      KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]))
  have hsz : ∀ P ∈ Y, D.ptSize P + s = S.G.r + 1 := fun P hP => by rw [hY' P hP]; omega
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  have hΓ : 0 < ΓS S (S.G.r + 1) := PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _
  have hsa : 0 < S.sizeAt v a := sizeAt_pos S hGo v a ha'
  set ka : ℝ := 1 / (ΓS S (S.G.r + 1) * S.sizeAt v a) with hka
  have hka0 : 0 ≤ ka := by positivity
  have hΛpos : 0 < Λ := lam_sum_pos grid hinj

  have h1 := loe_diag (omT S s t) (loe_smul ka hka0 hK1)
  have h1' : Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
      (fun P Q => (((‖c‖ ^ 2 * Λ * C0 ^ C.Kst) * Λ : ℝ) : ℂ) * ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q))) := by
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => ?_) h1
    · rw [gN_top hVT hB F v ε s hs2 t a P Q (hsz P hP) (hsz Q hQ)]
      ring
    · exact mix_alg _ _ _ _ _ _ _ _ hΛpos.ne' fun n => (hPn n).ne'

  have hmixY : ∀ P ∈ Y, ∀ Q ∈ Y, KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
      (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)) := by
    intro P hP Q hQ
    refine (mix_pushT (setC S p F) v ε (S.G.r + 1) grid (fun ys => KB.plusW ys a) _ _).trans ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [thGrid_eq, ← hΛ, gN_top hVT hB F v ε s hs2 t _ P Q (hsz P hP) (hsz Q hQ), sizeAt_plusW]
    have hk : 1 / (ΓS S (S.G.r + 1) * (((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod *
        S.sizeAt v a)) = ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
      rw [hka]; have := (hPn n).ne'; field_simp
    rw [hk]
    ring
  have hpsdY := psd_mixω Y (omT S s t) (fun n : Fin C.Kst → Fin (d + 1) => |∏ b, F7.lagCo (grid b) (n b)| / Λ)
    (fun n => ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod)
    (fun n => div_nonneg (abs_nonneg _) hΛpos.le) (fun n => div_nonneg hka0 (hPn n).le)
    (fun n P Q => ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
      gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)
    (fun n => psd_dsum Y _ (fun e' ρ => second_defect_nonneg S p v _ e' ρ) _)
  have hX : 0 ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) - ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ := by
    have hlv : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) :=
      zpow_pos (by positivity) _
    set lv : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) with hlvdef
    have hτn : ‖τ‖ = lv * ‖t‖ := by
      rw [hτ, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hlv.le]
    have hcn : ‖c‖ = ‖τ‖ ^ C.Kst := by
      rw [hc, norm_inv, norm_pow, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_pow, inv_inv]
    set B : ℝ := (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ d with hBdef
    have hΛB : Λ ≤ B ^ C.Kst := lam_sum_le grid B hbnd
    have hlenpos := lenI_posT hB (Fin.pos v)
    have hB0 : 0 ≤ B := by
      rw [hBdef, len_eq_lenI']; exact pow_nonneg (div_nonneg (by positivity) hlenpos.le) _

    have hA0 : 0 ≤ (2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r ((S.G.r + 2 - s : ℕ) : ℤ)
        ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)))) * Real.exp 1 *
        (28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (√(S.T * S.T'))⁻¹ := by
      have : 0 ≤ S.G.N := by unfold Sz.Glob.N; positivity
      have := supA_nonneg S hg hk v false
      positivity
    have hlam2 : lamTop S (S.G.r + 2 - s) v ^ 2 = lv ^ 2 * B ^ 2 * C0 := by
      unfold lamTop
      rw [Real.sq_sqrt hA0]
      have e1 : ((S.G.r + 2 - s : ℕ) : ℤ) = ((1 + d : ℕ) : ℤ) := by rw [hd]; push_cast; omega
      have e2 : (S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ) = (s : ℤ) := by push_cast; omega
      have e3 : (S.g : ℝ) = S.G.g := by unfold C.HidaSetting.g Sz.Glob.g; push_cast; ring
      have e4 : S.G.r + 2 - s - 1 = d := by omega
      rw [e2, e1, e4, hlvdef, zpow_sq_eq _ (by positivity), inv_div, e3, hBdef, ← pow_mul, ntop_eq_N'',
        len_eq_lenI', hC0, mul_comm d 2]
      ring
    have hfin : ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) := by
      have e5 : (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by
        rw [pow_mul, mul_pow (‖t‖) (lamTop S (S.G.r + 2 - s) v) 2, hlam2]
      rw [e5, hcn, hτn]
      have hΛ0 : 0 ≤ Λ := hΛpos.le
      have hsq : Λ * Λ ≤ B ^ C.Kst * B ^ C.Kst := mul_le_mul hΛB hΛB hΛ0 (pow_nonneg hB0 _)
      calc ((lv * ‖t‖) ^ C.Kst) ^ 2 * Λ * C0 ^ C.Kst * Λ = ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (Λ * Λ) := by ring
        _ ≤ ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (B ^ C.Kst * B ^ C.Kst) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by ring
    linarith
  have h3 := loe_scale hpsdY hX
  exact loe_trans h1' (loe_congr (fun _ _ _ _ => rfl) (fun P hP Q hQ => by rw [hmixY P hP Q hQ]) h3)

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_local_built_places : Formalism.FourierDecayAlt.P.PBL.TopLocB := Formalism.FourierDecayAlt.P.PBL.topLocB
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem hasCompactSupport_rho (D : B.RealPlaceData k r Wp Wq) {q : B.SS k r} (hq : D.inSS q)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : HasCompactSupport F) : HasCompactSupport (B.rho D q F) := by
  have ha := Formalism.FourierDecayAlt.P.B5.inSS_left D hq
  have hb := Formalism.FourierDecayAlt.P.B5.inSS_right D hq
  have himg : B.sgs q ⁻¹' tsupport F ⊆ (fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F := by
    intro x hx
    refine ⟨B.sgs q x, hx, ?_⟩
    dsimp only
    rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
    have key : ∀ (a b y : B.Mat k r), a * a⁻¹ = 1 → b * b⁻¹ = 1 → a * (a⁻¹ * y * b) * b⁻¹ = y := by
      intro a b y ha hb
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hb, Matrix.mul_one, ← Matrix.mul_assoc, ha, Matrix.one_mul]
    exact key _ _ x (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv ha).1 (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hb).1
  have hcK : IsCompact ((fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F) :=
    hF.image ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  refine hcK.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx => himg (subset_tsupport _ ?_)) hcK.isClosed)
  intro h0
  apply hx
  show B.rho D q F x = 0
  unfold B.rho
  rw [h0]
  simp

variable [FiniteDimensional ℂ Wq]

noncomputable def II (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  ∫ x : Mt k r, B.hsInner (X (Matrix.of x)) (Y (Matrix.of x)) ∂D.μG

theorem ii_swap (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : II D X Y = conj (II D Y X) := by
  unfold II
  rw [← integral_conj]
  congr 1
  funext x
  unfold B.hsInner
  rw [inner_conj_symm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hermitian_curvature_adjoint_integral : AdjIntAsm := by
  intro hU hF k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp φ hφ hφc hφs
  obtain ⟨p', hp', hUp⟩ := hU k r Wp Wq D p hp
  have hU' : ∀ X Y, II D (B.rho D p X) Y = II D X (B.rho D p' Y) := hUp
  have hF' : ∀ F F' : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F →
      B.SuppIn (B.GPos D) F → B.CkOn ⊤ (B.GV k r) F' → HasCompactSupport F' → B.SuppIn (B.GPos D) F' →
      II D (B.opApply Θ F) F' = II D F (B.opAdj Θ F') := hF k r Wp Wq D Θ hs hc
  have hcomm : II D (B.opApply Θ (B.rho D p' φ)) f = II D (B.rho D p' (B.opApply Θ φ)) f := by
    unfold II
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
    by_cases hxp : Matrix.of x ∈ B.GPos D
    · rw [hc p' hp' φ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hφ) _ hxp]
    · have h0 : f (Matrix.of x) = 0 := by
        by_contra hne
        exact hxp (hfs (subset_closure ⟨hx, hne⟩))
      simp only [h0, Formalism.FourierDecayAlt.P.B5.hs_zero_right]
  show II D (B.opAdj Θ (B.rho D p f)) φ = II D (B.rho D p (B.opAdj Θ f)) φ
  calc II D (B.opAdj Θ (B.rho D p f)) φ = conj (II D φ (B.opAdj Θ (B.rho D p f))) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ φ) (B.rho D p f)) := by
        rw [hF' φ (B.rho D p f) hφ hφc hφs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (hasCompactSupport_rho D hp hfc)
          (suppIn_rho D hp hfs)]
    _ = II D (B.rho D p f) (B.opApply Θ φ) := (ii_swap D _ _).symm
    _ = II D f (B.rho D p' (B.opApply Θ φ)) := hU' _ _
    _ = conj (II D (B.rho D p' (B.opApply Θ φ)) f) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ (B.rho D p' φ)) f) := by rw [hcomm]
    _ = conj (II D (B.rho D p' φ) (B.opAdj Θ f)) := by
        rw [hF' (B.rho D p' φ) f (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp' hφ) (hasCompactSupport_rho D hp' hφc)
          (suppIn_rho D hp' hφs) hf hfc hfs]
    _ = II D (B.opAdj Θ f) (B.rho D p' φ) := (ii_swap D _ _).symm
    _ = II D (B.rho D p (B.opAdj Θ f)) φ := (hU' _ _).symm

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

namespace Formalism.FourierDecayAlt.P

theorem cutSH_sliceStepHer_of_sfg (h7 : CutSH.SliceFamGood) : PTie.SliceStepHer :=
  CutSH.sliceStepHer_of CutSH.family_orbital_valid CutSH.family_algebraic CutSH.representation_linear
    cell_compatibility_identity h7 CutSH.slice_family_orbital operator_class_closed boundary_torus_adjoin
    unipotent_scalar_identity

theorem cutSH_levTransportHer_of_sfg (h7 : CutSH.SliceFamGood) : PTie.LevTransportHer :=
  ptie_levTransportHer_of_sliceStep (cutSH_sliceStepHer_of_sfg h7)

theorem level_transport_hermitian : PTie.LevTransportHer := cutSH_levTransportHer_of_sfg slice_family_good

end Formalism.FourierDecayAlt.P
end
