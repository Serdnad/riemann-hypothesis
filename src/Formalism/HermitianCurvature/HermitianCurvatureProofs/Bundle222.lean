module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.Bundle006
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle211
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle085
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle212
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGRadProper
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle220
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle197
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvCB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEig
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvMain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

def PStdC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2)

theorem pStdC_of (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) : PStdC :=
  Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT

theorem decay_scale (lam x : ℝ) (hlam : 0 < lam) (hx : 0 ≤ x) :
    ((1 + lam * x) ^ 3)⁻¹ ≤ (max 1 lam⁻¹) ^ 3 * ((1 + x) ^ 3)⁻¹ := by
  have hM : 1 ≤ max 1 lam⁻¹ := le_max_left _ _
  have hle : 1 + x ≤ max 1 lam⁻¹ * (1 + lam * x) := by
    rcases le_or_gt 1 lam with h1 | h1
    · have e1 : x ≤ lam * x := le_mul_of_one_le_left hx h1
      have e2 : 1 + lam * x ≤ max 1 lam⁻¹ * (1 + lam * x) := le_mul_of_one_le_left (by positivity) hM
      linarith
    · have hi : lam⁻¹ ≤ max 1 lam⁻¹ := le_max_right _ _
      have e : lam⁻¹ * (1 + lam * x) = lam⁻¹ + x := by field_simp
      have h2 : 1 ≤ lam⁻¹ := by rw [le_inv_comm₀ one_pos hlam]; simpa using h1.le
      nlinarith [mul_le_mul_of_nonneg_right hi (by positivity : (0 : ℝ) ≤ 1 + lam * x)]
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + lam * x := by positivity
  have hc : (1 + x) ^ 3 ≤ (max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h1.le hle 3
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ((1 + lam * x) ^ 3)⁻¹ * (1 + x) ^ 3 ≤ ((1 + lam * x) ^ 3)⁻¹ * ((max 1 lam⁻¹) ^ 3 * (1 + lam * x) ^ 3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (max 1 lam⁻¹) ^ 3 := by field_simp

section frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Kg (S : C.HidaSetting E Wp Wq) (j : ℕ) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j

theorem gramLoc_setC_app {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) (c : ℂ) (hc : c ≠ 0) :
    (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) =
      ((Kg S j h h' : ℝ) : ℂ) * ((KB.levW (D.parOf S v) (j + 1) ((lamS S j : ℂ) * c) : ℝ) : ℂ) *
        (p v).RR (F v ε) (j + 1) w (stdS S h ++ [(1, (lamS S j : ℂ) * c)])
          (stdS S h' ++ [(1, (lamS S j : ℂ) * c)]) := by
  have hgpos := g_pos_of_built hB
  have hTT := (pdG_of_built hB v).2
  have hrd := rd_pos' E
  have hfr : ∀ b s, 0 < S.fr b s := fun b s => Real.rpow_pos_of_pos hrd _
  set lam := lamS S j with hlam
  have hlam_pos : 0 < lam := lamS_pos S hgpos j
  set xw : ℂ → ℝ := fun c => C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] with hxw
  have hn_nonneg : ∀ H, D.ptSize H = j → 0 ≤ nnS S H := fun H hH =>
    lpt_value_nonneg_of_pos_of_size_le _ _ _ _ hfr H 1 le_rfl (by omega)
  have hsq : √(nnS S (h ++ [(1, c)])) * √(nnS S (h' ++ [(1, c)])) =
      √(nnS S h) * √(nnS S h') * (√(xw c) * √(xw c)) := by
    rw [nnS_app S j hj h c hsz, nnS_app S j hj h' c hsz', Real.sqrt_mul (hn_nonneg h hsz),
      Real.sqrt_mul (hn_nonneg h' hsz')]
    ring
  set RRs : ℕ → C.LPt → C.LPt → ℂ := fun i P Q => (p v).RR (F v ε) i w P Q with hRRs
  set Mj : ℤ := C.Mlev S.G.k S.G.r (j + 1) with hMj
  have hW : ∀ (H H' : C.LPt), D.ptSize H = j →
      ((√(xw c) * √(xw c) : ℝ) : ℂ) * RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) =
        ((rhoS S j * KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) : ℝ) : ℂ) *
          RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) := by
    intro H H' hH
    by_cases hjt : j = S.G.r
    · have hnu : S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; rw [hjt]; push_cast; ring
      have hlam1 : lam = 1 := by rw [hlam, lamS, hnu, zpow_zero]
      have hfr1 : S.fr (j + 1) 1 = 1 := by
        unfold C.HidaSetting.fr
        have : ((S6.nuBlock (S.G.r : ℤ) (Nat.cast (j + 1)) (Nat.cast 1) : ℤ) : ℝ) = 0 := by
          unfold S6.nuBlock; rw [hjt]; push_cast; ring
        rw [this]; simp
      have hρ1 : rhoS S j = 1 := by rw [rhoS, ← hlam, hlam1, hfr1]; simp
      have hx : xw c = (Complex.normSq c - S.T * S.T') ^ (S.G.k - 1) := by
        simp only [hxw, C.nAux]
        rw [if_pos (by constructor <;> first | trivial | omega), mul_one]
      have hlev : KB.levW (D.parOf S v) (j + 1) ((lam : ℂ) * c) = B2.zWeight S.G.k S.T S.T' c := by
        rw [hlam1, Complex.ofReal_one, one_mul]
        unfold KB.levW
        rw [if_pos (by simp [hjt])]
      rw [hρ1, hlev, one_mul, hx]
      by_cases hc2 : S.T * S.T' ≤ Complex.normSq c
      · rw [Real.mul_self_sqrt (pow_nonneg (by linarith) _)]
        unfold B2.zWeight
        rw [if_pos hc2]
      · have h0 : RRs (j + 1) (H ++ [(1, (lam : ℂ) * c)]) (H' ++ [(1, (lam : ℂ) * c)]) = 0 := by
          have := rrTop_zero (D.parOf S v) (p v).l0 (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
            (M.sgn (D.parOf S v) (p v).l0) (F v ε) w H (H' ++ [(1, (lam : ℂ) * c)])
            ((lam : ℂ) * c) (by rw [hH, hjt]) (by
              rw [hlam1, Complex.ofReal_one, one_mul]
              rw [hTT]; linarith)
          simp only [hRRs]
          rw [show j + 1 = (D.parOf S v).r + 1 by rw [hjt]]
          exact this
        rw [h0, mul_zero, mul_zero]
    · have hx : xw c = (S.fr (j + 1) 1 * ‖c‖) ^ (2 * (Mj - 2)) := by
        simp only [hxw, C.nAux]
        rw [if_neg (by omega), mul_one, hMj]
        congr 1
        simp only [Nat.add_sub_cancel, Nat.cast_one]
        ring
      have hxpos : 0 < xw c := by rw [hx]; exact zpow_pos (mul_pos (hfr _ _) (norm_pos_iff.2 hc)) _
      rw [Real.mul_self_sqrt hxpos.le]
      congr 2
      rw [hx, rhoS, ← hlam, ← hMj]
      unfold KB.levW
      rw [if_neg (by show ¬ (j + 1 = S.G.r + 1); omega)]
      have hnorm : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnorm, ← mul_zpow]
      congr 1
      field_simp
  rw [gramLoc_setC hB, stdS_app S j h c hsz, stdS_app S j h' c hsz']
  have hWc := hW (stdS S h) (stdS S h') (by rw [stdS_size]; exact hsz)
  have hb1 : bS S (h ++ [(1, c)]) = bS S h := bSt_append_one _ _ _
  have hb2 : bS S (h' ++ [(1, c)]) = bS S h' := bSt_append_one _ _ _
  rw [hb1, hb2, hsq]
  simp only [hRRs] at hWc
  unfold Kg
  push_cast at hWc ⊢
  linear_combination ((√(nnS S h) : ℂ) * (√(nnS S h') : ℂ) *
    (1 / ((bS S h : ℂ) * (bS S h' : ℂ) * (ΓS S (j + 1) : ℂ)))) * hWc

theorem int_gramLoc_setC (hPS : PStdC) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (hF : KB.CptCoef (p v).T.base (F v ε)) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j) :
    ∫ c : ℂ, (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S l c =
      ((Kg S j h h' * |(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)) := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
  have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
  obtain ⟨φ, -, -, hφ, hφint⟩ := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w
    (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) hF (by rw [hl0]; exact hw)
  have hlam_pos := lamS_pos S hgpos j
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c' := ⟨_, rfl⟩
  have hae : (fun c : ℂ => (setC S p F).gramLoc v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) *
      KB.psiL S l c) =ᵐ[volume] fun c => ((Kg S j h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    filter_upwards [ae_ne_zero_complex] with c hc
    have hlc : (lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
    simp only [hgdef, Complex.real_smul]
    rw [gramLoc_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc, psiL_eq_fsv S hgpos j l c]
    ring
  rw [integral_congr_ae hae, integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex,
    Complex.real_smul, hgdef]
  simp only
  rw [hφint (sW S j l)]
  push_cast
  ring

end frame

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem act_one_variable_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Pr (V1 E))) (s : ℂ) (x : Wd.Ix S → V1 E) :
    act1 M (fun b => s • x b) = fun e => s • act1 M x e := by
  funext e
  simp only [act1, map_smul, Finset.smul_sum]

theorem kapM_eq (P : M.Par) (j : ℕ) : kapM (P.r - j) P.k = kapJ P j := by
  unfold kapM kapJ
  push_cast
  ring

theorem headPic_of (hJ : HeadJ) : HeadPic := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh X μ L st Φ hD hF hw hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega
  have hc : y.1 ∈ OmX (P.r - (j + 1)) := hy.1
  have hdom := fun τ (hτ : τ ≠ 0) => base_point_mem_domain hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj) hy hτ
  have hL : IsActualLevel X L := hD.2.2.1

  set gg : ℝ := ∏ a : Fin (P.r - (j + 1)),
    (if a.val < (Fin.last (P.r - (j + 1))).val then ‖y.1 a‖ ^ (Mdim P.k (P.r - (j + 1)) a - 1) else 1) with hgg
  have hgg0 : gg ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => by
    split_ifs
    · exact pow_ne_zero _ (norm_ne_zero_iff.2 (hc a))
    · exact one_ne_zero
  set γ := wCell P.k (P.r - (j + 1)) (Fin.last _) y.1 * y.2 with hγdef
  have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hy.2.1
  have hΩ : γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2

  let Rd := rdL (k := P.k) (π := (p.T.bs j).π) (π' := (p.T.bs j).π') hn y hdom
  let φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp) := fun b => (((gg⁻¹ : ℝ)) : ℂ) • Rd (Φ b)
  have hφ : ∀ b τ, τ ≠ 0 → (φ b).1 τ =
      B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b) (mLev P j hj τ γ) := by
    intro b τ hτ
    have hr := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
      (Subtype.val (Φ b)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)) (hΦ b) hτ y hy
    have hraw := raw_eq hn y hdom (Φ b) hτ
    change (((gg⁻¹ : ℝ)) : ℂ) • (Rd (Φ b)).1 τ = _
    have hpos : ‖τ‖ ^ (2 * (P.r - j) + P.k) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hτ)
    have hR : (Rd (Φ b)).1 τ = Q.resG P.k (P.r - (j + 1)) (Fin.last _)
        (fun γ' => B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)
          (D.castM hn (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => τ) γ'))) y.1 y.2 := by
      have h2 := hraw.symm.trans hr
      have h3 := congrArg (fun v => (((‖τ‖ ^ (2 * (P.r - j) + P.k))⁻¹ : ℝ) : ℂ) • v) h2
      simp only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos, Complex.ofReal_one, one_smul] at h3
      exact h3
    rw [hR]
    unfold resG
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hgg0, Complex.ofReal_one, one_smul]
    rfl
  have hRφ : (fun b => Rd (Φ b)) = fun b => ((gg : ℝ) : ℂ) • φ b := by
    funext b
    simp only [φ, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hgg0, Complex.ofReal_one, one_smul]
  have hJe := hJ Wp Wq P p F j hj w h hh γ hF hw hγ hΩ φ hφ t ht e

  have hraw := raw_eq hn y hdom (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Φ e) ht0
  have hact := rd_act hn y hc hdom X hL (D.positionted w) Φ e
  refine hraw.trans ?_
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (Rd (P5.act _ Φ e)).1 t = _
  rw [hact, hRφ]
  unfold oneBT
  rw [act_one_variable_smul, kapM_eq]
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (((gg : ℝ) : ℂ) • (oneBT (kapJ P j) (D.positionted w) φ e).1 t) = _
  rw [← hJe]
  congr 1

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem pb_radHead_of_headJ (hJ : LevelPointCoordinates.HeadJ) : KB.RadHead := pb_radHead_of_headPic (PBP.headPic_of hJ)

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

def GermPartsC : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ n v, GermRealisation.GermFibres (PBL.setC S p (cutSeq S p f χ n)) v ∧ GermRealisation.GermCont (PBL.setC S p (cutSeq S p f χ n)) v

theorem germLocB_of (hI : IntB) (hG : GermPartsC) : GermLocB := by
  intro Cb
  obtain ⟨c1, h1⟩ := hI Cb
  obtain ⟨c2, h2⟩ := hG Cb
  refine ⟨max c1 c2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hI' := h1 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_left _ _) hB) n v
  obtain ⟨hF, hC⟩ := h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_right _ _) hB) n v
  exact GermRealisation.germLoc_of_fibres hI' hB.1 hB.2.1 hF hC

end

end Formalism.FourierDecayAlt.P.PBASM
end

section

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

section thr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem supA_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (one : Bool) :
    0 < J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGR, -⟩ := hB'
  have hcard : 1 ≤ (S.grid1 v).card := by
    have h1 := (hGR v).1
    have h20 := PBD.ntop_ge S
    have : (1 : ℝ) ≤ S.Ntop := by linarith
    have : 1 ≤ S.Ntop := by exact_mod_cast this
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.1 hcard
  obtain ⟨-, -, hI1, -, -, hnode⟩ := hGo v
  obtain ⟨hyI, -, hP0, hP1⟩ := hnode y (Or.inr hy)
  have hy1 := (hI1 y hy).1
  have hq : (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y ≠ 0 := by
    rw [← PBL.qC_re]
    refine (PBL.q_pos_cut hB v y ?_).ne'
    rw [← PBL.cutI_eq]; exact hyI
  have hcore : 0 < (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y := by
    unfold Sz.Cfg.core
    exact Real.sqrt_pos.2 (abs_pos.2 (div_ne_zero (mul_ne_zero hP0 hP1) hq))
  refine lt_of_lt_of_le hcore (PBL.core_le_supA hB v one y ?_)
  cases one
  · simpa using hyI
  · simp only [if_true]
    rw [← PBL.ntop_eq_N']
    exact hy1

theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g := by
  obtain ⟨hg1, hg2, -⟩ := hB
  unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2

theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hS : 0 < S.f) : 0 < S.G.lenI := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hB
  obtain ⟨hlen, -⟩ := hG ⟨0, hS⟩
  have he : S.cutHi ⟨0, hS⟩ - S.cutLo ⟨0, hS⟩ = S.G.lenI := by
    simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring
  rw [he] at hlen
  have h20 := PBD.ntop_ge S
  have h6 : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by positivity
  linarith

theorem thrS_pos (hC : 0 < Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) :
    0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v) := by
  have hg := glob_pos' hB
  have hI := lenI_pos' hB (Fin.pos v)
  have hA := supA_pos hB v (decide (b = 1 ∧ s = 1))
  have hN : (0 : ℝ) < S.G.N := by rw [← PBL.ntop_eq_N']; linarith [PBD.ntop_ge S]
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCA, -⟩ := hB'
  have hC' : 0 < S.CA := lt_of_lt_of_le hC hCA
  unfold J.thrS Sz.lamThreshold
  have hk : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

end thr

theorem thrPos : ThresholdsPositive := by
  intro Cb
  refine ⟨1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB b s v _ _
  exact thrS_pos one_pos hB b s v

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P

theorem slice_family_good : CutSH.SliceFamGood :=
  CutSH.cutSH_sliceFamGood_of CutSH.SFG.gram_function_induction CutSH.SFG.radial_proper
    CutSH.SFG.parameter_smooth CutSH.SFG.point_smooth

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem inverse_function_positive_holds : JDRInvFn :=
  jDRInvFn_of inverse_alpha_positive_holds inverse_beta_positive_holds inverse_beta_left_positive

theorem inverse_function_minus_holds : JDRInvFnM :=
  jDRInvFnM_of inverse_alpha_minus_holds inverse_alpha_left_minus inverse_beta_minus_holds

end Formalism.FourierDecayAlt.P.CutMP
end
