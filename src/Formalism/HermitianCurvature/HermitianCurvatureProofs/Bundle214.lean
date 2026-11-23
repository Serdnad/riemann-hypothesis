module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle189
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle163
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle114
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle204
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieDecompositionLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem local_square_integrable_transfer : LocalSquareIntegrableTransfer := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A ε J e hFr hBg hε hA hJ π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  obtain ⟨F, -, hCC, hFJ⟩ := hJ.2 ε hε
  set A' := A - 5 * Bg with hA'
  have hC5 : ∀ m, m ≤ 5 → B.InCC A' m F := by
    intro m hm
    refine inCC_antiA ?_ (hCC m)
    have : (m : ℝ) ≤ 5 := by exact_mod_cast hm
    rw [hA']; nlinarith

  have hAB : B.AB S.G.k S.G.r ≤ A' := by
    have := jd_AB_le S.G.k S.G.r
    rw [hA']; linarith
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A' hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hC5 4 (by norm_num)
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hC5 5 le_rfl) (hC5 5 le_rfl) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ.1 π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  have hGm : Measurable (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT => MA.Gq (D.parOf S v) q) := by
    unfold MA.Gq; fun_prop
  have hs : MeasurableSet {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q} :=
    measurableSet_le measurable_const hGm
  refine ⟨(((jd_evQ_meas _ _).norm).pow 2).restrict, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q ∈ {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q},
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2) ≤ H q.1 := by
    intro q hqs
    refine ENNReal.ofReal_le_ofReal ?_
    have hGg : ε ≤ GfP S T v (B.gq (T v).base q.1) := by
      have h1 := Formalism.FourierDecayAlt.P.CutMP.cutTr_Gf_gq (T v).base q.2.1 (by rw [hTT]; exact q.2.2)
      have h2 : GfP S T v (B.gq (T v).base q.1) = MA.Gq (D.parOf S v) q := by
        unfold GfP MA.Gq; rw [h1, hTT]
      rw [h2]; exact hqs
    have hJF : J (B.gq Db q.1) = B.JF Db F (B.gq Db q.1) := hFJ q.1 q.2 hGg
    have hq : MA.evQ (D.parOf S v) (trJ S T v e J π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := by
      rw [← hJF]; exact congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          ∂(MA.mu0 (D.parOf S v).r (D.parOf S v).TT).restrict
            {q | ε ≤ MA.Gq (D.parOf S v) q}
        ≤ ∫⁻ q in {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q}, H q.1
            ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT := setLIntegral_mono' hs p1
      _ ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section

noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXUw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gloc

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LocOpG (T : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  ∀ O : Set (B.Mat k r), IsOpen O → ∀ f₁ f₂ : B.Mat k r → E, (∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) →
    ∀ x ∈ O, x ∈ B.GV k r → T f₁ x = T f₂ x

theorem locOpG_top (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    LocOpG (k := k) (r := r) (E := E) (Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b) := by
  intro O hO f₁ f₂ h x hx hxG
  exact PBG.top_congr' O hO u a b h x hx hxG

theorem locOpG_foldr : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))), (∀ T ∈ L, LocOpG T) →
    LocOpG (fun f => L.foldr (fun T h => T h) f)
  | [], _ => fun _ _ _ _ h => h
  | T :: L, hL => by
    intro O hO f₁ f₂ h x hx hxG
    simp only [List.foldr_cons]
    exact hL T List.mem_cons_self O hO _ _
      (locOpG_foldr L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) O hO f₁ f₂ h) x hx hxG

theorem locOpG_qminorOp {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (qminorOp (EabH (Hpk k r)) a b u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine locOpG_foldr _ (fun T hT => ?_) O hO f₁ f₂ h x hx hxG
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact locOpG_top _ _ _

theorem locOpG_AAop (m : ℕ) (hm : m ≤ r) (u : ℂ) : LocOpG (k := k) (r := r) (E := E) (C3.AAop k r m hm u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_AAvop (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (C3.AAvop k r m hm ell) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAvop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    LocOpG (k := k) (r := r) (E := E) (D.vLet k r z z' j hj l e) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [locOpG_AAop _ _ _ O hO f₁ f₂ h x hx hxG]
  · rw [locOpG_AAvop _ _ _ O hO f₁ f₂ h x hx hxG]

theorem uwG_congrG (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → E} (h : ∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ x ∈ O, x ∈ B.GV k r →
      D.uwG k r z z' f₁ j hj w e x = D.uwG k r z z' f₂ j hj w e x
  | [], _ => h
  | l :: w, e => by
    intro x hx hxG
    simp only [D.uwG]
    exact locOpG_vLet z z' j hj l _ O hO _ _ (uwG_congrG z z' j hj hO h w _) x hx hxG

theorem top_zero (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
  exact PBG.eabH_zero a b g

theorem foldr_zero : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))),
    (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) → L.foldr (fun T h => T h) (fun _ => (0 : E)) = fun _ => 0
  | [], _ => rfl
  | T :: L, hL => by
    simp only [List.foldr_cons]
    rw [foldr_zero L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))]
    exact hL T List.mem_cons_self

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (EabH (Hpk k r)) a b u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  unfold qminorOp
  apply Finset.sum_eq_zero
  intro σ _
  rw [foldr_zero _ (fun T hT => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT; exact top_zero _ _ _)]
  funext g
  simp

theorem AAop_zero (m : ℕ) (hm : m ≤ r) (u : ℂ) : C3.AAop k r m hm u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    C3.AAvop k r m hm ell (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAvop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    D.vLet k r z z' j hj l e (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [AAop_zero]; simp
  · rw [AAvop_zero]; simp

theorem uwG_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      D.uwG k r z z' (fun _ : B.Mat k r => (0 : E)) j hj w e = fun _ => 0
  | [], _ => rfl
  | l :: w, e => by
    simp only [D.uwG]
    rw [uwG_zero z z' j hj w _]
    exact vLet_zero z z' j hj l _

end gloc

theorem continuous_gN {k r : ℕ} : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

theorem topCls_uwG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : CutEX.TopCls Bs F) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) :
    CutEX.TopCls Bs (D.uwG k r Bs.z Bs.z' F r le_rfl w e) := by
  obtain ⟨⟨hsm, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, ⟨K, hK, h0K, hDK⟩⟩ := hF
  let S : Set (B.Mat k r) := {x | x ∈ B.GV k r ∧ F x ≠ 0}
  have hDc : Continuous (fun x : B.Mat k r => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _).continuous
  have hvan : ∀ x ∈ (closure S)ᶜ, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x = 0 := by
    intro x hx hxG
    have hz : ∀ y ∈ (closure S)ᶜ, y ∈ B.GV k r → F y = (fun _ => (0 : Wq →L[ℂ] Wp)) y := by
      intro y hy hyG
      by_contra hne
      exact hy (subset_closure ⟨hyG, hne⟩)
    rw [uwG_congrG Bs.z Bs.z' r le_rfl isClosed_closure.isOpen_compl hz w e x hx hxG, uwG_zero]
  have hcl : ∀ x, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x ≠ 0 → x ∈ closure S := by
    intro x hxG hne
    by_contra hx
    exact hne (hvan x hx hxG)
  have hDcl : ∀ x ∈ closure S, Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩ ∈ K := by
    have hsub : S ⊆ (fun x => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) ⁻¹' K := fun x hx => hDK x hx.1 hx.2
    exact fun x hx => closure_minimal hsub (hK.isClosed.preimage hDc) hx
  refine ⟨⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩, ⟨K, hK, h0K, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hD : Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩ = 0
    · have hg₀S : g₀ ∈ (closure S)ᶜ := fun h => h0K (hD ▸ hDcl g₀ h)
      exact ⟨(closure S)ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hg₀S, contDiffOn_const,
        fun x hx hxG => hvan x hx hxG⟩
    · exact PBG.uwG_mem Bs.z Bs.z' r le_rfl hsm w e g₀ hD hg₀
  · intro g hg hne
    have hsub : S ⊆ {x | B.gN x ≤ R} := fun x hx => hR x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_gN continuous_const) (hcl g hg hne)
  · intro g hg hne
    have hsub : S ⊆ {x | ε ≤ Gf k r Bs.z Bs.z' x} := fun x hx => hεG x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _)) (hcl g hg hne)
  · intro g hg hne
    exact hDcl g (hcl g hg hne)

end Formalism.FourierDecayAlt.P.CutEXUw

namespace Formalism.FourierDecayAlt.P

theorem unipotent_weight_top : CutEX.UwTop := by
  intro Wp Wq _ _ _ _ _ _ P p F hF w e
  exact CutEXUw.topCls_uwG p.T.base F hF w e

end Formalism.FourierDecayAlt.P
end
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutEXTop

theorem domR_pt (k i r' : ℕ) (hr' : r' = 0) (zs zs' : Fin (2 * r' + k + 1) → ℂ) (x : (Fin (i + r') → ℂ) × Q.Mx k (i + r'))
    (hx : x ∈ Q.DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs')) :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = ιLev k i r' g := by
  subst hr'
  obtain ⟨-, hxG, hxP⟩ := hx
  have himg := Formalism.FourierDecayAlt.P.level_group_image k i 0
  have hxG' : x.2 ∈ Q.Glev k (i + 0) ⟨i, by omega⟩ := hxG
  rw [himg] at hxG'
  obtain ⟨g, hgU, hgx⟩ := hxG'
  refine ⟨g, ⟨hgU, fun a => a.elim0⟩, ?_, hgx.symm⟩
  rw [← Formalism.FourierDecayAlt.P.WordCorrespondence.ggl_lift zs zs' g, hgx]
  exact hxP

theorem domR_pt_cast (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0) {z z' : Fin (2 * n + k + 1) → ℂ}
    {zs zs' : Fin (2 * r' + k + 1) → ℂ} (hz : D.castV hn (liftVec k i r' zs) = z)
    (hz' : D.castV hn (liftVec k i r' zs') = z') (x : (Fin n → ℂ) × Q.Mx k n) (hx : x ∈ Q.DomR k n z z') :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = D.castM hn (ιLev k i r' g) := by
  subst hn
  subst hz
  subst hz'
  obtain ⟨g, h1, h2, h3⟩ := domR_pt k i r' hr' zs zs' x hx
  exact ⟨g, h1, h2, h3⟩

theorem gv_iff_glev (k ρ : ℕ) (hρ : ρ = 0) (γ : B.Mat k ρ) : γ ∈ B.GV k ρ ↔ γ ∈ Q.Glev k ρ (Fin.last ρ) := by
  subst hρ
  constructor
  · intro h
    exact ⟨h, fun a => a.elim0⟩
  · intro h
    exact h.1

end Formalism.FourierDecayAlt.P.CutEXTop

open Formalism.FourierDecayAlt.P.CutEXTop in
theorem Formalism.FourierDecayAlt.P.top_point_existence : Formalism.FourierDecayAlt.P.CutEX.TopPt := by
  intro Wp Wq _ _ _ _ _ _ P p
  refine ⟨fun x hx => ?_, fun γ => gv_iff_glev P.k (P.r - P.r) (by omega) γ⟩
  exact domR_pt_cast P.k P.r P.r (P.r - P.r) (by omega) (by omega) (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) x hx
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem derivative_local_representative : RdVRep := by
  intro k r E _ _ X U F f hX hU hc he h hh hhG
  have hc' : ContDiffOn ℝ (((1 : ℕ∞) : WithTop ℕ∞)) F U := by exact_mod_cast hc
  refine ⟨LieDecompositionLocal.rdV_eq_fderiv (m := 1) le_rfl hU hh hhG hc' he hX, ?_⟩
  have hd : DifferentiableAt ℝ F h :=
    (hc.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hh)
  have hloc : Q.LdV X f h = Q.LdV X F h := by
    show deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * h)) 0 =
      deriv (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * h)) 0
    apply Filter.EventuallyEq.deriv_eq
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * h) := by
      have h1 := (gpMulR h).continuous.comp (B5.curve_contDiff (1 : B.Mat k r) X).continuous
      refine h1.congr fun t => ?_
      simp [gpMulR_apply]
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * h ∈ U := by
      apply hcont.continuousAt.preimage_mem_nhds
      have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * h = h := by simp
      rw [h0]
      exact hU.mem_nhds hh
    filter_upwards [hev] with t ht
    exact he _ ht (WeylGroupFacts.uh_mul (B5.exp_mem hX t) hhG)
  rw [hloc]
  exact gp_ldV X h F hd

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
