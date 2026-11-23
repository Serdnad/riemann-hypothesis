module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReflectionTransposeEntriesMem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Lagrange
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

theorem star_algebraMap_real (P : M.Par) (Y : ℝ) :
    star (algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ)) = algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ) := by
  rw [← algebraMap_star_comm, Complex.star_def, Complex.conj_ofReal]

theorem star_Ts_mul_0 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    star ((Wd.Ts σ Y * V) 0 0) =
      star (V 0 0) * star (algebraMap ℂ (MA.A P (MA.DQ P)) Y + σ.p) + -(star (V 1 0) * star σ.c) := by
  simp only [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, star_add, star_mul, star_neg, neg_mul, mul_neg]

theorem star_Ts_mul_1 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    star ((Wd.Ts σ Y * V) 1 0) = star (V 0 0) * star σ.ci := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul]

theorem actA_sp (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).p) f = fun ρ => -MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

theorem actA_sc' (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).c) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

theorem actA_sci (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).ci) f =
      fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem vabs_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℝ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Φ) =
          MA.actA P (star (Vp P Y i 0 0)) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) Φ) =
          MA.actA P (star (Vp P Y i 1 0)) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, star_one, star_zero, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    set l : Fin P.r := ⟨i, h⟩ with hl
    have hv : Q.vABs (E := Wq →L[ℂ] Wp) P.r (Y : ℂ) (i + 1) =
        (fun f => (Q.vABs P.r (Y : ℂ) i).1 ((Y : ℂ) • f - pbOp l f) - (Q.vABs P.r (Y : ℂ) i).2 (cbOp l f),
          fun f => (Q.vABs P.r (Y : ℂ) i).1 (cbiOp l f)) := by
      simp only [Q.vABs, dif_pos h, hl]
    set Ψ := (Y : ℂ) • Φ - Q.crd (pbOp l) Φ with hΨ
    have hpb : FamR P Bs Dc (Q.crd (pbOp l) Φ) := famR_opL hΦ l 3
    have hcb : FamR P Bs Dc (Q.crd (cbOp l) Φ) := famR_opL hΦ l 4
    have hcbi : FamR P Bs Dc (Q.crd (cbiOp l) Φ) := famR_opL hΦ l 5
    have hΨf : FamR P Bs Dc Ψ := famR_sub (famR_smul hΦ _) hpb
    obtain ⟨⟨hA, tA⟩, -⟩ := ih (Nat.le_of_lt h) Dc Ψ hΨf
    obtain ⟨-, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc _ hcb
    obtain ⟨⟨hA', tA'⟩, -⟩ := ih (Nat.le_of_lt h) Dc _ hcbi
    have e0 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) (i + 1)) 0) Φ =
        Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Ψ - Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) (Q.crd (cbOp l) Φ) := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) (i + 1)) 1) Φ =
        Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) (Q.crd (cbiOp l) Φ) := by
      rw [hv]; rfl
    have tΨ : trR P Bs.μsec e Ψ =
        MA.actA P (star (algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ) + (MA.siteA P (MA.DQ P) l).p))
          (trR P Bs.μsec e Φ) := by
      rw [hΨ, trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hΦ _) ρ) (fun ρ => smR hpl hk he hpb ρ),
        trR_smul, trR_pb hpl hk he hΦ, star_add, star_algebraMap_real, actA_add, actA_algebraMap, actA_sp,
        sub_eq_add_neg]
      rfl
    have tcb : trR P Bs.μsec e (Q.crd (cbOp l) Φ) =
        MA.actA P (star (MA.siteA P (MA.DQ P) l).c) (trR P Bs.μsec e Φ) := by
      rw [actA_sc']
      exact trR_mul hpl hk he hΦ _ hcb (fun c => star (c l)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tcbi : trR P Bs.μsec e (Q.crd (cbiOp l) Φ) =
        MA.actA P (star (MA.siteA P (MA.DQ P) l).ci) (trR P Bs.μsec e Φ) := by
      rw [actA_sci]
      exact trR_mul hpl hk he hΦ _ hcbi (fun c => (star (c l))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hA hB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hA ρ) (fun ρ => smR hpl hk he hB ρ), tA, tB, tΨ, tcb,
        Vp_succ P Y i h, star_Ts_mul_0, actA_add, actA_mul, actA_neg, actA_mul, sub_eq_add_neg]
    · rw [e1]; exact hA'
    · rw [e1, tA', tcbi, Vp_succ P Y i h, star_Ts_mul_1, actA_mul]

end ind

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

open VLem

theorem gauge_conj_vector_transition : GVsTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y a
  have h := vabs_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
  rw [sitesCommonSpace_v0_eq_Vp]
  fin_cases a
  · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
  · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section lev

variable {k : ℕ}

theorem det_corner_matrix_level_zero {r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    (Zhat k r' z z' g).det = Q.zetaL k r' z z' (Fin.last r') g := by
  subst hr
  exact (Matrix.det_fin_one _).trans rfl

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem grpInt_at_dframe (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    GrpInt (p.T.bs P.r) ν'r m₀r ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) := by
  have hG : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' := hx.2.2
  have hT := mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos
  have hdet : (Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀).det ≠ 0 := by
    rw [det_corner_matrix_level_zero (Nat.sub_self P.r), hζ]
    intro h0
    rw [h0, map_zero] at hG
    linarith
  have hdom : ((x.1, γ₀) : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r) ∈
      Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := by
    refine ⟨hx.1, ⟨hγG, fun a _ => ?_⟩, ?_⟩
    · exfalso
      have ha := a.isLt
      revert ha
      show ¬ (a.val < P.r - P.r)
      omega
    · show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
        Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
      rw [hζ]
      exact hG
  obtain ⟨-, -, he⟩ := Ψ.2
  intro hB hhB hBν
  have e := he (x.1, γ₀) hdom _ (Formalism.FourierDecayAlt.P.Topx1.vecw_conj_mem _ hLev.2.2 hhB) _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hhB)
  try dsimp only at e
  have hc := Formalism.FourierDecayAlt.P.PBI.dframe_commute _ (Nat.sub_self P.r) hLev.2.2 hγG hγF hdet hhB hBν
  exact e.symm.trans (congrArg (fun g => (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 g) hc)

end place

end Formalism.FourierDecayAlt.P.PBI
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

def ClassEigenC : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : NumberField.InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    100 ≤ Cc → JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∀ v : Fin S.f,
      Q.CkLev S.G.k S.G.r 0 (2 * S.G.r + S.G.k + 1) (Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z')
          (B.JF (T v).base (f v)) ∧
        ∀ (Y : ℝ), ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z',
          Q.CV S.G.k S.G.r (Y : ℂ) (B.JF (T v).base (f v)) g = ((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v) g

theorem class_eigenvalue_constant : ClassEigenC := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hCc hB v
  obtain ⟨_, _, _, hbuilt, _, _, _, _, _, hCk, hk2, hA, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, heig⟩ := hv v
  have hpos : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
  have hA' : 100 * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ := by
    calc 100 * ((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)
        = 100 * (((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)) := by ring
      _ ≤ Cc * (((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)) :=
          mul_le_mul_of_nonneg_right hCc hpos
      _ = Cc * ((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by ring
      _ ≤ A₀ := hA
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    Formalism.FourierDecayAlt.P.CutMP.thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA'
  have hW := Formalism.FourierDecayAlt.P.jacquet_derivative_formula S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) hThr (hCC _)
  refine ⟨hW.1, ?_⟩
  intro Y g hg
  have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
  have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) (f v) :=
    Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (hCk v)
  rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ p ∂(T v).base.μSS,
      JF.xiP (T v).base p • Q.CV S.G.k S.G.r (Y : ℂ) (B.rho (T v).base p (f v)) g =
        ((S.P v Y : ℝ) : ℂ) • (JF.xiP (T v).base p • B.rho (T v).base p (f v) g) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS (T v).base] with p hp
    rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ (T v).base (Y : ℂ) (f v) p hp hCkn _ hgG]
    have hs := Formalism.FourierDecayAlt.P.B7.sgs_mem (T v).base hp hgG
    simp only [B.rho]
    rw [heig Y _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

theorem mem_om_of_mem_omP {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    {g : B.Mat S.G.k S.G.r} (hgG : g ∈ B.GV S.G.k S.G.r) (hg : g ∈ OmP S T v) :
    g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := by
  refine ⟨hgG, ?_, hg.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | hpos
  · have hl0 : l = 0 := Fin.ext h0
    subst hl0
    unfold Dmin
    have : IsEmpty (Fin ((0 : Fin (S.G.r + 2)) : ℕ)) := ⟨fun i => absurd i.isLt (by simp)⟩
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have := hg.2 ⟨l.val - 1, by omega⟩
    have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
    simpa [e] using this

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Inv

variable {A T : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype T]

theorem aeval_mem' (𝒜 : StarSubalgebra ℂ A) {x : A} (hx : x ∈ 𝒜) (p : Polynomial ℂ) :
    Polynomial.aeval x p ∈ 𝒜 := by
  refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
  · rw [Polynomial.aeval_C]; exact 𝒜.algebraMap_mem a
  · rw [map_add (f := _)]; exact 𝒜.add_mem hp hq
  · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact 𝒜.mul_mem (𝒜.algebraMap_mem a) (𝒜.pow_mem hx _)

theorem inv_mem_of_kappa (κ : (T → ℂ) →ₐ[ℂ] A) (𝒜 : StarSubalgebra ℂ A) (f : T → ℂ) (hf : κ f ∈ 𝒜) :
    κ (fun ρ => (f ρ)⁻¹) ∈ 𝒜 := by
  classical
  set N : Finset ℂ := Finset.univ.image f
  set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
  have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
    intro ρ
    have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
    have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
    simpa only [id] using h
  have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
    funext ρ
    rw [← hp ρ]
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : T => ℂ) ρ) f p
    rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    rfl
  rw [he, ← Polynomial.aeval_algHom_apply]
  exact aeval_mem' 𝒜 hf p

variable {r : ℕ}

theorem x_eq_of_start (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st) (Y : ℂ) :
    st.x Y = L.GGi * st.QQ Y 1 1 := by
  rw [hst.tau, ← mul_assoc, L.GGi_GG, one_mul]

theorem gens_of (𝒜 : StarSubalgebra ℂ A) (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st)
    (κ : (T → ℂ) →ₐ[ℂ] A) (x0 : T → ℂ → ℂ) (hx : ∀ Y, st.x Y = κ fun ρ => x0 ρ Y)
    (hxi : ∀ Y ∈ st.inv, st.xi Y = κ fun ρ => (x0 ρ Y)⁻¹)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) (hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ 𝒜) : Gens 𝒜 L st := by
  have hxm : ∀ Y : ℂ, star Y = Y → st.x Y ∈ 𝒜 := fun Y hY => by
    rw [x_eq_of_start L st hst Y]
    exact 𝒜.mul_mem (hz _ (by simp [zfns])) (hQ Y hY 1 1)
  refine ⟨hz, hQ, hxm, fun Y hYs hY => ?_⟩
  rw [hxi Y hYs]
  exact inv_mem_of_kappa κ 𝒜 (fun ρ => x0 ρ Y) (by rw [← hx Y]; exact hxm Y hY)

end Inv

section Fn

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fnVal_conj (j : Fin 6) (g : Mx k r) : conj (fnVal k r z z' (fnConj j) g) = fnVal k r z z' j g := by
  fin_cases j <;> simp [fnVal, fnConj, map_inv₀]

theorem fn_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π'))
    (hU : IntOn μ U) (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U) (j : Fin 6) :
    mkP (X.fn j) (X.fn (fnConj j)) ∈ adjAlg μ U hU := by
  refine ⟨fun Φ hΦ => hfn j Φ hΦ, fun Φ hΦ => hfn _ Φ hΦ, fun c _ Φ _ Ψ _ => ?_⟩
  show pairAt μ (X.fn j Φ) Ψ c = pairAt μ Φ (X.fn (fnConj j) Ψ) c
  unfold pairAt
  congr 1
  funext g
  by_cases hx : (c, Matrix.of g) ∈ DomR k r z z'
  · have e1 := X.fn_apply j Φ (c, Matrix.of g) hx
    have e2 := X.fn_apply (fnConj j) Ψ (c, Matrix.of g) hx
    simp only at e1 e2
    rw [e1, e2, hsInner_smul_left', hsInner_smul_right', fnVal_conj]
  · have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off Φ hx
    have h1 : (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off (X.fn j Φ) hx
    rw [h0, h1, hsInner_zero_left, hsInner_zero_left]

end Fn

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_tAdj (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U)
    (hT : ∀ Y : ℂ, star Y = Y → ∀ a b, X.QQ Y a b ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  have hD' := hD
  obtain ⟨κ, hx, hxi, -⟩ :=
    xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hAL, hQQ, -, -, -, hst⟩ := hD
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hGG, hGGi, -⟩ := hAL
  have hz : ∀ g ∈ zfns L, g ∈ adjAlg μ U hU := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hζ]; exact fn_adj X μ U hU hfn 0
    · rw [hζi]; exact fn_adj X μ U hU hfn 1
    · rw [hζb]; exact fn_adj X μ U hU hfn 2
    · rw [hζbi]; exact fn_adj X μ U hU hfn 3
    · rw [hGG]; exact fn_adj X μ U hU hfn 4
    · rw [hGGi]; exact fn_adj X μ U hU hfn 5
  have hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ adjAlg μ U hU := by
    intro Y hY i j
    rw [hQQ Y, Matrix.smul_apply]
    exact (adjAlg μ U hU).smul_mem (hT Y hY i j) _
  exact adjTop_of_gens P z z' π π' X μ L st K l0 hD' U hU hK
    (gens_of _ L st hst κ _ hx hxi hz hQ)

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end
