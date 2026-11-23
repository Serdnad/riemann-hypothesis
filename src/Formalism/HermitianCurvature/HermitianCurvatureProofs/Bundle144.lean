module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLEigPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem alg {ι : Type} [Fintype ι] [DecidableEq ι] (Qs : ι → (Wq →L[ℂ] Wq)) (x : ι → ℂ → ℂ)
    (C : ℂ → (Wq →L[ℂ] Wq)) (E : Wq →L[ℂ] Wp)
    (hQQ : ∀ ρ σ, (Qs ρ).comp (Qs σ) = if ρ = σ then Qs ρ else 0) (hsum : ∑ ρ, Qs ρ = 1)
    (hsep : ∀ ρ σ, ρ ≠ σ → ∃ Y, x ρ Y ≠ x σ Y)
    (hid : ∀ Y, E.comp (∑ σ, x σ Y • Qs σ) = E.comp (C Y)) (ρ : ι) :
    E.comp (Qs ρ) = E ↔ ∀ (Y : ℂ) (v : Wq), E (C Y v) = x ρ Y • E v := by
  have hQv : ∀ ρ σ v, Qs ρ (Qs σ v) = if ρ = σ then Qs ρ v else 0 := by
    intro ρ σ v
    have h := congrArg (fun T : Wq →L[ℂ] Wq => T v) (hQQ ρ σ)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    split_ifs <;> simp
  have hEC : ∀ Y v, E (C Y v) = ∑ σ, x σ Y • E (Qs σ v) := by
    intro Y v
    have h := congrArg (fun T : Wq →L[ℂ] Wp => T v) (hid Y)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h]

    simp [map_sum]
  have hEv : ∀ v, E v = ∑ σ, E (Qs σ v) := by
    intro v
    have h : (∑ σ, Qs σ) v = v := by rw [hsum, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← h]

    rw [ContinuousLinearMap.sum_apply, map_sum]
  constructor
  · intro h Y v
    have hE : ∀ w, E (Qs ρ w) = E w := fun w => congrArg (fun T : Wq →L[ℂ] Wp => T w) h
    have hσ : ∀ σ, E (Qs σ v) = if ρ = σ then E v else 0 := by
      intro σ
      rw [← hE (Qs σ v), hQv]
      split_ifs
      · exact hE v
      · exact map_zero E
    rw [hEC]
    simp [hσ, Finset.sum_ite_eq]
  · intro h
    have h0 : ∀ σ, σ ≠ ρ → ∀ v, E (Qs σ v) = 0 := by
      intro σ hσ v
      obtain ⟨Y, hY⟩ := hsep ρ σ (Ne.symm hσ)
      have h1 := h Y (Qs σ v)
      rw [hEC] at h1
      have h2 : ∑ τ, x τ Y • E (Qs τ (Qs σ v)) = x σ Y • E (Qs σ v) := by
        simp only [hQv]
        rw [Finset.sum_eq_single σ]
        · simp
        · intro τ _ hτ
          simp [hτ]
        · simp
      rw [h2] at h1
      have h3 : (x σ Y - x ρ Y) • E (Qs σ v) = 0 := by rw [sub_smul, h1, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hY))
    ext v
    rw [ContinuousLinearMap.comp_apply, hEv v, Finset.sum_eq_single ρ]
    · intro σ _ hσ
      exact h0 σ hσ v
    · simp

end KLEigPf

open KLEigPf in
theorem lie_eigenvalue_holds : KLEig := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hE
  obtain ⟨hpl, hk, hcs, hL, -, -, hQ⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => E) with hφdef
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)
    · intro q hq'
      rw [hφdef, Set.indicator_of_mem hq']
      have hst := hcs.2 q.2 ζ hq'.2 hζ'
      intro p hp
      exact hE p (hst ▸ hp)
    · intro q hq'
      exact Set.indicator_of_notMem hq' _
  have hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  obtain ⟨Φ, hΦ, hΦr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hval : Φ c0 g = E := by
    have h1 := congrFun hΦr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1
    exact h1
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq
  set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hx1 : ∀ Y : ℂ, (d.x Y).1 = X.fn 5 * X.t Y 1 1 := by
    intro Y
    have h : d.x Y = d.L.GGi * X.QQ Y 1 1 := by
      rw [hQ]
      simp only [Q.NFData.QQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
      rw [← mul_assoc, d.L.GGi_GG, one_mul]
    show Formalism.FourierDecayAlt.P5.Kfp.fstAlg _ (d.x Y) = _
    rw [h, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  let C : ℂ → (Wq →L[ℂ] Wq) := fun Y =>
    LinearMap.toContinuousLinearMap (qdet (Qr.EB Bs.π' Fr) (Y + ((P.k : ℂ) - 2) / 2))
  have hid : ∀ Y, E.comp (∑ σ, M.xC P σ Y • Qρ σ) = E.comp (C Y) := by
    intro Y
    ext v
    have hk1 := hK.2.2.2 (fun σ => M.xC P σ Y) Φ' qq
    have hk2 := congrArg (fun L : Wq →L[ℂ] Wp => L v) hk1
    have hact := Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hz hz' Bs.π'_rep Bs.π'_cont hx Fr hFr Y Φ' v
    have hκx : (d.κ fun σ => M.xC P σ Y) = d.x Y := rfl
    rw [hκx, hx1 Y] at hk2
    change (((X.fn 5 * X.t Y 1 1) Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 g v =
      (Φ c0 g) ((∑ σ, M.xC P σ Y • Qρ σ) v) at hk2
    rw [hact, hval] at hk2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hk2]
    show (Φ c0 g) _ = _
    rw [hval]
    rfl
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have hsep : ∀ ρ σ : M.Ty P, ρ ≠ σ → ∃ Y, M.xC P ρ Y ≠ M.xC P σ Y :=
    fun ρ σ h => ⟨(Y₀ : ℂ), fun he => h (hY₀ he)⟩
  classical
  exact alg Qρ (fun σ Y => M.xC P σ Y) C E hK.1 hK.2.1 hsep hid ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section lift

variable {k : ℕ}

theorem frame_lift_list {i r' m : ℕ} (vs : List (Fin (2 * r' + k + 1) → ℂ)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k (i + r') (vs.map (liftVec k i r')) (fun c => liftVec k i r' (Bs c)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => (PI.QnLevBasicsW.level_group_isotropic_vector k i r' (Bs a) (h1 a)).1, fun a b => ?_, fun a x hx => ?_⟩
  · rw [PIQnLT.herm_liftVec]; exact h2 a b
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    rw [PIQnLT.herm_liftVec]
    exact h3 a v hv

theorem frame_lift_cast {i r' n m : ℕ} (hn : i + r' = n) (vs : List (Fin (2 * r' + k + 1) → ℂ))
    (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k n (vs.map fun v => D.castV hn (liftVec k i r' v)) (fun c => D.castV hn (liftVec k i r' (Bs c))) := by
  subst hn
  simp only [JCTx5.castV_rfl]
  exact frame_lift_list vs Bs h

theorem capRep_lift_cast {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {i r' n m : ℕ} (hn : i + r' = n)
    (π0 : Mx k n → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (w : ℂ) (v : Wp) :
    capRep k n π0 (fun c => D.castV hn (liftVec k i r' (Bs c))) w v =
      capRep k r' (fun y => π0 (D.castM hn (ιLev k i r' y))) Bs w v := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact JCTx5.capRep_lift π0 Bs w v

theorem castV_mulVec_lift {i r' n : ℕ} (hn : i + r' = n) (M : B.Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    D.castM hn (ιLev k i r' M) *ᵥ D.castV hn (liftVec k i r' v) = D.castV hn (liftVec k i r' (M *ᵥ v)) := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact PIQnLT.mulVec_liftVec M v

end lift

section types

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tp_eigen_lev {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (ρ : M.Ty P) (w : ℂ) (u : Wp) :
    capRep P.k (P.r - P.r) (p.T.bs P.r).π (fun a => m₀r *ᵥ Bs' a) w (p.TP.E ρ u) =
      M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • p.TP.E ρ u := by
  have hn : P.r + (P.r - P.r) = P.r := by omega
  obtain ⟨hν, hm, hbase⟩ := hLF
  have hB1 := Topx1.vecw_frame_fwd (p.T.bs P.r) hbase hB
  have hB2 := frame_lift_cast hn _ _ hB1
  have ez : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have ee : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← castV_mulVec_lift hn, hm, hν]
  simp only [List.map_cons, List.map_nil, ez, ee] at hB2
  have h := p.TP.eigen _ hB2 ρ w u
  rw [capRep_lift_cast hn] at h
  have hπ : (fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y))) = (p.T.bs P.r).π :=
    funext fun y => (p.T.π_lev P.r le_rfl y).symm
  rw [hπ] at h
  exact h

theorem aeval_intertwine (V : Wq →L[ℂ] Wp) (R : Module.End ℂ Wq) (Lf : Module.End ℂ Wp)
    (h : ∀ v, V (R v) = Lf (V v)) (p : Polynomial ℂ) : ∀ v, V (Polynomial.aeval R p v) = Polynomial.aeval Lf p (V v) := by
  induction p using Polynomial.induction_on with
  | C a => intro v; simp
  | add p q hp hq => intro v; simp [hp, hq]
  | monomial n a ih =>
    intro v
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eR : Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n) * R := by rw [map_mul, Polynomial.aeval_X]
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    rw [e1, eR, eL, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_eigen (Lf : Module.End ℂ Wp) (x : Wp) (c : ℂ) (h : Lf x = c • x) (p : Polynomial ℂ) :
    Polynomial.aeval Lf p x = p.eval c • x := by
  induction p using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a ih =>
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    have ev : (Polynomial.C a * Polynomial.X ^ n * Polynomial.X).eval c =
        (Polynomial.C a * Polynomial.X ^ n).eval c * c := by rw [Polynomial.eval_mul, Polynomial.eval_X]
    rw [e1, eL, Module.End.mul_apply, h, map_smul, ih, smul_smul, ev, mul_comm]

theorem poly_types {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (V : Wq →L[ℂ] Wp)
    (hV : PBI.GrpInt (p.T.bs P.r) ν'r m₀r V) (hex : ∑ ρ : M.Ty P, (p.TP.E ρ).comp V = V)
    (Y₀ : ℂ) (q : Polynomial ℂ) (v : Wq) :
    V (Polynomial.aeval (qdet (Qr.EB (p.T.bs P.r).π' Bs') (Y₀ + ((P.k : ℂ) - 2) / 2)) q v) =
      ∑ ρ : M.Ty P, q.eval (M.xC P ρ Y₀) • p.TP.E ρ (V v) := by
  set S := p.T.bs P.r
  have hbase := hLF.2.2
  have hBz' : IsFrameOf P.k (P.r - P.r) [S.z'] Bs' :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBz : IsFrameOf P.k (P.r - P.r) [S.z] (fun a => m₀r *ᵥ Bs' a) :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (Topx1.vecw_frame_fwd S hbase hB)
  have hglR := Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k (P.r - P.r) (P.k - 1) S.z' S.π' Bs' ⟨S.π'_rep, S.π'_cont⟩ hBz'
  have hglL := Formalism.FourierDecayAlt.P.frame_general_linear Wp P.k (P.r - P.r) (P.k - 1) S.z S.π (fun a => m₀r *ᵥ Bs' a)
    ⟨S.π_rep, S.π_cont⟩ hBz
  set w0 : ℂ := Y₀ + ((P.k : ℂ) - 2) / 2
  have hint : ∀ v, V (qdet (Qr.EB S.π' Bs') w0 v) = qdet (Qr.EB S.π (fun a => m₀r *ᵥ Bs' a)) w0 (V v) := by
    intro v
    rw [← hglR.2, ← hglL.2]
    exact (PBI.gen_capRep_intertwine S hbase V hV hB w0 v).symm
  rw [aeval_intertwine V _ _ hint q v]
  conv_lhs => rw [← hex]

  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  refine aeval_eigen _ _ _ ?_ q
  rw [← hglL.2, tp_eigen_lev p ν'r m₀r hLF hB ρ w0 (V v)]
  congr 2
  ring

end types

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end

section

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

abbrev MJ (j : ℕ) : Type := Matrix (Fin j) (Fin j) ℂ

def levi (k r j : ℕ) (x : MJ j) : Q.Mx k r := Matrix.of fun p q =>
  if hp : p.val < j then (if hq : q.val < j then x ⟨p.val, hp⟩ ⟨q.val, hq⟩ else 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      -conj (x ⟨2 * r + k - q.val, by omega⟩ ⟨2 * r + k - p.val, by omega⟩) else 0)
  else 0

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def EZ {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) h Z

def EZs {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ)) h Z

def ParamCommF {j : ℕ} (T : (MJ j → E) → (MJ j → E)) : Prop :=
  ∀ (U : Set (ℂ × (Fin j → Fin j → ℂ))) (κ : ℂ → MJ j → E), IsOpen U →
    U ⊆ {q | (Matrix.of q.2).det ≠ 0} →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => T (κ q.1) (Matrix.of q.2)) U ∧
    ∀ q ∈ U, PBP.dz (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dz (fun τ => κ τ Z) q.1) (Matrix.of q.2) ∧
      PBP.dzb (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) (Matrix.of q.2)

structure ZOp {j : ℕ} (T : (MJ j → E) → MJ j → E) : Prop where
  loc : ∀ (h₁ h₂ : MJ j → E) (Z : MJ j), h₁ =ᶠ[𝓝 Z] h₂ → T h₁ Z = T h₂ Z
  add : ∀ (V : Set (MJ j)) (h₁ h₂ : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h₁ V →
    ContDiffOn ℝ ∞ h₂ V → ∀ Z ∈ V, T (h₁ + h₂) Z = T h₁ Z + T h₂ Z
  smul : ∀ (V : Set (MJ j)) (c : ℂ) (h : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h V →
    ∀ Z ∈ V, T (c • h) Z = c • T h Z
  par : ParamCommF T

end Formalism.FourierDecayAlt.P.WirtingerOperators

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

def CurveLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (x : MJ j) (t : ℝ),
    x0 k r j hj Z τ γ * NormedSpace.exp ((t : ℂ) • levi k r j x) =
      x0 k r j hj (Z * NormedSpace.exp ((t : ℂ) • x)) τ γ

def HpartLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j ≤ r) (a b : Fin j),
    hpart1 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) ∧
      hpart1 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ))

def XiCoef : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (a : Fin j)
    (p : Fin (2 * r + k + 1)),
    herm (Hpk k r) (x0 k r j hj Z τ γ *ᵥ bvec p) (bvec (eI k r (Fin.castLE (by omega) a))) =
      if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def XiCoefV : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → ∀ (a : Fin j) (p : Fin (2 * r + k + 1)),
    ((x0 k r j hj Z τ γ)⁻¹ *ᵥ bvec (eI k r (Fin.castLE (by omega) a))) p =
      if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0

def XiMem : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Q.Glev k r 0

def XiSmooth : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ) {Z | Z.det ≠ 0}

def ZOpRd : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (x : MJ j), ZOp (E := E) (fun h => RdV x h)

def DzSlice : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (ℂ × (Fin j → Fin j → ℂ)))
    (κ : ℂ → MJ j → E), IsOpen U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U → ∀ τ₀ : ℂ,
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dz (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U} ∧
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dzb (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U}

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end
