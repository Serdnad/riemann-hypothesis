module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle363
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle372
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle463
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaDer

theorem schr_comp_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  have hh : ⅟(2 : R) + ⅟(2 : R) = 1 := by rw [← two_mul, mul_invOf_self]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, add_assoc]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * hh

theorem exists_equiv {A : Type} [CommRing A] {m k d : ℕ} {G H : Matrix (Fin m) (Fin m) A} (hHG : H * G = 1)
    (hGH : G * H = 1) (e : Fin k ≃ Fin d) :
    ∃ T : Matrix (Fin m) (Fin k) A ≃+ Matrix (Fin d) (Fin m) A,
      (∀ u, T u = uᵀ.submatrix e.symm id * G) ∧ ∀ x, T.symm x = ((x * H)ᵀ).submatrix id e := by
  refine ⟨{ toFun := fun u => uᵀ.submatrix e.symm id * G
            invFun := fun x => ((x * H)ᵀ).submatrix id e
            left_inv := fun u => ?_
            right_inv := fun x => ?_
            map_add' := fun u v => ?_ }, fun u => rfl, fun x => rfl⟩
  · ext i j
    simp [Matrix.mul_assoc, hGH]
  · simp [Matrix.transpose_submatrix, Matrix.submatrix_submatrix, Matrix.mul_assoc, hHG]
  · simp [Matrix.transpose_add, Matrix.submatrix_add, Matrix.add_mul]

private theorem rho_add_twisted_operators {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ) (p q : W)
    (Φ : (κ → R) → ℂ) (z : κ → R) :
    co.rho ψ (p + q) Φ z = ψ (-(⅟(2 : R) * B p q)) * co.rho ψ p (co.rho ψ q Φ) z := by
  simp only [GlobalTheory.WeilM.Darboux.rho]
  rw [schr_comp_apply, ← co.form, map_add (f := _), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]


private theorem tendsto_add_smul_punctured_of_differentiableAt {D : D7} {n d m : ℕ} (u₀ : Matrix (Fin n) (Fin d) (AE D)) (e' : Fin d ≃ Fin m)
    (G : Matrix (Fin n) (Fin n) (AE D)) :
    Continuous fun t : ℝ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e'.symm id * G := by
  have c0 : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F) := GlobalTheory.ThetaLineDeriv.continuous_realAd
  have c1 : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀ := c0.smul continuous_const
  exact (c1.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const

private theorem fin_realAd_smul_eq_zero {D : D7} (t : ℝ) (a : AE D) :
    finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • a) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) = 0 := by
    show finPart D ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    have hs : sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 := rfl
    simp only [Formalism.L2.Theta.finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, hs,
      TensorProduct.zero_tmul]
  rw [h0, zero_mul]



theorem thO_pure_deriv {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hVJ : Vs.J = -S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : ∀ i j, D.sp.cm.sig (Vs.J j i) = Vs.J i j)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ)
    (u₀ : Matrix (Fin S.rank) (Fin d) (AE D)) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (hact : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u₀) g g₁)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ L : ℝ →+ WO S X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
      GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) =
        fun x => deriv (fun t : ℝ => heisO Bs.ψ S X (L t)
          (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) 0 := by
  classical
  have hTR : NumberField.IsTotallyReal D.host.F := hBs.cm.1
  have hCh : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hdet : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (gram_det_ne S)
  have hinc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
    simp
  have hinc' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨T, hT, hTs⟩ := exists_equiv (A := AE D) hinc' hinc e
  have hpt : ∀ x, GlobalTheory.TripleRead.ptO S.gram e x = T.symm x := fun x => (hTs x).symm
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F v} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA g φ hφ hstd
  have hΦ' := GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ hstd
  have hd : ∀ z, HasDerivAt (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ z) 0 :=
    fun z => hact _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd) z

  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram)ᵀ := by
    ext i j
    have h1 := hV j i
    rw [hVJ] at h1
    simp only [Matrix.neg_apply, map_neg, neg_inj] at h1
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR, h1]
  have h2 : (⅟(2 : AF D.host.F)) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [show (2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  have hphase : ∀ (x : WO S X) (q : Matrix (Fin S.rank) (Fin d) (AE D)),
      symplOH S X x (T q) = ⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x) q := by
    intro x q
    conv_lhs => rw [← T.apply_symm_apply x]
    have hh := GlobalTheory.SquareAgree.hTens_transpose_mul (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) hinc' hG (T.symm x) q
    rw [← hT, ← hT] at hh
    have hs := GlobalTheory.WeilSchrodinger.symp_eq_symplO D S X (X.gramᵀ) (D.host.xi0 • S.gram⁻¹) 1 rfl (by rw [one_smul])
      (T (T.symm x)) (T q)
    simp only [symplOH, ← hs, h2, GlobalTheory.WeilM.symp, one_mul, neg_one_mul, map_neg]
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hVJ]
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • Matrix.reindex e.symm e.symm (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hJW, Matrix.reindex_apply, map_mul]
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
    have e4 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [e4, e3, hh, e1, e2, map_neg]

  let ln : ℝ →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
    AddMonoidHom.mk' (fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (fun s t => by simp only [GlobalTheory.ThetaLineDeriv.realAd_add, add_smul])
  refine ⟨T.toAddMonoidHom.comp ln, ?_, ?_, ?_⟩
  · have hfun : (fun t => (T.toAddMonoidHom.comp ln) t) =
        fun t => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram :=
      funext fun t => hT _
    show Continuous fun t => (T.toAddMonoidHom.comp ln) t
    rw [hfun]
    exact tendsto_add_smul_punctured_of_differentiableAt u₀ e _
  · intro t
    show (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)).map (finPart D) = 0
    rw [hT, Matrix.map_mul]
    have hz : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id).map (finPart D) = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, fin_realAd_smul_eq_zero,
        Matrix.zero_apply]
    rw [hz, Matrix.zero_mul]
  · funext x
    have hfun : (fun t : ℝ => heisO Bs.ψ S X ((T.toAddMonoidHom.comp ln) t)
        (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) =
        fun t => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ (T.symm x)
          (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := by
      funext t
      show heisO Bs.ψ S X (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)) _ x = _
      simp only [heisO, GlobalTheory.TripleRead.thO, hpt, map_add (f := _), T.symm_apply_apply]
      rw [show M.co.rho Bs.ψ (T.symm x + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) =
        fun z => Bs.ψ (-(⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀))) *
          M.co.rho Bs.ψ (T.symm x) (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) z
        from funext (rho_add_twisted_operators M.co Bs.ψ _ _ _)]
      simp only [GlobalTheory.WeilM.thetaSum]
      rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul, hphase, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
    have hder := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr Bs.ψ hTR hCh (M.co.e u₀) hΦ hΦ' (by
      simpa only [GlobalTheory.WeilM.Darboux.rho, map_smul] using hd) (M.co.e (T.symm x))
    rw [hfun]
    simp only [GlobalTheory.WeilM.Darboux.rho, map_smul]
    rw [hder.deriv]
    simp only [GlobalTheory.TripleRead.thO, hpt, GlobalTheory.WeilM.Darboux.rho]

end GlobalTheory.ThetaDer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisDeriv

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

section Gen

variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ : Type} [Fintype κ]

theorem rho_rho (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (w v : W) (Φ : (κ → AF F) → ℂ) :
    d.rho ψ w (d.rho ψ v Φ) = ψ (⅟(2 : AF F) * B w v) • d.rho ψ (w + v) Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add (f := _), Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  rw [d.form]
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  linear_combination (-((d.e w).1 ⬝ᵥ (d.e v).2)) * h2

theorem thetaSum_smul (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

end Gen

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}

theorem algD_le_schA (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hM : M.IsGood ψ) : algD M ψ emb ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, -, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem exists_actsD_mem_Pol (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evI F) u) (g : SInf F (Fin n × Fin d))
    (hg : g ∈ M.Pol ψ emb) : ∃ g₁ ∈ M.Pol ψ emb, ActsD (evI F) (M.heisLine ψ u) g g₁ := by
  obtain ⟨Dr, hDr⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F Y.J) (incM F Wd.J) M.co hψ
  have hSD := (hDr u hu g).1
  have hA : ActsD (evI F) (M.heisLine ψ u) g (Dr u g) :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) g (Dr u g) (Dr u g)).1 (M.heisLine ψ u)
      (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr]) hSD
  refine ⟨Dr u g, Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ hA, hA⟩

theorem exists_deriv_algD (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (hψ : IsStd ψ) (hM : M.IsGood ψ) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evI F) u) :
    ∀ Φ ∈ algD M ψ emb, ∃ Φ' ∈ algD M ψ emb,
      ∀ x, HasDerivAt (fun t : ℝ => M.co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0 := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa [Darboux.rho, schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add a b _ _ ha hb =>
    obtain ⟨a', ha', hda⟩ := ha
    obtain ⟨b', hb', hdb⟩ := hb
    refine ⟨a' + b', add_mem ha' hb', fun x => ?_⟩
    have e : (fun t : ℝ => M.co.rho ψ (realAd F t • u) (a + b) x) =
        fun t => M.co.rho ψ (realAd F t • u) a x + M.co.rho ψ (realAd F t • u) b x := by
      funext t; simp [Darboux.rho, schr, mul_add]
    rw [e]
    exact (hda x).add (hdb x)
  | smul c a _ ha =>
    obtain ⟨a', ha', hda⟩ := ha
    refine ⟨c • a', Submodule.smul_mem _ c ha', fun x => ?_⟩
    have e : (fun t : ℝ => M.co.rho ψ (realAd F t • u) (c • a) x) =
        fun t => c * M.co.rho ψ (realAd F t • u) a x := by
      funext t; simp [Darboux.rho, schr]; ring
    rw [e]
    simpa using (hda x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨g, φ, hg, hSB, hev, rfl⟩ := hΦ
    obtain ⟨g₁, hg₁, hA⟩ := exists_actsD_mem_Pol M ψ emb hψ u hu g hg
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure g₁ φ, Submodule.subset_span ⟨g₁, φ, hg₁, hSB, hev, rfl⟩, fun x => ?_⟩
    exact hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hSB hstd) x

end Model

end GlobalTheory.SquareAgree.HeisDeriv

namespace GlobalTheory.SquareAgree.HeisDeriv

theorem heisDeriv_algD : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ f : WO S X → ℂ, IsDatum M ψ cS ΦD f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        ∃ ΦD' ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD' (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS ΦD hΦD f hf τ z
  subst hψ
  obtain ⟨hline, hAt⟩ := GlobalTheory.T.archimedeanLine_eq_realScalar_smul_supported D θ hθ τ z
  have hsm : ∀ (a : AF D.host.F) (u : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • u) = a • cS u := by
    intro a u
    rw [hcS, hcS]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_mul_assoc, id]
  set w₀ := lineAt θ τ z 1 with hw₀
  set u := cS.symm w₀ with hu_def
  have hcu : cS u = w₀ := cS.apply_symm_apply w₀
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u := by
    intro a ha
    apply cS.injective
    rw [hsm, hcu, map_zero]
    exact hAt a ha
  have hLt : ∀ t : ℝ, cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) = lineAt θ τ z t := by
    intro t
    rw [hsm, hcu, hline t]
  have hstd := hBs.std
  obtain ⟨Φ', hΦ', hder⟩ := exists_deriv_algD M Bs.ψ Bs.emb hstd hM u hu ΦD hΦD
  refine ⟨Φ', hΦ', algD_le_schA M Bs.ψ Bs.emb hM hΦ', fun u' => ?_⟩
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    simp
  have key : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) ΦD)) =
      heisO Bs.ψ (sgn ε S) X (lineAt θ τ z t) f (cS u') := by
    intro t
    rw [rho_rho, thetaSum_smul, hf.2, map_add (f := _), ← hLt t, heisO, symplOH, ← GlobalTheory.T.schrodingerModel_symplectic_eq_orientedPair D ε S X e Vs Ws hJ hJW cS hcS, h2]
  have hd := GlobalTheory.T.hasDerivAt_thetaSum_heisenbergLine M.co Bs.ψ hstd u hu ΦD (algD_le_schA M Bs.ψ Bs.emb hM hΦD) Φ' (algD_le_schA M Bs.ψ Bs.emb hM hΦ')
    hder u'
  simp only [key] at hd
  exact hd.deriv.symm

end GlobalTheory.SquareAgree.HeisDeriv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w),
    M.IsGood ψ → GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  first | exact @GlobalTheory.TripleAssembly.darbAlg_le_schA | exact GlobalTheory.TripleAssembly.darbAlg_le_schA | (intros; apply GlobalTheory.TripleAssembly.darbAlg_le_schA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowApprox

theorem ptF_eq_fock {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.ChainFr.ptF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f p =
      GlobalTheory.Grid.fock ψ θ true S T f p := by
  have : (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
  rw [this]
  rfl

theorem isFinVec_of_isVacF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D}
    {f : WO S.V T.V → ℂ}
    (h : GlobalTheory.ChainFr.IsVacF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f) :
    GlobalTheory.Grid.IsFinVec ψ θ true S T f :=
  ⟨h.1, fun τ => by have := h.2 τ; rwa [GlobalTheory.PairLift.cart_frSgn] at this⟩

end GlobalTheory.UpArrowApprox

namespace GlobalTheory.UpArrowApprox

end GlobalTheory.UpArrowApprox
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch


theorem _root_.GlobalTheory.T.tensorSymplecticForm_at_split_finite_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → ∀ (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) x → At (evFin F v) u →
    ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u) - pairM (coY σ X Y t b c x) (coX t b c u)) := by
  first | exact @GlobalTheory.FlipMatch.SplitSymp.symp_at_split | exact GlobalTheory.FlipMatch.SplitSymp.symp_at_split | (intros; apply GlobalTheory.FlipMatch.SplitSymp.symp_at_split <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z : FrPt Xo c Ω), hkRelFr P p i (hkTr Xo c p) Ω y C z → ∃ f f', HkWith p y z f f' := by
  first | exact @GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | exact GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr | (intros; apply GlobalTheory.HkIntegral.exists_hkWith_of_hkRelFr <;> assumption)
end
