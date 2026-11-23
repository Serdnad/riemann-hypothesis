module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle149
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.flag_subgroups_closed_normal_cocompact' : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), IsClosed (flagN d : Set (GA D V)) ∧ ∀ M : Subgroup (GA D V), (M = _root_.GlobalTheory.MixPer.centre d ∨ M = radX d ∨ ∃ j, M = Nfix d j) → M ≤ flagN d ∧ IsClosed (M : Set (GA D V)) ∧ (M.subgroupOf (flagN d)).Normal ∧ ∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ (GQ V).subgroupOf M, ∃ k ∈ K, m = γ * k := by
  first | exact @GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact | exact GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact | (intros; apply GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.RealMat

variable {D : D7}

theorem psiT_incA (τ : D.what₂.Tau) (x : D.host.E) : Formalism.IndefR.Eqv.psiT D τ (incA D x) = tauE D τ x := by
  show Formalism.IndefR.Eqv.thetaC D τ ((fstA D.host.F 1) ⊗ₜ[D.host.F] x) = _
  rw [Formalism.IndefR.Eqv.thetaC_tmul]
  simp

theorem embA_cols {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) :
    HMul.hMul (Formalism.L2.Theta.mt S (embA d o a)) (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) =
      HMul.hMul (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) (Formalism.L2.Theta.mt A a) := by
  have e : (rat (d.i₀ * o.iA) : Mx D S.rank A.rank) = HMul.hMul d.j0 o.jA := rat_mul _ _
  rw [e, GlobalTheory.MixPer.embA_apply d o a, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]

theorem embA_cols_at {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) (τ : D.what₂.Tau) :
    (Formalism.L2.Theta.mt S (embA d o a)).map (Formalism.IndefR.Eqv.psiT D τ) * (d.i₀ * o.iA).map (tauE D τ) =
      (d.i₀ * o.iA).map (tauE D τ) * (Formalism.L2.Theta.mt A a).map (Formalism.IndefR.Eqv.psiT D τ) := by
  have e : (d.i₀ * o.iA).map (tauE D τ) =
      (rat (d.i₀ * o.iA) : Mx D S.rank A.rank).map (Formalism.IndefR.Eqv.psiT D τ) := by
    ext i j
    exact (psiT_incA τ _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, embA_cols]

theorem act_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hr : (D.sp.Y 0).rank = I.n) (k : GA D (D.sp.Y 0))
    (τ : D.what₂.Tau) {m : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin m) D.host.E) (M : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin m → Fin I.n → I.E) (hx : ∀ i j, C i j = ιE (x j (Fin.cast hr i)))
    (hC : (Formalism.L2.Theta.mt (D.sp.Y 0) k).map (Formalism.IndefR.Eqv.psiT D τ) * C.map (tauE D τ) = C.map (tauE D τ) * M) (b : Fin m) :
    uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 (pl.symm τ)) *ᵥ rv I (pl.symm τ) (x b) =
      ∑ i, M i b • rv I (pl.symm τ) (x i) := by
  subst h
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (SeeReal.phi_inst v x))
  have hcol : ∀ j, (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ (pl.symm τ) (x j i)) =
      fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    funext i
    rw [hφ, Equiv.apply_symm_apply]
    exact (congrArg (tauE D τ) (hx i j)).symm
  subst hpl
  have hT : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := rfl
  have hP := Formalism.L2.SG.EvalTIota.P_isUnit_det' (D := D) (Formalism.L2.Host.tauPl D τ)
  have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i (Formalism.IndefR.RationalEmbedding.iota D k) τ
  rw [ContinuousMulEquiv.symm_apply_apply, Formalism.IndefR.Eqv.infMat_thetaC] at hbr
  have hu := SeeReal.eq_of_conj hP hbr.symm
  have hrv : ∀ j, rv (Formalism.L2.SG.InstExistsPf.instOf D) ((Formalism.L2.Host.tauPl D).symm.symm τ) (x j) =
      (Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    rw [← hcol j]
    rfl
  have main : Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ
      ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i b) =
      ∑ j, M j b • ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j) := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (Formalism.L2.SG.EvalTIota.Pi _), Matrix.mul_nonsing_inv _ hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext i
    have e := congrFun (congrFun hC i) b
    simp only [Matrix.mul_apply] at e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact e.trans (Finset.sum_congr rfl fun j _ => mul_comm _ _)
  refine (congrArg (fun w => Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ w) (hrv b)).trans ?_
  exact main.trans (Finset.sum_congr rfl fun j _ => congrArg (fun w => M j b • w) (hrv j).symm)

theorem gramQ_isUnit (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : (∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y) ∧ (∀ a, wt (X.eX a) = D.sp.hypE a) ∧
      (∀ a, wt (X.fY a) = D.sp.hypF a) ∧ wt (X.zu u) = D.zmOf u) (v : InfinitePlace X.B.I.F) :
    IsUnit (Formalism.L2.SG.ColDict.gramQ X wt v).det := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef
  have hgram : Formalism.L2.SG.ColDict.gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [Formalism.L2.SG.ColDict.gramQ, Matrix.of_apply, Formalism.L2.SG.ColDict.rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (Formalism.L2.SG.ColDict.qFr wt a)) (X.crd (Formalism.L2.SG.ColDict.qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
  rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]
  exact hdetG

end GlobalTheory.Core.Mi.RealMat


open GlobalTheory.Core.Mi.RealMat in
theorem GlobalTheory.Core.Mi.sTil_toH_eq_infM : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (θ : InfFam D), IsInfFam θ → IdE X → B.Adapted tr.wt → ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau), Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH a).1 : X.B.I.Ginf) τ = GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ := by
  intro D X h u ψ B F tr θ hθ hE hA a τ
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hdetQ := gramQ_isUnit X u tr.wt ⟨tr.wt_isom, tr.wt_e, tr.wt_f, tr.weight_z⟩ (X.pl.symm τ)
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hact := act_gen h X.ιE hE X.pl X.φ_eq (rank_eq X h) (embA B.d B.o a) τ (B.d.i₀ * B.o.iA) _
    (fun j => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast hn j))) hA (embA_cols_at B.d B.o a τ)
  have hlin : ∀ b, uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
      Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b) =
      ∑ i, GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ i b •
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt i) := by
    intro b
    refine (hact (Fin.cast hn.symm b)).trans ?_
    exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl
  have hM : (Matrix.of fun a' b => hJ (X.B.I.ε (X.pl.symm τ))
      (Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt a'))
      (uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b))) =
      Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ) * GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ := by
    ext a' b
    rw [Matrix.of_apply, hlin, Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, Formalism.L2.SG.ColDict.gramQ,
      Matrix.of_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  show (Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ))⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMatch

theorem unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one {D : D7} (a : GA D (D.sp.X 0)) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D))
    (hM : M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = M := by
  have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
    rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
  calc _ = (M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hM, one_mul]
    _ = M := by rw [mul_assoc, h1, mul_one]

end GlobalTheory.ColMatch

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamBij

variable {D : D7}

def contAutSub (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {φ | IsContAut S φ}
  add_mem' ha hb := ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ h := ⟨fun γ hγ g => by simp [h.1 γ hγ g], h.2.const_smul c⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem formAt_eq (β : Frame p S n) (P : Pair k n) {φ : Form k n (GA D S → ℂ)} (hφ : φ ∈ EqForm β.rep) :
    formAt β P (φ P) = φ := by
  funext P₁
  have h := Classical.epsilon_spec (p := fun g : GL n k => g • P = P₁) (MulAction.exists_smul_eq (GL n k) P P₁)
  show β.rep _ (φ P) = φ P₁
  rw [← hφ, h]

theorem sum_single_sum (β : Frame p S n) {ι : Type} (s : Finset ι) (g : ι → GL n k) (a : ι → ℂ)
    (φ₀ : GA D S → ℂ) :
    (∑ i ∈ s, Finsupp.single (g i) (a i)).sum (fun h b => b • β.rep h φ₀) = ∑ i ∈ s, a i • β.rep (g i) φ₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finsupp.sum_add_index' (h := fun h b => b • β.rep h φ₀) (fun h => zero_smul ℂ (β.rep h φ₀)) (fun h _ _ => add_smul _ _ (β.rep h φ₀)), Finsupp.sum_single_index (h := fun h b => b • β.rep h φ₀) (zero_smul ℂ _), ih]

section Ops

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (β : Frame p S n)

theorem isRam_diaFFStar (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (dia ε (FFStar q χ φ)) := by
  refine ⟨dia_mem_EqForm ε (FFStar_mem_EqForm q χ hφ.1), hO.dia_mem_ram ε _ (hO.FFStar_mem_ram _ hφ.2.1),
    fun P' => ?_⟩
  rw [dia_apply, FFStar_apply]
  exact (contAutSub S).sum_mem fun P₁ _ => (contAutSub S).smul_mem _ (hφ.2.2 P₁)

theorem isRam_FFdia (hO : OperatorIdentities k n (GA D S → ℂ) q χ) (c : ℂ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (c • FF q χ (dia ε⁻¹ φ)) := by
  refine ⟨(EqForm β.rep).smul_mem c (FF_mem_EqForm q χ (dia_mem_EqForm _ hφ.1)),
    (Mram k n _).smul_mem c (hO.FF_mem_ram _ (hO.dia_mem_ram _ _ hφ.2.1)), fun P' => ?_⟩
  rw [Pi.smul_apply, FF_apply]
  refine (contAutSub S).smul_mem c ((contAutSub S).sum_mem fun Q _ => (contAutSub S).smul_mem _ ?_)
  rw [dia_apply]
  exact hφ.2.2 _

theorem diaFFStar_inv (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) :
    dia ε (FFStar q χ (((resCard k : ℂ) ^ Fintype.card n)⁻¹ • FF q χ (dia ε⁻¹ φ))) = φ := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  rw [map_smul, map_smul, hO.FFStar_FF_ram _ (hO.dia_mem_ram _ _ h), map_smul, smul_smul, inv_mul_cancel₀ hqr,
    one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem diaFFStar_inj (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ φ' : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) (h' : φ' ∈ Mram k n (GA D S → ℂ))
    (he : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ')) : φ = φ' := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  have h2 : FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ))) = FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ'))) := by rw [he]
  have hd : ∀ X : Form k n (GA D S → ℂ), dia ε⁻¹ (dia ε X) = X := fun X => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hd, hd, hO.FF_FFStar_ram _ h, hO.FF_FFStar_ram _ h'] at h2
  exact smul_right_injective _ hqr h2

end Ops

theorem ramBijective_at (q : Unif k) (χ₀ : AddChar k Circle) (hχ : HasConductor χ₀ 1) (ε : 𝓀[k]ˣ)
    (β : Frame p S n) (P : Pair k n) :
    Set.BijOn (sOp β P q (resChar χ₀ hχ q) ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q (resChar χ₀ hχ q) φ)) ∧
        sOp β P q (resChar χ₀ hχ q) ε (φ P) = dia ε (FFStar q (resChar χ₀ hχ q) φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q (resChar χ₀ hχ q) ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q (resChar χ₀ hχ q) ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀) := by
  set χ := resChar χ₀ hχ q with hχdef
  have hO : OperatorIdentities k n (GA D S → ℂ) q χ :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ₀ hχ n).1 (GA D S → ℂ)).2
  set r : ℂ := ((resCard k : ℂ) ^ Fintype.card n)⁻¹ with hr

  have hval : ∀ φ, IsRam β φ → sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P := fun φ hφ => by
    show dia ε (FFStar q χ (formAt β P (φ P))) P = _
    rw [formAt_eq β P hφ.1]

  have hinv : ∀ φ, IsRam β φ → sOp β P q χ ε ((r • FF q χ (dia ε⁻¹ φ)) P) = φ P := fun φ hφ => by
    rw [hval _ (isRam_FFdia q χ ε β hO r hφ), diaFFStar_inv q χ ε hO hφ.2.1]
  let gch : Pair k n → GL n k := fun P₁ => Classical.epsilon fun g : GL n k => g • P = P₁
  refine ⟨⟨?_, ?_, ?_⟩, fun φ hφ => ⟨isRam_diaFFStar q χ ε β hO hφ, hval φ hφ⟩,
    ∑ P₁ ∈ withKer (ε • P).lat, Finsupp.single (gch P₁) (χ (-cross q P₁ (ε • P))),
    ∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q)), fun φ₀ => ?_, fun φ₀ hφ₀ => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, isRam_diaFFStar q χ ε β hO hφ, (hval φ hφ).symm⟩
  · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨φ', hφ', rfl⟩ he
    rw [hval φ hφ, hval φ' hφ'] at he
    have hX := isRam_diaFFStar q χ ε β hO hφ
    have hX' := isRam_diaFFStar q χ ε β hO hφ'
    have he' : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ') := by
      rw [← formAt_eq β P hX.1, ← formAt_eq β P hX'.1, he]
    rw [diaFFStar_inj q χ ε hO hφ.2.1 hφ'.2.1 he']
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨_, isRam_FFdia q χ ε β hO r hφ, rfl⟩, hinv φ hφ⟩
  · rw [sum_single_sum]
    rfl
  · obtain ⟨φ, hφ, rfl⟩ := hφ₀
    have hc : (∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q))).sum
        (fun g a => a • β.rep g (φ P)) = (r • FF q χ (dia ε⁻¹ φ)) P := by
      rw [sum_single_sum, Pi.smul_apply, FF_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [smul_smul, dia_apply]
      conv_rhs => rw [← formAt_eq β P hφ.1]
      rfl
    rw [hc]
    exact ⟨hinv φ hφ, _, isRam_FFdia q χ ε β hO r hφ, rfl⟩

end GlobalTheory.FinPl.RamBij

namespace GlobalTheory.FinPl

theorem ramBijective_holds : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  intro D k _ _ _ _ p n _ _ q χ₀ hχ χ hχeq ε S β P
  subst hχeq
  exact RamBij.ramBijective_at q χ₀ hχ ε β P

end GlobalTheory.FinPl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl

theorem SplitPt.sec_mem_idAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.sec a = p.e * p.sec a := by
    have := p.sec_pr (p.sec a)
    rwa [p.pr_sec] at this
  rw [(placeIdem_acts D p.v ε hε).1, ← hsum, he, ← mul_assoc, add_mul, p.split.1,
    mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]

theorem mt_mul_mt_inv {D : D7} (S : HSp D) (γ : GA D S) : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Frame.isLat_of_isLatMoved : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (β : Frame p S n) (γ : GA D S) (L M : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    Moves S γ L M (· = p.v) → β.IsLatMoved γ L Λ → β.IsLat M Λ := by
  intro D k _ _ _ _ p S n _ _ β γ L M Λ hM hL x
  have hsupp : ∀ i, (Formalism.L2.Theta.mt S γ⁻¹ *ᵥ fun i => p.sec ((β.b *ᵥ x) i)) i ∈ idAt D (· = p.v) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (p.sec_mem_idAt _)
  rw [hL x, hM _ hsupp, Matrix.mulVec_mulVec, mt_mul_mt_inv, Matrix.one_mulVec]

end GlobalTheory.FinPl
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.trueColumns_prime_weight_sizes : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → Formalism.L2.Col.Sizes (B.primes X) B.wts L.sc.a := by
  first | exact @GlobalTheory.CoreHt.sizes_trueCols | exact GlobalTheory.CoreHt.sizes_trueCols | (intros; apply GlobalTheory.CoreHt.sizes_trueCols <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.sizeInequalitiesNoLevelPrime_columnNormParameters : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  first | exact @GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | exact GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | (intros; apply GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.theta_functional_invariance_product : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ e, IsSplitIdem D e → ∀ (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ) (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ), (∀ u : WO A T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ A T f → ℓA (heisO ψ A T u f) = ℓA f) → (∀ u : WO B T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ B T f → ℓB (heisO ψ B T u f) = ℓB f) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → ℓ (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  first | exact @GlobalTheory.ProdForm.exists_product_form | exact GlobalTheory.ProdForm.exists_product_form | (intros; apply GlobalTheory.ProdForm.exists_product_form <;> assumption)
end

section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix

theorem _root_.GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n _ _ L hL g hg μ hμ
  letI := hL
  exact GlobalTheory.LatPair.Det.isUnram_det_latStab k n L inferInstance g hg μ hμ
end
