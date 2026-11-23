module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle013
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle018
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle015
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle040
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle006
public import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle004
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle022
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle005
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



section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF GlobalTheory.RealWeil
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}
variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem exists_inf_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  have hB := C.good
  have hc : IsCharAF F B.ψ := (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB).1
  have hθ := C.inf
  have hι := C.chart
  have hS := C.hS
  have hT := C.hT
  have hξ := C.h0
  have hξσ := C.hξ
  have hH := _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ
  have hHeis : IsHeis (fun x y => (star y ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => norm_rhoBF hc _ f, fun f => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι 0) f = f
      rw [iotaVF_zero, rhoBF_zero]
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) f) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι (u + v)) f
      rw [rhoBF_rhoBF, iotaVF_add, _root_.GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    · exact (GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions F E σ nS nT JS JT ξ₀ B.ψ hc f).comp (continuous_iotaVF hι)
  obtain ⟨Ω, ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩, htriv, hcont, hvac⟩ :=
    GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian (IxF F nS nT) (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)) hH.1 hH.2
      (BBF σ JS JT ξ₀ B.ψ) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hHeis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
      (_root_.GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι)
  have sm := _root_.GlobalTheory.T.archimedean_chart_gaussian_norm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc
  have hfr := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀
  have rcomm : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) =
        rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, (hfr u _ hu (real_iotaVF hι v)).2, add_comm]
  have radd : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc (u + iotaVF ι v) f = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, AddChar.map_zero_eq_one, one_smul]
  have hfin : ∀ p {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ f : BBF σ JS JT ξ₀ B.ψ,
      Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) f → Ω p (rhoBF σ JS JT ξ₀ B.ψ hc u f) = rhoBF σ JS JT ξ₀ B.ψ hc u (Ω p f) :=
    fun p u hu f hf => hcomm p _ (fun v g => rcomm hu v g) f hf
  have hth : ∀ p (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 → IsThetaFunOF σ JS JT ξ₀ B.ψ (Ω p f).1 := by
    intro p f hf
    obtain ⟨U, hU, hl⟩ := hf.level
    refine _root_.GlobalTheory.T.archimedean_chart_gaussian_invariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc _ (hsm p f (sm f hf)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoBF σ JS JT ξ₀ B.ψ hc u f = f := QB_ext fun x => congrFun ((coe_rhoBF hc u f).trans (hl u hu h0)) x
    rw [← coe_rhoBF hc, ← hfin p h0 f (sm f hf), e]
  have hbd := GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hc
  obtain ⟨om, hom⟩ := exists_homF hbd Ω hth (fun p f f' h1 h2 => hadd p f f' (sm f h1) (sm f' h2))
    (fun p a f h1 => hsmul p a f (sm f h1)) (fun f h1 => hone f (sm f h1)) fun p p' f h1 => hmul p p' f (sm f h1)
  have lift : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ G : BBF σ JS JT ξ₀ B.ψ, (G.1 : WOF F E nS nT → ℂ) = f :=
    fun f hf => ⟨toBF f hf.cont (hbd f hf) hf.quasi, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk w f hf => ?_⟩, fun s hs hpos p hsc f hf hv => ?_⟩ <;> obtain ⟨G, rfl⟩ := lift f hf
  · rw [hom p G hf]
    exact hth p G hf
  · simp only [hom _ G hf]
    exact (ev _ _ w).continuous.comp
      (hcont (_root_.GlobalTheory.T.continuous_moment_map F E σ B hB nS nT JS JT θ hθ) G (sm G hf))
  · rw [hom p G hf]
    exact GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 _ _
      fun H _ _ _ Φ hΦ => hunit H Φ (fun v g => hΦ _ g) p G (sm G hf)
  · rw [hom _ G hf, htriv _ (mMF_fin θ hg hk) G (sm G hf)]
  · obtain ⟨u, v, hu, rfl⟩ := GlobalTheory.T.exists_finiteAdelic_add_realChartPoint F E nS nT θ ι hι w
    have h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoVF σ JS JT ξ₀ B.ψ hc ι v G).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ hf
    have h2 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v G)).1 :=
      _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀ _ _ h1
    have e1 : actOF σ JS JT g k (u + iotaVF ι v) = u + iotaVF ι (mMF σ JS JT θ (g, k) *ᵥ v) := by
      rw [GlobalTheory.RealWeilF.actOF_add, GlobalTheory.T.unitaryRealPoints_fix_finiteAdelicHoms F E σ nS nT JS JT g k hg hk u hu, _root_.GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι]
    rw [hom _ G hf, e1, ← coe_rhoBF hc _ G, ← coe_rhoBF hc _ (Ω (g, k) G), radd hu v G,
      radd hu _ (Ω (g, k) G), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm G hf)]
  · rw [hom _ G hf, hvac s p hs hpos hsc G (sm G hf) (fderiv_vacF hc ι s G (sm G hf) hv)]
    rfl
end PositivityTheory.ThKW
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}
variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k (hL : _root_.GlobalTheory.ThK.Dbl.FinLevel_k) (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have hmem := n2 uᵀ (tr hu) f hf
    rwa [ht] at hmem
end GlobalTheory.ThK.Dbl.Box
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Cpt σ d.A.J := by
  have h := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl hA) d.ok.aniso
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr hA) d.ok.aniso
theorem exists_lth_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ l ∈ (adeleClass F).adm d.κ, ∀ Φ ∈ d.sch, l Φ = thetaSum F Φ :=
  GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F d.κ
theorem cont_S_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : Continuous fun g : UA σ d.A.J => thetaSum F (d.S g Ψ) := by
  obtain ⟨l, hl, hlθ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_lth_k d
  exact (d.ok.dbl.lin.cont l hl Ψ hΨ).congr fun g => hlθ _ (d.ok.dbl.lin.pres g Ψ hΨ)
theorem inv_S_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∀ γ ∈ ratU σ d.A.J, ∀ g, thetaSum F (d.S (γ * g) Ψ) = thetaSum F (d.S g Ψ) := fun γ hγ g => by
  rw [map_mul, Module.End.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_S_rat_k hP hT d hγ (d.ok.dbl.lin.pres g Ψ hΨ)]
theorem bdd_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∃ C : ℝ, ∀ g, ‖thetaSum F (d.S g Ψ)‖ ≤ C :=
  (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).bdd (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.inv_S_k hP hT d hΨ)
theorem intOn_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    IntegrableOn (fun g => thetaSum F (d.S g Ψ)) d.D d.μ := by
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.bdd_S_k hS hP hT d hΨ
  exact Measure.integrableOn_of_bounded (M := C) ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom).ne
    (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ).aestronglyMeasurable (Eventually.of_forall hC)
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR {p q r : Type} [Fintype q] (w' : InfinitePlace F) (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w' (A * B) = d.cw w' A * d.cw w' B :=
  Matrix.map_mul (f := piInf (d.B.emb w'))
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_loc (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have e : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [e, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_gram (X : Mx F E d.m d.n) :
    d.cw w (d.gram X X) = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, R.cw_loc w X]
  exact gram_loc _ _ _ _ hζ0 (R.hfr w) _
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.psi_nU (b : Matrix (Fin d.n) (Fin d.n) ℂ) (hb : bᴴ = b) (β : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hβw : d.cw w β = R.ζ • b) (hβo : ∀ w', w' ≠ w → d.cw w' β = 0) (hβf : finOne F • β = 0) (X : Mx F E d.m d.n) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) = Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)))) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set z : AE F E := (-(⅟(2 : AF F))) • (β * d.gram X X).trace with hz
  have e1 : -(⅟(2 : AF F) * d.tt (β * d.gram X X)) = Algebra.trace (AF F) (AE F E) z := by
    rw [hz, LinearMap.map_smul, smul_eq_mul, neg_mul]
    rfl
  have hpi : ∀ w', piInf (d.B.emb w') z = -(1 / 2) * (d.cw w' β * d.cw w' (d.gram X X)).trace := by
    intro w'
    rw [hz, Algebra.smul_def, map_mul, map_neg, map_neg, piInf_half, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]
    congr 1

    simp only [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.diag, map_sum]
  have hf : finOne F • z = 0 := by
    rw [hz, smul_comm, ← Matrix.trace_smul, ← Matrix.smul_mul, hβf, Matrix.zero_mul, Matrix.trace_zero, smul_zero]
  have ho : ∀ u, u ≠ w → piInf (d.B.emb u) z = 0 := by
    intro u hu
    rw [hpi, hβo u hu, Matrix.zero_mul, Matrix.trace_zero, mul_zero]
  rw [e1, Place.psi_trace_at d.std d.cm d.B.emb w z hf ho, hpi, hβw, R.cw_gram w X]
  set T := (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace with hT
  have hreal : ((T.re : ℝ) : ℂ) = T := trace_herm_real _ _ hb (by rw [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose])
  have e2 : (R.ζ • b * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace = ((R.sg w : ℤ) : ℂ) * T := by
    rw [smul_mul_smul_comm, Matrix.trace_smul, hT, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  rw [e2]
  rw [← hreal]
  congr 1
  push_cast
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im, zero_mul]
  push_cast
  ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem unipotent_realEmbedding_exists (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb)
    (xN : GR d.n) (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hxN : mR xN = nU h) :
    ∃ β₁ : nA σ d.Y d.b, R.ι w xN = nb β₁ ∧ d.cw w β₁.1 = R.ζ • h ∧ (∀ u, u ≠ w → d.cw u β₁.1 = 0) ∧
      finOne F • β₁.1 = 0 := by
  have hP : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w xN)).toBlocks₁₂ 0 1 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro u
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_toBlocks₁₂_k]
      by_cases hu : u = w
      · subst hu
        rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_unip_k d R u xN _ hxN, Matrix.toBlocks_fromBlocks₁₂]
      · rw [R.off_w w u xN hu, KSing.UnitaryGroupBasics.toBlocks₁₂_one, Matrix.fromBlocks_one]
    · rw [Matrix.fromBlocks_smul, KSing.UnitaryGroupBasics.fin_toBlocks₁₂, R.off_f w xN, ← KSing.UnitaryGroupBasics.fin_toBlocks₁₂, KSing.UnitaryGroupBasics.toBlocks₁₂_one,
        smul_zero]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
  let β₁ : nA σ d.Y d.b := ⟨(inFrame d.b (R.ι w xN)).toBlocks₁₂, AddSubgroup.subset_closure ⟨R.ι w xN, hP⟩⟩
  have hB : inFrame d.b (R.ι w xN) = Matrix.fromBlocks 1 β₁.1 0 1 := hP
  refine ⟨β₁, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_inj_k d (by rw [hN]; exact hB), ?_, fun u hu => ?_, ?_⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_unip_k d R w xN _ hxN
    rw [hB, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_w w u xN hu
    rw [hB, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k, ← Matrix.fromBlocks_one] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1
  · have e := R.off_f w xN
    rw [hB, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at e
    exact (Matrix.fromBlocks_inj.1 e).2.1.trans (smul_zero _)
def betaW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (T : nF σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • d.cw w T.1.1))
theorem character_unipotent_trace (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b)
    (h : Matrix (Fin d.n) (Fin d.n) ℂ) (hh : h.IsHermitian) (hBw : d.cw w β₁.1 = R.ζ • h)
    (hBu : ∀ u, u ≠ w → d.cw u β₁.1 = 0) (hBf : finOne F • β₁.1 = 0) :
    d.B.ψ (d.tt (T.1.1 * β₁.1)) = Complex.exp (Complex.I * (_root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k d R w T * h).trace) := by
  have hT : (d.cw w T.1.1)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w T.1.1).map star = 0 := by
    refine AddSubgroup.closure_induction
      (p := fun β _ => (d.cw w β)ᵀ + ((R.ε : ℤ) : ℂ) • (d.cw w β).map star = 0) ?_ ?_ ?_ ?_ T.1.2
    · rintro β ⟨x, hx⟩
      have e := _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_w_k d R w x
      rw [hx, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_fromBlocks_k] at e
      simp [Krd.Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply] at e
      rw [add_comm]
      exact e
    · ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · intro a b _ _ ha hb
      ext i j
      have ea := congrFun (congrFun ha i) j
      have eb := congrFun (congrFun hb i) j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at ea eb ⊢
      linear_combination ea + eb
    · intro a _ ha
      ext i j
      have ea := congrFun (congrFun ha i) j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at ea ⊢
      linear_combination -ea
  unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.betaW_k
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = d.cw w T.1.1 := ⟨_, rfl⟩
  rw [← hTw] at hT ⊢
  have hAh : (R.ζ • Tw)ᴴ = R.ζ • Tw := by
    ext i j
    have e := congrFun (congrFun hT j) i
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
      smul_eq_mul] at e
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul']
    rcases R.hζ with ⟨hε, hζ⟩ | ⟨hε, hζ⟩
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination -e
    · rw [hζ]; rw [hε] at e; simp at e ⊢; linear_combination (-Complex.I) * e
  have hf : finOne F • (T.1.1 * β₁.1).trace = 0 := by
    rw [← Matrix.trace_smul, ← Matrix.mul_smul, hBf, Matrix.mul_zero, Matrix.trace_zero]
  have hw : ∀ u, u ≠ w → piInf (d.B.emb u) (T.1.1 * β₁.1).trace = 0 := fun u hu => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.piInf_trace_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, hBu u hu, Matrix.mul_zero, Matrix.trace_zero]
  have hz := Place.psi_trace_at d.std d.cm d.B.emb w (T.1.1 * β₁.1).trace hf hw
  have hw' : piInf (d.B.emb w) (T.1.1 * β₁.1).trace = ((R.ζ • Tw) * h).trace := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.piInf_trace_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, hBw, ← hTw, Matrix.mul_smul, Matrix.smul_mul]
  have hreal : ((((R.ζ • Tw) * h).trace).re : ℂ) = ((R.ζ • Tw) * h).trace := by
    have hs : star (((R.ζ • Tw) * h).trace) = ((R.ζ • Tw) * h).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh, hh.eq, Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.1 hs
  have eR : ((((2 * Real.pi : ℝ) : ℂ) • (-(2 : ℂ) • (R.ζ • Tw))) * h).trace =
      ((2 * Real.pi : ℝ) : ℂ) * (-2 * (R.ζ • Tw * h).trace) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt
  rw [hz, hw', eR]
  generalize (R.ζ • Tw * h).trace = c at hreal ⊢
  congr 1
  push_cast
  rw [hreal]
  ring
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.om_sch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch := fun x Φ hΦ =>
  d.ok.dbl.weil.2.1.pres x Φ hΦ
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_zero : d.T 0 = 0 := by
  funext X
  have h : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (0 : d.Fn) = 0 := fun p => by
    funext x
    simp [schr]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Darboux.rho, h, map_zero, Pi.zero_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_inj (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0 := fun Φ hΦ h => (hT.1 F E σ d).2.2 Φ hΦ h
end SD
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc_surj (w : InfinitePlace F) : ∀ (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ), ∃ Z : Mx F E d.m d.n,
    (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0 ∧ R.loc w (X + Z) = u := by
  intro X u
  obtain ⟨ins, h1, h2, h3⟩ := d.exists_insW w
  set M : Matrix (Fin d.m) (Fin d.n) ℂ := (R.fr w).1 * (Matrix.of u).map star - d.cw w X with hM
  refine ⟨M.map ins, fun w' hw' => ?_, ?_, ?_⟩
  · ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h2 w' hw']
  · ext i j
    simp [h3]
  · have hc : d.cw w (X + M.map ins) = (R.fr w).1 * (Matrix.of u).map star := by
      have : d.cw w (M.map ins) = M := by
        ext i j
        simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h1]
      rw [show d.cw w (X + M.map ins) = d.cw w X + d.cw w (M.map ins) from by
        ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw], this, hM]
      abel
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, hc, ← Matrix.mul_assoc]
    rw [show ((R.fr w)⁻¹).1 * (R.fr w).1 = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], Matrix.one_mul]
    ext i j
    simp
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.weilRep_mem_polynomialFock_of_finite_place :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), ∀ r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ PolData B M, om (g, h) Φ ∈ PolData B M := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v g hg h hh Φ hΦ
  classical
  refine Submodule.span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun x y _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c x _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, hf, φ, hSB, hcof, rfl⟩
  obtain ⟨φ₁, ⟨s1, a1⟩, -⟩ := (T.acts F E σ B n d X W M χX χW om r s r' s' hp v).1 g hg h hh (φ v) (hSB v)
  have e := (PositivityTheory.ThKF.pureAct F _ v (om (g, h)) f φ hSB
    ((hcof.and hp.good.std).mono fun _ k => k.1.trans k.2)).2.2 φ₁ a1
  refine e ▸ Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, fun u => ?_, ?_, ?_⟩
  · by_cases hu : u = v
    · subst hu; simpa using s1
    · simpa [Function.update_of_ne hu] using hSB u
  · have : ∀ᶠ u in cofinite, u ≠ v := (Set.finite_singleton v).compl_mem_cofinite
    exact (hcof.and this).mono fun u k => by rw [Function.update_of_ne k.2, k.1]
  · congr!
end
end
