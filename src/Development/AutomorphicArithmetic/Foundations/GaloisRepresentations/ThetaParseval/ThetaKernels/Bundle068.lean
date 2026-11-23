module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle045
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle061
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle060
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle053
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SdEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle058
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.SplitDomOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitCut
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.COneLawPf
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



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem splitDom_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.Kdil.DecompW_k) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.SplitDom_k := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ g
  obtain ⟨x, y₀, hg, hx⟩ := hD F E σ d R w g
  obtain ⟨A, hA⟩ := hAw F E σ d R w x hx
  have hind : d.Indep w Ψ := ((_root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k F E σ d R).2.1 w Ψ hΨ).2
  refine ⟨y₀, A Ψ, ?_, ?_⟩
  · intro Φ hΦ f hf hTΦ y
    obtain ⟨hLf, hLΦ⟩ := hL (y₀ * y) f hf
    have h1 := hLΦ Ψ hind Φ hΦ hTΦ
    rw [hg, mul_assoc, ← map_mul, map_mul, Module.End.mul_apply]
    exact ((hA Ψ hind).2 _ hLf _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d _ hΦ) h1)
  · intro δ hδ
    obtain ⟨Φ, hΦ, hTΦ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftSw1_k hT.1 d R w _ (isSw_gauss hδ) Ψ hΨ
    rw [← (hA Ψ hind).2 _ (isSw_gauss hδ) Φ hΦ hTΦ]
    exact (hT.1 F E σ d).1 _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d x hΦ)
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem commW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x hx y
theorem iota_mem_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w y hy
theorem kSplit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.kSplit_k d R w k hk
theorem iota_isPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar_k d R w q hq
theorem siegel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.siegel_k d hp
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.T_zero_k d Φ
theorem loc_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitP.loc_zero_k d R w
theorem gSplit_of_k (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ φ hφ g
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  obtain ⟨y, hk'K, hk'w⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.kSplit_k d R w k hk
  set k' := (R.ι w y)⁻¹ * k with hk'
  have hcomm := _root_.PositivityTheory.SiegelWeilFormula.KSplit.commW_k d R w k' hk'w
  obtain ⟨A, hA⟩ := hAw F E σ d R w k' hk'w
  have hΨi : d.Indep w Ψ := ((hF F E σ d R).2.1 w Ψ hΨ).2
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.siegel_k d hp
  refine ⟨p * k', y, C * A Ψ 0, (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ), absE_pos _, ?_,
    fun y' => ⟨?_, fun P => ?_⟩⟩
  · rw [mul_assoc, hcomm y, hk', mul_inv_cancel_left]
  · obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := Glob.locIwasawa y'
    obtain ⟨tq, hPq, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.iota_isPar_k d R w q hq
    have e : p * k' * R.ι w (q * k₀) = (p * R.ι w q) * (R.ι w k₀ * k') := by
      rw [map_mul, mul_assoc p, ← mul_assoc k', hcomm q, mul_assoc (R.ι w q), hcomm k₀]
      simp only [mul_assoc]
    have hval := d.ok.hgt.val _ _ (isPar_mul hp hPq) _ ((d.K).mul_mem (_root_.PositivityTheory.SiegelWeilFormula.KSplit.iota_mem_K_k d R w k₀ hk₀) hk'K)
    have h0 : 0 ≤ d.a ((p * R.ι w q) * (R.ι w k₀ * k')) := by rw [hval]; exact NNReal.coe_nonneg _
    show ((d.a (p * k' * R.ι w (q * k₀))).toNNReal : ℝ) = _
    rw [e, Real.coe_toNNReal _ h0, hval, map_mul, map_mul, NNReal.coe_mul, habs, hloc]
  · have hsw := fP_sw P
    have hΞ := (hL y' (fP P) hsw).2 Ψ hΨi (φ P) (hφ P).1 (hφ P).2
    have hΞs : d.om (R.ι w y') (φ P) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ (hφ P).1
    have h2 := (hA Ψ hΨi).2 _ (hL y' (fP P) hsw).1 _ hΞs hΞ
    have hs2 : d.om k' (d.om (R.ι w y') (φ P)) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ hΞs
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hs2, ← _root_.PositivityTheory.SiegelWeilFormula.KSplit.T_zero_k, h2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KSplit.loc_zero_k]
    ring
end PositivityTheory.SiegelWeilFormula.KSplit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald.Asc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.SiegelWeilFormula.Ald.Asc
namespace PositivityTheory.SiegelWeilFormula.Ald
open Asc in
theorem bigT_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k := by
  intro hT _hA F E _ _ _ _ _ σ d dd0 had hrat
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ
    (Fin d.m × Fin d.n × Fin 2) _ d.dd dd0 (by exact d.ok.dbl.rat) (by exact hrat)
  have hop := hS.1
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = dd0.rho d.B.ψ w (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ]
    simp
  have rhoS' : ∀ w, ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), S0' (dd0.rho d.B.ψ w φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm (Fin d.m × Fin d.n × Fin 2) := hop.adm' d.l d.ok.dbl.adm
  have hsurj : ∀ y : Fin d.m × Fin d.n × Fin 2 → AF F, ∃ Z : Mx F E d.m d.n,
      dd0.e (Z * (incM F d.b.1.toCols₁)ᵀ) = (0, y) := by
    intro y
    obtain ⟨Z, X, hw⟩ := eq_split d.b (dd0.e.symm (0, y))
    have h1 := had Z X
    rw [← hw, LinearEquiv.apply_symm_apply] at h1
    have h2 := had Z 0
    rw [Matrix.zero_mul, add_zero, crdB_zero] at h2
    refine ⟨Z, h2.trans ?_⟩
    have h3 := congrArg Prod.snd h1
    simp only at h3
    rw [← h3]
  obtain ⟨t, ht0⟩ := d.ok.frame.2
  have ht : (d.b.1.toCols₁ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * (t.1 : Matrix (Fin d.n) (Fin d.n) E) := ht0
  have hinv : ∀ (y : Fin d.m × Fin d.n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2),
      l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨Z, hZ⟩ := hsurj y
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = dd0.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) φ := by
      funext x
      simp [Darboux.rho, hZ, schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    have e2 : Z * (incM F d.b.1.toCols₁)ᵀ = ((Z * (incM F t.1)ᵀ : Mx F E d.m d.n)) *
        ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)))ᵀ := by
      rw [ht, incM_mul', incM_diagCols, Matrix.transpose_mul]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [e2]
    exact d.ok.dbl.kill _ _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin d.n × Fin 2) l' hadm hinv
  have hform : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = c * S0 Φ (crdB d.bs X) := by
    intro Φ hΦ X
    have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ hΦ
    have h0 := had 0 X
    rw [Matrix.zero_mul, zero_add] at h0
    simp only [Bf_zero_left] at h0
    have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
      rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
      rfl
    rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ]
    simp [Darboux.rho, h0, schr]
  refine ⟨S0, S0', c, ?_, hS, hform⟩
  rintro rfl
  obtain ⟨φ, hφ, hφ0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have hz : d.T φ = 0 := by
    funext X
    rw [hform φ hφ X, zero_mul]
    rfl
  exact hφ0 (by rw [(hT.1 F E σ d).2.2 φ hφ hz]; rfl)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C s : ℂ) (B : d.MF → d.MF), s ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B :=
  R.stepW_pf w hT hA
end RD
end PositivityTheory.SiegelWeilFormula
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
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_gen (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ t : GL (Fin d.n) (AE F E), d.cw w t.1 = a ∧ (∀ w', w' ≠ w → d.cw w' t.1 = 1) ∧ finOne F • t.1 = finOne F • 1 ∧
      R.StepOK w (R.ι w y) (fun f u => ((d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ)) * f (Matrix.of u * a)) id := by
  intro y a ha hy
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ := by
    have h1 : mR y * mR y⁻¹ = 1 := by
      show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1
      rw [mul_inv_cancel]; rfl
    have h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1 := by
      rw [hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]
    calc mR y⁻¹ = (Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y) * mR y⁻¹ := by rw [h2, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨hM, hA1, -, hO1, hF1, -⟩ := R.frame_diag w y a (aᴴ)⁻¹ hy
  obtain ⟨hM', -, hD', hO', -, hF'⟩ := R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi
  set M := inFrame d.b (R.ι w y) with hMdef
  set M' := inFrame d.b (R.ι w y⁻¹) with hM'def
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]
  have hMM' : M' * M = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]
  have bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)},
      P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ →
      P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1 := by
    intro P Q hP hQ hPQ
    rw [hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hPQ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.mp hPQ
    exact ⟨h1, h4⟩
  obtain ⟨t1, u1⟩ := bl hM hM' hMM
  obtain ⟨t2, u2⟩ := bl hM' hM hMM'
  let t : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩
  let u : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩
  have hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1 := hM
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  refine ⟨t, hA1, fun w' h => (hO1 w' h).1, hF1, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ
    exact ⟨ψ, hψ⟩
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]
    have hui : (u⁻¹).1 = M'.toBlocks₂₂ := rfl
    rw [hui]
    set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ
    have hZo : ∀ w', w' ≠ w → d.cw w' Z = 0 := by
      intro w' h
      rw [hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by
        rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]; exact Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,
        Matrix.mul_one, sub_self]
    have hZf : finOne F • Z = 0 := by
      rw [hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one, sub_self]
    have hX : X * (M'.toBlocks₂₂)ᵀ = X + Z := by rw [hZ]; abel
    have hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a := by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
      rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, hD', ← Matrix.mul_assoc, mapStar_mulR]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    rw [hloc, hX, hΨ X Z hZo hZf]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepN (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b →
    R.StepOK w (R.ι w y) (fun f u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) id :=
  R.stepN_pf w hT
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ c : ℂ, c ≠ 0 ∧ R.StepOK w (R.ι w y) (fun f u => c * f (Matrix.of u * a)) id :=
  R.stepM_pf w hT
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem relEx_of_k (hA : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelAlg_k) (hS : SdEx) (hR : _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.RelRealP_k) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelEx_k := by
  intro _ _ F E _ _ _ _ _ σ d R Φ _ P gf hP x t u hx T hTnd
  obtain ⟨η, hOf, hη, hherm, hof, haniso, hcm, hJ, hTT⟩ := hA F E σ d
  obtain ⟨T₀, hrat, hTdh, hTdd⟩ := hTT T hTnd
  obtain ⟨θ, fr, g, l, εs, Φg, Φf, Φv, hth, hfr, hg, hΦg, hεs, hchr, hpl, hfrm, hpf, hpr⟩ :=
    hR F E σ d R Φ P gf hP x t u hx η hη hherm
  obtain ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ := hS F E σ hcm d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) hJ d.B.ψ hchr d.n
  exact ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, ⟨hx, hrat, hη, hherm, hof, hth, hfr, hg⟩, hΦg, haniso, hεs,
    hcm, hJ, hTdh, hTdd, hchr, hpl, hfrm, hpf, hpr, hμ, hν⟩
theorem relEx_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelEx_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.relEx_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.relAlg_pf_k sdEx _root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.relReal_k
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cOneLaw_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (w : InfinitePlace F)
    {nb' lam' 𝓖'} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') (T' : nF σ L.Y L.b)
    (τ : ℝ) (y : GR d.n) (hy : IsDil (Pi.single L.i₀ 1) τ y) (z : ℂ) (x : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' (R.ι w y * x) =
      Complex.exp (τ * (2 * z + d.n)) * _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x := by
  set c := Complex.exp (τ * (2 * z + d.n)) with hc
  have hterm : ∀ g : L.sd.G, ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x)) =
      c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := by
    intro g
    rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.AStep.j_comm_dil_k R L w τ y hy g, mul_assoc]
    obtain ⟨ha, h0⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.a_dil_k R w L.i₀ τ y hy (L.j g * x)
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.constantTerm_dilation H R w L.i₀ τ y hy hΦ]
    have e1 : ((d.Ht (R.ι w y * (L.j g * x)) : ℝ) : ℂ) = ((Real.exp (2 * τ) : ℝ) : ℂ) * ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ (by rw [ha]; exact mul_nonneg (Real.exp_pos _).le h0), ha, Complex.ofReal_mul]
    have e2 : ((d.Ht (L.j g * x) : ℝ) : ℂ) = ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ h0]
    rw [e1, e2, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le h0, cpow_exp, hc]
    have e3 : Complex.exp (((2 * τ : ℝ) : ℂ) * (z - s0 d.m d.n)) * Complex.exp (τ * d.m) = Complex.exp (τ * (2 * z + d.n)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold s0
      push_cast
      ring
    rw [← e3]
    ring
  unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k
  have hfun : (fun g : L.sd.G => ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x))) =
      fun g => c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := funext hterm
  rw [hfun]
  have hcs : ∀ (Ψ : L.sd.G → ℂ), GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => c * Ψ g) =
      fun g' => c * GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) Ψ g' := by
    intro Ψ
    funext g'
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    exact tsum_mul_left
  rw [hcs]
  simp only [fc, mul_assoc]
  exact integral_const_mul _ _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
