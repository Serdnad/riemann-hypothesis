module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactActionPreservesPolynomialDegree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle205
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle010
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle391
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepPointMulPeriodUnipotentGLMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaGaussAlg

variable {D : D7}

theorem fockF_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    (f : WO M X → ℂ) : fockF ψ θ ε A B f 1 = f := by
  simp only [fockF, pureTensorO, pureTensorL]
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank M.rank) ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem det_gram_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  have hb : ∀ i, V.hT (V.frame i) (∑ j, v j • V.frame j) = 0 := by
    intro i
    have hi : V.hT (V.frame i) (∑ j, v j • V.frame j) = (V.gram *ᵥ v) i := by

      simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hi, hv]
    rfl
  have hy : (∑ j, v j • V.frame j) = 0 := by
    refine V.nondeg.2 _ fun x => ?_

    rw [← V.frame.sum_repr x, map_sum V.hT, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  exact hv0 (funext (Fintype.linearIndependent_iff.mp V.frame.linearIndependent v hy))

theorem incM_gram_inv (S : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ = 1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram = 1 := by
  have hu : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (det_gram_ne_zero S)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

def crd (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) : Matrix (Fin S.rank) (Fin k) (AE D) ≃+ WO S X where
  toFun u := (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D))
  invFun x := GlobalTheory.TripleRead.ptO S.gram e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, (incM_gram_inv S).1, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have : (GlobalTheory.TripleRead.ptO S.gram e x)ᵀ.submatrix e.symm id =
        (HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹) : Matrix (Fin X.rank) (Fin S.rank) (AE D)) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [this]
    rw [Matrix.mul_assoc, (incM_gram_inv S).2, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.ThetaGaussAlg

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm


theorem _root_.GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (M X : HSp D) (A : Fr M) (B : Fr X)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ false M X χ χ' ω → ∀ Φ ∈ algF ψ θ false A B, ∀ γ ∈ GQ M,
    ∀ (g : GA D M) (h : GA D X), thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := by
  first | exact @GlobalTheory.SquareComm.ThetaLeft.main | exact GlobalTheory.SquareComm.ThetaLeft.main | (intros; apply GlobalTheory.SquareComm.ThetaLeft.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  first | exact @GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | exact GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | (intros; apply GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem one_mem_Kset {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem isItW_of_globIt {M : DSModel V S} {M' : DSModel W S'} {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF D.host.F) ℂ} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    {aS aT : D.what₂.Tau → ℚ} {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    {I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ} (hI : GlobIt M M' aS aT It I)
    (hr : D.what₂.Tau → 0 < V.rank ∧ 0 < W.rank) (hpt : Function.Injective (ptOf ψ θ M M' f))
    (hC : ∀ τ, CompactFock ψ θ M M' ω f τ (aS τ) (aT τ)) (hL : ∀ τ, LieFock ψ θ M M' ω f τ (aS τ) (aT τ)) :
    IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  first
  | exact @_root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt
  | exact _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt
  | (apply _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt <;> assumption)
  | (intros; apply _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SourceOperatorLemmas.isItW_of_globIt ..)

theorem exists_locIt {X : ProvA} (hX : ChosenSeries X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X)
    (hB : ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ be) (ga ++ de) aT))
    (hS' : S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨-, p1, p2, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + be.length) (ga.length + de.length) _ _ aT
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + de.length + t) (ga.length + be.length) _ _ aS
    ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨Φ, hΦ⟩ := (h1.1 t al be ga de hd).1
  obtain ⟨Tm, hi, hq, -⟩ := h2.1 t al be ga de hd Φ hΦ
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_contraction_isometric_discreteSeries_fock _ _ _ _ _ _ _ _ _ _ Tm hi hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨v, hv, -⟩ := (hX _ _ _ p2).1
  have c1 := Fintype.card_congr e
  have c2 := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_fin] at c1 c2
  exact ⟨⟨by omega, by omega⟩,
    GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ B hm hm' hU hU' ⟨v, 0, hv⟩ hκ hB⟩

theorem itPair (D : D7) (X : ProvA) (hX : ChosenSeries X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D) (hV : VacChar D) (hB : ModelsAreCoverSeries D)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction) : ItPair D := by
  intro k V W M M' θ ψ hθ hP
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (expS D k τ) (expT D k τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd (congrArg dualPar e1) (congrArg dualPar e2)
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' (expS D k) (expT D k) A hC.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => hV V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (hF V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

end GlobalTheory.Chain.RealIt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.EvalAt

theorem theta_eval : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t h Λ hh hht hΛf hhm g L hg hgt hLf hgm a ha Q
  have hΛ0 : C.X.Λ.FG := C.X.Λ_fg
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ hΛ0 hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  have hLl : L ∈ Lv.lats := (hL Lv g L hLf hgm).2.1 hgt
  have hsb : ∀ L ∈ Lv.lats, ∀ Λ ∈ Vset D.host.E S.rank M, SW.IsSB (Lv.phi C.bas hn v₀ L Λ) :=
    fun L hL Λ hΛ => (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      L hL Λ hΛ).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hφ0 := hsb _ hΛl _ hstd
  have hφ := hsb L hLl Λ (hV M h Λ hM hht hΛf hhm)
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hth : ∀ B', C.IsB B' → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B') φ) :=
    fun B' hB' φ hφ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B' hB').2.1 φ hφ).1.1
  have hmv := (hJ B hB).2.2.2.2.2
  have hBa : C.IsB (C.mvB a B) := (hmv a).1
  have hgB : C.mvB g B = B := (hmv g).2.2.1 hg
  have hcomm : a * g = g * a := (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1 a ha).2.2 g hg
  have p1 : ((h, g * a) : GA D S × GA D T) = (1, a) * (h, g) := by
    rw [Prod.mk_mul_mk, one_mul, hcomm]
  obtain ⟨-, -, e3⟩ := hep h Λ g L hh hht hΛf hhm hg hgt hLf hgm
  rw [(GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ0) Q).2.2.2.2.1, p1, map_mul, Module.End.mul_apply,
    map_smul, GlobalTheory.Ker.Red.om_fvec C om hW h hh g _ (hth B hB _ hφ0) B hB Q, hgB, e3,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ) Q).2.2.2.2.1, map_smul, map_smul,
    GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) a _ (hth B hB _ hφ) B hB Q, hz a ha _ hφ,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C _ hBa (fun _ => 1) _ (hth _ hBa _ hφ) Q).2.2.2.2.1]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 _ hBa _ hφ).2 Q]
  ring

end GlobalTheory.AdSpan.EvalAt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspL2

theorem exists_toLp_ext {G : Type} [MeasurableSpace G] (ν : Measure G) :
    ∃ E : (G → ℂ) →ₗ[ℂ] Lp ℂ 2 ν, ∀ φ, MemLp φ 2 ν → E φ =ᵐ[ν] φ := by
  classical
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | MemLp φ 2 ν}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := by
        first
          | exact MemLp.zero
          | exact MemLp.zero'
          | exact zero_memLp
          | simp
      smul_mem' := fun c _ h => h.const_smul c }
  let f : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun φ => MemLp.toLp (φ : G → ℂ) φ.2
      map_add' := fun φ ψ => MemLp.toLp_add φ.2 ψ.2
      map_smul' := fun c φ => MemLp.toLp_const_smul c φ.2 }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend f
  refine ⟨E, fun φ hφ => ?_⟩
  have hval : E φ = f ⟨φ, hφ⟩ := LinearMap.congr_fun hE ⟨φ, hφ⟩
  rw [hval]
  exact MemLp.coeFn_toLp hφ

theorem inner_eq {G : Type} [MeasurableSpace G] {ν : Measure G} {f f' : Lp ℂ 2 ν} {φ φ' : G → ℂ}
    (h : f =ᵐ[ν] φ) (h' : f' =ᵐ[ν] φ') : ⟪f, f'⟫_ℂ = ∫ g, (starRingEnd ℂ) (φ g) * φ' g ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h, h'] with g hg hg'
  rw [hg, hg']
  first
    | (rw [RCLike.inner_apply]; try ring)
    | simp [mul_comm]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bounded (hP : GlobalTheory.Published.CuspDecaySobolev) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsCuspGrow θ V φ) :
    ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B := by
  obtain ⟨ha, hs, hc, hg⟩ := h
  obtain ⟨-, -, hd⟩ := GlobalTheory.Size.rapidDec_of_cuspDecaySobolev hP hθ ha hs hg hc
  obtain ⟨C, hC⟩ := hd 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem conj_mul {G : Type} [TopologicalSpace G] {φ φ' : G → ℂ} (c : Continuous φ) (c' : Continuous φ')
    (b : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) (b' : ∃ B : ℝ, ∀ g, ‖φ' g‖ ≤ B) :
    Continuous (fun g => (starRingEnd ℂ) (φ g) * φ' g) ∧ ∃ B : ℝ, ∀ g, ‖(starRingEnd ℂ) (φ g) * φ' g‖ ≤ B := by
  obtain ⟨B, hB⟩ := b
  obtain ⟨B', hB'⟩ := b'
  refine ⟨(Complex.continuous_conj.comp c).mul c', max B 0 * max B' 0, fun g => ?_⟩
  calc ‖(starRingEnd ℂ) (φ g) * φ' g‖ = ‖φ g‖ * ‖φ' g‖ := by simp [norm_mul]
    _ ≤ max B 0 * max B' 0 :=
      mul_le_mul ((hB g).trans (le_max_left _ _)) ((hB' g).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)

theorem exists_embedding_skew : GlobalTheory.Published.CuspDecaySobolev → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∃ E : (GA D V → ℂ) →ₗ[ℂ] Lp ℂ 2 (μ.restrict 𝓕), (∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) ∧ (E φ = 0 → φ = 0)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', IsCuspGrow θ V φ → IsCuspGrow θ V φ' → IsCuspGrow θ V (Rder θ V τ X φ) → IsCuspGrow θ V (Rder θ V τ X φ') → ⟪E (Rder θ V τ X φ), E φ'⟫_ℂ + ⟪E φ, E (Rder θ V τ X φ')⟫_ℂ = 0 := by
  intro hP D θ V μ 𝓕 hθ hμ h𝓕
  haveI := hμ
  obtain ⟨-, -, -, iB, iT, -, iC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := iB
  haveI := iT
  haveI := iC
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ).1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 (And.intro hμ h𝓕)).2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hmem : ∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := bounded hP hθ hφ
    exact MemLp.of_bound hφ.1.cont.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hint : ∀ F : GA D V → ℂ, Continuous F → (∃ B : ℝ, ∀ g, ‖F g‖ ≤ B) → Integrable F (μ.restrict 𝓕) := by
    rintro F hF ⟨B, hB⟩
    exact memLp_one_iff_integrable.1 (MemLp.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall hB))
  obtain ⟨E, hE⟩ := exists_toLp_ext (μ.restrict 𝓕)
  refine ⟨E, fun φ hφ => ⟨hmem φ hφ, fun h0 => ?_⟩, ?_⟩
  · have h1 := hE φ (hmem φ hφ)
    rw [h0] at h1
    have hz : ⇑(0 : Lp ℂ 2 (μ.restrict 𝓕)) =ᵐ[μ.restrict 𝓕] (0 : GA D V → ℂ) := Lp.coeFn_zero ..
    have hae : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0 := by
      filter_upwards [h1, hz] with g a b
      rw [← a, b]
      rfl
    have hopen : IsOpen {g | φ g ≠ 0} := isOpen_ne_fun hφ.1.cont continuous_const
    haveI : SMulInvariantMeasure (GQ V) (GA D V) μ := by
      first
        | exact inferInstance
        | exact ⟨fun γ s _ => measure_preimage_mul μ (γ : GA D V) s⟩
    open Pointwise in
    have hinv : ∀ γ : GQ V, γ • {g | φ g ≠ 0} = {g | φ g ≠ 0} := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show φ ((γ⁻¹ : GQ V) * x) ≠ 0 ↔ φ x ≠ 0
      rw [hφ.1.left _ (γ⁻¹).2 x]
    have hnull : μ {g | φ g ≠ 0} = 0 := by
      refine h𝓕.measure_zero_of_invariant _ hinv ?_
      rw [← Measure.restrict_apply hopen.measurableSet]
      exact ae_iff.1 hae
    have hempty := (hopen.measure_eq_zero_iff μ).1 hnull
    funext g
    by_contra hne
    have hg : g ∈ {g | φ g ≠ 0} := hne
    rw [hempty] at hg
    exact hg
  · intro τ X hX φ φ' h1 h2 h3 h4
    rw [inner_eq (hE _ (hmem _ h3)) (hE _ (hmem _ h2)), inner_eq (hE _ (hmem _ h1)) (hE _ (hmem _ h4))]
    obtain ⟨c1, B1, b1⟩ := conj_mul h3.1.cont h2.1.cont (bounded hP hθ h3) (bounded hP hθ h2)
    obtain ⟨c2, B2, b2⟩ := conj_mul h1.1.cont h4.1.cont (bounded hP hθ h1) (bounded hP hθ h4)
    obtain ⟨c0, B0, b0⟩ := conj_mul h1.1.cont h2.1.cont (bounded hP hθ h1) (bounded hP hθ h2)
    rw [← integral_add (hint _ c1 ⟨B1, b1⟩) (hint _ c2 ⟨B2, b2⟩)]
    have key : ∀ ψ : GA D V → ℂ, ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → ∀ g t,
        HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X s)) (Rder θ V τ X ψ (g * oneP θ V τ X t)) t := by
      intro ψ hψ g t
      have d0 : HasDerivAt (fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) 0 :=
        ((GlobalTheory.Mem.AutSpace.differentiable_oneP hψ hX (g * oneP θ V τ X t)) 0).hasDerivAt
      have d1 : HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t)))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) t :=
        HasDerivAt.comp_sub_const (f := fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u)) t t
          (by rw [sub_self]; exact d0)
      refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show ψ (g * oneP θ V τ X s) = ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t))
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, show t + (s - t) = s by ring]
    have hd : ∀ g t, HasDerivAt
        (fun s : ℝ => (starRingEnd ℂ) (φ (g * oneP θ V τ X s)) * φ' (g * oneP θ V τ X s))
        ((starRingEnd ℂ) (Rder θ V τ X φ (g * oneP θ V τ X t)) * φ' (g * oneP θ V τ X t) +
          (starRingEnd ℂ) (φ (g * oneP θ V τ X t)) * Rder θ V τ X φ' (g * oneP θ V τ X t)) t := by
      intro g t
      exact ((key φ h1.2.1 g t).star).mul (key φ' h2.2.1 g t)
    exact GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun g => (starRingEnd ℂ) (φ g) * φ' g)
      (Φ' := fun g => (starRingEnd ℂ) (Rder θ V τ X φ g) * φ' g + (starRingEnd ℂ) (φ g) * Rder θ V τ X φ' g)
      (fun γ hγ g => by
        show (starRingEnd ℂ) (φ (γ * g)) * φ' (γ * g) = (starRingEnd ℂ) (φ g) * φ' g
        rw [h1.1.left γ hγ g, h2.1.left γ hγ g])
      c0 (c1.add c2) b0
      (fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g)))
      (GlobalTheory.Mem.Lift.oneP_zero hθ) hd

end GlobalTheory.Chain.CuspL2

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.det_unitaryConj_atPlace_eq_det_latticeBasisComponent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k u : FinPt G (.top (j + 1))) (w : Pl D.host.E), ((Formalism.L2.Theta.mt (G.V (.top (j + 1))) ((u⁻¹ * k * u : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))).map fun z => GlobalTheory.StdFrames.cpt w (toEAf D z)).det = ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) := by
  first | exact @GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt | exact GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt | (intros; apply GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.stepPoint_mul_periodUnipotent_GL_measurePreserving : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n' (c + 1), ∀ κ : GL n' k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, stepPt x₀ e * (v * embX (c + 1) κ).val = stepPt (x₀ * κ.val) (φ e) := by
  first | exact @GlobalTheory.TopLevelInv.stepPt_mul_symN_embX | exact GlobalTheory.TopLevelInv.stepPt_mul_symN_embX | (intros; apply GlobalTheory.TopLevelInv.stepPt_mul_symN_embX <;> assumption)
end
