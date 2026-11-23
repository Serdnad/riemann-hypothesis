module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle388
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle389
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem det_eq_one_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) : M.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  simp [fun i => (h i i).2]

theorem mem_UX_iff_entries {D : D7} {ρ : ℕ} (v : GL (Fin ρ) (AE D)) :
    v ∈ UX D ρ ↔ ∀ i j : Fin ρ, (j < i → v.val i j = 0) ∧ v.val i i = 1 := Iff.rfl

theorem exists_unit_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) :
    ∃ v : GL (Fin ρ) A, v.val = M ∧ (v⁻¹).val = M.adjugate := by
  have hdet := det_eq_one_of_upperUni h
  refine ⟨⟨M, M.adjugate, ?_, ?_⟩, rfl, rfl⟩
  · rw [Matrix.mul_adjugate, hdet, one_smul]
  · rw [Matrix.adjugate_mul, hdet, one_smul]

theorem isCompact_setOf_rat_mul_mem : ∀ (D : D7) (n ρ : ℕ) (x₀ : Matrix (Fin n) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → ∀ K : Set (Mx D n ρ), IsCompact K → IsCompact {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} := by
  intro D n ρ x₀ hx K hK
  obtain ⟨-, hT2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hinj : Function.Injective x₀.mulVec := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin x₀) (LinearMap.ker_eq_bot.2 hinj)
  have hL : LinearMap.toMatrix' g * x₀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hLr : rat (LinearMap.toMatrix' g) ⬝ rat x₀ = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := by
    simp only [rat]
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set S' : Set (Matrix (Fin ρ) (Fin ρ) (AE D)) :=
    {M | (∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) ∧ rat x₀ ⬝ M ∈ K} with hS'def
  have hC : IsCompact ((fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K) :=
    hK.image (continuous_const.matrix_mul continuous_id)
  have hsub : S' ⊆ (fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K := by
    rintro M ⟨-, hM⟩
    exact ⟨_, hM, by simp only [← Matrix.mul_assoc, hLr, Matrix.one_mul]⟩
  have hcl : IsClosed S' := by
    rw [hS'def, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) (hK.isClosed.preimage ((continuous_const (y := (rat x₀ : Mx D n ρ))).matrix_mul (continuous_id (X := Matrix (Fin ρ) (Fin ρ) (AE D)))))
    rw [Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    rw [Set.setOf_and]
    exact (isClosed_imp isOpen_const (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hS' : IsCompact S' := hC.of_isClosed_subset hcl hsub
  let ι : UX D ρ → Matrix (Fin ρ) (Fin ρ) (AE D) × (Matrix (Fin ρ) (Fin ρ) (AE D))ᵐᵒᵖ := fun u => Units.embedProduct _ u.1
  have hι : Topology.IsEmbedding ι := Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
  have hF : Continuous (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate)
  have heq : ι '' {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} = (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) '' S' := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hU : ∀ i j : Fin ρ, (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
      refine ⟨u.1.1, ⟨hU, hu⟩, ?_⟩
      have hdet := det_eq_one_of_upperUni hU
      refine Prod.ext rfl ?_
      show MulOpposite.op u.1.1.adjugate = MulOpposite.op (Units.val (u.1)⁻¹)
      congr 1
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    · rintro ⟨M, ⟨hU, hM⟩, rfl⟩
      have hdet := det_eq_one_of_upperUni hU
      obtain ⟨v, hv1, hv2⟩ := exists_unit_of_upperUni hU
      subst hv1
      have hmem : v ∈ UX D ρ := (mem_UX_iff_entries v).2 hU
      refine ⟨⟨v, hmem⟩, hM, ?_⟩
      exact Prod.ext rfl (congrArg MulOpposite.op hv2)
  rw [hι.isInducing.isCompact_iff, heq]
  exact hS'.image hF

end GlobalTheory.AscFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PosNhdsChar

theorem posNhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  intro D ψ hψ n ρ L x
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hlin : ∀ c : AE D, Continuous fun a : AE D => c * a := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF D.host.F) c)
  have htr : Continuous fun a : AE D => Algebra.trace (AF D.host.F) (AE D) a :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hψc : Continuous ψ := hψ.1.1
  have hcont : Continuous fun z : Mx D n ρ => star (psiE ψ (upSum (L ⬝ (z - x)))) := by
    refine continuous_star.comp (hψc.comp (htr.comp ?_))
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · simp only [Matrix.mul_apply, Matrix.sub_apply]
      refine continuous_finsetSum _ fun k _ => ?_
      have hk : Continuous fun z : Mx D n ρ => z k j - x k j := by
        simp only [sub_eq_add_neg]
        exact (continuous_id.matrix_elem k j).add continuous_const
      exact (hlin (L i k)).comp hk
    · exact continuous_const
  refine IsOpen.mem_nhds (isOpen_lt continuous_const (Complex.continuous_re.comp hcont)) ?_
  show (0:ℝ) < (star (psiE ψ (upSum (L ⬝ (x - x))))).re
  simp [upSum, psiE]

end GlobalTheory.PosNhdsChar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc


theorem _root_.GlobalTheory.T.continuous_thetaMatrixCoeff_heisenbergTranslate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Continuous (fun w : WO S T => thPair μ 𝓕 f (heisO ψ S T w f₀)) := by
  first | exact @GlobalTheory.MatCoefCont.continuous_thPair_heisO | exact GlobalTheory.MatCoefCont.continuous_thPair_heisO | (intros; apply GlobalTheory.MatCoefCont.continuous_thPair_heisO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc


theorem _root_.GlobalTheory.T.thetaMatrixCoeff_polynomialDecay_realDirections : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  first | exact @GlobalTheory.RealDecay.realDecay | exact GlobalTheory.RealDecay.realDecay | (intros; apply GlobalTheory.RealDecay.realDecay <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc


theorem _root_.GlobalTheory.T.fourierInversion_thetaMatrixCoeff_rationalTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ w x : WO S T, Summable (fun γ : ratL T S => ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖) → ∑' γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x = f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x := by
  first | exact @GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | exact GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate | (intros; apply GlobalTheory.TranslateCoefInversion.sum_coef_mul_translate <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCompress

open GlobalTheory.WeilVacMove

theorem gauss_ode (c : ℝ → ℂ) (a : ℂ) (h : ∀ s : ℝ, HasDerivAt c ((s : ℂ) * a * c s) s) :
    c 1 = Complex.exp (a / 2) * c 0 := by
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * ((t : ℂ) * (t : ℂ)) / 2)) * c t) 0 s := by
    intro s
    have e1 : HasDerivAt (fun x : ℂ => -(a * (x * x) / 2)) (-(a * (1 * (s : ℂ) + (s : ℂ) * 1) / 2)) (s : ℂ) :=
      ((((hasDerivAt_id (s : ℂ)).mul (hasDerivAt_id (s : ℂ))).const_mul a).div_const 2).neg
    have e3 := (e1.cexp.comp_ofReal).mul (h s)
    exact e3.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (key s).differentiableAt) (fun s => (key s).deriv) 1 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_div, neg_zero,
    Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add]
  simp

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem wAt_eq_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (w : Mx D m n) :
    wAt (.inr τ) w = lineAt θ τ (compAt θ τ w) 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  obtain ⟨-, -, -, -, hfi, -, hth⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  ext i j
  rw [← sub_eq_zero]
  apply hσ.ext
  · have h1 : finPart D (lineAt θ τ (compAt θ τ w) 1 i j) = 0 := by
      have := congrFun (congrFun (hfin 1) i) j
      simpa only [Matrix.map_apply, Matrix.zero_apply] using this
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, hfi τ, h1]
  · intro τ'
    have h2 := congrFun (congrFun (hcomp 1 τ') i) j
    by_cases hτ : τ' = τ
    · subst hτ
      rw [if_pos rfl, Complex.ofReal_one, one_smul] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ' (compAt θ τ' w) 1 i j)) = θ τ' (infPart D (w i j)) := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, (hth θ hθ τ').1, one_mul, h2']
      exact sub_self _
    · have h3 := (hth θ hθ τ').2 τ (Ne.symm hτ)
      rw [if_neg hτ] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ (compAt θ τ w) 1 i j)) = 0 := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, h3, zero_mul, zero_sub, neg_eq_zero, h2']

theorem dLine_heisO (hψ : IsStdChar D ψ (-1)) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (v : WO S T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    dLine ψ S T L (heisO ψ S T v f) x =
      -2 * phase lam S T (L 1) v * heisO ψ S T v f x + ψ (symplOH S T x v) * dLine ψ S T L f (x + v) := by
  have hG : (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) =
      fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        heisO ψ S T (L t) f (x + v) := by
    funext t
    have e1 := GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 v t
    have hX : Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) =
        (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ * (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring
    have hE := Complex.exp_ne_zero ((t : ℂ) * phase lam S T (L 1) v)
    show ψ (symplOH S T x (L t)) * (ψ (symplOH S T (x + L t) v) * f (x + L t + v)) =
      ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        (ψ (symplOH S T (x + v) (L t)) * f (x + v + L t))
    rw [GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_left,
      GlobalTheory.WeilVacMove.symplOH_skew S T v (L t), AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, e1, add_right_comm x (L t) v, hX]
    field_simp
  have hH := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hL hL0 hf).1 (x + v)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)))
      (Complex.exp (((0 : ℝ) : ℂ) * (-2 * phase lam S T (L 1) v)) * (1 * (-2 * phase lam S T (L 1) v))) 0 :=
    (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const _).cexp).comp_ofReal
  have hD := (hexp.const_mul (ψ (symplOH S T x v))).mul hH
  show deriv (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) 0 = _
  have hD' : HasDerivAt (fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
      heisO ψ S T (L t) f (x + v)) _ 0 := hD
  rw [hG, hD'.deriv]
  have hv : heisO ψ S T v f x = ψ (symplOH S T x v) * f (x + v) := rfl
  rw [hv, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  ring

private theorem flow_lemma {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (hvf : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f)
    (hvg : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g) :
    ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z 1) f) g =
      Complex.exp (-(phase lam S T (lineAt θ τ z 1) (lineAt θ τ z 1) +
        Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * z * sS)) 1) (lineAt θ τ z 1)) / 2) *
        ipO μ 𝓕 f g := by
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  set J := Complex.I • (sT * z * sS) with hJ
  obtain ⟨hLc, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨hLc', hL0', -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ J
  set L := lineAt θ τ z with hLeq
  set L' := lineAt θ τ J with hLJeq
  set Dz := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z with hDz
  set DJ := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ J with hDJ
  have vf : Dz f + Complex.I • DJ f = 0 := hvf z
  have vg : Dz g + Complex.I • DJ g = 0 := hvg z
  have hp : ∀ (u : WO S T) (s : ℝ), phase lam S T u (L s) = (s : ℂ) * phase lam S T u (L 1) := by
    intro u s
    have hc : Continuous ((phase lam S T u).comp L) :=
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hLc continuous_const)
    exact GlobalTheory.WeilVacMove.additive_real _ hc s
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L t) f) g)
      ((s : ℂ) * -(phase lam S T (L 1) (L 1) + Complex.I * phase lam S T (L' 1) (L 1)) *
        ipO μ 𝓕 (heisO ψ S T (L s) f) g) s := by
    intro s
    set h := heisO ψ S T (L s) f with hheq
    have hh : IsThetaFunO ψ S T h := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 s) hf
    obtain ⟨hder, hXs⟩ := GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ z
    have hYs := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ J).2
    have h0 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g) (ipO μ 𝓕 (Dz h) g) (s - s) := by
      rw [sub_self]
      refine hder.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g = ipO μ 𝓕 (heisO ψ S T (L t) h) g
      rw [hheq, GlobalTheory.WeilVacMove.heisO_line_add hψ hLc hL0 t s f]
    have hd := (h0.comp_sub_const s s)
    simp only [sub_add_cancel] at hd
    refine hd.congr_deriv ?_
    have hDzh := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hh
    have hDJh : IsThetaFunO ψ S T (DJ h) := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hh
    have hDJg := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hg
    have cA : Dz h + Complex.I • DJ h =
        (-2 * (phase lam S T (L 1) (L s) + Complex.I * phase lam S T (L' 1) (L s))) • h := by
      funext x
      have c1 : Dz h x = -2 * phase lam S T (L 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * Dz f (x + L s) := dLine_heisO hψ hl hlam hLc hL0 (L s) hf x
      have c2 : DJ h x = -2 * phase lam S T (L' 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * DJ f (x + L s) := dLine_heisO hψ hl hlam hLc' hL0' (L s) hf x
      have c3 := congrFun vf (x + L s)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at c3 ⊢
      rw [c1, c2]
      linear_combination ψ (symplOH S T x (L s)) * c3
    have e3 : ipO μ 𝓕 h (Dz g) = Complex.I * ipO μ 𝓕 h (DJ g) := by
      have hz : Dz g = (-Complex.I) • DJ g := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left vg
      rw [hz, ((U h (DJ g) hh hDJg).2.2.1 (-Complex.I)).2]
      simp [Complex.conj_I]
    have e4 : ipO μ 𝓕 (Dz h + Complex.I • DJ h) g = ipO μ 𝓕 (Dz h) g + Complex.I * ipO μ 𝓕 (DJ h) g := by
      have hsmul : IsThetaFunO ψ S T (Complex.I • DJ h) := by
        refine { quasi := ?_, level := ?_, cont := ?_, smooth := ?_ }
        · intro γ w
          rw [Pi.smul_apply, Pi.smul_apply, hDJh.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        · obtain ⟨U, hU, h1⟩ := hDJh.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          change ψ (symplOH S T w u) * DJ h (w + u) = DJ h w at e1
          unfold heisO
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        · exact hDJh.cont.const_smul Complex.I
        · intro k L h1 h2 w
          exact contDiff_const.mul (hDJh.smooth k L h1 h2 w)
      rw [((U (Dz h) g hDzh hg).2.2.2.1 _ hsmul).1,
        ((U (DJ h) g hDJh hg).2.2.1 Complex.I).1]
    rw [cA, ((U h g hh hg).2.2.1 _).1, hp (L 1) s, hp (L' 1) s] at e4
    linear_combination (-1 / 2 : ℂ) * e4 + (1 / 2 : ℂ) * hXs - (Complex.I / 2) * hYs - (1 / 2 : ℂ) * e3
  have hfin := gauss_ode _ _ key
  simp only [map_zero, GlobalTheory.WeilVacMove.heisO_zero] at hfin
  exact hfin

theorem compress : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ), IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT → ∀ w : WO S T, ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ θ S T μ 𝓕 hψ hθ hμ τ sS sT _ _ w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  refine ⟨starRingEnd ℂ (Complex.exp (-(phase lam S T (lineAt θ τ (compAt θ τ w) 1) (lineAt θ τ (compAt θ τ w) 1) +
      Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * compAt θ τ w * sS)) 1)
        (lineAt θ τ (compAt θ τ w) 1)) / 2)), ?_⟩
  intro f g hf hg hvf hvg
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  obtain ⟨-, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  have h1 := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 1) hf
  rw [wAt_eq_lineAt hθ τ w, (U _ g h1 hg).2.1, (U f g hf hg).2.1,
    flow_lemma hψ hθ hμ hl hlam τ sS sT (compAt θ τ w) hf hg hvf hvg, map_mul]

end GlobalTheory.VacCompress

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



namespace GlobalTheory.FinPlLoc

theorem idem_smul_mem_latMul_at : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  intro D S 𝔞 L v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]
      exact mul_mem (ePl_int _ w) (hαi w)
    · rw [map_mul, evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.FinPlLoc
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


open GlobalTheory.FinPl.LatMem in
theorem GlobalTheory.FinPl.projB_mem_of_orthAt : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  intro D S A B o L LA LB hLG hO t ht
  apply hLG
  intro v
  have hY : (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * t i)) ∈ latV S L (· = v) :=
    AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
  have h2 := ((hO v _).1 hY).2
  convert h2 using 1
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = (1 : AF D.host.F) ⊗ₜ[D.host.F] (o.qB i j) * _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end
