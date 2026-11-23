module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumns
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem sum_three_fintype_reverse {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ y, ∑ x, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_fintype_permute {α β γ δ M : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := by
  calc ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ j, ∑ k, ∑ l, f k j i l := sum_three_fintype_reverse _
    _ = ∑ i, ∑ j, ∑ l, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem mvZ_subY_comp (hab : a ≤ b) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (subY hab y') = (subY hab (fun τ => h τ * y' τ)).comp (lft g) := by
  apply MvPolynomial.algHom_ext
  intro v

  rw [AlgHom.comp_apply, AlgHom.comp_apply, subY, lft, aeval_X, aeval_X, map_sum, map_sum]

  simp only [map_mul, mvZ, subY, aeval_X, algHom_C, algebraMap_eq, map_sum]

  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_three_fintype_reverse]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_mvZ_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (mvZ g' h') = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]

  simp only [map_mul, mvZ, aeval_X, algHom_C, algebraMap_eq, map_sum]

  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_fintype_permute]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lft_lft_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) :
    (lft g).comp (lft g') = lft (fun τ => g' τ * g τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]

  simp only [map_mul, lft, aeval_X, algHom_C, algebraMap_eq, map_sum]

  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_one : mvZ (ι := ι) (a := a) (b := b) (fun _ => 1) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [mvZ, Matrix.one_apply, apply_ite C, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem lft_one : lft (ι := ι) (a := a) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [lft, Matrix.one_apply]

def scaleFP (t : ι → ℂ) : FP ι a b →ₐ[ℂ] FP ι a b :=
  aeval fun v => C (t v.1) * X v

theorem subY_smul (hab : a ≤ b) (t : ι → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    subY hab (fun τ => t τ • y' τ) = (scaleFP t).comp (subY hab y') := by
  apply MvPolynomial.algHom_ext
  intro v

  simp only [subY, scaleFP, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C,
  Matrix.smul_apply, smul_eq_mul, C_mul, algebraMap_eq]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem scaleVariables_monomial (t : ι → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    scaleFP t (monomial m (1 : ℂ)) = (m.prod fun k n => t k.1 ^ n) • monomial m (1 : ℂ) := by
  rw [scaleFP, aeval_monomial, map_one, one_mul, ← C_mul', ← prod_X_pow_eq_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]

theorem jetL_monomial_one (c : ι → ℂ) (G : VCx ι a b → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    jetL c G (monomial m (1 : ℂ)) = jetC c G m := by
  have e : (monomial m (1 : ℂ) : FP ι a b) = basisMonomials (ι × Fin b × Fin a) ℂ m := by
    rw [coe_basisMonomials]
  rw [e, jetL, Module.Basis.constr_basis]

theorem jetL_comp_scale (c t : ι → ℂ) (G : VCx ι a b → ℂ) :
    (jetL c G).comp (scaleFP (a := a) (b := b) t).toLinearMap = jetL (fun τ => c τ * t τ) G := by
  refine (basisMonomials (ι × Fin b × Fin a) ℂ).ext fun m => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coe_basisMonomials]
  rw [scaleVariables_monomial, map_smul, jetL_monomial_one, jetL_monomial_one, smul_eq_mul, jetC, jetC, ← mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (frDet ℂ a τ : PY ι a) = (y τ).det := by
  rw [evalAt, frDet, RingHom.map_det]
  congr 1
  ext α s
  simp

theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (F * ∏ τ, (frDet ℂ a τ : PY ι a)) = evalAt y F * ∏ τ, (y τ).det := by
  unfold evalAt
  rw [map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => evalAt_frDet y τ

theorem frDet_prod_ne_zero : (∏ τ, (frDet ℂ a τ : PY ι a)) ≠ 0 := by
  intro h
  have h1 : (1 : PY ι a) * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by rw [one_mul, h]
  have h2 := congrArg (evalAt (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ))) h1
  rw [evalAt_mul_prod] at h2
  simp [evalAt] at h2

theorem eq_zero_of_invertible (F : PY ι a) (hF : ∀ y, IsInv y → evalAt y F = 0) : F = 0 := by
  have h0 : F * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by
    apply MvPolynomial.funext
    intro x
    have key : eval x (F * ∏ τ, (frDet ℂ a τ : PY ι a)) =
        evalAt (fun τ => Matrix.of fun α s => x (τ, α, s)) (F * ∏ τ, (frDet ℂ a τ : PY ι a)) := rfl
    rw [map_zero, key, evalAt_mul_prod]
    by_cases hI : IsInv (fun τ => Matrix.of fun α s => x (τ, α, s))
    · rw [hF _ hI, zero_mul]
    · simp only [IsInv, not_forall] at hI
      obtain ⟨τ, hτ⟩ := hI
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by simpa using hτ), mul_zero]
  exact (mul_eq_zero.mp h0).resolve_right frDet_prod_ne_zero

theorem evalAt_lft_eq (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  simp only [evalAt, lft]
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>

    simp only [map_mul, hp, aeval_X, eval_X, map_sum, eval_C, Matrix.mul_apply]

theorem substIdentities : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), (∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), mvZ g h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) (lft g F)) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b), mvZ g h (mvZ g' h' P) = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) P) ∧ (∀ P : FP ι a b, mvZ (fun _ => 1) (fun _ => 1) P = P) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), lft g (lft g' F) = lft (fun τ => g' τ * g τ) F) ∧ (∀ F : PY ι a, lft (fun _ => 1) F = F) ∧ (∀ (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F) ∧ (∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) ∧ ∀ (c t : ι → ℂ) (G : VCx ι a b → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), jetL c G (subY hab (fun τ => t τ • y' τ) F) = jetL (fun τ => c τ * t τ) G (subY hab y' F) := by
  intro ι _ a b hab
  refine ⟨fun g h y' F => ?_, fun g g' h h' P => ?_, fun P => ?_, fun g g' F => ?_, fun F => ?_,
    fun g y F => evalAt_lft_eq g y F, fun F hF => eq_zero_of_invertible F hF, fun c t G y' F => ?_⟩
  · have := DFunLike.congr_fun (mvZ_subY_comp hab g h y') F
    simpa only [AlgHom.comp_apply] using this
  · have := DFunLike.congr_fun (mvZ_mvZ_comp g g' h h') P
    simpa only [AlgHom.comp_apply] using this
  · rw [mvZ_one, AlgHom.id_apply]
  · have := DFunLike.congr_fun (lft_lft_comp g g') F
    simpa only [AlgHom.comp_apply] using this
  · rw [lft_one, AlgHom.id_apply]
  · rw [subY_smul, AlgHom.comp_apply, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, jetL_comp_scale]

end GlobalTheory.KJInf
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.completion_representatives_normal_form_mod_unipotent : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → (∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0) → ∀ j c (h : j + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1)) k), IsGL ι (L.h j al P) g → ∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j c h (r * g) := by
  first | exact @GlobalTheory.TwNormalReps.exists_normal_rep | exact GlobalTheory.TwNormalReps.exists_normal_rep | (intros; apply GlobalTheory.TwNormalReps.exists_normal_rep <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  first | exact @GlobalTheory.TwBridge.idxIsProd_of_ok | exact GlobalTheory.TwBridge.idxIsProd_of_ok | (intros; apply GlobalTheory.TwBridge.idxIsProd_of_ok <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY | exact GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY | (intros; apply GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.TwBridgeInhab in

theorem _root_.GlobalTheory.T.exists_completionTwistData_chainColumns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  intro X Pr R Ch sel S₀ mu cst L G s hL P hP k _ _ _ _ ι ϖ hc hϖ ψ hψc hψ1 hψt μ hμ
  have hm : R.m = s + 2 := hL.hm
  have hm0 : 0 < R.m := by omega
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.SymBridge.ComplRes.q_ne_zero hc
  have hqpos : 0 < qOf P.1 := Nat.pos_of_ne_zero fun h => hq0 (by rw [h, Nat.cast_zero])
  have hqmem : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := GlobalTheory.SymBridge.ComplRes.q_mem hc
  let δ : kˣ →* ℂˣ := μ 1 * (GlobalTheory.SmGL.unrChar k (μ 1 ϖ))⁻¹
  have hδ_unit (x : kˣ) (hx : valuation k (x : k) = 1) : δ x = μ 1 x := by
    simp [δ, GlobalTheory.SmGL.isUnram_unrChar k _ x hx]
  have hμ_unit (i : ℕ) {a : X.E} (ha : IsUnit (redP P.1 a)) :
      muAt Ch sel mu cst i P a = LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹ a := by
    unfold muAt
    rw [ite_eq_right hP]
    unfold LocE.locChar
    rw [GlobalTheory.LastSteps.vP_unit ha]
    simp
  have hμ_uniformizer (i : ℕ) :
      muAt Ch sel mu cst i P (qOf P.1 : X.E) = cst.muq (i + 1) P := by
    unfold muAt
    rw [ite_eq_right hP]
    unfold LocE.locChar
    rw [valuation_self P.1 _ hqmem hqpos, zpow_one, zpow_one, div_self hq0]
    have hred : redP P.1 (1 : X.E) = 1 := by
      rw [← (map_one (algebraMap (𝓞 X.E) X.E)), reduction_coe, map_one]
    have hu : IsUnit (redP P.1 (1 : X.E)) := hred ▸ isUnit_one
    unfold LocE.unitV
    rw [dite_eq_left hu]
    have hu_one : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hred, Units.val_one])
    rw [hu_one, map_one, Units.val_one, mul_one]
  have hμ1 : ∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ 1 u : ℂ) = G.σ₀ (muAt Ch sel mu cst 0 P a) :=
    fun a u h => (hμ 0 hm0).1 a u h
  have ht1 : IsTame (μ 1) := (hμ 0 hm0).2
  have hδ_tame : IsTame δ := by
    intro x hx
    rw [hδ_unit x (val_eq_one_of_sub_one hx)]
    exact ht1 x hx

  have hδ : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = δ x := by
    intro i hi x hx
    rw [hδ_unit x hx]
    obtain ⟨a, ha⟩ := exists_near hc.dense (x : k)
    have hva : valuation k (ι a) = 1 := by
      have e : ι a = (ι a - x) + x := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hx]; exact ha), hx]
    have ha0 : ι a ≠ 0 := by
      intro h0; rw [h0, map_zero] at hva; exact zero_ne_one hva
    have hint : IntAt P.1 a := GlobalTheory.SymBridge.ComplRes.intAt_of_v hc (le_of_eq hva)
    have hred : IsUnit (redP P.1 a) := (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ hint).mp hva
    have hn : valuation k (((Units.mk0 (ι a) ha0 : kˣ) : k) - x) < 1 := ha
    rw [← tame_near (hμ i hi).2 hx hn, ← tame_near ht1 hx hn]
    apply Units.ext
    rw [(hμ i hi).1 a _ rfl, hμ1 a _ rfl, hμ_unit i hred, hμ_unit 0 hred]

  have hsq : G.σ₀ (cst.sq P) ^ 2 = ((Real.sqrt (qOf P.1) : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hL.cst_ok.sq_sq P, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_natCast]
  obtain ⟨sg, hsg1, hsg2⟩ : ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧ G.σ₀ (cst.sq P) = sg * (Real.sqrt (qOf P.1) : ℂ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  refine ⟨⟨ϖ, hϖ, ψ, hψc, hψ1, δ, hδ_tame, eta μ R.m (δ),
    eta_unram μ R.m _ hδ, sg⟩, ⟨hP, hm, hc, ?_, ?_, ?_, hsg2⟩, rfl, rfl, fun i hi => eta_mul μ R.m _ hi, hsg1⟩
  · intro a ha
    show (ψ (ι a) : ℂ) = G.σ₀ (cst.psi P a)
    have hxi : IntAt P.1 G.xi0 := (hL.xiUnitAtPrime P).1
    have hx : valuation k (ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a))) ≤ 1 :=
      GlobalTheory.SymBridge.ComplRes.v_le_one hc (hxi.mul ha)
    obtain ⟨i, -, hi⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep hc hϖ (cst.D P) _ hx
    have hqk : ((qOf P.1 : ℕ) : k) ≠ 0 := by
      rw [← GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]; exact ϖ.ne_zero
    have hint : IntAt P.1 (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) := by
      apply GlobalTheory.SymBridge.ComplRes.intAt_of_v hc
      have e : ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a)) - (i : k) =
          ι (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) * (ϖ : k) ^ cst.D P := by
        rw [GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]
        simp only [map_mul, map_sub, map_div₀, map_pow, map_intCast, map_natCast]
        push_cast
        field_simp
      rw [e, map_mul, map_pow] at hi
      have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) ^ cst.D P :=
        pow_pos (zero_lt_iff.mpr (by simp)) _
      exact le_of_mul_le_mul_right (by rwa [one_mul]) h0
    rw [hψt a (i : ℤ) (cst.D P) hint, hL.weil P a (i : ℤ) ha hint]
  · intro a u ha hr hu
    show ((δ u : ℂˣ) : ℂ) = _
    have hva : valuation k (u : k) = 1 := by
      rw [hu]; exact (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ ha).mpr hr
    rw [hδ_unit u hva, hμ1 a u hu, hμ_unit 0 hr]
    unfold LocE.unitV
    rw [dite_eq_left hr, dite_eq_left hr, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
  · intro i hi
    show ((eta μ R.m (δ) (i + 1) * δ) ϖ : ℂ) = _
    rw [eta_mul μ R.m _ hi, (hμ i hi).1 ((qOf P.1 : ℕ) : X.E) ϖ hc.unif, hμ_uniformizer i]
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.parahoric_test_functions_agree_rational_points : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W := by
  first | exact @GlobalTheory.TwBridge.PhiProof.phiAgree_of_atTwist | exact GlobalTheory.TwBridge.PhiProof.phiAgree_of_atTwist | (intros; apply GlobalTheory.TwBridge.PhiProof.phiAgree_of_atTwist <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem mem_KO_iff_intAt_isUnit_det : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l τ j M
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  let e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
    (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv
  have he : ∀ a, ((e a : Fin _) : ℕ) = zPos a := by
    rintro ((i | i) | ⟨i, u⟩) <;> simp [e, zPos, finProdFinEquiv] <;> ring
  let A : Matrix (Fin (κ + l + j * τ)) (Fin (κ + l + j * τ)) E := Matrix.of fun s s' => M s.1 s'.1
  let T : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b))
  have hT : T = (A.map ι).submatrix e e := by
    ext a b; simp [T, A, he]
  have hdet : T.det = ι A.det := by
    rw [hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl
  have hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k] := fun x hx =>
    (Valuation.mem_integer_iff (valuation k) x).2 hx.le
  change (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = T) ↔ _
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hI := intM_of_mem_KO hg
    rw [hgv] at hI
    refine ⟨fun p p' hp hp' => ?_, ?_⟩
    · have h := hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)
      simp only [T, Matrix.of_apply] at h
      rw [← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact (hC.int _).1 h
    · have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet] at hv
      exact (h3 _ ((hC.int _).1 (hint _ hv))).1 hv
  · rintro ⟨hent, hunit⟩
    have hTint : ∀ a b, T a b ∈ 𝒪[k] := fun a b =>
      (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))
    let B : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) 𝒪[k] :=
      Matrix.of fun a b => ⟨T a b, hTint a b⟩
    have hB : B.map (algebraMap 𝒪[k] k) = T := by ext a b; rfl
    have hBdet : algebraMap 𝒪[k] k B.det = ι A.det := by
      rw [RingHom.map_det]; change (B.map (algebraMap 𝒪[k] k)).det = _; rw [hB, hdet]
    have hAint : IntAt P A.det := (hC.int _).1 (hBdet ▸ (B.det).2)
    have hv : valuation k (ι A.det) = 1 := (h3 _ hAint).2 hunit
    have hBu : IsUnit B.det :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.SymBridge
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.symmetricLevel_character_at_rational_point : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  first | exact @GlobalTheory.symLevel_lam_residue_elim | exact GlobalTheory.symLevel_lam_residue_elim | (intros; apply GlobalTheory.symLevel_lam_residue_elim <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

theorem _root_.GlobalTheory.T.parahoricBiTransforming_lowerUnipotent_diag_value : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) else 0 := by
  first | exact @GlobalTheory.LowerHeckeSupp.biType_lowU_emb | exact GlobalTheory.LowerHeckeSupp.biType_lowU_emb | (intros; apply GlobalTheory.LowerHeckeSupp.biType_lowU_emb <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverCone

theorem inCone_of_kTypesAbove : GlobalTheory.Dec.KTypesAbove → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (blockPar P e) μ := by
  intro KTA p q n e P T R σ hb hσ hds μ v hv
  obtain ⟨S, hS⟩ := GlobalTheory.RealPar.isKTypeOf_of_isHW R hb hσ μ ⟨v, hv⟩
  obtain ⟨c, hc, hμ⟩ := KTA n P.sgn P.lam R.U.H σ P.hc hds _ S hS
  refine ⟨fun a b => c (e a) (e b), fun a b hab => ?_, ?_⟩
  · have h2 := P.hc.1 (hc _ _ hab)
    rw [← GlobalTheory.RealPar.ratEntry_cast, ← GlobalTheory.RealPar.ratEntry_cast] at h2
    exact_mod_cast h2
  · funext x
    apply Rat.cast_injective (α := ℝ)
    have hx := congrFun hμ (e x)
    simp only [Equiv.symm_apply_apply] at hx
    push_cast
    rw [hx, GlobalTheory.RealPar.blattner_eq P hb (lam := GlobalTheory.RealPar.blockPar P e) (fun a => GlobalTheory.RealPar.ratEntry_cast P (e a)) x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.RealPar.root_apply]
    split_ifs <;> simp

end GlobalTheory.CoverCone
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.card_subspaces_containing_range_qVandermonde : ∀ (κ : Type) [Field κ] [Finite κ] (U U' : Type) [AddCommGroup U] [Module κ U] [FiniteDimensional κ U] [AddCommGroup U'] [Module κ U'] [FiniteDimensional κ U'] (f : U →ₗ[κ] U') (t e : ℕ), Module.finrank κ U' = Module.finrank κ U + t → e ≤ Module.finrank κ U' → Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} = ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then Nat.card κ ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin (Nat.card κ) t (e - n) else 0) * Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} := by
  first | exact @GlobalTheory.RangeKerCount.card_above_range_eq_sum | exact GlobalTheory.RangeKerCount.card_above_range_eq_sum | (intros; apply GlobalTheory.RangeKerCount.card_above_range_eq_sum <;> assumption)
end
