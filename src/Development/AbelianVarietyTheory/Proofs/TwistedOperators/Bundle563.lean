module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle559
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle556
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle557
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalisedAdaptedVectorZero
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle558
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle513
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleMulSingle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareRel

section Rel

variable {P Q Pr : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pr] [Module ℂ Pr]

def relOf (q : P →ₗ[ℂ] Pr) (q' : Q →ₗ[ℂ] Pr) : Submodule ℂ (P × Q) :=
  LinearMap.eqLocus (q ∘ₗ LinearMap.fst ℂ P Q) (q' ∘ₗ LinearMap.snd ℂ P Q)

theorem mem_relOf {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} {x : P × Q} : x ∈ relOf q q' ↔ q x.1 = q' x.2 := Iff.rfl

theorem relOf_fst {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq' : Function.Surjective q') (a : P) : ∃ b, (a, b) ∈ relOf q q' := by
  obtain ⟨b, hb⟩ := hq' (q a)
  exact ⟨b, hb.symm⟩

theorem relOf_snd {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) (b : Q) : ∃ a, (a, b) ∈ relOf q q' := by
  obtain ⟨a, ha⟩ := hq (q' b)
  exact ⟨a, ha⟩

theorem relOf_ne_top [Nontrivial Pr] {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) : relOf q q' ≠ ⊤ := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
  obtain ⟨a, rfl⟩ := hq y
  have h1 : (a, (0 : Q)) ∈ relOf q q' := h ▸ Submodule.mem_top
  rw [mem_relOf, map_zero] at h1
  exact hy h1

end Rel

section Pol

variable {σ₁ σ₂ ν : Type} (e : σ₁ ⊕ σ₂ ≃ ν)

def polTens : MvPolynomial σ₁ ℂ ⊗[ℂ] MvPolynomial σ₂ ℂ ≃ₗ[ℂ] MvPolynomial ν ℂ :=
  ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)).equiv
    (MvPolynomial.basisMonomials ν ℂ) (Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr e).toEquiv)

theorem finsupp_sum_eq (m : σ₁ →₀ ℕ) (n : σ₂ →₀ ℕ) :
    Finsupp.domCongr e (Finsupp.sumElim m n) = m.mapDomain (e ∘ Sum.inl) + n.mapDomain (e ∘ Sum.inr) := by
  ext x
  obtain ⟨s, rfl⟩ := e.surjective x
  have h1 : Function.Injective (e ∘ Sum.inl) := e.injective.comp Sum.inl_injective
  have h2 : Function.Injective (e ∘ Sum.inr) := e.injective.comp Sum.inr_injective
  rcases s with s | s
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inl]
    rw [show e (Sum.inl s) = (e ∘ Sum.inl) s from rfl, Finsupp.mapDomain_apply_of_injective h1, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu).symm
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inr]
    rw [show e (Sum.inr s) = (e ∘ Sum.inr) s from rfl, Finsupp.mapDomain_apply_of_injective h2, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu)

theorem polTens_tmul (p₁ : MvPolynomial σ₁ ℂ) (p₂ : MvPolynomial σ₂ ℂ) :
    polTens e (p₁ ⊗ₜ p₂) = MvPolynomial.rename (e ∘ Sum.inl) p₁ * MvPolynomial.rename (e ∘ Sum.inr) p₂ := by
  have key : (TensorProduct.mk ℂ _ _).compr₂ (polTens e).toLinearMap =
      (LinearMap.mul ℂ (MvPolynomial ν ℂ)).compl₁₂ (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inl)).toLinearMap
        (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inr)).toLinearMap := by
    refine (MvPolynomial.basisMonomials σ₁ ℂ).ext fun m => (MvPolynomial.basisMonomials σ₂ ℂ).ext fun n => ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
    have h : (MvPolynomial.monomial m (1 : ℂ)) ⊗ₜ[ℂ] (MvPolynomial.monomial n (1 : ℂ)) =
        ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)) (m, n) := by
      rw [Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials, MvPolynomial.coe_basisMonomials]
    rw [h, polTens]
    erw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, mul_one,
      Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
    rw [finsupp_sum_eq]
  exact LinearMap.congr_fun₂ key p₁ p₂

end Pol

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

section Route

variable {D : D7} {a b c d b' : ℕ}

end Route

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : ℕ) {d b' b₁ : ℕ}

theorem hasInfExp_alpha {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (τ : D.what₂.Tau) {a : ℚ}
    (h : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ a) : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j) τ a := by
  obtain ⟨-, -, ⟨θ, hθ⟩, -⟩ := id h
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨n', hn', ho'⟩ := hL.xi_fin t'
  have h0 := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  have h0' := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t') hn' ho' τ
  have hK : ∀ s, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G s i j = (L.mu0 (j + 1) * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) * L.xi s := fun s => by
    show L.mu0 (j + 1) * L.xi s * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = _
    exact mul_right_comm _ _ _
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j * (L.xi t)⁻¹ * L.xi t' := by
    rw [hK t', hK t, mul_inv_cancel_right]
  have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.Chain.StepVac.hasInfExp_mul h (GlobalTheory.Chain.StepVac.hasInfExp_inv h0)) h0'
  rw [e]
  simpa using this

end Grid

theorem nontrivial_of_tensor {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
    [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi] (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) : Nontrivial Pr := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨u, hu⟩ := exists_ne (0 : Pi)
  apply hu
  rw [← e.apply_symm_apply u, hz (e.symm u), map_zero]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7} {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
  [AddCommGroup Pi] [Module ℂ Pi]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7}

end GlobalTheory.SquareRel
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix


theorem _root_.GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol ψ τ,
          (∃ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁) ∧
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.RealLieFock.lie_deriv_pol | exact GlobalTheory.RealLieFock.lie_deriv_pol | (intros; apply GlobalTheory.RealLieFock.lie_deriv_pol <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_good_rational_schroedingerModel : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ {n d : ℕ} (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
    V.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
    ∀ (μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)) (dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)),
      μ.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig V.J) dom μ →
    ∃ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws, M.μ = μ ∧ M.dom = dom ∧ M.IsGood Bs.ψ := by
  first | exact @GlobalTheory.SquareAgree.exists_good_model | exact GlobalTheory.SquareAgree.exists_good_model | (intros; apply GlobalTheory.SquareAgree.exists_good_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

theorem _root_.GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.FockCount.rank_pol_le_aleph0 | exact GlobalTheory.FockCount.rank_pol_le_aleph0 | (intros; apply GlobalTheory.FockCount.rank_pol_le_aleph0 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModel_thetaSeries_moderate_growth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), (∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω p f)) 0) ∧ ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (g, h) f)) 0‖ₑ ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  first | exact @GlobalTheory.MixedSeriesGrowth.mixed_series_growth | exact GlobalTheory.MixedSeriesGrowth.mixed_series_growth | (intros; apply GlobalTheory.MixedSeriesGrowth.mixed_series_growth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentRadical_stabiliser_scales_restriction : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ g : GA D V, g ∈ NI V C → ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (g, 1) f) = c • res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.SourceUnip.scal | exact GlobalTheory.SourceUnip.scal | (intros; apply GlobalTheory.SourceUnip.scal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentRadical_target_preserves_isotropic_mean : ∀ (D : D7) (V W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)), IsCovolOne (ratMx D s V.rank) μ 𝓐 → ∀ (n : NI W L) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫ a in 𝓐, ω (1, (n : GA D W)) f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = ∫ a in 𝓐, f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  first | exact @GlobalTheory.UnipMean.mean_target | exact GlobalTheory.UnipMean.mean_target | (intros; apply GlobalTheory.UnipMean.mean_target <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

theorem _root_.GlobalTheory.T.finiteIdeleModulus_prod_localUnitIdeles : ∀ {D : D7} (P : Finset (Pl D.host.E)) (y : ∀ w : P, (Kw w.1)ˣ),
    (∀ w, valuation (Kw w.1) (y w : Kw w.1) = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (∏ w : P, GlobalTheory.LFun.locIdele D.host.F w.1 (y w)) = 1 := by
  first | exact @GlobalTheory.TopLevelInv.absFin_prod_locIdele_unit | exact GlobalTheory.TopLevelInv.absFin_prod_locIdele_unit | (intros; apply GlobalTheory.TopLevelInv.absFin_prod_locIdele_unit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VertexFromTransport

theorem vertexAt_of_levTransport : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) →
    ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Transport L.Pg (Wc D i) (Yc D 0) (L.βW i) (L.βY 0) →
    ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf L.βY 0) (L.βW i) eW ι L.Pg := by
  intro D T L _ i ht
  have hr : (D.sp.Y 0).rank = (D.sp.W ((i : ℕ) + 1)).rank := by
    rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.W_rank _ (by omega) (by omega)]
    simp [Ranks.rankY]
  exact GlobalTheory.NormalFramesLevels.vertexAt_of_transport L.Pg _ hr _ _
    (GlobalTheory.NormalFramesLevels.transport_betaYOf L.Pg (Wc D i) (L.βW i) L.βY ht)

end GlobalTheory.VertexFromTransport
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlipPath

variable {D : D7}

section Local

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

variable {e I}

end Local

theorem isSelfDualC_sgn (ε : Bool) {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : IsSelfDualC S Λ) :
    IsSelfDualC (sgn ε S) Λ := by
  cases ε
  · exact h
  · refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
    have e : ∑ i, ∑ j, star (x i) * (neg S).gram i j * y j = -∑ i, ∑ j, star (x i) * S.gram i j * y j := by
      simp [neg_gram, Finset.sum_neg_distrib]
    refine ⟨fun ⟨b, hb⟩ => ⟨-b, ?_⟩, fun ⟨b, hb⟩ => ⟨-b, ?_⟩⟩
    · refine Eq.trans ?_ e.symm
      rw [← hb]; simp
    · have := hb.trans e
      rw [← neg_eq_iff_eq_neg] at this
      rw [← this]; simp

section Fin

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : Node D} {e : AE D} {P : Finset (Pl D.host.E)} {f₀ f : WO S.V T.V → ℂ}

theorem isFinVec_of_own {ε : Bool} (hv : IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    {φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ} (h : IsDatOwn ψ ε S T e f₀ φ f) : IsFinVec ψ θ ε S T f := by
  obtain ⟨hSB, ⟨Tm, hTm⟩, hall⟩ := h
  rw [hall Tm hTm]
  exact finVec_of_mem_span (S := sgn ε S.V) hv (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 (isSelfDualC_sgn ε hS) hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm hSB).1

end Fin

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

end GlobalTheory.FlipPath

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (ι : Type) (s : Finset ι) (v : ι → FinPl D) (a : ι → AE D), (∀ i ∈ s, IsSplitIdem D (a i) ∧ a i + cA D (a i) = idem D (.inl (v i))) → Set.InjOn v s → ∀ Φ : ι → WO S T → ℂ, (∀ i ∈ s, IsSBHalf (a i) (latO S T ΛS ΛT fun _ => True) (Φ i)) → ∀ (x : Place D → WO S T → ℂ) (f Ψ : WO S T → ℂ), (∀ i ∈ s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i) (x (.inl (v i)))) → (∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀) → (∀ t, IsHalf (∑ i ∈ s, a i) t → Ψ t = ∏ i ∈ s, Φ i (a i • t)) → (∀ t, ¬ IsHalf (∑ i ∈ s, a i) t → Ψ t = 0) → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i ∈ s, a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Ψ f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  exact GlobalTheory.PlaceTensor.SplitProduct.isPure_of_facts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕
    (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1
    (GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ)
    (GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1
    (fun a h1 h2 h3 =>
      ⟨fun x y hx hy Tm hTm =>
        ((GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT (base_std hB) hB.2.2.1 hB.2.2.2.1 a h1 h2 h3).1 x y hx hy).2 f₀ Tm hTm,
        (GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT (base_std hB) hB.2.2.1 hB.2.2.2.1 a h1 h2 h3).2⟩)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

theorem _root_.GlobalTheory.T.first_standard_pair_member_has_theta_function : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A WW : HSp D) (rA : Rig A) (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (vac : WO A WW → ℂ), rA.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ (neg A) WW (fun τ => -rA.s τ) rW.s rA.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) e (latO (neg A) WW rA.Λ rW.Λ fun _ => True) 1 vac (stdFst ν e I A WW rA.β rW.β) f ∧ IsThetaFunO ψ (neg A) WW f := by
  first | exact @GlobalTheory.Adopt.first_standard_pair_member_has_theta_function | exact GlobalTheory.Adopt.first_standard_pair_member_has_theta_function | (intros; apply GlobalTheory.Adopt.first_standard_pair_member_has_theta_function <;> assumption)
end
