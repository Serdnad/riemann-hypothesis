module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle494
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle495
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle453
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle491
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle497
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle499
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle498
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
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
  first | exact @GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | exact GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | (intros; apply GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
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
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  first | exact @GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO | exact GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO | (intros; apply GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section
namespace GlobalTheory.FockEntire
open GlobalTheory.FockCompare

theorem gauss_w_cr {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) :
    Differentiable ℝ (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ)) ∧
    ∀ Z Y : VCx ι a b, fderiv ℝ (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ)) Z Y +
        Complex.I * fderiv ℝ (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ)) Z (Complex.I • Y) =
      (∑ τ, ∑ i, ∑ j, (c τ : ℂ) * Z τ i j * conj (Y τ i j)) * ((Real.exp (gq c Z / 2) : ℝ) : ℂ) := by
  let P : ι → Fin b → Fin a → (VCx ι a b →L[ℝ] ℂ) := fun τ i j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin b => Fin a → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin b → Fin a → ℂ) τ))
  have hP : ∀ τ i j (Z : VCx ι a b), P τ i j Z = Z τ i j := fun _ _ _ _ => rfl
  have hq : ∀ Z : VCx ι a b, HasFDerivAt (fun Z : VCx ι a b => gq c Z / 2)
      ((1 / 2 : ℝ) • ∑ τ, ∑ i, ∑ j, c τ • (2 : ℕ) • (innerSL ℝ (Z τ i j)).comp (P τ i j)) Z := fun Z => by
    have h : HasFDerivAt (fun Z : VCx ι a b => gq c Z)
        (∑ τ, ∑ i, ∑ j, c τ • (2 : ℕ) • (innerSL ℝ (Z τ i j)).comp (P τ i j)) Z := by
      unfold gq
      refine HasFDerivAt.fun_sum fun τ _ => HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
      exact ((P τ i j).hasFDerivAt.norm_sq).const_smul (c τ)
    have e : (fun Z : VCx ι a b => gq c Z / 2) = fun Z => (1 / 2 : ℝ) • gq c Z := by
      funext Z; rw [smul_eq_mul]; ring
    rw [e]
    exact h.const_smul (1 / 2 : ℝ)
  have hE : ∀ Z : VCx ι a b, HasFDerivAt (fun Z : VCx ι a b => ((Real.exp (gq c Z / 2) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (Real.exp (gq c Z / 2) •
        ((1 / 2 : ℝ) • ∑ τ, ∑ i, ∑ j, c τ • (2 : ℕ) • (innerSL ℝ (Z τ i j)).comp (P τ i j)))) Z :=
    fun Z => Complex.ofRealCLM.hasFDerivAt.comp Z (hq Z).exp
  refine ⟨fun Z => (hE Z).differentiableAt, fun Z Y => ?_⟩
  rw [(hE Z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply, hP, Pi.smul_apply,
    nsmul_eq_mul]
  have key : ∀ z y : ℂ, z * starRingEnd ℂ y =
      ((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ) := by
    intro z y
    rw [Complex.inner, Complex.inner]
    apply Complex.ext <;> simp <;> ring
  have key2 : ∀ (r : ℝ) (z y : ℂ), (r : ℂ) * z * starRingEnd ℂ y =
      (r : ℂ) * (((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ)) := by
    intro r z y; rw [mul_assoc, key]
  simp_rw [key2]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {D : D7}

theorem cplxO_smulC {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

theorem cplxO_sum {m n p q : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin p → Fin q → Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t (∑ i, ∑ j, x i j) = ∑ i, ∑ j, cplxO s t (x i j) := by
  simp only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]

theorem jO_fockMat {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (Y : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.VacUnique.jO S T A.cart B.cart (fun τ => fockMat A B τ (Y τ) : RW T S) =
      (fun τ => fockMat A B τ ((Complex.I • Y) τ) : RW T S) := by
  funext τ
  show cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (Y τ)) = fockMat A B τ ((Complex.I • Y) τ)
  unfold fockMat
  rw [cplxO_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.VacUnique.cplxO_add, cplxO_smulC, cplxO_smulC, GlobalTheory.FockCreaDir.cplxO_unitMap_fr, cplxO_smulC,
    GlobalTheory.FockCreaDir.cplxO_unitMap_fr]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, smul_smul]
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def fockLin {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) :
    VCx D.what₂.Tau S.rank T.rank →ₗ[ℝ] RW T S where
  toFun z := (fun τ => fockMat A B τ (z τ) : RW T S)
  map_add' z w := by
    funext τ
    show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)
    simp only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    abel
  map_smul' c z := by
    funext τ
    show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)
    simp only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul,
      mul_smul, Finset.smul_sum, smul_add]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.coe_smul]

theorem rd_differentiable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D),
    IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ x, Differentiable ℂ (rd ψ σ A B f x) := by
  intro D ψ θ σ hψ h S T A B f hf x
  let M : VCx D.what₂.Tau S.rank T.rank →L[ℝ] RW T S := LinearMap.toContinuousLinearMap (fockLin A B)
  have hM : ∀ Z, M Z = (fun τ => fockMat A B τ (Z τ) : RW T S) := fun Z => rfl
  set G : RW T S → ℂ := fun w => heisO ψ S T (iotaW σ T S w) f x with hG
  set E : VCx D.what₂.Tau S.rank T.rank → ℂ := fun Z => ((Real.exp (gq (fw D) Z / 2) : ℝ) : ℂ) with hE
  obtain ⟨hGd, hGc⟩ := GlobalTheory.T.heisenbergTranslate_fockVacuum_cauchyRiemann D θ σ h ψ hψ S T A B f hf x
  obtain ⟨hEd, hEc⟩ := gauss_w_cr (a := S.rank) (b := T.rank) (fw D)
  have hrd : rd ψ σ A B f x = fun Z => G (M Z) * E Z := by
    funext Z
    show _ * _ = _
    rw [mul_comm]
    rfl
  rw [hrd]
  have hd : ∀ Z Y, fderiv ℝ (fun Z => G (M Z)) Z Y = fderiv ℝ G (M Z) (M Y) := fun Z Y => by
    have h1 : HasFDerivAt (fun Z => G (M Z)) ((fderiv ℝ G (M Z)).comp M) Z :=
      (hGd (M Z)).hasFDerivAt.comp Z M.hasFDerivAt
    rw [h1.fderiv]
    rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => G (M Z)) E
    (fun Z Y => ∑ τ, ∑ i, ∑ j, (fw D τ : ℂ) * Z τ i j * conj (Y τ i j))
    (hGd.comp M.differentiable) hEd (fun Z Y => ?_) hEc
  rw [hd, hd]
  have hJ : M (Complex.I • Y) = GlobalTheory.VacUnique.jO S T A.cart B.cart (M Y) := by
    rw [hM, hM, jO_fockMat]
  rw [hJ, hGc, ← hJ, hM, hM, hM, GlobalTheory.T.symplecticForm_fockMatrix_eq_neg_sum_im_real_places, GlobalTheory.T.symplecticForm_fockMatrix_eq_neg_sum_im_real_places]
  have h1 : ∀ τ i j, (Z τ i j * conj ((Complex.I • Y) τ i j)).im = -(Z τ i j * conj (Y τ i j)).re := by
    intro τ i j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_im, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  simp only [h1]
  have h2 : ∀ τ i j, (fw D τ : ℂ) * Z τ i j * conj (Y τ i j) =
      (2 * Real.pi * ‖tauE D τ D.host.xi0‖ : ℝ) * (((Z τ i j * conj (Y τ i j)).re : ℂ) +
        ((Z τ i j * conj (Y τ i j)).im : ℂ) * Complex.I) := by
    intro τ i j
    rw [Complex.re_add_im, fw, mul_assoc]
  simp only [h2]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, neg_neg]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf
  rw [Complex.I_sq]
  ring

end GlobalTheory.FockEntire
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.integral_exp_bk_mul_eq_zero_of_moments_zero : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  first | exact @GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments | exact GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments | (intros; apply GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fock_bargmann_reproducing_formula : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ z₀, G z₀ = ((∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) : ℂ) * ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z := by
  first | exact @GlobalTheory.FockRepr.bargmann_repr | exact GlobalTheory.FockRepr.bargmann_repr | (intros; apply GlobalTheory.FockRepr.bargmann_repr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType : ∀ (D : D7) (C : ℝ) (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank), (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  first | exact @GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | exact GlobalTheory.RowReal.hw_basePar_eq_neg_lowK | (intros; apply GlobalTheory.RowReal.hw_basePar_eq_neg_lowK <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.HeckeEx.Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nfac_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) {la : Wt X.Ψ r}
    {la' : Wt X'.Ψ r} (hl : ∀ (τ : X'.Ψ) i, la' τ i = la ⟨τ.1, h.mem τ⟩ i) (x : Frame X.Ψ r) :
    X'.nfac la' (lact a (castFr h.psi x)) = X.nfac la x := by
  unfold Data.nfac
  simp only [h.dmin_eq]
  exact (GlobalTheory.Dict.Pull.cast_wt h.psi rfl hl (castFr h.psi x)).symm

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs in
theorem lact_flow_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a)
    (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    lact a (castFr h.psi (X.flow ξ s x)) =
      X'.flow ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => s ⟨τ.1, h.mem τ⟩) (lact a (castFr h.psi x)) := by
  funext τ
  have hm : (a : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) =
      X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
        (a : Matrix (Fin r) (Fin r) E).map τ.1 := by
    have he : Data.emb τ.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) =
        (a : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ Data.emb τ.1 ξ := by
      funext i
      simp [Data.emb, Matrix.mulVec, dotProduct]
    have hc : X'.c τ = X.c ⟨τ.1, h.mem τ⟩ := by simp only [Data.c, h.xi]
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flowMat_mulVec, flowMat_mulVec, he, h.hermC_eq, hc,
      Matrix.mulVec_add, Matrix.mulVec_smul]
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ ⟨τ.1, h.mem τ⟩ (s ⟨τ.1, h.mem τ⟩) *
      mat x ⟨τ.1, h.mem τ⟩) = X'.flowMat ((a : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s ⟨τ.1, h.mem τ⟩) *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hm]

theorem flowMat_nsmul (X : Data E r) (n : ℕ) (v : Fin r → E) (τ : X.Ψ) (z : ℂ) :
    X.flowMat ((n : E) • v) τ z = X.flowMat v τ ((n : ℂ) ^ 2 * z) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
    Complex.conj_natCast, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem flow_nsmul (X : Data E r) {n : ℕ} (hn : 0 < n) (v : Fin r → E) (t : ℝ) (x : Frame X.Ψ r) :
    X.flow ((n : E) • v) (fun _ => Complex.I * ((t / (n : ℝ) ^ 2 : ℝ) : ℂ)) x =
      X.flow v (fun _ => Complex.I * (t : ℂ)) x := by
  funext τ
  simp only [Data.flow, flowMat_nsmul]
  congr 2
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  push_cast
  field_simp

theorem lact_mul_q {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact (a * b) x = lact a (lact b x) := by
  funext τ
  simp only [lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
  rw [Matrix.mul_assoc]
  rfl

theorem norm_chi (X : Data E r) (la : Wt X.Ψ r) {g : GL (Fin r) E} (hg : g ∈ X.Γ) : ‖X.χ la g‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have := congrArg norm (h g hg)
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

end GlobalTheory.HeckeEx.Dom


open GlobalTheory.HeckeEx.Dom in
theorem GlobalTheory.HeckeEx.mem_SS_of_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (I₀ : Type) [Finite I₀] (X' : I₀ → Data E r) (la : Wt X.Ψ r) (la' : ∀ j, Wt (X' j).Ψ r) (P : Frame X.Ψ r → ℂ) (Q : ∀ j, Frame (X' j).Ψ r → ℂ) (N : ℕ) (M : ℝ), 0 < N → 0 ≤ M → X.IsSec la P → (∀ j, Q j ∈ (X' j).SS (la' j)) → (∀ j a (h : QMatch X (X' j) N a) τ m, la' j τ m = la ⟨τ.1, h.mem τ⟩ m) → (∀ x ∈ X.dom, ∀ B : ℝ, 0 ≤ B → (∀ j a (h : QMatch X (X' j) N a), ‖Q j (lact a (castFr h.psi x))‖ ≤ B) → ‖P x‖ ≤ M * B) → P ∈ X.SS la := by
  intro E _ _ _ r X I₀ _ X' la la' P Q N M hN hM hP hQ hl hdom
  classical
  haveI : Fintype I₀ := Fintype.ofFinite I₀

  choose C hC using fun j => (hQ j).1.2
  have hbd : ∀ x ∈ X.dom, X.pnorm la P x ≤ M * ∑ j, |C j| := fun x hx => by
    have hn := BoundedSectionAlgebra.nfac_pos X hx la
    have h1 := hdom x hx ((∑ j, |C j|) / X.nfac la x)
      (div_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) hn.le) fun j a h => by
        rw [le_div_iff₀ hn]
        have := hC j _ (h.mem_dom hx)
        rw [BoundedSectionAlgebra.pnorm_eq, nfac_q h (hl j a h)] at this
        exact this.trans ((le_abs_self _).trans
          (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
    rw [BoundedSectionAlgebra.pnorm_eq]
    calc ‖P x‖ * X.nfac la x ≤ M * ((∑ j, |C j|) / X.nfac la x) * X.nfac la x :=
          mul_le_mul_of_nonneg_right h1 hn.le
      _ = M * ∑ j, |C j| := by field_simp
  have hB : X.IsBddSec la P := ⟨hP, _, hbd⟩
  refine ⟨hB, fun ξ hξ x hx => ?_⟩

  choose S hS hS' using fun j => GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator E r X (X' j) N hN
  obtain ⟨hmem, hlim⟩ := GlobalTheory.T.boundedSection_tendsto_constantTerm_imaginary_flow E r X la P hB ξ hξ x hx
  let xt : ℝ → Frame X.Ψ r := fun t => X.flow ξ (fun _ => Complex.I * (t : ℂ)) x
  let Bt : ℝ → ℝ := fun t => ∑ j, ∑ s ∈ (S j).attach,
    ‖Q j (lact s.1 (castFr (hS j s.1 s.2).psi (xt t)))‖
  have hdomt : ∀ t : ℝ, 0 ≤ t → ‖P (xt t)‖ ≤ M * Bt t := fun t ht => by
    refine hdom _ (hmem t ht) _ (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => norm_nonneg _)
      fun j a h => ?_
    obtain ⟨s, hs, b, hb, rfl⟩ := hS' j a h
    have hy := (hS j s hs).mem_dom (hmem t ht)
    have e1 : ‖Q j (lact (b * s) (castFr h.psi (xt t)))‖ = ‖Q j (lact s (castFr (hS j s hs).psi (xt t)))‖ := by
      rw [lact_mul_q, (hQ j).1.1.2.2 b hb _ hy, norm_mul, norm_chi _ _ hb, _root_.one_mul]
    rw [e1]
    have e2 : ‖Q j (lact s (castFr (hS j s hs).psi (xt t)))‖ ≤
        ∑ s' ∈ (S j).attach, ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖ :=
      Finset.single_le_sum (f := fun s' : (S j) => ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖)
        (a := ⟨s, hs⟩) (fun _ _ => norm_nonneg _) (Finset.mem_attach _ _)
    exact e2.trans (Finset.single_le_sum (f := fun j => ∑ s' ∈ (S j).attach,
      ‖Q j (lact s'.1 (castFr (hS j s'.1 s'.2).psi (xt t)))‖)
      (a := j) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  have hBt : Filter.Tendsto Bt Filter.atTop (nhds 0) := by
    have : (0 : ℝ) = ∑ j : I₀, ∑ s ∈ (S j).attach, (0 : ℝ) := by simp
    rw [this]
    refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun s _ => ?_
    have h := hS j s.1 s.2
    let v : Fin r → E := (N : E) • ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ)
    have hv : (X' j).IsIso v := by
      refine ⟨h.lat ξ hξ.1, ?_, ?_⟩
      · have e : herm (X' j).Gm v v = ((N : E) * cc (N : E)) *
            herm (X' j).Gm ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ) ((s.1 : Matrix (Fin r) (Fin r) E) *ᵥ ξ) := by
          simp only [v, herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          simp only [cc, map_mul]
          ring
        rw [e, h.iso, hξ.2.1, MulZeroClass.mul_zero]
      · intro e
        have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
        have hv0 := (smul_eq_zero.1 e).resolve_left hN0
        apply hξ.2.2
        rw [← GlobalTheory.Dict.Pull.inv_mulVec s.1 ξ, hv0, Matrix.mulVec_zero]
    have hy := h.mem_dom hx
    obtain ⟨-, hl'⟩ := GlobalTheory.T.boundedSection_tendsto_constantTerm_imaginary_flow E r (X' j) (la' j) (Q j) (hQ j).1 v hv _ hy
    rw [(hQ j).2 v hv _ hy] at hl'
    have hdiv : Filter.Tendsto (fun t : ℝ => t / (N : ℝ) ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_div_const (by positivity)
    have key := (hl'.comp hdiv).norm
    rw [norm_zero] at key
    refine key.congr fun t => ?_
    simp only [Function.comp_apply, xt, v]
    rw [lact_flow_q h, flow_nsmul _ hN]
  have hP0 : Filter.Tendsto (fun t : ℝ => P (xt t)) Filter.atTop (nhds 0) := by
    have hMB : Filter.Tendsto (fun t => M * Bt t) Filter.atTop (nhds 0) := by
      simpa using hBt.const_mul M
    exact squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨0, fun t ht => hdomt t ht⟩) hMB
  exact tendsto_nhds_unique hlim hP0
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_rigidified_theta_iso_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeEx.exists_isRigIso_baseChange | exact GlobalTheory.HeckeEx.exists_isRigIso_baseChange | (intros; apply GlobalTheory.HeckeEx.exists_isRigIso_baseChange <;> assumption)
end
