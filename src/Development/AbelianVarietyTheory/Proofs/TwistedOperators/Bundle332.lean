module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle192
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle243
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

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

namespace GlobalTheory.TripleRead

variable {D : D7}

def toUX (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨⟨(mt X g).submatrix e e, (mt X g⁻¹).submatrix e e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]; exact Matrix.submatrix_one_equiv e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]; exact Matrix.submatrix_one_equiv e⟩, by
    subst hJ
    have k : (mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (mt X g).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
      have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    show ((mt X g).submatrix e e)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) *
      ((mt X g).submatrix e e).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((X.gramᵀ).submatrix e e) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ).submatrix e e := rfl
    have e2 : ((mt X g).submatrix e e).map (cA D) = ((mt X g).map (cA D)).submatrix e e := rfl
    rw [e1, e2, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, k]⟩

theorem toUX_val (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : (toUX X e hJ g).1.1 = (mt X g).submatrix e e := rfl

end GlobalTheory.TripleRead

namespace GlobalTheory.TripleRead

variable {D : D7}

structure IsReading (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : Bs.ψ = ψ

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = A.cart τ ∧ Γ.V'.θ w = -A₁.cart τ ∧
    Γ.W.θ w = ((B.cart τ).submatrix e e).map conj

  α : Xc.α = α

  β : Xc.β = β

def ptO {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin m) (AE D)) :
    Matrix (Fin m) (Fin k) (AE D) :=
  ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹)ᵀ).submatrix id e

def thO {m k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) {d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ) (x : Matrix (Fin d) (Fin m) (AE D)) : ℂ :=
  GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ (ptO G e x) Φ)

def IsTransp (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} {k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z) (ω : WRep M X) (e : Fin k ≃ Fin X.rank)
    (gM : GA D M → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (gX : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Z.J) : Prop :=
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), ∀ g h,
    thO Mo ψ (sgn ε M).gram e (om (gM g, gX h) Φ) = ω (g, h) (thO Mo ψ (sgn ε M).gram e Φ)

end GlobalTheory.TripleRead

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviGLRes

variable {D : D7}

theorem covolOne_integral_mul_right {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (M M' : Mx D n n) (hM'M : M' * M = 1) (hMM' : M * M' = 1)
    (hM : M ∈ GlobalTheory.MixModel.ratMx D n n) (hM' : M' ∈ GlobalTheory.MixModel.ratMx D n n) (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (a * M) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  let e : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => a * M
      invFun := fun a => a * M'
      left_inv := fun a => by simp only [Matrix.mul_assoc, hMM', Matrix.mul_one]
      right_inv := fun a => by simp only [Matrix.mul_assoc, hM'M, Matrix.mul_one]
      map_add' := fun a b => Matrix.add_mul _ _ _ }
  have he : Continuous e := continuous_id.matrix_mul continuous_const
  have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
  have hr : ∀ x, e x ∈ GlobalTheory.MixModel.ratMx D m n ↔ x ∈ GlobalTheory.MixModel.ratMx D m n := fun x =>
    ⟨fun h => by
      have h2 := GlobalTheory.MixModel.ratMx_mul h hM'
      have h3 : e x * M' = x := e.symm_apply_apply x
      rwa [h3] at h2,
     fun h => GlobalTheory.MixModel.ratMx_mul h hM⟩
  obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hμ e he he' hr
  rw [← GlobalTheory.MixModel.covolOne_integral_eq hμ h1 φ hφ, hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]
  rfl

end GlobalTheory.LeviGLRes

namespace GlobalTheory.LeviGLRes

theorem res_levi_GL : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) D.host.E) (f : WO V W → ℂ), IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (d.levi (Matrix.GeneralLinearGroup.map (incA D) a), 1) f) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs d hC hB ψ χS χT ω hω μ 𝓨 hcov a f hf
  subst hC hB
  set A : GL (Fin r) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a with hA
  have hA1 : A.1 = GlobalTheory.MixModel.rat a.1 := rfl
  have hAi : (A⁻¹).1 = GlobalTheory.MixModel.rat (a⁻¹).1 := rfl
  have hmem : d.levi A ∈ GQ V :=
    d.levi_mem_GQ (by rw [hA1]; exact GlobalTheory.MixModel.rat_mem _) (by rw [hAi]; exact GlobalTheory.MixModel.rat_mem _)
  have hsub : ∀ w : WO V W, ω (d.levi A, 1) f w = f (w * Formalism.L2.Theta.mt V (d.levi A)) := fun w => by
    have h := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω _ hmem 1 (one_mem _) f hf
      (w * Formalism.L2.Theta.mt V (d.levi A))
    rwa [GlobalTheory.LeviRes.actO_mul_mt] at h
  set M : Mx D r r := GlobalTheory.MixModel.adj (A⁻¹).1 with hMdef
  set M' : Mx D r r := GlobalTheory.MixModel.adj A.1 with hM'def
  have hMM' : M * M' = 1 := by
    rw [hMdef, hM'def, ← GlobalTheory.MixModel.adj_mul, Units.mul_inv, GlobalTheory.MixModel.adj_one]
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← GlobalTheory.MixModel.adj_mul, Units.inv_mul, GlobalTheory.MixModel.adj_one]
  have hM : M ∈ GlobalTheory.MixModel.ratMx D r r := GlobalTheory.MixModel.ratMx_adj (by rw [hAi]; exact GlobalTheory.MixModel.rat_mem _)
  have hM' : M' ∈ GlobalTheory.MixModel.ratMx D r r := GlobalTheory.MixModel.ratMx_adj (by rw [hA1]; exact GlobalTheory.MixModel.rat_mem _)
  funext x
  have key : ∀ y : Mx D W.rank r,
      ω (d.levi A, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) =
        f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e (y * M) + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) := by
    intro y
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y * Formalism.L2.Theta.mt V (d.levi A) =
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e (y * M) := by
      show (y * d.pY) * Formalism.L2.Theta.mt V (d.levi A) = (y * M) * d.pY
      rw [Matrix.mul_assoc, d.pY_levi, ← Matrix.mul_assoc]
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x * Formalism.L2.Theta.mt V (d.levi A) =
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x := by
      rw [GlobalTheory.Bridge.orthProjPartHomToHermitian_eq_wittDecompositionCore, GlobalTheory.MixModel.HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.wittDecomp_projAnisotropic_levi]
    rw [hsub, Matrix.add_mul, e1, e2]
  show ∫ y in 𝓨, ω (d.levi A, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) ∂μ =
    ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) ∂μ
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact covolOne_integral_mul_right hcov M M' hM'M hMM' hM hM'
    (fun y => f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x))
    (GlobalTheory.LeviRes.periodic hs hf x)

end GlobalTheory.LeviGLRes
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistThetaMean

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a b : Mx D W.rank r) :
    isoPart V W C (a + b) = isoPart V W C a + isoPart V W C b :=
  Matrix.add_mul _ _ _

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {γ : Mx D W.rank r}
    (hγ : γ ∈ ratMx D W.rank r) : isoPart V W C γ ∈ ratL W V := by
  obtain ⟨g, rfl⟩ := hγ
  refine ⟨g * (adj D C * V.gram), ?_⟩
  show (g * (adj D C * V.gram)).map (incA D) = g.map (incA D) * (adj D C * V.gram).map (incA D)
  exact Matrix.map_mul

theorem isoPart_continuous (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) :=
  continuous_id.matrix_mul continuous_const

theorem midPart_continuous (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    Continuous (midPart V V' W B) :=
  continuous_id.matrix_mul continuous_const

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean

theorem integral_continuous_of_bounded {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : X × Y → ℂ) (hk : Continuous k) (b : ℝ) (hb : ∀ q, ‖k q‖ ≤ b) :
    Continuous (fun p => ∫ y, k (p, y) ∂ν) ∧ ∀ p, ‖∫ y, k (p, y) ∂ν‖ ≤ b * ν.real Set.univ := by
  refine ⟨continuous_of_dominated (bound := fun _ => b) (fun p => ?_) (fun p => ?_) (integrable_const _) ?_,
    fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => hb _)⟩
  · exact (hk.comp (Continuous.prodMk_right p)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hb _
  · exact Filter.Eventually.of_forall fun y => hk.comp (Continuous.prodMk_left y)

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean


open TopologicalSpace in
theorem mean_continuous_periodic : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B _hs C' _h1 _h2 _h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' h𝓕' P G hP hG
  haveI hAE : SecondCountableTopology (AE D) := by
    have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E)
      (AF D.host.F)
    exact e.secondCountableTopology
  haveI hM : SecondCountableTopology (Mx D W.rank r) :=
    inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin r → AE D))
  haveI hM2 : SecondCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    @instSecondCountableTopologyProd _ _ _ _ hM hM
  haveI : FirstCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    SecondCountableTopology.to_firstCountableTopology _
  haveI : FirstCountableTopology (Mx D W.rank r) := SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V'
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO V' W) (ratL W V') hK hKc μ' h𝓕'⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by
    rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b1, hb1⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hP
  obtain ⟨b2, hb2⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hh : Continuous fun w => P w * star (G w) := hP.cont.mul hG.cont.star
  have hhb : ∀ w, ‖P w * star (G w)‖ ≤ b1 * b2 := fun w => by
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb1 w) (hb2 w) (norm_nonneg _) ((norm_nonneg _).trans (hb1 w))
  have hu : Continuous fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2 :=
    (((isoPart_continuous V W C').comp (continuous_fst.comp continuous_fst)).add
      ((isoPart_continuous V W C).comp (continuous_snd.comp continuous_fst))).add
      ((midPart_continuous V V' W B).comp continuous_snd)
  obtain ⟨hin, hinb⟩ := integral_continuous_of_bounded (μ'.restrict 𝓕')
    (fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      P (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2) *
        star (G (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2))) (hh.comp hu) (b1 * b2)
    (fun q => hhb _)
  refine ⟨?_, ?_⟩
  · exact (integral_continuous_of_bounded (μ.restrict 𝓨)
      (fun q : Mx D W.rank r × Mx D W.rank r => ∫ x in 𝓕',
        P (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x) *
          star (G (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x)) ∂μ') hin _ hinb).1
  · intro γ hγ t
    have key : ∀ y x, P (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x)) =
        P (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' t + isoPart V W C y + midPart V V' W B x)) := fun y x => by
      rw [isoPart_add, add_assoc (isoPart V W C' γ) (isoPart V W C' t),
        add_assoc (isoPart V W C' γ) (isoPart V W C' t + isoPart V W C y)]
      exact GlobalTheory.ThetaSchur.prod_periodic hψ hP hG (isoPart_rat V W C' hγ) _
    simp_rw [key]

end GlobalTheory.TwistThetaMean
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoefUnfold

theorem pcoef : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ (y : Mx D W.rank r) (a : Matrix (Fin W.rank) (Fin r) D.host.E), (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = ∫ t in 𝓨, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * (κ • (∫ y' in 𝓨, ∫ x in 𝓕', (heisO ψ V W (isoPart V W C y) F) (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ)) ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕' κ hκ F G hF hG y a
  have hth := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have horth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hPt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) := hth.1 _ F hF
  have hγrat : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
    rw [← GlobalTheory.TwistEquiRat.ratW_eq_isoPart]; exact ⟨_, rfl⟩
  have hfirst : heisO ψ V W (isoPart V W C (y + a.map (incA D))) F =
      heisO ψ V W (isoPart V W C (a.map (incA D))) (heisO ψ V W (isoPart V W C y) F) := by
    rw [hth.2.1, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame, AddChar.map_zero_eq_one, one_smul,
      GlobalTheory.TwistEquiRat.isoPart_add, add_comm]
  have hpt : ∀ w, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) =
      ψ (symplO V W w (isoPart V W C (a.map (incA D)))) * (heisO ψ V W (isoPart V W C y) F w * star (G w)) := by
    intro w
    rw [hfirst, GlobalTheory.ThetaSchur.heisO_rat hPt hγrat]
    ring
  have hsym : ∀ t y' x, symplO V W (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)
      (isoPart V W C (a.map (incA D))) = symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))) := by
    intro t y' x
    rw [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left, horth.1 y' _,
      GlobalTheory.PlaceModel.symplO_skew V W (isoPart V W C (a.map (incA D))) (midPart V V' W B x), horth.2.1 _ x]
    simp
  have hHt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C (y + a.map (incA D))) F) := hth.1 _ F hF
  have hHc : Continuous fun w => heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) :=
    hHt.cont.mul hG.cont.star
  have hHb : ∃ b : ℝ, ∀ w, ‖heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w)‖ ≤ b := by
    obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hHc.continuousOn
    refine ⟨b, fun w => ?_⟩
    obtain ⟨g, hg, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w]
    exact hb _ h
  have key := hκ _ hHc hHb (fun g hg w => GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w)
  rw [key]
  simp_rw [hpt, hsym, integral_const_mul]
  rw [← integral_smul]
  congr 1
  funext t
  rw [mul_smul_comm]

end GlobalTheory.TwistCoefUnfold
end
end

section


theorem _root_.GlobalTheory.T.satakeTrivialBound_inertPlace_unitarisable_spherical : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  first | exact @GlobalTheory.SatBoundInert.satakeBoundInert | exact GlobalTheory.SatBoundInert.satakeBoundInert | (intros; apply GlobalTheory.SatBoundInert.satakeBoundInert <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.OpsRowsTuple

theorem offS_badPl_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (w : Pl D.host.E) :
    OffS D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) w ↔ GlobalTheory.Hk3.Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_ops_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ t : T, ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H, (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) ∧ GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h ∧ (∀ (c : Pl D.host.E → List ℤ → ℂ) P, GlobalTheory.Hk3.Good R t P → ∀ cc, ∀ x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, h P cc x = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x) ∧ ∀ (c : Pl D.host.E → List ℤ → ℂ) x, (∀ P d, GlobalTheory.Hk3.Good R t P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = c P (dualLab d) • x) → x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t
  have hgp := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg := hgp.2.1
  have hoff := offS_badPl_iff R t
  have h0 : ∀ P, Good R t P → Good R A.μ0 P := fun P hP => (hg t P hP).2.2
  have hβ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  cases hβ with
  | intro n hβ =>
  have lev := fun P (hP : Good R t P) => GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hg _ P (h0 P hP)).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => h0 P hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have H := GlobalTheory.Hk3.OpsRows.exists_ops (θ := R.θ) (M := R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) R.ν0 R.fd0 hC.models.inf hC.models.ν0.1.1 hC.models.ν0.2
    hS.2.1 R.HE _ hC.models.HE (goodPart_le _ _ _ _ _) (Good R t)
    (fun P d B => ⟨fun hB => by
        have hP : Good R t P := by
          obtain ⟨_, _, _, _, hO, -⟩ := hB
          exact (hoff P).1 hO
        exact ⟨hP, (((lev P hP).2.1 _ d B).1 hB).2⟩,
      fun hB => ((lev P hB.1).2.1 _ d B).2 ⟨(hoff P).2 hB.1, hB.2⟩⟩)
    (fun P hP => (lev P hP).1)
    (fun P hP c U hU => by
      obtain ⟨hU1, hU2⟩ := (mem_goodPart _ _ _ _ _ _).1 hU
      refine (mem_goodPart _ _ _ _ _ _).2 ⟨(lev P hP).2.2.2.2 _ _ _ c hC.models.inf U hU1, fun v => ?_⟩
      have hfix : ∀ k ∈ hyp (Yc D 0) P, ∀ g, U v (g * k) = U v g := fun k hk g => by
        rw [GlobalTheory.Hk3.OpsRows.mult_lev hU1 v k ((lev P hP).1 k hk).1 g, ((lev P hP).1 k hk).2, one_mul]
      rw [postOn_apply]
      conv_rhs => rw [← hU2 v]

      simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      exact (lev P hP).2.2.2.1 c _ _ hfix)
  cases H with
  | intro h H2 =>
  exact ⟨h, H2.1, H2.2.1, fun c => H2.2.2.2.1 _, fun c => H2.2.2.2.2 _⟩

end GlobalTheory.Hk3.OpsRowsTuple

end
end
