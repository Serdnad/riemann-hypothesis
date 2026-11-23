module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle499
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle387
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle613
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelBasePointMulMemRationalMatrices
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle278
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle647
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefCenChar

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem unframe_mem_UH {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.MainNotions.S.UJset (M.ε τ)) :
    (M.fr τ)⁻¹ * u * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : uᴴ * Formalism.REAL.Jm (M.ε τ) * u = Formalism.REAL.Jm (M.ε τ) := hu
  have e1 : M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) = u * M.fr τ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  change ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * u * M.fr τ) = gramAt D V τ
  rw [← M.fr_gram τ]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ)) := by
        rw [Matrix.conjTranspose_mul (M.fr τ)]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
        rw [e1, Matrix.conjTranspose_mul]
        calc (M.fr τ)ᴴ * uᴴ * Formalism.REAL.Jm (M.ε τ) * (u * M.fr τ) = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hJ]

theorem rep_scalar {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {a : Matrix (Fin V.rank) (Fin V.rank) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), g * a = a * g) : ∃ c : ℂ, ∀ w, M.rep τ a w = c • w := by
  haveI : Nontrivial (M.H τ) := (M.ds τ).2.1
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  let A : Module.End ℂ (M.H τ) := (M.rep τ a : M.H τ →ₗ[ℂ] M.H τ)
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, fun w => ?_⟩
  have hirr := (M.ds τ).2.2.2.1
  have hinv : ∀ u ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ v ∈ A.eigenspace c, M.σ τ u v ∈ A.eigenspace c := by
    intro u hu v hv
    have hg := unframe_mem_UH M τ hu
    have e : M.σ τ u = M.rep τ ((M.fr τ)⁻¹ * u * M.fr τ) := by
      unfold DSModel.rep
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [e]
    show M.rep τ a (M.rep τ _ v) = c • M.rep τ _ v
    rw [← GlobalTheory.ConjMult.rep_mul M τ _ ha _ hg, ← hc _ hg, GlobalTheory.ConjMult.rep_mul M τ _ hg _ ha]
    have hv' : M.rep τ a v = c • v := hv
    rw [hv', map_smul]
  rcases hirr (A.eigenspace c) (Submodule.closed_of_finiteDimensional _) hinv with h | h
  · exact absurd h hcA
  · have hw : w ∈ A.eigenspace c := h ▸ Submodule.mem_top
    exact (Module.End.mem_eigenspace_iff).1 hw

theorem infMat_comm {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {z : GA D V} (hzc : z ∈ Subgroup.center (GA D V))
    (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    g * infMat D.sp.cm.sig V.gram (θ τ) z = infMat D.sp.cm.sig V.gram (θ τ) z * g := by
  have e := congrArg (infMat D.sp.cm.sig V.gram (θ τ)) (Subgroup.mem_center_iff.1 hzc (atTau θ V τ g))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul,
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg).2.1] at e
  exact e

theorem rTr_atTau_of_scalar {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {c : ℂ} (hc : ∀ w, M.rep τ g w = c • w) (v : M.Vec) :
    rTr V (atTau θ V τ g) (T v) = c • T v := by
  classical
  have e := hT.equiv τ g hg v (c • v τ) (by rw [hc]; rfl)
  rw [← e, T.map_update_smul, Function.update_eq_self]
  rfl

theorem rTr_realAll {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (Mz : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hM : ∀ ρ, Mz ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (c : D.what₂.Tau → ℂ) (hc : ∀ ρ w, M.rep ρ (Mz ρ) w = c ρ • w) (v : M.Vec) :
    rTr V (GlobalTheory.RowReal.realAll θ V Mz) (T v) = (∏ ρ, c ρ) • T v := by
  classical
  have key : ∀ s : Finset D.what₂.Tau,
      rTr V (GlobalTheory.RowReal.realAll θ V (fun ρ => if ρ ∈ s then Mz ρ else 1)) (T v) = (∏ ρ ∈ s, c ρ) • T v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun ρ : D.what₂.Tau => if ρ ∈ (∅ : Finset D.what₂.Tau) then Mz ρ else 1) = 1 := by
        funext ρ; simp
      rw [e, GlobalTheory.RowReal.realAll_one hθ, Finset.prod_empty, one_smul]
      funext x; simp [rTr]
    | insert τ s hτ ih =>
      have hMs : ∀ ρ, (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun ρ => by
        dsimp only
        split_ifs
        · exact hM ρ
        · exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
      rw [GlobalTheory.RowReal.realAll_eq_atTau_mul hθ hMs τ]
      have e : Function.update (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) τ 1 =
          fun ρ => if ρ ∈ s then Mz ρ else 1 := by
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp [hτ]
        · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
      rw [e, Finset.prod_insert hτ]
      simp only [Finset.mem_insert_self, if_true]
      funext x
      have i1 := congrFun ih (x * atTau θ V τ (Mz τ))
      have i2 := congrFun (rTr_atTau_of_scalar hT τ (hM τ) (hc τ) v) x
      simp only [rTr, Pi.smul_apply, smul_eq_mul] at i1 i2 ⊢
      rw [← mul_assoc, i1, i2]
      ring
  have e : (fun ρ : D.what₂.Tau => if ρ ∈ (Finset.univ : Finset D.what₂.Tau) then Mz ρ else 1) = Mz := by
    funext ρ; simp
  have := key Finset.univ
  rwa [e] at this

theorem cusp_hasCen : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ν : ℕ) (P : D.what₂.Tau → SPar), N.Is ν 0 P → ∃ χ : GA D N.V → ℂ, ∀ (F : N.Cusp θ) (v : SmT N.M), GlobalTheory.SeeSaw.HasCen N.V χ (F.1 v) := by
  intro D θ hθ N ν P hN
  have hs : N.V.SigOK := hN.sigOK
  have hd : N.V.IsDefinite := fun τ => Or.inl (by rw [hN.sig, hN.rank]; simp)
  have hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have key : ∀ (z : GA D N.V) (ρ : D.what₂.Tau), ∃ c : ℂ, z ∈ Subgroup.center (GA D N.V) →
      ∀ w, N.M.rep ρ (infMat D.sp.cm.sig N.V.gram (θ ρ) z) w = c • w := by
    intro z ρ
    by_cases hz : z ∈ Subgroup.center (GA D N.V)
    · haveI := hfd ρ
      obtain ⟨c, hc⟩ := rep_scalar N.M ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ)
        (fun g hg => infMat_comm hθ hz ρ hg)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose c hc using key
  refine ⟨fun z => ∏ ρ, c z ρ, fun F v z hz hzc h => ?_⟩
  have hreal : ∀ T : MMap N.M, IsMultMap θ N.M ∅ 1 T → ∀ (u : N.M.Vec) (g : GA D N.V),
      T u (g * z) = (∏ ρ, c z ρ) * T u g := by
    intro T hT u g
    have e : GlobalTheory.RowReal.realAll θ N.V (fun ρ => infMat D.sp.cm.sig N.V.gram (θ ρ) z) = z :=
      GlobalTheory.RowReal.realAll_eq hθ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) ⟨hz, fun ρ => rfl⟩
    have := rTr_realAll hθ hT _ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) (c z)
      (fun ρ => hc z ρ hzc) u
    rw [e] at this
    exact congrFun this g
  have key2 : ∀ T ∈ Mult θ N.M ∅ 1, ∀ (x : SmT N.M) (g : GA D N.V),
      PiTensorProduct.lift T x (g * z) = (∏ ρ, c z ρ) * PiTensorProduct.lift T x g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        intro g
        simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
        rw [hreal T hT f g]
        ring
      | add a b ha hb =>
        intro g
        simp only [map_add (f := _), Pi.add_apply]
        rw [ha g, hb g]
        ring
    | zero => intro x g; simp
    | add T T' _ _ h1 h2 =>
      intro x g
      simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
      rw [h1 x g, h2 x g]
      ring
    | smul a T _ h =>
      intro x g
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h x g]
      ring
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ N.M ∅ 1 := (mem_multT θ N.M ∅ 1 F.1).1 F.2
  have := key2 _ hm v h
  rw [LinearEquiv.apply_symm_apply] at this
  exact this

end GlobalTheory.DefCenChar

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

open GlobalTheory.Unf.FB GlobalTheory.FlatBase

namespace GlobalTheory.Asc.FlatBaseL

theorem fl_base_eq_contract : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  intro D ψ σ J B s vb vL y Ψ hy hΨ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hchar := hstd.1
  obtain ⟨-, ⟨My, hMy, -⟩, -, -, -, hlaw0⟩ := GlobalTheory.Unf.FB.ThLawsL.th_laws D ψ hstd σ J B y hy
  have hlaw : ∀ b, ∀ u ∈ UX D (σ + 1), star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b * J.d.levi u) y 0) * star (psiFlag ψ J.d (J.d.nB b * J.d.levi u)) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := hlaw0
  have hnorm : ∀ u : UX D (σ + 1), ‖psiUni ψ u.1‖ = 1 := fun u => hchar.2.1 _
  have hfl : ∀ u : UX D (σ + 1), (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ) =
      star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := by
    intro u
    have hf : Quasi ψ J.W₀ B.V (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1)) := by
      have h := (GlobalTheory.MixValues.mixed_values D ψ hstd).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1)
      exact ⟨h.quasi, h.cont⟩
    have hh := (GlobalTheory.Asc.heis_baseL D ψ hstd σ J.W₀ B vb s.vT vL _ y hf hy).1
    calc (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ)
        = ∫ b in vb.𝓕, star (psiUni ψ u.1) * (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b) *
            star (y (zEll B.L (σ + 1) B.ζ ⬝ b))) ∂vb.μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
          simp only [flFun]
          rw [hlaw b u.1 u.2]
          simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          ring
      _ = _ := by
          rw [integral_const_mul]
          exact congrArg (star (psiUni ψ u.1) * ·) hh
  have hLeft : fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = ∫ u, star (psiUni ψ u.1) *
      ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν := by
    unfold fl
    exact integral_congr_ae (Filter.Eventually.of_forall hfl)
  obtain ⟨x, hxo, hx⟩ := GlobalTheory.Asc.FBx.exists_rat_eq_xLast D σ B
  obtain ⟨M, hMi, hMb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x
    hxo.1 Ψ hΨ {1} isCompact_singleton
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  have hbound : ∀ (u : UX D (σ + 1)) (v : WO J.W₀ B.L),
      ‖flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)‖ ≤
        M u * My := by
    intro u v
    have h := hMb 1 (Set.mem_singleton 1) 0 ((B.o.resT J.W₀).symm (0, v)) u
    rw [hx, hom1] at h
    rw [norm_mul, norm_star]
    exact mul_le_mul h (hMy v) (norm_nonneg _) ((norm_nonneg _).trans h)
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  have : SecondCountableTopology (WO J.W₀ B.L) := (lattice_Mx D B.L.rank J.W₀.rank).2.2.1
  have hE : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ p.1.1.1) 0 ((B.o.resT J.W₀).symm (0, p.2)) := by
    have hmc := (GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ).2
    have hc : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => (p.1.1.1 : Mx D (σ + 1) (σ + 1)) :=
      (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
    have hin : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
        ((1 : GA D J.W × GA D B.V), xLast B.d (vecB B.o B.ζ) ⬝ p.1.1.1, (0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, p.2)) :=
      continuous_const.prodMk ((continuous_const.matrix_mul hc).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd))))
    have h := hmc.comp hin
    simpa only [Function.comp_def, hom1] using h
  have hK : Continuous (Function.uncurry fun (u : UX D (σ + 1)) (v : WO J.W₀ B.L) =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)) :=
    ((continuous_star.comp ((continuous_psiUni hchar.1 (σ + 1)).comp continuous_fst)).mul hE).mul
      (continuous_star.comp (hy.2.comp continuous_snd))
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; simp)
  have hswap := integral_swap_of_majorant s.vU.ν (vL.μ.restrict vL.𝓕) (fun u v =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v))
    hK.stronglyMeasurable M hMi My hbound
  have h1 : fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := by
    rw [hLeft]
    calc (∫ u, star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
            ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν)
        = ∫ u, ∫ v in vL.𝓕, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂vL.μ ∂s.vU.ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [flatFun]
          ring
      _ = ∫ v in vL.𝓕, ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂s.vU.ν ∂vL.μ := hswap
      _ = ∫ v in vL.𝓕, (∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u
            ∂s.vU.ν) * star (y v) ∂vL.μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => integral_mul_const _ _)
      _ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := rfl
  refine ⟨h1, fun Mb hMb' => ?_⟩
  rw [← h1]
  unfold fl
  calc ‖∫ u, ∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ ∂s.vU.ν‖ₑ
      ≤ ∫⁻ u, ‖∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ‖ₑ ∂s.vU.ν :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ‖flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b‖ₑ ∂vb.μ ∂s.vU.ν :=
        lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ENNReal.ofReal Mb *
          ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
        refine lintegral_mono fun u => lintegral_mono fun b => ?_
        simp only [flFun]
        rw [enorm_mul]
        gcongr
        · rw [hlaw b u.1 u.2, ← ofReal_norm, norm_mul, norm_star, norm_star, hnorm u, one_mul]
          exact ENNReal.ofReal_le_ofReal (hMb' _)
        · simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, le_refl]
    _ = _ := (lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end GlobalTheory.Asc.FlatBaseL

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_down {D : D7} {X : ProvA} (h : GlobalTheory.ArchRec.Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) (τ : D.what₂.Tau) (V W : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ForAllAt τ V W aS aT S S' fun MS MT A B pt =>
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.LiftLaw MT τ B pt MS A ∧ ∀ ip, GlobalTheory.ArchRec.IsIp V W ip → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaLaw MT τ B pt MS A ip := by
  obtain ⟨al, be, ga, de, hd, -, rfl, rfl⟩ := hp
  intro ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf
  obtain ⟨hm, e, u, hk⟩ := GlobalTheory.ArchRec.tie_small h hd.1 MS τ true false p1
  obtain ⟨e', u', hk'⟩ := GlobalTheory.ArchRec.tie_large h hd.1 MT τ false true p2
  obtain ⟨κ, hR⟩ := GlobalTheory.ArchRec.exists_real hω hS hT (GlobalTheory.ArchRec.isFrameOf_model MS τ) (GlobalTheory.ArchRec.isFrameOf_model MT τ) hf
    hk.ord.1 hk'.ord.1
  exact GlobalTheory.ArchRec.lift_down h h1 h3 hd hm hk hk' hR

theorem pairPar_of_upPair {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) :
    GlobalTheory.PairLift.PairPar S S' aS aT ∧ GlobalTheory.PairLift.PairPar S' S aT aS := by
  obtain ⟨al, be, ga, de, hd, hfar, rfl, rfl⟩ := hp
  have hT : GlobalTheory.PairLift.ThetaPar t (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) (GlobalTheory.Chain.signed (al ++ block t ++ de) (ga ++ be) aS) aT aS :=
    ⟨al, be, ga, de, rfl, Or.inl ⟨hd, rfl⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + aT := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨⟨t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩, ⟨t, _, _, rfl, rfl, Or.inr hT⟩⟩

theorem upPair_arch : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (S S' : SPar) (aS aT : ℚ),
    UpPair t S S' aS aT → (∀ (τ : D.what₂.Tau) (V W : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ToSource τ V W aS aT S S' ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaSource τ V W aS aT S S') ∧ ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X →
      Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → GlobalTheory.PairLift.RulePar X S S' aS aT ∧ GlobalTheory.PairLift.RulePar X S' S aT aS := by
  intro hDS hHC D t S S' aS aT hp
  refine ⟨fun τ V W => ?_, fun X h3 h4 h5 => ?_⟩
  · obtain ⟨X, hX, h1, -, h3, -, -⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
    have h : GlobalTheory.ArchRec.Good D X :=
      ⟨hX, GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX, hHC.admQ5_of_harishChandraModules X, GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D⟩
    have down := upPair_down h h1 h3 hp τ V W
    exact ⟨fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).1,
      fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf μ 𝓕 m1 m2 =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).2 _ ⟨μ, 𝓕, m1, m2, rfl⟩⟩
  · obtain ⟨q1, q2⟩ := pairPar_of_upPair hp
    exact ⟨GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q1, GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q2⟩

end GlobalTheory.EvenOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.coefficientPoincareSeries_summable_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) → (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) → (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V, Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
  first | exact @GlobalTheory.poincare_sum_bound | exact GlobalTheory.poincare_sum_bound | (intros; apply GlobalTheory.poincare_sum_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.coefficientPoincareSeries_isAutomorphic : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, (∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsAutFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ModGrowth V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ (∀ g, Summable fun γ : GQ V => ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * g)‖) ∧ ∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪), ∀ g, poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (fun τ => a τ) (g * k) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (fun τ => a τ) g) ∧ (∃ T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M, ∀ a, T₀ a = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ (a : ∀ τ, M.H τ) τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (Function.update a τ (M.rep τ k (a τ))) = rTr V (atTau θ V τ k) (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c a) := by
  first | exact @GlobalTheory.PoinAut.poin_aut | exact GlobalTheory.PoinAut.poin_aut | (intros; apply GlobalTheory.PoinAut.poin_aut <;> assumption)
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


theorem _root_.GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) {S B : HSp D} (LS : Lat S) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ₀ : Lat B), IsSelfDualC S LS → IsSelfDualC B (idLat I Λ₀) → IsSelfDualC B (idLat (I * shiftId G) Λ₀) → ∀ z : WO S B, z ∈ latO S B (LS : Set _) (idLat I Λ₀ : Set _) (fun _ => True) → (∃ e, IsIdemSum e G.pl.W0 ∧ e • z ∈ hatMx (G.modul • homLat LS (idLat I Λ₀))) → z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) (fun _ => True) := by
  first | exact @GlobalTheory.DepthShift.mem_latO_shift | exact GlobalTheory.DepthShift.mem_latO_shift | (intros; apply GlobalTheory.DepthShift.mem_latO_shift <;> assumption)
end
end
