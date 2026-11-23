module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle359
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle387

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitaryKernelLeExpPowEight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder Matrix

namespace GlobalTheory.OneParamOrbit

theorem eps_true_of_posDef {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) (i : Fin X.rank) : B.ε τ i = true := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hinj : Function.Injective ((B.fr τ)⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_nonsing_inv_iff).mpr (B.fr_unit τ))
  have hJ : ((B.fr τ)⁻¹)ᴴ * gramAt D X τ * (B.fr τ)⁻¹ = Formalism.REAL.Jm (B.ε τ) := by
    rw [← B.fr_gram τ]
    have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * Formalism.REAL.Jm (B.ε τ) * B.fr τ) * (B.fr τ)⁻¹
        = (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (B.ε τ) := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hpos := (hG.conjTranspose_mul_mul_same hinj).diag_pos (i := i)
  rw [hJ] at hpos
  by_contra hne
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hne] at hpos
  norm_num at hpos

theorem conj_mem_Kset {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) {E : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hE : Eᴴ * gramAt D X τ * E = gramAt D X τ) :
    B.fr τ * E * (B.fr τ)⁻¹ ∈ Formalism.REAL.Kset (B.ε τ) := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hJ1 : Formalism.REAL.Jm (B.ε τ) = 1 := by
    have : B.ε τ = fun _ => true := funext (eps_true_of_posDef B τ hG)
    rw [this]; simp [Formalism.REAL.Jm]
  have hgram : (B.fr τ)ᴴ * B.fr τ = gramAt D X τ := by
    rw [← B.fr_gram τ, hJ1, Matrix.mul_one]
  refine ⟨?_, by rw [hJ1, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
  calc (B.fr τ * E * (B.fr τ)⁻¹)ᴴ * (B.fr τ * E * (B.fr τ)⁻¹)
      = ((B.fr τ)⁻¹)ᴴ * (Eᴴ * ((B.fr τ)ᴴ * B.fr τ) * E) * (B.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ * (B.fr τ * (B.fr τ)⁻¹) := by
        rw [hgram, hE, ← hgram]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem orbit_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X),
    GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, ∃ a b : ℚ, HasInfExp D χ τ a ∧ HasInfExp D χ' τ b) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A B,
      ∃ V : Submodule ℂ (WO M X → ℂ), FiniteDimensional ℂ V ∧ ∀ t : ℝ, ω (1, oneP θ X τ Y t) Φ ∈ V := by
  intro D ψ θ _hψ hθ M X A B χ χ' ω hω hexp hsig τ Y hY Φ hΦ
  have hG : (gramAt D X τ).PosDef := GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hsig τ)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    by_cases hf0 : f = 0
    · subst hf0
      have h0 : fockF ψ θ false A B 0 P = 0 := by
        have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ (GlobalTheory.Grid.sgn false M) X (frSgn false A).cart B.cart
          A.onb B.onb 0 0 P
        rwa [zero_smul, zero_smul] at this
      refine ⟨⊥, inferInstance, fun t => ?_⟩
      rw [h0, map_zero]; exact zero_mem _
    · obtain ⟨a, b, ha, hb⟩ := hexp τ
      obtain ⟨x, y, -, -, hK⟩ := GlobalTheory.CompactFockAction.compactFockAll D (GlobalTheory.Grid.sgn false M) X
        (frSgn false A) B θ ψ χ χ' (ω.toSgn false) f τ a b hθ hω ha hb hf hf0
      refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (fockF ψ θ false A B f),
        inferInstance, fun t => ?_⟩
      have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
      have hE : (NormedSpace.exp (t • Y))ᴴ * gramAt D X τ * NormedSpace.exp (t • Y) = gramAt D X τ :=
        GlobalTheory.SmoothAutCheck.exp_mem_UH (Matrix.isUnit_iff_isUnit_det _ |>.mp hG.isUnit) hY t
      have hk := conj_mem_Kset B τ hG hE
      have hA1 : (frSgn false A).elt θ τ 1 = 1 := by
        have hAu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.fr_unit τ)
        show atTau θ _ τ ((A.fr τ)⁻¹ * 1 * A.fr τ) = 1
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hAu]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ _ τ
      have hBk : B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) = oneP θ X τ Y t := by
        show atTau θ X τ ((B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ) = _
        rw [show (B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ
            = ((B.fr τ)⁻¹ * B.fr τ) * NormedSpace.exp (t • Y) * ((B.fr τ)⁻¹ * B.fr τ) by
              simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]
        rfl
      have hω1 : ω (1, oneP θ X τ Y t)
          = (ω.toSgn false) ((frSgn false A).elt θ τ 1, B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹)) := by
        rw [hA1, hBk]
        show ω (1, _) = ω ((GlobalTheory.Grid.ofSgn false M) 1, _)
        rw [map_one]
      have key := hK 1 (GlobalTheory.Chain.RealIt.one_mem_Kset _) _ hk P
      have hfock : fockF ψ θ false A B f P = GlobalTheory.ChainFr.ptF ψ θ (frSgn false A) B f P := rfl
      rw [hfock, hω1, key]
      refine Submodule.smul_mem _ _ ⟨_, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun t => by rw [map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨V₁, h₁, hV₁⟩ := hx
    obtain ⟨V₂, h₂, hV₂⟩ := hy
    exact ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, fun t => by
      rw [map_add]; exact add_mem (Submodule.mem_sup_left (hV₁ t)) (Submodule.mem_sup_right (hV₂ t))⟩
  | smul c x _ hx =>
    obtain ⟨V, h, hV⟩ := hx
    exact ⟨V, h, fun t => by rw [map_smul]; exact Submodule.smul_mem _ _ (hV t)⟩

end GlobalTheory.OneParamOrbit
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SpecTraceProof

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}


open Classical in
theorem isCopyFinDS_of_equiv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : GA D V →* (H →L[ℂ] H)} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {σ : Representation ℂ (GfC V) W} {σ' : Representation ℂ (GfC V) W'} (f : σ.Equiv σ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ' M ρ ⊤ := by
  obtain ⟨T, hT, hinj, hspan⟩ := h
  refine ⟨T ∘ₗ f.symm.toLinearEquiv.toLinearMap, ?_, hinj.comp f.symm.toLinearEquiv.injective, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => h3 i g _ y⟩
    have e : f.symm.toLinearEquiv (σ' g w) = σ g (f.symm.toLinearEquiv w) :=
      LinearMap.congr_fun (f.symm.isIntertwining' g) w
    have h2' := h2 g (f.symm.toLinearEquiv w) y
    rw [← e] at h2'
    exact h2'
  · rw [← hspan]
    congr 2
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_setOf_eq]
    exact ⟨fun ⟨w, y, hv⟩ => ⟨_, y, hv⟩, fun ⟨w, y, hv⟩ => ⟨f.toLinearEquiv w, y, by simpa using hv⟩⟩


open Classical in
theorem isCopyFinDS_of_uEquiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : GA D V →* (H →L[ℂ] H)} {ρ' : GA D V →* (H' →L[ℂ] H')} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hρ : UEquiv ρ ρ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ M ρ' ⊤ := by
  obtain ⟨A, hA⟩ := hρ
  obtain ⟨T, hT, hinj, hspan⟩ := h
  let C := (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H'
    (A.toContinuousLinearEquiv : H →L[ℂ] H')).toLinearMap
  have hC : ∀ w y, (C ∘ₗ T) w y = A (T w y) := fun _ _ => rfl
  refine ⟨C ∘ₗ T, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => ?_⟩
    · rw [hC, hC, h2, hA]
    · rw [hC, hC, h3, hA]
  · intro w w' e
    refine hinj (ContinuousMultilinearMap.ext fun y => A.injective ?_)
    rw [← hC, ← hC, e]
  · have hS : {v | ∃ w y, v = (C ∘ₗ T) w y} = A '' {v | ∃ w y, v = T w y} := by
      ext v
      simp only [hC, Set.mem_setOf_eq, Set.mem_image]
      exact ⟨fun ⟨w, y, hv⟩ => ⟨_, ⟨w, y, rfl⟩, hv.symm⟩, fun ⟨_, ⟨w, y, rfl⟩, hv⟩ => ⟨w, y, hv.symm⟩⟩
    rw [hS]
    have hd : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
      Submodule.dense_iff_topologicalClosure_eq_top.2 hspan
    refine Submodule.dense_iff_topologicalClosure_eq_top.1 ?_
    have e2 : (Submodule.span ℂ ((A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y}) : Set H') =
        (A.toLinearEquiv : H →ₗ[ℂ] H') '' (Submodule.span ℂ {v | ∃ w y, v = T w y} : Set H) := by
      rw [Submodule.span_image, Submodule.map_coe]
    have e3 : (A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y} = A '' {v | ∃ w y, v = T w y} := rfl
    rw [← e3, e2]
    exact A.surjective.denseRange.dense_image A.continuous hd

theorem not_isIntegralOp_zero {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    {ν : Measure G} {σ : Representation ℂ G W} {F : G → ℂ} {c : ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ F c) (hc : c ≠ 0) : ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ F 0 := by
  intro h0
  obtain ⟨A, hA, -, rfl⟩ := h
  obtain rfl := hA.unique h0
  refine hc ?_
  have e : (LinearMap.restrict (0 : W →ₗ[ℂ] W) (p := LinearMap.range (0 : W →ₗ[ℂ] W))
      (q := LinearMap.range (0 : W →ₗ[ℂ] W)) fun v _ => LinearMap.mem_range_self _ v) = 0 :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [e, map_zero]

theorem specTrace : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → SpecTrace := by
  intro hDSC _ _ _ hFlath hChar hCO hPCT hPCS
  intro D V lam S M T U μa μf μ _ _ fa ff hTD ν hν n Ws _ _ σs hIrr hcover c hc
  have hcusp := GlobalTheory.T.discrete_series_multiplicity hCO hPCT D V lam S M T U μa μf μ fa ff hTD
  have hpone := GlobalTheory.T.discrete_series_model_trace_terms hDSC hFlath hChar hPCS D V lam S M T U μa μf μ fa ff hTD ν hν
  refine ⟨hcusp.traceClass, ?_⟩
  refine GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching (UDual (GA D V)) n (fun x => (mCusp V μ x.rep.π).toNat)
    (fun x => repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) (fun i => (mCuspDS μ (σs i) M).toNat) c
    (fun x i => IsCopyFinDS (σs i) M x.rep.π ⊤) _ hcusp.hasSum_trace ?_ ?_ ?_ ?_ ?_
  ·
    intro x hm ht
    have hm' : mCusp V μ x.rep.π ≠ 0 := fun h => hm (by rw [h]; simp)
    have htr : HasTrace (repOp x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff))
        (repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) := ⟨hcusp.traceClass_rep x hm', rfl⟩
    obtain ⟨W, _, _, σ, hσi, hσa, hcopy, hσt⟩ := hpone x.rep.H x.rep.π x.rep.isIrr _ htr ht
    have hmσ : mCuspDS μ σ M ≠ 0 := by
      rwa [← GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr W σ hσi hσa hcopy]
    obtain ⟨i, ⟨f⟩⟩ := hcover W σ hσi hσa hmσ (not_isIntegralOp_zero hσt ht)
    exact ⟨i, isCopyFinDS_of_equiv f hcopy⟩
  ·
    intro i hi
    have hi' : mCuspDS μ (σs i) M ≠ 0 := fun h => hi (by rw [h]; simp)
    obtain ⟨H, _, _, π, hπ, hcopy⟩ := GlobalTheory.T.exists_irreducibleUnitary_completion_finiteTimesDS D V S M μ (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi'
    let R : IrrU (GA D V) := ⟨H, π, hπ⟩
    refine ⟨R.cl, isCopyFinDS_of_uEquiv ?_ hcopy⟩
    exact (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).symm
  ·
    intro x i hR
    refine ⟨?_, ?_⟩
    · rw [GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hR]
    · exact (GlobalTheory.T.test_data_haar_factorization D V lam S M T U μa μf μ fa ff hTD ν hν x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i)
        (hIrr.1 i) (hIrr.2.1 i) hR (c i) (hc i)).2
  ·
    intro x i j hi hj
    by_contra hne
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi
      x.rep.H x.rep.π x.rep.isIrr (Ws j) (σs j) (hIrr.1 j) (hIrr.2.1 j) hj).1 (UEquiv.refl _)
    exact (hIrr.2.2 i j hne).false e.some
  ·
    intro x y i hx hy
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hx
      y.rep.H y.rep.π y.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hy).2 ⟨Representation.Equiv.refl _⟩
    rw [← UDual.cl_rep x, ← UDual.cl_rep y]
    exact IrrU.cl_eq_iff.2 e

end GlobalTheory.SpecTraceProof

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

namespace GlobalTheory.BirigidLift

theorem pull_one_prod_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) [IsMonHom u₀] [IsMonHom u], u₀.left ≫ i = i ≫ u.left →
    ∀ (P₀ Q₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → LBIso Q₀ (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left) →
    ∀ (P Q : LB (A ⊗ A).left), P.IsLB → Q.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso Q (P.pull (lift (fst A A) (snd A A ≫ u)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL u₀ u _ _ hu P₀ Q₀ hP₀ hQ₀ eQ₀ P Q hP hQ
    p₁ p₂ q₁ q₂ eP eQ
  set m : (A ⊗ A).left ⟶ (A ⊗ A).left := (lift (fst A A) (snd A A ≫ u)).left with hm
  set m₀ : (A₀ ⊗ A₀).left ⟶ (A₀ ⊗ A₀).left := (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left with hm₀
  have hP' : (P.pull m).IsLB := pull_isLB hP m
  have hev : ∀ (a : A ⟶ A) (t : A ⟶ A), evc hP' a t = evc hP a (t ≫ u) := fun a t ↦ by
    have := evc_ev hP (fst A A) (snd A A ≫ u) hP' a t
    rw [this, lift_fst, lift_snd_assoc]
  have z₁ : evc hP (1 : A ⟶ A) (𝟙 A) = 0 := (triv_ev_iff hP _ _).1 p₁
  have z₂ : evc hP (𝟙 A) (1 : A ⟶ A) = 0 := (triv_ev_iff hP _ _).1 p₂
  have h₁' : Triv (ev (P.pull m) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hP', hev, Category.id_comp]
    have := pull_evc hP u (1 : A ⟶ A) (𝟙 A)
    rw [z₁, map_zero, Category.comp_id, MonObj.comp_one] at this
    exact this.symm
  have h₂' : Triv (ev (P.pull m) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hP', hev, MonObj.one_comp]
    exact z₂
  have sq : l ≫ m = m₀ ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_fst, hl.1, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_snd, hl.2, lift_left_snd_assoc, Over.comp_left,
        Over.comp_left, ← Category.assoc, hl.2, Category.assoc, Category.assoc, hu]
  have e' : LBIso ((P.pull m).pull l) Q₀ := by
    refine (cls_eq_iff (pull_isLB hP' l) hQ₀).1 ?_
    rw [cls_pull hP' l, cls_pull hP m, ← pull_comp, sq, pull_comp, ← cls_pull hP l (pull_isLB hP l),
      (cls_eq_iff (pull_isLB hP l) hP₀).2 eP, ← cls_pull hP₀ m₀ (pull_isLB hP₀ m₀),
      (cls_eq_iff hQ₀ (pull_isLB hP₀ m₀)).2 eQ₀]
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h hl.1 hl.2 hL aL hL aL hQ₀ hQ q₁ q₂ eQ hP' h₁' h₂' e'

end GlobalTheory.BirigidLift
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.BirigidLift

theorem symm_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) →
      HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso (P.pull l) P₀ →
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL P₀ hP₀ hsym P hP h₁ h₂ e
  obtain ⟨l₁, l₂⟩ := hl
  have hs : (P.pull (lift (snd A A) (fst A A)).left).IsLB := pull_isLB hP _
  have h₁' : Triv (ev (swap P) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₂
  have h₂' : Triv (ev (swap P) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₁
  have sq : l ≫ (lift (snd A A) (fst A A)).left = (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₂, l₁, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₁, l₂, lift_left_snd_assoc]
  have hl0 := pull_isLB hP l
  have e' : LBIso ((swap P).pull l) P₀ := by
    refine (cls_eq_iff (pull_isLB hs l) hP₀).1 ?_
    rw [cls_pull hs l, cls_pull hP, ← pull_comp, sq, pull_comp, ← cls_pull hP l hl0,
      (cls_eq_iff hl0 hP₀).2 e, ← cls_pull hP₀ _ (pull_isLB hP₀ _)]
    exact ((cls_eq_iff hP₀ (pull_isLB hP₀ _)).2 hsym).symm
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h l₁ l₂ hL aL hL aL hP₀ hP h₁ h₂ e hs h₁' h₂' e'

end GlobalTheory.BirigidLift
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.SmoothLift

theorem isIso_spMap_mk_bot (R : Type) [CommRing R] : IsIso (spMap (Ideal.Quotient.mk (⊥ : Ideal R))) := by
  let e : R ≃+* R ⧸ (⊥ : Ideal R) := RingEquiv.ofBijective (Ideal.Quotient.mk ⊥)
    ⟨fun a b h ↦ by simpa [sub_eq_zero] using Ideal.Quotient.eq.1 h, Ideal.Quotient.mk_surjective⟩
  have : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  exact this

def ofSmooth (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (hs : Smooth s) (hsep : IsSeparated s)
    (hqc : QuasiCompact s) : Data where
  R := R
  I := ⊥
  κ := dp0 R
  nil := isDPNilpotent_bot R
  X := X
  X₀ := X
  s := s
  t := s
  i := 𝟙 X
  smooth := hs
  sep := hsep
  qc := hqc
  red := by
    haveI := isIso_spMap_mk_bot R
    refine ⟨s ≫ inv (spMap (Ideal.Quotient.mk (⊥ : Ideal R))), ?_, by simp⟩
    exact IsPullback.of_horiz_isIso ⟨by simp⟩

end GlobalTheory.SmoothLift

namespace GlobalTheory.CechDR

open GlobalTheory.SmoothLift

theorem cechDeRham_comparison_bijective_cup_smooth (hP : GlobalTheory.Published.CrystallineSmoothLift) : ∀ (R : Type) [CommRing R] (X : Scheme.{0})
    (s : X ⟶ Sp R), Smooth s → IsSeparated s → QuasiCompact s → Function.Bijective (cmp1 s) ∧
    ∃ e : SecondDeRham s ≃ₗ[R] HH2 s, ∀ a b : FirstDeRham s, e (cup _ a b) = cupHH s (cmp1 s a) (cmp1 s b) := by
  intro R _ X s hs hsep hqc
  obtain ⟨e₁, e₂, hcup, hcmp, -⟩ := hP
  let D := ofSmooth R X s hs hsep hqc
  have key : ∀ c : FirstDeRham s, e₁ D c = cmp1 s c := fun c ↦ by
    have h1 := hcmp D (IsMor.id (dp0 R) s) c
    have h2 : (IsMor.id (dp0 R) s).pull1 c = c := IsMor.pullCohomologyOne_id _ c
    exact (congrArg (e₁ D) h2).symm.trans h1
  refine ⟨?_, e₂ D, fun a b ↦ ?_⟩
  · have hf : (cmp1 s : FirstDeRham s → HH1 s) = e₁ D := funext fun c ↦ (key c).symm
    rw [hf]; exact (e₁ D).bijective
  · rw [← key, ← key]; exact hcup D a b

end GlobalTheory.CechDR
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_unitaryKernel_le_exp_pow_eight : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) := by
  first | exact @GlobalTheory.KernelIntegral.lintegral_kaF_le | exact GlobalTheory.KernelIntegral.lintegral_kaF_le | (intros; apply GlobalTheory.KernelIntegral.lintegral_kaF_le <;> assumption)
end
