module

public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTsumOfFactor
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle353
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IsotypicTrace

open ContinuousLinearMap

variable {G X H : Type} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {π : G →* (H →L[ℂ] H)}

theorem exists_homIn_ne_zero (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π) {U : Submodule ℂ H}
    (hU : IsSubrep π U) (h0 : U ≠ ⊥) : ∃ S ∈ homIn δ π U, S ≠ 0 := by
  have := hU.completeSpace
  by_contra hn
  push_neg at hn
  apply h0
  have hle : isoPart δ π ⊤ ≤ Uᗮ := isoPart_le U.isClosed_orthogonal fun T hT x => by
    have hS : U.starProjection ∘L T ∈ homIn δ π U :=
      ⟨fun x => U.starProjection_apply_mem _, fun g x => by
        simp only [comp_apply, hT.2 g x, hU.starProjection_apply hπ]⟩
    have := DFunLike.congr_fun (hn _ hS) x
    rw [comp_apply, zero_apply] at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).1 this
  rw [hiso, top_le_iff, Submodule.orthogonal_eq_top_iff] at hle
  exact hle

theorem exists_isCopy_le (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π)
    {U : Submodule ℂ H} (hU : IsSubrep π U) (h0 : U ≠ ⊥) : ∃ W ≤ U, IsCopy δ π W := by
  obtain ⟨S, hS, hS0⟩ := exists_homIn_ne_zero hπ hiso hU h0
  exact ⟨_, by rintro _ ⟨x, rfl⟩; exact hS.1 x, isCopy_range hδ hπ hS hS0⟩

theorem isCopy_of_isIrredSubrep (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π)
    {W : Submodule ℂ H} (hW : IsIrredSubrep π W) : IsCopy δ π W := by
  obtain ⟨V, hVW, hV⟩ := exists_isCopy_le hδ hπ hiso hW.1 hW.2.1
  have hV' := hV.isIrredSubrep hδ.irred
  rcases hW.2.2 V hVW hV'.1 with h | h
  · exact absurd h hV'.2.1
  · exact h ▸ hV

theorem exists_hilbertBasis (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π) :
    ∃ (ι : Type) (e : ι → (X →ₗᵢ[ℂ] H)) (b : HilbertBasis (Σ _ : ι, GlobalTheory.OpTrace.stdIndex X) ℂ H),
      (∀ i g x, e i (δ g x) = π g (e i x)) ∧ ∀ p, b p = e p.1 (GlobalTheory.OpTrace.stdBasis (H := X) p.2) := by
  obtain ⟨ι, W, hW, hs⟩ := GlobalTheory.DiscreteSum.exists_isHilbertSum hπ fun U hU h0 => by
    obtain ⟨V, hV, hc⟩ := exists_isCopy_le hδ hπ hiso hU h0
    exact ⟨V, hV, hc.isIrredSubrep hδ.irred⟩
  choose e he hr using fun i => isCopy_iff.1 (isCopy_of_isIrredSubrep hδ hπ hiso (hW i))
  have hmem : ∀ i x, e i x ∈ W i := fun i x => hr i ▸ ⟨x, rfl⟩
  let v : (Σ _ : ι, GlobalTheory.OpTrace.stdIndex X) → H := fun p => e p.1 (GlobalTheory.OpTrace.stdBasis (H := X) p.2)
  have hon : Orthonormal ℂ v := by
    refine ⟨fun p => by simp [v, (GlobalTheory.OpTrace.stdBasis (H := X)).orthonormal.1], fun p q hpq => ?_⟩
    obtain ⟨i, a⟩ := p
    obtain ⟨j, c⟩ := q
    by_cases hij : i = j
    · subst hij
      have hac : a ≠ c := fun h => hpq (by rw [h])
      simp only [v, LinearIsometry.inner_map_map]
      exact (GlobalTheory.OpTrace.stdBasis (H := X)).orthonormal.2 hac
    · exact hs.OrthogonalFamily hij ⟨_, hmem i _⟩ ⟨_, hmem j _⟩
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    refine GlobalTheory.DiscreteSum.eq_zero_of_isHilbertSum hs fun i y hy => ?_
    obtain ⟨z, rfl⟩ : y ∈ LinearMap.range (e i).toLinearMap := (hr i).symm ▸ hy
    have h1 : ∀ a, ⟪GlobalTheory.OpTrace.stdBasis (H := X) a, adjoint (e i).toContinuousLinearMap x⟫_ℂ = 0 := fun a => by
      rw [adjoint_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self (f := v) ⟨i, a⟩)) hx
    have h2 : adjoint (e i).toContinuousLinearMap x = 0 := by
      have := (GlobalTheory.OpTrace.stdBasis (H := X)).hasSum_repr (adjoint (e i).toContinuousLinearMap x)
      simp only [HilbertBasis.repr_apply_apply, h1, zero_smul] at this
      exact (hasSum_zero.unique this).symm
    change ⟪(e i).toContinuousLinearMap z, x⟫_ℂ = 0
    rw [← adjoint_inner_right, h2, inner_zero_right]
  exact ⟨ι, e, HilbertBasis.mkOfOrthogonalEqBot hon hsp, he, fun p => by simp [v]⟩

end GlobalTheory.IsotypicTrace

noncomputable section

namespace GlobalTheory.IsotypicTrace

open ContinuousLinearMap MeasureTheory

variable {G X H : Type} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {π : G →* (H →L[ℂ] H)}

theorem hasSum_copy [MeasurableSpace G] {μ : Measure G} {f : G → ℂ} (hδ : IsIrrUnitary δ)
    (hπ : IsUnitaryRep π) (hR : IsRepOp π μ f (repOp π μ f)) (e : X →ₗᵢ[ℂ] H)
    (he : ∀ g x, e (δ g x) = π g (e x)) (Q : H →L[ℂ] H) (hQ : ∀ g, Q * π g = π g * Q)
    (htr : trace (repOp δ μ f) = 0) (hA : IsTraceClass (repOp π μ f * Q)) :
    HasSum (fun a => ⟪e (stdBasis (H := X) a), (repOp π μ f * Q) (e (stdBasis (H := X) a))⟫_ℂ) 0 := by
  let E : X →L[ℂ] H := e.toContinuousLinearMap
  have he' : ∀ g x, E (δ g x) = π g (E x) := he
  have hEE : ∀ x, adjoint E (E x) = x := fun x => ext_inner_left ℂ fun y => by
    rw [adjoint_inner_right]
    exact e.inner_map_map y x
  have hEa : ∀ g y, adjoint E (π g y) = δ g (adjoint E y) := fun g y =>
    (GlobalTheory.DiscreteSum.adjoint_mem_homIn hδ.unitary hπ (T := E) (mem_homIn_top.2 he')).2 g y
  have hRδ' : IsRepOp δ μ f (adjoint E ∘L repOp π μ f ∘L E) := fun x => by
    have hk : ∀ g, f g • δ g x = adjoint E (f g • π g (E x)) := fun g => by
      rw [map_smul, hEa, hEE]
    simp only [hk]
    refine ⟨(adjoint E).integrable_comp (hR (E x)).1, ?_⟩
    rw [comp_apply, comp_apply, (hR (E x)).2, (adjoint E).integral_comp_comm (hR (E x)).1]
  have hRδ : IsRepOp δ μ f (repOp δ μ f) := by rw [hRδ'.repOp_eq]; exact hRδ'
  have hcomm : ∀ y, adjoint E (repOp π μ f y) = repOp δ μ f (adjoint E y) := fun y => by
    rw [(hR y).2, ← (adjoint E).integral_comp_comm (hR y).1, (hRδ (adjoint E y)).2]
    simp only [map_smul, hEa]
  have hQ' : ∀ g y, Q (π g y) = π g (Q y) := fun g y => DFunLike.congr_fun (hQ g) y
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur X G δ hδ.unitary.norm_apply (fun S hS h => hδ.irred.2 S ⟨hS, h⟩)
    (adjoint E ∘L Q ∘L E) fun g => by
      ext x
      change δ g (adjoint E (Q (E x))) = adjoint E (Q (E (δ g x)))
      rw [he', hQ', hEa]
  have hP : adjoint E ∘L (repOp π μ f * Q) ∘L E = c • repOp δ μ f := by
    ext x
    have hx : adjoint E (Q (E x)) = c • x := DFunLike.congr_fun hc x
    change adjoint E (repOp π μ f (Q (E x))) = c • repOp δ μ f x
    rw [hcomm, hx, map_smul]
  have htr' : trace (adjoint E ∘L (repOp π μ f * Q) ∘L E) = 0 := by
    rw [hP, trace_smul, htr, mul_zero]
  have h := (hA.comp_comp (adjoint E) E).hasSum_trace (stdBasis (H := X))
  rw [htr'] at h
  refine h.congr_fun fun a => ?_
  change _ = ⟪stdBasis (H := X) a, adjoint E ((repOp π μ f * Q) (E (stdBasis (H := X) a)))⟫_ℂ
  rw [adjoint_inner_right]
  rfl

end GlobalTheory.IsotypicTrace

namespace GlobalTheory

theorem trace_repOp_mul_eq_zero_of_isIsotypic : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ), Integrable f μ → ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (δ : G →* (X →L[ℂ] X)) (π : G →* (H →L[ℂ] H)), IsIrrUnitary δ → IsUnitaryRep π → GlobalTheory.AutMult.IsIsotypic δ π → ∀ [SecondCountableTopology G] (Q : H →L[ℂ] H), (∀ g, Q * π g = π g * Q) → HasTrace (repOp δ μ f) 0 → IsTraceClass (repOp π μ f * Q) → trace (repOp π μ f * Q) = 0 := by
  intro G _ _ _ _ _ μ f hf X _ _ _ H _ _ _ δ π hδ hπ hiso _ Q hQ htr hA
  by_cases hex : ∃ T, IsRepOp π μ f T
  swap
  · have h0 : repOp π μ f = 0 := by rw [repOp, dite_eq_right hex]
    rw [h0, zero_mul, trace_zero]
  have hR : IsRepOp π μ f (repOp π μ f) := by
    obtain ⟨T, hT⟩ := hex
    rw [hT.repOp_eq]; exact hT
  obtain ⟨ι, e, b, he, hb⟩ := IsotypicTrace.exists_hilbertBasis hδ hπ hiso
  have h1 := hA.hasSum_trace b
  have h2 : ∀ i, HasSum (fun a => ⟪b ⟨i, a⟩, (repOp π μ f * Q) (b ⟨i, a⟩)⟫_ℂ) 0 := fun i => by
    simpa only [hb] using IsotypicTrace.hasSum_copy hδ hπ hR (e i) (he i) Q hQ htr.2 hA
  exact (hasSum_zero.unique (h1.sigma h2)).symm

end GlobalTheory
end
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace

open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.UnitCoefIP

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem exists_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ C : ℂ, ∀ y₁ ∈ GlobalTheory.LiftLower.partH R i σ ev, ∀ (y₂ : (R.HW i σ).H) (w : c.W), ‖w‖ = 1 →
    GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e y₂ fun ρ => v ρ)) = C * inner ℂ y₁ y₂ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _hirr _hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν _hy _hH v hv ev
  have hC := hd.1
  obtain ⟨⟨μ, 𝓧⟩, hμ⟩ := hd.2.2.2.2.2.2.2.1.1.2.norm.1
  obtain ⟨⟨Fr, hFr⟩, hFr2⟩ := (hC.models.νW i).1.2.2 R.θ hC.models.inf
  obtain ⟨mR, hmR⟩ := (hFr2 Fr hFr).1
  choose δ _hδpos hδ' using hδ i σ
  have hδv : ∀ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) = δ ρ :=
    fun ρ => (hδ' ρ Fr hFr (mR ρ) (hmR ρ) (v ρ) (hv ρ)).2
  have hW := GlobalTheory.LiftScalarL.inner_HW R hC.models.HW i σ
  set N : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : 0 < N := Finset.prod_pos fun ρ _ => by
      have := one_le_dimK i σ ρ
      positivity
    exact_mod_cast this.ne'
  by_cases h0 : typePart R i σ A.μ0 R.triv ev = ⊥
  · refine ⟨0, fun y₁ hy₁ y₂ w _ => ?_⟩
    have e1 : y₁ = 0 := by
      rw [← GlobalTheory.LiftLower.typePart_base hC.lev, h0] at hy₁
      exact (Submodule.mem_bot ℂ).1 hy₁
    subst e1
    simp [l2, Lift.pet, upLift, petW]
  · obtain ⟨Bf, -, -, -, hK⟩ := hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ ev h0
    refine ⟨(((R.νV i A.μ0) (R.fdV i A.μ0)).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, (δ ρ : ℂ)) *
      ((Nat.card R.triv.H : ℂ) * (Datum.nrm2 μ 𝓧 f : ℂ) *
        (GlobalTheory.LFun.LSD D (finS R A.μ0) Bf μ' ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R A.μ0) : ℂ)))) / N,
      fun y₁ hy₁ y₂ w hw => ?_⟩
    have hm : ∀ x, (R.HW i σ).e x ∈ R.Wall i σ := HMod_mem (hC.models.HW i σ)
    have hw' : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hy' : y₁ ∈ typePart R i σ A.μ0 R.triv ev := by
      rw [GlobalTheory.LiftLower.typePart_base hC.lev]; exact hy₁
    have hK1 := hK _ (Submodule.mem_comap.1 hy') _ (hm y₂)
    have hIP := isMultiplicityInner_of_model (R.HW i σ) hW y₁ y₂
    have key := GlobalTheory.LiftScalarL.l2_upwardLift R hI hFo hd hν hμ hFr hmR (hm y₁) (hm y₂) hIP _ hK1 v δ hδv w hw'
    refine key.trans ?_
    rw [hW y₁ y₂]
    field_simp

end GlobalTheory.UnitCoefIP

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem cmp_mul' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (a b : GA D V) :
    cmp θ τ (a * b) = cmp θ τ a * cmp θ τ b := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) (a * b) = infMat D.sp.cm.sig V.gram (θ τ) a * infMat D.sp.cm.sig V.gram (θ τ) b
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]

theorem cmp_one' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) : cmp θ τ (1 : GA D V) = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) 1 = 1
  rw [e, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem frConj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  change _ * _ * _ = _
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem rep_one' (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

theorem rep_mul'' (M : DSModel V S) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (frConj_mem M τ hg) _ (frConj_mem M τ hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

theorem rep_inner' (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (a b : M.H τ) : ⟪M.rep τ g a, M.rep τ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(M.rep τ g : M.H τ →ₗ[ℂ] M.H τ), fun v => (M.ds τ).2.2.1.2.1 _ (frConj_mem M τ hg) v⟩ :
    M.H τ →ₗᵢ[ℂ] M.H τ).inner_map_map a b

end GlobalTheory.PoinConj

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem poin_conj : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v₀ : ∀ τ, M.H τ) (g₀ : GA D V), g₀ ∈ GinfC V → ∀ c g : GA D V, poin θ M K v₀ (g₀⁻¹ * c) v₀ (g * g₀) = poin θ M K (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) c (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) g := by
  intro D θ hθ V S M K v₀ g₀ hg₀ c g
  unfold poin
  congr 1
  funext γ
  have ez : g₀⁻¹ * c * γ * (g * g₀) = g₀⁻¹ * (c * γ * g) * g₀ := by group
  rw [ez]
  set z := c * γ * g
  have h1 : Lev.finE V g₀ = 1 := by
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom V g₀ = 1 from hg₀, map_one]
  have hf : Lev.finE V (g₀⁻¹ * z * g₀) = Lev.finE V z := by
    rw [map_mul, map_mul, map_inv, h1, inv_one, one_mul, mul_one]
  unfold coef
  rw [hf]
  split_ifs with hK
  · unfold coefR
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hU : ∀ x : GA D V, cmp θ τ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun x => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ
    rw [cmp_mul', cmp_mul', rep_mul'' M τ (by rw [← cmp_mul']; exact hU _) (hU _),
      rep_mul'' M τ (hU _) (hU _), ← rep_inner' M τ (hU g₀), ← rep_mul'' M τ (hU g₀) (hU g₀⁻¹), ← cmp_mul',
      mul_inv_cancel, cmp_one', rep_one']
  · rfl

end GlobalTheory.PoinConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.OnePDecay

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hsn_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hsn A = ‖A‖ := by
  rw [hsn, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hsn (A * B) ≤ hsn A * hsn B := by
  rw [hsn_eq_norm, hsn_eq_norm, hsn_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn A := Real.sqrt_nonneg _

theorem continuous_hsn_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun s : ℝ => hsn (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold hsn
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_iff_continuousAt.2 fun t => (GlobalTheory.Mem.Lift.hasDerivAt_exp_entry X t i j).continuousAt).norm.pow 2

theorem decay_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤
        L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  intro D θ hθ V τ X hX N
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_hsn_exp X).continuousOn
  set m : ℝ := max 1 (max M (hsn (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hbound : ∀ τ' (s : ℝ), |s| ≤ 1 → hsn (cmp θ τ' (oneP θ V τ X s)) ≤ m := by
    intro τ' s hs
    have h := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s
    by_cases e : τ' = τ
    · subst e
      show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.1]
      have := hM s ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_of_le_right (le_max_left _ _)))
    · show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.2 τ' e]
      exact le_max_of_le_right (le_max_right _ _)
  have hkey : ∀ (x : GA D V) (t : ℝ) τ', |t| < 1 →
      1 + hsn (cmp θ τ' x) ≤ (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) * m := by
    intro x t τ' ht
    have hx : x = x * oneP θ V τ X t * oneP θ V τ X (-t) := by
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one]
    have h1 : hsn (cmp θ τ' x) ≤ hsn (cmp θ τ' (x * oneP θ V τ X t)) * m := by
      have e2 : cmp θ τ' x = cmp θ τ' (x * oneP θ V τ X t) * cmp θ τ' (oneP θ V τ X (-t)) := by
        show infMat _ _ (θ τ') x = infMat _ _ (θ τ') _ * infMat _ _ (θ τ') _
        rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, ← hx]
      rw [e2]
      exact (hsn_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (hbound τ' (-t) (by rw [abs_neg]; exact ht.le)) (hsn_nonneg' _))
    nlinarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]
  refine ⟨m ^ (N * Fintype.card D.what₂.Tau), by positivity, fun x t ht => ?_⟩
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun τ' _ => inv_nonneg.2 (pow_nonneg (by linarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]) N)) (fun τ' _ => ?_)
  have ha := hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))
  have hb := hsn_nonneg' (cmp θ τ' x)
  have hk := hkey x t τ' ht
  have hpa : 0 < (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N := pow_pos (by linarith) N
  have hpb : 0 < (1 + hsn (cmp θ τ' x)) ^ N := pow_pos (by linarith) N
  rw [← div_eq_mul_inv, le_div_iff₀ hpb, inv_mul_eq_div, ← div_pow]
  refine pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) ?_ N
  rw [div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.OnePDecay

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.Chain.LiftConv

theorem liftInteg_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.Chain.LiftInteg D :=
  fun hP D => liftInteg_of_growth hP D (GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms D)

end GlobalTheory.Chain.LiftConv
end
