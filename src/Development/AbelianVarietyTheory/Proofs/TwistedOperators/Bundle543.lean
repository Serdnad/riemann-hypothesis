module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle478
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle492
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle525
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle527
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeEqAtMulSplitSupported
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle278
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle529
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKEigen

theorem isGKSub_iSup_eigen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ C : Finset (D.what₂.Tau × ℕ → ℂ), GlobalTheory.CuspGK.IsGKSub θ M (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) := by
  intro D θ V S M hθ ψ hψ C
  have hG : GlobalTheory.CuspGK.IsGKSub θ M (GlobalTheory.CuspGK.gkGen θ M ψ) := by
    constructor
    · intro τ g hg f hf
      exact Submodule.mem_sInf.2 fun A hA => hA.2.k τ g hg f (Submodule.mem_sInf.1 hf A hA)
    · intro τ X hX f hf
      exact Submodule.mem_sInf.2 fun A hA => hA.2.lie τ X hX f (Submodule.mem_sInf.1 hf A hA)
  have hsm : ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth
  set T : Set (GA D V → ℂ) := ⋃ c ∈ C,
    {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h} with hTdef
  have hspan : (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) =
      Submodule.span ℂ T := by
    rw [hTdef, Submodule.span_iUnion₂]
  rw [hspan]
  have hTG : T ⊆ GlobalTheory.CuspGK.gkGen θ M ψ := by
    intro h hh
    rw [hTdef, Set.mem_iUnion₂] at hh
    obtain ⟨c, _, hh, _⟩ := hh
    exact hh
  have hSG : Submodule.span ℂ T ≤ GlobalTheory.CuspGK.gkGen θ M ψ := Submodule.span_le.2 hTG
  have hTk : ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ h ∈ T, rTr V (atTau θ V τ g) h ∈ T := by
    intro τ g hg h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.k τ g hg h hhG, fun i => ?_⟩
    rw [GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ i.1 i.2 (hsm h hhG), he i]
    rfl
  have hTl : ∀ τ, ∀ X ∈ lieAt V τ, ∀ h ∈ T, Rder θ V τ X h ∈ T := by
    intro τ X hX h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.lie τ X hX h hhG, fun i => ?_⟩
    rw [GlobalTheory.CuspLie.gelf_Rder hθ hX (hsm h hhG) i.1 i.2, he i, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTk τ g hg x hx)
    | zero => exact (Submodule.span ℂ T).zero_mem
    | add x y _ _ hx hy => exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx => exact (Submodule.span ℂ T).smul_mem a hx
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTl τ X hX x hx)
    | zero =>
      rw [Formalism.IndefR.Mult.rder_zero θ V τ X]
      exact (Submodule.span ℂ T).zero_mem
    | add x y hx' hy' hx hy =>
      rw [GlobalTheory.Mem.AutSpace.Rder_add (hsm x (hSG hx')) (hsm y (hSG hy')) hX]
      exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx =>
      rw [GlobalTheory.Mem.AutSpace.Rder_smul]
      exact (Submodule.span ℂ T).smul_mem a hx

end GlobalTheory.GKEigen

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical


theorem _root_.GlobalTheory.T.kFiniteDecomposition_assemble_realPlaces : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @GlobalTheory.KFinDecomp.assemble_places | exact GlobalTheory.KFinDecomp.assemble_places | (intros; apply GlobalTheory.KFinDecomp.assemble_places <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size


theorem _root_.GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.Size.RapidDecSm θ N.V φ → ∀ (l : List D.what₂.Tau), l.Nodup → ∀ (d : ℕ) (η : ℝ), 0 < η → ∃ e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ, (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) ∧ GlobalTheory.Size.growthSob θ N.V d 0 (φ - GlobalTheory.CuspApproxAll.avgList θ N e l φ) ≤ ENNReal.ofReal η := by
  first | exact @GlobalTheory.KAvgApprox.approx_avgList | exact GlobalTheory.KAvgApprox.approx_avgList | (intros; apply GlobalTheory.KAvgApprox.approx_avgList <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.exists_rational_split_stabilizer_decomposition : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  first | exact @GlobalTheory.RatSplitLat.exists_rat_split_lat | exact GlobalTheory.RatSplitLat.exists_rat_split_lat | (intros; apply GlobalTheory.RatSplitLat.exists_rat_split_lat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.mem_splitPlaceFinitePointsOffPrimes_of_supported : ∀ {D : D7} (V : HSp D) (Q : Finset ℕ) (s : GfC V),
    GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (∏ q ∈ Q, q) (finHom V s.1).1 → s ∈ GlobalTheory.MovedKappaEx.splitOff V Q := by
  first | exact @GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit | exact GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit | (intros; apply GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.vertexLattice_eqAt_mul_splitSupported : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ (q : ℕ), q.Prime → ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e →
    GlobalTheory.MovedKappaEx.OffPrime e q → ∀ g y : FinPt G X, SuppAt e (G.V X) g.1 →
    EqAt D q (GlobalTheory.SumSize.latAt S X (g * y)) (GlobalTheory.SumSize.latAt S X y) := by
  first | exact @GlobalTheory.MovedSplitEq.eqAt_latAt_mul | exact GlobalTheory.MovedSplitEq.eqAt_latAt_mul | (intros; apply GlobalTheory.MovedSplitEq.eqAt_latAt_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

namespace GlobalTheory.RatMoveJets

theorem exists_unitary_ratCoord {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (r : FinPt G X) (hr : GlobalTheory.MovedKappaEx.RatFin (G.V X) r) :
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  obtain ⟨γ, hγ, hf⟩ := hr
  obtain ⟨γ', h1, h2⟩ := id hγ
  have hG : star γ'.1 * (G.V X).gram * γ'.1 = (G.V X).gram := h1
  have hmt : Formalism.L2.Theta.mt (G.V X) γ = γ'.1.map (incA D) := congrArg Units.val h2.symm
  set F := (S.N.fr X).1 with hFdef
  set Fi := ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1 with hFidef
  have hF : star F * (G.V X).gram * F = 1 := S.N.fr_on X hX
  have e1 : Fi * F = 1 := by rw [hFdef, hFidef]; exact Units.inv_mul _
  have e2 : F * Fi = 1 := by rw [hFdef, hFidef]; exact Units.mul_inv _
  have hGram : star Fi * Fi = (G.V X).gram := by
    have : star Fi * (star F * (G.V X).gram * F) * Fi = (G.V X).gram := by
      calc star Fi * (star F * (G.V X).gram * F) * Fi = star (F * Fi) * (G.V X).gram * (F * Fi) := by
            rw [star_mul]; simp only [Matrix.mul_assoc]
        _ = (G.V X).gram := by rw [e2, star_one, Matrix.one_mul, Matrix.mul_one]
    rw [hF, Matrix.mul_one] at this
    exact this
  have hU : star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = 1 := by
    calc star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = star F * (star γ'.1 * (star Fi * Fi) * γ'.1) * F := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hGram, hG]; exact hF
  refine ⟨⟨Fi * γ'.1 * F, Matrix.mem_unitaryGroup_iff'.2 hU⟩, γ, hγ, hf, ?_⟩
  rw [hmt]
  congr 1
  change γ'.1 = F * (Fi * γ'.1 * F) * Fi
  simp only [← Matrix.mul_assoc, e2, Matrix.one_mul]
  rw [Matrix.mul_assoc, e2, Matrix.mul_one]

end GlobalTheory.RatMoveJets
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

noncomputable section
namespace GlobalTheory.RatMoveLat
open Matrix

theorem mem_globLat_rat {D : D7} {n : ℕ} (a g : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (M : Matrix (Fin n) (Fin n) D.host.E)
    (ha : a.1 = M.map (Formalism.IndefR.Datum.eToEAf D)) (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Fin n → D.host.E) :
    M *ᵥ y ∈ Formalism.UG.CS.globLat (a * g) C ↔ y ∈ Formalism.UG.CS.globLat g C := by
  have hv : (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) =
      (a : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ fun i => Formalism.IndefR.Datum.eToEAf D (y i) := by
    funext i
    rw [ha]
    exact RingHom.map_mulVec _ _ _ _
  have hw : (((a * g)⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ
        (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) =
      ((g⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ
        fun i => Formalism.IndefR.Datum.eToEAf D (y i) := by
    rw [hv, Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  unfold Formalism.UG.CS.globLat
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  have he : Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) = Formalism.IndefR.Datum.eToEAf D := rfl
  rw [he, hw]

theorem finG_rat {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) (h : GlobalTheory.RatMoveJets.RatCoord V fr g U) :
    (GlobalTheory.FunObj.finG V g).1 = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (Formalism.IndefR.Datum.eToEAf D) := by
  obtain ⟨γ, -, hfin, hmt⟩ := h
  have key : ∀ e : D.host.E, Formalism.IndefR.Lev.swapAE D
      ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (incA D e)) =
      Formalism.IndefR.Datum.eToEAf D e := by
    intro e
    simp [Formalism.IndefR.Lev.swapAE, Formalism.IndefR.Datum.eToEAf, Formalism.L2.Theta.incA, inclR]
  unfold GlobalTheory.FunObj.finG Formalism.IndefR.Lev.finE
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← hfin]
  have hm : ((Formalism.L2.Theta.matHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) =
      (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D) := hmt
  unfold Formalism.L2.Theta.finHom
  simp only [Formalism.UG.bc, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, hm,
    Matrix.map_map]
  ext i j
  exact key _

theorem latAt_rat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E),
    GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U → ∀ x : FinPt G X,
      GlobalTheory.SumSize.latAt S X (r * x) = SDLat.smulLat U.1 (GlobalTheory.SumSize.latAt S X x) := by
  intro D T L sc G W S X r U hr x
  have hfr := finG_rat _ _ _ _ hr
  have hU : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hmv : ∀ v : Fin (G.V X).rank → D.host.E,
      ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1) *ᵥ ((S.N.fr X).1 *ᵥ v) =
        (S.N.fr X).1 *ᵥ (U.1 *ᵥ v) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hzz : ∀ z : Fin (G.V X).rank → D.host.E, U.1 *ᵥ (star U.1 *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  ext z
  simp only [GlobalTheory.SumSize.latAt, SDLat.smulLat, Submodule.mem_map, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.toLin'_apply, map_mul]
  constructor
  · intro hz
    refine ⟨star U.1 *ᵥ z, ?_, ?_⟩
    · rw [← mem_globLat_rat _ _ _ hfr, hmv, hzz]
      exact hz
    · exact hzz z
  · rintro ⟨w, hw, rfl⟩
    rw [← hmv, mem_globLat_rat _ _ _ hfr]
    exact hw

end GlobalTheory.RatMoveLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

theorem _root_.GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau)
    (u : Matrix (Fin B.rank) (Fin B.rank) ℂ), u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (e.map (tauE D τ)) →
    atTau θ B τ u ∈ NFlag B e := by
  first | exact @GlobalTheory.FlagRealUnip.atTau_mem_NFlag | exact GlobalTheory.FlagRealUnip.atTau_mem_NFlag | (intros; apply GlobalTheory.FlagRealUnip.atTau_mem_NFlag <;> assumption)
end

section

namespace GlobalTheory.Published

theorem cuspTraceClass_of_factorisation : DixmierMalliavinFactorisation → CuspTraceClass :=
  fun h => cuspTraceClass_of_decay GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay h

end GlobalTheory.Published
end

section


theorem _root_.GlobalTheory.T.geometricLemma_cell_semisimplification_GL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  first | exact @GlobalTheory.SmGL.CellSemis.cellSemisimplification | exact GlobalTheory.SmGL.CellSemis.cellSemisimplification | (intros; apply GlobalTheory.SmGL.CellSemis.cellSemisimplification <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory

theorem zelevinskyPolynomialRing_of_parts :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  intro hBZ hSeg hRing k _ _ _ _
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.zelevinskySegmentClass_exists_for_every_placing hSeg k
  obtain ⟨Ψ, h1, hmul, hX⟩ := hRing k Z hZ
  refine ⟨Z, Ψ, hZ, ⟨h1, fun r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ => ?_⟩, hX⟩
  have h := GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k r t V W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h, hmul r t V W π₁ π₂ h₁ h₂ s₁ s₂ h⟩

end GlobalTheory
end
