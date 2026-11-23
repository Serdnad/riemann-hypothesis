module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle637
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle507
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModerat
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle481
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle638
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ v, vac v ≠ 0) → (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] (p : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] P) (Q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type)
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ i, ∀ v ∉ T, φ i v = vac v) → ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = 0 →
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) = 0 := by
  first | exact @GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | exact GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | (intros; apply GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.constantTermLift_isotropicSubspace : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by
  first | exact @GlobalTheory.TowerConstTermObj.towerConstTerm | exact GlobalTheory.TowerConstTermObj.towerConstTerm | (intros; apply GlobalTheory.TowerConstTermObj.towerConstTerm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainTw.ParInv

variable {D : D7}

theorem conjP_eq_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl', GlobalTheory.GridPlaces.under_conjP]

theorem absNorm_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (Formalism.DivisionValues.conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem conjPl_ne_of_isSplit (w : HeightOneSpectrum (𝓞 D.host.E))
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : Formalism.DivisionValues.conjPl w ≠ w := by
  rintro hc
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) R.asIdeal = (w.under (𝓞 D.host.F)).asIdeal → R = w := by
    intro R hR
    rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := R) (HeightOneSpectrum.ext hR) with h | h
    · exact h
    · rw [h, conjP_eq_conjPl', hc]
  exact hPQ ((key P hP).trans (key Q hQ).symm)

end GlobalTheory.ChainTw.ParInv

end


open GlobalTheory.ChainTw.ParInv in
theorem GlobalTheory.ChainTw.invFam_bounded : ∀ D : D7, ForStageQ D fun c _ j s => ∀ (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E), IsPar u (chainPar c B j) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (GlobalTheory.ChainNS.invFam B) D.R.r ((D.R.r : ℝ) / 2) := by
  intro D c tw htw j hj s hs u B hu hB
  classical
  obtain ⟨hr, -, hflat⟩ := hs
  have hsd : IsSelfDualC s.V s.Λ := hflat.selfDual
  obtain ⟨hu0, hpar⟩ := hu
  obtain ⟨v0, hv0⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (Subtype.ext (LinearMap.ext fun v => by simpa using h v))
  have hP := hpar v0 hv0
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram s.V
  have key : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hw
    have hd :=
      (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) hJ.2
        (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice s.V s.Λ hsd)).2 (fun y => hsd.2 y) (w.under (𝓞 D.host.F))
    have hx := hP (w.under (𝓞 D.host.F)) hv w rfl
    by_cases hc : Formalism.DivisionValues.conjPl w = w
    · rw [hc]
      rcases hx with ⟨hs, -⟩ | ⟨hin, -⟩
      · exact absurd hc (conjPl_ne_of_isSplit w hs)
      · exact (GlobalTheory.LFun.ConjPlace.map_inv_of_isParamVec hin (hP _ hv w rfl)).symm
    · have hx' := hP (w.under (𝓞 D.host.F)) hv (Formalism.DivisionValues.conjPl w) (under_conjPl w)
      exact GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd (Ne.symm hc) hx hx'
  intro w hw
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    show (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
    rw [under_conjPl]; exact hw
  have hB' : B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := GlobalTheory.T.firstMemberParameter_inv_of_chainParameter_inv D c htw.com j hj B w hw (key w hw)
  have e : GlobalTheory.ChainNS.invFam B w = B (Formalism.DivisionValues.conjPl w) := hB'.symm
  rw [e]
  have h2 := hB (Formalism.DivisionValues.conjPl w) hw'
  rwa [absNorm_conjPl'] at h2
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.exists_finiteSupport_mul_latticeStabilizer : ∀ {D : D7} (V : HSp D) (L : GlobalTheory.FinPl.Lat V), L.FG → Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : GA D V), ∃ (b' : GA D V) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b' = 1) ∧ GlobalTheory.FinPl.InK V L (fun v => v ∉ S) (b'⁻¹ * b) := by
  first | exact @GlobalTheory.TruncAway.exists_trunc_mul_inK | exact GlobalTheory.TruncAway.exists_trunc_mul_inK | (intros; apply GlobalTheory.TruncAway.exists_trunc_mul_inK <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)


theorem _root_.GlobalTheory.T.levelVector_squareNorm_eq_prod_localVolumes : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), P = LevelP.ofLocal Hl cl → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → nrm2 μ 𝓧 f = (∏ PP ∈ R.Pg.attach, (Nat.card (Hl PP) : ℝ) * ((Nat.card (kP PP.1) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
  first | exact @GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | exact GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | (intros; apply GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F := by
  first | exact @GlobalTheory.FinZeta.finiteZetaL | exact GlobalTheory.FinZeta.finiteZetaL | (intros; apply GlobalTheory.FinZeta.finiteZetaL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CosSupport

theorem isHalf_actO_one {D : D7} (S T : HSp D) (c : AE D) (h : GA D T) (y : WO S T) (hy : IsHalf c y) :
    IsHalf c (actO S T 1 h y) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hy k l]
  ring

theorem cosSupp : CosSupp := by
  classical
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ Φ hΦ m X hm g hg hne
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hw := W.om_is (.core i) (by show Node.InRange D.R.m (.core (i + 1)); simp [Node.InRange]; omega)
  have hth : IsThetaFunO W.ψ _ _ Φ := hΦ.1.1
  have hchar : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y)) := by
    intro y h1 h2 h3
    by_contra hne'
    exact hne (GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters D W.ψ _ _ _ _ (W.om (.core i)) hw m X hm Φ hth g y _ _ (hΦ.2 e he y h1 h2)
      (hΦ.2 e he _ (isHalf_actO_one _ _ _ _ y h1) h3) hne')
  have hloc := GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hchar
  refine GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent D (G.V (.core i)) (G.Λ (.core i)) (G.sp.P_is i (by omega)).sd G.pl.W0 e he G.modul ?_ g ?_ hloc
  · intro PP hPP
    have hprime : PP.asIdeal.IsPrime := PP.isPrime
    obtain ⟨v, hv, hle⟩ := hprime.prod_le.1 hPP
    have hle' : (G.pl.w v).asIdeal ≤ PP.asIdeal := hprime.le_of_pow_le hle
    have heq : G.pl.w v = PP := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hprime.ne_top hle')
    unfold Places.W0
    exact Finset.mem_image.2 ⟨v, hv, heq⟩
  · intro v hv
    apply hg v
    intro hvS
    exact hv _ (by unfold Places.W0; exact Finset.mem_image.2 ⟨v, hvS, rfl⟩) (G.pl.under_w hvS)

end GlobalTheory.CosSupport

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ c : GA D V, ∃ (C : ℝ) (A : ℕ), ∀ (g : GA D V) (s : Finset (GQ V)), (∀ γ ∈ s, Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤) → ∑ γ ∈ s, ∏ τ, ((1 + hsn (GlobalTheory.SepPer.cmp θ τ (c * (γ : GA D V) * g))) ^ (2 * V.rank ^ 2 + 1))⁻¹ ≤ C * height V g ^ A := by
  first | exact @GlobalTheory.PoinCount.poincare_count | exact GlobalTheory.PoinCount.poincare_count | (intros; apply GlobalTheory.PoinCount.poincare_count <;> assumption)
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

namespace GlobalTheory.AscFinStab

variable {D : D7}

theorem symplO_eq_two (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_comm_of (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {a b : WO S T} (g : WO S T → ℂ)
    (h : ψ (symplOH S T a b + symplOH S T a b) = 1) :
    heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g) := by
  rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_skew S T a b, add_comm b a]
  congr 1
  calc ψ (symplOH S T a b) = ψ ((symplOH S T a b + symplOH S T a b) + -symplOH S T a b) := by congr 1; ring
    _ = ψ (-symplOH S T a b) := by rw [AddChar.map_add_eq_mul, h, one_mul]

theorem heisO_smul'' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (c • g) = c • heisO ψ S T w g := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem fin_of_mxAt {m n : ℕ} {a : Mx D m n} (h : MxAt (fun _ => True) a) : a.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (h i j)).1

theorem fin_mul_left {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : u.map (infPart D) = 0) :
    (M * u).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.mul_zero]

theorem fin_mul_right {k m n : ℕ} {u : Mx D k m} (hu : u.map (infPart D) = 0) (M : Mx D m n) :
    (u * M).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

theorem isHalf_mul_left {e : AE D} {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (M * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hu l j]

theorem isHalf_mul_right {e : AE D} {k m n : ℕ} {u : Mx D k m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hu i l]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ}

def Comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : WO S T) : Prop :=
  ∀ g : WO S T → ℂ, heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g)

theorem mem_cls_of_comm (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ)
    (y : Mx D V₀.rank σ) {Φ : WO V W → ℂ} (hΦ : Φ ∈ cls dV dW p x y ψ) (c : WO V W)
    (hθ : IsThetaFunO ψ V W (heisO ψ V W c Φ))
    (h₁ : ∀ a ∈ p.A₁, Comm ψ V W (dV.extX W a) c) (h₂ : ∀ a ∈ p.A₂, Comm ψ V W (dV.extY W a) c)
    (h₃ : ∀ ξ ∈ p.B₁, Comm ψ V W (dV.ext0 W (dW.incX V₀ ξ)) c)
    (h₄ : ∀ η ∈ p.B₂, Comm ψ V W (dV.ext0 W (dW.incY V₀ η)) c)
    (h₅ : ∀ u ∈ p.Γ₀, Comm ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) c)
    (h₆ : ∀ e, IsSplitIdem D e → ∀ u ∈ p.Γ₀, IsHalf e (dV.ext0 W (dW.inc0 V₀ u)) → Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) c) :
    heisO ψ V W c Φ ∈ cls dV dW p x y ψ := by
  simp only [cls, Set.mem_ofPred_eq] at hΦ ⊢
  obtain ⟨_, hA₁, hA₂, hB₁, hB₂, hL⟩ := hΦ
  refine ⟨hθ, fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_, fun η hη => ?_, ?_⟩
  · rw [h₁ a ha, hA₁ a ha]
  · rw [h₂ a ha, hA₂ a ha, heisO_smul'']
  · rw [h₃ ξ hξ, hB₁ ξ hξ, heisO_smul'']
  · rw [h₄ η hη, hB₂ η hη]
  · unfold IsLatVac
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.1 (dV.ext0 W (dW.inc0 V₀ u₀)) hu
      show heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₅ u₀ hu₀, e1]
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.2 e he (dV.ext0 W (dW.inc0 V₀ u₀)) hu hh
      show heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₆ e he u₀ hu₀ hh, e1]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

theorem cls_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, (∀ w : WO V W, w.map (finPart D) = 0 → heisO ψ V W w Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ (∀ w ∈ Ann ψ V₀ W₀ p.Γ₀, heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ VacG ψ V₀ W₀ p.Γ₀ (flatS dV dW s (rat x₀) y Φ) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hlin p hp Φ hΦ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hΦ' := hΦ
  simp only [cls, Set.mem_ofPred_eq] at hΦ'
  obtain ⟨hθ, -, -, -, -, hL⟩ := hΦ'
  have hJ : ∀ a b : WO V₀ W₀,
      symplOH V W (dV.ext0 W (dW.inc0 V₀ a)) (dV.ext0 W (dW.inc0 V₀ b)) = symplOH V₀ W₀ a b := by
    intro a b
    rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclAnisotropic_inclAnisotropic V₀]
  have hfin0 : ∀ u ∈ p.Γ₀, (dV.ext0 W (dW.inc0 V₀ u)).map (infPart D) = 0 := fun u hu =>
    fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.fin₀ u hu))) _
  have comm0 : ∀ {a b : WO V W}, symplOH V W a b = 0 → Comm ψ V W a b := fun h g =>
    heisO_comm_of ψ g (by rw [h, add_zero, AddChar.map_zero_eq_one])
  refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
  · have cr : ∀ {a : WO V W}, a.map (infPart D) = 0 → Comm ψ V W a w := fun ha =>
      comm0 (GlobalTheory.FinTranslate.symplOH_fin_real ha hw)
    exact mem_cls_of_comm dV dW p _ y hΦ w (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ w)
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₁.fin a ha)) _))
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₂.fin a ha)) _))
      (fun ξ hξ => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₁.fin ξ hξ))) _))
      (fun η hη => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₂.fin η hη))) _))
      (fun u hu => cr (by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hfin0 _ (nsmul_mem hu 2)))
      (fun e _ u hu _ => cr (hfin0 u hu))
  · obtain ⟨hw1, hw2⟩ := hw
    have hc : ∀ u : WO V₀ W₀, ψ (symplO V₀ W₀ w u) = 1 →
        Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) (dV.ext0 W (dW.inc0 V₀ w)) := by
      intro u hu g
      refine heisO_comm_of ψ g ?_
      rw [hJ, GlobalTheory.FinTranslate.symplOH_skew V₀ W₀ w u, ← neg_add, AddChar.map_neg_eq_inv, ← symplO_eq_two, hu, inv_one]
    exact mem_cls_of_comm dV dW p _ y hΦ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ _)
      (fun a _ => comm0 (dV.wittDecomp_sympl_extIsotropic_extAnisotropic W a _))
      (fun a _ => comm0 (dV.wittDecomp_sympl_extDual_extAnisotropic W a _))
      (fun ξ _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclIsotropic_inclAnisotropic V₀]))
      (fun η _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclDual_inclAnisotropic V₀]))
      (fun u hu => by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hc _ (hw1 u hu))
      (fun e he u hu hh => hc u (hw2 e he u hu (by
        have h' := isHalf_mul_right (isHalf_mul_left dW.p0 hh) dV.j0
        have eq : dW.p0 * (dV.ext0 W (dW.inc0 V₀ u)) * dV.j0 = u := by
          rw [dV.matrixExtendByZero_apply, dW.wittDecomp_inclAnisotropicHom_apply]
          simp only [← Matrix.mul_assoc, dW.p0_j0, Matrix.one_mul]
          rw [Matrix.mul_assoc, dV.p0_j0, Matrix.mul_one]
        rwa [eq] at h')))
  · have hfl := GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU (rat x₀) y Φ hθ
    unfold VacG IsLatVac
    refine ⟨(GlobalTheory.Unf.Flat.flatLaw D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU x₀ hlin y Φ hθ).2,
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.1 _ (AddSubgroup.mem_map_of_mem _ hu)
      show heisO ψ V₀ W₀ (2 • u) (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, map_nsmul (dW.inc0 V₀), map_nsmul (dV.ext0 W), e1]
    · have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.2 e he _ (AddSubgroup.mem_map_of_mem _ hu) (isHalf_mul_right (isHalf_mul_left _ hh) _)
      show heisO ψ V₀ W₀ u (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, e1]

end GlobalTheory.AscFinStab

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

theorem _root_.GlobalTheory.T.depthCongruenceSubgroup_compactOpen_places_to_adeles : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → (lev G (.grid i 0) ≤ GfC _ ∧ IsCompact (lev G (.grid i 0) : Set (GA D (G.V (.grid i 0)))) ∧ IsOpen (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0))))) ∧ ∀ (R : Subgroup (GA D (G.V (.grid i 0)))) h, (∀ v ∉ G.pl.S0, ∀ h₁ ∈ grpAt _ (· = v), ∀ h₂ ∈ grpOff _ (· = v), h = h₁ * h₂ → CosetAt _ R (G.Λ (.grid i 0)) v h₁) → (∀ h₁ ∈ grpAt _ (fun v => v ∈ G.pl.S0), ∀ h₂ ∈ grpOff _ (fun v => v ∈ G.pl.S0), h = h₁ * h₂ → ∃ r ∈ R, r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid i 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ h₁ = r * k) → ∃ r ∈ R, ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid i 0), h = r * a * k := by
  first | exact @GlobalTheory.PlaceLevelCosets.levCoset_of_places | exact GlobalTheory.PlaceLevelCosets.levCoset_of_places | (intros; apply GlobalTheory.PlaceLevelCosets.levCoset_of_places <;> assumption)
end
