module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevel
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  first | exact @GlobalTheory.PlaneCompl.exists_compl | exact GlobalTheory.PlaneCompl.exists_compl | (intros; apply GlobalTheory.PlaneCompl.exists_compl <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hasInfinityExponent_of_finitePartPower : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → HasFinPart χ c e →
  ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  first | exact @GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart | exact GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart | (intros; apply GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_normScale_curveIdeal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∃ r : D.host.E, IsScale D cc r := by
  first | exact @GlobalTheory.NormRatio.exists_scale | exact GlobalTheory.NormRatio.exists_scale | (intros; apply GlobalTheory.NormRatio.exists_scale <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n)), V.gram = 1 →
  (∀ x, IsFinPt V (ι x) x) → Function.Injective ι → ι.range = GfC V → J ≤ intG D n → IsCongLevel J →
  ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsOpenCompactLevel V K ∧ ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J := by
  first | exact @GlobalTheory.CongLevelStd.exists_level | exact GlobalTheory.CongLevelStd.exists_level | (intros; apply GlobalTheory.CongLevelStd.exists_level <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heisenbergTranslate_fixes_theta_deepLevel : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    heisO ψ S T (actO S T g h (finPt hS hT r z) - finPt hS hT r z') F = F := by
  first | exact @GlobalTheory.LevelTr.level_translate | exact GlobalTheory.LevelTr.level_translate | (intros; apply GlobalTheory.LevelTr.level_translate <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

def scaleCLM {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) : VC D N N' →L[ℂ] VC D N N' :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ i j => c τ * Z τ i j
      map_add' := fun Z Z' => by funext τ i j; simp [mul_add]
      map_smul' := fun s Z => by funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem scaleCLM_apply {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (Z : VC D N N') :
    scaleCLM c Z = fun τ i j => c τ * Z τ i j := rfl

theorem scaleCLM_coordV {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (k : D.what₂.Tau × Fin N' × Fin N) :
    scaleCLM c (Formalism.MainNotions.TaylorLogMetric.coordV D k) = c k.1 • Formalism.MainNotions.TaylorLogMetric.coordV D k := by
  funext τ i j
  simp only [scaleCLM_apply, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.1]
  · simp

theorem prod_toList_get {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ)
    (h : ∀ i : Fin (Finsupp.toMultiset m).card, (i : ℕ) < (Finsupp.toMultiset m).toList.length) :
    (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩)) =
      m.prod fun k e => g k ^ e := by
  have hl : (Finsupp.toMultiset m).card = (Finsupp.toMultiset m).toList.length := (Multiset.length_toList _).symm
  calc (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩))
      = ∏ i : Fin (Finsupp.toMultiset m).toList.length, g ((Finsupp.toMultiset m).toList.get i) :=
        Fin.prod_congr' (fun i => g ((Finsupp.toMultiset m).toList.get i)) hl
    _ = ((Finsupp.toMultiset m).toList.map g).prod := Fin.prod_univ_fun_getElem _ g
    _ = (Multiset.map g (Finsupp.toMultiset m)).prod := by
        conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
        rw [Multiset.map_coe, Multiset.prod_coe]
    _ = m.prod fun k e => g k ^ e := by
        rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
          Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem taylor_scale {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) α =
      (α.prod fun k e => c k.1 ^ e) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  have hfun : (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) = G ∘ scaleCLM c := rfl
  have hGc : ContDiff ℂ ⊤ G := (GlobalTheory.SCV.analyticOnNhd_of_differentiable hG Set.univ).contDiff
  rw [Formalism.MainNotions.TaylorLogMetric.taylor, Formalism.MainNotions.TaylorLogMetric.taylor, hfun,
    (scaleCLM c).iteratedFDeriv_comp_right hGc 0 le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  simp only [scaleCLM_coordV]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_div_assoc]
  congr 1
  exact prod_toList_get α (fun k => c k.1) _

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

def placeWt (D : D7) (a d : ℕ) : Formalism.MainNotions.GL3Theta.Idx D a d → D.what₂.Tau → ℕ := fun k => Pi.single k.1 1

theorem prod_eq_prod_weight {D : D7} {a d : ℕ} (f : D.what₂.Tau → ℂ) (v : Formalism.MainNotions.GL3Theta.Idx D a d →₀ ℕ) :
    (v.prod fun k e => f k.1 ^ e) = ∏ τ, f τ ^ Finsupp.weight (placeWt D a d) v τ := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single k.1]
  · simp [placeWt]
  · intro τ _ hτ
    simp [placeWt, hτ]
  · simp

theorem minorPol_isWeightedHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (t : Tup D a d n) :
    (minorPol D t).IsWeightedHomogeneous (placeWt D a d) (fun τ => a * n τ) := by
  have hdet : ∀ τ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, (t τ j).1 i, i') :
      MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det.IsWeightedHomogeneous (placeWt D a d) (a • Pi.single τ 1) := by
    intro τ j
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun i => (MvPolynomial.X (τ, (t τ j).1 (σ i), i) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ))
      (fun _ => (Pi.single τ 1 : D.what₂.Tau → ℕ))
      (fun i _ => MvPolynomial.isWeightedHomogeneous_X ℂ (placeWt D a d) (τ, (t τ j).1 (σ i), i))
    simpa using this
  have h := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun τ _ =>
    MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun j _ => hdet τ j
  have hdeg : (fun τ => a * n τ) = ∑ τ, ∑ _j : Fin (n τ), a • (Pi.single τ 1 : D.what₂.Tau → ℕ) := by
    funext τ'
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hdeg]
  exact h

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

theorem fock_minorPol_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ (n : D.what₂.Tau → ℕ) (t : Tup D a d n),
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f
        (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hT.symm k.2.1, Fin.cast hS.symm k.2.2) : FVar D T.rank S.rank))
          (minorPol D t)) 0 =
      (∏ τ, period D δ r τ ^ (a * n τ)) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D t) G := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hG hR n t
  subst hS hT
  have hren : MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D S.rank T.rank =>
      ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : FVar D T.rank S.rank)) (minorPol D t) = minorPol D t :=
    MvPolynomial.rename_id_apply _
  rw [hren]
  obtain ⟨hstd, hinf, hgS, hgT, hcrv, hsc⟩ := hs
  have hrd := (reads_iff hcrv hsc G f).1 hR
  have hΦ : Differentiable ℂ (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) :=
    hG.comp (scaleCLM (fun τ => δ * embT D τ r)).differentiable
  have hfr : ∀ m, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin m) D.host.E) = fun _ => 1 := fun m =>
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  have hon : ∀ V : HSp D, V.gram = 1 →
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 * V.gram *
        (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    simp [Formalism.UG.cT, hV]
  have hmono := GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ S T 1 1 hstd hinf (hon S hgS) (hon T hgT) f _ hΦ hrd.2
  rw [hfr, hfr] at hmono
  set P := minorPol D t with hPdef
  have hP : P = ∑ v ∈ P.support, AddMonoidAlgebra.coeff P v • MvPolynomial.monomial v (1 : ℂ) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    exact Finset.sum_congr rfl fun v _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

  conv_lhs => rw [hP, map_sum, Finset.sum_apply]
  rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hmono v]
  have happ : Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial v 1)
      (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) =
      (v.prod fun _ e => (e.factorial : ℂ)) *
        Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) v := by
    rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.sum_subset MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
    intro x _ hx
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul, zero_mul]
  rw [happ, taylor_scale (fun τ => δ * embT D τ r) G hG v]
  have hw : Finsupp.weight (placeWt D S.rank T.rank) v = fun τ => S.rank * n τ :=
    minorPol_isWeightedHomogeneous t (MvPolynomial.mem_support_iff.1 hv)
  have hper : (∏ τ, period D δ r τ ^ (S.rank * n τ)) =
      (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (v.sum fun _ e => e) *
        v.prod fun k e => (δ * embT D k.1 r) ^ e := by
    rw [← Finset.prod_congr rfl fun τ _ => congrArg (period D δ r τ ^ ·) (congrFun hw τ),
      ← prod_eq_prod_weight]
    simp only [period, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← mul_pow,
      div_eq_mul_inv]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [hper]
  ring

end GlobalTheory.NormExact
end
end

section

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

namespace GlobalTheory.GLTwoHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_adicCompletionIntegers_loc (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem eventually_singleNU_mem {N : Set (FiniteAdeleRing (𝓞 E) E)} (hN : N ∈ 𝓝 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ y ∈ w.adicCompletionIntegers E, singleNU w y ∈ N := by
  classical
  let s : (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) → FiniteAdeleRing (𝓞 E) E :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) cofinite
  have hs : Continuous s :=
    (RestrictedProduct.isOpenEmbedding_structureMap isOpen_adicCompletionIntegers_loc).continuous
  have hs0 : s 0 = 0 := rfl
  have h1 : s ⁻¹' N ∈ 𝓝 (0 : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) :=
    hs.continuousAt.preimage_mem_nhds (by rw [hs0]; exact hN)
  rw [nhds_pi, Filter.mem_pi'] at h1
  obtain ⟨I, t, ht, hIt⟩ := h1
  refine Filter.mem_of_superset I.finite_toSet.compl_mem_cofinite fun w hw y hy => ?_
  have hx : s (Pi.single w ⟨y, hy⟩) = singleNU w y := by
    refine Subtype.ext (funext fun u => ?_)
    change ((Pi.single w (⟨y, hy⟩ : w.adicCompletionIntegers E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) u : u.adicCompletion E) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E u (GlobalTheory.AdelicU.singleFin w y)
    by_cases h : u = w
    · subst h
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, Pi.single_eq_same]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, Pi.single_eq_of_ne h]
      rfl
  rw [← hx]
  refine hIt fun u hu => ?_
  have hne : u ≠ w := fun e => hw (e ▸ hu : w ∈ (I : Set _))
  rw [Pi.single_eq_of_ne hne]
  exact mem_of_mem_nhds (ht u)

end GlobalTheory.GLTwoHecke
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport


noncomputable section

namespace GlobalTheory.FrameColSmul

theorem colMul_mem_of_span {A : Type} [CommRing A] (S : Subring A) {ι : Type} (M : Submodule S (ι → A))
    (c : ι → A) (G : Set A) (hG : ∀ y ∈ G, (fun i => c i * y) ∈ M) (x : A)
    (hx : x ∈ Submodule.span S G) : (fun i => c i * x) ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero =>
    have : (fun i => c i * (0 : A)) = 0 := by funext i; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b) := by
      funext i; simp [mul_add]
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => c i * (r • a)) = r • (fun i => c i * a) := by
      funext i
      show c i * ((r : A) * a) = (r : A) * (c i * a)
      exact mul_left_comm _ _ _
    rw [this]; exact M.smul_mem r ha

theorem mulVec_eq_sum_col {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (w : Fin n → A) :
    P *ᵥ w = ∑ j, (fun i => P i j * w j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

theorem map_col_mul {E A : Type} [Field E] [NumberField E] [CommRing A] (φ : E →+* A) {n : ℕ}
    (c : Fin n → E) (b : 𝓞 E) :
    (fun i => φ (c i) * φ (b : E)) = fun i => φ ((b • c) i) := by
  funext i
  show _ = φ ((b : E) * c i)
  rw [map_mul, mul_comm]

theorem gen_mem {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (j : Fin n)
    (b : 𝓞 D.host.E) (hb : b ∈ 𝔪) :
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j) *
        GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  have hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr :=
    Submodule.subset_span ⟨j, rfl⟩
  have hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr :=
    Submodule.smul_mem_smul hb hcol
  rw [map_col_mul]
  exact Submodule.subset_span ⟨_, hm, rfl⟩

theorem mulVec_mem : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  intro D n fr 𝔪 w hw
  rw [mulVec_eq_sum_col]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _
    (by
      rintro _ ⟨b, hb, rfl⟩
      exact gen_mem fr 𝔪 j b hb) (w j) (hw j)

end GlobalTheory.FrameColSmul
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem infTensAt_of_places {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) {C : ℝ} (hC : 0 ≤ C)
    (hd : DatAt ch (C / 2)) (hc : CoefAt ch (C / 2)) : InfTensAt ch C := by
  intro σ Φ β hβ x y
  set K : ℝ := C / 2 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hK
  have h1 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => ((ch.S.term A.μ0 Φ β v).coef : ℂ)) (fun v => K * placeSz ch.G v)
    (fun v _ => absLe_rat σ _ (by simpa [hK] using hc Φ β hβ v))
  have h2 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => (ch.S.term A.μ0 Φ β v).datum (ch.S.colAt A.μ0 v x) (ch.S.rowAt A.μ0 v y)) (fun v => K * placeSz ch.G v)
    (fun v _ => by simpa [hK] using hd σ Φ β hβ v x y)
  refine absLe_mono (absLe_mul h1 h2) ?_
  rw [← Finset.mul_sum, ← two_mul, ← mul_assoc]
  have : 2 * K = C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 := by rw [hK]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (sum_placeSz_le ch.G A.μ0) (by positivity)

end GlobalTheory.ArchTens


end
end
