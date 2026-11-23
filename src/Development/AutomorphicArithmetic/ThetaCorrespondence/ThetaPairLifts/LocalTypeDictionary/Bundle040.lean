module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle478
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle553
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle555
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle026
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle034
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleDualAlgebraicityFiniteData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle331
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle512
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle400
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TendstoSlopeOfArchimedeanPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
theorem GlobalTheory.PlaceDecomp.weil_decomposition_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  intro D θ hθ hp N U W _ _ _ ρ hρ τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  obtain ⟨e, he, he1⟩ := GlobalTheory.T.exists_K_finite_reproducing_function _ (N.M.ε τ) (W τ) (ρ τ) (hρ τ)
  have hcl := _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp D θ hθ hp N U W ρ τ (fun f f' hf hf' => _root_.GlobalTheory.T.kFinite_isotypic_decomposition_additive D θ hθ hp N U f f' hf hf')
    (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).1 (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).2
  obtain ⟨m, a, c, haK, hQ, hA⟩ := GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed _ (N.M.ε τ) (N.M.H τ) (N.M.σ τ) hσ (HasCtp θ N U (TyOf θ N ρ) τ)
    (_root_.GlobalTheory.T.placewise_decomposition_translation_invariant D θ hθ hp N U W ρ τ) hcl.1 hcl.2.1 (_root_.GlobalTheory.T.placewise_decomposition_of_K_average D θ hθ hp N U W ρ τ) hcl.2.2 e he
  choose A hAop hAmv using fun j (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) => hA j u u.2
  have hexp := fun (f : GA D N.V → ℂ) (hf : f ∈ Cls θ N U) => _root_.GlobalTheory.T.twist_exists_exponential_model D θ hθ hp N τ f hf.1.1 (hf.1.2.2 τ)
  refine ⟨m, fun j => ⟨a j, haK j⟩, A, hAop, fun j f hf => ?_, fun f hf hTy => ?_⟩
  · choose S v ℓ C hW hc h using hexp f hf
    exact (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f) fun u => hAmv j u f hf).2
  · choose S v ℓ C hW hc h using hexp f hf
    have hform := fun j => (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f)
      fun u => hAmv j u f hf).1
    funext x
    have h1 := (moves_avg hθ (N.M.fr_unit τ) (N.M.fr_gram τ) hσ he f x _ _ _ _ (hW x) (hc x) (h x)).1.2.2.2.2 1
      (one_mem_UJ _)

    simp only [res_one hθ (N.M.fr_unit τ), sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (haK j))).hasSum)
    have h3 : avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f x = f x := by
      have := he1 _ (hTy x)
      have h4 : f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK (1 : KG (N.M.ε τ)) * N.M.fr τ)) = f x :=
        res_one hθ (N.M.fr_unit τ) f x
      exact this.trans h4
    rw [Finset.sum_apply]
    simp only [hform]
    rw [← h2, h3]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

theorem _root_.GlobalTheory.T.weil_representation_place_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | exact _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | (intros; apply _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology
noncomputable section
namespace GlobalTheory.BotSpanSnd
open Formalism.L2.Fam.ThC (fixSig)
section General
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
end General
section Bottom
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
end Bottom
section Real
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
end Real
theorem twistedClassSums_span_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A'.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A'.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  classical
  obtain ⟨K, hK⟩ := vanish_off_finite hX
  obtain ⟨J, hJ, hl⟩ := level_right hX
  obtain ⟨H, hH, hc⟩ := _root_.GlobalTheory.BotClassFin.bottomClass_exists_finite_reps hP hI hL hX J hJ
  refine ⟨H, K, conjField D, finiteDimensional_conjField, hH, ?_⟩
  intro t h hh k
  obtain ⟨γ, hγ, r, hrI, h₀, hh₀, κ, hκJ, hκf, rfl⟩ := hc h hh
  have hx : h₀ * κ ∈ GfC WW := mul_mem (hH h₀ hh₀) hκf
  have hγr : γ * r ∈ GfC WW := by
    have e : γ * r = (γ * r * h₀ * κ) * (h₀ * κ)⁻¹ := by group
    rw [e]; exact mul_mem hh (inv_mem hx)
  obtain ⟨c, hcM, hcE⟩ := real_right hX t hγ hrI hγr (h₀ * κ) k
  have e1 : X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) (γ * r * h₀ * κ) =
      ∑ k' ∈ c.support, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ := by
    have e0 : γ * r * h₀ * κ = γ * ((h₀ * κ) * r) := by
      rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC WW hrI hx]; simp only [mul_assoc]
    rw [e0, rat_left hX t _ hγ, hcE]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [hl t κ hκJ hκf]
  refine ⟨fun h' k' => if h' = h₀ then c.coeff k' else 0, fun a b => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hcM b
    · exact zero_mem _
  rw [e1, Finset.sum_eq_single_of_mem h₀ hh₀ (fun b _ hb => by simp [hb])]
  simp only [if_true]
  calc ∑ k' ∈ c.support, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀
      = ∑ k' ∈ c.support ∪ K, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        Finset.sum_subset Finset.subset_union_left fun k' _ hk' => by
          rw [MvPolynomial.notMem_support_iff.1 hk', zero_mul]
    _ = ∑ k' ∈ K, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        (Finset.sum_subset Finset.subset_union_right fun k' _ hk' => by
          rw [hK t h₀ k' hk', mul_zero]).symm
end GlobalTheory.BotSpanSnd
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_spanned_by_twistedClassSums : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A'.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A'.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  first | exact @_root_.GlobalTheory.BotSpanSnd.twistedClassSums_span_bottom | exact _root_.GlobalTheory.BotSpanSnd.twistedClassSums_span_bottom | (intros; apply _root_.GlobalTheory.BotSpanSnd.twistedClassSums_span_bottom <;> assumption)
end
end

section

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM Filter Topology
open scoped SchwartzMap GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
noncomputable section
namespace GlobalTheory.ArchJointCont
theorem tendsto_schrodinger_action_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _hM hW γ hγ r hr0 hR h k h₀ hk hh
  have hs := IsUWeilPair.isUSplitting hW
  let δ : ℝ → UA σ Y.J × UA σ Wd.J := fun t => (γ (Multiplicative.ofAdd t), 1)
  have hδc : Continuous δ := (hγ.1.comp continuous_ofAdd).prodMk continuous_const
  have hδ0 : δ 0 = 1 := by
    show (γ (Multiplicative.ofAdd 0), 1) = 1
    rw [ofAdd_zero, map_one]; rfl
  have hδm : ∀ s t, δ (s + t) = δ s * δ t := fun s t => by
    show (γ (Multiplicative.ofAdd (s + t)), 1) = (γ (Multiplicative.ofAdd s), 1) * (γ (Multiplicative.ofAdd t), 1)
    rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
  have ex := fun f => _root_.GlobalTheory.ArchLinePair.exists_orbit_pair_archimedean_line hP M ψ χX χW om hψ hW δ hδc hδ0 hδm (fun t => hγ.2 _)
    (fun t u _ => by simp [δ, mat]) f
  choose c g hc0 hslope hact using ex
  have hrr : ∀ x z, At (evI F) z → r (x + z) = r x := (hR 0).1
  have hinj := GlobalTheory.ArchCancel.eq_of_tens_eq F r hrr ⟨0, hr0⟩
  have hA : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c f t) r :=
    fun t f => hact f t r (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r = tens (evI F) ⇑f r + tens (evI F) ⇑g r := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (a : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(a • f) r = a • tens (evI F) ⇑f r := by
    intro a f; funext x; simp [tens, mul_assoc]
  let A : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := fun f => c f t
      map_add' := fun f g => hinj _ _ (by rw [← hA, tadd, map_add (f := _), hA, hA, tadd])
      map_smul' := fun a f => hinj _ _ (by rw [← hA, tsmul, map_smul, hA, RingHom.id_apply, tsmul]) }
  have hAf : ∀ t f, A t f = c f t := fun _ _ => rfl
  have hmul : ∀ s t f, c f (s + t) = c (c f t) s := fun s t f => hinj _ _ (by
    rw [← hA (s + t) f, ← hA s (c f t), ← hA t f, hδm, map_mul, Module.End.mul_apply])
  have hcont0 : ∀ f, Tendsto (fun s => c f s) (𝓝 0) (𝓝 f) := by
    intro f
    have h1 : Tendsto (fun s : ℝ => s • (s⁻¹ • (c f s - f))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • g f)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hslope f)
    rw [zero_smul] at h1
    have h2 : Tendsto (fun s => c f s) (𝓝[≠] 0) (𝓝 f) := by
      have h1' := h1.add_const f
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul, sub_add_cancel]
    have h3 : ContinuousAt (fun s => c f s) 0 := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hc0]; exact h2
    have h4 := h3.tendsto
    rwa [hc0] at h4
  have hcont : ∀ f, Continuous fun s => c f s := by
    intro f
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have ht : Tendsto (fun s : ℝ => s - t₀) (𝓝 t₀) (𝓝 0) := by
      have h5 := (continuous_sub_right t₀).tendsto t₀
      rwa [sub_self] at h5
    refine ((hcont0 (c f t₀)).comp ht).congr fun s => ?_
    show c (c f t₀) (s - t₀) = c f s
    rw [← hmul, sub_add_cancel]
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  have hAcont : ∀ t, Continuous (A t) := by
    intro t
    refine continuous_of_weak (A t) fun T => ?_
    obtain ⟨l, hl, hlf⟩ := exists_adm F T
    obtain ⟨T', hT'⟩ := hs.adm (δ t) l hl g₀ hg₀
    refine T'.continuous.congr fun f => ?_
    have e1 : om (δ t) (pureA F ⇑f g₀) = pureA F ⇑(c f t) g₀ := hact f t r₀ (hR₀ f)
    have e2 := hT' f
    rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
    exact e2.symm
  let 𝓕 : Set.Icc (-1 : ℝ) 1 → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) := fun i => ⟨A i, hAcont i⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hq := schwartz_withSeminorms ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ 𝓕) := hq.banach_steinhaus fun q x => by
    have hc : Continuous fun t : ℝ => schwartzSeminormFamily ℂ _ ℂ q (c x t) :=
      (hq.continuous_seminorm q).comp (hcont x)
    have := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hc.continuousOn
    rw [Set.image_eq_range] at this
    exact this
  have hk' : ∀ t, k t = c (h t) t := fun t => hinj _ _ ((hk t).symm.trans (hA t (h t)))
  have h1 : Tendsto (fun t => A t (h t - h₀)) (𝓝 0) (𝓝 0) := by
    have hE := hUE.equicontinuous 0
    intro U hU
    have hU' : {p : SInf F (Fin n × Fin d) × SInf F (Fin n × Fin d) | p.2 - p.1 ∈ U} ∈
        uniformity (SInf F (Fin n × Fin d)) := by
      rw [uniformity_eq_comap_nhds_zero]; exact ⟨U, hU, fun p hp => hp⟩
    have ev := hE _ hU'
    have hz : Tendsto (fun t => h t - h₀) (𝓝 0) (𝓝 0) := by simpa using hh.sub_const h₀
    have ev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := Icc_mem_nhds (by norm_num) (by norm_num)
    refine Filter.mem_map.2 ?_
    filter_upwards [hz.eventually ev, ev3] with t ht ht'
    have := ht ⟨t, ht'⟩
    simpa [𝓕] using this
  have h2 : Tendsto (fun t => A t (h t - h₀) + c h₀ t) (𝓝 0) (𝓝 (0 + h₀)) := h1.add (hcont0 h₀)
  rw [zero_add] at h2
  refine h2.congr fun t => ?_
  rw [hk' t, map_sub]
  show c (h t) t - c h₀ t + c h₀ t = c (h t) t
  exact sub_add_cancel _ _
end GlobalTheory.ArchJointCont
end
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField

theorem _root_.GlobalTheory.T.jointly_continuous_archimedean_weil_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  first | exact @_root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line | exact _root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line | (intros; apply _root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
namespace GlobalTheory.Twist.SmoothLine
theorem smooth_line_of_pure_tensor_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    (∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0) →
    ∀ c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) →
      ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hCM hψ hM hW γ hγ f φ hSB hvac hne c hc
  obtain ⟨c₁, c', h0, hlim, hacts⟩ := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP M ψ χX χW om hCM hψ hW γ hγ f
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI F) (⇑f) r :=
    ⟨fun x z hz => finprod_add_of_at φ x z hz, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  obtain ⟨y, hy⟩ := hne
  have heq : ∀ t, c t = c₁ t := by
    intro t
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evI F) (⇑(c₁ t)) r :=
      (hc t).symm.trans (hacts t r hRest)
    ext x
    let z : Fin n × Fin d → AF F := fun i => (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i),
        (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from y i).2))
    have hzI : (fun i => evI F (z i)) = x := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i)) = x i
      exact RingEquiv.apply_symm_apply _ _
    have hzF : (∏ᶠ v, φ v fun i => evFin F v (z i)) = ∏ᶠ v, φ v fun i => evFin F v (y i) := rfl
    have e := congrFun h1 z
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, r, hzI, hzF] at e
    exact mul_right_cancel₀ hy e
  have hc' : c = c₁ := funext heq
  subst hc'
  refine ⟨c', ?_⟩
  rw [h0]
  exact hlim
end GlobalTheory.Twist.SmoothLine
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

theorem _root_.GlobalTheory.T.pure_tensor_theta_smooth_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    (∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0) →
    ∀ c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) →
      ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @_root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta | exact _root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta | (intros; apply _root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta <;> assumption)
end
end
