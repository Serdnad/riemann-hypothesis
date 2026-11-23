module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle190
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle364
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle011
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspPureApprox
theorem exists_sum_approx_pure_cusp_form : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj φ hφ a δ hδ
  obtain ⟨ψ, hψ, hK, hle⟩ := _root_.GlobalTheory.T.kFinite_cusp_forms_dense hP D G₀ Pl0 T A Ks R G hR hG i j hi hj φ hφ a δ hδ
  obtain ⟨n, Tm, v, hT, heq⟩ := _root_.GlobalTheory.T.kFinite_cusp_form_finite_sum_expansion hP D G₀ Pl0 T A Ks R G hR hG i j hi hj ψ hψ hK
  exact ⟨n, Tm, v, hT, fun g => by rw [← heq g]; exact hle g⟩
end GlobalTheory.CuspPureApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.pure_cusp_form_approx_of_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.CuspPureApprox.exists_sum_approx_pure_cusp_form | exact _root_.GlobalTheory.CuspPureApprox.exists_sum_approx_pure_cusp_form | (intros; apply _root_.GlobalTheory.CuspPureApprox.exists_sum_approx_pure_cusp_form <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SplitSphVPrimeStab
theorem vacuum_fixed_by_split_spherical_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hTr
  classical
  have hfin1 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) |
      ¬ G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    hTr.geo.hM'.std
  have hfin2 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal}.Finite := by
    have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 hv
  have hfin3 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ⟨X.T ∪ hfin1.toFinset ∪ hfin2.toFinset ∪ hfin3.toFinset, ?_⟩
  intro v hv _ k hk
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨⟨hvT, hstd⟩, hdiff⟩, h2⟩ := hv
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (GlobalTheory.SphOffFinite.isUnram_of_unramified hTr.base.unram v) with hs | ⟨w, hw⟩
  · have hψ := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v hdiff
    obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
    obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v k hk.1
    obtain ⟨hφ₁, hact⟩ := hS _ hSB
    have h1 := GlobalTheory.InertSphLeft.acts_vacCond_of_mem_KAt_left F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB _ hφ₁ hact hvac
    obtain ⟨c, hc'⟩ := _root_.GlobalTheory.SphOffFinite.spherical_vacuum_unique_off_finite_set hPr F E σ B a a' G X om om' hTr v hs hψ h2 θ hθ hvac _ hφ₁ h1
    rw [hc'] at hact
    have hc := _root_.GlobalTheory.T.split_left_scalar_factor_eq_one hPr F E σ B a a' G X om om' hTr v hs hvT hψ h2 hstd k hk c hact
    rwa [hc, one_smul] at hact
  · exact GlobalTheory.InertSphLeft.vac_fixed_left F E σ B a a' G X om om' hTr v w hw hvT k hk
end GlobalTheory.SplitSphVPrimeStab
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.split_vprime_stabilizer_fixes_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @_root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left | exact _root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left | (intros; apply _root_.GlobalTheory.SplitSphVPrimeStab.vacuum_fixed_by_split_spherical_left <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.HoweGlobal.RealTransfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealActs
theorem howe_real_place_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have PA : PolActs Bs G.M om := _root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair
  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  have key : ∀ N : Submodule ℂ ↥P, relInf Bs G om ≤ N → (∀ g ∈ opInf Bs G om, ∀ x ∈ N, g x ∈ N) →
      GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N.map P.subtype) := by
    intro N hrel hop
    refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.1 γ hγ
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩, hrel (Submodule.subset_span (Or.inl ⟨γ, hγ, f, hf, hA⟩)), rfl⟩
    · intro k hk f hf f₁ hA
      obtain ⟨D, hDP, hD⟩ := PA.2.1 k hk
      have e : f₁ = D f := (hD f hf f₁).1 hA
      have h1 : f₁ ∈ P := e ▸ hDP f hf
      refine ⟨⟨f₁, h1⟩ - ⟨f, hf⟩, hrel (Submodule.subset_span (Or.inr ⟨k, hk, ⟨f, hf⟩, ⟨f₁, h1⟩, hA, rfl⟩)), rfl⟩
    · intro γ hγ f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.1 γ hγ
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inr ⟨γ, hγ, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
    · intro k hk f hf f₁ hA
      obtain ⟨y, hy, rfl⟩ := hf
      obtain ⟨D, hDP, hD⟩ := PA.2.2.2 k hk
      let g : Module.End ℂ ↥P := D.restrict hDP
      have hg : g ∈ opInf Bs G om := Or.inl ⟨k, hk, fun f => (hD f f.2 _).2 rfl⟩
      have e : f₁ = D y := (hD y y.2 f₁).1 hA
      exact ⟨g y, hop g hg y hy, e.symm⟩
  have hinj : Function.Injective (Submodule.map P.subtype) :=
    Submodule.map_injective_of_injective P.injective_subtype
  have hne : ∀ N : Submodule ℂ ↥P, N ≠ ⊤ → N.map P.subtype ≠ P := by
    intro N hN h
    apply hN
    apply hinj
    rw [h, Submodule.map_subtype_top]
  refine ⟨_root_.GlobalTheory.T.polarization_rank_le_dim hP F E σ Bs _ _ _ _ G.M _ _ om _ _ _ _ hPair, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hreal.1
    refine ⟨L, fun m N hN hN' => hL m (fun i => (N i).map P.subtype)
      ((Submodule.map_strictMono_of_injective P.injective_subtype).comp hN) fun i => key _ (hN' i).1 (hN' i).2⟩
  · intro N hrel hop hN x hx
    exact hreal.2 _ (key N hrel hop) (hne N hN) x ⟨x, hx, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro x (⟨γ, hγ, f, hf, hA⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
    · exact hM.real.quot.lie γ hγ f hf _ hA
    · show R.p (((f₁ - f : ↥P)) : SInf F _) = 0
      rw [Submodule.coe_sub, map_sub, hM.real.quot.cpt k hk f f.2 f₁ hA, sub_self]
  · intro g hg x hx
    have hx' : R.p (x : SInf F _) = 0 := hx
    show R.p ((g x : ↥P) : SInf F _) = 0
    rcases hg with ⟨k, hk, hA⟩ | ⟨γ, hγ, hA⟩
    · have := hM.real.cpt k hk x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.acts_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
    · have := hM.real.lie γ hγ x x.2 0 (G.M'.Pol Bs.ψ Bs.emb).zero_mem _ 0 (hA x)
        (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [hx', map_zero])
      rw [this, map_zero]
end GlobalTheory.HoweGlobal.RealTransfer
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.global_howe_transfer_real_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    Module.rank ℂ ↥(G.M.Pol Bs.ψ Bs.emb) ≤ Cardinal.aleph0 ∧
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb)), StrictMono N →
        (∀ j, GlobalTheory.HoweGlobal.relInf Bs G om ≤ N j ∧ ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) ∧
    (∀ N : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N →
        (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ →
        N ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype)) ∧
    GlobalTheory.HoweGlobal.relInf Bs G om ≤ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) ∧
    ∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype),
      g x ∈ LinearMap.ker (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) := by
  first | exact @_root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | exact _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer | (intros; apply _root_.GlobalTheory.HoweGlobal.RealTransfer.howe_real_place_transfer <;> assumption)
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
noncomputable section
namespace GlobalTheory.LineSumV'
theorem lineSum_exists_derivative_factor (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (hθ : IsInfFam θ) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ) :
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb,
      ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) ΦD x) (Ψ x) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hJ
  obtain ⟨Dop, hDP, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ D.sp.cm.sig Bs _ _ Γ.V' Γ.W Γ.M' Xc.α (Xc.α / Xc.β) om' _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V' hT)).2.2.1 γ hγ
  have hfun : ∀ Φ : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ, ∀ x,
      (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) Φ x) = fun t => om' (1, γ (Multiplicative.ofAdd t)) Φ x := by
    intro Φ x; funext t; rw [hγt t]
  intro ΦD hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q _ _ hp hq =>
    obtain ⟨p', hp', hdp⟩ := hp
    obtain ⟨q', hq', hdq⟩ := hq
    refine ⟨p' + q', add_mem hp' hq', fun x => ?_⟩
    have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) (p + q) x) =
        fun t => om' (1, kapX X e hJ (oneP θ X τ Y t)) p x + om' (1, kapX X e hJ (oneP θ X τ Y t)) q x := by
      funext t; simp
    rw [e1]
    exact (hdp x).add (hdq x)
  | smul c p _ hp =>
    obtain ⟨p', hp', hdp⟩ := hp
    refine ⟨c • p', Submodule.smul_mem _ c hp', fun x => ?_⟩
    have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X τ Y t)) (c • p) x) =
        fun t => c * om' (1, kapX X e hJ (oneP θ X τ Y t)) p x := by
      funext t; simp
    rw [e1]
    simpa using (hdp x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dop f) φ, Submodule.subset_span ⟨Dop f, φ, hDP f hf, hSB, hev, rfl⟩, fun x => ?_⟩
    rw [hfun]
    exact ((hD f hf (Dop f)).2 rfl) _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
theorem lineSum_product_rule (hpure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a' × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
    ∀ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (∑ i, Ψ i x) 0 := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD
  have hex : ∀ (Φ : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ), Φ ∈ algD Γ.M' Bs.ψ Bs.emb → ∀ i : Fin l.length,
      ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) Φ x) (Ψ x) 0 :=
    fun Φ hΦ i => _root_.GlobalTheory.LineSumV'.lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) Φ hΦ
  induction hΦD using Submodule.span_induction with
  | zero =>
    intro Ψ hΨ x
    have h0 : ∀ i, Ψ i x = 0 := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    simp only [h0, Finset.sum_const_zero]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add p q hp hq ihp ihq =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    choose Ψq hΨq hdq using hex q (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hq)
    have hsplit : ∀ i, Ψ i x = Ψp i x + Ψq i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (p + q) x) =
          fun t => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x +
            om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) q x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).add (hdq i x)
    have e2 : (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (p + q) x) =
        fun t => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x +
          om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) q x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).add (ihq Ψq (fun i => ⟨hΨq i, hdq i⟩) x)
  | smul c p hp ihp =>
    intro Ψ hΨ x
    choose Ψp hΨp hdp using hex p (Submodule.span_le.2 (fun _ h => Submodule.subset_span h) hp)
    have hsplit : ∀ i, Ψ i x = c * Ψp i x := by
      intro i
      refine ((hΨ i).2 x).unique ?_
      have e1 : (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (c • p) x) =
          fun t => c * om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) p x := by
        funext t; simp
      rw [e1]
      exact (hdp i x).const_mul c
    have e2 : (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (c • p) x) =
        fun t => c * om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) p x := by
      funext t; simp
    rw [e2, Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum]
    exact (ihp Ψp (fun i => ⟨hΨp i, hdp i⟩) x).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    exact hpure hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl f hf φ hSB hev
theorem lineSum_derivative_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Φ₁D hΦ₁
  have hex : ∀ i : Fin l.length, ∃ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ x,
      HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ x) 0 :=
    fun i => _root_.GlobalTheory.LineSumV'.lineSum_exists_derivative_factor hP D θ X e Bs Γ Xc om om' hJ hθ hT _ _ (hl _ (List.get_mem l i)) ΦD hΦD
  choose Ψ hΨ hder using hex
  refine ⟨Ψ, fun i => ⟨hΨ i, hder i⟩, ?_⟩
  funext x
  rw [Finset.sum_apply]
  exact (hΦ₁ x).unique (_root_.GlobalTheory.LineSumV'.lineSum_product_rule _root_.GlobalTheory.T.dual_pure_tensor_product_rule hP D θ X e Bs Γ Xc om om' hJ hθ hT l hl ΦD hΦD Ψ (fun i => ⟨hΨ i, hder i⟩) x)
end GlobalTheory.LineSumV'
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.lineSum_derivation_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₁D : (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : Fin l.length → (Fin a' × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ i, Ψ i ∈ algD Γ.M' Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) ΦD x) (Ψ i x) 0) ∧
      Φ₁D = ∑ i, Ψ i := by
  first | exact @_root_.GlobalTheory.LineSumV'.lineSum_derivative_sum | exact _root_.GlobalTheory.LineSumV'.lineSum_derivative_sum | (intros; apply _root_.GlobalTheory.LineSumV'.lineSum_derivative_sum <;> assumption)
end
end
