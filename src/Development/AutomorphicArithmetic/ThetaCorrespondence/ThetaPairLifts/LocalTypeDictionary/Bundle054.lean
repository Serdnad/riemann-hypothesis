module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle437
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle596
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle654
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle597
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle050
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle052
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open scoped ENNReal
namespace GlobalTheory.SobolevCuspApprox
theorem sobolev_approximation_by_cuspForms : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB _ i _ φ hφ U hU hlev d δ hδ
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨hAut, hc, -⟩ := id hφ
  have hφg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V φ :=
    ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hAut hc, hc⟩
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hr : 0 < r := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 h)] at hr1
    exact lt_irrefl _ hr1
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D R.θ hθ (G.P (i + 1)) φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList
    (Finset.nodup_toList _) d r hr
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition D R.θ hθ hP (G.P (i + 1)) φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  let F' : ℕ → (G.P (i + 1)).Maps := fun k => if h : k < n then F ⟨k, h⟩ else 0
  let v' : ℕ → Formalism.IndefR.Links.SmT (G.P (i + 1)).M := fun k => if h : k < n then v ⟨k, h⟩ else 0
  have hval : ∀ j : Fin n, F' j (v' j) = F j (v j) := fun j => by simp [F', v', j.2]
  have hsumeq : ∑ k ∈ Finset.range n, F' k (v' k) = ∑ j, F j (v j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => F' k (v' k))]
    exact Finset.sum_congr rfl fun j _ => hval j
  refine ⟨Finset.range n, F', v', fun k hk => ?_, fun k hk u hu hu' g => ?_, ?_⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', hk'] using hF ⟨k, hk'⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', v', hk'] using hFlev ⟨k, hk'⟩ u hu hu' g
  · rw [hsumeq]
    have hsg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (∑ j, F j (v j)) :=
      Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
        (GlobalTheory.CuspApproxAll.good_zero R.θ (G.P (i + 1)).V) fun j _ =>
          GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ (G.P (i + 1)) (hF j) (v j)
    have hg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (φ - ∑ j, F j (v j)) := by
      have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
      rwa [neg_one_smul, ← sub_eq_add_neg] at this
    exact ⟨fun e' => GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1 e', lt_of_le_of_lt hgrow hr2⟩
end GlobalTheory.SobolevCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.cuspForm_sobolev_density : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ := by
  first | exact @_root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms | exact _root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms | (intros; apply _root_.GlobalTheory.SobolevCuspApprox.sobolev_approximation_by_cuspForms <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
open scoped ENNReal
theorem GlobalTheory.CuspApproxAll.cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  intro D θ hθ hP N φ hφ A ε hε
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 A
  have hφg : GlobalTheory.CuspApproxAll.Good θ N.V φ := ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc, hc⟩
  have hη : 0 < ε / ((C : ℝ) + 1) := div_pos hε (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D θ hθ N φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) d _ hη
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition D θ hθ hP N φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  refine ⟨n, F, v, hF, fun g => ?_⟩
  set ψ : GA D N.V → ℂ := φ - ∑ j, F j (v j) with hψ
  have hsg : GlobalTheory.CuspApproxAll.Good θ N.V (∑ j, F j (v j)) :=
    Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good θ N.V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
      (GlobalTheory.CuspApproxAll.good_zero θ N.V) fun j _ => GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ N (hF j) (v j)
  have hg : GlobalTheory.CuspApproxAll.Good θ N.V ψ := by
    have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := fun k hk hk' x => by
    simp only [hψ, Pi.sub_apply, Finset.sum_apply, hlev k hk hk' x, hFlev _ k hk hk' x]
  have h1 := hC ψ hg.1.toIsAutFun hψlev hg.1.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1) hg.2
  have h2 : decaySize N.V A ψ ≤ ENNReal.ofReal ε := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (ε / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ A) ≤ ENNReal.ofReal ε := (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ A)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hε.le] at h3
  simpa [hψ, Finset.sum_apply] using h3
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  first | exact @_root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | exact _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | (intros; apply _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.FockKFin
theorem fock_space_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP f hf
  have hPA := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff hDspan using hD
  have hK := hPA.2.1
  simp only [GlobalTheory.RealActs.OpOn] at hK
  choose! Tk hTpres hTacts using hK
  have hGP : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → f₀ ∈ M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hmin : ∀ N : Submodule ℂ (SInf F (Fin n × Fin d)), {f₀ | M.IsGauss B.ψ B.emb f₀} ⊆ N →
      (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | At (evI F) u}, ∀ g ∈ N, Dfun u g ∈ N) → M.Pol B.ψ B.emb ≤ N := by
    intro N hG hN
    refine sInf_le ⟨fun f₀ h => hG h, fun u hu g hg g₁ hg₁ => ?_⟩
    rw [(hDiff u hu g g₁).1 hg₁]
    exact hN u hu g hg
  have hAt : ∀ k : UA σ X.J, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) (mat k * u) :=
    fun k u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨S, hS, hSk⟩ := GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated (SInf F (Fin n × Fin d)) (Matrix (Fin n) (Fin d) (AE F E))
    {k // k ∈ KInf σ X B.emb} {u | At (evI F) u} {f₀ | M.IsGauss B.ψ B.emb f₀} (M.Pol B.ψ B.emb) Dfun m L
    (fun k => Tk k.1) (fun k u => mat k.1 * u) (GlobalTheory.T.fockVacua_span_finiteDimensional F E σ B n d X W M χX χW om r s r' s' hP)
    (fun u hu g => hDspan u hu g) (fun f₀ h => hGP f₀ h) (fun u hu g hg => hclos u hu g hg) hmin
    (fun k g hg => Submodule.subset_span
      (_root_.GlobalTheory.T.fock_vacuum_stabilized_is_gaussian hPr F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 g hg _
        ((hTacts k.1 k.2 g (hGP g hg) _).2 rfl)))
    (fun k u hu => hAt k.1 u hu)
    (fun k u hu g hg => (hDiff _ (hAt k.1 u hu) _ _).1
      (GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 u hu g (Dfun u g) (Tk k.1 g)
        (Tk k.1 (Dfun u g)) ((hDiff u hu g _).2 rfl) ((hTacts k.1 k.2 g hg _).2 rfl)
        ((hTacts k.1 k.2 _ (hclos u hu g hg) _).2 rfl)))
    f hf
  exact ⟨S, hS, fun k hk f₁ hact => by rw [(hTacts k hk f hf f₁).1 hact]; exact hSk ⟨k, hk⟩⟩
end GlobalTheory.FockKFin
end

section
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.fock_vectors_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  first | exact @_root_.GlobalTheory.FockKFin.fock_space_kFinite | exact _root_.GlobalTheory.FockKFin.fock_space_kFinite | (intros; apply _root_.GlobalTheory.FockKFin.fock_space_kFinite <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
namespace GlobalTheory.RowEx
theorem twisted_linear_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) : LinB := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hsc hch a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.twisted_base_change_lift_exists hP hL large₂ hS ch hch CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ch.ξ _ (col_mem ch a) _ h2⟩
end GlobalTheory.RowEx
end
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
namespace GlobalTheory.LatStabVac
theorem lattice_vacuum_fixed_outside_finite_set : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.T.split_spherical_left_fixes_vacuum hP F E σ B a a' G X om om' hT
  obtain ⟨S₂, hS₂⟩ := _root_.GlobalTheory.T.split_vprime_stabilizer_fixes_vacuum hP F E σ B a a' G X om om' hT
  refine ⟨X.T ∪ S₁ ∪ S₂, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hvT, hv₁⟩, hv₂⟩ := hv
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hT.base v with hs | ⟨w, hw⟩
  · exact ⟨hS₁ v hv₁ hs, hS₂ v hv₂ hs⟩
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · exact GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hw hvT k hk 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v)
    · exact GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hT v w hw hvT k hk
end GlobalTheory.LatStabVac
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

theorem _root_.GlobalTheory.T.lattice_stabilizer_fixes_vacuum_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @_root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | exact _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | (intros; apply _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set <;> assumption)
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
namespace GlobalTheory.StabFinAdelic
theorem kappa_stabilized_of_isStabilizedW : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ g ∈ GfC X, ∀ ΦD ∈ N, om (1, kapX X e hO.JX g) ΦD ∈ N := by
  classical
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT Pi rf rl p p' _ N hN g hg Φ hΦ
  have hinf := GlobalTheory.InfKill.smul_mat_kapX_sub_one D X e hO.JX g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  have hfix : ∀ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, ∃ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
      T ⊆ S → S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∈ S, ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin D.host.F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w) →
      om (1, k) Ψ = Ψ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, φ, -, hφ, hcof, rfl⟩ := hx
      refine ⟨hcof.toFinset, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      refine (hS₀ S hS₀S k hk1 hk2 hk3 hk4).1 f φ hφ fun w hw => ?_
      by_contra hne
      exact hw (hTS (Set.Finite.mem_toFinset _ |>.2 hne))
    | zero => exact ⟨∅, fun _ _ _ k _ _ _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, h₁⟩ := hx
      obtain ⟨T₂, h₂⟩ := hy
      refine ⟨T₁ ∪ T₂, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      rw [map_add (f := _), h₁ S (Finset.union_subset_left hTS) hS₀S k hk1 hk2 hk3 hk4,
        h₂ S (Finset.union_subset_right hTS) hS₀S k hk1 hk2 hk3 hk4]
    | smul c x _ hx =>
      obtain ⟨T, hT'⟩ := hx
      exact ⟨T, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => by rw [map_smul, hT' S hTS hS₀S k hk1 hk2 hk3 hk4]⟩
  obtain ⟨T, hTfix⟩ := hfix Φ (hN.1 hΦ)
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T ∪ S₀)
  have hk : om (1, k) Φ = Φ :=
    hTfix S (Finset.union_subset_left hTS) (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Ψ, om (1, x * y) Ψ = om (1, x) (om (1, y) Ψ) := by
    intro x y Ψ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      ∀ Ψ ∈ N, om (1, (l'.map Prod.snd).prod) Ψ ∈ N := by
    intro l'
    induction l' with
    | nil =>
      intro _ Ψ hΨ
      simp only [List.map_nil, List.prod_nil]
      rw [Prod.mk_one_one, map_one]
      exact hΨ
    | cons x l' ih =>
      intro hx Ψ hΨ
      simp only [List.map_cons, List.prod_cons]
      rw [split']
      exact hN.2.1 x.1 x.2 (hx x List.mem_cons_self) _
        (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) Ψ hΨ)
  rw [hprod, split', hk]
  exact key l (fun x hx => (hl x hx).2) Φ hΦ
end GlobalTheory.StabFinAdelic
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

theorem _root_.GlobalTheory.T.finite_adelic_stabilizer_fixes_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ g ∈ GfC X, ∀ ΦD ∈ N, om (1, kapX X e hO.JX g) ΦD ∈ N := by
  first | exact @_root_.GlobalTheory.StabFinAdelic.kappa_stabilized_of_isStabilizedW | exact _root_.GlobalTheory.StabFinAdelic.kappa_stabilized_of_isStabilizedW | (intros; apply _root_.GlobalTheory.StabFinAdelic.kappa_stabilized_of_isStabilizedW <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain
open scoped TensorProduct
theorem GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM
  have hiff := GlobalTheory.T.polynomialMatch_zero_iff_pureTensor_image_zero F E σ Bs a a' G Xc om om' R Rf hM
  obtain ⟨h00, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs G Xc om om' R Rf hM.fin
  let K : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        simpa using hlin x y 0 0 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h00⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by
        simpa using hlin 0 x 0 0 c h00 hx.2⟩ }
  have memK : ∀ Φ, Φ ∈ K ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf Φ := fun Φ =>
    ⟨fun h => (hiff Φ).1 h.2, fun h => ⟨GlobalTheory.PolKer.algD_of_polZero Bs G Xc R Rf Φ h, (hiff Φ).2 h⟩⟩
  have one_W : ∀ v, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) := by
    intro v u _; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]
  refine ⟨K, ⟨⟨fun Φ h => h.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro v h hh Φ hΦ
    exact (memK _).2 (GlobalTheory.T.finitePlace_unitaryPoint_keeps_zeroMatchedData F E σ Bs a a' G Xc om om' R Rf hM v h hh Φ ((memK Φ).1 hΦ))
  · intro k hk Φ hΦ
    exact (memK _).2 (_root_.GlobalTheory.T.polarization_kernel_compact_vanishing hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ ((memK Φ).1 hΦ))
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (_root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ ((memK Φ).1 hΦ) hd)
  · intro v g hg Φ hΦ
    exact (memK _).2 (GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero F E σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ)
  · intro k hk Φ hΦ
    exact (memK _).2 (_root_.GlobalTheory.T.maximalCompact_invariants_polynomialKernel hP F E σ Bs a a' G Xc om om' R Rf hM k hk Φ hΦ)
  · intro γ hγ Φ hΦ Φ₁ _ hd
    exact (memK _).2 (_root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel_dualSpace hP F E σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd)
  · intro hK
    obtain ⟨Φ, hΦ, hn⟩ := GlobalTheory.T.exists_algebraicDatum_not_matched_zero F E σ Bs a a' G Xc om om' R Rf hM
    rw [← hK] at hΦ
    exact hn ((memK Φ).1 hΦ)
  · intro ΦD hΦD
    exact ⟨fun h => h.2, fun h => ⟨hΦD, h⟩⟩
end

section
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.thetaSubspace_contains_polKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  first | exact @_root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match | exact _root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match | (intros; apply _root_.GlobalTheory.PolKer.polKernel_eq_thetaSubspace_of_match <;> assumption)
end
end
