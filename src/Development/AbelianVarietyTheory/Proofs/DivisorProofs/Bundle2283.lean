module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotent
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Petersson Formalism.L2.Host
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ComplexConjugate

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem measurable_chart_prod {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Measurable fun p : GA E a × Lie E a => chart φ p.1 p.2 := by
  classical
  have e : (fun p : GA E a × Lie E a => chart φ p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart φ p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ Set.univ ×ˢ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      have hp' : ¬ IsUnit (Matrix.of p.2) := fun h => hp ⟨trivial, h⟩
      exact dif_neg hp'
  rw [e]
  exact (GlobalTheory.ConstTermSmooth.continuousOn_chart hφ).measurable_piecewise continuousOn_const
    (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun p : GA E a × Lie E a => chart F p.1 p.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem IsRapidInf.integrable_norm {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable (fun x => ‖k x‖) ν := by
  simpa using hk.2.2 0

theorem kerInf_mem_bddForms {ω : HChar E} {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) {X : Type} [MeasurableSpace X]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · set_option synthInstance.maxHeartbeats 200000 in
    refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (hm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_mul_const _)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [kerInf, mul_assoc, h.2.1]
  · rw [kerInf, kerInf, ← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left {ω : HChar E} (hω : ω.IsUnitary) {F ψ : GA E a → ℂ} (h : F ∈ bddForms E a ω)
    (h' : ψ ∈ bddForms E a ω) {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    pet (latticeGL E a) μ (kerInf ν k γ F) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI hFin : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  haveI : SFinite (μ.restrict (stdDom (latticeGL E a))) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hFin)
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki).mono'
      (((hk.1.comp measurable_snd).mul hm).mul
        ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)).aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms h hk) h' hD).2]
  simp only [kerInf, ← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem rspan_central {π : CuspSub E a} {ω : HChar E} (hπ : π.HasCentChar ω) {F : GA E a → ℂ} (hF : F ∈ rspan π)
    (z : Ideles E) (g : GA E a) :
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g := by
  have hc := CuspSub.hasCentral_iff.2 hπ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (z : Ideles E) g, F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
      add_mem' := fun {F F'} hF hF' z g => by simp only [Pi.add_apply, hF z g, hF' z g, mul_add]
      zero_mem' := fun z g => by simp
      smul_mem' := fun c F hF z g => by simp only [Pi.smul_apply, smul_eq_mul, hF z g]; ring }
  refine rspan_le (S := S) (fun φ hφ z g => hc.apply hφ z g) (fun F hF h z g => ?_)
    (fun F hF X _ ν _ k γ _ z g => ?_) hF z g
  · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
    rw [mul_assoc]; exact hF z _
  · change ∫ x, k x * F (GeneralLinearGroup.scalar (Fin a) z * g * infGL E a (γ x)) ∂ν =
      _ * ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
    rw [← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, hF z]; ring

theorem pet_rt_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0) {φ : Sm E a} (hφ : φ ∈ π.V)
    (h : GA E a) : pet (latticeGL E a) μ (fun g => φ.1 (g * h)) ψ = 0 := by
  have hb : ∀ φ ∈ π.V, φ.1 ∈ bddForms E a ω := fun φ hφ =>
    mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
  rw [← infGL_mul_finGL h]
  have e : (fun g => φ.1 (g * (infGL E a (GeneralLinearGroup.map (pInf E) h) *
      finGL E a (GeneralLinearGroup.map (pFin E) h)))) =
      fun g => (finRep E a (GeneralLinearGroup.map (pFin E) h) φ).1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h)) := by
    funext g
    change _ = φ.1 (g * infGL E a _ * finGL E a _)
    rw [mul_assoc]
  rw [e]
  exact GlobalTheory.KeepOrth.pet_translate_eq_zero μ hω hψ hb (fun X => π.stable (.lie X)) (fun φ hφ => (π.cusp φ hφ).1) h0
    (π.stable (.fin _) φ hφ) _

theorem rspan_bdd_pet_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω)
    {ψ : GA E a → ℂ} (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0)
    {F : GA E a → ℂ} (hF : F ∈ rspan π) :
    F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0 := by
  have hψh : ∀ h : GA E a, (fun g => ψ (g * h)) ∈ bddForms E a ω := mul_right_mem_bddForms hψ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun h => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hψh h), hF.2 h, hF'.2 h, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun h => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun h => by
        rw [pet_smul_left, hF.2 h, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h' : GA E a, (fun g => F (g * h')) ∈ S := fun F hF h' =>
    ⟨mul_right_mem_bddForms hF.1 h', fun h => by
      rw [pet_mul_right_left μ hω hF.1 (hψh h) h']
      have := hF.2 (h'⁻¹ * h)
      simp only [mul_assoc] at this ⊢
      exact this⟩
  refine rspan_le (S := S) (fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun h => ?_⟩) htr (fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hF.1 hk, fun h => ?_⟩) hF
  · have hb := mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
    have e := pet_mul_right_left μ hω hb hψ h⁻¹
    rw [inv_inv] at e
    rw [← e]
    exact pet_rt_eq_zero μ hω hπ hψ h0 hφ h⁻¹
  · rw [pet_kerInf_left μ hω hF.1 (hψh h) ν hk]
    exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 h))

end GlobalTheory.JSW
end
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed (Xo := Xo) (c := c) → ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  first | exact @GlobalTheory.FlatCore.archSec_exists_eq_smul | exact GlobalTheory.FlatCore.archSec_exists_eq_smul | (intros; apply GlobalTheory.FlatCore.archSec_exists_eq_smul <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nonSplitPlace_stabilizer_fixes_latticeVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (H : Geo.Tor.Host D.host.E) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f, IsThetaFunO ψ V W f → IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f → ∀ v ε (k : GA D W), GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.SuppPl ε W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = f ∧ (V.rank ≠ 0 → mu k = 1) := by
  first | exact @GlobalTheory.AdTh.nonSplit_fixes_latVac | exact GlobalTheory.AdTh.nonSplit_fixes_latVac | (intros; apply GlobalTheory.AdTh.nonSplit_fixes_latVac <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem isClosed_fixG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k : ℕ} (C : Matrix (Fin n) (Fin k) E) :
    IsClosed ((fixG σ J C : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  exact isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const

theorem finCovol_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF π DM hπ hDM
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_homeomorph_columnFixator_coreUnitaryGroup F E σ n J j m C D Z J₀ hF
  have hcl : IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) :=
    (isClosed_fixG σ J C).inter (isClosed_fixG σ J D)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := hcl.locallyCompactSpace
  haveI : Countable (ratPts σ J₀) := inferInstance
  exact GlobalTheory.T.covolume_ne_top_of_continuousMulEquiv_subgroup (GAd σ J₀) _ e (ratPts σ J₀) _ (fun g => by rw [he g]; rfl)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteVolume_adelicUnitaryQuotient F E σ hF.cm m J₀ hF.herm₀ μ hμ 𝓕 h𝓕) π DM hπ hDM

end GlobalTheory.SphEis
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.double_splitting_pair_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → ∀ v : Pl (F := F), GlobalTheory.DblScal.LocOps omd v := by
  first | exact @GlobalTheory.DblScal.LocAt.locOps | exact GlobalTheory.DblScal.LocAt.locOps | (intros; apply GlobalTheory.DblScal.LocAt.locOps <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
open Matrix
namespace GlobalTheory.VacScalar

theorem hTens_eq_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hTens_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (A : Matrix α α E)
    (Bm : Matrix β β E) (hA : Aᵀ * JA * A.map c = JA) (hB : Bmᵀ * JB * Bm.map c = JB) (x y : Matrix α β E) :
    hTens c JA JB (A * x * Bmᵀ) (A * y * Bmᵀ) = hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (A * y * Bmᵀ).map c = A.map c * y.map c * (Bm.map c)ᵀ := by
    rw [show (A * y * Bmᵀ).map c = (A * y).map c * (Bmᵀ).map c from Matrix.map_mul (f := c.toRingHom),
      show (A * y).map c = A.map c * y.map c from Matrix.map_mul (f := c.toRingHom), Matrix.transpose_map]
  have e2 : (Bm.map c)ᵀ * JBᵀ * Bm = JBᵀ := by
    conv_rhs => rw [← hB]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = Matrix.trace (Bm * (xᵀ * (Aᵀ * JA * A.map c) * y.map c * ((Bm.map c)ᵀ * JBᵀ))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (xᵀ * JA * y.map c * ((Bm.map c)ᵀ * JBᵀ) * Bm) := by rw [hA, Matrix.trace_mul_comm]
    _ = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by rw [Matrix.mul_assoc _ _ Bm, e2]

theorem symp_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (k : UG c JA × UG c JB) (x : Matrix α β E) :
    symp c ξ JA JB (actAB c k x) (actAB c k x) = symp c ξ JA JB x x := by
  simp only [symp, actAB]
  rw [hTens_act c JA JB _ _ k.1.2 k.2.2]


open Classical in
theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (w : Pl (F := F))
    (c : ℂ) : pure f (Function.update φ w (c • φ w)) = c • pure f φ := by
  funext x
  have h1 := GlobalTheory.PureFactor.finprod_update φ w (c • φ w) hstd x
  have h2 := GlobalTheory.PureFactor.finprod_update φ w (φ w) hstd x
  rw [Function.update_eq_self] at h2
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem std_of_vac {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} (hG : G.IsGood B) (S : Finset (Pl (F := F)))
    (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hG.hM'.std, S.finite_toSet.compl_mem_cofinite] with v hv hvS
  rw [hvac v hvS, hv]

theorem pure_eigen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a')))
    (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w))
    (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) (w : Pl (F := F)) (hw : w ∉ S) :
    ∃ θ : 𝓞 E, ∀ γ ∈ latAtV G.V' G.W w, G.M'.co.rho B.ψ γ (pure f φ) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) •
        pure f φ := by
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac w
  refine ⟨θ, fun γ hγ => ?_⟩
  have hstd := std_of_vac hT.geo S φ hvac
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have e := GlobalTheory.ThK.LocalOps.acts_pure w (G.M'.co.rho B.ψ γ) f φ _ hΦ
    (fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x) (by rw [hvac w hw]; exact hθ γ hγ)
  rw [e, ← hvac w hw, pure_update_smul f φ hstd]
  rfl

theorem scalar_of_trivial : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, (mat g * γ * Matrix.transpose (mat h) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∃ c : ℂ, om' (g, h) (pure f φ) = c • pure f φ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS hlat f φ hSB hvac
  have hstd := std_of_vac hT.geo S φ hvac
  have hΦ : pure f φ ∈ schA F (Fin a' × Fin (a + a')) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hi : ∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ →
      G.M'.co.rho B.ψ γ (om' (g, h) (pure f φ)) = c • om' (g, h) (pure f φ) := by
    intro w hw γ hγ c hc
    obtain ⟨θ, hθ⟩ := pure_eigen hT S f φ hSB hvac w hw
    set γ' := actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((g, h)⁻¹) γ with hγ'def
    have e1 : mat g * mat g⁻¹ = 1 := by
      show (g * g⁻¹).1.1 = 1
      rw [mul_inv_cancel]; rfl
    have e2 : mat h * mat h⁻¹ = 1 := by
      show (h * h⁻¹).1.1 = 1
      rw [mul_inv_cancel]; rfl
    have hact : actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (g, h) γ' = γ := by
      change mat g * (mat g⁻¹ * γ * (mat h⁻¹)ᵀ) * (mat h)ᵀ = γ
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2,
        Matrix.transpose_one, Matrix.mul_one]
    have hγ' : γ' ∈ latAtV G.V' G.W w := (hlat w hw γ').1 (by change actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (g, h) γ' ∈ _; rw [hact]; exact hγ)
    have e3 := hW.impl (g, h) γ' (pure f φ) hΦ
    erw [hact] at e3
    have hsym : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ' γ' =
        symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ := by
      erw [← symp_act (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) _ _ _ (g, h) γ', hact]
      rfl
    erw [← e3, hθ γ' hγ', map_smul, hsym]
    by_cases hΦ0 : pure f φ = 0
    · rw [hΦ0, map_zero, smul_zero, smul_zero]
    · rw [hθ γ hγ] at hc
      rw [smul_left_injective ℂ hΦ0 hc]
  have hTΦ : om' (g, h) (pure f φ) ∈ schA F (Fin a' × Fin (a + a')) := hW.pres (g, h) _ hΦ
  obtain ⟨m, f', φ', hSB', hvac', heq⟩ := GlobalTheory.T.theta_series_factorizable_restriction hP F E σ B a a' G X om om' hT S f φ hSB hvac _ hTΦ hi
  have hco := GlobalTheory.T.theta_kernel_archimedean_unipotent_support F E σ B a a' G X om om' hT S g h hgI hhI hgS hhS (pure f φ) hΦ
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_series_factorizable_restriction_finite hP F E σ B a a' G X om om' hT S f φ hSB hvac m f' φ' hSB' hvac'
    (fun u hu μ hμ => by rw [← heq]; exact hco u hu μ hμ)
  exact ⟨c, heq.trans hc⟩

end GlobalTheory.VacScalar
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.isotropicEisensteinSeries_rationalPoints_permute_terms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
  first | exact @GlobalTheory.ResidueEisenstein.reps_perm | exact GlobalTheory.ResidueEisenstein.reps_perm | (intros; apply GlobalTheory.ResidueEisenstein.reps_perm <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.leviCentreFlow_conj_scales_haar_isotropicUnipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ b, IsFlowJ σ J X Y b → ∀ ν : Measure (unipRad σ J X), ν.IsHaarMeasure → ∀ (t : ℝ) (f : GAd σ J → ℝ≥0∞), Measurable f → ∫⁻ u : unipRad σ J X, f (b t * u * (b t)⁻¹) ∂ν = ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * t))) * ∫⁻ u : unipRad σ J X, f u ∂ν := by
  first | exact @GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow | exact GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow | (intros; apply GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  first | exact @GlobalTheory.IdxMap.idx_map_eq_colon_dets | exact GlobalTheory.IdxMap.idx_map_eq_colon_dets | (intros; apply GlobalTheory.IdxMap.idx_map_eq_colon_dets <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  first | exact @GlobalTheory.HorFrame.exists_basicOpen_det_ks | exact GlobalTheory.HorFrame.exists_basicOpen_det_ks | (intros; apply GlobalTheory.HorFrame.exists_basicOpen_det_ks <;> assumption)
end
