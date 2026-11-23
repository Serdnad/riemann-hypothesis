module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_blockDiagonalEmbedding_le_mul : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  first | exact @GlobalTheory.BlockHeight.ht_blkU_le | exact GlobalTheory.BlockHeight.ht_blkU_le | (intros; apply GlobalTheory.BlockHeight.ht_blkU_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors


theorem _root_.GlobalTheory.T.scaledBlockSum_selfDual_traceSkewForm : ∀ {D : D7}, (∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) → ∀ (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e ↔
      ∀ x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) := by
  first | exact @GlobalTheory.SkewLat.pairLat_trace_selfDual | exact GlobalTheory.SkewLat.pairLat_trace_selfDual | (intros; apply GlobalTheory.SkewLat.pairLat_trace_selfDual <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacIso

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW t (cA σ x) = piW (t.comp σ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem eq_zero_of_at_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v)
    {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) (h1 : piW τ z = 0) (h2 : piW (τ.comp σ) z = 0) : z = 0 := by
  have hc : compFin F E v z = 0 :=
    GlobalTheory.AdelicU.split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  have e := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at e
  rw [e, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  change GlobalTheory.EmbChart.tensAt E v ((1 : Fv F v) ⊗ₜ[F] (1 : E)) * z = 0
  rw [GlobalTheory.EmbChart.tensAt_mul_right, hc, mul_zero, map_zero]

theorem symp_self_eq_zero : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E),
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  intro D a a' Bs Γ X om om' hTr u hu hpi ξ
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := hTr.base.cm
  set z := GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u with hzdef
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) z := by
    intro c hc
    have hij : ∀ i j, c • u i j = 0 := fun i j => by
      have := congrFun (congrFun (hu c hc) i) j
      simpa using this
    simp only [hzdef, GlobalTheory.WeilM.hTens, Finset.smul_sum, ← smul_mul_assoc, hij, zero_mul, Finset.sum_const_zero]
  have first : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁, (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (u i j) = 0) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht

    simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, ht, zero_mul, Finset.sum_const_zero]
  have last : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁,
      (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp D.sp.cm.sig) (u i j) = 0) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht

    simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, GlobalTheory.VacIso.piW_cA, ht, mul_zero, Finset.sum_const_zero]
  have hz0 : z = 0 := by
    rcases hpi with h0 | h0
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁ (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      refine GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (first _ h0') (last _ ?_)
      rw [GlobalTheory.AdelicU.comp_conj_conj hcm]; exact h0'
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig) (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      exact GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (last _ h0') (first _ h0')
  simp only [GlobalTheory.WeilM.symp, ← hzdef, hz0, mul_zero, map_zero]

end GlobalTheory.VacIso
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.AdelicPush

open GlobalTheory.AdelicU

theorem lintegral_tens_eq_const_mul : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (r : (κ → AF F) → ℂ),
    @Measurable _ _ (borel _) _ r →
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) →
    ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ K : Set (κ → Fv F v), IsCompact K → (interior K).Nonempty →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : (κ → Fv F v) → ℂ, Continuous φ → HasCompactSupport φ →
      ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ v r hr hinv μA hμA μ hμ K hK hKi hK0 hKt
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have hcont : Continuous (evFin F v) := by
    change Continuous fun a => _
    exact (PI.LevelKSplit.W.Cont.continuous_evalV v).comp continuous_snd
  let evK : (κ → AF F) → (κ → Fv F v) := fun x i => evFin F v (x i)
  have hevKm : Measurable evK := (continuous_pi fun i => hcont.comp (continuous_apply i)).measurable
  let ρ : (κ → AF F) → ENNReal := fun x => ‖r x‖ₑ ^ 2
  have hρ : Measurable ρ := hr.enorm.pow_const 2
  let ν : Measure (κ → Fv F v) := (μA.withDensity ρ).map evK
  have hνA : ∀ A, MeasurableSet A → ν A = ∫⁻ x, A.indicator 1 (evK x) * ρ x ∂μA := by
    intro A hA
    rw [Measure.map_apply hevKm hA, withDensity_apply _ (hevKm hA), ← lintegral_indicator (hevKm hA)]
    refine lintegral_congr fun x => ?_
    by_cases h : evK x ∈ A <;> simp [Set.indicator, h]
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro y
    ext A hA
    rw [Measure.map_apply (measurable_const_add y) hA, hνA _ hA, hνA _ (measurable_const_add y hA)]
    let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
    have hev : ∀ x, evK (x + z) = y + evK x := fun x => funext fun i => by
      simp [evK, z, GlobalTheory.LatVac.evFin_liftV, add_comm]
    rw [← lintegral_add_right_eq_self (fun x => A.indicator 1 (evK x) * ρ x) z]
    refine lintegral_congr fun x => ?_
    simp only [hev, ρ, hinv x z hz]
    by_cases h : y + evK x ∈ A <;> simp [Set.indicator, h]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  haveI : ν.IsAddHaarMeasure := Measure.isAddHaarMeasure_of_isCompact_nonempty_interior ν K hK hKi
    (by rw [hνA K hKm]; exact hK0) (by rw [hνA K hKm]; exact hKt)
  have hsc : ∀ s : Set (κ → Fv F v), IsCompact (closure s) →
      ν s = (Measure.addHaarScalarFactor ν μ : ENNReal) * μ s := fun s hs => by
    rw [Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ hs, ENNReal.smul_def, smul_eq_mul]
  refine ⟨(Measure.addHaarScalarFactor ν μ : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · intro h0
    have := hsc K (by rw [hK.isClosed.closure_eq]; exact hK)
    rw [h0, zero_mul, hνA K hKm] at this
    exact hK0 this
  intro φ hφ hφc
  set C : ENNReal := (Measure.addHaarScalarFactor ν μ : ENNReal)
  let T := tsupport φ
  have hrest : ν.restrict T = C • μ.restrict T := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact hsc _ (hφc.isCompact.of_isClosed_subset isClosed_closure
      (closure_minimal Set.inter_subset_right (isClosed_tsupport φ)))
  have hf : Measurable fun y => ‖φ y‖ₑ ^ 2 := hφ.measurable.enorm.pow_const 2
  have hsupp : Function.support (fun y => ‖φ y‖ₑ ^ 2) ⊆ T := by
    intro y hy
    by_contra h
    exact hy (by simp [image_eq_zero_of_notMem_tsupport h])
  calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA
      = ∫⁻ x, (ρ * fun x => (fun y => ‖φ y‖ₑ ^ 2) (evK x)) x ∂μA := by
        refine lintegral_congr fun x => ?_
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.mul_apply, ρ, evK, enorm_mul, mul_pow, mul_comm]
    _ = ∫⁻ x, (fun y => ‖φ y‖ₑ ^ 2) (evK x) ∂(μA.withDensity ρ) :=
        (lintegral_withDensity_eq_lintegral_mul _ hρ (hf.comp hevKm)).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂ν := (lintegral_map hf hevKm).symm
    _ = ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂ν := (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(C • μ.restrict T) := by rw [hrest]
    _ = C * ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂μ := lintegral_smul_measure _ _
    _ = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by rw [setLIntegral_eq_of_support_subset hsupp]

end GlobalTheory.AdelicPush

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmallAtPlace

open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem smul_tens_single (v : HeightOneSpectrum (𝓞 F)) {u : AF F} (hu : evFin F v u = 0)
    (h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b)
    (z : Fv F v ⊗[F] E) :
    u • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) z) = 0 := by
  have key : ∀ b : AF F, u * b = 0 → ∀ e : E, u • (b ⊗ₜ[F] e : AF F ⊗[F] E) = 0 := fun b hb e => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, hb, TensorProduct.zero_tmul]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy, add_zero]
  | tmul a e =>
    let b : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v a)
    have hb : u * b = 0 := by
      refine Prod.ext (mul_zero _) ?_
      show u.2 * singleFin v a = 0
      refine _root_.GlobalTheory.AdelicU.af_ext fun t => ?_
      rw [map_mul, map_zero]
      by_cases ht : t = v
      · subst ht
        have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [evalV_singleFin_ne ht, mul_zero]
    exact key b hb e


omit [NumberField E] in
theorem smul_mat_emb_sub_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x : GLoc σ J v) {u : AF F} (hu : evFin F v u = 0) :
    u • ((HA.mat (AF F) σ J (emb σ J v x)).1 - 1) = 0 := by
  ext r s
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  have h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b :=
    fun _ _ => Prod.ext (mul_zero _).symm rfl
  have hm := GlobalTheory.AutFunCompare.mat_extH σ J (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
    (embLocFin σ J v x) r s
  have hm2 := GlobalTheory.AutFunCompare.mat_extH σ J (singleFin v) (singleFin_mul v) x r s
  have e1 : (HA.mat (AF F) σ J (emb σ J v x)).1 r s = _ := hm
  have e2 : (HA.mat (Af F) σ J (embLocFin σ J v x)).1 r s = _ := hm2
  rw [e1, e2]
  set T1 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
  set T2 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (singleFin v) (singleFin_mul v)
  have key : ∀ z, u • T1 (T2 z) = 0 := smul_tens_single v hu h1
  have : (1 - T1 1) * (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s +
      T1 ((1 - T2 1) * (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) r s + T2 ((HA.mat _ σ J x).1 r s)) -
      (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s =
      T1 (T2 ((HA.mat _ σ J x).1 r s - (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r s)) := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one, map_add (f := _), map_sub, map_sub, map_sub]
      abel
    · simp only [Matrix.one_apply_ne h, mul_zero, zero_add, sub_zero, map_zero]
  rw [this]
  exact key _

omit [NumberField E] in
theorem map_smul_of_eq_one {R : Type} [CommRing R] [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1)
    (y : AF F ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (a • y) = Algebra.TensorProduct.map ψ (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul,
      map_mul, ha, one_mul]

omit [NumberField E] in
theorem mapH_eq_one_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {R : Type} [CommRing R]
    [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1) {g : GAd σ J}
    (hg : a • ((HA.mat (AF F) σ J g).1 - 1) = 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J ψ g = 1 := by
  refine GlobalTheory.AutFunCompare.HA_ext σ J fun r s => ?_
  rw [GlobalTheory.AutFunCompare.mat_mapH]
  have h := congrArg (Algebra.TensorProduct.map ψ (AlgHom.id F E)) (congrFun (congrFun hg r) s)
  rw [Matrix.smul_apply, Matrix.sub_apply, map_smul_of_eq_one ψ ha, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h
  rw [h]
  show _ = (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s
  by_cases e : r = s
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, map_zero]


omit [NumberField E] in
theorem eq_emb_proj_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {g : GAd σ J} (hg : ∀ u : AF F, evFin F v u = 0 → u • ((HA.mat (AF F) σ J g).1 - 1) = 0) :
    g = emb σ J v (proj σ J v g) := by
  refine GAd_ext σ J (fun w => ?_) (fun u => ?_)
  · rw [projArch_emb]
    let a : AF F := ((1 : Ainf F), (0 : Af F))
    have h1 : evInf F w a = 1 := by
      show (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
      exact map_one _
    have h0 : evFin F v a = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (0 : Af F) = 0
      exact map_zero _
    exact mapH_eq_one_of_smul σ J (evInf F w) h1 (hg a h0)
  · by_cases h : u = v
    · subst h; rw [proj_emb_self]
    · rw [proj_emb_ne σ J h]
      let a : AF F := ((0 : Ainf F), singleFin u 1)
      have h1 : evFin F u a = 1 := evalV_singleFin_self u 1
      have h0 : evFin F v a = 0 := evalV_singleFin_ne (Ne.symm h) 1
      exact mapH_eq_one_of_smul σ J (evFin F u) h1 (hg a h0)

theorem exists_compact_subgroup_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  intro F E _ _ _ _ _ σ hσ n X v U hU
  have heq : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) = HR (AF F) σ (X.J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J ≃* GAd σ (X.J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let f : GLoc σ (X.J.map σ) v →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J := e.symm.toMonoidHom.comp (emb σ (X.J.map σ) v)
  have hf : Continuous f := he'.comp (continuous_emb σ (X.J.map σ) v)
  have hW : f ⁻¹' U ∈ 𝓝 (1 : GLoc σ (X.J.map σ) v) :=
    hf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ (X.J.map σ) v
  obtain ⟨V₀, hV₀⟩ := NonarchimedeanGroup.is_nonarchimedean _ hW
  haveI := isLattice_stdLattice (E := E) (n := n)
  let V₁ : Subgroup (GLoc σ (X.J.map σ) v) := (V₀ : Subgroup _) ⊓ stabLoc σ (X.J.map σ) (stdLattice E n) v
  have hV₁o : IsOpen (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    V₀.isOpen.inter (isOpen_stabLoc σ (X.J.map σ) (stdLattice E n) v)
  have hV₁c : IsCompact (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    (isCompact_stabLoc σ (X.J.map σ) (stdLattice E n) v).inter_left V₀.isClosed
  have hmat : ∀ g, (HA.mat (AF F) σ (X.J.map σ) (e g)).1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := fun g => rfl
  refine ⟨V₁.map f, ?_, ?_, ⟨(proj σ (X.J.map σ) v ∘ e) ⁻¹' (V₁ : Set _),
    hV₁o.preimage ((continuous_proj σ (X.J.map σ) v).comp he), ?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩ u hu
    have h := smul_mat_emb_sub_one σ (X.J.map σ) v x hu
    have h2 : (HA.mat (AF F) σ (X.J.map σ) (e (f x))).1 = (HA.mat (AF F) σ (X.J.map σ) (emb σ (X.J.map σ) v x)).1 := by
      simp [f]
    rw [← hmat, h2]
    exact h
  · rw [Subgroup.coe_map]
    exact hV₁c.image hf
  · show proj σ (X.J.map σ) v (e 1) ∈ V₁
    rw [map_one, map_one]
    exact one_mem _
  · intro g hg hgv
    refine ⟨proj σ (X.J.map σ) v (e g), hg, ?_⟩
    have h : e g = emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g)) :=
      eq_emb_proj_of_smul σ (X.J.map σ) v fun u hu => by rw [hmat]; exact hgv u hu
    show e.symm (emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g))) = g
    rw [← h, MulEquiv.symm_apply_apply]
  · rintro _ ⟨x, hx, rfl⟩
    exact hV₀ hx.1

end GlobalTheory.SmallAtPlace
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) : AddSubgroup (Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) where
  carrier := {z | z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v}
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem (latAtV X W v), zero_mem (latAtV X W v)⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, neg_mem ha.2⟩

theorem mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    z ∈ latDbl X W v ↔ z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v := Iff.rfl

theorem fromCols_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {γ₁ γ₂ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (h₁ : γ₁ ∈ latAtV X W v) (h₂ : γ₂ ∈ latAtV X W v) : Matrix.fromCols γ₁ γ₂ ∈ latDbl X W v := by
  rw [mem_latDbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
  exact ⟨h₁, h₂⟩

theorem at_of_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {z : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hz : z ∈ latDbl X W v) : At (evFin F v) z := by
  intro u hu
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.1 u hu
  have h2 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.2 u hu
  ext i (j | j)
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

end GlobalTheory.DblVacEigen
end
end
