module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F]

theorem isOp_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp ψ s S S') (ht : IsOp ψ t T T') : IsOp ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  exact
    { pres φ h := ht.pres _ (hs.pres φ h)
      pres' φ h := hs.pres' _ (ht.pres' φ h)
      left φ h := by simp only [LinearMap.comp_apply]; rw [ht.left _ (hs.pres φ h), hs.left φ h]
      right φ h := by simp only [LinearMap.comp_apply]; rw [hs.right _ (ht.pres' φ h), ht.right φ h]
      adm l hl := by rw [← LinearMap.comp_assoc]; exact hs.adm _ (ht.adm l hl)
      adm' l hl := by rw [← LinearMap.comp_assoc]; exact ht.adm' _ (hs.adm' l hl)
      Heisenberg₂ w φ h := by
        simp only [LinearMap.comp_apply, Function.comp_apply]
        rw [hs.Heisenberg₂ w φ h, ht.Heisenberg₂ _ _ (hs.pres φ h)]
      theta := by
        obtain ⟨c₁, hc₁, e₁⟩ := hs.theta
        obtain ⟨c₂, hc₂, e₂⟩ := ht.theta
        exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun φ h => by
          simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩
      norm μ μ'' hμ hμ'' := by
        letI : MeasurableSpace (κ' → AF F) := borel _
        haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
        haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
        obtain ⟨c₁, h1, h1', e₁⟩ := hs.norm μ Measure.addHaar hμ inferInstance
        obtain ⟨c₂, h2, h2', e₂⟩ := ht.norm Measure.addHaar μ'' inferInstance hμ''
        exact ⟨c₂ * c₁, mul_ne_zero h2 h1, ENNReal.mul_ne_top h2' h1', fun φ h => by
          simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩ }

theorem dblAct_comp {κ κ' κ'' : Type} (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) :
    dblAct (t ∘ s) = dblAct t ∘ dblAct s := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem isOp2_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp2 ψ s S S') (ht : IsOp2 ψ t T T') : IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  obtain ⟨hs1, Sd, Sd', hsd, hsb⟩ := hs
  obtain ⟨ht1, Td, Td', htd, htb⟩ := ht
  have hc : ∀ {ι : Type} [Fintype ι], ∀ φ ∈ schA F ι, star φ ∈ schA F ι := fun φ h => GlobalTheory.ConjSch.conj_mem_schA φ h
  refine ⟨isOp_comp hs1 ht1, Td ∘ₗ Sd, Sd' ∘ₗ Td', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · rw [dblAct_comp]; exact isOp_comp hsd htd
  · simp only [LinearMap.comp_apply]
    rw [hsb φ₁ h₁ φ₂ h₂, htb _ (hs1.pres _ h₁) _ (hc _ (hs1.pres _ (hc _ h₂))), star_star]

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

def addRe {X : Type} [TopologicalSpace X] [AddCommGroup X] (e : κ' ≃ κ) : (κ' → X) ≃ₜ+ (κ → X) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

def reix {R : Type} (e : κ' ≃ κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : κ' → R => x ∘ e.symm)

theorem reix_apply {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e.symm) := rfl

theorem reix_symm_reix {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) : reix e.symm (reix e φ) = φ := by
  funext x; simp only [reix_apply, Equiv.symm_symm]; congr 1; funext i; simp

def linRe (e : κ' ≃ κ) : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e.symm).toContinuousLinearEquiv

theorem sb_reix (e : κ' ≃ κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y : κ' → FiniteAdeleRing (𝓞 F) F => g (y ∘ e.symm)) ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) :=
  ⟨hg.1.comp_continuous (addRe e).continuous, hg.2.comp_homeomorph (addRe e).toHomeomorph⟩

theorem reix_pureA (e : κ' ≃ κ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    reix e (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e) f)
      (fun y => g (y ∘ e.symm)) := by
  funext x
  rfl

theorem reix_mem_schA (e : κ' ≃ κ) {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have hle : schA F κ ≤ (schA F κ').comap (reix e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, _, sb_reix e hg, reix_pureA e f g⟩
  exact hle h

theorem reix_adm (e : κ' ≃ κ) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ reix e ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl _ (sb_reix e hg)
  exact ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e)), fun f => by
    rw [LinearMap.comp_apply, reix_pureA]; exact hT _⟩

theorem reix_theta (e : κ' ≃ κ) (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AF F) (ξ i)))

theorem reix_heis (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    reix e (schr ψ w φ) = schr ψ (w.1 ∘ e, w.2 ∘ e) (reix e φ) := by
  have hd : ∀ u v : κ → AF F, (u ∘ e) ⬝ᵥ (v ∘ e) = u ⬝ᵥ v := fun u v => by
    simp only [dotProduct, Function.comp_apply]; exact Equiv.sum_comp e (fun i => u i * v i)
  funext x
  simp only [reix_apply, schr]
  have h1 : (x ∘ e.symm) ⬝ᵥ w.2 = x ⬝ᵥ (w.2 ∘ e) := by
    rw [← hd]; congr 1; funext i; simp
  have h2 : x ∘ e.symm + w.1 = (x + w.1 ∘ e) ∘ e.symm := by funext i; simp
  rw [h1, h2, hd]

theorem reix_norm (e : κ' ≃ κ) (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (hμ' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : (κ → AF F) → ℂ,
      ∫⁻ x, ‖reix e φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  letI : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  haveI := hμ'
  let L : (κ' → AF F) ≃ₜ+ (κ → AF F) := addRe e
  haveI : (μ'.map L).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ' L
  have heq := Measure.isAddLeftInvariant_eq_smul (μ'.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ'.map L) μ : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top,
    fun φ => ?_⟩
  have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv (μ := μ')
  have hL : (⇑L.toHomeomorph.toMeasurableEquiv : (κ' → AF F) → (κ → AF F)) = ⇑L := rfl
  rw [hL, heq, lintegral_smul_measure] at hm
  rw [ENNReal.smul_def, smul_eq_mul] at hm
  exact hm.symm

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem isOp_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  exact
    { pres _ h := reix_mem_schA e h
      pres' _ h := reix_mem_schA e.symm h
      left φ _ := reix_symm_reix e φ
      right φ _ := by simpa using reix_symm_reix e.symm φ
      adm _ hl := reix_adm e hl
      adm' _ hl := reix_adm e.symm hl
      Heisenberg₂ w φ _ := reix_heis ψ e w φ
      theta := ⟨1, one_ne_zero, fun φ _ => by rw [reix_theta, one_mul]⟩
      norm μ μ' hμ hμ' := by
        obtain ⟨c, h0, h1, h⟩ := reix_norm e μ μ' hμ hμ'
        exact ⟨c, h0, h1, fun φ _ => h φ⟩ }

theorem dblAct_reix (e : κ' ≃ κ) :
    dblAct (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) =
      fun w => (w.1 ∘ Equiv.sumCongr e e, w.2 ∘ Equiv.sumCongr e e) := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

theorem isOp2_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp2 ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  refine ⟨isOp_reix ψ e, reix (Equiv.sumCongr e e), reix (Equiv.sumCongr e e).symm, ?_, fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_reix]; exact isOp_reix ψ _
  · funext x
    simp only [reix_apply, boxFun, Pi.star_apply, star_star]
    congr 2 <;> funext i <;> simp

theorem realised_comp_reix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' :=
  fun _ _ _ ψ _ => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hs ht => isOp2_comp hs ht, fun _ _ _ _ e => ⟨_, _, isOp2_reix ψ e⟩⟩

end GlobalTheory.TowU.RealComp

end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.continuousAt_transgressionTopCoeffComplex : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, ContDiffAt ℝ 1 ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → ContinuousAt (corrC ρ G₀ G₁) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_corrC | exact GlobalTheory.GoodTop.continuousAt_corrC | (intros; apply GlobalTheory.GoodTop.continuousAt_corrC <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (V n)) (G₀ : V n → Matrix r r ℂ) (ρ : V n → ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) U := by
  first | exact @GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | exact GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | (intros; apply GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem position_eq_update {n : ℕ} {α : Type} [Zero α] (K₁ L K₀ : α) (j : Fin n) :
    intersection_update_fsHerm_neg_one K₁ L K₀ j = Function.update (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) j L := by
  funext i
  by_cases h : i = j
  · subst h; simp [intersection_update_fsHerm_neg_one]
  · simp [intersection_update_fsHerm_neg_one, Function.update_of_ne h, h]

theorem mixTop_position_linear {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ L L' : EndValuedForm11Coeffs n r)
    (s t : ℂ) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ (s • L + t • L') K₀ j) = s * mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + t * mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
  rw [position_eq_update, position_eq_update K₁ L, position_eq_update K₁ L', GlobalTheory.T.polarisedTopChernCoeff_update_add, GlobalTheory.T.polarisedTopChernCoeff_update_smul, GlobalTheory.T.polarisedTopChernCoeff_update_smul]

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.topFormIntegral_add : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {s t : ℝ}, IsTopForm e d S → IsTopForm e d' S → HasInt e d S s → HasInt e d' S t → HasInt e (fun i y => d i y + d' i y) S (s + t) := by
  first | exact @GlobalTheory.GoodTop.hasInt_add | exact GlobalTheory.GoodTop.hasInt_add | (intros; apply GlobalTheory.GoodTop.hasInt_add <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d : κ → Y → ℝ} (e' : OpenPartialHomeomorph Y (V n)) (W : Set Y) (g : V n → ℝ), IsOpen W → W ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → IsTopForm e d S → (∀ i y, y ∈ S → y ∉ W → y ∈ (e i).source → d i y = 0) → (∀ j y, y ∈ S → y ∈ W → y ∈ (e j).source → g (e' y) = ‖transDet e' (e j) y‖ ^ 2 * d j y) → IntegrableOn g (e' '' (S ∩ W)) → HasInt e d S (∫ v in e' '' (S ∩ W), g v) := by
  first | exact @GlobalTheory.GoodTop.hasInt_of_chart | exact GlobalTheory.GoodTop.hasInt_of_chart | (intros; apply GlobalTheory.GoodTop.hasInt_of_chart <;> assumption)
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_changeFrame {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n} (h₀ : MContDiffAt 2 G₀ v) (u₀ : IsUnit (G₀ v).det)
    (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) (hA : MContDiffAt 2 A v) (hAu : IsUnit (A v).det)
    (hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) :
    corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  unfold corrC
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← GlobalTheory.T.polarisedTopChernCoeff_conj (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) (A v) hAu]
  congr 1
  funext i a b
  unfold intersection_update_fsHerm_neg_one
  split_ifs
  · exact curv_changeFrame h₁ u₁ hA hAu hA0 _ _
  · simp only [cutForm]
    rw [conn_changeFrame (h₁.of_le one_le_two) u₁ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      conn_changeFrame (h₀.of_le one_le_two) u₀ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      ← Matrix.mul_sub, add_sub_add_right_eq_sub, ← Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  · exact curv_changeFrame h₀ u₀ hA hAu hA0 _ _

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexConjugate

namespace GlobalTheory.GoodTop

theorem isSesq_eq_sum_coordVec {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {α : V n → V n → M}
    (hα : IsSesq α) (x y : V n) :
    α x y = ∑ c, ∑ d, (x c * conj (y d)) • α (coordVec c) (coordVec d) := by
  have hex : ∀ w : V n, w = ∑ a, w a • coordVec a := by
    intro w
    ext i
    simp [coordVec, Pi.single_apply]
  have hl : ∀ (s : Finset (Fin n)) (c : Fin n → ℂ) (x : Fin n → V n) (y : V n),
      α (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i • α (x i) y := by
    intro s c x y
    induction s using Finset.induction_on with
    | empty =>
      have := hα.smul_left 0 0 y
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_left, hα.smul_left, ih]
  have hr : ∀ (s : Finset (Fin n)) (c : Fin n → ℂ) (x : V n) (y : Fin n → V n),
      α x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, conj (c i) • α x (y i) := by
    intro s c x y
    induction s using Finset.induction_on with
    | empty =>
      have := hα.smul_right 0 x 0
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_right, hα.smul_right, ih]
  calc α x y = α (∑ a, x a • coordVec a) (∑ b, y b • coordVec b) := by rw [← hex x, ← hex y]
    _ = _ := by
      rw [hl]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hr, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul]

theorem det_of_apply_coordVec {n : ℕ} (L : V n →L[ℂ] V n) :
    (Matrix.of fun c a => L (coordVec a) c).det = L.det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  congr 1

theorem mixTop_curvAt_comp_holo : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → mixTop (fun _ => curvAt (fun x => G (φ x)) w) = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * mixTop fun _ => curvAt G (φ w) := by
  intro n r _ _ G φ w hφ hG hu
  set J : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => fderiv ℂ φ w (coordVec a) c with hJ
  have h := GlobalTheory.T.polarisedTopChernCoeff_linear_substitution (fun _ : Fin n => curvAt G (φ w)) J (J.map conj)
  have e : (fun _ : Fin n => curvAt (fun x => G (φ x)) w) =
      fun (_ : Fin n) a b => ∑ c, ∑ d, (J c a * (J.map conj) d b) • curvAt G (φ w) c d := by
    funext _ a b
    rw [curvAt, curv_comp_holo hG hu hφ, isSesq_eq_sum_coordVec (isSesq_curv hG hu)]
    rfl
  have hc : (J.map conj).det = conj J.det := by
    rw [RingHom.map_det]; rfl
  rw [e, h, hc, hJ, det_of_apply_coordVec, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem exists_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ),
    IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hG y hy
  obtain ⟨e, S, hholo, hys, hy0, hcomp, A, hA, c, N, hev⟩ := hG y hy
  have h1 : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O → GoodBound S c N (fun v => H A (e.symm v) ()) (e z) :=
    (eventually_nhdsWithin_iff.1 hev).mono fun z hz hzO => hz hzO ()
  have h2 : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA
  have h3 : ∀ᶠ z in 𝓝 y, z ∈ e.source := e.open_source.mem_nhds hys
  have h4 : ∀ᶠ z in 𝓝 y, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2 := by
    refine (Filter.eventually_all_finset S).2 fun a ha => ?_
    have hc : ContinuousAt (fun z => e z a) y :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin X.dim => ℂ) a).continuous.comp
        (PiLp.continuous_ofLp 2 _)).continuousAt.comp (e.continuousAt hys)
    have h0 : e y a = 0 := hy0 a ha
    have : ∀ᶠ z in 𝓝 y, e z a ∈ Metric.ball (0 : ℂ) (1 / 2) :=
      hc.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ (by norm_num))
    exact this.mono fun z hz => le_of_lt (by simpa using hz)
  obtain ⟨W, hW, hWo, hyW⟩ := eventually_nhds_iff.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨e, S, A, W, c, hyW, ?_⟩
  exact
  { holo := hholo
    isOpen := hWo
    sub := fun z hz => (hW z hz).2.2.1
    frame := fun z hz => (hW z hz).2.1
    small := fun z hz => (hW z hz).2.2.2
    mem := fun z hz => by
      have := hcomp z (hW z hz).2.2.1
      constructor
      · intro hzO a ha h
        exact (this.2 ⟨a, ha, h⟩) hzO
      · intro hne
        by_contra hzO
        obtain ⟨a, ha, h⟩ := this.1 hzO
        exact hne a ha h
    form := fun z hz hzO a i j => ((hW z hz).1 hzO).form a i j
    dbar := fun z hz hzO a b i j => ((hW z hz).1 hzO).dbar a b i j }

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_mixTop_le_of_weighted : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  intro n r _ _ K w c hw hK
  set D : ℝ := (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 with hD
  have hs : ∀ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hterm : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      ‖((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤ D := by
    intro p π u
    rw [norm_mul, norm_mul, hs, hs, one_mul, one_mul]
    exact GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u w c hw (fun i b => by simpa using hK i (u i) b (p i) (p (π i)))
  have hsum : ‖∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤
      (Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun π _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun u _ => hterm p π u))).trans ?_
    simp [Finset.sum_const, Fintype.card_perm, Fintype.card_fun]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold mixTop
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n.factorial : ℝ)⁻¹ * ‖_‖ ≤ (n.factorial : ℝ)⁻¹ *
        ((Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hf.le)
    _ = _ := by rw [hD]; field_simp

end GlobalTheory.GoodTop
end
