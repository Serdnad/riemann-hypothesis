module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle002
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.MeasMul
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle006
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective

variable {F : Type} [Field F] [NumberField F]

private def rf {R : Type} [Neg R] (v : Fin 4 → R) : Fin 4 → R := Function.update v 1 (-v 1)

private theorem rf_rf {R : Type} [InvolutiveNeg R] (v : Fin 4 → R) : rf (rf v) = v := by
  funext i
  by_cases h : i = 1
  · subst h
    simp [rf]
  · simp [rf, h]

private theorem rf_ne {R : Type} [Neg R] (v : Fin 4 → R) {i : Fin 4} (h : i ≠ 1) : rf v i = v i := by
  simp [rf, h]

private theorem rf_one {R : Type} [Neg R] (v : Fin 4 → R) : rf v 1 = -v 1 := by
  simp [rf]

private def rfH (R : Type) [TopologicalSpace R] [AddGroup R] [IsTopologicalAddGroup R] :
    (Fin 4 → R) ≃ₜ (Fin 4 → R) where
  toFun := rf
  invFun := rf
  left_inv := rf_rf
  right_inv := rf_rf
  continuous_toFun := continuous_id.update 1 (continuous_apply 1).neg
  continuous_invFun := continuous_id.update 1 (continuous_apply 1).neg

private theorem fin_rf {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    (fun z => g (rf z)) ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
  exact (mem_finiteSchwartzBruhatPi F).2
    ⟨h1.comp_continuous (rfH _).continuous, h2.comp_homeomorph (rfH _)⟩

private theorem finPart_rf (v : V4 F) : finPartPi (rf v) = rf (finPartPi v) := by
  funext i
  by_cases h : i = 1
  · subst h
    rw [rf_one]
    change (finPartPi (rf v)) 1 = -(finPartPi v 1)
    simp only [GroundTheory.Heights₂.Theta.finPartPi_eq_adeleFinHom, rf_one, map_neg]
  · rw [rf_ne _ h]
    change (rf v i).2 = (v i).2
    rw [rf_ne _ h]

private theorem poly_rf [IsTotallyReal F] {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    (fun v => p (rf v)) ∈ polyFn (F := F) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨i, w, rfl⟩ := hp
    by_cases h : i = 1
    · subst h
      have e : (fun v : V4 F => ((TR.pInf F (rf v 1) w : ℝ) : ℂ)) =
          (-1 : ℂ) • (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) := by
        funext v
        simp [rf_one]
      have hm : (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ∈ polyFn (F := F) :=
        Algebra.subset_adjoin ⟨1, w, rfl⟩
      rw [e]
      exact Subalgebra.smul_mem _ hm _
    · have e : (fun v : V4 F => ((TR.pInf F (rf v i) w : ℝ) : ℂ)) =
          (fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) := by
        funext v
        rw [rf_ne _ h]
      rw [e]
      exact Algebra.subset_adjoin ⟨i, w, rfl⟩
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add p q _ _ hp hq => exact add_mem hp hq
  | mul p q _ _ hp hq => exact mul_mem hp hq

private theorem gauss_rf [IsTotallyReal F] (δ : F) (v : V4 F) : gauss δ (rf v) = gauss δ v := by
  have h0 : rf v 0 = v 0 := rf_ne _ (by decide)
  have h2 : rf v 2 = v 2 := rf_ne _ (by decide)
  have h3 : rf v 3 = v 3 := rf_ne _ (by decide)
  simp only [gauss, h0, h2, h3, rf_one, neg_sq]

private theorem fock_rf [IsTotallyReal F] {δ : F} {χ : V4 F → ℂ} (hχ : χ ∈ FockFn δ) :
    (fun v => χ (rf v)) ∈ FockFn δ := by
  induction hχ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, poly_rf hp, _, fin_rf hg, ?_⟩
    funext v
    simp only [gauss_rf, finPart_rf]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

private theorem fock_le [IsTotallyReal F] {δ : F} (hδ : ∀ e : F →+* ℝ, e δ < 0) {χ : V4 F → ℂ}
    (hχ : χ ∈ FockFn δ) : χ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  refine (Submodule.span_le.2 ?_) hχ
  rintro _ ⟨p, hp, g, hg, rfl⟩
  have h := pgMem F δ hδ Real.pi Real.pi_pos p hp g hg
  change _ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)
  simpa only [gauss_eq] using h

end UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective

open UpperTheory.ConvolutionTheory.R2.G.FourierHatSurjective in
theorem UpperTheory.ConvolutionTheory.R2.G.hatSurj :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ e : F →+* ℝ, e δ < 0) → ∀ χ ∈ FockFn δ, ∃ φ ∈ Fock δ, hat φ.1 = χ := by
  intro F _ _ _ δ hδ χ hχ
  have h1 := fock_rf hχ
  have h2 := hatFock F δ _ h1
  refine ⟨⟨hat fun v => χ (rf v), fock_le hδ h2⟩, h2, ?_⟩
  funext v
  exact (hatInv F ⟨fun v => χ (rf v), fock_le hδ h1⟩ v).trans (congrArg χ (rf_rf v))
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem enorm_tsum_le' {β : Type*} (f : β → ℂ) : ‖∑' b, f b‖ₑ ≤ ∑' b, ‖f b‖ₑ := by
  by_cases h : ∑' b, ‖f b‖ₑ = ⊤
  · simp [h]
  · have hs : Summable fun b => ‖f b‖ := by
      simpa [toReal_enorm] using ENNReal.summable_toReal h
    have h1 : ‖∑' b, f b‖ ≤ ∑' b, ‖f b‖ := norm_tsum_le_tsum_norm hs
    have h2 : ENNReal.ofReal (∑' b, ‖f b‖) = ∑' b, ‖f b‖ₑ := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp [ofReal_norm_eq_enorm]
    rw [← h2, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal h1

private theorem tsum_comm_of_enorm {α β : Type*} (f : α → β → ℂ) (h : ∑' a, ∑' b, ‖f a b‖ₑ ≠ ⊤) :
    ∑' b, ∑' a, f a b = ∑' a, ∑' b, f a b := by
  have h' : ∑' p : α × β, ‖Function.uncurry f p‖ₑ ≠ ⊤ := by
    have : ∑' p : α × β, ‖Function.uncurry f p‖ₑ = ∑' a, ∑' b, ‖f a b‖ₑ :=
      ENNReal.tsum_prod (f := fun a b => ‖f a b‖ₑ)
    rwa [this]
  have hs : Summable fun p => ‖Function.uncurry f p‖ := by
    simpa [toReal_enorm] using ENNReal.summable_toReal h'
  exact (Summable.of_norm hs).tsum_comm

theorem UpperTheory.ConvolutionTheory.R2.G.unfoldSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F), _root_.UpperTheory.ConvolutionTheory.R2.M.RowSec σ → ∀ (ι : Type) [Countable ι] (u : ι → G1 F → ℂ), (∀ i, NInv (u i)) → ∑' i, abelian₂ M (u i) ≠ ⊤ →
    Summable (fun i => ‖M.I0 (av (u i))‖) ∧ IntegrableOn (fun g => ∑' r, ∑' i, u i (ratS F (σ r) * g)) M.D M.μ ∧
    ∫ g in M.D, ∑' r, ∑' i, u i (ratS F (σ r) * g) ∂M.μ = ∑' i, M.I0 (av (u i)) := by
  intro F _ _ _ M σ hσ ι _ u hu hL
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hLi : ∀ i, abelian₂ M (u i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hL (ENNReal.le_tsum (f := fun i => abelian₂ M (u i)) i)
  have hC := fun i => _root_.UpperTheory.ConvolutionTheory.R2.M.unfC F M σ (u i) hσ (hu i).1 (hu i).2 (hLi i)
  have hTL : ∀ i, ∫⁻ g in M.D, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = abelian₂ M (u i) := fun i =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.unfL F M σ (fun g => ‖u i g‖ₑ) hσ (hu i).1.enorm
      (fun ξ g => by simp only [(hu i).2 ξ g])
  have hTm : ∀ i, Measurable fun g : G1 F => ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i =>
    Measurable.tsum fun r => ((hu i).1.comp (measurable_const_mul _)).enorm
  have hTT : ∫⁻ g in M.D, ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = ∑' i, abelian₂ M (u i) := by
    rw [lintegral_tsum fun i => (hTm i).aemeasurable]
    exact tsum_congr hTL
  have hfin : ∀ᵐ g ∂(M.μ.restrict M.D), ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ := by
    have hm : AEMeasurable (fun g : G1 F => ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ) (M.μ.restrict M.D) :=
      (Measurable.tsum hTm).aemeasurable
    filter_upwards [ae_lt_top' hm (by rw [hTT]; exact hL)] with g hg using hg.ne
  have hST : ∀ i g, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≤ ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i g =>
    enorm_tsum_le' _
  have hSL : ∀ i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ abelian₂ M (u i) := fun i =>
    (lintegral_mono fun g => hST i g).trans_eq (hTL i)
  have hsum : ∑' i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≠ ⊤ :=
    ne_top_of_le_ne_top hL (ENNReal.tsum_le_tsum hSL)
  have hSm : ∀ i, AEStronglyMeasurable (fun g => ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) :=
    fun i => (hC i).2.1.aestronglyMeasurable
  have hI := integral_tsum hSm hsum
  have hae : ∀ᵐ g ∂(M.μ.restrict M.D),
      ∑' r, ∑' i, u i (ratS F (σ r) * g) = ∑' i, ∑' r, u i (ratS F (σ r) * g) := by
    filter_upwards [hfin] with g hg using
      tsum_comm_of_enorm (fun i r => u i (ratS F (σ r) * g)) hg
  have hI0 : ∀ i, M.I0 (av (u i)) = ∫ g in M.D, ∑' r, u i (ratS F (σ r) * g) ∂M.μ := fun i =>
    ((hC i).2.2.2).symm
  refine ⟨?_, ?_, ?_⟩
  · have hle : ∀ i, ‖M.I0 (av (u i))‖ₑ ≤ ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ := fun i => by
      rw [hI0 i]
      exact enorm_integral_le_lintegral_enorm _
    have : ∑' i, ‖M.I0 (av (u i))‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hle)
    simpa [toReal_enorm] using ENNReal.summable_toReal this
  · have hsm : AEStronglyMeasurable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
        (f := fun (s : Finset ι) g => ∑ i ∈ s, ∑' r, u i (ratS F (σ r) * g)) ?_ ?_
      · intro s
        exact Finset.aestronglyMeasurable_fun_sum s fun i _ => hSm i
      · filter_upwards [hfin] with g hg
        have h1 : ∑' i, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ :=
          ne_top_of_le_ne_top hg (ENNReal.tsum_le_tsum fun i => hST i g)
        have h2 : Summable fun i => ‖∑' r, u i (ratS F (σ r) * g)‖ := by
          simpa [toReal_enorm] using ENNReal.summable_toReal h1
        exact (Summable.of_norm h2).hasSum
    have hint : Integrable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine ⟨hsm, ?_⟩
      have hb : ∫⁻ g in M.D, ‖∑' i, ∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ ∑' i, abelian₂ M (u i) := by
        rw [← hTT]
        refine lintegral_mono fun g => ?_
        exact (enorm_tsum_le' _).trans (ENNReal.tsum_le_tsum fun i => hST i g)
      exact lt_of_le_of_lt hb hL.lt_top
    exact hint.congr (hae.mono fun g hg => hg.symm)
  · rw [integral_congr_ae hae, hI]
    exact tsum_congr fun i => (hI0 i).symm
end
