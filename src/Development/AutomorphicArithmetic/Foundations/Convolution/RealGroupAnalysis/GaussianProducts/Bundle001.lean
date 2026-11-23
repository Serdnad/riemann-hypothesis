module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import GroundTheory.AutomorphicForms.FourierWhittaker.Series
import GroundTheory.AutomorphicForms.Bundle012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
import Mathlib.Topology.Compactness.Paracompact

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.goodSpan :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), Good D 0 ∧ (∀ Φ Φ', Good D Φ → Good D Φ' → Good D (Φ + Φ')) ∧ ∀ (c : ℂ) Φ, Good D Φ → Good D (c • Φ) := by
  intro F E _ _ _ _ _ D
  have hWE : ∀ (Φ : GL (Fin 2) (A E) → ℂ) h,
      WE D Φ h = ∫ u in FS2 F, Φ (nE D u * h) * ψ (2 * u 0) ∂(adeleMeasurePi F) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ _ => rfl, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun h => ?_⟩
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simp
    · have : ∀ ξ : Rw F, WE D (0 : GL (Fin 2) (A E) → ℂ) (aE (al D ξ.1) * h) = 0 := by
        intro ξ
        rw [hWE]
        simp
      simp only [this]
      exact hasSum_zero
  · intro Φ Φ' h1 h2
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.add_apply, h1.left, h2.left]
    · exact (h1.int0 h).add (h2.int0 h)
    · have heq : (fun u => (Φ + Φ') (nE D u * h) * ψ (2 * u 0))
          = (fun u => Φ (nE D u * h) * ψ (2 * u 0)) + fun u => Φ' (nE D u * h) * ψ (2 * u 0) := by
        funext u
        simp only [Pi.add_apply, add_mul]
      rw [heq]
      exact (h1.int1 h).add (h2.int1 h)
    · simp only [Pi.add_apply]
      rw [integral_add (h1.int0 h) (h2.int0 h), h1.zero, h2.zero, add_zero]
    · have : ∀ ξ : Rw F, WE D (Φ + Φ') (aE (al D ξ.1) * h)
          = WE D Φ (aE (al D ξ.1) * h) + WE D Φ' (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.add_apply, add_mul]
        exact integral_add (h1.int1 _) (h2.int1 _)
      simp only [this, Pi.add_apply]
      exact (h1.sum h).add (h2.sum h)
  · intro c Φ h1
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.smul_apply, h1.left]
    · exact (h1.int0 h).const_mul c
    · have heq : (fun u => (c • Φ) (nE D u * h) * ψ (2 * u 0))
          = fun u => c * (Φ (nE D u * h) * ψ (2 * u 0)) := by
        funext u
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [heq]
      exact (h1.int1 h).const_mul c
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul, h1.zero, mul_zero]
    · have : ∀ ξ : Rw F, WE D (c • Φ) (aE (al D ξ.1) * h) = c * WE D Φ (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul _ _
      simp only [this, Pi.smul_apply, smul_eq_mul]
      exact (h1.sum h).mul_left c
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem poly_pull {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {p : (Fin 2 → A F) → ℂ} (hp : p ∈ polyOn F (Fin 2)) :
    (fun v : V4 F => p ![v 0, v 1]) ∈ polyFn (F := F) := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, w, rfl⟩ := hx
    refine Algebra.subset_adjoin ?_
    fin_cases i
    · exact ⟨0, w, rfl⟩
    · exact ⟨1, w, rfl⟩
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

private theorem ind_mul_mem {F : Type} [Field F] [NumberField F]
    {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)} (hc : IsCompact T) (ho : IsOpen T)
    {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
      (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) ![y 0, y 1]) * g y) ∈
        finiteSchwartzBruhatPi F (ι := Fin 4) := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
  have hcl : IsClopen T := ⟨hc.isClosed, ho⟩
  have hi : IsLocallyConstant (T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ)) := by
    exact ((LocallyConstant.const (Fin 2 → FiniteAdeleRing (𝓞 F) F) (1 : ℂ)).indicator hcl).isLocallyConstant
  have hcont : Continuous fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => (![y 0, y 1] : Fin 2 → _) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_apply 1
  exact (mem_finiteSchwartzBruhatPi F).2 ⟨(hi.comp_continuous hcont).mul h1, h2.mul_left⟩

theorem UpperTheory.ConvolutionTheory.R2.G.fockMul :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ χ ∈ FockFn δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * χ v) ∈ FockFn δ) ∧ ∀ v₀ : V4 F, ∃ χ ∈ FockFn δ, χ v₀ ≠ 0 := by
  intro F _ _ _ δ
  refine ⟨?_, ?_⟩
  · intro χ hχ p hp T hc ho
    induction hχ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨q, hq, g, hg, rfl⟩ := hφ
      refine Submodule.subset_span ⟨_, mul_mem (poly_pull hp) hq, _, ind_mul_mem hc ho hg, ?_⟩
      funext v
      have hfin : finPartPi ![v 0, v 1] = ![finPartPi v 0, finPartPi v 1] := by
        funext i
        fin_cases i <;> rfl
      simp only [hfin, Pi.mul_apply]
      ring
    | zero =>
      have : (fun v : V4 F => p ![v 0, v 1] * T.indicator 1 (finPartPi ![v 0, v 1]) * (0 : V4 F → ℂ) v) = 0 := by
        funext v
        simp
      rw [this]
      exact zero_mem _
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext v
      simp only [Pi.add_apply]
      ring
    | smul a x _ hx =>
      have := Submodule.smul_mem _ a hx
      convert this using 1
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro v₀
    refine ⟨_, Submodule.subset_span ⟨1, one_mem _,
      finiteTensor fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2,
      finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat _ _, rfl⟩, ?_⟩
    have hone : finiteTensor (fun i => cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v₀ i).2)
        (finPartPi v₀) = 1 := by
      have hself : ∀ a : FiniteAdeleRing (𝓞 F) F,
          cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) a a = 1 := fun a => by
        rw [cosetIndicator_apply, if_pos]
        rw [sub_self]
        exact zero_mem _
      exact Finset.prod_eq_one fun i _ => hself _
    simp only [hone, Pi.one_apply, one_mul, mul_one]
    exact Complex.exp_ne_zero _
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open GroundTheory.Automorphic.FourierWhittaker

variable {F : Type} [Field F] [NumberField F]

private noncomputable def E (κ : Fin 2 → F) (u : Fin 2 → A F) : ℂ := ψ (rt (κ 0) * u 0 + rt (κ 1) * u 1)

private theorem E_cont (κ : Fin 2 → F) : Continuous (E κ) :=
  continuous_ψ.comp (((continuous_const).mul (continuous_apply 0)).add ((continuous_const).mul (continuous_apply 1)))

private theorem E_norm (κ : Fin 2 → F) (u : Fin 2 → A F) : ‖E κ u‖ = 1 := norm_ψ _

private theorem E_add_left (κ κ' : Fin 2 → F) (u : Fin 2 → A F) : E (κ + κ') u = E κ u * E κ' u := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply, map_add (f := _)]
  ring

private theorem E_add_right (κ : Fin 2 → F) (u v : Fin 2 → A F) : E κ (u + v) = E κ u * E κ v := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply]
  ring

private theorem E_zero (u : Fin 2 → A F) : E (0 : Fin 2 → F) u = 1 := by
  simp [E]

private theorem E_per (κ : Fin 2 → F) : ∀ ξ ∈ vecLattice F (Fin 2), ∀ x, E κ (ξ + x) = E κ x := by
  intro ξ hξ x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  rw [E_add_right]
  have : E κ (fun i => algebraMap F (A F) (η i)) = 1 := by
    simp only [E]
    rw [← map_mul, ← map_mul, ← map_add (f := _)]
    exact ψ_rt _
  rw [this, one_mul]

private theorem exists_ne (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∃ a, E κ a ≠ 1 := by
  obtain ⟨x, hx⟩ : ∃ x, adelicChar F x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := F) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hκ
  have hr : rt (κ i) * rt (κ i)⁻¹ = (1 : A F) := by
    rw [← map_mul, mul_inv_cancel₀ hi, map_one]
  refine ⟨Pi.single i (rt (κ i)⁻¹ * x), ?_⟩
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'
  · simp only [Fin.mk_one, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, zero_add,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'

private theorem E_int (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∫ u in FS2 F, E κ u ∂(adeleMeasurePi F) = 0 := by
  obtain ⟨a, ha⟩ := exists_ne κ hκ
  change ∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2)) = 0
  have h := setIntegral_comp_add (K := F) (ι := Fin 2) a (h := E κ) (E_per κ)
  simp only [E_add_right] at h
  rw [integral_mul_const] at h
  have h1 : (∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2))) * (E κ a - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 ha)

private theorem vol : (adeleMeasurePi F).restrict (FS2 F) Set.univ = 1 := by
  rw [Measure.restrict_apply_univ]
  exact vecMeasure_vecDomain

private theorem fin_inst : IsFiniteMeasure ((adeleMeasurePi F).restrict (FS2 F)) :=
  ⟨by rw [vol]; exact ENNReal.one_lt_top⟩

private theorem int_const (a : ℝ) : ∫ _ in FS2 F, a ∂(adeleMeasurePi (ι := Fin 2) F) = a := by
  rw [integral_const, measureReal_def, vol]
  simp

private theorem E_int_zero : ∫ u in FS2 F, E (0 : Fin 2 → F) u ∂(adeleMeasurePi F) = 1 := by
  simp only [E_zero]
  rw [integral_const, measureReal_def, vol]
  simp

private theorem cont_int {g : (Fin 2 → A F) → ℂ} (hg : Continuous g) : IntegrableOn g (FS2 F) (adeleMeasurePi F) := by
  obtain ⟨C, hC, hs⟩ := exists_isCompact_superset_vecDomain (K := F) (ι := Fin 2)
  exact (hg.continuousOn.integrableOn_compact (μ := vecMeasure F (Fin 2)) hC).mono_set hs

private theorem core (κ₀ : Fin 2 → F) (L : (Fin 2 → F) → Fin 2 → F) (c₀ : ℂ) (c : (Fin 2 → F) → ℂ)
    (hc : Summable fun ξ => ‖c ξ‖) (Φ : (Fin 2 → A F) → ℂ) (hΦ : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ) :
    IntegrableOn (fun u => Φ u * E κ₀ u) (FS2 F) (adeleMeasurePi F) ∧
    HasSum (fun ξ => (∫ u in FS2 F, E (κ₀ + L ξ) u ∂(adeleMeasurePi F)) * c ξ)
      ((∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F)) := by
  haveI := countable_numberField F
  haveI := fin_inst (F := F)
  set g : (Fin 2 → F) → (Fin 2 → A F) → ℂ := fun ξ u => E (κ₀ + L ξ) u * c ξ with hgdef
  have hgc : ∀ ξ, Continuous (g ξ) := fun ξ => (E_cont _).mul continuous_const
  have hgn : ∀ ξ u, ‖g ξ u‖ = ‖c ξ‖ := fun ξ u => by simp [hgdef, norm_mul, E_norm]
  have hsum : ∀ u, Summable fun ξ => E (L ξ) u * c ξ := fun u =>
    Summable.of_norm (by simpa [norm_mul, E_norm] using hc)
  have e : ∀ u, Φ u * E κ₀ u = c₀ * E κ₀ u + ∑' ξ, g ξ u := by
    intro u
    rw [hΦ, add_mul, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun ξ => ?_
    simp only [hgdef, E_add_left]
    ring
  have hcont : Continuous fun u => ∑' ξ, g ξ u := continuous_tsum hgc hc fun ξ u => (hgn ξ u).le
  have hI := cont_int hcont
  have hT := cont_int (E_cont κ₀)
  have hT' : IntegrableOn (fun u => c₀ * E κ₀ u) (FS2 F) (adeleMeasurePi F) := hT.const_mul c₀
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact hT'.add hI
  · have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasurePi F).restrict (FS2 F))
      (F := g) (fun ξ => cont_int (hgc ξ)) (by
        simp only [hgn]
        simpa only [int_const] using hc)
    have h2 : (∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F) =
        ∫ u in FS2 F, ∑' ξ, g ξ u ∂(adeleMeasurePi F) := by
      simp only [e]
      rw [integral_add hT' hI, integral_const_mul]
      ring
    rw [h2]
    simpa only [hgdef, integral_mul_const] using hS

end UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors in
theorem UpperTheory.ConvolutionTheory.R2.G.orth :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (c₀ : ℂ) (c : (Fin 2 → F) → ℂ) (Φ : (Fin 2 → A F) → ℂ), Summable (fun ξ => ‖c ξ‖) →
    (∀ u, Φ u = c₀ + ∑' ξ, chi δ ξ u * c ξ) → IntegrableOn Φ (FS2 F) (adeleMeasurePi F) ∧
    IntegrableOn (fun u => Φ u * ψ (2 * u 0)) (FS2 F) (adeleMeasurePi F) ∧
    ∫ u in FS2 F, Φ u ∂(adeleMeasurePi F) = c₀ + c 0 ∧ ∫ u in FS2 F, Φ u * ψ (2 * u 0) ∂(adeleMeasurePi F) = c ![1, 0] := by
  intro F _ _ δ hδ c₀ c Φ hc hΦ
  set L : (Fin 2 → F) → Fin 2 → F := fun ξ => ![-(2 * ξ 0), 2 * δ * ξ 1] with hL
  have hchi : ∀ ξ u, chi δ ξ u = E (L ξ) u := by
    intro ξ u
    simp only [chi, E, hL]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_mul, map_ofNat]
    ring
  have hΦ' : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ := fun u => by
    rw [hΦ]; simp only [hchi]
  set κ : Fin 2 → F := ![2, 0] with hκ
  have hψ : ∀ u : Fin 2 → A F, ψ (2 * u 0) = E κ u := by
    intro u
    have h2A : rt (2 : F) = (2 : A F) := map_ofNat _ 2
    simp only [E, hκ]
    congr 1
    simp [h2A]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hκ0 : κ ≠ 0 := fun h => h2 (by simpa [hκ] using congrFun h 0)
  obtain ⟨i0, s0⟩ := core 0 L c₀ c hc Φ hΦ'
  obtain ⟨i1, s1⟩ := core κ L c₀ c hc Φ hΦ'
  simp only [E_zero, mul_one, zero_add] at i0 s0
  simp only [← hψ] at i1
  refine ⟨i0, i1, ?_, ?_⟩
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c 0) := by
      have hL0 : L 0 = 0 := by
        ext i; fin_cases i <;> simp [hL]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (0 : Fin 2 → F) (fun ξ hξ => by
        have hne : L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · exact a0
          · exact a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s0.unique t
    have e2 : ∫ u in FS2 F, (1 : ℂ) ∂(adeleMeasurePi F) = 1 := by
      simpa only [E_zero] using E_int_zero (F := F)
    rw [e2, mul_one] at e1
    rw [sub_eq_iff_eq_add] at e1
    rw [e1, add_comm]
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c ![1, 0]) := by
      have hL0 : κ + L ![1, 0] = 0 := by
        ext i; fin_cases i <;> simp [hL, hκ]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (![1, 0] : Fin 2 → F) (fun ξ hξ => by
        have hne : κ + L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, hκ, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_add, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · have : 2 * (1 - ξ 0) = 0 := by linear_combination a0
            have := (mul_eq_zero.1 this).resolve_left h2
            simpa using (sub_eq_zero.1 this).symm
          · simpa using a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s1.unique t
    rw [E_int κ hκ0, mul_zero, sub_zero] at e1
    simpa only [hψ] using e1
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem adelicWeightFour_eq_product {F : Type} [Field F] [NumberField F] (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x y z : A F) :
    wt4 L N ![0, x, y, z] = GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N x * (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N y * GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N z) := by
  simp [wt4, Fin.prod_univ_four, GlobalTheory.CompanionTheory.EpConvB.adeleWeight_zero, mul_assoc]

private theorem tsum_pi_fin_two_product {F : Type} (f : F → ℝ≥0∞) :
    ∑' ξ : Fin 2 → F, f (ξ 0) * f (ξ 1) = (∑' x, f x) * ∑' x, f x := by
  rw [← (finTwoArrowEquiv F).symm.tsum_eq, ENNReal.tsum_prod' ]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

private theorem real_bound {w b T c : ℝ} (hw : 0 ≤ w) (hb : 0 < b) (hT0 : 0 ≤ T) (hT : T ≤ c * (1 + b)) :
    b ^ 2 * (w * (T * T)) ≤ 2 * c ^ 2 * (w * b ^ 2 + w * b ^ 4) := by
  have h1 : T * T ≤ (c * (1 + b)) * (c * (1 + b)) := mul_le_mul hT hT hT0 (hT0.trans hT)
  have h2 : (c * (1 + b)) * (c * (1 + b)) ≤ 2 * c ^ 2 * (1 + b ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (1 - b))]
  have h3 : b ^ 2 * w ≥ 0 := by positivity
  calc b ^ 2 * (w * (T * T)) = (b ^ 2 * w) * (T * T) := by ring
    _ ≤ (b ^ 2 * w) * (2 * c ^ 2 * (1 + b ^ 2)) := mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.R2.G.zetaFin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ N : ℕ, ∀ L : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∫⁻ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
    ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ∂(ideleMeasure F) ≠ ⊤ := by
  intro F _ _
  obtain ⟨A2, h2⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 2) (by norm_num)
  obtain ⟨A4, h4⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 4) (by norm_num)
  refine ⟨max (max A2 A4) (Module.finrank ℚ F + 1), fun L => ?_⟩
  set N := max (max A2 A4) (Module.finrank ℚ F + 1) with hN
  have hfr : Module.finrank ℚ F < N := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.CompanionTheory.EpConvB.theta_bound L hfr
  have I2 := h2 L N ((le_max_left _ _).trans (le_max_left _ _))
  have I4 := h4 L N ((le_max_right _ _).trans (le_max_left _ _))
  let w : IdeleGroup F → ℝ := fun b => GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (b : A F)
  let G : IdeleGroup F → ℝ := fun b => 2 * c ^ 2 * (w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 2 + w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 4)
  have hG : Integrable G (ideleMeasure F) := by
    have e2 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (2 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have e4 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (4 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have J2 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) (ideleMeasure F) := e2 ▸ I2
    have J4 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) (ideleMeasure F) := e4 ▸ I4
    exact (J2.add J4).const_mul (2 * c ^ 2)
  have key : ∀ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
      ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ≤ ENNReal.ofReal (G a⁻¹) := by
    intro a
    obtain ⟨hs, hb⟩ := hc a
    have hf0 : ∀ x : F, 0 ≤ GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) :=
      fun x => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    set T : ℝ := ∑' x : F, GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) with hTdef
    have hT0 : 0 ≤ T := tsum_nonneg hf0
    have hw0 : 0 ≤ w a⁻¹ := GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    have e : ∑' ξ : Fin 2 → F,
        ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
        ENNReal.ofReal (w a⁻¹ * (T * T)) := by
      have e1 : ∀ ξ : Fin 2 → F,
          ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
          ENNReal.ofReal (w a⁻¹) * ((fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 0) *
            (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 1)) := by
        intro ξ
        rw [adelicWeightFour_eq_product, ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul (hf0 _)]
      have t2 := tsum_pi_fin_two_product (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x)))
      beta_reduce at t2
      simp_rw [e1]
      rw [ENNReal.tsum_mul_left, t2, ← ENNReal.ofReal_tsum_of_nonneg hf0 hs,
        ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul hT0]
    have hbpos : 0 < (UpperTheory.ConvolutionTheory.R2.ab a)⁻¹ := inv_pos.mpr (M.ab_pos a)
    have hr := real_bound hw0 hbpos hT0 hb
    rw [e, M.wt, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [G, M.ab_inv] using hr
  haveI : (ideleMeasure F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular _
  have h3 : ∫⁻ a : IdeleGroup F, ENNReal.ofReal (G a⁻¹) ∂(ideleMeasure F) = ∫⁻ b : IdeleGroup F, ENNReal.ofReal (G b) ∂(ideleMeasure F) :=
    lintegral_inv_eq_self (fun b => ENNReal.ofReal (G b))
  exact ne_top_of_le_ne_top (h3 ▸ hG.lintegral_lt_top.ne) (lintegral_mono key)
end
