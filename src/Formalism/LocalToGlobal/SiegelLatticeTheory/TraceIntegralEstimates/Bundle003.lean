module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def IsTensAbs (σ : ∀ v, G v → (H v →L[ℂ] H v)) (σs : (∀ v, G v) → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) : Prop :=
  (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) ∧ (∀ g x, σs g (tens x) = tens fun v => σ v (g v) (x v)) ∧
    Dense (Submodule.span ℂ (Set.range tens) : Set Hs)

variable {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}

theorem continuous_tens (h : IsTensAbs σ σs tens) : Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x0
  set F : (∀ v, H v) → ℝ := fun x => RCLike.re (∏ v, ⟪x v, x v⟫_ℂ) -
    2 * RCLike.re (∏ v, ⟪x v, x0 v⟫_ℂ) + RCLike.re (∏ v, ⟪x0 v, x0 v⟫_ℂ) with hF
  have hFc : Continuous F := by fun_prop
  have hnorm : ∀ x, ‖tens x - tens x0‖ = Real.sqrt (F x) := by
    intro x
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      norm_sq_eq_re_inner (𝕜 := ℂ), h.1, h.1, h.1]
  have hF0 : F x0 = 0 := by simp only [hF]; ring
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  have h2 : Tendsto (fun x => Real.sqrt (F x)) (𝓝 x0) (𝓝 (Real.sqrt (F x0))) :=
    (Real.continuous_sqrt.comp hFc).tendsto x0
  rw [hF0, Real.sqrt_zero] at h2
  exact h2

theorem tens_unit (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a : Hs) (x : ∀ v, H v) :
    ⟪σs g (tens x), σs g a⟫_ℂ = ⟪tens x, a⟫_ℂ := by
  have hS : ∀ b ∈ Submodule.span ℂ (Set.range tens), ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨y, rfl⟩ := hb
      rw [h.2.1, h.2.1, h.1, h.1]
      exact Finset.prod_congr rfl fun v _ => (hσ v).2.2.1 (g v) (x v) (y v)
    | zero => simp
    | add b c _ _ hb hc => rw [map_add (f := _), inner_add_right, inner_add_right, hb, hc]
    | smul c b _ hb => rw [map_smul, inner_smul_right, inner_smul_right, hb]
  have hcl : IsClosed {b : Hs | ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ} :=
    isClosed_eq (continuous_const.inner (σs g).continuous) (continuous_const.inner continuous_id)
  have hsub := closure_minimal (fun b hb => hS b hb) hcl
  rw [h.2.2.closure_eq] at hsub
  exact hsub (Set.mem_univ a)

theorem tens_unit_all (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a b : Hs) :
    ⟪σs g a, σs g b⟫_ℂ = ⟪a, b⟫_ℂ := by
  have hS : ∀ c ∈ Submodule.span ℂ (Set.range tens), ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨x, rfl⟩ := hc
      exact tens_unit hσ h g b x
    | zero => simp
    | add c d _ _ hc hd => rw [map_add (f := _), inner_add_left, inner_add_left, hc, hd]
    | smul t c _ hc => rw [map_smul, inner_smul_left, inner_smul_left, hc]
  have hcl : IsClosed {c : Hs | ⟪σs g c, σs g b⟫_ℂ = ⟪c, b⟫_ℂ} :=
    isClosed_eq ((σs g).continuous.inner continuous_const) (continuous_id.inner continuous_const)
  have hsub := closure_minimal (fun c hc => hS c hc) hcl
  rw [h.2.2.closure_eq] at hsub
  exact hsub (Set.mem_univ a)

theorem isUnitRep_tens (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) : IsUnitRep σs := by
  have hnorm : ∀ g c, ‖σs g c‖ = ‖c‖ := by
    intro g c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), tens_unit_all hσ h g c c]
  have hspan : ∀ b ∈ Submodule.span ℂ (Set.range tens), Continuous fun g => σs g b := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨x, rfl⟩ := hb
      have e : (fun g => σs g (tens x)) = fun g => tens (fun v => σ v (g v) (x v)) :=
        funext fun g => h.2.1 g x
      rw [e]
      exact (continuous_tens h).comp (continuous_pi fun v => ((hσ v).2.2.2 (x v)).comp (continuous_apply v))
    | zero => simp only [map_zero]; exact continuous_const
    | add b c _ _ hb hc => simp only [map_add (f := _)]; exact hb.add hc
    | smul t b _ hb => simp only [map_smul]; exact hb.const_smul t
  refine ⟨?_, ?_, fun g a b => tens_unit_all hσ h g a b, ?_⟩
  · apply ContinuousLinearMap.ext_on h.2.2
    rintro _ ⟨x, rfl⟩
    rw [h.2.1]
    simp only [ContinuousLinearMap.one_apply]
    congr 1
    funext v
    show σ v 1 (x v) = x v
    rw [(hσ v).1]
    rfl
  · intro g g'
    apply ContinuousLinearMap.ext_on h.2.2
    rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.mul_apply, h.2.1, h.2.1, h.2.1]
    congr 1
    funext v
    show σ v (g v * g' v) (x v) = σ v (g v) (σ v (g' v) (x v))
    rw [(hσ v).2.1]
    rfl
  · intro a
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hab⟩ := h.2.2.exists_dist_lt a (by positivity : (0 : ℝ) < ε / 3)
    have hc := Metric.tendsto_nhds.mp ((hspan b hb).tendsto g0) (ε / 3) (by positivity)
    filter_upwards [hc] with g hg
    have h1 : dist (σs g a) (σs g b) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm]
    have h2 : dist (σs g0 b) (σs g0 a) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm, norm_sub_rev]
    calc dist (σs g a) (σs g0 a)
        ≤ dist (σs g a) (σs g b) + dist (σs g b) (σs g0 b) + dist (σs g0 b) (σs g0 a) :=
          dist_triangle4 _ _ _ _
      _ < ε := by rw [h1, h2]; linarith

end Formalism.L2.S.Pv.SchurTens
end
end

section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) : V' →L[ℂ] V :=
  (ContinuousLinearMap.adjoint Y).comp ((σ γ).comp Y')

theorem inner_sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) (a : V) (b : V') :
    ⟪a, sand σ Y Y' γ b⟫_ℂ = ⟪Y a, σ γ (Y' b)⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right Y a (σ γ (Y' b))

private theorem norm_sq_eq_sum_norm_inner_stdBasis_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, v⟫_ℂ‖ ^ 2 := by
  exact ((stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right v).symm

theorem hsA_eq (A : V' →L[ℂ] V) :
    hsA A = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V i, A (stdOrthonormalBasis ℂ V' j)⟫_ℂ‖ ^ 2 := by
  show ∑ j, ‖A (stdOrthonormalBasis ℂ V' j)‖ ^ 2 = _
  exact Finset.sum_congr rfl fun j _ => norm_sq_eq_sum_norm_inner_stdBasis_sq _

theorem hsA_sand (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) :
    hsA (sand σ Y Y' γ) = ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 := by
  rw [hsA_eq]
  simp only [inner_sand]

theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem schur_sq {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d) (a b : HH) :
    Integrable (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪a, σ γ b⟫_ℂ‖ ^ 2 ∂μ = ‖a‖ ^ 2 * ‖b‖ ^ 2 / d := by
  obtain ⟨hI, hE⟩ := hS.2 b a b a
  have hfun : (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) =
      fun γ => RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) := by
    funext γ
    exact norm_sq_eq_re_mul_conj _
  have h2 : ∫ γ, RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) ∂μ =
      RCLike.re (⟪b, b⟫_ℂ * ⟪a, a⟫_ℂ / (d : ℂ)) := by
    rw [← hE]
    exact integral_re hI
  have hsq : ∀ x : HH, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hI.re
  · rw [hfun, h2, hsq a, hsq b, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    ring

theorem lintegral_hsA_sand {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d)
    (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) :
    ∫⁻ γ, ENNReal.ofReal (hsA (sand σ Y Y' γ)) ∂μ =
      ENNReal.ofReal ((∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d) := by
  have hterm : ∀ j i,
      Integrable (fun γ => ‖⟪Y (stdOrthonormalBasis ℂ V i),
        σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
        ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d :=
    fun j i => schur_sq hS _ _
  have hInt : Integrable (fun γ => ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1
  have hrow : ∀ j, ∫ γ, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      ∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d := by
    intro j
    rw [integral_finsetSum _ fun i _ => (hterm j i).1]
    exact Finset.sum_congr rfl fun i _ => (hterm j i).2
  have hval : ∫ γ, ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      (∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    simp only [Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_comm
  simp_rw [hsA_sand]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ fun γ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _), hval]

end Formalism.L2.S.Pv.EnergyAbs
end
end

section

noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section HS

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem hsA_smul (c : ℂ) (A : V' →L[ℂ] V) : hsA (c • A) = ‖c‖ ^ 2 * hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow]

private theorem sum_norm_inner_stdBasis_sq_eq_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (x : E) :
    ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
  exact (stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right x

theorem hsA_eq_adjoint (A : V' →L[ℂ] V) :
    hsA A = ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  calc ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪stdOrthonormalBasis ℂ V j, A (stdOrthonormalBasis ℂ V' i)⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]
    _ = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V' i,
          (ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]

private theorem norm_sq_apply_of_inner_preserving {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →L[ℂ] E) (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ) (v : E) : ‖U v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := hU v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

theorem hsA_conj (U : V →L[ℂ] V) (U' : V' →L[ℂ] V') (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hU' : ∀ a b, ⟪U' a, U' b⟫_ℂ = ⟪a, b⟫_ℂ) (A : V' →L[ℂ] V) :
    hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) = hsA A := by
  have h1 : Formalism.L2.SG.Pf.EnergyAbs.hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) =
      Formalism.L2.SG.Pf.EnergyAbs.hsA (A.comp (ContinuousLinearMap.adjoint U')) := by
    unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply]
    exact norm_sq_apply_of_inner_preserving U hU _
  rw [h1, hsA_eq_adjoint, hsA_eq_adjoint A]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]
  exact norm_sq_apply_of_inner_preserving U' hU' _

def hsL : (V' →L[ℂ] V) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) where
  toFun A := WithLp.toLp 2 (fun j => A (stdOrthonormalBasis ℂ V' j))
  map_add' A B := by
    ext j
    simp
  map_smul' c A := by
    ext j
    simp

def hsC : (V' →L[ℂ] V) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) :=
  LinearMap.toContinuousLinearMap hsL

theorem norm_hsC (A : V' →L[ℂ] V) : ‖hsC A‖ = Real.sqrt (hsA A) := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem sqrt_hsA_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → (V' →L[ℂ] V))
    (hf : Integrable f μ) :
    Real.sqrt (hsA (∫ x, f x ∂μ)) ≤ ∫ x, Real.sqrt (hsA (f x)) ∂μ := by
  simp_rw [← norm_hsC]
  rw [← ContinuousLinearMap.integral_comp_comm _ hf]
  exact norm_integral_le_integral_norm _

theorem sqrt_hsA_le_add_sub (A B : V' →L[ℂ] V) :
    Real.sqrt (hsA A) ≤ Real.sqrt (hsA B) + Real.sqrt (hsA (A - B)) := by
  simp_rw [← norm_hsC]
  have h : hsC A = hsC B + hsC (A - B) := by
    simp [map_sub]
  rw [h]
  exact norm_add_le _ _

end HS

section Rep

variable {G : Type} [Group G] [TopologicalSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]

theorem rep_mul_apply {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ x (σ y a) = σ (x * y) a := by
  obtain ⟨-, hmul, -, -⟩ := hσ
  rw [hmul, ContinuousLinearMap.mul_apply]

end Rep

section Kernel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

end Kernel

section Quot

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem quot_map_inv {μ μS ν : Measure G} [SFinite ν] [SFinite μS] (hq : IsQuot μ μS ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) :
    μ = (ν.prod μS).map (fun p => p.2⁻¹ * p.1) := by
  have hm : Measurable (fun p : G × G => p.2⁻¹ * p.1) := measurable_snd.inv.mul measurable_fst
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have h := hq (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have hx : MeasurableSet ((fun t : G => t * x) ⁻¹' s) := measurable_mul_const x hs
  have hx' : MeasurableSet ((fun t : G => t⁻¹ * x) ⁻¹' s) := (measurable_inv.mul_const x) hs
  calc ∫⁻ t, s.indicator (1 : G → ℝ≥0∞) (t * x) ∂μS
      = ∫⁻ t, ((fun t : G => t * x) ⁻¹' s).indicator (1 : G → ℝ≥0∞) t ∂μS := rfl
    _ = μS ((fun t : G => t * x) ⁻¹' s) := lintegral_indicator_one hx
    _ = (μS.map (fun t => t⁻¹)) ((fun t : G => t⁻¹ * x) ⁻¹' s) := by
        rw [Measure.map_apply measurable_inv hx']
        congr 1
        ext t
        simp
    _ = μS ((fun t : G => t⁻¹ * x) ⁻¹' s) := by rw [hinv]
    _ = _ := rfl

end Quot

end Formalism.L2.S.Pv.EnergyAbs
end
end
