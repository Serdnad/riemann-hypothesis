module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FriedrichsFc

open UniformSpace (Completion)

theorem exists_extension {E F : Type} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : E →ₗ[ℂ] F) (hf : ∀ u, ‖f u‖ ≤ ‖u‖) :
    ∃ g : Completion E →L[ℂ] F, (∀ u : E, g (u : Completion E) = f u) ∧ ‖g‖ ≤ 1 := by
  let f' : E →L[ℂ] F := f.mkContinuous 1 (by simpa using hf)
  let e : E →L[ℂ] Completion E := UniformSpace.Completion.toComplL
  have hd : DenseRange e := UniformSpace.Completion.denseRange_coe
  have hu : IsUniformInducing e := UniformSpace.Completion.isUniformInducing_coe E
  have he : ∀ u : E, (f'.extend e) (u : Completion E) = f u := fun u => f'.extend_eq hd hu u
  refine ⟨f'.extend e, he, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [he, UniformSpace.Completion.norm_coe, one_mul]
    exact hf u

theorem norm_map_le {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ)
    (V V' : H →L[ℂ] H) (V₀ : E →ₗ[ℂ] E) (h1 : V' * V = 1)
    (hadj : ∀ u v, ⟪V u, v⟫_ℂ = ⟪u, V' v⟫_ℂ)
    (hι : ∀ u, V (ι u) = ι (V₀ u)) (hBV : ∀ u, B (V₀ u) = V (B u)) (u : E) :
    ‖V₀ u‖ ≤ ‖u‖ := by
  have key : ⟪V₀ u, V₀ u⟫_ℂ = ⟪u, u⟫_ℂ := by
    have h2 : V' (V (ι u)) = ι u := by
      have := congrArg (fun W : H →L[ℂ] H => W (ι u)) h1
      simpa using this
    rw [← hB, hBV, ← hι, hadj, h2, hB]
  have : ‖V₀ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  exact le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this)

theorem exists_inverse_of_form {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ) (hι : ∀ u, ‖ι u‖ ≤ ‖u‖) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : E →ₗ[ℂ] E), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  obtain ⟨g, hg, hgn⟩ := exists_extension ι hι
  let S : H →L[ℂ] Completion E := ContinuousLinearMap.adjoint g
  have hSi : ∀ h c, ⟪S h, c⟫_ℂ = ⟪h, g c⟫_ℂ := fun h c =>
    ContinuousLinearMap.adjoint_inner_left g c h
  have hS : ∀ u : E, S (B u) = (u : Completion E) := by
    intro u
    refine ext_inner_right ℂ fun c => ?_
    rw [hSi]
    induction c using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih v => rw [hg, hB, UniformSpace.Completion.inner_coe]
  have hSn : ‖S‖ ≤ 1 := by
    have : ‖S‖ = ‖g‖ := by simp [S]
    rw [this]; exact hgn
  have hTpos : (g ∘L S).IsPositive := ContinuousLinearMap.isPositive_self_comp_adjoint g
  refine ⟨g ∘L S, hTpos.isSelfAdjoint, ?_, ?_, ?_⟩
  · calc ‖g ∘L S‖ ≤ ‖g‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · intro u
    simp only [ContinuousLinearMap.comp_apply]
    rw [hS, hg]
  · intro U U' U₀ U₀' hUU' hU'U hadj hι₀ hι₀' hB₀ hB₀'
    have hadj' : ∀ u v, ⟪U' u, v⟫_ℂ = ⟪u, U v⟫_ℂ := fun u v => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    let c : E →ₗ[ℂ] Completion E :=
      (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap
    have hc : ∀ u : E, c u = (u : Completion E) := fun _ => rfl
    obtain ⟨U₁, hU₁, -⟩ := exists_extension (c ∘ₗ U₀) (fun u => by
      simpa [hc] using norm_map_le ι B hB U U' U₀ hU'U hadj hι₀ hB₀ u)
    obtain ⟨U₁', hU₁', -⟩ := exists_extension (c ∘ₗ U₀') (fun u => by
      simpa [hc] using norm_map_le ι B hB U' U U₀' hUU' hadj' hι₀' hB₀' u)
    have h1 : ∀ x, g (U₁ x) = U (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁, LinearMap.comp_apply, hc, hg, hg, hι₀]
    have h1' : ∀ x, g (U₁' x) = U' (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁', LinearMap.comp_apply, hc, hg, hg, hι₀']
    have h3 : ∀ a x, ⟪U₁ a, x⟫_ℂ = ⟪a, U₁' x⟫_ℂ := by
      intro a x
      induction a using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u =>
        induction x using UniformSpace.Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih v =>
          rw [hU₁, hU₁', LinearMap.comp_apply, LinearMap.comp_apply, hc, hc,
            UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
            ← hB, hB₀, hadj, hι₀', hB]
    have h4 : ∀ h, S (U h) = U₁ (S h) := by
      intro h
      refine ext_inner_right ℂ fun x => ?_
      rw [hSi, hadj, ← h1', ← hSi, h3]
    ext h
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [h4, h1]

theorem exists_inverse_of_coercive {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [AddCommGroup D] [Module ℂ D] (ι B : D →ₗ[ℂ] H)
    (hsym : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪ι u, B v⟫_ℂ)
    (hpos : ∀ u, ‖ι u‖ ^ 2 ≤ (⟪B u, ι u⟫_ℂ).re) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : D →ₗ[ℂ] D), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  letI core : PreInnerProductSpace.Core ℂ D :=
    { inner := fun u v => ⟪B u, ι v⟫_ℂ
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) ⟪B y, ι x⟫_ℂ = ⟪B x, ι y⟫_ℂ
        rw [inner_conj_symm, hsym]
      re_inner_nonneg := fun x => le_trans (sq_nonneg _) (hpos x)
      add_left := fun x y z => by
        show ⟪B (x + y), ι z⟫_ℂ = ⟪B x, ι z⟫_ℂ + ⟪B y, ι z⟫_ℂ
        rw [map_add (f := _), inner_add_left]
      smul_left := fun x y r => by
        show ⟪B (r • x), ι y⟫_ℂ = (starRingEnd ℂ) r * ⟪B x, ι y⟫_ℂ
        rw [map_smul, inner_smul_left] }
  letI sn : SeminormedAddCommGroup D := InnerProductSpace.Core.toSeminormedAddCommGroup (c := core)
  letI ips : InnerProductSpace ℂ D := InnerProductSpace.ofCore core
  have hι : ∀ u : D, ‖ι u‖ ≤ ‖u‖ := fun u => by
    have h : ‖u‖ ^ 2 = (⟪B u, ι u⟫_ℂ).re := @norm_sq_eq_re_inner ℂ D _ sn ips u
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h ▸ hpos u)
  exact exists_inverse_of_form ι B (fun _ _ => rfl) hι

theorem friedrichs : PositivityTheory.RgBcC.Fc.Friedrichs := by
  intro H _ _ _ D A hsym hpos
  obtain ⟨R, hR, hRn, hRA, hRU⟩ := exists_inverse_of_coercive (D := D) D.subtype A
    (fun x y => hsym x y) (fun x => hpos x)
  refine ⟨R, hR, hRn, fun x => hRA x, ?_⟩
  intro U hU1 hU2 hD hD'
  have lift : ∀ (V : H →L[ℂ] H), (∀ x : D, ∃ y : D, (y : H) = V x ∧ A y = V (A x)) →
      ∃ V₀ : D →ₗ[ℂ] D, (∀ u, V (D.subtype u) = D.subtype (V₀ u)) ∧ ∀ u, A (V₀ u) = V (A u) := by
    intro V hV
    have hmem : ∀ x : D, (V.toLinearMap ∘ₗ D.subtype) x ∈ D := fun x => by
      obtain ⟨y, hy, -⟩ := hV x
      simpa [← hy] using y.2
    refine ⟨LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem, fun u => rfl, fun u => ?_⟩
    obtain ⟨y, hy, hAy⟩ := hV u
    have : LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem u = y :=
      Subtype.ext (by simp [hy])
    rw [this, hAy]
  obtain ⟨U₀, h1, h2⟩ := lift U hD
  obtain ⟨U₀', h1', h2'⟩ := lift (ContinuousLinearMap.adjoint U) hD'
  exact hRU U (ContinuousLinearMap.adjoint U) U₀ U₀' hU2 hU1
    (fun u v => (ContinuousLinearMap.adjoint_inner_right U u v).symm) h1 h1' h2 h2'

end GlobalTheory.CompanionTheory.FriedrichsFc
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.Casimir

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact (isOpen_compl_singleton (x := (0 : ℂ))).preimage hc

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun g : Mat n => g * X) :=
  ((LinearMap.mulRight ℝ X).toContinuousLinearMap).contDiff

theorem differentiableAt_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) {g : Mat n}
    (hg : g ∈ GLs n) : DifferentiableAt ℝ (Rd X f) g := by
  have h1 := hf.fderiv_of_isOpen (m := 1) isOpen_GLs (by norm_cast)
  have h2 : ContDiffOn ℝ 1 (Rd X f) (GLs n) :=
    h1.clm_apply ((contDiff_mul_right X).contDiffOn.of_le (by norm_cast))
  exact (h2.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by norm_num)

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  have : fderiv ℝ (0 : Mat n → V) g = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : V)
  simp [Rd, this]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  simp only [Epow]
  rw [Finset.sum_eq_single a]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem Rd_comb (X : Mat n) (σ : ℂ) {u v : Mat n → V} {g : Mat n} (hu : DifferentiableAt ℝ u g)
    (hv : DifferentiableAt ℝ v g) :
    Rd X ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • (Rd X u g + σ • Rd X v g) := by
  have hsv : DifferentiableAt ℝ (σ • v) g := hv.const_smul σ
  have h1 : fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • fderiv ℝ (u + σ • v) g :=
    fderiv_const_smul (hu.add hsv) _
  have h2 : fderiv ℝ (u + σ • v) g = fderiv ℝ u g + fderiv ℝ (σ • v) g := fderiv_add hu hsv
  have h3 : fderiv ℝ (σ • v) g = σ • fderiv ℝ v g := fderiv_const_smul hv _
  show fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g (g * X) = _
  rw [h1, h2, h3]
  rfl

theorem comb_identity (P B C Q : V) :
    (2 : ℂ) • ((1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + (-Complex.I) • B) +
          (-Complex.I) • ((1 / 2 : ℂ) • (C + (-Complex.I) • Q))) +
        (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + Complex.I • B) +
          Complex.I • ((1 / 2 : ℂ) • (C + Complex.I • Q)))) = P - Q := by
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem Eu_Eu {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a c : Fin n) {g : Mat n}
    (hg : g ∈ GLs n) :
    Eu s a c (Eu s c a f) g =
      (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g) +
        (if s then -Complex.I else Complex.I) •
          ((1 / 2 : ℂ) • (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g))) := by
  have hu := differentiableAt_Rd hf (Matrix.single c a (1 : ℂ)) hg
  have hv := differentiableAt_Rd hf (Matrix.single c a Complex.I) hg
  have e := fun X : Mat n => Rd_comb X (if s then -Complex.I else Complex.I) hu hv
  show ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Eu s c a f) +
    (if s then -Complex.I else Complex.I) • Rd (Matrix.single a c Complex.I) (Eu s c a f))) g = _
  simp only [Pi.smul_apply, Pi.add_apply]
  have e' : ∀ X : Mat n, Rd X (Eu s c a f) g = _ := e
  rw [e', e']

theorem omFormula : OmFormula := by
  intro n V _ _ f hf g hg
  have hgel : ∀ s : Bool, gel s 2 f g = ∑ a, ∑ c, Eu s a c (Eu s c a f) g := by
    intro s
    simp only [gel, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : Epow s 2 a a f = ∑ c, Eu s a c (Epow s 1 c a f) := rfl
    simp only [h2, Finset.sum_apply, Epow_one]
  simp only [Om, Pi.smul_apply, Pi.add_apply, hgel]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Eu_Eu hf true a c hg, Eu_Eu hf false a c hg]
  have key := comb_identity (V := V)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g)
  simp only [↓reduceIte, Bool.false_eq_true]
  exact key

end GlobalTheory.CompanionTheory.Casimir
end
end

section

namespace GlobalTheory.CompanionTheory.WaveFc

open PositivityTheory.RgBcC.Fc

theorem wvAlg : WvAlg := by
  intro c N t y
  have hsq : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = y := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : Even 2 := ⟨1, rfl⟩
    have h0 : Even 0 := ⟨0, rfl⟩
    simp only [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj, h2, h0, if_true, hsq, pow_zero, one_mul]
    first
      | ring
      | (simp [hsq]; ring_nf)
      | simp [hsq]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · intro j
    simp only [PositivityTheory.RgBcC.Fc.wv]
    rw [pow_succ (1 + y ^ 2) N, mul_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WaveFc
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcCls

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} [MeasurableSpace (G n)]

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  show Matrix.det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem cls_eq_toLp (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = hf.toLp _ := by
  rw [cls, dite_eq_left hf]

theorem continuous_lift {V : Type} [TopologicalSpace V] {f : Mat n → V}
    (hf : ContinuousOn f (GLs n)) : Continuous (fun y : G n => f y.val) := by
  exact hf.comp_continuous Units.continuous_val (fun y => val_mem_GLs y)

theorem cls_congr (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f f' : Mat n → V} (h : ∀ g ∈ GLs n, f g = f' g) : cls μ f = cls μ f' := by
  have hff : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => h _ (val_mem_GLs y)
  unfold cls
  rw [hff]

theorem cls_unique [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {f f' : Mat n → V}
    (hc : ContinuousOn f (GLs n)) (hc' : ContinuousOn f' (GLs n))
    (hf : MemLp (fun y : G n => f y.val) 2 μ) (hf' : MemLp (fun y : G n => f' y.val) 2 μ)
    (h : cls μ f = cls μ f') : ∀ g ∈ GLs n, f g = f' g := by
  intro g hg
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf'] at h
  have h1 := (MemLp.toLp_eq_toLp_iff hf hf').1 h
  have h2 := (Continuous.ae_eq_iff_eq μ (continuous_lift hc) (continuous_lift hc')).1 h1
  have hu : IsUnit (Matrix.det g) := isUnit_iff_ne_zero.2 hg
  exact congrFun h2 (Matrix.nonsingInvUnit g hu)

theorem cls_add_smul (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a : ℂ) {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) : cls μ (a • f + f') = a • cls μ f + cls μ f' := by
  have hs : MemLp (fun y : G n => (a • f + f') y.val) 2 μ := (hf.const_smul a).add hf'
  rw [cls_eq_toLp (f := a • f + f') μ hs, cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf',
    ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  rfl

theorem rR_cls [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (hU : Unimod) (h : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    rR μ V h (cls μ f) = cls μ (fun y => f (y * h.val)) := by
  have hmp : MeasurePreserving (fun y : G n => y * h) μ μ := by
    have := (hU n μ).1
    exact measurePreserving_mul_right μ h
  rw [cls_eq_toLp (f := f) μ hf,
    cls_eq_toLp (f := fun y => f (y * h.val)) μ (hf.comp_measurePreserving hmp)]
  unfold rR
  rw [dite_eq_left hmp]
  exact Lp.toLp_compMeasurePreserving hf hmp

theorem compLpL_cls (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →L[ℂ] V) {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    A.compLpL 2 μ (cls μ f) = cls μ (fun y => A (f y)) := by
  have hA : MemLp (fun y : G n => A (f y.val)) 2 μ := A.comp_memLp' hf
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := fun y => A (f y)) μ hA]
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (p := 2) (μ := μ) (hf.toLp _), MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hA]
    with y h1 h2 h3
  rw [h1, h2, h3]

theorem clsFacts : ClsFacts := by
  intro n _ _ μ _ V _ _ hU
  exact ⟨fun f f' hc hc' hf hf' h => cls_unique μ hc hc' hf hf' h,
    fun a f f' hf hf' => cls_add_smul μ a hf hf',
    fun f f' h => cls_congr μ h,
    fun h f hf => rR_cls μ hU h hf,
    fun A f hf => compLpL_cls μ A hf⟩

end GlobalTheory.CompanionTheory.FcCls
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_time_reversal : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl | exact GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.cosh_transform_casimir_real : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T → conj (coshT g (cas χ)) = coshT g (cas χ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | exact GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.center_operator_commutes_integral : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T → ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | exact GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg <;> assumption)
end

section


theorem _root_.GlobalTheory.T.algebra_estimate_for_regularity : PositivityTheory.RgBcC.AlgEst := by
  first | exact @GlobalTheory.CompanionTheory.SkewWords.algEst | exact GlobalTheory.CompanionTheory.SkewWords.algEst | (intros; apply GlobalTheory.CompanionTheory.SkewWords.algEst <;> assumption)
end
