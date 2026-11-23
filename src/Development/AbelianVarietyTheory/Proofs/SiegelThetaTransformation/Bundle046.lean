module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceInvariantNormBounded
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle012
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FourierTranslatesVacuumRootsLevelPoints
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle045
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ M R : ℕ, ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ, (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ Hn Ψ (N + 1), ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  first | exact @GlobalTheory.SW.swd_invariant_bound | exact GlobalTheory.SW.swd_invariant_bound | (intros; apply GlobalTheory.SW.swd_invariant_bound <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Onto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem exponent_eq {x : Frame X.Ψ r}
    (h : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) (z p : Fin n → Fin g → ℂ) :
    -(π * I * ((∑ k, hx X bas idx x (z k) (p k)).im : ℝ)) +
      -(π / 2 * ∑ k, hx X bas idx x (z k + p k) (z k + p k)) =
    -(π / 2 * ∑ k, hx X bas idx x (z k) (z k)) +
      -(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • p k) (p k)) := by
  have h1 (k) : hx X bas idx x (z k + p k) (z k + p k) = hx X bas idx x (z k) (z k) +
      hx X bas idx x (z k) (p k) + conj (hx X bas idx x (z k) (p k)) +
      hx X bas idx x (p k) (p k) := by
    rw [← h]
    simp only [hx, mulVec_add, star_add, add_dotProduct, dotProduct_add]
    ring
  have h2 (k) : hx X bas idx x (z k + (1 / 2 : ℂ) • p k) (p k) = hx X bas idx x (z k) (p k) +
      1 / 2 * hx X bas idx x (p k) (p k) := by
    simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

  simp only [h1, h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum]
  have h3 := Complex.sub_conj (∑ k, hx X bas idx x (z k) (p k))
  push_cast at h3
  linear_combination (π / 2 : ℂ) * h3

theorem exists_canonical (h τ W : Matrix (Fin g) (Fin g) ℂ) (hu : IsUnit h.det)
    (hτ : τ ∈ Siegel (Fin g)) (hW : W.IsSymm) (hY : W * τ.map (fun z => (z.im : ℂ)) = 1)
    {D : ℂ} (hD : D ≠ 0) {N : ℕ} (hN : 0 < N) {θ : (Fin n → Fin g → ℂ) → ℂ}
    (hθ : Differentiable ℂ θ)
    (key : ∀ a b : Fin n → Fin g → ℤ, ∃ p : Fin n → Fin g → ℂ,
      (∀ k, h *ᵥ p k = (fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ)) ∧
      ∀ z : Fin n → Fin g → ℂ, cexp (-(π * ∑ k, (h *ᵥ (z k + (1 / 2 : ℂ) • p k)) ⬝ᵥ W *ᵥ
        star (h *ᵥ p k))) * θ (fun k => z k + p k) = θ z) :
    ∃ φ : TF n g, IsSB φ ∧ ∀ z : Fin n → Fin g → ℂ,
      D * cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ W *ᵥ (h *ᵥ z k)) * thS φ τ (fun k => h *ᵥ z k) = θ z := by
  obtain ⟨c, hcd⟩ : ∃ c : (Fin n → Fin g → ℂ) → ℂ,
    c = fun ζ => cexp (π / 2 * ∑ k, ζ k ⬝ᵥ W *ᵥ ζ k) := ⟨_, rfl⟩
  obtain ⟨Θ, hΘd⟩ : ∃ Θ : (Fin n → Fin g → ℂ) → ℂ,
    Θ = fun ζ => (D * c ζ)⁻¹ * θ fun k => h⁻¹ *ᵥ ζ k := ⟨_, rfl⟩
  have hc (ζ) : D * c ζ ≠ 0 := mul_ne_zero hD (hcd ▸ Complex.exp_ne_zero _)
  have hΘ : Differentiable ℂ Θ := by
    rw [hΘd]
    refine Differentiable.mul (Differentiable.inv ?_ hc) (hθ.comp ?_)
    · simp only [hcd, mulVec, dotProduct]
      fun_prop
    · refine differentiable_pi.2 fun k => differentiable_pi.2 fun i => ?_
      simp only [mulVec, dotProduct]
      fun_prop
  have main : ∀ (a b : Fin n → Fin g → ℤ) (ζ : Fin n → Fin g → ℂ),
      cexp (π * I * ∑ k, ((fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ
        (fun i => (N * b k i : ℂ)) + 2 * ((fun i => (N * b k i : ℂ)) ⬝ᵥ ζ k) +
        (fun i => (N * a k i : ℂ)) ⬝ᵥ (fun i => (N * b k i : ℂ)))) *
      Θ (fun k => ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))) = Θ ζ := by
    intro a b ζ
    have hq (m : Fin g → ℤ) : qv (fun i => (N * m i : ℚ)) = fun i => (N * m i : ℂ) := by
      funext i; simp [qv]
    obtain ⟨p, hp, h1⟩ := key a b
    have h1 := h1 fun k => h⁻¹ *ᵥ ζ k
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
      heis_exponent _ _ hτ.1 hW hY (fun i => (N * a k i : ℚ)) (fun i => (N * b k i : ℚ)) (ζ k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at he
    have he' := congrArg cexp he
    rw [Complex.exp_add, Complex.exp_add] at he'
    simp only [hq] at he'
    have h2 (k) : h⁻¹ *ᵥ (ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))) =
        h⁻¹ *ᵥ ζ k + p k := by
      rw [← hp, mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    simp only [mulVec_add h, mulVec_smul h, hp, mulVec_mulVec, mul_nonsing_inv _ hu,
      one_mulVec] at h1
    simp only [hΘd, h2]
    rw [← h1, ← mul_assoc, ← mul_assoc]
    congr 1
    have h3 := hc ζ
    have h4 := hc fun k => ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))
    rw [mul_inv_eq_iff_eq_mul₀ h4, mul_assoc (_ * c ζ)⁻¹, eq_inv_mul_iff_mul_eq₀ h3]
    simp only [hcd]
    linear_combination D * he'
  obtain ⟨φ, hφ, h5⟩ := GlobalTheory.Ker.LevelTheta.exists_thS_eq n g τ hτ N hN Θ hΘ (fun a ζ => by
      have := main a 0 ζ
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, ← Pi.zero_def, mulVec_zero, add_zero,
        dotProduct_zero, zero_dotProduct, Finset.sum_const_zero, Complex.exp_zero, one_mul] at this
      exact this) (fun b ζ => by
      have := main 0 b ζ
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, ← Pi.zero_def, zero_add, add_zero,
        zero_dotProduct] at this
      exact this)
  refine ⟨φ, hφ, fun z => ?_⟩
  have h6 := hc fun k => h *ᵥ z k
  rw [h5]
  simp only [hΘd, hcd, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at h6 ⊢
  exact mul_inv_cancel_left₀ h6 (θ z)

theorem exists_thA_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (N : ℕ), 0 < N → ∀ θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ θ → (∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ v : WR X n, cexp (-(π * I * (EFR X v (N • embR X y) : ℝ))) * (gaussR X bas idx x (zR X idx x (v + N • embR X y)) * θ (zR X idx x (v + N • embR X y))) = gaussR X bas idx x (zR X idx x v) * θ (zR X idx x v)) → ∃ φ : TF n g, IsSB φ ∧ ∀ z, thA X bas idx φ x z = θ z := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hx' N hN θ hθ hinv
  obtain ⟨⟨L, hL⟩, him, -⟩ := GlobalTheory.Ker.zR_laws E r X g q0 hr bas idx n hs hn x hx'
  have hconj := (GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hx').1
  have hu := isUnit_det_hMat idx hs hx'
  have key : ∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ z : Fin n → Fin g → ℂ,
      cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • (N • pv X idx x (y k)))
        (N • pv X idx x (y k)))) * θ (fun k => z k + N • pv X idx x (y k)) = θ z := by
    intro y hy z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 : zR X idx x (N • embR X y) = fun k => N • pv X idx x (y k) := by
      rw [← hL, map_nsmul, hL]; rfl
    have h2 : zR X idx x (v + N • embR X y) = fun k => L v k + N • pv X idx x (y k) := by
      rw [← hL, map_add (f := _), hL (N • _), h1]; rfl
    have h3 := hinv y hy v
    rw [← him, h1, h2, ← hL v, gaussR, gaussR, ← mul_assoc, ← Complex.exp_add,
      exponent_eq idx hconj (L v) fun k => N • pv X idx x (y k), Complex.exp_add, mul_assoc] at h3
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h3
  refine exists_canonical (hMat X bas idx x) (tauMat X bas idx x) (imInv X bas idx x) hu
    ⟨tauMat_isSymm idx hs hx', tauMat_im_posDef idx hs hx'⟩ (imInv_isSymm idx hs hx')
    (imInv_mul_im idx hs hx') (pow_ne_zero (n / 2) hu.ne_zero) hN hθ fun a b =>
    ⟨fun k => N • pv X idx x (bas (Sum.elim (a k) (b k))), fun k => ?_,
      key (Matrix.of fun k => (bas (Sum.elim (a k) (b k)) : Fin r → E)) fun k => (bas _).2⟩
  beta_reduce
  rw [← Nat.cast_smul_eq_nsmul ℂ, mulVec_smul, pv, hMat_mulVec_per_bas idx hs hx', smul_add,
    ← mulVec_smul]
  rfl

end GlobalTheory.Ker.Onto
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  first | exact @GlobalTheory.Ker.zR_laws | exact GlobalTheory.Ker.zR_laws | (intros; apply GlobalTheory.Ker.zR_laws <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.Proj

section General

variable {α β : Type} [Fintype α] [Fintype β]

theorem ip_smul_smul {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hlin := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.1 (a * conj b)
  have hfun : (fun x => (a • φ) x * conj ((b • ψ) x)) = (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  show haar (fun x => (a • φ) x * conj ((b • ψ) x)) = a * conj b * haar (φ * fun x => conj (ψ x))
  rw [hfun, hlin]

theorem ip_conj {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ip ψ φ = conj (ip φ ψ) := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hc := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.2.1
  have hfun : (fun x => ψ x * conj (φ x)) = fun x => conj ((φ * fun x => conj (ψ x)) x) := by
    funext x
    simp only [Pi.mul_apply, map_mul, Complex.conj_conj]
    ring
  show haar (fun x => ψ x * conj (φ x)) = conj (haar (φ * fun x => conj (ψ x)))
  rw [hfun, hc]

theorem ph_ip [DecidableEq β] {φ ψ : Matrix α β ℚ → ℂ} (hφ : PV φ) (hψ : PV ψ) : Ph (ip φ ψ) := by
  have sφ : Shape φ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β φ).2.1 hφ
  have sψ : Shape ψ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β ψ).2.1 hψ
  have sψc : Shape (fun x => conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β ψ sψ).1
  have spr : Shape (fun x => φ x * conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β φ sφ).2.2 _ sψc
  exact GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase α β _ spr

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem isVac_smul {w : E} {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {v : TF n g}
    (hv : IsVac X bas w A v) {u : ℂ} (hu : ‖u‖ = 1) : IsVac X bas w A (u • v) := by
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨hsb, hip, hfix⟩ := hv'
  unfold IsVac
  refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hsb hsb).2.1 u, ?_, ?_⟩
  · rw [ip_smul_smul hsb hsb, hip, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  · intro y hy
    have hlin : heisG X bas y (u • v) = u • heisG X bas y v := by
      funext x
      simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, smul_comm, hfix y hy]

theorem unitv_smul {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) (c : ℂ) :
    unitv (c • v) = (((‖c‖ : ℝ) : ℂ)⁻¹ * c) • v := by
  have hc : ip (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip_smul_smul hv hv, h1, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold unitv
  rw [hc, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg c), smul_smul]

theorem proj_phases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ Λ ∈ Vset E n 1, IsVac X bas w (tens Λ L) (unitv (projA X bas w (tens Λ L) v)) ∧ PV (u • unitv (projA X bas w (tens Λ L) v)) ∧ projA X bas w (tens Λ L) v = ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • unitv (projA X bas w (tens Λ L) v) := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw1 L hL v hv
  have hstd : stdL E n ∈ Vset E n 1 := GlobalTheory.SW.Base.stdL_mem_Vset n 1
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨A, ε, hA⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL (stdL E n) hstd v hv
  obtain ⟨u, hu1, hupv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) v).2.2.1 A ε hA
  refine ⟨u, hu1, fun Λ hΛ => ?_⟩
  have H := GlobalTheory.T.tensorLattice_vacua_exist_unique E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ
  obtain ⟨vΛ, hvΛ⟩ := H.1
  have hvΛ' := hvΛ
  unfold IsVac at hvΛ'
  have hproj : projA X bas w (tens Λ L) v = ip v vΛ • vΛ := H.2.2.1 v hv'.1 vΛ hvΛ
  have hnorm := H.2.2.2 L hL (stdL E n) hstd vΛ v hvΛ hv
  rw [(GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ).2.2.2.2.2 (stdL E n) hstd,
    ip_conj hv'.1 hvΛ'.1, Complex.norm_conj] at hnorm
  have hsq := congrArg Real.sqrt hnorm
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at hsq
  have hc0 : ‖ip v vΛ‖ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsq
    exact zero_ne_one hsq
  have hunit : unitv (projA X bas w (tens Λ L) v) = (((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ) • vΛ := by
    rw [hproj]
    exact unitv_smul hvΛ'.1 hvΛ'.2.1 _
  have he : ‖((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ‖ = 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hc0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hunit]
    exact isVac_smul hvΛ he
  · obtain ⟨A', ε', hA'⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL Λ hΛ vΛ hvΛ
    obtain ⟨u', hu'1, hu'pv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) vΛ).2.2.1 A' ε' hA'
    have hph : Ph (ip (u • v) (u' • vΛ)) := ph_ip hupv hu'pv
    have hu'u : conj u' * u' = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu'1]
      simp
    have heq : u • unitv (projA X bas w (tens Λ L) v) =
        (ip (u • v) (u' • vΛ) * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹) • (u' • vΛ) := by
      rw [hunit, ip_smul_smul hv'.1 hvΛ'.1, smul_smul, smul_smul]
      congr 1
      linear_combination (-(u * ip v vΛ * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹)) * hu'u
    rw [heq]
    exact (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) (u' • vΛ)).2.2.2.1 hu'pv _
      (Ph.mul hph (Ph.inv ((GlobalTheory.T.complex_phase_calculus_rootOfUnity).2.2.1 ‖ip v vΛ‖)))
  · have hC : ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ) *
        ((‖ip v vΛ‖ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq, Complex.ofReal_one]
    rw [hunit, hproj, smul_smul, ← _root_.mul_assoc, ← _root_.mul_inv, hC, inv_one, _root_.one_mul]

end GlobalTheory.Phase.Proj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.analyticFibre_unitFrame_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = _root_.Formalism.L2.PjFree.perFr (U.X k) x v (_root_.Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = _root_.Formalism.L2.PjFree.relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  first | exact @GlobalTheory.Dict.uw_anFib | exact GlobalTheory.Dict.uw_anFib | (intros; apply GlobalTheory.Dict.uw_anFib <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.coverFourierCoeff_eq_finite_fourier_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r : ℕ) (X : Data E r) (D : SW.Level X) (hn : r ≤ n), r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ L ∈ D.lats, ∀ (mk mk₂ δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (x0 : Fin n → Dw.La), IsMark l L mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → ∀ q, algebraMap d.c₂.F ℂ (d.w x0 q) = t * ∑ᶠ cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸ (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _, datF D (Mfr l) hn (cl.out : Matrix (Fin n) (Fin r) E) * cexp (-(2 * Real.pi * I * ((∑ b, EF X ((cl.out : Matrix (Fin n) (Fin r) E) b) (Y q b) : ℚ) : ℂ))) := by
  first | exact @GlobalTheory.Dict.CoverFourier.w_eq_sum | exact GlobalTheory.Dict.CoverFourier.w_eq_sum | (intros; apply GlobalTheory.Dict.CoverFourier.w_eq_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.fourier_translates_vacuum_roots_levelPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), SelfD X L → IsMark l L mk → ∀ Λ ∈ Vset E n l.M, ∀ N : ℕ, NOK Λ N l.M → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ p : TF n g, IsSB p → (∀ u ∈ tens Λ L, epsW X w u • heisG X bas u p = p) → ∀ u ∈ tens Λ ((Ideal.span {2} * conjI (Mfr l)) • L), ∑ᶠ q, cexp (-(2 * Real.pi * I * ((∑ b, EF X (u b) (Y q b) : ℚ) : ℂ))) • heisG X bas (Y q) p = ((Nat.card (Fin n → LevQ Dw l) : ℕ) : ℂ) • heisG X bas u (projA X bas w (tens Λ (idq (Mfr l) (conjI (Mfr l)) L)) p) := by
  first | exact @GlobalTheory.Dict.poisson_roots | exact GlobalTheory.Dict.poisson_roots | (intros; apply GlobalTheory.Dict.poisson_roots <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.vacuum_multiplier_unitary_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : SW.Level X, ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ‖mu ga L‖ = 1) ∧ (∀ L ∈ D.lats, mu 1 L = 1) ∧ ∀ ga ∈ D.grp, ∀ ga' ∈ D.grp, ∀ L ∈ D.lats, mu (ga * ga') L = mu ga (mapL ga' L) * mu ga' L := by
  first | exact @GlobalTheory.Dict.vac_multiplier_cocycle | exact GlobalTheory.Dict.vac_multiplier_cocycle | (intros; apply GlobalTheory.Dict.vac_multiplier_cocycle <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.levelTestFunction_finite_sum_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, IsSB (D.phi bas hn v₀ L Λ) ∧ IsVac X bas D.w (tens Λ (D.sh L)) (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ (∀ L' ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), s.card = Nat.card D.J ∧ (∀ y ∈ s, y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • (L ⊓ L')) ∧ ‖D.dat hn y‖ = 1 ∧ ∀ y' ∈ s, (∀ k, Cong X D.𝔪 (y k) (y' k)) → y = y') ∧ D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ D.phi bas hn v₀ L' Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L')))) ∧ ∀ γ ∈ D.grp, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → ∀ t : ℂ, ‖t‖ = 1 → wG X bas idx γ (v₀ L) = t • v₀ (mapL γ L) → wG X bas idx γ (D.phi bas hn v₀ L Λ) = (t * ((D.lam k : ℂˣ) : ℂ)⁻¹) • D.phi bas hn v₀ (mapL γ L) Λ := by
  first | exact @GlobalTheory.SW.RecSum.phi_sum_equivariant | exact GlobalTheory.SW.RecSum.phi_sum_equivariant | (intros; apply GlobalTheory.SW.RecSum.phi_sum_equivariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.Red

variable {D : D7}

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by rw [Formalism.L2.Theta.mt, map_one]; rfl

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by rw [fmt, mt_one']; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem fmtC_one (V : HSp D) : fmtC V 1 = 1 := by rw [fmtC, mt_one', cM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem trivAt_one (V : HSp D) (I : Ideal (𝓞 D.host.F)) : TrivAt V I 1 := by
  intro v _ ε _ i j
  simp [mt_one']

theorem isMov_one {k : ℕ} (L : Lt D.host.E k) : IsMov 1 L L := by
  intro u
  exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, by rintro ⟨u₀, h, rfl⟩; rwa [Matrix.one_mulVec]⟩

theorem stdL_fg (n : ℕ) : (stdL D.host.E n).FG := by
  unfold stdL
  exact Submodule.fg_span (Set.finite_range _)

theorem compAt_of_fin (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (h : GA D V) (hh : h ∈ GfC V) :
    compAt θ τ (mt V h) = 1 := by
  unfold GfC infHom at hh
  unfold compAt
  rw [MonoidHom.mem_ker] at hh
  have h1 : (Formalism.L2.Theta.mt V h).map (infPart D) = 1 := by
    have := congrArg Units.val hh
    exact this
  have h2 : ((Formalism.L2.Theta.mt V h).map fun a => θ τ (infPart D a)) =
      ((Formalism.L2.Theta.mt V h).map (infPart D)).map (θ τ) := by
    rw [Matrix.map_map]; rfl
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]

variable {S T : HSp D}

theorem om_fvec (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeak C.ψ S T om)
    (h : GA D S) (hh : h ∈ GfC S) (g : GA D T) (f : WO S T → ℂ) (hf : C.IsTh f) (B : C.Bas) (hB : C.IsB B)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (h, g) (C.fvec B f Q) = C.fvec (C.mvB g B) (om (h, g) f) Q := by
  have hc : (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) = fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) :=
    funext fun τ => compAt_of_fin C.θ τ S h hh
  rw [((GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors D S T C om hW h g f hf).2 B hB).2 Q, hc]
  rfl

theorem levK_one (C : Ctx S T) (Lv : SW.Level C.X) (k : GA D T) (hk : k ∈ GfC T)
    (hm : IsMov (fmt T k) C.X.Λ C.X.Λ)
    (hc : ∀ u ∈ hatV C.X.Λ, fmt T k *ᵥ u - u ∈ hatV (Lv.𝔪 • C.X.Λ)) : C.LevK Lv k 1 := by
  refine ⟨hk, hm, 1, by simp, fun i => ?_⟩
  have hβ : toAf (Lv.β i) ∈ hatV C.X.Λ :=
    ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D T.rank C.X.Λ ⟨C.X.Λ_fg, C.X.Λ_span⟩).1 (Lv.β i)).2 (Lv.β_mem i)
  have hsum : (∑ j, (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) j i • Lv.β j) = Lv.β i := by
    simp [Matrix.one_apply]
  rw [hsum]
  exact hc _ hβ

end GlobalTheory.Ker.Red
end
