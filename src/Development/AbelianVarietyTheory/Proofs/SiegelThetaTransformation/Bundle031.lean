module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle030
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

namespace GlobalTheory.Dict

section General
open Filter Topology

theorem const_of_norm_factor {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {U : Set V}
    (hU : IsOpen U) (hc : IsPreconnected U) {J : Type*} (R T : J → V → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hR : ∀ i, DifferentiableOn ℂ (R i) U) (hT : ∀ i, DifferentiableOn ℂ (T i) U)
    (h : ∀ x ∈ U, ∃ k : ℂ, ‖k‖ = ρ ∧ ∀ i, R i x = k * T i x) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ U, R i x = C * T i x := by
  by_cases hz : ∀ i, ∀ x ∈ U, T i x = 0
  ·
    refine ⟨(ρ : ℂ), Complex.ofReal_ne_zero.mpr hρ.ne', fun i x hx => ?_⟩
    obtain ⟨k, -, hk⟩ := h x hx
    rw [hk i, hz i x hx, mul_zero, mul_zero]
  simp only [not_forall, exists_prop] at hz
  obtain ⟨j, x0, hx0, hTj⟩ := hz

  have hev : ∀ᶠ y in 𝓝 x0, y ∈ U ∧ T j y ≠ 0 :=
    (hU.eventually_mem hx0).and (((hT j).continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne hTj)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hsub : Metric.ball x0 ε ⊆ U := fun y hy => (hball y hy).1

  have hqd : DifferentiableOn ℂ (fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) := fun y hy =>
    (((hR j).mono hsub) y hy).mul ((((hT j).mono hsub) y hy).inv (hball y hy).2)
  have hqk : ∀ y ∈ Metric.ball x0 ε, ∀ k : ℂ, (∀ i, R i y = k * T i y) → R j y * (T j y)⁻¹ = k := by
    intro y hy k hk
    rw [hk j, mul_inv_cancel_right₀ (hball y hy).2]
  have hqn : ∀ y ∈ Metric.ball x0 ε, ‖R j y * (T j y)⁻¹‖ = ρ := by
    intro y hy
    obtain ⟨k, hkn, hk⟩ := h y (hsub hy)
    rw [hqk y hy k hk, hkn]
  have hx0b : x0 ∈ Metric.ball x0 ε := Metric.mem_ball_self hε
  have hmax : IsMaxOn (norm ∘ fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) x0 :=
    isMaxOn_iff.mpr fun y hy => by
      simp only [Function.comp_apply]
      rw [hqn y hy, hqn x0 hx0b]

  have hqc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x0 ε).isPreconnected
    Metric.isOpen_ball hqd hx0b hmax
  set C : ℂ := R j x0 * (T j x0)⁻¹ with hCdef
  have hCn : ‖C‖ = ρ := hqn x0 hx0b
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hCn
    exact hρ.ne' hCn.symm
  have hloc : ∀ y ∈ Metric.ball x0 ε, ∀ i, R i y = C * T i y := by
    intro y hy i
    obtain ⟨k, -, hk⟩ := h y (hsub hy)
    have hqy : R j y * (T j y)⁻¹ = C := hqc hy
    rw [hk i, ← hqk y hy k hk, hqy]

  let S : Set V := {x | ∀ᶠ y in 𝓝 x, ∀ i, R i y = C * T i y}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hx0S : x0 ∈ S := Filter.eventually_of_mem (Metric.ball_mem_nhds x0 hε) hloc
  have hcl : closure S ∩ U ⊆ S := by
    rintro y ⟨hyS, hyU⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU y hyU
    have hδ4 : 0 < δ / 4 := by linarith
    obtain ⟨x1, hx1S, hdist⟩ := Metric.mem_closure_iff.mp hyS (δ / 4) hδ4
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y hδ4) fun z hz i => ?_

    have hφD : ∀ t ∈ Metric.ball (0 : ℂ) (3 / 2), x1 + t • (z - x1) ∈ Metric.ball y δ := by
      intro t ht
      have ht' : ‖t‖ < 3 / 2 := by simpa using ht
      have hx1' : ‖x1 - y‖ < δ / 4 := by rw [← dist_eq_norm, dist_comm]; exact hdist
      have hz' : ‖z - y‖ < δ / 4 := by rw [← dist_eq_norm]; exact hz
      have hw : ‖z - x1‖ ≤ ‖z - y‖ + ‖x1 - y‖ := by
        calc ‖z - x1‖ = ‖(z - y) - (x1 - y)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖x1 - y‖ := norm_sub_le _ _
      have htw : ‖t • (z - x1)‖ ≤ 3 / 2 * ‖z - x1‖ := by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖x1 + t • (z - x1) - y‖ = ‖(x1 - y) + t • (z - x1)‖ := by congr 1; abel
        _ ≤ ‖x1 - y‖ + ‖t • (z - x1)‖ := norm_add_le _ _
        _ < δ := by linarith
    have hφc : Continuous fun t : ℂ => x1 + t • (z - x1) := by fun_prop

    have hgd : DifferentiableOn ℂ (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1)))
        (Metric.ball (0 : ℂ) (3 / 2)) := by
      intro t ht
      have hmem : x1 + t • (z - x1) ∈ U := hδU (hφD t ht)
      have hlin : DifferentiableAt ℂ (fun t : ℂ => x1 + t • (z - x1)) t := by fun_prop
      have h1 : DifferentiableAt ℂ (R i) (x1 + t • (z - x1)) := (hR i).differentiableAt (hU.mem_nhds hmem)
      have h2 : DifferentiableAt ℂ (T i) (x1 + t • (z - x1)) := (hT i).differentiableAt (hU.mem_nhds hmem)
      exact ((h1.comp t hlin).sub ((h2.comp t hlin).const_mul C)).differentiableWithinAt

    have htend : Filter.Tendsto (fun t : ℂ => x1 + t • (z - x1)) (𝓝 0) (𝓝 x1) :=
      hφc.tendsto' 0 x1 (by simp)
    have hg0 : (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1))) =ᶠ[𝓝 0] 0 :=
      (htend.eventually hx1S).mono fun t ht => by
        simp only [Pi.zero_apply]
        rw [ht i, sub_self]

    have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (3 / 2) := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]; norm_num
    have hg1 := (hgd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (3 / 2)).isPreconnected (Metric.mem_ball_self (by norm_num)) hg0 h1mem
    have hz1 : x1 + (1 : ℂ) • (z - x1) = z := by rw [one_smul, add_sub_cancel]
    simp only [Pi.zero_apply, hz1] at hg1
    exact sub_eq_zero.mp hg1
  have hUS : U ⊆ S := hc.subset_of_closure_inter_subset hSo ⟨x0, hx0, hx0S⟩ hcl
  exact ⟨C, hC0, fun i x hx => (hUS hx).self_of_nhds i⟩

end General

end GlobalTheory.Dict

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem bchar_ne_zero_of_mem_bor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : Wt Ψ r)
    {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  unfold bchar
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_

  have htri : (mat b τ).BlockTriangular id := fun a c hca => (hb τ).2 a c hca
  have hdet := (hb τ).1
  rw [Matrix.det_of_isUpperTriangular htri] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

private theorem abs_psgn' (p0 n : ℕ) : |psgn p0 n| = 1 := by
  rw [psgn, Finset.abs_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> simp

private theorem dmin_eq_psgn_of_gram_diagonal {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
    {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) (τ : Ψ)
    (hx : gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (i : Fin (r + 1)) : dmin G x τ i = ((psgn p0 i : ℝ) : ℂ) := by
  rw [dmin, lminor, hx, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn,
    Complex.ofReal_prod, Finset.prod_range]
  simp

theorem exists_unitFr_rmul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ IsUnitFr X (rmul x b) := by
  obtain ⟨x₀, b, hb, hgram, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.ofReal_re]
    have h1 := abs_psgn' X.p0 i
    refine mul_self_pos.mpr fun h0 => ?_
    rw [h0, abs_zero] at h1
    exact zero_ne_one h1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.norm_real, Real.norm_eq_abs, abs_psgn']

theorem const_of_norm_factor_unitFr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (Jx : Type) (R T : Jx → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ → (∀ i, DifferentiableOn ℂ (R i) X.dom ∧ DifferentiableOn ℂ (T i) X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, R i (rmul x b) = bchar la b * R i x ∧ T i (rmul x b) = bchar la b * T i x) → (∀ x ∈ X.dom, IsUnitFr X x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x) → ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ X.dom, R i x = C * T i x := by
  intro E _ _ _ r X la Jx R T ρ hρ hRT hunit
  have hcd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := by
    intro τ
    unfold mat
    fun_prop
  have hopen : IsOpen X.dom := by
    show IsOpen {x | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (continuous_const.mul (Complex.continuous_re.comp (hcd τ i))))
  have hconn : IsPreconnected X.dom := (GlobalTheory.frames_isConnected E r X).isPreconnected
  refine const_of_norm_factor hopen hconn R T ρ hρ (fun i => (hRT i).1) (fun i => (hRT i).2.1) ?_

  intro x hx
  obtain ⟨b, hb, hxb, hu⟩ := exists_unitFr_rmul X hx
  obtain ⟨κ, hκ, hRTκ⟩ := hunit _ hxb hu
  refine ⟨κ, hκ, fun i => ?_⟩
  have hne := bchar_ne_zero_of_mem_bor la hb
  have h1 := hRTκ i
  rw [((hRT i).2.2 x hx b hb).1, ((hRT i).2.2 x hx b hb).2] at h1
  apply mul_left_cancel₀ hne
  rw [h1]
  ring

end GlobalTheory.Dict
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

namespace GlobalTheory.Dict

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
  (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem fock_hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, mulVec_add, add_dotProduct]

theorem fock_hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, mulVec_add, star_add, dotProduct_add]

theorem fock_hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem fock_hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul]
  rfl

theorem fock_hx_zero_right (z : Fin g → ℂ) : hx X bas idx x z 0 = 0 := by
  simp [hx]

theorem fock_hx_differentiable (w : Fin g → ℂ) : Differentiable ℂ fun z => hx X bas idx x z w := by
  simp only [hx, dotProduct, mulVec]
  fun_prop

theorem fock_hx_conj (hs : IsSympl X bas) (hd : x ∈ X.dom) (z w : Fin g → ℂ) :
    hx X bas idx x w z = conj (hx X bas idx x z w) := by
  have h := imInv_isSymm idx hs hd
  have hr : ∀ i j, conj (imInv X bas idx x i j) = imInv X bas idx x j i := by
    intro i j
    rw [h.apply i j]
    simp [ThFr.imInv]
  simp only [hx]
  generalize hMat X bas idx x *ᵥ z = u
  generalize hMat X bas idx x *ᵥ w = v

  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply, hr, RCLike.star_def,
    _root_.Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

theorem fock_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), (∀ a b, fock X bas idx x k a (fock X bas idx x k b θ) = cexp (-((k : ℂ) * Real.pi * I * ((hx X bas idx x a b).im : ℂ))) • fock X bas idx x k (a + b) θ) ∧ fock X bas idx x k 0 θ = θ ∧ (∀ (N : ℕ) a, fock X bas idx x (N ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock X bas idx x 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ (Differentiable ℂ θ → ∀ a, Differentiable ℂ (fock X bas idx x k a θ)) ∧ ∀ (th : Fin n → (Fin g → ℂ) → ℂ) (κ : ℂ) (φ : TF n g), IsSB φ → (∀ z : Fin n → Fin g → ℂ, ∏ b, th b (z b) = κ * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x 1 (pv X idx x (y b)) (th b) (z b) = κ * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hs hn x hd k θ
  refine ⟨fun a b => ?_, ?_, fun N a => ?_, fun hθ a => ?_, fun th κ φ hφ h y z => ?_⟩
  · funext z
    simp only [fock, Pi.smul_apply, smul_eq_mul]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    rw [add_assoc z a b]
    congr 2
    simp only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left, smul_add]
    rw [fock_hx_conj X bas idx x hs hd a b]
    have := Complex.sub_conj (hx X bas idx x a b)
    push_cast at this
    linear_combination (-(k : ℂ) * Real.pi / 2) * this
  · funext z
    simp [fock, fock_hx_zero_right]
  · funext z
    simp only [fock, smul_add]
    congr 2
    simp only [fock_hx_add_left, fock_hx_smul_left, fock_hx_smul_right, map_natCast]
    push_cast
    ring
  · have h1 := fock_hx_differentiable X bas idx x a
    unfold fock
    refine Differentiable.mul (Differentiable.cexp (Differentiable.neg (Differentiable.const_mul ?_ _))) ?_
    · exact h1.comp (differentiable_id.add_const _)
    · exact hθ.comp (differentiable_id.add_const _)
  · rw [((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hd z]
    simp only [fock, Finset.prod_mul_distrib]
    rw [h fun b => z b + pv X idx x (y b), ← Complex.exp_sum, mul_left_comm]
    congr 2
    simp only [hx, pv, Finset.mul_sum, Finset.sum_neg_distrib, Nat.cast_one, _root_.one_mul]

end GlobalTheory.Dict
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

namespace GlobalTheory.Dict

private theorem herm_mulVec_mulVec' {g : ℕ} (H0 H1 B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z w, hermForm H1 (B *ᵥ z) (B *ᵥ w) = hermForm H0 z w) :
    H0 = Bᵀ * H1 * B.map conj := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single j 1 : Fin g → ℂ) = (Pi.single j 1 : Fin g → ℂ) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have e : hermForm H0 (Pi.single i 1) (Pi.single j 1) = H0 i j := by
    unfold hermForm
    rw [hs]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e] at h1
  rw [← h1]
  simp [hermForm, Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, Finset.mul_sum,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)

theorem det_hx_of_isUnitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, IsUnitFr X x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ z w, hermForm Hm z w = hx X bas idx x z w) → Hm.det = ((∏ τ : X.Ψ, X.c τ ^ r : ℝ) : ℂ) := by
  intro E _ _ _ r X g bas idx n hs hn x hx hu Hm hH
  have hG : ∀ a b, cc (X.Gm a b) = X.Gm b a := X.4
  have hA : x ∈ GG X.Ψ X.Gm X.p0 := by
    unfold Data.dom at hx
    exact hx
  obtain ⟨x₀, b, hb, ho, hbd, rfl⟩ :=
    (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm hG).1 x hA hu
  have ho' : X.IsOrtho x₀ := ho

  have hone : (1 : Matrix (Fin g) (Fin g) ℂ).map conj = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h1 : Hm = GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b) := by
    have h := herm_mulVec_mulVec' Hm (GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b)) 1 (by
      intro z w
      rw [Matrix.one_mulVec, Matrix.one_mulVec, hH, GlobalTheory.ThFr.hermForm_Hm]
      rfl)
    rw [h, hone, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

  have h0 : GlobalTheory.ThFr.Hm X bas idx x₀ = ((GlobalTheory.ThFr.borMat X b).submatrix idx idx)ᵀ *
      GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b) * ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).map conj :=
    herm_mulVec_mulVec' _ _ _ (fun z w =>
      GlobalTheory.ThFr.hermForm_Hm_rmul (bas := bas) (idx := idx) (x := x₀) (hb := hb) z w)
  have hdet0 := GlobalTheory.ThFr.det_Hm_of_isOrtho (idx := idx) (hs := hs) (ho := ho')
  have hnB : ‖((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det‖ = 1 := by
    rw [GlobalTheory.ThFr.det_borMat hb idx, norm_prod]
    apply Finset.prod_eq_one
    intro p _
    unfold GlobalTheory.ThFr.rowFac
    split_ifs <;> simp [hbd]
  have hc : (((GlobalTheory.ThFr.borMat X b).submatrix idx idx).map conj).det =
      conj ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det := by
    rw [RingHom.map_det]
    rfl
  have hm : ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det *
      conj ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnB]
    norm_num
  rw [h1, ← hdet0, h0, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  linear_combination (-(GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b)).det) * hm

end GlobalTheory.Dict
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.tensorLattice_selfDual_semicharacter_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (tens Λ L).FG ∧ (∀ y, y ∈ tens Λ L ↔ ∀ y' ∈ tens Λ L, ∃ k : ℤ, ∑ i, EF X (y i) (y' i) = k) ∧ (∀ y ∈ tens Λ L, epsW X w y ^ 2 = 1 ∧ ∀ y' ∈ tens Λ L, epsW X w (y + y') = epsW X w y * epsW X w y' * cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ y : Matrix (Fin n) (Fin r) E, y ∈ tens (stdL E n) L ↔ ∀ k, y k ∈ L) ∧ (∀ L', SelfD X L' → (tens Λ L').relIndex (tens Λ L) = L'.toAddSubgroup.relIndex L.toAddSubgroup ^ n ∧ tens Λ L ⊓ tens Λ L' = tens Λ (L ⊓ L')) ∧ ∀ Λ' ∈ Vset E n M, (tens Λ' L).relIndex (tens Λ L) = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup ^ r := by
  first | exact @GlobalTheory.SW.TensLat.tens_selfDual_semichar_index | exact GlobalTheory.SW.TensLat.tens_selfDual_semichar_index | (intros; apply GlobalTheory.SW.TensLat.tens_selfDual_semichar_index <;> assumption)
end
