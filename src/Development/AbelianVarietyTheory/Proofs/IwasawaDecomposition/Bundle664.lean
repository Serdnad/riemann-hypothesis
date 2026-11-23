module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_conj_symm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hH.apply i j
  rw [← this]
  simp only [star_star, Pi.star_apply]
  ring

noncomputable def hermFormImBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem hermForm_periods_alternating_nondeg :
    ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  intro g r x M Hm hli hsp hH hpos hM
  have hanti : Mᵀ = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, ← hM]
    rw [hermForm_conj_symm_of_isHermitian Hm hH]
    simp
  refine ⟨hanti, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z : Fin g → ℂ := ∑ j, v j • x j with hz
    have hz0 : z ≠ 0 := by
      intro h0
      apply hv0
      funext j
      exact Fintype.linearIndependent_iff.mp hli v h0 j
    have hxi : ∀ i, hermFormImBilin Hm (x i) z = 0 := by
      intro i
      have : hermFormImBilin Hm (x i) z = ∑ j, v j * M i j := by

        rw [hz, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, ← hM i j]
        rfl
      rw [this]
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have hall : ∀ y, hermFormImBilin Hm y z = 0 := by
      have hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker ((hermFormImBilin Hm).flip z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa using hxi i
      intro y
      have hy : y ∈ Submodule.span ℝ (Set.range x) := by rw [hsp]; trivial
      simpa using hle hy
    have h1 := hall (Complex.I • z)
    have h2 : hermFormImBilin Hm (Complex.I • z) z = (hermForm Hm z z).re := by
      show (hermForm Hm (Complex.I • z) z).im = _
      simp [hermForm, smul_dotProduct]
    have := hpos z hz0
    linarith
  · have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Module.finrank_pi_fintype] at h1
    simp [Complex.finrank_real_complex] at h1
    omega

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_relations_period_matrix : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  intro g d Hm E F τ hH hpos hF hA hFE
  have hexp : ∀ z w : Fin g → ℂ, hermForm Hm z w = ∑ x, ∑ y, z x * Hm x y * star (w y) := by
    intro z w; unfold hermForm; simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [Pi.star_apply]; ring
  have lin1 : ∀ (c : Fin d → ℂ) (w : Fin g → ℂ),
      hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
    intro c w
    unfold hermForm
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have symm : ∀ z w : Fin g → ℂ, hermForm Hm w z = star (hermForm Hm z w) := by
    intro z w
    simp only [hexp, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show star (Hm x y) = Hm y x from hH.apply y x]; ring
  have lin2 : ∀ (c : Fin d → ℂ) (z : Fin g → ℂ),
      hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
    intro c z
    rw [symm, lin1, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', ← symm]
  set a : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hA])
  have asymm : aᵀ = a := by
    ext i k; simp only [a, Matrix.transpose_apply, Matrix.of_apply]; rw [symm]; simp
  set Y : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).im with hY
  set X : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).re with hX
  have hYA : Yᵀ * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hF j, lin1] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] at h
    simpa [Matrix.mul_apply, Matrix.one_apply, Y] using h
  have hAY : a * Y = 1 := by
    have h := congrArg Matrix.transpose hYA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, asymm, Matrix.transpose_one] at h
  have hYs : Yᵀ = Y := by
    calc Yᵀ = Yᵀ * (a * Y) := by rw [hAY, Matrix.mul_one]
    _ = (Yᵀ * a) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hYA, Matrix.one_mul]
  have e1 : ∀ i m, ∑ p, Y p i * a p m = if i = m then 1 else 0 := fun i m => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hYA i) m
  have e2 : ∀ p j, ∑ m, a p m * Y m j = if p = j then 1 else 0 := fun p j => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hAY p) j
  have ys : ∀ i j, Y i j = Y j i := fun i j => by
    simpa using (congrFun (congrFun hYs j) i)
  refine ⟨fun v hv => ?_, fun i j => ?_⟩
  · have him : (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im = v ⬝ᵥ (Y *ᵥ v) := by
      simp only [Complex.im_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Y, Complex.mul_im]; ring
    rw [him]
    set w := Y *ᵥ v with hw
    have hAw : a *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hAY, Matrix.one_mulVec]
    set Q : Fin g → ℂ := ∑ i, ((w i : ℝ) : ℂ) • E i with hQ
    have hQE : ∀ k, (hermForm Hm Q (E k)).re = v k := by
      intro k
      rw [hQ, lin1, ← hAw]
      simp only [hAr, Complex.re_sum, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.mul_re]
      rw [show a k i = a i k from by simpa using congrFun (congrFun asymm i) k]; ring
    have hQQ : (hermForm Hm Q Q).re = v ⬝ᵥ w := by
      have hl := lin2 (fun i => (w i : ℂ)) Q
      rw [← hQ] at hl
      rw [hl]
      simp only [Complex.re_sum, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hQE k]; simp [Complex.mul_re]; ring
    have hQ0 : Q ≠ 0 := by
      intro h; apply hv; funext k; rw [← hQE k, h]; simp [hermForm]
    rw [← hQQ]; exact hpos Q hQ0
  · have key : (hermForm Hm (F i) (F j)).im = X i j - X j i := by
      rw [hF i, lin1]
      simp only [hF j, lin2, hAr, Complex.im_sum, Finset.mul_sum]
      have h1 : ∀ p m, ((τ p i) * (star (τ m j) * (a p m : ℂ))).im
          = Y p i * a p m * X m j - X p i * (a p m * Y m j) := fun p m => by
        simp [Y, X, Complex.mul_im, Complex.mul_re]; ring
      simp only [h1, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, e1, e2]
      simp [X]
    apply Complex.ext
    · simp [key, X]
    · simp [Y] at ys; simp [ys j i]
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem unitOn_injective : Function.Injective (unitOn (R := ℂ)) := by
  intro c c' h
  ext
  have := congrArg (fun u : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (u : Γ(Sp ℂ, ⊤))) h
  simpa [unitOn] using this

theorem unitOn_one : unitOn (1 : ℂˣ) = 1 := by simp [unitOn]

theorem map_nsmul_eq_pow {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) (N : ℕ) (u : Fin g → ℂ) : f ((N : ℂ) • u) = f u ^ N := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Nat.cast_succ, add_smul, one_smul, hf, ih, pow_succ]

theorem pow_eq_one_of_map {g : ℕ} {Q : Type} [Monoid Q] (f : (Fin g → ℂ) → Q) (hf : ∀ v w, f (v + w) = f v * f w)
    (h0 : f 0 = 1) {N : ℕ} (hN : 0 < N) {v : Fin g → ℂ} (hv : f v = 1) : f ((N : ℂ)⁻¹ • v) ^ N = 1 := by
  rw [← map_nsmul_eq_pow f hf h0, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_smul, hv]

end GlobalTheory.ShFam.Hor.LogCh
end
end
