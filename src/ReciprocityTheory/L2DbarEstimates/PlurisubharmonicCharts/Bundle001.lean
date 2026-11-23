module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Matrix.Order

@[expose] public section

section

open Filter Topology Set
open scoped ContDiff

noncomputable section

namespace ReciprocityTheory.L2DbarEstimates.Y

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

theorem zd_fderiv_symm {k : ℕ} {g : E → ContinuousMultilinearMap ℂ (fun _ : Fin k => E) F}
    {y : E} (h : ∀ᶠ z in 𝓝 y, ∀ (τ : Equiv.Perm (Fin k)) (w : Fin k → E), g z (w ∘ τ) = g z w)
    (τ : Equiv.Perm (Fin k)) (u : E) (w : Fin k → E) :
    fderiv ℂ g y u (w ∘ τ) = fderiv ℂ g y u w := by
  by_cases hg : DifferentiableAt ℂ g y
  · have hev : (fun z => g z (w ∘ τ)) =ᶠ[𝓝 y] fun z => g z w := h.mono fun z hz => hz τ w
    rw [← fderiv_continuousMultilinear_apply_const_apply hg (w ∘ τ) u,
      ← fderiv_continuousMultilinear_apply_const_apply hg w u, hev.fderiv_eq]
  · simp [fderiv_zero_of_not_differentiableAt hg]

theorem zd_iter_two_left (f : E → F) (k : ℕ) (y : E) (m : Fin (k + 2) → E) :
    iteratedFDeriv ℂ (k + 2) f y m =
      fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y (m 0) (m 1) (Fin.tail (Fin.tail m)) := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left,
    LinearIsometryEquiv.comp_fderiv]
  simp [Fin.tail, Fin.succ_zero_eq_one]

theorem zd_iteratedFDeriv_comp_perm {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) :
    ∀ k, ∀ y ∈ U, ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E),
      iteratedFDeriv ℂ k f y (v ∘ σ) = iteratedFDeriv ℂ k f y v := by
  intro k
  induction k with
  | zero =>
    intro y _ σ v
    congr 1
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro y hy
    have hmul : ∀ σ τ : Equiv.Perm (Fin (k + 1)),
        (∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ σ) = iteratedFDeriv ℂ (k + 1) f y v) →
        (∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ τ) = iteratedFDeriv ℂ (k + 1) f y v) →
        ∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ ⇑(σ * τ)) =
          iteratedFDeriv ℂ (k + 1) f y v := by
      intro σ τ hσ hτ v
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ, hσ]
    have hstab : ∀ τ' : Equiv.Perm (Fin (k + 1)), τ' 0 = 0 →
        ∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ τ') =
          iteratedFDeriv ℂ (k + 1) f y v := by
      intro τ' h0 v
      set p := Equiv.Perm.decomposeFin τ' with hpdef
      have hp : τ' = Equiv.Perm.decomposeFin.symm p := by rw [hpdef, Equiv.symm_apply_apply]
      have hp1 : p.1 = 0 := by
        have := Equiv.Perm.decomposeFin_symm_apply_zero p.1 p.2
        rw [Prod.mk.eta, ← hp, h0] at this
        exact this.symm
      have hτ : τ' = Equiv.Perm.decomposeFin.symm (0, p.2) := by
        conv_lhs => rw [hp]
        congr 1
        exact Prod.ext hp1 rfl
      rw [hτ, iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have e1 : (v ∘ ⇑(Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), p.2))) 0 = v 0 := by
        simp [Equiv.Perm.decomposeFin_symm_apply_zero]
      have e2 : Fin.tail (v ∘ ⇑(Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), p.2))) =
          Fin.tail v ∘ p.2 := by
        funext i
        simp [Fin.tail, Equiv.Perm.decomposeFin_symm_apply_succ]
      rw [e1, e2]
      refine zd_fderiv_symm ?_ p.2 (v 0) (Fin.tail v)
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ih z hz
    rcases k with _ | k
    · intro σ v
      have hσ1 : σ = 1 := Equiv.ext fun i => Fin.ext (by
        have h1 := (σ i).isLt
        have h2 := i.isLt
        simp only [Equiv.Perm.coe_one, id_eq]
        omega)
      rw [hσ1]
      rfl
    have hswap01 : ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℂ (k + 2) f y (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1)) =
          iteratedFDeriv ℂ (k + 2) f y v := by
      intro v
      have hc : ContDiffAt ℂ 2 (iteratedFDeriv ℂ k f) y :=
        (hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (by
          first
          | exact_mod_cast (le_top : ((2 + k : ℕ) : ℕ∞) ≤ ⊤)
          | (norm_cast; exact le_top)
          | exact le_top
          | (rw [← WithTop.coe_natCast, ← WithTop.coe_ofNat, ← WithTop.coe_add]; exact WithTop.coe_le_coe.2 le_top))
      have hsym : IsSymmSndFDerivAt ℂ (iteratedFDeriv ℂ k f) y :=
        hc.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      rw [zd_iter_two_left, zd_iter_two_left]
      have e3 : Fin.tail (Fin.tail (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1))) =
          Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
      rw [e3]
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hsym (v 1) (v 0)]
    have hswap : ∀ j : Fin (k + 2), ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℂ (k + 2) f y (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) j)) =
          iteratedFDeriv ℂ (k + 2) f y v := by
      intro j
      by_cases hj0 : j = 0
      · subst hj0
        intro v
        rw [Equiv.swap_self]
        rfl
      by_cases hj1 : j = 1
      · subst hj1
        exact hswap01
      have h01 : (0 : Fin (k + 2)) ≠ 1 := by simp
      have hconj : Equiv.swap (1 : Fin (k + 2)) j * Equiv.swap 0 1 * Equiv.swap 1 j =
          Equiv.swap 0 j := by
        rw [Equiv.swap_mul_swap_mul_swap h01 (Ne.symm hj0), Equiv.swap_comm]
      have hfix : (Equiv.swap (1 : Fin (k + 2)) j) 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)
      rw [← hconj]
      exact hmul _ _ (hmul _ _ (hstab _ hfix) hswap01) (hstab _ hfix)
    intro σ v
    have hfix : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      simp [Equiv.swap_apply_right]
    rw [← Equiv.swap_mul_self_mul (0 : Fin (k + 2)) (σ 0) σ]
    exact hmul _ _ (hswap _) (hstab _ hfix) v

end ReciprocityTheory.L2DbarEstimates.Y
end
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open Matrix
open scoped MatrixOrder

theorem uniLat_det_one_add {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) : (1 + Q).det = ∏ i, (1 + hQ.1.eigenvalues i) := by
  have hs := hQ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U := hQ.1.eigenvectorUnitary with hU
  have hUU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := Unitary.coe_mul_star_self U
  have hUU' : star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) = 1 := Unitary.coe_star_mul_self U
  have e : 1 + Q = (U : Matrix ι ι ℝ) * (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues))
      * star (U : Matrix ι ι ℝ) := by
    conv_lhs => rw [hs]
    rw [mul_add, add_mul, mul_one, hUU]
  have hd : ((U : Matrix ι ι ℝ)).det * (star (U : Matrix ι ι ℝ)).det = 1 := by
    rw [← det_mul, hUU, det_one]
  rw [e, det_mul, det_mul, mul_comm ((U : Matrix ι ι ℝ).det), mul_assoc, hd, mul_one,
    ← diagonal_one, diagonal_add, det_diagonal]
  simp [RCLike.ofReal_real_eq_id]

theorem uniLat_det_le_of_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {G H : Matrix ι ι ℝ}
    (hG : G.PosDef) (hGH : (H - G).PosSemidef) : G.det ≤ H.det := by
  set Q := H - G with hQdef
  have hH : H = G + Q := by rw [hQdef]; abel
  have hs := hG.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at hs
  set U := hG.1.eigenvectorUnitary with hU
  set ev := hG.1.eigenvalues with hev
  have hpos : ∀ i, 0 < ev i := hG.eigenvalues_pos
  set D : Matrix ι ι ℝ := diagonal (fun i => (Real.sqrt (ev i))⁻¹) with hD
  set C : Matrix ι ι ℝ := D * star (U : Matrix ι ι ℝ) with hC
  have hUU' : star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) = 1 := Unitary.coe_star_mul_self U
  have hCt : Cᴴ = (U : Matrix ι ι ℝ) * D := by
    rw [hC, conjTranspose_mul, ← star_eq_conjTranspose, star_star, hD, diagonal_conjTranspose]
    congr 2

  have hCG : C * G * Cᴴ = 1 := by
    rw [hCt, hC]
    conv_lhs => rw [hs]
    have e : D * star (U : Matrix ι ι ℝ) * ((U : Matrix ι ι ℝ) * diagonal ev * star (U : Matrix ι ι ℝ))
        * ((U : Matrix ι ι ℝ) * D)
        = D * (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * diagonal ev
          * (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * D := by
      simp only [Matrix.mul_assoc]
    rw [e, hUU', Matrix.mul_one, Matrix.mul_one, hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    have h1 := Real.mul_self_sqrt (hpos i).le
    have h2 : Real.sqrt (ev i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    field_simp
    linarith
  have hQ' : (C * Q * Cᴴ).PosSemidef := by
    have := hGH.conjTranspose_mul_mul_same Cᴴ
    rwa [conjTranspose_conjTranspose] at this
  have hCH : C * H * Cᴴ = 1 + C * Q * Cᴴ := by
    rw [hH, Matrix.mul_add, Matrix.add_mul, hCG]
  have h1 : 1 ≤ (C * H * Cᴴ).det := by
    rw [hCH, uniLat_det_one_add hQ']
    calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hQ'.eigenvalues_nonneg i])
  have h2 : (C * G * Cᴴ).det = 1 := by rw [hCG, det_one]
  rw [det_mul, det_mul, det_conjTranspose, star_trivial] at h1 h2
  have hc : C.det ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2
  have hc2 : 0 < C.det * C.det := mul_self_pos.mpr hc
  have : G.det * (C.det * C.det) ≤ H.det * (C.det * C.det) := by nlinarith
  exact le_of_mul_le_mul_right this hc2

end ReciprocityTheory.L2DbarEstimates.Y
end
