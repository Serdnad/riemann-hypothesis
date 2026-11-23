module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussLatticeCoords

theorem toLp_mulVec_intVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (k : Fin g → ℤ) :
    WithLp.toLp 2 (B *ᵥ intVec k) = ∑ i, k i • WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  have h : intVec k = ∑ i, (k i : ℝ) • (Pi.single i 1 : Fin g → ℝ) := by
    ext j
    simp [intVec, Finset.sum_apply, Pi.single_apply]
  rw [h, Matrix.mulVec_sum, WithLp.toLp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, Int.cast_smul_eq_zsmul]

end PGaussLatticeCoords


open PGaussLatticeCoords in
theorem GaussLatticeCoords.proof : GaussLatticeCoords.Statement := by
  intro g B hB
  refine ⟨fun k => ?_, fun x hx => ?_, fun k k' hkk' => ?_⟩
  · rw [toLp_mulVec_intVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    exact ⟨c, by rw [toLp_mulVec_intVec, hc]⟩
  · have hk : B *ᵥ intVec k = B *ᵥ intVec k' := hkk'
    have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
    have hv : intVec k = intVec k' := by
      have := congrArg (fun v => B⁻¹ *ᵥ v) hk
      simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec] using this
    funext i
    exact Int.cast_injective (congrFun hv i)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PGaussDetFactor

lemma rpow_neg_half_sq {d : ℝ} (hd : 0 < d) : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num
  exact Real.rpow_neg_one d

end PGaussDetFactor


open PGaussDetFactor in
theorem GaussDetFactor.proof : GaussDetFactor.Statement := by
  intro g Y B hY hBY
  have hd : 0 < Y.det := hY.det_pos
  have hsq : B.det ^ 2 = (1 / 2 : ℝ) ^ g * Y.det := by
    have := congrArg Matrix.det hBY
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at this
    rw [sq]; exact this
  have hB0 : 0 < |B.det| := by
    have : B.det ^ 2 ≠ 0 := by rw [hsq]; positivity
    exact abs_pos.mpr (fun h => this (by rw [h]; ring))
  have hL : 0 ≤ |B.det|⁻¹ := (inv_pos.mpr hB0).le
  have hR : 0 ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) := by positivity
  refine (pow_left_inj₀ hL hR (two_ne_zero)).mp ?_
  rw [inv_pow, sq_abs, hsq, mul_pow, rpow_neg_half_sq hd, ← pow_mul, mul_comm g 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_inv, one_div, inv_pow, inv_inv]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace KThetaConstants

lemma log_lhs (C₃ ρ d : ℝ) (g : ℕ) (hC₃ : 0 < C₃) (hg : (0 : ℝ) < g) (hρ : 0 < ρ) (hd : 0 < d) :
    Real.log ((C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) =
      (g / 2) * Real.log (C₃ * g) + (-(1 / 2)) * Real.log d + g * Real.log (1 + 1 / ρ) := by
  have h1 : 0 < C₃ * g := mul_pos hC₃ hg
  have h2 : 0 < 1 + 1 / ρ := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow h1, Real.log_rpow hd, Real.log_pow]

lemma log_rhs (C ρ d : ℝ) (g : ℕ) (hd : 0 < d) :
    Real.log (((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) *
        exp (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g))) =
      (-(1 / 4)) * (g * Real.log 2 + Real.log d) +
        (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)) := by
  have h1 : 0 < (2 : ℝ) ^ g * d := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow h1, Real.log_exp,
    Real.log_mul (by positivity) hd.ne', Real.log_pow]

end KThetaConstants


open KThetaConstants in
theorem ThetaConstants.proof : ThetaConstants.Statement := by
  intro C₃ hC₃
  have hK1 : (1 : ℝ) ≤ max C₃ 1 := le_max_right _ _
  have hK0 : (0 : ℝ) < max C₃ 1 := by linarith
  have hlK : 0 ≤ Real.log (max C₃ 1) := Real.log_nonneg hK1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + Real.log (max C₃ 1) / (2 * Real.log 2), by positivity, ?_⟩
  intro g ρ d hg hρ hd hρ2 hdinv
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  have h2g : (0 : ℝ) < 2 * g := by linarith
  have hl2g : Real.log 2 ≤ Real.log (2 * g) := Real.log_le_log (by norm_num) (by linarith)
  have h1 : -Real.log d ≤ g * Real.log (2 * g) := by
    have hpow : ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) ≤ (2 * (g : ℝ)) ^ g := by
      obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ' (2 * ((n + 1 : ℕ) : ℝ)) n]
      exact mul_le_mul_of_nonneg_right hρ2 (pow_nonneg h2g.le n)
    have := Real.log_le_log (inv_pos.mpr hd) (hdinv.trans hpow)
    rwa [Real.log_inv, Real.log_pow] at this
  have h2 : Real.log (C₃ * g) ≤ Real.log (max C₃ 1) + Real.log (2 * g) := by
    rw [← Real.log_mul hK0.ne' h2g.ne']
    apply Real.log_le_log (mul_pos hC₃ hg0)
    have : C₃ ≤ max C₃ 1 := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_right this hg0.le,
      mul_le_mul_of_nonneg_left (show (g : ℝ) ≤ 2 * g by linarith) hK0.le]
  have h5 : (g : ℝ) / 2 * Real.log (max C₃ 1) ≤
      Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) := by
    rw [show Real.log (max C₃ 1) / (2 * Real.log 2) * g * Real.log (2 * g) =
        (g * Real.log (max C₃ 1) * Real.log (2 * g)) / (2 * Real.log 2) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hl2g (mul_nonneg hg0.le hlK)]
  have ha := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ g / 2 by positivity)
  have hc := mul_le_mul_of_nonneg_left hl2g hg0.le
  rw [← Real.log_le_log_iff (by positivity) (by positivity), log_lhs C₃ ρ d g hC₃ hg0 hρ hd,
    log_rhs _ ρ d g hd]
  nlinarith [h1, ha, hc, h5]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussDualMin

theorem inner_toLp_eq_dotProduct {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

theorem qf_inv_transpose_mulVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (m : Fin g → ℝ) : qf (Bᵀ * B)⁻¹ (Bᵀ *ᵥ m) = m ⬝ᵥ m := by
  have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
  have hBu : IsUnit B.det := hB.isUnit
  have h1 : (Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ m) = B⁻¹ *ᵥ m := by
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBt,
      Matrix.mul_one]
  unfold qf
  rw [h1, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hBu,
    one_mulVec]

end PGaussDualMin


open PGaussDualMin in
theorem GaussDualMin.proof : GaussDualMin.Statement := by
  intro g B hB μ hμ hμ0
  classical
  obtain ⟨m, rfl⟩ : ∃ m : Fin g → ℝ, μ = WithLp.toLp 2 m := ⟨WithLp.ofLp μ, (WithLp.toLp_ofLp _ μ).symm⟩
  have hdual := GroundTheory.Global.mem_dualLattice.1 hμ
  have hex : ∀ i : Fin g, ∃ k : ℤ, inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g))
      (WithLp.toLp 2 (B *ᵥ Pi.single i 1)) = k :=
    fun i => hdual _ (Submodule.subset_span ⟨i, rfl⟩)
  choose l hl using hex
  have hlm : intVec l = Bᵀ *ᵥ m := by
    funext i
    change ((l i : ℤ) : ℝ) = _
    rw [← hl i, inner_toLp_eq_dotProduct, dotProduct_mulVec, dotProduct_single_one,
      mulVec_transpose]
  refine ⟨l, ?_, ?_⟩
  · intro hl0
    apply hμ0
    have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
    have h0 : Bᵀ *ᵥ m = 0 := by
      rw [← hlm, hl0]; funext i; simp [intVec]
    have hm0 : m = 0 := by
      calc m = (Bᵀ)⁻¹ *ᵥ (Bᵀ *ᵥ m) := by
            rw [mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
        _ = 0 := by rw [h0, mulVec_zero]
    rw [hm0]; rfl
  · rw [hlm, qf_inv_transpose_mulVec B hB, ← real_inner_self_eq_norm_sq,
      inner_toLp_eq_dotProduct]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MeasureTheory Module

noncomputable section

namespace PGaussLatticeCovolume

def cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) : Fin g → EuclideanSpace ℝ (Fin g) :=
  fun i => WithLp.toLp 2 (B *ᵥ Pi.single i 1)

theorem cols_linearIndependent {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    LinearIndependent ℝ (cols B) := by
  have h := Matrix.linearIndependent_cols_of_det_ne_zero hB
  have e : cols B = (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm ∘ B.col := by
    funext i
    simp [cols]
  rw [e]
  exact h.map' _ (LinearEquiv.ker _)

def colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  basisOfLinearIndependentOfCardEqFinrank' (cols B) (cols_linearIndependent hB) (by simp)

theorem coe_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ⇑(colBasis hB) = cols B := by
  simp [colBasis]

theorem span_colBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Submodule.span ℤ (Set.range (colBasis hB)) = gaussLattice B := by
  rw [coe_colBasis]
  rfl

def intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    Basis (Fin g) ℤ (gaussLattice B) :=
  ((colBasis hB).restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (span_colBasis hB))

theorem coe_intBasis {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ((↑) : gaussLattice B → EuclideanSpace ℝ (Fin g)) ∘ intBasis hB = cols B := by
  funext i
  simp [intBasis, Basis.restrictScalars_apply, coe_colBasis]

theorem det_cols {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    (EuclideanSpace.basisFun (Fin g) ℝ).toBasis.det (cols B) = B.det := by
  rw [Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, cols]

theorem volume_fundamentalDomain_basisFun (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin g) ℝ).toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume),
    OrthonormalBasis.coe_toBasis, measureReal_def,
    (EuclideanSpace.basisFun (Fin g) ℝ).volume_parallelepiped, ENNReal.toReal_one]

end PGaussLatticeCovolume


open PGaussLatticeCovolume in
theorem GaussLatticeCovolume.proof (hL : GaussLatticeIsLattice.Statement) :
    GaussLatticeCovolume.Statement := by
  intro g B hB
  have : DiscreteTopology (gaussLattice B) := (hL g B hB).1
  have : IsZLattice ℝ (gaussLattice B) := (hL g B hB).2
  rw [ZLattice.covolume_eq_det_mul_measureReal (gaussLattice B) volume (intBasis hB)
      (EuclideanSpace.basisFun (Fin g) ℝ).toBasis,
    coe_intBasis, det_cols, volume_fundamentalDomain_basisFun, mul_one]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PGaussLatticeIsLattice

def colBasis {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    Module.Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  (Pi.basisFun ℝ (Fin g)).map
    ((B.toLinearEquiv' (B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hB))).trans
      (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm)

theorem colBasis_apply {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) (i : Fin g) :
    colBasis B hB i = WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  rw [colBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

theorem gaussLattice_eq_span {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    gaussLattice B = Submodule.span ℤ (Set.range (colBasis B hB)) := by
  unfold gaussLattice
  congr 2
  funext i
  exact (colBasis_apply B hB i).symm

end PGaussLatticeIsLattice


open PGaussLatticeIsLattice in
theorem GaussLatticeIsLattice.proof : GaussLatticeIsLattice.Statement := by
  intro g B hB
  have h := gaussLattice_eq_span B hB
  refine ⟨?_, fun {_} => ⟨?_⟩⟩
  · rw [h]; infer_instance
  · rw [h]; exact ZSpan.span_top (colBasis B hB)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussShellSum

theorem inv_one_sub_exp_neg_one_le_two : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlt : 0 < 1 - Real.exp (-1) := by linarith
  rw [inv_le_comm₀ hlt (by norm_num)]
  linarith

theorem exp_neg_nat (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end PGaussShellSum


open PGaussShellSum in
theorem GaussShellSum.proof (hS : GaussShell.Statement) : GaussShellSum.Statement := by
  intro n hn Λ δ hδ hmin
  set K : ℝ := gaussShellConst n * (1 + 1 / δ) ^ n with hK
  let f : Λ → ℝ := fun μ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hf : 0 ≤ f := fun μ => (Real.exp_pos _).le
  have hK0 : 0 ≤ K := by
    have hc : 0 ≤ gaussShellConst n := by unfold gaussShellConst; positivity
    have : 0 ≤ 1 + 1 / δ := by positivity
    positivity
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.2 (by norm_num)
  have hgeo : Summable fun j : ℕ => K * Real.exp (-1) ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hbound : ∀ u : Finset Λ, ∑ μ ∈ u, f μ ≤ 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by
    intro u
    let fl : Λ → ℕ := fun μ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := fl) (t := u.image fl)
      (fun μ hμ => Finset.mem_image_of_mem fl hμ) f]
    calc ∑ j ∈ u.image fl, ∑ μ ∈ u with fl μ = j, f μ
        ≤ ∑ j ∈ u.image fl, K * Real.exp (-1) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← exp_neg_nat]
          exact hS n hn Λ δ hδ hmin u j
      _ ≤ ∑' j : ℕ, K * Real.exp (-1) ^ j :=
          hgeo.sum_le_tsum _ (fun j _ => by positivity)
      _ = K * (1 - Real.exp (-1))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ ≤ K * 2 := mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two hK0
      _ = 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by rw [hK]; ring
  exact ⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

theorem ThetaBound.proof (hG : GaussianSum.Statement) (hMean : ThetaMean.Statement)
    (hMaj : ThetaNormMajorant.Statement) (hSplit : ThetaFirstCoordSplit.Statement)
    (hConst : ThetaConstants.Statement) : ThetaBound.Statement := by
  obtain ⟨C₃, hC₃, hG⟩ := hG
  obtain ⟨C, hC, hK⟩ := hConst C₃ hC₃
  refine ⟨C, hC, ?_⟩
  intro g _ X Y ρ a b _ hY hR _ _
  refine ⟨hMean g X Y a b hY, fun u₁ u₂ => ?_⟩
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ))
  have hdet : Y.det⁻¹ ≤ ρ ^ 2 * (2 * (g : ℝ)) ^ (g - 1) := by
    have h := hR.det_le
    rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h
  have hg : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have h1 := hMaj g X Y a b u₁ u₂ hY
  have h2 := hSplit g Y ρ a u₁ hY hR.pos hR.first
  have h3 := (hG g Y ρ hY hR.pos hR.min (a + u₁)).2
  have h4 := hK g ρ Y.det hg hR.pos hY.det_pos hR.sq_le hdet
  have he : 0 ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := (exp_pos _).le
  calc thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := h1
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := h2
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) *
          ((C₃ * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g) :=
        mul_le_mul_of_nonneg_left h3 he
    _ ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) * (((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))) :=
        mul_le_mul_of_nonneg_left h4 he
    _ = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
          exp (-(π / (2 * ρ ^ 2)) * δ ^ 2 + (g * log (1 + 1 / ρ) + C * g * log (2 * g))) := by
        rw [exp_add (-(π / (2 * ρ ^ 2)) * δ ^ 2)]; ring

end GroundTheory.Heights₂.Heights
end
