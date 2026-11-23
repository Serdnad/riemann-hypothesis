module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DoublingSeries

def ratFun (q N : ℕ) (α : Fin N → ℂˣ) (X : ℂ) : ℂ :=
  (∏ i, (1 - (α i : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
    (∏ i, (1 - (((α i)⁻¹ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
      ∏ i ∈ Finset.Icc 1 N, (1 - (q : ℂ) ^ (-(i : ℂ)) * X ^ 2)

theorem ratFun_cpow {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (s : ℂ) :
    lFactor q α (s + 1 / 2) * lFactor q α⁻¹ (s + 1 / 2) * invNormFactor q N s =
      ratFun q N α ((q : ℂ) ^ (-s)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h1 : (q : ℂ) ^ (-(s + 1 / 2)) = (q : ℂ) ^ (-(1 / 2 : ℂ)) * (q : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hq0]; ring_nf
  have h2 : ∀ i : ℕ, (q : ℂ) ^ (-(2 * s + i)) = (q : ℂ) ^ (-(i : ℂ)) * ((q : ℂ) ^ (-s)) ^ 2 := fun i => by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]; push_cast; ring_nf
  simp only [lFactor, invNormFactor, ratFun, h1, h2, Pi.inv_apply, mul_assoc]

theorem ratFun_differentiableOn {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (ρ : ℝ)
    (hα : ∀ x, ‖(α x : ℂ)‖ ≤ (q : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (q : ℝ) ^ ρ) :
    DifferentiableOn ℂ (ratFun q N α) (Metric.ball 0 ((q : ℝ) ^ (1 / 2 - ρ))) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have key : ∀ a : ℂ, ‖a‖ ≤ (q : ℝ) ^ ρ → ∀ X ∈ Metric.ball (0 : ℂ) ((q : ℝ) ^ (1 / 2 - ρ)),
      1 - a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X ≠ 0 := by
    intro a ha X hX
    rw [mem_ball_zero_iff] at hX
    have hn : ‖a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X‖ < 1 := by
      rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
      rw [hre]
      calc ‖a‖ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ ≤ (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ := by gcongr
        _ < (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (q : ℝ) ^ (1 / 2 - ρ) := by gcongr
        _ = 1 := by rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, show ρ + -(1 / 2 : ℝ) + (1 / 2 - ρ) = 0 by ring, Real.rpow_zero]
    intro h
    have e : a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X = 1 := by linear_combination -h
    rw [e, norm_one] at hn
    exact lt_irrefl _ hn
  unfold ratFun
  refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key _ (hα i).1 X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key (((α i)⁻¹ : ℂˣ) : ℂ) (by rw [Units.val_inv_eq_inv_val, norm_inv]; exact (hα i).2) X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      (differentiableOn_const (𝕜 := ℂ) (1 : ℂ)).sub ((differentiableOn_const (𝕜 := ℂ) ((q : ℂ) ^ (-(i : ℂ)))).mul (differentiableOn_id (𝕜 := ℂ).pow 2))

theorem exists_cpow_neg_eq {q : ℕ} (hq : 1 < q) (s₀ : ℝ) {z : ℂ} (hz : z ≠ 0) (hzs : ‖z‖ < (q : ℝ) ^ (-s₀)) :
    ∃ s : ℂ, s₀ < s.re ∧ (q : ℂ) ^ (-s) = z := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hl : 0 < Real.log q := Real.log_pos hq1
  refine ⟨-Complex.log z / (Real.log q : ℂ), ?_, ?_⟩
  · have e : (-Complex.log z / (Real.log q : ℂ)).re = -Real.log ‖z‖ / Real.log q := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    rw [e, lt_div_iff₀ hl]
    have := Real.log_lt_log (norm_pos_iff.2 hz) hzs
    rw [Real.log_rpow (by linarith)] at this
    linarith
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    have hl' : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
    rw [show (Real.log q : ℂ) * -(-Complex.log z / (Real.log q : ℂ)) = Complex.log z by field_simp]
    exact Complex.exp_log hz

theorem cpow_split {q : ℕ} (hq : 1 < q) (N : ℕ) (s : ℂ) {m : ℤ} (hm : 0 ≤ m) :
    (q : ℂ) ^ (-((N : ℂ) / 2 + s) * (m : ℂ)) =
      (((q : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) * ((q : ℂ) ^ (-s)) ^ m.toNat := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]
  congr 1
  have : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hm
  push_cast
  rw [this]
  ring

theorem sumAbs_nonneg {D : Type} [Fintype D] (e : D → ℤ) : 0 ≤ sumAbs e :=
  Finset.sum_nonneg fun i _ => abs_nonneg (e i)

end GlobalTheory.DoublingSeries
end
end

section

open GlobalTheory.InertZeta

open MeasureTheory Pointwise

namespace GlobalTheory.InertZeta

theorem cosetIntegral_holds : CosetIntegral := by
  intro G _ _ _ _ _ μ _ K hK hμK F Z hF hZ
  classical
  set f : G ⧸ K → ℂ := fun x => F x.out with hf
  let A : G ⧸ K → Set G := fun x => QuotientGroup.mk ⁻¹' {x}
  have hA : ∀ x, A x = x.out • (K : Set G) := by
    intro x; ext g
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff, mem_leftCoset_iff]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
    rfl
  have hAm : ∀ x, MeasurableSet (A x) := fun x => by
    rw [hA]; exact (hK.smul x.out).measurableSet
  have hAμ : ∀ x, μ (A x) = 1 := fun x => by rw [hA, measure_smul]; exact hμK
  have hconst : ∀ x, ∀ g ∈ A x, F g = f x := by
    intro x g hg
    rw [hA, mem_leftCoset_iff] at hg
    have := hF x.out _ hg
    rwa [mul_inv_cancel_left] at this
  have hself : ∀ g : G, g ∈ A (QuotientGroup.mk g) := fun g => rfl
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro x y hxy
    exact (Set.disjoint_singleton.mpr hxy).preimage _
  set S := Function.support f with hSdef
  have hS : S.Countable := hZ.summable.countable_support
  haveI : Countable S := hS.to_subtype
  let B : S → Set G := fun i => A i.1
  have hBint : ∀ i : S, ∫ g in B i, F g ∂μ = f i.1 := by
    intro i
    rw [setIntegral_congr_fun (hAm i.1) (fun g hg => hconst i.1 g hg), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBnorm : ∀ i : S, ∫ g in B i, ‖F g‖ ∂μ = ‖f i.1‖ := by
    intro i
    rw [setIntegral_congr_fun (g := fun _ => ‖f i.1‖) (hAm i.1) (fun g hg => by simp only [hconst i.1 g hg]), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBon : ∀ i : S, IntegrableOn F (B i) μ := by
    intro i
    have h1 : IntegrableOn (fun _ : G => f i.1) (B i) μ :=
      integrableOn_const (by simp [B, hAμ]) (by simp)
    exact h1.congr_fun (fun g hg => (hconst i.1 g hg).symm) (hAm i.1)
  have hsumm : Summable fun i : S => ∫ g in B i, ‖F g‖ ∂μ := by
    simp only [hBnorm]
    exact (summable_norm_iff.mpr hZ.summable).subtype (fun x => x ∈ S)
  have hU : IntegrableOn F (Set.iUnion B) μ :=
    integrableOn_iUnion_of_summable_integral_norm hBon hsumm
  have hzero : ∀ g ∉ Set.iUnion B, F g = 0 := by
    intro g hg
    have hnot : (QuotientGroup.mk g : G ⧸ K) ∉ S := by
      intro hm
      exact hg (Set.mem_iUnion.mpr ⟨⟨_, hm⟩, hself g⟩)
    rw [hconst _ g (hself g)]
    simpa [hSdef] using hnot
  have hInt : Integrable F μ := hU.integrable_of_forall_notMem_eq_zero hzero
  refine ⟨hInt, ?_⟩
  have h1 := hasSum_integral_iUnion (fun i : S => hAm i.1) (fun i j hij => hdisj (fun h => hij (Subtype.ext h))) hU
  have hfun : (fun i : S => ∫ g in B i, F g ∂μ) = fun i => f i.1 := funext hBint
  rw [hfun] at h1
  have h2 : HasSum (fun i : S => f i.1) Z :=
    (hasSum_subtype_iff_of_support_subset (s := S) subset_rfl).mpr hZ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact h1.unique h2

end GlobalTheory.InertZeta
end

section

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section Herm

variable {L : Type} [Field L] {N : ℕ}

def hermJ (σ : L →+* L) (x y : Fin N → L) : L := ∑ i, σ (x i) * y i.rev

theorem hermJ_add_left (σ : L →+* L) (x x' y : Fin N → L) :
    hermJ σ (x + x') y = hermJ σ x y + hermJ σ x' y := by
  simp only [hermJ, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hermJ_add_right (σ : L →+* L) (x y y' : Fin N → L) :
    hermJ σ x (y + y') = hermJ σ x y + hermJ σ x y' := by
  simp only [hermJ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem map_hermJ {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x y : Fin N → L) :
    σ (hermJ σ x y) = hermJ σ y x := by

  simp only [hermJ, map_sum, map_mul, hσσ]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, mul_comm]

theorem dotProduct_eq_neg_hermJ {σ : L →+* L} (r b w : Fin N → L) (h : ∀ j, r j = -σ (b j.rev)) :
    r ⬝ᵥ w = -hermJ σ b w := by
  rw [hermJ, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, h, neg_mul]

end Herm

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem hermJ_mulVec (g : GU σ N) (x y : Fin N → L) :
    hermJ σ (mat g *ᵥ x) (mat g *ᵥ y) = hermJ σ x y := by
  have hconj : ∀ i k : Fin N, σ (mat g i k) = mat g⁻¹ k.rev i.rev := fun i k => by
    rw [mat_inv_apply, Fin.rev_rev, Fin.rev_rev]
  have hinner : ∀ k l : Fin N, ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l = (1 : Matrix (Fin N) (Fin N) L) k.rev l := by
    intro k l
    rw [← mat_inv_mul g, Matrix.mul_apply]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  calc hermJ σ (mat g *ᵥ x) (mat g *ᵥ y)
      = ∑ k : Fin N, ∑ l : Fin N, σ (x k) * y l * ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l := by

        simp only [hermJ, Matrix.mulVec, dotProduct, map_sum, map_mul, hconj, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k : Fin N, σ (x k) * y k.rev := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hinner, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          if_true]

theorem sigma_mem_intL {x : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (h : x ∈ intL L) : σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]
  exact h

theorem hermJ_int {ϖ : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hϖ : σ ϖ = ϖ) (e : ℕ) (x : Fin N → L)
    (h : ∀ i, ϖ ^ e * x i ∈ intL L) : ϖ ^ (2 * e) * hermJ σ x x ∈ intL L := by
  have hsum : ϖ ^ (2 * e) * hermJ σ x x = ∑ i, σ (ϖ ^ e * x i) * (ϖ ^ e * x i.rev) := by
    simp only [hermJ, Finset.mul_sum, map_mul, map_pow, hϖ]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (sigma_mem_intL hσ (h i)) (h i.rev)

end Unitary

theorem smallCorner_of_heis_dual : Heis → Dual → SmallCorner := by
  intro hH hD
  unfold SmallCorner
  intro L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr
  have hU' := hU
  unfold IsUnramInv at hU'
  obtain ⟨hσσ, hσv, hϖσ, hϖv, -⟩ := hU'

  obtain ⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev) := ⟨_, rfl⟩
  have hrb : ∀ j, r j = -σ (b j.rev) := fun j => by
    rw [hb]
    simp only [Fin.rev_rev, map_neg, hσσ, neg_neg]
  obtain ⟨b₁, hb₁⟩ : ∃ x : Fin N → L, x = (C * V * mat g₀) *ᵥ b := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x : Fin N → L, x = (C * U) *ᵥ b := ⟨_, rfl⟩
  have hsplit : b₁ + b₂ = b := by
    have hCinv : C * (U + V * mat g₀) = 1 := mul_eq_one_comm.mp hF.2.2.2.2
    rw [hb₁, hb₂, ← Matrix.add_mulVec, add_comm, Matrix.mul_assoc, ← Matrix.mul_add, hCinv,
      Matrix.one_mulVec]
  obtain ⟨τ, hτint, hτ⟩ := exists_trace_one hU
  obtain ⟨s, hs⟩ : ∃ s : L, s = hermJ σ b₁ b₁ - hermJ σ b₂ b₂ := ⟨_, rfl⟩
  have hσs : σ s = s := by rw [hs, map_sub, map_hermJ hσσ, map_hermJ hσσ]
  have hrb₁ : r ⬝ᵥ b₁ = -hermJ σ b b₁ := dotProduct_eq_neg_hermJ r b b₁ hrb
  have hnorm : -∑ j, r j * σ (r j.rev) = -hermJ σ b b := by
    rw [← dotProduct_eq_neg_hermJ r b b hrb, hb]
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  have hc : r ⬝ᵥ b₁ + τ * s + σ (r ⬝ᵥ b₁ + τ * s) = -∑ j, r j * σ (r j.rev) := by
    rw [hnorm, hrb₁, map_add (f := _), map_mul, map_neg, map_hermJ hσσ, hσs, ← hsplit]
    simp only [hermJ_add_left, hermJ_add_right]
    linear_combination s * hτ + hs
  obtain ⟨hHrad, -, hHex⟩ := hH L ϖ σ q N hU
  obtain ⟨u, hu, hur, huc⟩ := hHex r (r ⬝ᵥ b₁ + τ * s) hc
  have hcol : colOf u = b := by
    funext i
    have hi := (hHrad u hu).1 i.rev
    rw [hur, Fin.rev_rev] at hi
    rw [hb]
    simp only [hi, map_neg, hσσ, neg_neg]
  obtain ⟨h₁, h₂⟩ := (hD L ϖ σ q N hU g₀ U V C hF r b (ϖ ^ e) hrb).1 hr
  refine ⟨u, hu, hur, ?_, ?_⟩
  · rw [hur]
    exact hr
  · rw [hur, hcol, huc, ← hb₁, add_sub_cancel_left]
    have hϖint : ϖ ∈ intL L := by
      change Valued.v ϖ ≤ 1
      rw [hϖv]
      exact WithZero.coe_le_one.mpr (by decide)
    have i₁ : ϖ ^ (2 * e) * hermJ σ b₁ b₁ ∈ intL L :=
      hermJ_int hσv hϖσ e b₁ (by rw [hb₁]; exact h₁)
    have hg : mat g₀ *ᵥ b₂ = (mat g₀ * C * U) *ᵥ b := by
      rw [hb₂, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have i₂ : ϖ ^ (2 * e) * hermJ σ b₂ b₂ ∈ intL L := by
      rw [← hermJ_mulVec g₀ b₂ b₂, hg]
      exact hermJ_int hσv hϖσ e _ h₂
    have hf : ϖ ^ f = ϖ ^ (f - 2 * e) * ϖ ^ (2 * e) := by rw [← pow_add, Nat.sub_add_cancel hef]
    have hsplit' : ϖ ^ f * (τ * s) =
        τ * ϖ ^ (f - 2 * e) * (ϖ ^ (2 * e) * hermJ σ b₁ b₁ - ϖ ^ (2 * e) * hermJ σ b₂ b₂) := by
      rw [hf, hs]
      ring
    rw [hsplit']
    exact Subring.mul_mem _ (Subring.mul_mem _ hτint (Subring.pow_mem _ hϖint _)) (Subring.sub_mem _ i₁ i₂)

end GlobalTheory.InertZeta
end
end

section

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.DualLat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

def tw (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)

def IntT (t : L) (x : Fin N → L) : Prop := ∀ i, t * x i ∈ intL L

theorem IntT.add {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x + y) := fun i => by
  simp only [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)

theorem IntT.neg {t : L} {x : Fin N → L} (hx : IntT t x) : IntT t (-x) := fun i => by
  simp only [Pi.neg_apply, mul_neg]; exact neg_mem (hx i)

theorem IntT.sub {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IntT.mulVec {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hM : IsInt M) (hx : IntT t x) :
    IntT t (M *ᵥ x) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [mul_left_comm]; exact mul_mem (hM i k) (hx k)

theorem IntT.vecMul {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hx : IntT t x) (hM : IsInt M) :
    IntT t (x ᵥ* M) := fun j => by
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [← mul_assoc]; exact mul_mem (hx k) (hM k j)

theorem IntT.twist {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {t : L} {x : Fin N → L} (hx : IntT t x) :
    IntT t (tw σ x) := fun j => by
  show Valued.v (t * σ (x j.rev)) ≤ 1
  rw [map_mul, hσ, ← map_mul]; exact hx j.rev

theorem tw_tw {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x : Fin N → L) : tw σ (tw σ x) = x := by
  ext j; simp [tw, hσσ]

theorem tw_add (σ : L →+* L) (x y : Fin N → L) : tw σ (x + y) = tw σ x + tw σ y := by
  ext j; simp [tw]

theorem tw_neg (σ : L →+* L) (x : Fin N → L) : tw σ (-x) = -tw σ x := by
  ext j; simp [tw]

theorem tw_vecMul {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (g : GU σ N) (x : Fin N → L) :
    tw σ x ᵥ* mat g = tw σ (mat g⁻¹ *ᵥ x) := by
  ext j

  simp only [tw, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mat_inv_apply, hσσ, Fin.rev_rev]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
  simp [mul_comm]

end GlobalTheory.InertZeta.DualLat

namespace GlobalTheory.InertZeta

open DualLat

theorem dual_inter_eq_sum : Dual := by
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσ, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hgC, e⟩ := hF
  have e' : C * (U + V * mat g) = 1 := mul_eq_one_comm.1 e
  have hr' : r = -tw σ b := by ext j; simp [tw, hr]
  have m1 : C * V * mat g = 1 - C * U := by
    rw [Matrix.mul_assoc, ← e', Matrix.mul_add]; abel
  have m2 : C * V * mat g * mat g⁻¹ = C * V := by rw [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
  have hCU : C * U = 1 - C * V * mat g := by rw [m1]; abel
  have m3 : mat g * C * U * mat g⁻¹ = 1 - mat g * C * V := by
    rw [Matrix.mul_assoc (mat g) C U, hCU]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, mat_mul_inv]
  change IntT t (r ᵥ* C) ↔ IntT t ((C * V * mat g) *ᵥ b) ∧ IntT t ((mat g * C * U) *ᵥ b)
  constructor
  · intro hρ
    have h1 : r = (r ᵥ* C) ᵥ* U + ((r ᵥ* C) ᵥ* V) ᵥ* mat g := by
      rw [Matrix.vecMul_vecMul (r ᵥ* C) V, ← Matrix.vecMul_add, Matrix.vecMul_vecMul, e', Matrix.vecMul_one]
    have hl₁ : IntT t (-tw σ ((r ᵥ* C) ᵥ* U)) := ((hρ.vecMul hUi).twist hσ).neg
    have hl₂ : IntT t (-tw σ ((r ᵥ* C) ᵥ* V)) := ((hρ.vecMul hVi).twist hσ).neg
    have htw : tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)) = -r := by
      rw [tw_add, ← tw_vecMul hσσ, tw_neg, tw_neg, tw_tw hσσ, tw_tw hσσ, Matrix.neg_vecMul]
      conv_rhs => rw [h1]
      abel
    have hb : b = -tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V) := by
      calc b = tw σ (tw σ b) := (tw_tw hσσ b).symm
        _ = tw σ (tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V))) := by
          rw [htw, hr', neg_neg]
        _ = _ := tw_tw hσσ _
    rw [hb]
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m2, m1, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (hl₁.sub (IntT.mulVec (hCi.mul hUi) hl₁)).add (IntT.mulVec (hCi.mul hVi) hl₂)
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m3, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (IntT.mulVec (hgC.mul hUi) hl₁).add (hl₂.sub (IntT.mulVec (hgC.mul hVi) hl₂))
  · rintro ⟨h1, h2⟩
    have hb : b = (C * V * mat g) *ᵥ b + (C * U) *ᵥ b := by
      rw [← Matrix.add_mulVec, m1, sub_add_cancel, Matrix.one_mulVec]
    have key : ∀ b₁ b₂ : Fin N → L,
        -tw σ (b₁ + b₂) ᵥ* C = -(tw σ b₁ ᵥ* C) - tw σ (mat g *ᵥ b₂) ᵥ* (mat g * C) := by
      intro b₁ b₂
      rw [← Matrix.vecMul_vecMul, tw_vecMul hσσ, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, tw_add,
        Matrix.neg_vecMul, Matrix.add_vecMul]
      abel
    have h2' : IntT t (mat g *ᵥ ((C * U) *ᵥ b)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]; exact h2
    rw [hr', hb, key]
    exact ((h1.twist hσ).vecMul hCi).neg.sub ((h2'.twist hσ).vecMul hgC)

end GlobalTheory.InertZeta

end
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.cyclicVector_of_separable_charpoly_field : GlobalTheory.RegSS.CyclicField := by
  first | exact @GlobalTheory.RegSS.cyclicField | exact GlobalTheory.RegSS.cyclicField | (intros; apply GlobalTheory.RegSS.cyclicField <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.laurentPolynomial_character_isMonomial : GlobalTheory.RegSS.CharacterMonomial := by
  first | exact @GlobalTheory.RegSS.characterMonomial | exact GlobalTheory.RegSS.characterMonomial | (intros; apply GlobalTheory.RegSS.characterMonomial <;> assumption)
end
