module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.NumberTheory.LocalField.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.IwJac

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

variable {k n}

def tor (ϖ : kˣ) (x : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => ϖ ^ x i

end GlobalTheory.CompanionTheory.IwJac

end
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_prod_symm_eq_diag_mul_prs_sq {n : ℕ} (g : Fin n → Fin n → ℂ) (hg : ∀ a b, g a b = g b a) :
    ∏ a, ∏ b, g a b = (∏ a, g a a) * (∏ p ∈ prs n, g p.1 p.2) ^ 2 := by
  have h1 : ∏ a, ∏ b, g a b = ∏ p : Fin n × Fin n, g p.1 p.2 :=
    (Fintype.prod_prod_type' (f := g)).symm
  have hd : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => p.1 = p.2),
      g p.1 p.2 = ∏ a, g a a := by
    refine Finset.prod_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro a _; simp
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      ext <;> simp [this]
    · intro a _; rfl
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      simp [← this]
  have ho : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => ¬ p.1 = p.2),
      g p.1 p.2 = ∏ p ∈ prs n, g p.1 p.2 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [prs, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hp.1) (Ne.symm hp.2)
    · intro p hp
      have hlt : p.1 < p.2 := by simpa [prs] using hp
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨not_lt.mpr hlt.le, hlt.ne'⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; simpa using hg p.1 p.2
  rw [h1, ← Finset.prod_filter_mul_prod_filter_not univ (fun p : Fin n × Fin n => p.1 < p.2),
    ← Finset.prod_filter_mul_prod_filter_not (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2)
      (fun p => p.1 = p.2), hd, ho]
  change (∏ p ∈ prs n, g p.1 p.2) * _ = _
  ring

theorem prod_one_add_div_mul_prod_pow {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, z a ≠ 0) :
    (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1)
      = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  have hZ : (∏ a, z a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hz a
  have h1 : ∏ a, ∏ b, (1 + z a / z b) = (∏ a, ∏ b, (z a + z b)) / (∏ a, z a) ^ n := by
    have hterm : ∀ a b, 1 + z a / z b = (z a + z b) / z b := by
      intro a b
      field_simp [hz b]
      ring
    simp only [hterm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h2 : ∏ a, ∏ b, (z a + z b) = 2 ^ n * (∏ a, z a) * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
    rw [prod_prod_symm_eq_diag_mul_prs_sq (fun a b => z a + z b) (fun a b => add_comm _ _)]
    have : ∏ a, (z a + z a) = 2 ^ n * ∏ a, z a := by
      simp only [← two_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [this]
  have h3 : (∏ a, z a) * (∏ a, z a) ^ (n - 1) = (∏ a, z a) ^ n := by
    rcases n with _ | m
    · simp
    · simp [pow_succ, mul_comm]
  rw [h1, h2]
  field_simp
  rw [mul_comm (∏ a, z a), ← h3]
  ring

end GlobalTheory.CompanionTheory.CoefId
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

lemma prod_prs_eq_iter {n : ℕ} (f : Fin n × Fin n → ℂ) :
    ∏ p ∈ prs n, f p = ∏ i : Fin n, ∏ j ∈ Ioi i, f (i, j) := by
  apply Finset.prod_finset_product
  intro p
  simp [prs]

lemma det_rev_vandermonde {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) *
        ∏ p ∈ prs n, (v p.2 - v p.1) := by
  have h : (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i j
    have : n - 1 - (j : ℕ) = n - (j + 1) := by omega
    simp [Matrix.vandermonde_apply, Fin.val_rev, this]
  rw [h, Matrix.det_permute', Matrix.det_vandermonde, prod_prs_eq_iter]

theorem det_vandermonde_sq {n : ℕ} (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det *
        ∏ p ∈ prs n, (z p.1 + z p.2) := by
  rw [det_rev_vandermonde (fun i => z i ^ 2), det_rev_vandermonde z, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  ring

end GlobalTheory.CompanionTheory.CoefId
end
end

section

open scoped Matrix Topology

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem isOpen_posOn (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} := by
  set K : Set (Fin n → ℂ) := (S : Set (Fin n → ℂ)) ∩ Metric.sphere 0 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left S.closed_of_finiteDimensional
  let F : Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → ℝ := fun Z w => ε * (star w ⬝ᵥ Z.mulVec w).re
  have hF : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => F p.1 p.2) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)))
  have hscale : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (c : ℝ),
      F Z ((c : ℂ) • w) = c ^ 2 * F Z w := by
    intro Z w c
    simp only [F, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
    ring
  have heq : {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} = {Z | ∀ w ∈ K, 0 < F Z w} := by
    ext Z
    constructor
    · rintro hZ w ⟨hwS, hw1⟩
      refine hZ w hwS ?_
      rintro rfl
      simp at hw1
    · intro hZ w hwS hw0
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ K := by
        refine ⟨S.smul_mem _ hwS, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
      have h2 := hZ _ hmem
      rw [hscale] at h2
      exact pos_of_mul_pos_right h2 (by positivity)
  rw [heq, isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  exact hKc.eventually_forall_of_forall_eventually fun w hw =>
    (hF.tendsto (Z₀, w)).eventually (lt_mem_nhds (hZ₀ w hw))

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open scoped ComplexConjugate

def blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks b (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) (star u))
      (Matrix.of fun _ _ => (d : ℂ)))

theorem blkM_mem {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) :
    blkM (b : Matrix (Fin n) (Fin n) ℂ) u d ∈ hermC (n + 1) := by
  have hb : (b : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b.2
  rw [mem_hermC]
  unfold blkM
  simp only [Matrix.reindex_apply]
  apply Matrix.IsHermitian.submatrix
  apply Matrix.IsHermitian.fromBlocks hb
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · ext i j
    simp [Matrix.conjTranspose_apply]

def blk {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) : hermC (n + 1) :=
  ⟨blkM (b : Matrix (Fin n) (Fin n) ℂ) u d, blkM_mem b u d⟩

theorem continuous_blkM {n : ℕ} :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) × ℝ => blkM x.1 x.2.1 x.2.2) := by
  refine continuous_matrix fun i j => ?_
  unfold blkM
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.star_apply,
      Matrix.of_apply]
  all_goals fun_prop

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

theorem continuous_phaseM_X {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (B : W → Matrix (Fin n) (Fin n) ℂ) :
    Continuous (phaseM J B) := by
  unfold phaseM
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ => ?_
  refine continuous_const.mul ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun X : W → Fin n → Fin M → ℂ => X w c i := by fun_prop
  have h2 : Continuous fun X : W → Fin n → Fin M → ℂ => X w a j := by fun_prop
  first
    | exact ((Complex.continuous_conj.comp h1).mul continuous_const).mul (by fun_prop)
    | exact ((Complex.continuous_conj.comp h2).mul continuous_const).mul (by fun_prop)

theorem continuous_phaseM_b {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (X : W → Fin n → Fin M → ℂ) :
    Continuous fun b : W → hermC n =>
      phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X := by
  unfold phaseM
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ => ?_
  refine Continuous.mul ?_ continuous_const
  have h0 : Continuous fun b : W → hermC n => (b w : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.comp (continuous_apply w)
  have h1 : Continuous fun m : Matrix (Fin n) (Fin n) ℂ => m a c :=
    (continuous_apply c).comp (continuous_apply a)
  exact h1.comp h0

theorem integrable_comp {E : Type} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (N : ℕ) (e : E ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (fun X => f (e X)) μ := by
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hs := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ)
    (volume : Measure (Fin N → ℝ))
  have hi : Integrable f (Measure.map e μ) := by
    rw [hs]
    exact (f.integrable (μ := volume)).smul_measure_nnreal
  exact hi.comp_measurable he.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz
    (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e)
    (hes : Continuous e.symm) (f : SchwartzMap (Fin N → ℝ) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure) :
    Continuous (coreC J μ (fun X => f (e X))) := by
  have hint := Cont.integrable_comp N e he hes f μ
  have hg : Continuous fun X => f (e X) := f.continuous.comp he
  have hnorm : ∀ t : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    have : (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  unfold coreC
  refine continuous_of_dominated (bound := fun X => ‖f (e X)‖) ?_ ?_ hint.norm ?_
  · intro b
    refine Continuous.aestronglyMeasurable (hg.mul ?_)
    have := Cont.continuous_phaseM_X J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ))
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp this))
  · intro b
    refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, hnorm, mul_one]
  · refine Filter.Eventually.of_forall fun X => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (Cont.continuous_phaseM_b J X))))
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntSwap

def swapW (k : Type) [Field k] (n : ℕ) : GL (Ix n) k :=
  ⟨fromBlocks 0 1 1 0, fromBlocks 0 1 1 0,
    by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

lemma lowerRightBlock_mul_block_swap {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k) :
    dBlk (g * swapW k n) = lowerLeftBlock g := by
  show (g.1 * fromBlocks 0 1 1 0).toBlocks₂₂ = g.1.toBlocks₂₁
  conv_lhs => rw [← fromBlocks_toBlocks g.1]
  rw [fromBlocks_multiply]
  simp

theorem card_lower_left_rank_eq_card_lower_right_rank : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  intro k _ _ n i
  exact Nat.card_congr ((Equiv.mulRight (swapW k n)).subtypeEquiv (fun g => by
    rw [Equiv.coe_mulRight, lowerRightBlock_mul_block_swap]))

end GlobalTheory.CompanionTheory.Jp.CntSwap
end

section

noncomputable section

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.AvgRight

theorem avgK_right_invariant : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  intro O _ _ n ϖ φ hφ j
  have hout : ∀ x : GL (Ix n) O,
      φ (Quotient.out (QuotientGroup.mk x : GL (Ix n) O ⧸ Gam2 (n := n) ϖ)) = φ x := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gam2 (n := n) ϖ) x
    rw [hh]
    exact hφ x h.1 h.2
  have hshift : ∀ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ,
      φ (Quotient.out u * j) =
        φ (Quotient.out (u * (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))) := by
    intro u
    rw [← hout (Quotient.out u * j)]
    congr 2
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  unfold avgK
  congr 1
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))
    (f := fun u => φ (Quotient.out u))

end GlobalTheory.CompanionTheory.Jp.AvgRight

end
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedUnique

theorem exists_pM_of_low_zero {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k)
    (hg : g.1.toBlocks₂₁ = 0) :
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k), g = pM a d b := by
  have hgb : g.1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ 0 g.1.toBlocks₂₂ := by
    rw [← hg, fromBlocks_toBlocks]
  have hdet : g.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [hgb, det_fromBlocks_zero₂₁] at hdet
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), g.1.toBlocks₁₂, ?_⟩
  apply Units.ext
  exact hgb

theorem low_inv_mul_pM {R : Type} [CommRing R] {n : ℕ} (a₁ d₁ a₂ d₂ : GL (Fin n) R)
    (b₁ b₂ : Matrix (Fin n) (Fin n) R) :
    (((pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ : GL (Ix n) R)).1.toBlocks₂₁ = 0 := by
  have h1 : ((pM a₁ d₁ b₁ : GL (Ix n) R)).1 = fromBlocks a₁.1 b₁ 0 d₁.1 := rfl
  have h2 : (((pM a₂ d₂ b₂)⁻¹ : GL (Ix n) R)).1 =
      fromBlocks (a₂⁻¹).1 (-((a₂⁻¹).1 * b₂ * (d₂⁻¹).1)) 0 (d₂⁻¹).1 := rfl
  rw [Units.val_mul, h1, h2, fromBlocks_multiply]
  simp [toBlocks_fromBlocks₂₁]

theorem red_unique : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  intro O L _ _ _ _ _ _ n w κ h₁ h₂ r₁ r₂
  obtain ⟨a₁, d₁, b₁, κ₁, e₁, rfl⟩ := r₁
  obtain ⟨a₂, d₂, b₂, κ₂, e₂, rfl⟩ := r₂
  obtain ⟨c, hcd⟩ : ∃ c : GL (Ix n) O, c = κ₂ * κ₁⁻¹ := ⟨_, rfl⟩
  have hc : inL (L := L) c = (pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ := by
    have e : pM a₁ d₁ b₁ * inL (L := L) κ₁ = pM a₂ d₂ b₂ * inL (L := L) κ₂ := e₁.symm.trans e₂
    rw [hcd, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e, mul_inv_cancel_right]
  have hlow : (inL (L := L) c).1.toBlocks₂₁ = 0 := by
    rw [hc]; exact low_inv_mul_pM _ _ _ _ _ _
  have hO : ∀ i j, c.1 (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have h0 : algebraMap O L (c.1 (Sum.inr i) (Sum.inl j)) = 0 := congrFun (congrFun hlow i) j
    exact IsFractionRing.injective O L (h0.trans (map_zero _).symm)
  have hk : (resK c).1.toBlocks₂₁ = 0 := by
    ext i j
    change IsLocalRing.residue O (c.1 (Sum.inr i) (Sum.inl j)) = 0
    rw [hO, map_zero]
  obtain ⟨a, d, b, hp⟩ := exists_pM_of_low_zero _ hk
  refine ⟨a, d, b, ?_⟩
  rw [← hp, ← map_mul, hcd, inv_mul_cancel_right]

end GlobalTheory.CompanionTheory.Jp.RedUnique

end
end
