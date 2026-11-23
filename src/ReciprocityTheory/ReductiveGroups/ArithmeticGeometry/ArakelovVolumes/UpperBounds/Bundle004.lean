module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfB
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

theorem coordL {n : ℕ} (W : V n → ℂ) (S : Fin n → V n → ℂ) (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0)
    (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => S k z / W z : V n)) 0).det ≠ 0) :
    ∃ L : V n ≃L[ℂ] V n, (∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z) ∧
      (fun z => (WithLp.toLp 2 fun k => S k z / W z : V n) - L z) =o[𝓝 0] fun z => z := by
  classical
  let F : V n → V n := fun z => (WithLp.toLp 2 fun k => S k z / W z : V n)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  have hcomp : ∀ k, DifferentiableAt ℂ (fun y => S k y / W y) 0 :=
    fun k => ((hS k).div hW hW0).differentiableAt
  have hG : DifferentiableAt ℂ (fun z k => S k z / W z) 0 := differentiableAt_pi.2 hcomp
  have hFd : DifferentiableAt ℂ F 0 := e.symm.differentiableAt.comp 0 hG
  have hdet' : LinearMap.det (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) ≠ 0 := hdet
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) hdet').toContinuousLinearEquiv
  have hL : ∀ z, L z = fderiv ℂ F 0 z := fun z => rfl
  refine ⟨L, fun k z => ?_, ?_⟩
  · rw [hL]
    have h1' := ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).hasFDerivAt (x := F 0)).comp (0 : V n) hFd.hasFDerivAt
    have h1 : HasFDerivAt (fun y => S k y / W y)
        ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).comp (fderiv ℂ F 0)) 0 := h1'
    rw [h1.fderiv]
    rfl
  · have h2 := hFd.hasFDerivAt.isLittleO
    have hF0 : F 0 = 0 := by
      apply PiLp.ext
      intro k
      simp [F, hS0]
    simp only [hF0, sub_zero] at h2
    exact h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal

noncomputable section

variable {p q : ℕ}

theorem sumBdJf_eq_diag : Jf p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Jf, Matrix.diagonal_apply, Matrix.one_apply] <;>
    split_ifs <;> simp

private theorem Jf_mul_self_eq_one : Jf p q * Jf p q = 1 := by
  rw [sumBdJf_eq_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

private theorem inv_eq_lemma_2 {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    g⁻¹ = Jf p q * gᴴ * Jf p q := by
  have hg : gᴴ * Jf p q * g = Jf p q := h
  apply Matrix.inv_eq_left_inv
  calc Jf p q * gᴴ * Jf p q * g = Jf p q * (gᴴ * Jf p q * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jf_mul_self_eq_one]

theorem sumBd_inv_entry {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g)
    (i j : Fin p ⊕ Fin q) : ‖g⁻¹ i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ =
      ‖g j i - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) j i‖ := by
  have hs : ∀ z : ℂ, ‖(starRingEnd ℂ) z - 1‖ = ‖z - 1‖ := fun z => by
    have h0 := Complex.norm_conj (z - 1)
    rwa [map_sub, map_one] at h0
  rw [inv_eq_lemma_2 h, sumBdJf_eq_diag]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij, Ne.symm hij]
  · simp
  · simp
  · by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij, Ne.symm hij]

theorem sumBd_sep {f : ℕ} (Γ : Subgroup (Fin f → GL (Fin p ⊕ Fin q) ℂ)) (hd : DiscreteTopology Γ)
    (hU : ∀ γ ∈ Γ, ∀ k, IsUpq ((γ k : GL (Fin p ⊕ Fin q) ℂ) :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ Γ, γ ≠ 1 → ∃ k i j,
      c ≤ ‖((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j -
        (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
  by_contra hcon
  push_neg at hcon
  have hc' : ∀ n : ℕ, ∃ γ ∈ Γ, γ ≠ 1 ∧ ∀ k i j,
      ‖((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j -
        (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ < 1 / ((n : ℝ) + 1) :=
    fun n => hcon _ (by positivity)
  choose γ hγΓ hγ1 hγc using hc'
  have hent : ∀ k i j, Filter.Tendsto
      (fun n => ((γ n k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)
      Filter.atTop (𝓝 ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)) := by
    intro k i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hγc n k i j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv : ∀ k i j, Filter.Tendsto
      (fun n => (((γ n k)⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)
      Filter.atTop (𝓝 ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)) := by
    intro k i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Matrix.coe_units_inv, sumBd_inv_entry (hU _ (hγΓ n) k) i j]
    exact (hγc n k j i).le
  have hT : Filter.Tendsto γ Filter.atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [(Units.isEmbedding_embedProduct (M := Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).tendsto_nhds_iff]
    simp only [Function.comp_def, Units.embedProduct_apply, Pi.one_apply, inv_one, Units.val_one]
    refine Filter.Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hent k i j
    · exact (MulOpposite.continuous_op.tendsto _).comp
        (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hinv k i j)
  have hδ : Filter.Tendsto (fun n => (⟨γ n, hγΓ n⟩ : Γ)) Filter.atTop (𝓝 1) := tendsto_subtype_rng.mpr hT
  have hev : ∀ᶠ n in Filter.atTop, (⟨γ n, hγΓ n⟩ : Γ) ∈ ({1} : Set Γ) :=
    hδ ((isOpen_discrete ({1} : Set Γ)).mem_nhds rfl)
  obtain ⟨n, hn⟩ := hev.exists
  exact hγ1 n (congrArg Subtype.val hn)

theorem sumBd_inv_eq {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    g⁻¹ = Jf p q * gᴴ * Jf p q := inv_eq_lemma_2 h

theorem sumBd_mul_inv {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) : g * g⁻¹ = 1 := by
  have hg : gᴴ * Jf p q * g = Jf p q := h
  have hl : g⁻¹ * g = 1 := by
    rw [sumBd_inv_eq h]
    calc Jf p q * gᴴ * Jf p q * g = Jf p q * (gᴴ * Jf p q * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Jf_mul_self_eq_one]
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl)

theorem sumBd_inv_entry' {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g)
    (i j : Fin p ⊕ Fin q) : ‖g⁻¹ i j‖ = ‖g j i‖ := by
  rw [sumBd_inv_eq h, sumBdJf_eq_diag]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem sumBd_sep_diff {g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsUpq g) {R c : ℝ}
    (hR : 0 < R) (hc0 : 0 < c) (hgR : ∀ i j, ‖g i j‖ ≤ R) {i j : Fin p ⊕ Fin q}
    (hc : c ≤ ‖(h * g⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) :
    ∃ l, c / (((p + q : ℕ) : ℝ) + 1) / R ≤ ‖h i l - g i l‖ := by
  by_contra hcon
  push_neg at hcon
  have hN : (0 : ℝ) < ((p + q : ℕ) : ℝ) + 1 := by positivity
  have hgi : ∀ l, ‖g⁻¹ l j‖ ≤ R := fun l => by rw [sumBd_inv_entry' hg]; exact hgR j l
  have e : (h * g⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j = ((h - g) * g⁻¹) i j := by
    rw [Matrix.sub_mul, sumBd_mul_inv hg, Matrix.sub_apply]
  rw [e, Matrix.mul_apply] at hc
  have hle : ‖∑ l, (h - g) i l * g⁻¹ l j‖ ≤ ∑ _l : Fin p ⊕ Fin q, c / (((p + q : ℕ) : ℝ) + 1) / R * R := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, Matrix.sub_apply]
    exact mul_le_mul (hcon l).le (hgi l) (norm_nonneg _) (by positivity)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
    div_mul_cancel₀ _ hR.ne'] at hle
  have h3 : ((p + q : ℕ) : ℝ) * (c / (((p + q : ℕ) : ℝ) + 1)) < c := by
    rw [mul_div_assoc', div_lt_iff₀ hN]
    nlinarith
  push_cast at hle h3
  linarith

theorem sumBd_count {f : ℕ} {ι : Type*} (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    {R η : ℝ} (hη : 0 < η)
    (hsep2 : ∀ a, (∀ k i j, ‖x a k i j‖ ≤ R) → ∀ b, (∀ k i j, ‖x b k i j‖ ≤ R) → a ≠ b →
      ∃ k i j, 2 * η ≤ ‖x b k i j - x a k i j‖) :
    ({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard ≤
      ((Fintype.piFinset fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
        Finset.Icc (-⌈R / η⌉) ⌈R / η⌉).card : ℕ∞) := by
  classical
  let S : Set ι := {a | ∀ k i j, ‖x a k i j‖ ≤ R}
  let val : ι → Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool → ℝ := fun a t =>
    if t.2.2.2 then (x a t.1 t.2.1 t.2.2.1).re else (x a t.1 t.2.1 t.2.2.1).im
  let φ : ι → (Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool → ℤ) := fun a t => ⌊val a t / η⌋
  have hmaps : ∀ a ∈ S, φ a ∈ Fintype.piFinset (fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
      Finset.Icc (-⌈R / η⌉) ⌈R / η⌉) := by
    intro a ha
    rw [Fintype.mem_piFinset]
    intro t
    rw [Finset.mem_Icc]
    have hb := ha t.1 t.2.1 t.2.2.1
    have hv : |val a t| ≤ R := by
      simp only [val]
      split_ifs
      · exact (Complex.abs_re_le_norm _).trans hb
      · exact (Complex.abs_im_le_norm _).trans hb
    rw [abs_le] at hv
    have h1 : -(R / η) ≤ val a t / η := by rw [← neg_div]; exact div_le_div_of_nonneg_right hv.1 hη.le
    have h2 : val a t / η ≤ R / η := div_le_div_of_nonneg_right hv.2 hη.le
    constructor
    · apply Int.le_floor.2
      push_cast
      linarith [Int.le_ceil (R / η)]
    · exact Int.cast_le.1 ((Int.floor_le _).trans (h2.trans (Int.le_ceil _)))
  have hinj : Set.InjOn φ S := by
    intro a ha b hb hab
    by_contra hne
    obtain ⟨k, i, j, hsep⟩ := hsep2 a ha b hb hne
    have hre := congrFun hab (k, i, j, true)
    have him := congrFun hab (k, i, j, false)
    simp only [φ, val, if_true, Bool.false_eq_true, if_false] at hre him
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hre
    have h2 := Int.abs_sub_lt_one_of_floor_eq_floor him
    rw [← sub_div, abs_div, abs_of_pos hη, div_lt_one hη] at h1 h2
    have h3 := Complex.norm_le_abs_re_add_abs_im (x b k i j - x a k i j)
    simp only [Complex.sub_re, Complex.sub_im] at h3
    rw [abs_sub_comm] at h1 h2
    linarith
  calc S.encard = (φ '' S).encard := hinj.encard_image.symm
    _ ≤ ((Fintype.piFinset fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
          Finset.Icc (-⌈R / η⌉) ⌈R / η⌉ : Finset _) : Set _).encard :=
        Set.encard_le_encard (by rintro _ ⟨a, ha, rfl⟩; exact hmaps a ha)
    _ = _ := Set.encard_coe_eq_coe_finsetCard _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def LA (A : ι → Matrix (Fin r) (Fin r) ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun v i := (A i.1 * Mt v i.1) i.2.1 i.2.2
  map_add' v v' := by
    funext i; simp only [Pi.add_apply, Matrix.mul_apply, Mt, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i; simp only [Pi.smul_apply, Matrix.mul_apply, Mt, Matrix.of_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring

def eB (ι : Type*) (r : ℕ) : Ix ι r ≃ Fin r × (ι × Fin r) where
  toFun i := (i.2.1, (i.1, i.2.2))
  invFun j := (j.2.1, j.1, j.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.det (LA A) = ∏ τ, (A τ).det ^ r := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ix ι r)), ← Matrix.det_reindex_self (eB ι r)]
  have hM : Matrix.reindex (eB ι r) (eB ι r)
      (LinearMap.toMatrix (Pi.basisFun ℂ (Ix ι r)) (Pi.basisFun ℂ (Ix ι r)) (LA A)) =
      Matrix.blockDiagonal (fun k : ι × Fin r => A k.1) := by
    ext ⟨a, τ, b⟩ ⟨c, τ', d⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Pi.basisFun_repr, Matrix.blockDiagonal_apply]
    simp only [eB, Equiv.coe_fn_symm_mk, LA, LinearMap.coe_mk, AddHom.coe_mk, Mt, Matrix.mul_apply,
      Matrix.of_apply]
    by_cases h : (τ, b) = (τ', d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [if_pos rfl, Finset.sum_eq_single c]
      · simp
      · intro k _ hk
        simp [Pi.single_apply, hk]
      · simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ((τ, k, b) : Ix ι r) ≠ (τ', c, d) := by
        intro he
        apply h
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨he.1, he.2.2⟩
      simp [Pi.single_apply, this]
  rw [hM, Matrix.det_blockDiagonal, Fintype.prod_prod_type]
  simp [Finset.prod_const]

theorem lintegral_comp_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ τ, (A τ).det ≠ 0)
    {F : (Ix ι r → ℂ) → ENNReal} (hF : Measurable F) :
    ∫⁻ v, F (LA A v) = ENNReal.ofReal (Complex.normSq (∏ τ, (A τ).det ^ r))⁻¹ * ∫⁻ v, F v := by
  have hdet : LinearMap.det ((LA A).restrictScalars ℝ) = Complex.normSq (∏ τ, (A τ).det ^ r) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_LA]
  have hne : LinearMap.det ((LA A).restrictScalars ℝ) ≠ 0 := by
    rw [hdet, Ne, Complex.normSq_eq_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hA τ)
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Ix ι r → ℂ))) hne
  have hmeas : Measurable ((LA A).restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫⁻ v, F (LA A v) = ∫⁻ v, F ((LA A).restrictScalars ℝ v) := rfl
    _ = ∫⁻ v, F v ∂(Measure.map ((LA A).restrictScalars ℝ) volume) :=
        (lintegral_map hF hmeas).symm
    _ = _ := by
        rw [hmap, lintegral_smul_measure, hdet,
          abs_of_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg _)), smul_eq_mul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end
