module

public import ReciprocityTheory.SemistableReduction.Bundle002
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle003
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable abbrev unitBallRing (K : Type*) [NormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

theorem mem_unitBallRing {K : Type*} [NormedField K] [IsUltrametricDist K] (x : K) :
    x ∈ unitBallRing K ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]

theorem residue_eq_zero_iff_norm_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : unitBallRing K) :
    IsLocalRing.residue (unitBallRing K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx1 : ‖(x : K)‖ ≤ 1 := (mem_unitBallRing (x : K)).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx1 fun h1 => hnu ?_
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : K)⁻¹ ∈ unitBallRing K := by
      rw [mem_unitBallRing, norm_inv, h1, inv_one]
    have hm : x * ⟨(x : K)⁻¹, hinv⟩ = 1 := Subtype.ext (by simp [hx0])
    exact ⟨⟨x, ⟨(x : K)⁻¹, hinv⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  · intro hlt hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h := congrArg (fun t : unitBallRing K => ‖(t : K)‖) hy
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, norm_mul, norm_one] at h
    have hy1 : ‖(y : K)‖ ≤ 1 := (mem_unitBallRing (y : K)).1 y.2
    nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]

theorem infinite_residues {K : Type*} [NormedField K] [IsUltrametricDist K] (K₀ : Subfield K)
    (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) :
    {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}.Infinite := by
  classical
  intro hfin
  have hrep : ∀ y ∈ {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y},
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y :=
    fun y hy => hy
  choose! r hr using hrep
  unfold ResidueFieldInfiniteOn at hK₀
  obtain ⟨x, hxK, hx1, hxs⟩ := hK₀ (insert 0 (hfin.toFinset.image fun y => (r y : K)))
  have hx0 : 1 ≤ ‖x‖ := by simpa using hxs 0 (Finset.mem_insert_self _ _)
  have hxn : ‖x‖ = 1 := le_antisymm hx1 hx0
  let xb : unitBallRing K := ⟨x, (mem_unitBallRing x).2 hx1⟩
  have hmem : IsLocalRing.residue _ xb ∈ {y : IsLocalRing.ResidueField (unitBallRing K) |
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y} :=
    ⟨xb, hxK, hxn, rfl⟩
  obtain ⟨-, -, hreq⟩ := hr _ hmem
  have h0 : IsLocalRing.residue _ (xb - r (IsLocalRing.residue _ xb)) = 0 := by
    rw [map_sub, hreq, sub_self]
  rw [residue_eq_zero_iff_norm_lt_one] at h0
  have h0' : ‖x - (r (IsLocalRing.residue _ xb) : K)‖ < 1 := by simpa [xb] using h0
  have h1 := hxs (r (IsLocalRing.residue _ xb) : K)
    (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 hmem, rfl⟩))
  linarith

theorem exists_torus_point_one_le_norm_sum {K : Type*} [NormedField K] [IsUltrametricDist K]
    (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) {n : ℕ}
    (F : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → K) (ha : ∀ χ, ‖a χ‖ ≤ 1)
    (χ₀ : Fin n → ℤ) (hχ₀ : χ₀ ∈ F) (ha₀ : ‖a χ₀‖ = 1) :
    ∃ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) ∧
      1 ≤ ‖∑ χ ∈ F, a χ * ∏ i, τ i ^ χ i‖ := by
  classical
  let N : ℕ := ∑ χ ∈ F, ∑ i, (χ i).natAbs
  have hN : ∀ χ ∈ F, ∀ i, 0 ≤ χ i + N := by
    intro χ hχ i
    have h1 : (χ i).natAbs ≤ ∑ j, (χ j).natAbs :=
      Finset.single_le_sum (f := fun j => (χ j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j, (χ j).natAbs ≤ N :=
      Finset.single_le_sum (f := fun χ : Fin n → ℤ => ∑ j, (χ j).natAbs)
        (fun _ _ => Nat.zero_le _) hχ
    omega
  let e : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun χ =>
    Finsupp.equivFunOnFinite.symm (fun i => (χ i + N).toNat)
  have he : ∀ χ ∈ F, ∀ χ' ∈ F, e χ = e χ' → χ = χ' := by
    intro χ hχ χ' hχ' h
    funext i
    have h3 := congrArg (fun f : Fin n →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h3
    have h1 := hN χ hχ i
    have h2 := hN χ' hχ' i
    omega
  let aO : (Fin n → ℤ) → unitBallRing K := fun χ => ⟨a χ, (mem_unitBallRing _).2 (ha χ)⟩
  let P : MvPolynomial (Fin n) (unitBallRing K) := ∑ χ ∈ F, monomial (e χ) (aO χ)
  have hcoeff : AddMonoidAlgebra.coeff P (e χ₀) = aO χ₀ := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem χ₀ hχ₀]
    · simp
    · intro χ hχ hne
      rw [ite_eq_right]
      exact fun h => hne (he χ hχ χ₀ hχ₀ h)
  have hQ : MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P ≠ 0 := by
    intro h0
    have h4 := congrArg (AddMonoidAlgebra.coeff · (e χ₀)) h0
    rw [coeff_map, hcoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      residue_eq_zero_iff_norm_lt_one] at h4
    exact absurd ha₀ (ne_of_lt h4)
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ Set.pi Set.univ (fun _ : Fin n =>
      {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
        (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}),
      eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (funext_set _ (fun _ => infinite_residues K₀ hK₀) (fun x hx => by
      rw [hcon x hx, map_zero]))
  choose σ hσK hσ1 hσr using fun i => hy i (Set.mem_univ i)
  refine ⟨fun i => (σ i : K), fun i => ⟨hσK i, hσ1 i⟩, ?_⟩
  have hr : IsLocalRing.residue (unitBallRing K) (eval σ P) ≠ 0 := by
    have hy' : y = fun i => IsLocalRing.residue (unitBallRing K) (σ i) :=
      funext fun i => (hσr i).symm
    have h5 : eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) =
        IsLocalRing.residue (unitBallRing K) (eval σ P) := by
      rw [eval_map, hy', MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hom_eval₂,
        RingHom.comp_id]
    rwa [h5] at hyne
  have hge : 1 ≤ ‖((eval σ P : unitBallRing K) : K)‖ :=
    not_lt.1 fun h => hr ((residue_eq_zero_iff_norm_lt_one _).2 h)
  have hσ0 : ∀ i, (σ i : K) ≠ 0 := fun i h => by
    have h6 := hσ1 i
    rw [h, norm_zero] at h6
    exact zero_ne_one h6
  have hval : ((eval σ P : unitBallRing K) : K) =
      ∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ (χ i + N).toNat := by

    simp only [P, map_sum, eval_monomial]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp [e, aO]
  have hterm : ∀ χ ∈ F, ∏ i, (σ i : K) ^ (χ i + N).toNat =
      (∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    intro χ hχ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hN χ hχ i), zpow_add₀ (hσ0 i), zpow_natCast]
  have hsum : ((eval σ P : unitBallRing K) : K) =
      (∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    rw [hval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hterm χ hχ, mul_assoc]
  have hnorm1 : ‖∏ i, (σ i : K) ^ N‖ = 1 := by
    rw [norm_prod]
    simp [norm_pow, hσ1]
  rw [hsum, norm_mul, hnorm1, mul_one] at hge
  exact hge

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_eval_smul_of_isHomogeneous {σ : Type*} {φ : MvPolynomial σ ℂ} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (t : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval (t • z) φ = t ^ d * MvPolynomial.eval z φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hdeg]
  ring

def bwpMat {p : ℕ} (z : Fin p × Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun i j => z (i, j)

def bwpId (p : ℕ) : Fin p × Fin p → ℂ := fun ij => if ij.1 = ij.2 then 1 else 0

theorem bwp_det_line_poly {p : ℕ} (z v : Fin p × Fin p → ℂ) :
    ∃ Λ : ℂ[X], ∀ t : ℂ, Λ.eval t = (bwpMat (z + t • v)).det := by
  refine ⟨(Matrix.of fun i j => Polynomial.C (z (i, j)) + Polynomial.C (v (i, j)) * Polynomial.X).det,
    fun t => ?_⟩
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, bwpMat, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem bwp_finite_det_line {p : ℕ} (z v : Fin p × Fin p → ℂ) (hz : (bwpMat z).det ≠ 0) :
    {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite := by
  obtain ⟨Λ, hΛ⟩ := bwp_det_line_poly z v
  have hΛ0 : Λ ≠ 0 := by
    intro h
    apply hz
    have h0 := hΛ 0
    rw [h, Polynomial.eval_zero] at h0
    simpa using h0.symm
  refine (bwp_finite_eval_eq_zero hΛ0).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [hΛ]
  exact ht

theorem bwp_finite_det_id_line {p : ℕ} (z : Fin p × Fin p → ℂ) :
    {s : ℂ | (bwpMat (z + s • bwpId p)).det = 0}.Finite := by
  have hne : (-bwpMat z).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  refine (bwp_finite_eval_eq_zero hne).subset fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  convert hs using 2
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply]
    ring
  · simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply, h]

theorem bwp_continuous_of_matrix {p : ℕ} :
    Continuous (fun y : Fin p → Fin p → ℂ => Matrix.of y) := by
  first
    | exact continuous_id
    | exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)

theorem bwp_exists_bound_unitary {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) :
    ∃ C : ℝ, ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ‖P U‖ ≤ C := by
  set S : Set (Fin p → Fin p → ℂ) := {y | Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1} with hS
  have hcl : IsClosed S :=
    isClosed_eq (bwp_continuous_of_matrix.matrix_conjTranspose.matrix_mul bwp_continuous_of_matrix)
      continuous_const
  have hbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun y hy => ?_⟩
    have hU : Matrix.of y ∈ Matrix.unitaryGroup (Fin p) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    first
      | exact entry_norm_bound_of_unitary hU i j
      | exact Matrix.UnitaryGroup.entry_norm_bound hU i j
      | exact Matrix.norm_entry_le_one_of_unitary hU i j
  have hK : IsCompact S := Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hsub : S ⊆ {y | (Matrix.of y).det ≠ 0} := fun y hy => by
    have h := congrArg Matrix.det (show Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1 from hy)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (DifferentiableOn.continuousOn hP |>.mono hsub)
  refine ⟨C, fun U hU => ?_⟩
  have hU' : U ∈ S := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  exact hC U hU'

theorem bwp_line_poly (hH : LemmaHStatement) (hO : OnePolyGrowthStatement) {p : ℕ} (a : Fin p → ℕ)
    (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) (hT : IsTriEquivariant a P)
    (z v : Fin p × Fin p → ℂ) (hB : {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite) :
    ∃ Q : ℂ[X], Q.natDegree ≤ ∑ i, a i ∧
      ∀ t, (bwpMat (z + t • v)).det ≠ 0 → P (bwpMat (z + t • v)) = Q.eval t := by
  classical
  obtain ⟨C, hC⟩ := bwp_exists_bound_unitary P hP
  set M : ℝ := ∑ i, ∑ j, (‖z (i, j)‖ + ‖v (i, j)‖) with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hMj : ∀ j, ∑ i, (‖z (i, j)‖ + ‖v (i, j)‖) ≤ M := fun j =>
    Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => ‖z (i, j')‖ + ‖v (i, j')‖)
      (fun j' _ => by positivity) (Finset.mem_univ j)
  have hbound : ∀ t ∉ {t : ℂ | (bwpMat (z + t • v)).det = 0},
      ‖P (bwpMat (z + t • v))‖ ≤ (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by
    intro t ht
    have hdet : (bwpMat (z + t • v)).det ≠ 0 := ht
    have hcol : ∀ j, colNormSq (bwpMat (z + t • v)) j ≤ (M * (1 + ‖t‖)) ^ 2 := by
      intro j
      have hz : ∑ i, ‖z (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (norm_nonneg _)) (hMj j)
      have hv : ∑ i, ‖v (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_left (norm_nonneg _)) (hMj j)
      set e : Fin p → ℝ := fun i => ‖bwpMat (z + t • v) i j‖ with he_def
      have he0 : ∀ i, 0 ≤ e i := fun i => norm_nonneg _
      have he : ∑ i, e i ≤ M * (1 + ‖t‖) := by
        calc ∑ i, e i ≤ ∑ i, (‖z (i, j)‖ + ‖t‖ * ‖v (i, j)‖) := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [he_def, bwpMat, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              exact (norm_add_le _ _).trans (by rw [norm_mul])
          _ = ∑ i, ‖z (i, j)‖ + ‖t‖ * ∑ i, ‖v (i, j)‖ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ M * (1 + ‖t‖) := by nlinarith [norm_nonneg t]
      have hsq : ∑ i, e i ^ 2 ≤ (∑ i, e i) ^ 2 := by
        calc ∑ i, e i ^ 2 = ∑ i, e i * e i := Finset.sum_congr rfl fun i _ => sq (e i)
          _ ≤ ∑ i, e i * ∑ j', e j' := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (fun j' _ => he0 j') (Finset.mem_univ i)) (he0 i)
          _ = (∑ i, e i) ^ 2 := by rw [← Finset.sum_mul, sq]
      calc colNormSq (bwpMat (z + t • v)) j = ∑ i, e i ^ 2 := rfl
        _ ≤ (∑ i, e i) ^ 2 := hsq
        _ ≤ (M * (1 + ‖t‖)) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => he0 i) he 2
    have hR : 0 ≤ M * (1 + ‖t‖) := mul_nonneg hM0 (by positivity)
    have h := hH Unit (fun _ => p) (fun _ => a) (fun x => P (x ())) C (M * (1 + ‖t‖))
      (by
        intro x s b hx hb htri
        cases s
        first
          | simp only [Function.update_self]
          | simp only [Function.update_same]
        exact hT (x ()) b (hx ()) hb htri)
      (fun k hk => hC (k ()) (hk ())) hR (fun _ => bwpMat (z + t • v)) (fun _ => hdet)
      (fun _ j => hcol j)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    calc ‖P (bwpMat (z + t • v))‖ ≤ C * (M * (1 + ‖t‖)) ^ ∑ i, a i := h
      _ = (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by rw [mul_pow]; ring
  have hdiff : DifferentiableOn ℂ (fun t => P (bwpMat (z + t • v)))
      {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ := by
    have hL : Differentiable ℂ (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)) := by
      rw [differentiable_pi]
      intro i
      rw [differentiable_pi]
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have hc : DifferentiableOn ℂ ((fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) ∘
        (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)))
        {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ :=
      DifferentiableOn.comp hP hL.differentiableOn (fun t ht => ht)
    exact hc
  obtain ⟨Q, hQdeg, hQ⟩ := hO (fun t => P (bwpMat (z + t • v))) _ (C * M ^ (∑ i, a i)) (∑ i, a i) hB
    hdiff hbound
  exact ⟨Q, hQdeg, fun t ht => hQ t ht⟩

end ReciprocityTheory.MultiplicativeHeights
end
end
