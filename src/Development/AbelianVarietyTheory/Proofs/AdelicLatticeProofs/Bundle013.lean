module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Field
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.OrbitProper

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma tpow_mul' (n : ℕ) (y z : Matrix ι ι ℂ) : tpow n (y * z) = tpow n y * tpow n z := by
  classical
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

lemma tpow_one' (n : ℕ) : tpow n (1 : Matrix ι ι ℂ) = 1 := by
  ext a b
  simp only [tpow, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

variable {m : ℕ} (d : Fin m → ℕ)

omit [DecidableEq ι] in
lemma act_mul' (t : TIdx ι d → ℂ) (y z : Matrix ι ι ℂ) :
    act d t (y * z) = act d (act d t y) z := by
  funext k
  simp only [act, tpow_mul', ← Matrix.vecMul_vecMul]

lemma act_one' (t : TIdx ι d → ℂ) : act d t 1 = t := by
  funext k
  simp [act, tpow_one']

omit [DecidableEq ι] in
lemma continuous_act_right (t : TIdx ι d → ℂ) : Continuous (act d t) := by
  refine continuous_pi fun k => ?_
  simp only [act, Matrix.vecMul, dotProduct, tpow, Matrix.of_apply]
  fun_prop

omit [DecidableEq ι] in
lemma continuous_act_left (y : Matrix ι ι ℂ) : Continuous (fun t : TIdx ι d → ℂ => act d t y) := by
  refine continuous_pi fun k => ?_
  simp only [act, Matrix.vecMul, dotProduct, tpow, Matrix.of_apply]
  fun_prop

def box (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℝ) : Set (Matrix ι ι ℂ) :=
  {y | y.det = 1 ∧ ∀ i j, ‖y i j‖ ≤ N}

lemma isCompact_box (N : ℝ) : IsCompact (box ι N) := by
  have h1 : IsCompact (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) N) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h2 : IsClosed {y : Matrix ι ι ℂ | y.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  have h3 := IsCompact.inter_left (X := Matrix ι ι ℂ) h1 h2
  convert h3 using 1
  ext y
  exact ⟨fun h => ⟨h.1, fun i _ j _ => mem_closedBall_zero_iff.2 (h.2 i j)⟩,
    fun h => ⟨h.1, fun i j => mem_closedBall_zero_iff.1 (h.2 i trivial j trivial)⟩⟩

lemma box_mono {N M : ℝ} (h : N ≤ M) : box ι N ⊆ box ι M :=
  fun _ hy => ⟨hy.1, fun i j => (hy.2 i j).trans h⟩

lemma box_mul (N : ℝ) (g : Matrix ι ι ℂ) (hg : g.det = 1) : ∃ M : ℝ, ∀ a ∈ box ι N, a * g ∈ box ι M := by
  refine ⟨∑ j, ∑ k, |N| * ‖g k j‖, fun a ha => ⟨by rw [Matrix.det_mul, ha.1, hg, one_mul], fun i j => ?_⟩⟩
  calc ‖(a * g) i j‖ ≤ ∑ k, |N| * ‖g k j‖ := by
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ((ha.2 i k).trans (le_abs_self N)) (norm_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun j => ∑ k, |N| * ‖g k j‖)
        (fun j _ => Finset.sum_nonneg fun k _ => by positivity) (Finset.mem_univ j)

lemma det_adj {y : Matrix ι ι ℂ} (hy : y.det = 1) : y.adjugate.det = 1 := by
  rw [Matrix.det_adjugate, hy, one_pow]

lemma adj_mul {y : Matrix ι ι ℂ} (hy : y.det = 1) : y.adjugate * y = 1 := by
  rw [Matrix.adjugate_mul, hy, one_smul]

lemma mul_adj {y : Matrix ι ι ℂ} (hy : y.det = 1) : y * y.adjugate = 1 := by
  rw [Matrix.mul_adjugate, hy, one_smul]

lemma exists_interior (v : TIdx ι d → ℂ) (hX : IsClosed (orb d v)) :
    ∃ (n : ℝ) (O : Set (TIdx ι d → ℂ)) (y₀ : Matrix ι ι ℂ), IsOpen O ∧ y₀.det = 1 ∧ act d v y₀ ∈ O ∧
      ∀ w ∈ O, w ∈ orb d v → w ∈ act d v '' box ι n := by
  haveI : CompleteSpace (orb d v) := hX.completeSpace_coe
  haveI : Nonempty (orb d v) := ⟨⟨act d v 1, 1, Matrix.det_one, rfl⟩⟩
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed (X := orb d v)
    (f := fun n : ℕ => Subtype.val ⁻¹' (act d v '' box ι n))
    (fun n => ((isCompact_box (n : ℝ)).image (continuous_act_right d v)).isClosed.preimage
      continuous_subtype_val)
    (by
      refine Set.eq_univ_of_forall fun ⟨w, y, hy, hw⟩ => ?_
      obtain ⟨M, hM⟩ := box_mul (ι := ι) 1 y hy
      have h1 : (1 : Matrix ι ι ℂ) ∈ box ι 1 := ⟨Matrix.det_one, fun i j => by
        rw [Matrix.one_apply]; split_ifs <;> simp⟩
      have := hM 1 h1
      rw [one_mul] at this
      exact Set.mem_iUnion.2 ⟨⌈M⌉₊, y, box_mono (Nat.le_ceil M) this, hw.symm⟩)
  rw [mem_interior] at hx
  obtain ⟨t, hts, hto, hxt⟩ := hx
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hto
  obtain ⟨x, y₀, hy₀, rfl⟩ := x
  exact ⟨n, O, y₀, hO, hy₀, hxt, fun w hw hwX => hts (a := ⟨w, hwX⟩) hw⟩

lemma locally_box (v : TIdx ι d → ℂ) (hX : IsClosed (orb d v)) (w : TIdx ι d → ℂ) (hw : w ∈ orb d v) :
    ∃ O : Set (TIdx ι d → ℂ), IsOpen O ∧ w ∈ O ∧ ∃ N : ℝ, O ∩ orb d v ⊆ act d v '' box ι N := by
  obtain ⟨n, O, y₀, hO, hy₀, hmem, hsub⟩ := exists_interior d v hX
  obtain ⟨y, hy, rfl⟩ := hw
  obtain ⟨M, hM⟩ := box_mul (ι := ι) n (y₀.adjugate * y)
    (by rw [Matrix.det_mul, det_adj hy₀, hy, one_mul])
  refine ⟨(fun t => act d t (y.adjugate * y₀)) ⁻¹' O, hO.preimage (continuous_act_left d _), ?_, M, ?_⟩
  · show act d (act d v y) (y.adjugate * y₀) ∈ O
    rwa [← act_mul', ← mul_assoc, mul_adj hy, one_mul]
  · rintro w ⟨hwO, z, hz, rfl⟩
    obtain ⟨a, ha, hav⟩ := hsub _ hwO ⟨z * (y.adjugate * y₀),
      by rw [Matrix.det_mul, Matrix.det_mul, det_adj hy, hy₀, hz]; simp, (act_mul' d v _ _).symm⟩
    refine ⟨_, hM a ha, ?_⟩
    simp only at hav
    rw [act_mul', hav, ← act_mul', mul_assoc, ← mul_assoc y₀, mul_adj hy₀, one_mul, adj_mul hy, act_one']

lemma isCompact_nsq {κ : Type} [Fintype κ] (C : ℝ) : IsCompact {w : κ → ℂ | nsq w ≤ C} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine isClosed_le ?_ continuous_const
    unfold nsq
    fun_prop
  · refine (Metric.isBounded_closedBall (x := (0 : κ → ℂ)) (r := Real.sqrt C)).subset fun w hw => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    refine Real.le_sqrt_of_sq_le (le_trans ?_ hw)
    exact Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

end GlobalTheory.ClassFin.OrbitProper


open GlobalTheory.ClassFin.OrbitProper in
theorem GlobalTheory.ClassFin.orbit_proper_of_isClosed : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C' := by
  intro ι _ _ m d v hX C
  have hK : IsCompact (orb d v ∩ {w | nsq w ≤ C}) := (isCompact_nsq C).inter_left hX
  have key : ∃ N : ℝ, orb d v ∩ {w | nsq w ≤ C} ⊆ act d v '' box ι N := by
    refine hK.induction_on (p := fun s => ∃ N : ℝ, s ⊆ act d v '' box ι N) ⟨0, Set.empty_subset _⟩
      (fun s t hst ⟨N, hN⟩ => ⟨N, hst.trans hN⟩) ?_ ?_
    · rintro s t ⟨N, hN⟩ ⟨M, hM⟩
      exact ⟨max N M, Set.union_subset (hN.trans (Set.image_mono (box_mono (le_max_left _ _))))
        (hM.trans (Set.image_mono (box_mono (le_max_right _ _))))⟩
    · intro w hw
      obtain ⟨O, hO, hwO, N, hN⟩ := locally_box d v hX w hw.1
      refine ⟨O ∩ orb d v, ?_, N, hN⟩
      exact mem_nhdsWithin.2 ⟨O, hO, hwO, fun x hx => ⟨hx.1, hx.2.1⟩⟩
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun y hy hC => ?_⟩
  obtain ⟨a, ha, hav⟩ := hN (a := act d v y) ⟨⟨y, hy, rfl⟩, hC⟩
  refine ⟨a * y.adjugate, by rw [Matrix.det_mul, ha.1, det_adj hy, one_mul], ?_, ?_⟩
  · rw [act_mul', hav, ← act_mul', mul_adj hy, act_one']
  · rw [mul_assoc, adj_mul hy, mul_one]
    exact ha.2
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.LogCompress

theorem jensen_exp {ι : Type} [Fintype ι] (w d : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (h1 : ∑ j, w j = 1) :
    0 < ∑ j, w j * Real.exp (d j) ∧ ∑ j, w j * d j ≤ Real.log (∑ j, w j * Real.exp (d j)) ∧
      (∑ j, w j * d j = Real.log (∑ j, w j * Real.exp (d j)) →
        ∀ j, w j ≠ 0 → Real.exp (d j) = ∑ j, w j * Real.exp (d j)) := by
  set m := ∑ j, w j * Real.exp (d j) with hm
  have hpos : 0 < m := by
    obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset ι), w j ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
      ⟨j, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw j) hj.symm) (Real.exp_pos _)⟩
  have hexp : ∀ j, Real.exp (d j - Real.log m) = Real.exp (d j) / m := by
    intro j
    rw [Real.exp_sub, Real.exp_log hpos]
  have hnn : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1)) :=
    fun j _ => mul_nonneg (hw j) (sub_nonneg.2 (Real.add_one_le_exp _))
  have hsum : ∑ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
      = Real.log m - ∑ j, w j * d j := by
    have : ∀ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
        = w j * Real.exp (d j) / m - w j * d j + w j * (Real.log m - 1) := by
      intro j
      rw [hexp]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, h1, ← hm, div_self hpos.ne']
    ring
  refine ⟨hpos, ?_, ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · intro h j hj
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [hsum, h, sub_self]) j
      (Finset.mem_univ _)
    have h2 := (mul_eq_zero.1 h0).resolve_left hj
    have h3 : d j - Real.log m = 0 := by
      by_contra hne
      have := Real.add_one_lt_exp hne
      linarith
    have h4 : d j = Real.log m := by linarith
    rw [h4, Real.exp_log hpos]

theorem compress_diag {ι κ : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι κ ℂ) (f : ι → ℝ) (k : κ) :
    (Cᴴ * diagonal (fun i => (f i : ℂ)) * C) k k = ((∑ j, Complex.normSq (C j k) * f j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

theorem exists_diag {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (hB : B.IsHermitian) :
    ∃ (V : Matrix κ κ ℂ) (m : κ → ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ Vᴴ * B * V = diagonal m := by
  refine ⟨hB.eigenvectorUnitary, RCLike.ofReal ∘ hB.eigenvalues, ?_, ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2)
  · exact (Matrix.mem_unitaryGroup_iff'.1 hB.eigenvectorUnitary.2)
  · have := hB.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this

theorem trace_log_le_log_det : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (H A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ), IsLog H A → Qᴴ * Q = 1 → (Matrix.trace (Qᴴ * H * Q)).re ≤ Real.log (Qᴴ * A * Q).det.re ∧ ((Matrix.trace (Qᴴ * H * Q)).re = Real.log (Qᴴ * A * Q).det.re → ∃ N : Matrix κ κ ℂ, A * Q = Q * N) := by
  intro ι _ _ κ _ _ H A Q ⟨U, d, hU, hH, hA⟩ hQ
  have hAh : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose _ ?_
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  obtain ⟨V, m, hV, hV', hm⟩ := exists_diag _ (Matrix.isHermitian_conjTranspose_mul_mul Q hAh)
  set C : Matrix ι κ ℂ := Uᴴ * Q * V with hC
  have hCH : Cᴴ = Vᴴ * Qᴴ * U := by
    simp [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have key : ∀ D : Matrix ι ι ℂ, Cᴴ * D * C = Vᴴ * (Qᴴ * (U * D * Uᴴ) * Q) * V := by
    intro D
    rw [hCH, hC]
    simp only [Matrix.mul_assoc]
  have hw : ∀ k, ∑ j, Complex.normSq (C j k) = 1 := by
    intro k
    have h := compress_diag C (fun _ => 1) k
    have h1 : diagonal (fun _ : ι => ((1 : ℝ) : ℂ)) = 1 := by simp
    rw [key, h1, Matrix.mul_one, hU, Matrix.mul_one, hQ, Matrix.mul_one, hV'] at h
    simp only [Matrix.one_apply_eq, mul_one] at h
    exact_mod_cast h.symm
  have hmk : ∀ k, m k = ((∑ j, Complex.normSq (C j k) * Real.exp (d j) : ℝ) : ℂ) := by
    intro k
    rw [← compress_diag C (fun j => Real.exp (d j)) k, key, ← hA, hm, Matrix.diagonal_apply_eq]
  have hJ := fun k => jensen_exp (fun j => Complex.normSq (C j k)) d
    (fun j => Complex.normSq_nonneg _) (hw k)
  have hdet : (Qᴴ * A * Q).det.re = ∏ k, ∑ j, Complex.normSq (C j k) * Real.exp (d j) := by
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal] at h
    rw [h]
    simp only [hmk]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have htr : (Matrix.trace (Qᴴ * H * Q)).re = ∑ k, ∑ j, Complex.normSq (C j k) * d j := by
    have h : Matrix.trace (Cᴴ * diagonal (fun i => (d i : ℂ)) * C) = Matrix.trace (Qᴴ * H * Q) := by
      rw [key, ← hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [← h, Matrix.trace]
    simp only [Matrix.diag_apply, compress_diag]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hdet, htr, Real.log_prod (fun k _ => (hJ k).1.ne')]
  refine ⟨Finset.sum_le_sum fun k _ => (hJ k).2.1, fun h => ?_⟩
  have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => (hJ k).2.1).1 h
  have hDC : diagonal (fun i => (Real.exp (d i) : ℂ)) * C = C * diagonal m := by
    ext j k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : C j k = 0
    · simp [h0]
    · have := (hJ k).2.2 (heq k (Finset.mem_univ _)) j (by simpa using h0)
      rw [hmk, ← this, mul_comm]
  refine ⟨V * diagonal m * Vᴴ, ?_⟩
  have h1 : A * Q = U * (diagonal (fun i => (Real.exp (d i) : ℂ)) * C) * Vᴴ := by
    rw [hA, hC]
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [h1, hDC, hC]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

end GlobalTheory.LogCompress
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbHom

variable {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A)

theorem res_one' : res b (1 : Matrix κ κ A) = 1 := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst h
    simp [res, Matrix.one_apply]
  · simp [res, Matrix.one_apply, h]

omit [DecidableEq κ] in
theorem res_mul' (g h : Matrix κ κ A) : res b (g * h) = res b g * res b h := by
  ext ⟨i, x⟩ ⟨j, y⟩

  simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
  Fintype.sum_prod_type]

omit [Fintype κ] [DecidableEq κ] in
theorem res_inj' (g h : Matrix κ κ A) (e : res b g = res b h) : g = h := by
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext x y
  exact congrFun (congrFun e (i, x)) (j, y)

theorem emb_one' : emb b (1 : GL κ A) = 1 := by
  unfold emb
  rw [inv_one, Units.val_one, res_one', Matrix.det_one, ← Matrix.fromBlocks_one]
  congr 1

theorem emb_mul' (g h : GL κ A) : emb b (g * h) = emb b g * emb b h := by
  unfold emb
  rw [Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, res_mul', res_mul',
    Matrix.det_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  simp [Matrix.mul_apply, mul_comm]

theorem emb_det' (g : GL κ A) : (emb b g).det = 1 := by
  unfold emb
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply, ← Matrix.det_mul, ← res_mul',
    Units.mul_inv, res_one', Matrix.det_one]

theorem emb_adjugate' (g : GL κ A) : (emb b g).adjugate = emb b g⁻¹ := by
  have h1 : emb b g * emb b g⁻¹ = 1 := by rw [← emb_mul', mul_inv_cancel, emb_one']
  calc (emb b g).adjugate = (emb b g).adjugate * (emb b g * emb b g⁻¹) := by rw [h1, Matrix.mul_one]
    _ = emb b g⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, emb_det', one_smul, Matrix.one_mul]

theorem emb_injective' : Function.Injective (fun g : GL κ A => emb b g) := by
  intro g h e
  apply Units.ext
  apply res_inj' b
  exact (Matrix.fromBlocks_inj.mp e).1

theorem emb_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  intro R A β κ _ _ _ _ _ _ _ b
  exact ⟨emb_one' b, emb_mul' b, fun g => ⟨emb_det' b g, emb_adjugate' b g⟩, emb_injective' b⟩

end GlobalTheory.ClassFin.EmbHom
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isLog_kronecker {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ] [DecidableEq κ]
    {H A : Matrix ι ι ℂ} {H' A' : Matrix κ κ ℂ} (h : IsLog H A) (h' : IsLog H' A') :
    IsLog (H ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H') (A ⊗ₖ A') := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  obtain ⟨U', d', hU', rfl, rfl⟩ := h'
  refine ⟨U ⊗ₖ U', fun p => d p.1 + d' p.2, ?_, ?_, ?_⟩
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hU', one_kronecker_one]
  · have e : (diagonal (fun p : ι × κ => ((d p.1 + d' p.2 : ℝ) : ℂ))) =
        diagonal (fun i => (d i : ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) +
          (1 : Matrix ι ι ℂ) ⊗ₖ diagonal (fun i => (d' i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal,
        diagonal_add]
      congr 1
      funext p
      rw [Complex.ofReal_add, mul_one, one_mul]
    rw [e, conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      hU, hU']
  · have e : (diagonal (fun p : ι × κ => ((Real.exp (d p.1 + d' p.2) : ℝ) : ℂ))) =
        diagonal (fun i => (Real.exp (d i) : ℂ)) ⊗ₖ diagonal (fun i => (Real.exp (d' i) : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext p
      rw [Real.exp_add, Complex.ofReal_mul]
    rw [e, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

theorem harm_kronecker : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ) (g' : σ → Matrix κ κ ℂ), Harm g → Harm g' → Harm (fun s => g s ⊗ₖ g' s) := by
  intro ι _ _ κ _ _ σ _ g g' ⟨H, hH, hs⟩ ⟨H', hH', hs'⟩
  refine ⟨fun s => H s ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H' s, fun s => ?_, ?_⟩
  · have := isLog_kronecker (hH s) (hH' s)
    simpa only [conjTranspose_kronecker, ← mul_kronecker_mul] using this
  · ext ⟨i, k⟩ ⟨j, l⟩
    have h1 : ∑ s, H s i j = 0 := by
      have := congrFun (congrFun hs i) j
      simpa [Matrix.sum_apply] using this
    have h2 : ∑ s, H' s k l = 0 := by
      have := congrFun (congrFun hs' k) l
      simpa [Matrix.sum_apply] using this
    simp only [Matrix.sum_apply, Matrix.add_apply, kroneckerMap_apply, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, h1, h2, Matrix.zero_apply]
    simp

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem ideleChar_conj_eq_inv_of_trivial_on_base :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ χ : (AE F E)ˣ →* Circle, (∀ a : (AF F)ˣ, χ (idF F E a) = 1) → ∀ x y : (AE F E)ˣ, (y : AE F E) = cA σ x → χ y = (χ x)⁻¹ := by
  intro F E _ _ _ _ _ σ h χ hχ x y hy
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨n, hn⟩ := exists_unit_mul_conj_eq_algebraMap F E σ h1 h2 h3 h4 (AF F) x
  have hxy : x * y = idF F E n := by
    apply Units.ext
    rw [Units.val_mul, hy]
    exact hn
  have h5 : χ x * χ y = 1 := by rw [← map_mul, hxy, hχ]
  exact eq_inv_of_mul_eq_one_right h5

end GlobalTheory
end
