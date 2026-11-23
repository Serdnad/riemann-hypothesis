module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem gauss_re (z : GaussianInt) : (z : ℂ).re = z.re := by rw [GaussianInt.toComplex_def₂]

theorem gauss_im (z : GaussianInt) : (z : ℂ).im = z.im := by rw [GaussianInt.toComplex_def₂]

theorem gauss_fin (R0 : ℝ) : {z : GaussianInt | ‖(z : ℂ)‖ ≤ R0}.Finite := by
  have hfin : (Set.Icc (-⌈R0⌉) ⌈R0⌉ ×ˢ Set.Icc (-⌈R0⌉) ⌈R0⌉ : Set (ℤ × ℤ)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hinj : Set.InjOn (fun z : GaussianInt => (z.re, z.im))
      ((fun z : GaussianInt => (z.re, z.im)) ⁻¹' (Set.Icc (-⌈R0⌉) ⌈R0⌉ ×ˢ Set.Icc (-⌈R0⌉) ⌈R0⌉)) := by
    intro z _ w _ h
    simp only [Prod.mk.injEq] at h
    exact Zsqrtd.ext_iff.mpr ⟨h.1, h.2⟩
  refine (Set.Finite.preimage hinj hfin).subset ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  have key : ∀ n : ℤ, |(n : ℝ)| ≤ R0 → -⌈R0⌉ ≤ n ∧ n ≤ ⌈R0⌉ := by
    intro n hn
    have h1 := abs_le.mp hn
    have h2 := Int.le_ceil R0
    constructor
    · have : ((-⌈R0⌉ : ℤ) : ℝ) ≤ n := by push_cast; linarith [h1.1]
      exact_mod_cast this
    · have : (n : ℝ) ≤ ((⌈R0⌉ : ℤ) : ℝ) := by linarith [h1.2]
      exact_mod_cast this
  have hre : |(z.re : ℝ)| ≤ R0 := by rw [← gauss_re]; exact (Complex.abs_re_le_norm _).trans hz
  have him : |(z.im : ℝ)| ≤ R0 := by rw [← gauss_im]; exact (Complex.abs_im_le_norm _).trans hz
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
  exact ⟨key _ hre, key _ him⟩

theorem fin_bdd (R0 : ℝ) : ∃ R : ℕ, ∀ F : Finset (SpecialLinearGroup (Fin N) GaussianInt),
    (∀ c ∈ F, ∀ c' ∈ F, ∀ i j,
      ‖((((c⁻¹ * c' : SpecialLinearGroup (Fin N) GaussianInt) : Matrix (Fin N) (Fin N) GaussianInt) i j :
        GaussianInt) : ℂ)‖ ≤ R0) → F.card ≤ R := by
  classical
  have h1 : (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      {z : GaussianInt | ‖(z : ℂ)‖ ≤ R0}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => gauss_fin R0
  refine ⟨h1.toFinset.card, fun F hF => ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp
  refine Finset.card_le_card_of_injOn
    (fun c : SpecialLinearGroup (Fin N) GaussianInt =>
      (((c0⁻¹ * c : SpecialLinearGroup (Fin N) GaussianInt) : Matrix (Fin N) (Fin N) GaussianInt) :
        Fin N → Fin N → GaussianInt)) ?_ ?_
  · intro c hc
    refine Finset.mem_coe.mpr (h1.mem_toFinset.mpr ?_)
    intro i _ j _
    exact hF c0 hc0 c hc i j
  · intro c _ c' _ h
    have h' : c0⁻¹ * c = c0⁻¹ * c' := Subtype.ext h
    exact mul_left_cancel h'

def umat (x : Fin N → Fin N → ℕ × ℕ) : Matrix (Fin N) (Fin N) GaussianInt :=
  fun i j => if i = j then 1 else if i < j then ⟨(x i j).1, (x i j).2⟩ else 0

theorem umat_upper (x : Fin N → Fin N → ℕ × ℕ) : (umat x).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  have h1 : i ≠ j := (ne_of_lt hij').symm
  have h2 : ¬ i < j := not_lt.mpr hij'.le
  simp [umat, h1, h2]

theorem umat_det (x : Fin N → Fin N → ℕ × ℕ) : (umat x).det = 1 := by
  rw [Matrix.det_of_upperTriangular (umat_upper x)]
  simp [umat]

def uel (x : Fin N → Fin N → ℕ × ℕ) : SpecialLinearGroup (Fin N) GaussianInt := ⟨umat x, umat_det x⟩

private theorem coe_uel_eq_umat (x : Fin N → Fin N → ℕ × ℕ) :
    ((uel x : SpecialLinearGroup (Fin N) GaussianInt) : Matrix (Fin N) (Fin N) GaussianInt) = umat x :=
  rfl

theorem count (s0 : Fin N → ℝ) : ∃ F : Finset (SpecialLinearGroup (Fin N) GaussianInt),
    (∀ c ∈ F, ((c : Matrix (Fin N) (Fin N) GaussianInt).map GaussianInt.toComplex).BlockTriangular id ∧
      ∀ i j, i ≤ j → ‖(((c : Matrix (Fin N) (Fin N) GaussianInt) i j : GaussianInt) : ℂ)‖ ≤
        2 * Real.exp (s0 i - s0 j)) ∧
    ENNReal.ofReal (Real.exp (2 * Phi s0)) ≤ F.card := by
  classical
  set K : Fin N → Fin N → ℕ := fun i j => ⌈Real.exp (s0 i - s0 j)⌉₊ with hK
  set S : Finset (Fin N → Fin N → ℕ × ℕ) := Fintype.piFinset fun i => Fintype.piFinset fun j =>
    if i < j then Finset.range (K i j) ×ˢ Finset.range (K i j) else {((0 : ℕ), (0 : ℕ))} with hS
  have hmem : ∀ x ∈ S, ∀ i j, x i j ∈
      (if i < j then Finset.range (K i j) ×ˢ Finset.range (K i j) else {((0 : ℕ), (0 : ℕ))}) := by
    intro x hx i j
    exact Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hx i) j
  have hsmall : ∀ i j (n : ℕ), n < K i j → (n : ℝ) ≤ Real.exp (s0 i - s0 j) := by
    intro i j n hn
    have h1 : (n : ℝ) + 1 ≤ (K i j : ℝ) := by exact_mod_cast hn
    have h2 : (K i j : ℝ) < Real.exp (s0 i - s0 j) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    linarith
  refine ⟨S.image uel, ?_, ?_⟩
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    rw [coe_uel_eq_umat]
    refine ⟨?_, ?_⟩
    · intro i j hij
      simp [Matrix.map_apply, umat_upper x hij]
    · intro i j hij
      rcases hij.lt_or_eq with h | rfl
      · have hx' := hmem x hx i j
        rw [if_pos h, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx'
        have e : umat x i j = ⟨((x i j).1 : ℤ), ((x i j).2 : ℤ)⟩ := by simp [umat, h.ne, h]
        rw [e]
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [gauss_re, gauss_im]
        have a1 := hsmall i j _ hx'.1
        have a2 := hsmall i j _ hx'.2
        show |((((x i j).1 : ℤ)) : ℝ)| + |(((x i j).2 : ℤ) : ℝ)| ≤ _
        rw [Int.cast_natCast, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (Nat.cast_nonneg _)]
        linarith
      · norm_num [umat]
  · rw [Finset.card_image_of_injOn]
    · rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      rw [hS]
      simp only [Fintype.card_piFinset, apply_ite Finset.card, Finset.card_product, Finset.card_range,
        Finset.card_singleton]
      push_cast
      unfold Phi
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le)
      intro i _
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le)
      intro j _
      split_ifs with h
      · rw [show 2 * (s0 i - s0 j) = (s0 i - s0 j) + (s0 i - s0 j) by ring, Real.exp_add]
        have hc := Nat.le_ceil (Real.exp (s0 i - s0 j))
        exact mul_le_mul hc hc (Real.exp_pos _).le (Nat.cast_nonneg _)
      · simp
    · intro x hx y hy hxy
      funext i j
      have hx' := hmem x hx i j
      have hy' := hmem y hy i j
      by_cases h : i < j
      · have e := congrArg
          (fun g : SpecialLinearGroup (Fin N) GaussianInt => (g : Matrix (Fin N) (Fin N) GaussianInt) i j) hxy
        simp only [coe_uel_eq_umat, umat, h.ne, h, if_false, if_true] at e
        have e1 := congrArg Zsqrtd.re e
        have e2 := congrArg Zsqrtd.im e
        simp only [Nat.cast_inj] at e1 e2
        exact Prod.ext e1 e2
      · rw [if_neg h, Finset.mem_singleton] at hx' hy'
        rw [hx', hy']

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem cone_step {T : ℝ} {s : Fin N → ℝ} (h : Cone T s) :
    ∀ d : ℕ, ∀ l q : Fin N, (q : ℕ) = l + d → s q ≤ s l + d * T := by
  intro d
  induction d with
  | zero =>
    intro l q hq
    have : q = l := Fin.ext (by simpa using hq)
    subst this
    simp
  | succ d ih =>
    intro l q hq
    have hlt : (l : ℕ) + d < N := by have := q.isLt; omega
    have h1 := ih l ⟨(l : ℕ) + d, hlt⟩ rfl
    have h2 := h ⟨(l : ℕ) + d, hlt⟩ q (by simp; omega)
    push_cast
    linarith

theorem cone_le {T : ℝ} {s : Fin N → ℝ} (h : Cone T s) {l q : Fin N} (hlq : l ≤ q) :
    s q - s l ≤ N * |T| := by
  have h1 := cone_step h ((q : ℕ) - l) l q (by have : (l : ℕ) ≤ q := hlq; omega)
  have h2 : (((q : ℕ) - l : ℕ) : ℝ) ≤ N := by
    have : (q : ℕ) - l ≤ N := by omega
    exact_mod_cast this
  have h3 : (((q : ℕ) - l : ℕ) : ℝ) * T ≤ (((q : ℕ) - l : ℕ) : ℝ) * |T| :=
    mul_le_mul_of_nonneg_left (le_abs_self T) (Nat.cast_nonneg _)
  have h4 : (((q : ℕ) - l : ℕ) : ℝ) * |T| ≤ N * |T| := mul_le_mul_of_nonneg_right h2 (abs_nonneg T)
  linarith

theorem env (M T : ℝ) : ∃ R1 : ℝ, ∀ (n p k : Matrix (Fin N) (Fin N) ℂ) (s0 s : Fin N → ℝ), Cone T s0 →
    (∀ i, |s i - s0 i| ≤ 1) → n.BlockTriangular id → (∀ i j, i ≤ j → ‖n i j‖ ≤ 2 * Real.exp (s0 i - s0 j)) →
    p.BlockTriangular id → (∀ i j, ‖p i j‖ ≤ M) → k ∈ unitaryGroup (Fin N) ℂ →
    ∀ i j, ‖(diagonal (fun i => ((Real.exp (-s0 i) : ℝ) : ℂ)) *
      (n * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k)) i j‖ ≤ R1 := by
  refine ⟨(N : ℝ) * N * (2 * |M| * Real.exp (1 + N * |T|)), ?_⟩
  intro n p k s0 s hc hs hnb hn hpb hp hk i j
  have key : ∀ l m : Fin N, ‖((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j)‖
      ≤ 2 * |M| * Real.exp (1 + N * |T|) := by
    intro l m
    by_cases hil : l < i
    · rw [hnb hil]; simp; positivity
    by_cases hlm : m < l
    · rw [hpb hlm]; simp; positivity
    push_neg at hil hlm
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have h1 := hn i l hil
    have h2 : ‖p l m‖ ≤ |M| := (hp l m).trans (le_abs_self M)
    have h3 : ‖k m j‖ ≤ 1 := entry_norm_bound_of_unitary hk m j
    have h4 := cone_le hc hlm
    have h5 := (abs_le.mp (hs m)).2
    have hexp : Real.exp (-s0 i) * Real.exp (s0 i - s0 l) * Real.exp (s m) = Real.exp (s m - s0 l) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-s0 i) * (‖n i l‖ * ‖p l m‖ * Real.exp (s m) * ‖k m j‖)
        ≤ Real.exp (-s0 i) * (2 * Real.exp (s0 i - s0 l) * |M| * Real.exp (s m) * 1) := by gcongr
      _ = 2 * |M| * (Real.exp (-s0 i) * Real.exp (s0 i - s0 l) * Real.exp (s m)) := by ring
      _ = 2 * |M| * Real.exp (s m - s0 l) := by rw [hexp]
      _ ≤ 2 * |M| * Real.exp (1 + N * |T|) := by gcongr; linarith
  have entry : (diagonal (fun i => ((Real.exp (-s0 i) : ℝ) : ℂ)) *
      (n * p * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k)) i j
      = ∑ m, ∑ l, ((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j) := by
    rw [diagonal_mul, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  rw [entry]
  calc ‖∑ m, ∑ l, ((Real.exp (-s0 i) : ℝ) : ℂ) * (n i l * p l m * ((Real.exp (s m) : ℝ) : ℂ) * k m j)‖
      ≤ ∑ m : Fin N, ∑ l : Fin N, (2 * |M| * Real.exp (1 + N * |T|)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => key l m))
    _ = (N : ℝ) * N * (2 * |M| * Real.exp (1 + N * |T|)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem cpt_box (R : ℝ) : IsCompact {A : Matrix (Fin N) (Fin N) ℂ | ∀ i j, ‖A i j‖ ≤ R} := by
  have : {A : Matrix (Fin N) (Fin N) ℂ | ∀ i j, ‖A i j‖ ≤ R} =
      Set.univ.pi (fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R) := by
    ext A
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem cpt_SL (R : ℝ) :
    IsCompact {A : SpecialLinearGroup (Fin N) ℂ | ∀ i j, ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R} :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage (cpt_box R)

theorem cpt_Z [Fintype ι] (R : ℝ) : IsCompact (Zb (ι := ι) (N := N) R) := by
  have : Zb (ι := ι) (N := N) R = Set.univ.pi (fun _ =>
      {A : SpecialLinearGroup (Fin N) ℂ | ∀ i j, ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R}) := by
    ext z; simp [Zb]
  rw [this]
  exact isCompact_univ_pi fun _ => cpt_SL R

theorem cont_val : Continuous fun A : SpecialLinearGroup (Fin N) ℂ => (A : Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous

theorem cpt_U : IsCompact {A : SpecialLinearGroup (Fin N) ℂ |
    (A : Matrix (Fin N) (Fin N) ℂ) ∈ unitaryGroup (Fin N) ℂ} := by
  refine (cpt_SL (N := N) 1).of_isClosed_subset ?_ ?_
  · have : {A : SpecialLinearGroup (Fin N) ℂ | (A : Matrix (Fin N) (Fin N) ℂ) ∈ unitaryGroup (Fin N) ℂ} =
        {A : SpecialLinearGroup (Fin N) ℂ | (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ)ᴴ = 1} := by
      ext A; simp [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rw [this]
    exact isClosed_eq (cont_val.matrix_mul cont_val.matrix_conjTranspose)
      continuous_const
  · intro A hA i j
    exact entry_norm_bound_of_unitary hA i j

theorem cpt_KS : IsCompact (KS (ι := ι) (N := N)) := by
  have : KS (ι := ι) (N := N) = Set.univ.pi (fun _ =>
      {A : SpecialLinearGroup (Fin N) ℂ | (A : Matrix (Fin N) (Fin N) ℂ) ∈ unitaryGroup (Fin N) ℂ}) := by
    ext z; simp [KS]
  rw [this]
  exact isCompact_univ_pi fun _ => cpt_U

theorem cont_mt (w : ι) (i j : Fin N) : Continuous fun p : G ι N => mt p w i j :=
  (continuous_apply j).comp ((continuous_apply i).comp (cont_val.comp (continuous_apply w)))

theorem cpt_Om [Fintype ι] (M : ℝ) : IsCompact (OmG (ι := ι) (N := N) M) := by
  refine (cpt_Z (ι := ι) (N := N) M).of_isClosed_subset ?_ ?_
  · have : OmG (ι := ι) (N := N) M =
        {p : G ι N | ∀ w i j, j < i → mt p w i j = 0} ∩ {p | ∀ w i j, ‖mt p w i j‖ ≤ M} ∩
          {p | ∀ w i, M⁻¹ ≤ ‖mt p w i i‖} ∩ {p | ∀ i, ∏ w, ‖mt p w i i‖ = 1} := by
      ext p
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨fun w i j hij => h1 w hij, h2⟩, h3⟩, h4⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨fun w i j hij => h1 w i j hij, h2, h3, h4⟩
    rw [this]
    simp only [Set.ofPred_forall]
    refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
    · exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (cont_mt w i j) continuous_const
    · exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (cont_mt w i j).norm continuous_const
    · exact isClosed_iInter fun w => isClosed_iInter fun i =>
        isClosed_le continuous_const (cont_mt w i i).norm
    · exact isClosed_iInter fun i =>
        isClosed_eq (continuous_finsetProd _ fun w _ => (cont_mt w i i).norm) continuous_const
  · intro p hp
    exact hp.2.1

theorem cont_dg : Continuous fun s : {s : Fin N → ℝ // ∑ i, s i = 0} => (dg s.1 s.2 : G ι N) := by
  refine continuous_pi fun w => Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
  exact Continuous.matrix_diagonal (continuous_pi fun i =>
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp ((continuous_apply i).comp continuous_subtype_val)))

theorem cpt_S (T : ℝ) (m : Fin N → ℤ) : IsCompact
    {s : {s : Fin N → ℝ // ∑ i, s i = 0} | Cone T s.1 ∧ ∀ i, (m i : ℝ) ≤ s.1 i ∧ s.1 i ≤ m i + 1} := by
  have hemb : Topology.IsClosedEmbedding (Subtype.val : {s : Fin N → ℝ // ∑ i, s i = 0} → (Fin N → ℝ)) :=
    (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const).isClosedEmbedding_subtypeVal
  have hbox : IsCompact {s : Fin N → ℝ | Cone T s ∧ ∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1} := by
    refine (isCompact_univ_pi fun i => isCompact_Icc (a := (m i : ℝ)) (b := m i + 1)).of_isClosed_subset ?_ ?_
    · have hc1 : IsClosed {s : Fin N → ℝ | Cone T s} := by
        have : {s : Fin N → ℝ | Cone T s} = ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : (j : ℕ) = i + 1),
            {s : Fin N → ℝ | s j ≤ s i + T} := by
          ext s; simp [Cone]
        rw [this]
        exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_le (continuous_apply j) ((continuous_apply i).add continuous_const)
      have hc2 : IsClosed {s : Fin N → ℝ | ∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1} := by
        have : {s : Fin N → ℝ | ∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1} = ⋂ i : Fin N,
            ({s : Fin N → ℝ | (m i : ℝ) ≤ s i} ∩ {s | s i ≤ m i + 1}) := by
          ext s; simp
        rw [this]
        exact isClosed_iInter fun i => (isClosed_le continuous_const (continuous_apply i)).inter
          (isClosed_le (continuous_apply i) continuous_const)
      exact hc1.inter hc2
    · intro s hs
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
      exact hs.2
  exact hemb.isCompact_preimage hbox

theorem cpt_X {P : Set (G ι N)} (hP : IsCompact P) (T : ℝ) (m : Fin N → ℤ) : IsCompact (Xb P T m) := by
  have himg : Xb P T m = (fun x : G ι N × {s : Fin N → ℝ // ∑ i, s i = 0} × G ι N =>
      x.1 * dg x.2.1.1 x.2.1.2 * x.2.2) ''
      (P ×ˢ {s : {s : Fin N → ℝ // ∑ i, s i = 0} | Cone T s.1 ∧ ∀ i, (m i : ℝ) ≤ s.1 i ∧ s.1 i ≤ m i + 1} ×ˢ
        KS) := by
    ext x
    constructor
    · rintro ⟨p, hp, s, hs, hc, hb, k, hk, rfl⟩
      exact ⟨(p, ⟨s, hs⟩, k), ⟨hp, ⟨hc, hb⟩, hk⟩, rfl⟩
    · rintro ⟨⟨p, ⟨s, hs⟩, k⟩, ⟨hp, ⟨hc, hb⟩, hk⟩, rfl⟩
      exact ⟨p, hp, s, hs, hc, hb, k, hk, rfl⟩
  rw [himg]
  refine (hP.prod ((cpt_S T m).prod cpt_KS)).image ?_
  exact (continuous_fst.mul (cont_dg.comp (continuous_fst.comp continuous_snd))).mul
    (continuous_snd.comp continuous_snd)

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
end
