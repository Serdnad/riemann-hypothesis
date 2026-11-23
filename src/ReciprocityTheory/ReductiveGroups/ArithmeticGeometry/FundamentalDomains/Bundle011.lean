module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds

open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

lemma cc_cc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma cc_two : cc (2 : E) = 2 := by
  unfold cc
  exact map_ofNat _ 2

lemma inner_iota_eq_trace (x y : E) :
    inner ℝ (iota E x) (iota E y) = (1 / 2 : ℝ) * (Algebra.trace ℚ E (x * cc y) : ℝ) := by
  rw [inner_iota, ← sum_re_eq_trace]
  apply Finset.sum_congr rfl
  intro w _
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj]


variable (E) in
noncomputable def ed : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate (K := ℚ) (L := E)) (integralBasis E)

lemma trace_ed (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (integralBasis E i * ed E j) = if i = j then 1 else 0 := by
  rw [← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_right _ (Algebra.traceForm_isSymm ℚ) _ i j


variable (E) in
noncomputable def bd (j : Free.ChooseBasisIndex ℤ (𝓞 E)) : VS E := iota E (2 * cc (ed E j))

lemma inner_bas_bd (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    inner ℝ (bas E i) (bd E j) = if i = j then 1 else 0 := by
  rw [bas_apply, bd, inner_iota_eq_trace, cc_mul, cc_cc, cc_two]
  have h2 : integralBasis E i * (2 * ed E j) = (2 : ℚ) • (integralBasis E i * ed E j) := by
    rw [Algebra.smul_def, map_ofNat]
    ring
  rw [h2, LinearMap.map_smul, trace_ed]
  split_ifs <;> norm_num

lemma trace_int (c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ) (γ : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((∑ j, c j • ed E j) * (γ : E)) = m := by
  obtain ⟨m, hm⟩ : ∃ m : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
      (γ : E) = ∑ i, m i • integralBasis E i := by
    refine ⟨(RingOfIntegers.basis E).repr γ, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr γ]
    simp [integralBasis_apply]
  have key : ∀ j i, Algebra.trace ℚ E ((c j • ed E j) * (m i • integralBasis E i)) =
      if i = j then ((c j * m i : ℤ) : ℚ) else 0 := by
    intro j i
    rw [smul_mul_smul_comm, map_zsmul, mul_comm (ed E j), trace_ed]
    split_ifs <;> simp
  refine ⟨∑ j, c j * m j, ?_⟩

  rw [hm, Finset.sum_mul_sum, map_sum]

  simp_rw [map_sum, key]
  simp [Finset.sum_ite_eq']

lemma norm_discr (β : E) (hβ : β ≠ 0)
    (hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * (γ : E)) = m) :
    1 ≤ |(Algebra.norm ℚ β : ℝ)| * dE E := by
  choose m hm using fun i j => hint (RingOfIntegers.basis E i * RingOfIntegers.basis E j)
  have hbB : ∀ i, integralBasis E i = ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [integralBasis_apply]
  have hP : Matrix.of (fun i j => ((m i j : ℤ) : ℚ)) =
      Algebra.traceMatrix ℚ (integralBasis E) * Algebra.leftMulMatrix (integralBasis E) β := by
    ext i j
    rw [Matrix.of_apply, ← hm i j, Matrix.mul_apply]
    have e : β * ((RingOfIntegers.basis E i * RingOfIntegers.basis E j : 𝓞 E) : E) =
        integralBasis E i * (β * integralBasis E j) := by
      rw [hbB, hbB]
      push_cast
      ring
    rw [e]
    conv_lhs => rw [← (integralBasis E).sum_repr (β * integralBasis E j)]

    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    ring
  have h1 : ((Matrix.of m).det : ℚ) = (Matrix.of (fun i j => ((m i j : ℤ) : ℚ))).det := by
    rw [show ((Matrix.of m).det : ℚ) = (Int.castRingHom ℚ) (Matrix.of m).det from rfl,
      RingHom.map_det]
    rfl
  have hdet : ((Matrix.of m).det : ℚ) = (NumberField.discr E : ℚ) * Algebra.norm ℚ β := by
    rw [h1, hP, Matrix.det_mul, NumberField.coe_discr, Algebra.discr_def,
      Algebra.norm_eq_matrix_det (integralBasis E)]
  have hN0 : Algebra.norm ℚ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
  have hD0 : (NumberField.discr E : ℚ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hZ : (Matrix.of m).det ≠ 0 := by
    intro h
    have h0 : ((Matrix.of m).det : ℚ) = 0 := by rw [h]; simp
    rw [hdet] at h0
    exact mul_ne_zero hD0 hN0 h0
  have hR : ((Matrix.of m).det : ℝ) =
      ((NumberField.discr E : ℤ) : ℝ) * ((Algebra.norm ℚ β : ℚ) : ℝ) := by
    have h2 := congrArg (Rat.cast : ℚ → ℝ) hdet
    simp only [Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2
  unfold dE
  rw [← abs_mul, mul_comm, ← hR]
  exact_mod_cast Int.one_le_abs hZ

lemma prod_norm (β : E) :
    ∏ w : CP E, ‖w.1.embedding β‖ ^ 2 = |(Algebra.norm ℚ β : ℝ)| := by
  rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm,
    ← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace E => IsTotallyComplex.isComplex w)).prod_comp]
  apply Finset.prod_congr rfl
  intro w _
  rw [InfinitePlace.norm_embedding_eq]
  change w.1 β ^ 2 = w.1 β ^ w.1.mult
  rw [InfinitePlace.mult_isComplex]

lemma dE_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)

lemma card_complexPlaces_pos : 0 < Fintype.card (CP E) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact Fintype.card_pos_iff.mpr ⟨⟨w, IsTotallyComplex.isComplex w⟩⟩

lemma norm_bd_ge (x : VS E) (hx : x ∈ span ℤ (Set.range (bd E))) (hx0 : x ≠ 0) :
    4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤ ‖x‖ ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  obtain ⟨β, hβdef⟩ : ∃ β : E, β = ∑ j, c j • ed E j := ⟨_, rfl⟩
  have hxβ : x = iota E (2 * cc β) := by
    rw [← hc, hβdef]

    simp only [bd, cc, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm]
  have hβ0 : β ≠ 0 := by
    rintro h
    apply hx0
    rw [hxβ, h, cc, map_zero, mul_zero, map_zero]
  have hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * γ) = m := by
    intro γ
    rw [hβdef]
    exact trace_int c γ
  have hN := norm_discr β hβ0 hint
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnorm : ‖x‖ ^ 2 = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
    rw [hxβ, norm_sq_iota, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [map_mul, norm_mul, cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj,
      map_ofNat, h2n]
    ring
  have hn : (0 : ℝ) < Fintype.card (CP E) := by exact_mod_cast card_complexPlaces_pos
  have hd : 0 < dE E := dE_pos
  have hNinv : (dE E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ hd]
    exact hN
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (CP E))
    (fun _ => 1 / (Fintype.card (CP E) : ℝ)) (fun w => ‖w.1.embedding β‖ ^ 2)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun _ _ => by positivity)
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), prod_norm, ← Finset.mul_sum] at hgm
  have h1 : dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤
      |(Algebra.norm ℚ β : ℝ)| ^ (1 / (Fintype.card (CP E) : ℝ)) := by
    rw [Real.rpow_neg hd.le, ← Real.inv_rpow hd.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hd.le) hNinv (by positivity)
  rw [hnorm]
  have h3 := mul_le_mul_of_nonneg_left (h1.trans hgm)
    (by positivity : (0 : ℝ) ≤ 4 * (Fintype.card (CP E) : ℝ))
  calc 4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ)))
      ≤ 4 * (Fintype.card (CP E) : ℝ) *
        (1 / (Fintype.card (CP E) : ℝ) * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2) := h3
    _ = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
      rw [← mul_assoc, mul_assoc 4, mul_one_div_cancel hn.ne', mul_one]

end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma sum_split (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by
  set g : ℕ → ℂ := fun i => if h : i < r then f ⟨i, h⟩ else 0 with hg
  have e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hg, dif_pos j.isLt]
  have e2 : ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range (X.p0 + (r - X.p0)), g i := by
    rw [Nat.add_sub_cancel' X.p0_le]
  rw [e1, e2, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha : (a : ℕ) < r := lt_of_lt_of_le a.isLt X.p0_le
    simp only [hg, dif_pos ha]
    rfl
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : X.p0 + (m : ℕ) < r := by have := m.isLt; have := X.p0_le; omega
    simp only [hg, dif_pos hm]

def nI (m : Fin (r - X.p0)) : Fin r := ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩

private lemma nI_val_eq_p0_add (m : Fin (r - X.p0)) : ((nI X m : Fin r) : ℕ) = X.p0 + m := rfl

lemma L_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) = if a = c then 1 else 0 := by
  have ha := a.isLt
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0) := by
    simp only [Fin.val_castLE]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : a = c
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (Fin.castLE_injective X.p0_le e))]

lemma L_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (nI X m) = 0 := by
  have ha := a.isLt
  have h1 : (Fin.castLE X.p0_le a : Fin r) ≠ nI X m := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((nI X m : Fin r) : ℕ) < X.p0) := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_neg h2, add_zero]

lemma L_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    X.lowBlock Z τ (nI X m) (Fin.castLE X.p0_le c) = Z τ m c := by
  have hc := c.isLt
  have h1 : nI X m ≠ (Fin.castLE X.p0_le c : Fin r) := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_pos h2, zero_add]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [nI_val_eq_p0_add])) (Fin.ext (by simp))

lemma L_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    X.lowBlock Z τ (nI X m) (nI X m') = if m = m' then 1 else 0 := by
  have h2 : ¬ (X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((nI X m' : Fin r) : ℕ) < X.p0) := by
    rw [nI_val_eq_p0_add, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : m = m'
  · subst h
    simp
  · have h1 : nI X m ≠ nI X m' := by
      intro e
      have h' := congrArg Fin.val e
      rw [nI_val_eq_p0_add, nI_val_eq_p0_add] at h'
      exact h (Fin.ext (by omega))
    rw [if_neg h, if_neg h1]

lemma sgn_p (a : Fin X.p0) : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn, a.isLt]

lemma sgn_n (m : Fin (r - X.p0)) : sgn X.p0 ((nI X m : Fin r) : ℕ) = -1 := by
  rw [nI_val_eq_p0_add]
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn]

def Gp (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (X.lowBlock Z τ)ᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
    (X.lowBlock Z τ).map (starRingEnd ℂ)

private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma gram_xZ {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := by
  have h := ho τ
  rw [gram_eq_upper_bounds] at h
  have hm : mat (X.xZ x Z) τ = mat x τ * X.lowBlock Z τ := rfl
  rw [gram_eq_upper_bounds, hm, Gp, ← h, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

lemma Gp_apply (Z : X.Coord) (τ : X.Ψ) (a c : Fin r) :
    Gp X Z τ a c = ∑ j, X.lowBlock Z τ j a * ((sgn X.p0 (j : ℕ) : ℝ) : ℂ) * conj (X.lowBlock Z τ j c) := by
  rw [Gp, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

private lemma sum_eq_sum_castLE_add_sum_nI (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) :=
  sum_split X f

lemma Gp_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    Gp X Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) =
      (if a = c then 1 else 0) - ∑ m, Z τ m a * conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_np X, sgn_p X, sgn_n X]
  by_cases hac : a = c
  · subst hac
    simp [sub_eq_add_neg]
  · simp [hac, Ne.symm hac, sub_eq_add_neg]

lemma Gp_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    Gp X Z τ (nI X m) (Fin.castLE X.p0_le c) = -conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

lemma Gp_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    Gp X Z τ (Fin.castLE X.p0_le a) (nI X m) = -Z τ m a := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

lemma Gp_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    Gp X Z τ (nI X m) (nI X m') = -(if m = m' then 1 else 0) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_nn X, sgn_p X, sgn_n X]
  by_cases h : m = m'
  · subst h
    simp
  · simp [h, Ne.symm h]

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frameBasisRadius (r p0 f : ℕ) (d laStar ρ : ℝ) : ℝ :=
  (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (laStar / Real.sqrt f)) ρ) ^ (2 * p0 + 1)

def frameRadius (w : ℝ) (r : ℕ) : ℝ := 1 / (10 * Real.sqrt (w * r))

def LamBasis {r : ℕ} (X : DataX E r) (La : ℝ) (x : Frame X.Ψ r) (lam : Fin r → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L') ∧ LinearIndependent E lam ∧
  (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
  (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
  (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
  ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) =
    Submodule.span ℂ (Set.range fun a : Fin X.p0 => Data.emb τ.1 (lam (Fin.castLE X.p0_le a)))

def LatticeBoundAtMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (z0 x0 : Frame X.Ψ r) (laStar ρ : ℝ),
    z0 ∈ X.dom → x0 ∈ X.dom → X.IsOrtho x0 → X.SameFlag z0 x0 → 0 < laStar → laStar ≤ 1 → 0 < ρ → ρ ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (lam : Fin r → Fin r → E) (Z : X.Coord), X.zN Z ≤ ρ / 3 ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar ρ) (X.xZ x0 Z) lam

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def CuspCoefficientBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ ν : X.Ψ → ℝ,
      DifferentiableOn ℂ (X.fj la (u 0) ν P) X.dom ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.fj la (u 0) ν P (rmul x b) = bchar la b * X.fj la (u 0) ν P x) ∧
      ∀ b ∈ X.LZ X.g, ∀ x ∈ X.dom, X.fj la (u 0) ν P (X.Zb u b x) = X.fj la (u 0) ν P x

def FlowCoefficientDecay : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (X.fz ![ξ, (X.NC : E) • x] X.g χ (X.fj la ξ ν P)) z ≤
        2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
          sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}

end

end ReciprocityTheory.ChartRestriction.G.FD
end
