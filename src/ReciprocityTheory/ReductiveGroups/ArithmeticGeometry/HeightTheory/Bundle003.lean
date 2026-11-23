module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.Polynomial.Monic

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open MeasureTheory Module Submodule

theorem gtA_countable {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Countable (span ℤ (Set.range B)).toAddSubgroup := by
  have e : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      Set.range (fun c : Fin n → ℤ => ∑ i, c i • B i) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  have hc : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)).Countable := by
    rw [e]
    exact Set.countable_range _
  exact hc.to_subtype

theorem gtA_mink_pi_lt {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (h : |(Matrix.of B).det| < t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ < t := by
  haveI := gtA_countable B
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.ball (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_ball (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_ball 0 ht, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_lt_ofReal_iff (by positivity), mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_lt_mul_of_pos_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_mink_pi_le {n : ℕ} (hn : 0 < n) (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ}
    (ht : 0 < t) (h : |(Matrix.of B).det| ≤ t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ ≤ t := by
  haveI := gtA_countable B
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.closedBall (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_closedBall (0 : Fin n → ℝ) t) (isCompact_closedBall (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_closedBall 0 ht.le, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_le_mul_of_nonneg_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_norm_le_sqrt_mul (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hM : ∀ i, ‖x i‖ ≤ ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := fun i =>
    norm_le_pi_norm (EuclideanSpace.equiv (Fin n) ℝ x) i
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin n, ‖EuclideanSpace.equiv (Fin n) ℝ x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => by gcongr; exact hM i
    _ = Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem gtB_inner_eq (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, EuclideanSpace.equiv (Fin n) ℝ x k * EuclideanSpace.equiv (Fin n) ℝ y k := by
  first
    | simp [PiLp.inner_apply, mul_comm]
    | (rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct, mul_comm])

theorem gtB_nondeg (n : ℕ) : (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate := by
  show _ ∧ _
  constructor
  · intro x hx
    first
      | simpa using hx x
      | simpa [innerₗ_apply_apply] using hx x
  · intro y hy
    first
      | simpa using hy y
      | simpa [innerₗ_apply_apply] using hy y

theorem gtB_dual_short {n : ℕ} (hn : 0 < n) (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) ∧
      ‖y‖ ≤ n / lam := by
  set e := EuclideanSpace.equiv (Fin n) ℝ with he
  set B := b.map e.toLinearEquiv with hBdef
  have hB : ∀ j, B j = e (b j) := fun j => by simp [B]
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hdet : (lam / Real.sqrt n) ^ n ≤ |(Matrix.of B).det| := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_lt B (by positivity) hlt
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
    have hex : e (∑ i, c i • b i) = ∑ i, c i • B i := by simp [hB, map_sum, map_zsmul]
    have hx'0 : (∑ i, c i • b i) ≠ 0 := by intro h; apply hx0; rw [← hex, h, map_zero]
    have h1 := hmin _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hx'0
    have h2 := gtA_norm_le_sqrt_mul n (∑ i, c i • b i)
    rw [hex] at h2
    have : Real.sqrt n * ‖∑ i, c i • B i‖ < lam := by
      calc _ < Real.sqrt n * (lam / Real.sqrt n) := mul_lt_mul_of_pos_left hxn hsq
        _ = lam := by field_simp
    linarith
  set c := LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (gtB_nondeg n) b with hcdef
  have hc : ∀ i j, inner ℝ (c i) (b j) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left (gtB_nondeg n) b i j
    simpa using this
  set C := c.map e.toLinearEquiv with hCdef
  have hC : ∀ j, C j = e (c j) := fun j => by simp [C]
  have hCB : Matrix.of C * (Matrix.of B).transpose = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, hB, hC]
    rw [← gtB_inner_eq, hc]
    simp [eq_comm]
  have hdetCB : (Matrix.of C).det * (Matrix.of B).det = 1 := by
    rw [← Matrix.det_transpose (Matrix.of B), ← Matrix.det_mul, hCB, Matrix.det_one]
  have hdetC : |(Matrix.of C).det| ≤ (Real.sqrt n / lam) ^ n := by
    have hpos : 0 < (lam / Real.sqrt n) ^ n := by positivity
    have h1 : |(Matrix.of C).det| * |(Matrix.of B).det| = 1 := by rw [← abs_mul, hdetCB, abs_one]
    have h2 : |(Matrix.of C).det| = |(Matrix.of B).det|⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, show (Real.sqrt n / lam) ^ n = ((lam / Real.sqrt n) ^ n)⁻¹ by
      rw [← inv_pow, inv_div]]
    exact inv_anti₀ hpos hdet
  obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_le hn C (by positivity) hdetC
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
  have hex : e (∑ i, k i • c i) = ∑ i, k i • C i := by simp [hC, map_sum, map_zsmul]
  refine ⟨∑ i, k i • c i, ?_, ?_, ?_⟩
  · intro h; apply hx0; rw [← hex, h, map_zero]
  · intro j
    refine ⟨k j, ?_⟩
    rw [sum_inner]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]
    simp
  · have h2 := gtA_norm_le_sqrt_mul n (∑ i, k i • c i)
    rw [hex] at h2
    calc _ ≤ _ := h2
      _ ≤ Real.sqrt n * (Real.sqrt n / lam) := mul_le_mul_of_nonneg_left hxn hsq.le
      _ = n / lam := by
        rw [← mul_div_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule

theorem gtC_prim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) (y1 : E) (hy1 : y1 ≠ 0)
    (hint : ∀ j, ∃ m : ℤ, inner ℝ y1 (b j) = m) :
    ∃ y0 : E, ∃ xu ∈ span ℤ (Set.range b), y0 ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y0 (b j) = m) ∧
      ‖y0‖ ≤ ‖y1‖ ∧ inner ℝ y0 xu = 1 := by
  classical
  choose m hm using hint
  have hPI := IsPrincipalIdealRing.principal (Ideal.span (Set.range m))
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (Set.range m))
  have hgI : g ∈ Ideal.span (Set.range m) := by
    rw [hg]
    exact Submodule.mem_span_singleton_self g
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hgI
  simp only [smul_eq_mul] at hc
  have hdiv : ∀ j, ∃ a : ℤ, a * g = m j := by
    intro j
    have hj : m j ∈ Ideal.span (Set.range m) := Ideal.subset_span ⟨j, rfl⟩
    rw [hg] at hj
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hj
    exact ⟨a, by simpa using ha⟩
  choose a ha using hdiv
  have hne : ∃ j, m j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy1
    have h0 : ∀ x, inner ℝ y1 x = 0 := by
      intro x
      rw [← b.sum_repr x, inner_sum]
      simp [inner_smul_right, hm, hcon]
    exact inner_self_eq_zero.1 (h0 y1)
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne
    exact hj (by rw [← ha j, mul_zero])
  have hgR : (g : ℝ) ≠ 0 := Int.cast_ne_zero.2 hg0
  refine ⟨(g : ℝ)⁻¹ • y1, ∑ i, c i • b i,
    (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩,
    smul_ne_zero (inv_ne_zero hgR) hy1, fun j => ⟨a j, ?_⟩, ?_, ?_⟩
  · rw [real_inner_smul_left, hm, ← ha j]
    push_cast
    field_simp
  · rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |(g : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hg0
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)
  · rw [inner_sum]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_smul_left, hm]
    have h2 : ∑ i, (c i : ℝ) * ((g : ℝ)⁻¹ * (m i : ℝ)) = (g : ℝ)⁻¹ * ((∑ i, c i * m i : ℤ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h2, hc]
    exact inv_mul_cancel₀ hgR

theorem gtD_lat {m : ℕ} (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (y0 xu : EuclideanSpace ℝ (Fin (m + 1))) (hy0 : y0 ≠ 0) (hxu : xu ∈ span ℤ (Set.range b))
    (h1 : inner ℝ y0 xu = 1) (hint : ∀ j, ∃ k : ℤ, inner ℝ y0 (b j) = k) :
    ∃ bW : Basis (Fin m) ℝ (ℝ ∙ y0)ᗮ,
      (∀ x ∈ span ℤ (Set.range bW),
        ((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b)) ∧
      (∀ v ∈ span ℤ (Set.range b), ∃ p ∈ span ℤ (Set.range bW),
        (p : EuclideanSpace ℝ (Fin (m + 1))) = v - inner ℝ y0 v • xu) := by
  classical
  have hintL : ∀ v ∈ span ℤ (Set.range b), ∃ k : ℤ, inner ℝ y0 v = k := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv
    choose k hk using hint
    refine ⟨∑ i, c i * k i, ?_⟩
    rw [inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hk]
  have hPW : ∀ v : EuclideanSpace ℝ (Fin (m + 1)), v - inner ℝ y0 v • xu ∈ (ℝ ∙ y0)ᗮ := by
    intro v
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right, h1,
      mul_one, sub_self]
  have hPL : ∀ v ∈ span ℤ (Set.range b), v - inner ℝ y0 v • xu ∈ span ℤ (Set.range b) := by
    intro v hv
    obtain ⟨k, hk⟩ := hintL v hv
    rw [hk, Int.cast_smul_eq_zsmul]
    exact sub_mem hv (Submodule.smul_mem _ k hxu)
  let K : Submodule ℤ (ℝ ∙ y0)ᗮ :=
    (span ℤ (Set.range b)).comap (((ℝ ∙ y0)ᗮ).subtype.restrictScalars ℤ)
  have hKmem : ∀ x : (ℝ ∙ y0)ᗮ,
      x ∈ K ↔ (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b) := fun x => Iff.rfl
  have : DiscreteTopology K := by
    let f : K → span ℤ (Set.range b) := fun x =>
      ⟨((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))), (hKmem x).1 x.2⟩
    refine DiscreteTopology.of_continuous_injective (f := f)
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext hv)
  have : IsZLattice ℝ K := by
    refine ⟨eq_top_iff.2 fun w _ => ?_⟩
    have hw0 : inner ℝ y0 (w : EuclideanSpace ℝ (Fin (m + 1))) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 w.2
    have hw0' : ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j * inner ℝ y0 (b j) = 0 := by
      rw [← hw0]
      conv_rhs => rw [← b.sum_repr (w : EuclideanSpace ℝ (Fin (m + 1)))]
      rw [inner_sum]
      simp_rw [real_inner_smul_right]
    have hsum : w = ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j •
        (⟨b j - inner ℝ y0 (b j) • xu, hPW (b j)⟩ : (ℝ ∙ y0)ᗮ) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, smul_sub, Finset.sum_sub_distrib]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, hw0', zero_smul, sub_zero, b.sum_repr]
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact (hKmem _).2 (hPL (b j) (Submodule.subset_span ⟨j, rfl⟩))
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hrank : Module.finrank ℤ K = m := by
    rw [ZLattice.rank ℝ K, Submodule.finrank_orthogonal_span_singleton (n := m) hy0]
  let bK : Basis (Fin m) ℤ K := Module.finBasisOfFinrankEq ℤ K hrank
  refine ⟨bK.ofZLatticeBasis ℝ K, ?_, ?_⟩
  · intro x hx
    rw [Basis.ofZLatticeBasis_span] at hx
    exact (hKmem x).1 hx
  · intro v hv
    refine ⟨⟨v - inner ℝ y0 v • xu, hPW v⟩, ?_, rfl⟩
    rw [Basis.ofZLatticeBasis_span]
    exact (hKmem _).2 (hPL v hv)

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete

theorem span_eq_top_of_complete {O N : Type*} [CommRing O] [AddCommGroup N] [Module O N] (ϖ : O)
    [IsPrecomplete (Ideal.span {ϖ}) O]
    (hsep : ∀ x : N, (∀ k : ℕ, ∃ y : N, x = ϖ ^ k • y) → x = 0) {n : ℕ} (S : Fin n → N)
    (hS : ∀ x : N, ∃ c : Fin n → O, ∃ y : N, x = ∑ i, c i • S i + ϖ • y) :
    Submodule.span O (Set.range S) = ⊤ := by
  classical
  choose c y hcy using hS
  rw [eq_top_iff]
  intro x _
  let xs : ℕ → N := fun k => Nat.rec x (fun _ z => y z) k
  have hxs : ∀ k, xs (k + 1) = y (xs k) := fun k => rfl
  let a : ℕ → Fin n → O := fun k i => ∑ j ∈ Finset.range k, ϖ ^ j * c (xs j) i
  have hxa : ∀ k, x = ∑ i, a k i • S i + ϖ ^ k • xs k := by
    intro k
    induction k with
    | zero => simp [a, xs]
    | succ k ih =>
      have hk := hcy (xs k)
      calc x = ∑ i, a k i • S i + ϖ ^ k • xs k := ih
        _ = ∑ i, a k i • S i + ϖ ^ k • (∑ i, c (xs k) i • S i + ϖ • y (xs k)) := by rw [← hk]
        _ = ∑ i, a (k + 1) i • S i + ϖ ^ (k + 1) • xs (k + 1) := by
          rw [hxs]
          simp only [a, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
            smul_smul, pow_succ]
          abel

  have hmem : ∀ m k, m ≤ k → ∀ i, a k i - a m i ∈ Ideal.span {ϖ ^ m} := by
    intro m k hmk i
    have : a k i - a m i = ∑ j ∈ Finset.Ico m k, ϖ ^ j * c (xs j) i := by
      simp only [a]
      rw [← Finset.sum_range_add_sum_Ico _ hmk]
      ring
    rw [this]
    refine Ideal.sum_mem _ fun j hj => ?_
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow ϖ (Finset.mem_Ico.1 hj).1) _
  have hpow : ∀ m : ℕ, (Ideal.span {ϖ} ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
    intro m
    rw [Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ i, ∃ L : O, ∀ k, a k i - L ∈ Ideal.span {ϖ ^ k} := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun k => a k i) (fun {m k} hmk => by
      rw [SModEq.sub_mem, hpow]
      have := hmem m k hmk i
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
    exact ⟨L, fun k => by have := hL k; rwa [SModEq.sub_mem, hpow] at this⟩
  choose L hL using hlim
  have hx : x = ∑ i, L i • S i := by
    rw [← sub_eq_zero]
    refine hsep _ fun k => ?_
    have ht : ∀ i, ∃ t : O, a k i - L i = ϖ ^ k * t := fun i => Ideal.mem_span_singleton'.1 (hL i k) |>.imp
      fun t ht => by rw [← ht, mul_comm]
    choose t ht using ht
    refine ⟨∑ i, t i • S i + xs k, ?_⟩
    conv_lhs => rw [hxa k]
    have e : ∀ i, a k i • S i = L i • S i + ϖ ^ k • t i • S i := by
      intro i
      rw [smul_smul, ← ht i, sub_smul]
      abel
    simp only [e, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
    abel
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HNm

theorem wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  cases a with
  | top => simp at h
  | coe x =>
    cases b with
    | top => simp at h
    | coe y =>
      have h' : x + y = 0 := by exact_mod_cast h
      have hx : 0 ≤ x := by exact_mod_cast ha
      have hy : 0 ≤ y := by exact_mod_cast hb
      exact_mod_cast (show x = 0 by omega)

theorem nonneg_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (w : AddValuation L (WithTop ℤ)) (h0 : ∀ r : R, 0 ≤ w (algebraMap R L r)) {x : L}
    (hx : IsIntegral R x) : 0 ≤ w x := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
  have hm0 : m < 0 := by rw [← hm] at hneg; exact_mod_cast hneg
  obtain ⟨p, hpm, hp⟩ := hx
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  have hsum := eq_neg_of_add_eq_zero_left hp
  have hlow : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤
      w (∑ i ∈ Finset.range p.natDegree, algebraMap R L (p.coeff i) * x ^ i) := by
    apply w.map_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [w.map_mul, w.map_pow, ← hm]
    have ha := h0 (p.coeff i)
    have hle : ((p.natDegree : ℤ) - 1) * m ≤ (i : ℤ) * m :=
      mul_le_mul_of_nonpos_right (by omega) hm0.le
    calc ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤ (((i : ℤ) * m : ℤ) : WithTop ℤ) := by
          exact_mod_cast hle
      _ = i • (m : WithTop ℤ) := by rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      _ ≤ w (algebraMap R L (p.coeff i)) + i • (m : WithTop ℤ) := le_add_of_nonneg_left ha
  have hxn : w (x ^ p.natDegree) = (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [w.map_pow, ← hm, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have key : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤
      (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [← hxn, hsum, w.map_neg]; exact hlow
  have key' := WithTop.coe_le_coe.mp key
  nlinarith

end HNm

end ReciprocityTheory.ChartRestriction.G.T0
end
