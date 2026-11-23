module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.TileIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
public import ReciprocityTheory.SemistableReduction.Bundle001
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle003
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

section

namespace GlobalTheory

open MeasureTheory

section

variable {V κ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Fintype κ]

theorem setIntegral_fundamentalDomain_add_right {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v) (a : V) :
    ∫ v in ZSpan.fundamentalDomain b, f (v + a) ∂μ = ∫ v in ZSpan.fundamentalDomain b, f v ∂μ := by
  have hA := ZSpan.isAddFundamentalDomain' b μ
  have hT : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup
      ((fun x => x - a) ⁻¹' ZSpan.fundamentalDomain b) μ := by
    refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
    · exact ((ZSpan.fundamentalDomain_measurableSet b).preimage
        (measurable_sub_const a)).nullMeasurableSet
    · obtain ⟨g, hg, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (x - a)
      refine ⟨⟨g, g.2⟩, ?_, ?_⟩
      · change (g : V) + x - a ∈ ZSpan.fundamentalDomain b
        rw [add_sub_assoc]; exact hg
      · rintro ⟨y, hy⟩ h
        change y + x - a ∈ ZSpan.fundamentalDomain b at h
        rw [add_sub_assoc] at h
        exact Subtype.ext (congrArg Subtype.val (hu ⟨y, hy⟩ h))
  have hper : ∀ (g : (Submodule.span ℤ (Set.range b)).toAddSubgroup) (x : V),
      f (g +ᵥ x) = f x := by
    intro g x
    change f ((g : V) + x) = f x
    rw [add_comm]
    exact hb g g.2 x
  rw [hA.setIntegral_eq hT hper]
  have e := (measurePreserving_sub_right μ a).setIntegral_preimage_emb
    (measurableEmbedding_subRight a) (fun y => f (y + a)) (ZSpan.fundamentalDomain b)
  simp only [sub_add_cancel] at e
  exact e.symm

theorem integrableOn_fundamentalDomain_of_continuous {E : Type} [NormedAddCommGroup E]
    (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hf : Continuous f) : IntegrableOn f (ZSpan.fundamentalDomain b) μ :=
  (hf.continuousOn.integrableOn_compact
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure).mono_set subset_closure

end

theorem average_fundamentalDomain_eq_real {V κ κ' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Fintype κ] [Fintype κ'] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (b : Module.Basis κ ℝ V) (b' : Module.Basis κ' ℝ V)
    (f : V → ℝ) (hf : Continuous f)
    (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v)
    (hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range b)) (a : V) :
    ⨍ v in ZSpan.fundamentalDomain b', f (v + a) ∂μ =
      ⨍ v in ZSpan.fundamentalDomain b, f v ∂μ := by
  have h1 : ⨍ v in ZSpan.fundamentalDomain b', f (v + a) ∂μ =
      ⨍ v in ZSpan.fundamentalDomain b', f v ∂μ := by
    rw [setAverage_eq, setAverage_eq,
      setIntegral_fundamentalDomain_add_right μ b' f (fun γ hγ => hb γ (hle hγ)) a]
  rw [h1, ← ZSpan.fundamentalDomain_reindex b' (b'.indexEquiv b)]
  refine ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.tile_average μ _ b ?_ f hf hb
  rwa [Module.Basis.range_reindex]

end GlobalTheory
end

section

namespace GlobalTheory

theorem card_exponents_sum_lt_sub (D T : ℕ) (hT : D < T) :
    Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D := by
  have e : {α : Fin D →₀ ℕ // α.degree ≤ T - D - 1} ≃ {α : Fin D → ℕ // ∑ i, α i < T - D} :=
    Finsupp.equivFunOnFinite.subtypeEquiv fun α => by
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.equivFunOnFinite_apply]
      omega
  rw [← Nat.card_congr e, ReciprocityTheory.MultiplicativeHeights.card_degree_le, show T - D - 1 + D = T - 1 by omega]

theorem le_of_add_mul_choose_pred_le (D T δ d ρ : ℕ) (hD : 2 ≤ D) (hT : 11 * D ^ 2 ≤ T)
    (hd : d ≤ δ * (T + 2 * D + 6).choose D) (hρ : ρ + δ * (T - 1).choose D ≤ d) :
    (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T := by
  have hT' : D * (2 * D + 7) ≤ T := by nlinarith
  have hTpos : (0 : ℝ) < T := by
    have : 0 < T := by nlinarith
    exact_mod_cast this
  have key := ReciprocityTheory.ChartRestriction.G.T0.sub_mul_choose_le_mul_choose T D hT' D le_rfl
  have hd' : (d : ℝ) ≤ δ * (((T + 2 * D + 6).choose D : ℕ) : ℝ) := by exact_mod_cast hd
  have hρ' : (ρ : ℝ) + δ * (((T - 1).choose D : ℕ) : ℝ) ≤ d := by exact_mod_cast hρ
  have hTD : (0 : ℝ) ≤ (T : ℝ) - D * (2 * D + 7) := by
    have : ((D : ℝ) * (2 * D + 7)) ≤ T := by exact_mod_cast hT'
    linarith
  have hδ : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have s1 := mul_le_mul_of_nonneg_left key hδ
  have s2 := mul_le_mul_of_nonneg_left hd' hTD
  have s3 := mul_le_mul_of_nonneg_left hρ' hTpos.le
  have s4 : (D : ℝ) * (2 * D + 7) * d ≤ 22 * (D : ℝ) ^ 2 * d :=
    mul_le_mul_of_nonneg_right (by nlinarith) hd0
  rw [le_div_iff₀ hTpos]
  nlinarith

theorem card_exponents_and_choose_ratio_bounds : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  intro D T
  refine ⟨fun _ h => card_exponents_sum_lt_sub D T h, fun δ d ρ hD hT hd =>
    ⟨le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd, fun h => ?_⟩⟩
  refine le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd (le_trans ?_ h)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.choose_le_choose D (by omega))) _

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem minkowski_det_bound_gram_of_det_ne_zero (m : ℕ) (hm : 0 < m) (B : Matrix (Fin m) (Fin m) ℝ) (hB : B.det ≠ 0)
    (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ (B * Bᵀ) *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * (B * Bᵀ).det := by
  classical
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (Ne.isUnit hB)
  have hli : LinearIndependent ℝ B.row := Matrix.linearIndependent_rows_iff_isUnit.2 hu
  let b : Module.Basis (Fin m) ℝ (Fin m → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (b : Fin m → Fin m → ℝ) = B.row := coe_basisOfPiSpaceOfLinearIndependent hli
  have hpos : 0 < |B.det| := abs_pos.2 hB
  set t : ℝ := |B.det| ^ ((m : ℝ)⁻¹) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hpos _
  have htm : t ^ m = |B.det| := Real.rpow_inv_natCast_pow hpos.le hm.ne'
  obtain ⟨x, hx, hx0, hxt⟩ := ReciprocityTheory.ChartRestriction.G.T0.gtA_mink_pi_le hm b ht0 (by
    rw [htm, hb]; exact le_of_eq rfl)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hx0
  have hx' : ∑ i, c i • b i = (fun i => (c i : ℝ)) ᵥ* B := by
    ext j
    simp [hb, Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [hx'] at hxt
  have h1 := h c hc
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at h1
  set y := (fun i => (c i : ℝ)) ᵥ* B
  have h2 : y ⬝ᵥ y ≤ m * t ^ 2 := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin m)), y i * y i ≤ t ^ 2 := by
      intro i _
      have h3 : |y i| ≤ t := (norm_le_pi_norm y i).trans hxt
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have h4 := Finset.sum_le_sum this
    simpa [dotProduct] using h4
  calc a ^ m ≤ (m * t ^ 2) ^ m := pow_le_pow_left₀ ha (h1.trans h2) m
    _ = (m : ℝ) ^ m * (B * Bᵀ).det := by
      rw [mul_pow, ← pow_mul, mul_comm 2 m, pow_mul, htm, sq_abs, det_mul, det_transpose, sq]

theorem minkowski_det_bound_posDef (m : ℕ) (hm : 0 < m) (G : Matrix (Fin m) (Fin m) ℝ)
    (hG : G.PosDef) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) :
    a ^ m ≤ (m : ℝ) ^ m * G.det := by
  open MatrixOrder in
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hG.posSemidef.nonneg
  have hC' : G = Cᵀ * Cᵀᵀ := by
    rw [hC, transpose_transpose, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hd := hG.det_pos
  have hB : (Cᵀ).det ≠ 0 := by
    intro h0
    rw [hC', det_mul, h0, zero_mul] at hd
    exact lt_irrefl _ hd
  rw [hC'] at h ⊢
  exact minkowski_det_bound_gram_of_det_ne_zero m hm _ hB a ha h

theorem minkowski_det_bound_posSemidef :
    ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → ∀ a : ℝ, 0 ≤ a →
      (∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) →
      a ^ m ≤ (m : ℝ) ^ m * G.det := by
  intro m G hG a ha h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have key : ∀ ε : ℝ, 0 < ε →
      a ^ m ≤ (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det := by
    intro ε hε
    refine minkowski_det_bound_posDef m hm _
      (Matrix.PosDef.posSemidef_add hG (Matrix.PosDef.one.smul hε)) a ha ?_
    intro z hz
    refine (h z hz).trans ?_
    rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul]
    have : 0 ≤ (fun i => (z i : ℝ)) ⬝ᵥ (fun i => (z i : ℝ)) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have := mul_nonneg hε.le this
    simpa using this
  have hc : Continuous fun ε : ℝ =>
      (m : ℝ) ^ m * (G + ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det :=
    continuous_const.mul (Continuous.matrix_det (by fun_prop))
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  simpa using this

end GlobalTheory
end

section

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace DualFamily

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.herm_one_eq {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = ∑ a, x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp [Matrix.one_apply]

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.herm_one_symm {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x) := by
  rw [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.DualFamily.herm_one_eq]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.isIntegral_cc {a : E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact ha.map (RingHom.toIntAlgHom (IsCMField.complexConj E).toRingEquiv.toRingHom)


open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.exists_herm_eq {n : ℕ} (f : (Fin n → E) →ₗ[E] E) :
    ∃ w : Fin n → E, ∀ u, f u = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u w := by
  refine ⟨fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (f fun b => if a = b then 1 else 0), fun u => ?_⟩
  rw [f.pi_apply_eq_sum_univ u, _root_.GlobalTheory.DualFamily.herm_one_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  rw [IsCMField.complexConj_apply_apply, smul_eq_mul]


open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.eq_zero_of_line {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (w : Fin n → E) (hw : ∀ c : E, c • w ∈ Λ) : w = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have htop : Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) j) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ⟨(x / w j) • w, hw _, ?_⟩
    simp [div_mul_cancel₀ _ hj]
  have : Module.Finite (𝓞 E) E := ⟨by rw [← htop]; exact hfg.map _⟩
  have := Algebra.IsIntegral.of_finite (𝓞 E) E
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.span_eq_top {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.DualFamily.exists_herm_eq f
  have hline : ∀ c : E, c • w ∈ Λ := fun c => hdual _ fun y hy => by
    have hfy : f y = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hy))
    have hsmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (c • w) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w y := by
      simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        mul_assoc]
    rw [hsmul, _root_.GlobalTheory.DualFamily.herm_one_symm w y, ← hw, hfy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    rw [map_zero, mul_zero]
    exact isIntegral_zero
  have hw0 := _root_.GlobalTheory.DualFamily.eq_zero_of_line Λ hfg w hline
  exact hf0 (LinearMap.ext fun u => by simp [hw u, hw0, _root_.GlobalTheory.DualFamily.herm_one_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc])

end DualFamily

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in
private lemma exists_linearForm_extend_of_span_eq_univ {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (g : Λ →ₗ[𝓞 E] 𝓞 E) :
    ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y : Λ, φ y = g y := by
  obtain ⟨t, htΛ, hts, hli⟩ := exists_linearIndependent E (Λ : Set (Fin n → E))
  let b : Module.Basis t E (Fin n → E) :=
    Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hts, hspan]))
  have hb : ∀ i, b i ∈ Λ := fun i => by rw [Module.Basis.mk_apply]; exact htΛ i.2
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  refine ⟨b.constr E fun i => ((g ⟨b i, hb i⟩ : 𝓞 E) : E), fun y => ?_⟩
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ (b.repr y)
  have hd' : ∀ i, ∃ x : 𝓞 E, algebraMap (𝓞 E) E x = (d : 𝓞 E) • b.repr y i :=
    fun i => hd i (Finset.mem_univ _)
  choose a ha using hd'
  have hdy : (d : 𝓞 E) • y = ∑ i, a i • (⟨b i, hb i⟩ : Λ) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_sum]
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul E (a i), ha i, smul_assoc]
  have hg := congrArg (fun z => ((g z : 𝓞 E) : E)) hdy

  simp only [map_smul, map_sum, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul] at hg
  simp only [RingOfIntegers.coe_eq_algebraMap]
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  apply mul_left_cancel₀ hd0
  rw [hg]
  conv_lhs => rw [← b.sum_repr (y : Fin n → E)]

  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, ha i, smul_eq_mul, Algebra.smul_def]
  ring

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.exists_dual_family {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ ∃ (m : ℕ) (v w : Fin m → Fin n → E),
      (∀ i, v i ∈ Λ) ∧ (∀ i, w i ∈ Λ) ∧ ∀ u : Fin n → E, u = ∑ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u (w i) • v i := by
  have hspan := _root_.GlobalTheory.DualFamily.span_eq_top Λ hfg hdual
  refine ⟨hspan, ?_⟩
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have := Module.finitePresentation_of_finite (𝓞 E) Λ
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hext : ∀ j : Fin m, ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y (hy : y ∈ Λ), φ y = σ ⟨y, hy⟩ j :=
    fun j => (exists_linearForm_extend_of_span_eq_univ Λ hspan ((LinearMap.proj j).comp σ)).imp
      fun φ h y hy => h ⟨y, hy⟩
  choose φ hφ using hext
  choose w hw using fun j => _root_.GlobalTheory.DualFamily.exists_herm_eq (φ j)
  let v : Fin m → Fin n → E := fun j => (π fun k => if j = k then 1 else 0 : Λ)
  refine ⟨m, v, w, fun j => (π _).2, fun j => hdual _ fun y hy => ?_, fun u => ?_⟩
  · rw [_root_.GlobalTheory.DualFamily.herm_one_symm, ← hw, hφ j y hy]
    exact _root_.GlobalTheory.DualFamily.isIntegral_cc (RingOfIntegers.isIntegral_coe _)
  · have hL : (∑ j, (φ j).smulRight (v j)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun y hy => ?_
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have hy' : y = ((π (σ ⟨y, hy⟩) : Λ) : Fin n → E) := by
        rw [← LinearMap.comp_apply, hσ]
        rfl
      conv_rhs => rw [hy', π.pi_apply_eq_sum_univ]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hφ j y hy, RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    have hu := congrArg (fun L : (Fin n → E) →ₗ[E] (Fin n → E) => L u) hL
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply, hw] at hu
    exact hu.symm

end GlobalTheory
end
