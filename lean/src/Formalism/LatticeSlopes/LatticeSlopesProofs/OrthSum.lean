import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot

/-! # Slope bounds for orthogonal sums of lattices -/

section GramDetLe

open Module

noncomputable section

namespace Formalism.F

theorem normDet_le_pow_finrank {R F : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : R →ₗ[ℝ] F) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ y, ‖g y‖ ≤ K * ‖y‖) :
    g.normDet ≤ K ^ finrank ℝ R := by
  unfold LinearMap.normDet
  split_ifs with h
  swap
  · positivity
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩

  let φ : LinearMap.range g ≃ₗᵢ[ℝ] R := h.some.repr.trans (stdOrthonormalBasis ℝ R).repr.symm
  let T : R →ₗ[ℝ] R := φ.toLinearEquiv.toLinearMap ∘ₗ g.rangeRestrict
  have hmat : LinearMap.toMatrix (stdOrthonormalBasis ℝ R).toBasis h.some.toBasis g.rangeRestrict =
      LinearMap.toMatrix (stdOrthonormalBasis ℝ R).toBasis (stdOrthonormalBasis ℝ R).toBasis T := by
    ext i j
    simp [LinearMap.toMatrix_apply, T, φ]
  rw [hmat, LinearMap.det_toMatrix, Real.norm_eq_abs]
  have hT : ∀ y, ‖T y‖ = ‖g y‖ := by
    intro y
    simp [T]
  have hsub : T '' Metric.ball 0 1 ⊆ Metric.closedBall 0 K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff] at hy
    rw [mem_closedBall_zero_iff, hT]
    calc ‖g y‖ ≤ K * ‖y‖ := hg y
      _ ≤ K * 1 := by gcongr
      _ = K := mul_one K
  have hm := MeasureTheory.measure_mono (μ := (MeasureTheory.volume : MeasureTheory.Measure R)) hsub
  rw [MeasureTheory.Measure.addHaar_image_linearMap, MeasureTheory.Measure.addHaar_closedBall _ _ hK] at hm
  have hpos : 0 < MeasureTheory.volume (Metric.ball (0 : R) 1) := Metric.measure_ball_pos _ _ one_pos
  have hfin : MeasureTheory.volume (Metric.ball (0 : R) 1) ≠ ⊤ := MeasureTheory.measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin).1 hm
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

def linearCombinationMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

theorem linearCombinationMap_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) (c : EuclideanSpace ℝ ι) :
    linearCombinationMap v c = ∑ i, c i • v i := rfl

private theorem det_gram_eq_zero_of_linearCombination_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (c : EuclideanSpace ℝ ι) (hc : c ≠ 0)
    (h0 : linearCombinationMap v c = 0) : (Matrix.gram ℝ v).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => c i, ?_, ?_⟩
  · intro h
    apply hc
    ext i
    exact congrFun h i
  · ext i
    rw [linearCombinationMap_apply] at h0
    have h1 : inner ℝ (v i) (∑ j, c j • v j) = 0 := by rw [h0, inner_zero_right]
    rw [inner_sum] at h1
    simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, real_inner_smul_right, mul_comm] using h1

private theorem gram_linearCombinationMap_eq_toMatrix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (v : ι → E)
    (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ ι)) :
    Matrix.gram ℝ (fun k => linearCombinationMap v (b k)) =
      LinearMap.toMatrix b.toBasis b.toBasis
        (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ (linearCombinationMap v).rangeRestrict) := by
  ext k l
  rw [Matrix.gram_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, OrthonormalBasis.repr_apply_apply,
    LinearMap.adjoint_inner_right]
  rfl

theorem det_gram_eq_normDet_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) :
    (Matrix.gram ℝ v).det = (linearCombinationMap v).normDet ^ 2 := by
  have hv : v = fun i => linearCombinationMap v (EuclideanSpace.basisFun ι ℝ i) := by
    funext i
    rw [linearCombinationMap_apply]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, ite_smul]
  have h1 : (Matrix.gram ℝ v).det = LinearMap.det (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ
      (linearCombinationMap v).rangeRestrict) := by
    conv_lhs => rw [hv]
    rw [gram_linearCombinationMap_eq_toMatrix, LinearMap.det_toMatrix]
  unfold LinearMap.normDet
  split_ifs with h
  · have h2 : (Matrix.gram ℝ (fun k => linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))).det =
        LinearMap.det (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ
          (linearCombinationMap v).rangeRestrict) := by
      rw [gram_linearCombinationMap_eq_toMatrix, LinearMap.det_toMatrix]
    rw [h1, ← h2]
    have hG : Matrix.gram ℝ (fun k => linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k)) =
        (LinearMap.toMatrix (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)).toBasis h.some.toBasis
          (linearCombinationMap v).rangeRestrict).transpose *
        LinearMap.toMatrix (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)).toBasis h.some.toBasis
          (linearCombinationMap v).rangeRestrict := by
      ext k l
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis]
      have e1 : inner ℝ (linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))
          (linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) l)) =
          inner ℝ ((linearCombinationMap v).rangeRestrict (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))
            ((linearCombinationMap v).rangeRestrict (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) l)) := rfl
      rw [e1, ← h.some.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [real_inner_comm (h.some m) ((linearCombinationMap v).rangeRestrict _),
        ← OrthonormalBasis.repr_apply_apply, ← OrthonormalBasis.repr_apply_apply]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, Real.norm_eq_abs, sq_abs, sq]
  · rw [zero_pow two_ne_zero]
    have hni : ¬ Function.Injective (linearCombinationMap v) := by
      intro hinj
      exact h ⟨(stdOrthonormalBasis ℝ (LinearMap.range (linearCombinationMap v))).reindex
        (finCongr (LinearMap.finrank_range_of_inj hinj))⟩
    rw [← LinearMap.ker_eq_bot] at hni
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hni
    exact det_gram_eq_zero_of_linearCombination_eq_zero v c hc0 (LinearMap.mem_ker.1 hc)

theorem gram_det_le : GramDetLe := by
  intro E F _ _ _ _ ι _ _ v w C hC
  have hvw : ∀ c : EuclideanSpace ℝ ι,
      ‖linearCombinationMap w c‖ ≤ C * ‖linearCombinationMap v c‖ := by
    intro c
    simpa only [linearCombinationMap_apply] using hC (fun i => c i)
  by_cases hinj : Function.Injective (linearCombinationMap v)
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Matrix.det_isEmpty]
    have hC0 : 0 ≤ C := by
      by_contra hneg
      push_neg at hneg
      obtain ⟨i⟩ := hι
      have h1 := hvw (EuclideanSpace.single i 1)
      have h3 : ‖linearCombinationMap v (EuclideanSpace.single i 1)‖ ≤ 0 := by
        nlinarith [norm_nonneg (linearCombinationMap v (EuclideanSpace.single i 1)),
          norm_nonneg (linearCombinationMap w (EuclideanSpace.single i 1))]
      have h4 := hinj ((norm_le_zero_iff.1 h3).trans (map_zero _).symm)
      have h5 := congrArg (fun x : EuclideanSpace ℝ ι => x i) h4
      simp at h5
    let e := LinearEquiv.ofInjective (linearCombinationMap v) hinj
    let G : E →ₗ[ℝ] F := linearCombinationMap w ∘ₗ e.symm.toLinearMap ∘ₗ
      ((LinearMap.range (linearCombinationMap v)).orthogonalProjection :
        E →ₗ[ℝ] LinearMap.range (linearCombinationMap v))
    have hP : ∀ y : LinearMap.range (linearCombinationMap v),
        (LinearMap.range (linearCombinationMap v)).orthogonalProjection (y : E) = y := fun y =>
      Submodule.orthogonalProjection_mem_subspace_eq_self y
    have hGf : G ∘ₗ linearCombinationMap v = linearCombinationMap w := by
      ext c
      have : linearCombinationMap v c = (e c : E) := (LinearEquiv.ofInjective_apply _ c).symm
      simp only [G, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_toLinearMap]
      rw [this, hP, LinearEquiv.symm_apply_apply]
    have hb : ∀ y : LinearMap.range (linearCombinationMap v),
        ‖G.domRestrict (LinearMap.range (linearCombinationMap v)) y‖ ≤ C * ‖y‖ := by
      intro y
      have hy : linearCombinationMap v (e.symm y) = (y : E) := by
        rw [← LinearEquiv.ofInjective_apply (h := hinj) (linearCombinationMap v) (e.symm y)]
        exact congrArg Subtype.val (e.apply_symm_apply y)
      simp only [LinearMap.domRestrict_apply, G, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        LinearEquiv.coe_toLinearMap]
      rw [hP]
      calc ‖linearCombinationMap w (e.symm y)‖ ≤ C * ‖linearCombinationMap v (e.symm y)‖ := hvw _
        _ = C * ‖y‖ := by rw [hy]; rfl
    have hdom := normDet_le_pow_finrank (G.domRestrict (LinearMap.range (linearCombinationMap v))) C hC0 hb
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace] at hdom
    have hle : (linearCombinationMap w).normDet ≤
        C ^ Fintype.card ι * (linearCombinationMap v).normDet := by
      rw [← hGf, LinearMap.normDet_comp]
      exact mul_le_mul_of_nonneg_right hdom (LinearMap.normDet_nonneg _)
    rw [det_gram_eq_normDet_sq w, det_gram_eq_normDet_sq v]
    calc (linearCombinationMap w).normDet ^ 2
        ≤ (C ^ Fintype.card ι * (linearCombinationMap v).normDet) ^ 2 :=
          pow_le_pow_left₀ (LinearMap.normDet_nonneg _) hle 2
      _ = C ^ (2 * Fintype.card ι) * (linearCombinationMap v).normDet ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2]
  · rw [← LinearMap.ker_eq_bot] at hinj
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hinj
    have hw0 : linearCombinationMap w c = 0 := by
      have h1 := hvw c
      rw [LinearMap.mem_ker.1 hc, norm_zero, mul_zero] at h1
      exact norm_le_zero_iff.1 h1
    rw [det_gram_eq_zero_of_linearCombination_eq_zero w c hc0 hw0]
    exact mul_nonneg (by rw [pow_mul]; positivity) (Matrix.posSemidef_gram ℝ v).det_nonneg

end Formalism.F

end

end GramDetLe

section SlopeInequality

open Module Submodule

noncomputable section

namespace Formalism.F

universe u v

private theorem finrank_int_eq_finrank_real_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L₀ ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      invFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e) ?_ e.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  haveI : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  rw [← e.finrank_eq, ZLattice.rank ℝ L₀]

theorem linearIndependent_coe_basis'' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical
  have h1 : Submodule.span ℤ (Set.range (fun i => (b i : E))) = L := by
    have := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range (fun i => (b i : E))) =
      Submodule.span ℝ (L : Set E) := by
    have h2 := Submodule.span_span_of_tower ℤ ℝ (Set.range (fun i => (b i : E)))
    rw [h1] at h2
    exact h2.symm
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, ← finrank_int_eq_finrank_real_span L,
    Module.finrank_eq_card_basis b]

theorem det_gram_basis_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    0 < (Matrix.gram ℝ (fun i => (b i : E))).det :=
  (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis'' L b)).det_pos

theorem covol_pos_of_discrete {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    0 < covol L := by
  classical
  rw [covol, dif_pos (inferInstance : DiscreteTopology L)]
  exact Real.sqrt_pos.mpr (det_gram_basis_pos L _)

theorem norm_sum_smul_le_of_int {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → F)
    (C : ℝ) (h : ∀ n : ι → ℤ, ‖∑ i, (n i : ℝ) • w i‖ ≤ C * ‖∑ i, (n i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by

  have hq : ∀ q : ι → ℚ, ‖∑ i, (q i : ℝ) • w i‖ ≤ C * ‖∑ i, (q i : ℝ) • v i‖ := by
    intro q
    classical
    obtain ⟨m, hm, hz⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ z : ℤ, (q i : ℝ) * m = z := by
      refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), fun i => ?_⟩
      obtain ⟨k, hk⟩ : (q i).den ∣ ∏ j, (q j).den :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(q i).num * k, ?_⟩
      rw [hk]
      push_cast
      rw [← mul_assoc]
      congr 1
      exact_mod_cast Rat.mul_den_eq_num (q i)
    choose n hn using hz
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hw : ∑ i, (n i : ℝ) • w i = (m : ℝ) • ∑ i, (q i : ℝ) • w i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have hv : ∑ i, (n i : ℝ) • v i = (m : ℝ) • ∑ i, (q i : ℝ) • v i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have key := h n
    rw [hw, hv, norm_smul, norm_smul, Real.norm_of_nonneg hm'.le, mul_left_comm] at key
    exact le_of_mul_le_mul_left key hm'

  intro c
  have hd : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  refine hd.induction_on (p := fun c : ι → ℝ => ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖) c ?_ hq
  exact isClosed_le (by fun_prop) (by fun_prop)

theorem slopeInequality_of (h : SlopeLeMuMax.{v}) : SlopeInequality.{u, v} := by
  intro E F _ _ _ _ _ _ L M hL hM hne φ C hφ hC
  classical
  let g : L →ₗ[ℤ] F := M.subtype.comp φ
  have ginj : Function.Injective g := M.injective_subtype.comp hφ
  let N : Submodule ℤ F := LinearMap.range g
  have hNM : N ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact (φ x).2
  haveI : DiscreteTopology L := hL
  haveI : DiscreteTopology M := hM
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (continuous_inclusion hNM)
      (Submodule.inclusion_injective hNM)
  let e : L ≃ₗ[ℤ] N := LinearEquiv.ofInjective g ginj

  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφx : ((φ ⟨x, hxL⟩ : M) : F) ≠ 0 := by
    intro h0
    apply hx0
    have h1 : φ ⟨x, hxL⟩ = φ 0 := by
      rw [map_zero]
      exact Subtype.ext h0
    exact congrArg Subtype.val (hφ h1)
  have hNne : N ≠ ⊥ := by
    intro h0
    apply hφx
    have hmem : g ⟨x, hxL⟩ ∈ N := LinearMap.mem_range_self g _
    rw [h0, Submodule.mem_bot] at hmem
    exact hmem
  have hCpos : 0 < C := by
    have h1 : ‖((φ ⟨x, hxL⟩ : M) : F)‖ ≤ C * ‖x‖ := hC ⟨x, hxL⟩
    have h2 : 0 < ‖((φ ⟨x, hxL⟩ : M) : F)‖ := norm_pos_iff.mpr hφx
    have h3 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h3.le]
  have h1 : slope N ≤ muMax M := h F M N hM hNM hNne

  set r := Module.finrank ℤ L with hr_def
  have hrkL : rk L = r := rfl
  have hrkN : rk N = r := by
    show Module.finrank ℤ N = Module.finrank ℤ L
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hrpos : 0 < r := Module.finrank_pos

  let b := Module.finBasis ℤ L
  have hcL : covol L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det :=
    covol_eq_gram E L (Fin r) b
  have hcN : covol N = Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det :=
    covol_eq_gram F N (Fin r) (b.map e)
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • ((φ (b i) : M) : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : E)‖ := by
    intro n
    have h2 := hC (∑ i, n i • b i)
    simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simpa only [Int.cast_smul_eq_zsmul] using h2
  have hreal := norm_sum_smul_le_of_int (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hint
  have hdet := gram_det_le E F (Fin r) (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hreal
  have hle : covol N ≤ C ^ r * covol L := by
    rw [hcN, hcL]
    calc Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin r)) *
            (Matrix.gram ℝ (fun i => (b i : E))).det) := Real.sqrt_le_sqrt hdet
      _ = C ^ r * Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
        rw [Fintype.card_fin, show C ^ (2 * r) = (C ^ r) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hcLpos := covol_pos_of_discrete L
  have hcNpos := covol_pos_of_discrete N
  have hlog : Real.log (covol N) ≤ r * Real.log C + Real.log (covol L) := by
    have h2 := Real.log_le_log hcNpos hle
    rwa [Real.log_mul (by positivity) hcLpos.ne', Real.log_pow] at h2
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hs : slope L ≤ slope N + Real.log C := by
    unfold slope deg
    rw [hrkL, hrkN, div_add' _ _ _ hr.ne', div_le_div_iff_of_pos_right hr]
    nlinarith
  linarith

end Formalism.F

end

end SlopeInequality

section SlopesBdd

open Module Submodule

noncomputable section

namespace Formalism.F

universe u

private theorem finrank_int_eq_finrank_span_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (span ℝ (L : Set E)) := by

  let V := span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L' ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : L' => (⟨((x : V) : E), x.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ L')

theorem linearIndependent_coe_basis' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR, ← finrank_int_eq_finrank_span_real L,
    Module.finrank_eq_card_basis e]

theorem gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem slopesBdd_of (hG : GramDetLe.{u, 0, 0}) : SlopesBdd.{u} := by
  intro E _ _ _ L hL
  haveI := hL
  let e := Module.finBasis ℤ L
  have he : LinearIndependent ℝ (fun i => (e i : E)) := linearIndependent_coe_basis' L e

  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, WithLp.ofLp x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h0 := Fintype.linearIndependent_iff.mp he (fun i => WithLp.ofLp x i) hx
    have h1 : WithLp.ofLp x = 0 := funext h0
    simpa using congrArg (WithLp.toLp 2) h1
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := by
    intro j
    rw [hfj j]
    simp [S, w]
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := by
    intro c
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by
      simp only [map_sum, map_smul, hSw]
    rw [← h1]
    simpa [dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N))
    (fun j => (f j : E)) w K hcomp
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin] at hdet

  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h2 : ∑ j, c j • (f j : E) = 0 := by
      rw [← map_zero S, ← hc]
      simp only [map_sum, map_smul, hSw]
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis' N f) c h2
  have hwpos : 0 < (Matrix.gram ℝ w).det := (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det] at hwpos
  have hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det := by
    simp only [eq_intCast] at hwpos ⊢
    have : (0 : ℤ) < (M.transpose * M).det := by exact_mod_cast hwpos
    exact_mod_cast this
  have hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ) := by
    haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
    exact_mod_cast Module.finrank_pos
  set g := (Matrix.gram ℝ (fun j => (f j : E))).det with hg
  have hgK : 1 ≤ (K : ℝ) ^ (2 * Module.finrank ℤ N) * g := hd1.trans hdet
  have hgpos : 0 < g := by
    by_contra hneg
    push_neg at hneg
    have : (K : ℝ) ^ (2 * Module.finrank ℤ N) * g ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hlog : -(2 * (Module.finrank ℤ N : ℝ)) * Real.log K ≤ Real.log g := by
    have h1 : Real.log 1 ≤ Real.log ((K : ℝ) ^ (2 * Module.finrank ℤ N) * g) :=
      Real.log_le_log one_pos hgK
    rw [Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hcov : covol N = Real.sqrt g := by rw [covol, dif_pos hN]
  show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K
  rw [hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]
  nlinarith

end Formalism.F

end

end SlopesBdd

section SlopeLeMuMaxOf

namespace Formalism.F

universe u

theorem slopeLeMuMax_of (h : SlopesBdd.{u}) : SlopeLeMuMax.{u} := by
  intro E _ _ _ L N hL hNL hN
  exact le_csSup (h E L hL) (show slope N ∈ slopes L from ⟨N, hNL, hN, rfl⟩)

theorem muMaxMono_of (h : SlopesBdd.{u}) : MuMaxMono.{u} := by
  intro E _ _ _ L N hL hNL hN
  apply csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)
  rintro t ⟨M, hMN, hM, rfl⟩
  exact ⟨M, hMN.trans hNL, hM, rfl⟩

end Formalism.F

end SlopeLeMuMaxOf

section OrthSum

open Module Submodule

noncomputable section

namespace Formalism.F

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_span_range_and_covol {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E)
    (hu : LinearIndependent ℝ u) :
    DiscreteTopology (span ℤ (Set.range u)) ∧
      covol (span ℤ (Set.range u)) = Real.sqrt (Matrix.gram ℝ u).det := by
  have hd := discreteTopology_span_range_of_linearIndependent u hu
  refine ⟨hd, ?_⟩
  haveI := hd
  have hZ : LinearIndependent ℤ u := hu.restrict_scalars' ℤ
  rw [covol_eq_gram E (span ℤ (Set.range u)) ι (Basis.span hZ)]
  simp only [Basis.span_apply]

theorem discreteTopology_sup_and_covol_sup (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [DiscreteTopology L₂]
    (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0) :
    DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E) ∧ covol (L₁ ⊔ L₂) = covol L₁ * covol L₂ := by
  classical

  let b₁ := Module.finBasis ℤ L₁
  let b₂ := Module.finBasis ℤ L₂
  let v₁ : Fin (Module.finrank ℤ L₁) → E := fun i => (b₁ i : E)
  let v₂ : Fin (Module.finrank ℤ L₂) → E := fun i => (b₂ i : E)
  have hv₁ : LinearIndependent ℝ v₁ := linearIndependent_coe_basis''' L₁ b₁
  have hv₂ : LinearIndependent ℝ v₂ := linearIndependent_coe_basis''' L₂ b₂
  have horth : ∀ i j, inner ℝ (v₁ i) (v₂ j) = 0 := fun i j => h _ (b₁ i).2 _ (b₂ j).2
  have horth' : ∀ i j, inner ℝ (v₂ i) (v₁ j) = 0 := fun i j => by
    rw [real_inner_comm]; exact horth j i
  have hdisj : Disjoint (span ℝ (Set.range v₁)) (span ℝ (Set.range v₂)) := by
    apply Submodule.IsOrtho.disjoint
    rw [Submodule.isOrtho_span]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact horth i j
  have hli := hv₁.sum_type hv₂ hdisj
  have hs₁ : span ℤ (Set.range v₁) = L₁ := span_range_coe_basis' L₁ b₁
  have hs₂ : span ℤ (Set.range v₂) = L₂ := span_range_coe_basis' L₂ b₂
  have hspan : span ℤ (Set.range (Sum.elim v₁ v₂)) = L₁ ⊔ L₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hs₁, hs₂]
  obtain ⟨hd, hc⟩ := discreteTopology_span_range_and_covol _ hli
  rw [hspan] at hd hc
  refine ⟨hd, ?_⟩
  have hc₁ : covol L₁ = Real.sqrt (Matrix.gram ℝ v₁).det := covol_eq_gram E L₁ _ b₁
  have hc₂ : covol L₂ = Real.sqrt (Matrix.gram ℝ v₂).det := covol_eq_gram E L₂ _ b₂
  have hp₁ : 0 ≤ (Matrix.gram ℝ v₁).det := (det_gram_basis_pos L₁ b₁).le
  have hg : Matrix.gram ℝ (Sum.elim v₁ v₂) =
      Matrix.fromBlocks (Matrix.gram ℝ v₁) 0 0 (Matrix.gram ℝ v₂) := by
    ext (i | i) (j | j) <;> simp [Matrix.gram_apply, horth, horth']
  rw [hc, hc₁, hc₂, hg, Matrix.det_fromBlocks_zero₂₁, Real.sqrt_mul hp₁]

theorem degree_le_rank_mul_maxSlope (L N : Submodule ℤ E) (hL : DiscreteTopology L) (hNL : N ≤ L) :
    deg N ≤ rk N * muMax L := by
  haveI := hL
  by_cases hN : N = ⊥
  · subst hN
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · haveI : DiscreteTopology N := discreteTopology_of_le hNL
    have hs : slope N ≤ muMax L := slopeLeMuMax_of (slopesBdd_of gram_det_le) E L N hL hNL hN
    have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN)
    have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith

theorem degree_le_rank_mul_maxSlope_of_injective (Q M : Submodule ℤ E) (hQ : DiscreteTopology Q)
    (hM : DiscreteTopology M) (ψ : Q →ₗ[ℤ] M) (hinj : Function.Injective ψ)
    (hψ : ∀ x : Q, ‖((ψ x : M) : E)‖ ≤ ‖(x : E)‖) : deg Q ≤ rk Q * muMax M := by
  haveI := hQ
  by_cases hQ0 : Q = ⊥
  · subst hQ0
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · have hs := slopeInequality_of (slopeLeMuMax_of (slopesBdd_of gram_det_le)) E E Q M hQ hM hQ0
      ψ 1 hinj (fun x => by simpa using hψ x)
    rw [Real.log_one, add_zero] at hs
    have hk : 0 < rk Q := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQ0)
    have hk' : (0 : ℝ) < (rk Q : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith

set_option maxHeartbeats 800000 in

theorem slope_le_max_maxSlope (L₁ L₂ : Submodule ℤ E) (h1 : DiscreteTopology L₁)
    (h2 : DiscreteTopology L₂) (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0)
    (hd : DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E))
    (N : Submodule ℤ E) (hN : N ≤ L₁ ⊔ L₂) (hN0 : N ≠ ⊥) :
    slope N ≤ max (muMax L₁) (muMax L₂) := by
  haveI := h1
  haveI := h2
  haveI := hd
  haveI hNd : DiscreteTopology N := discreteTopology_of_le hN

  obtain ⟨P, hPdef⟩ : ∃ P : E →L[ℝ] E, P = (span ℝ (L₂ : Set E)).starProjection := ⟨_, rfl⟩
  have hortho : span ℝ (L₁ : Set E) ≤ (span ℝ (L₂ : Set E))ᗮ := by
    rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    intro x hx y hy
    exact h x hx y hy
  have hP0 : ∀ x ∈ span ℝ (L₁ : Set E), P x = 0 := fun x hx => by
    rw [hPdef, Submodule.starProjection_apply_eq_zero_iff]
    exact hortho hx
  have hP1 : ∀ x ∈ L₁, P x = 0 := fun x hx => hP0 x (subset_span hx)
  have hP2 : ∀ x ∈ L₂, P x = x := fun x hx => by
    rw [hPdef, Submodule.starProjection_eq_self_iff]
    exact subset_span hx
  have hP3 : ∀ x ∈ L₁ ⊔ L₂, P x ∈ L₂ ∧ x - P x ∈ L₁ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hP1 y hy, hP2 z hz, zero_add, add_sub_cancel_right]
    exact ⟨hz, hy⟩
  have hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := fun x => by
    rw [hPdef]; exact Submodule.norm_starProjection_apply_le _ x

  set K : Submodule ℤ E := N ⊓ L₁ with hK
  have hKspan : span ℝ (K : Set E) ≤ span ℝ (L₁ : Set E) :=
    Submodule.span_mono (fun x hx => hx.2)
  have hsat : IsSaturated N K := by
    refine ⟨inf_le_left, fun x hx hxs => ⟨hx, ?_⟩⟩
    have h0 : P x = 0 := hP0 x (hKspan hxs)
    have := (hP3 x (hN hx)).2
    rwa [h0, sub_zero] at this
  obtain ⟨hQd, hrk, hdeg⟩ := degree_quotient E N K hNd hsat
  set Q := quot N K with hQ

  have hPR : ∀ x ∈ N, P ((span ℝ (K : Set E))ᗮ.starProjection x) = P x := by
    intro x hx
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have hS : (span ℝ (K : Set E)).starProjection x ∈ span ℝ (L₁ : Set E) := by
      apply hKspan
      rw [Submodule.starProjection_apply]
      exact SetLike.coe_mem _
    rw [hP0 _ hS, sub_zero]
  have hQmem : ∀ y ∈ Q, P y ∈ L₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) ∈ L₂
    rw [hPR x hx]
    exact (hP3 x (hN hx)).1
  let ψ : Q →ₗ[ℤ] L₂ := LinearMap.codRestrict L₂
    ((P.toLinearMap.restrictScalars ℤ).comp Q.subtype) (fun y => hQmem y.1 y.2)
  have hψ : ∀ y : Q, ((ψ y : L₂) : E) = P y := fun y => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy0
    have hPy : P y = 0 := by
      rw [← hψ, hy0]; rfl
    obtain ⟨y, hyQ⟩ := y
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyQ
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) = 0 at hPy
    rw [hPR x hx] at hPy
    have hx1 : x ∈ L₁ := by
      have := (hP3 x (hN hx)).2
      rwa [hPy, sub_zero] at this
    have hxK : x ∈ span ℝ (K : Set E) := subset_span ⟨hx, hx1⟩
    apply Subtype.ext
    change (span ℝ (K : Set E))ᗮ.starProjection x = 0
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hxK, sub_self]
  have hnorm : ∀ y : Q, ‖((ψ y : L₂) : E)‖ ≤ ‖(y : E)‖ := fun y => by
    rw [hψ]; exact hPnorm _
  have hdK : deg K ≤ rk K * muMax L₁ := degree_le_rank_mul_maxSlope L₁ K h1 inf_le_right
  have hdQ : deg Q ≤ rk Q * muMax L₂ := degree_le_rank_mul_maxSlope_of_injective Q L₂ hQd h2 ψ hinj hnorm
  have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN0)
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) ≤ (rk K : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ (rk Q : ℝ) := Nat.cast_nonneg _
  have e1 : (rk K : ℝ) * muMax L₁ ≤ (rk K : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hK0
  have e2 : (rk Q : ℝ) * muMax L₂ ≤ (rk Q : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hQ0
  have hrk' : (rk N : ℝ) = (rk K : ℝ) + (rk Q : ℝ) := by exact_mod_cast hrk
  unfold slope
  rw [div_le_iff₀ hk', hdeg, hrk']
  linarith

end

theorem orthogonal_sum_slope : OrthSum := by
  intro E _ _ _ L₁ L₂ h1 h2 h
  haveI := h1
  haveI := h2
  obtain ⟨hd, hc⟩ := discreteTopology_sup_and_covol_sup L₁ L₂ h
  refine ⟨hd, ?_, ?_⟩
  · have p1 := covol_pos_of_discrete L₁
    have p2 := covol_pos_of_discrete L₂
    unfold deg
    rw [hc, Real.log_mul p1.ne' p2.ne']
    ring
  · intro hL1 hL2
    apply le_antisymm
    · show sSup (slopes (L₁ ⊔ L₂)) ≤ _
      refine csSup_le ⟨_, L₁, le_sup_left, hL1, rfl⟩ ?_
      rintro t ⟨N, hN, hN0, rfl⟩
      exact slope_le_max_maxSlope L₁ L₂ h1 h2 h hd N hN hN0
    · have hmono := muMaxMono_of (slopesBdd_of gram_det_le)
      exact max_le (hmono E (L₁ ⊔ L₂) L₁ hd le_sup_left hL1)
        (hmono E (L₁ ⊔ L₂) L₂ hd le_sup_right hL2)

end Formalism.F

end

end OrthSum
