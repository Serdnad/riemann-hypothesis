module

public import ReciprocityTheory.SemistableReduction.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
public import ReciprocityTheory.SemistableReduction.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import ReciprocityTheory.SemistableReduction.Bundle002
public import ReciprocityTheory.SemistableReduction.Bundle005
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory

def scaledTorusMean {ι : Type*} [Fintype ι] (r : ι → ℂ) (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖ ∂(torusProb ι)

theorem scaledTorusMean_one {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) :
    scaledTorusMean (fun _ => 1) f = torusMean f := by
  unfold scaledTorusMean torusMean
  simp only [one_mul]

theorem eval_update_eq_eval_aeval {ι : Type*} [DecidableEq ι] (w : ι → ℂ) (i : ι) (z : ℂ)
    (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (Function.update w i z) f =
      (MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (w j)) f).eval z := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  rename_i p j hp
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X, Polynomial.eval_mul, hp]
  congr 1
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Function.update_of_ne h]

theorem eval_bind₁_scale {ι : Type*} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
    ← MvPolynomial.eval_assoc]
  refine congrArg (fun v => MvPolynomial.eval v f) (funext fun j => ?_)
  simp only [Function.comp_apply, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

private theorem bind1_C_mul_X_ne_zero_of_ne_zero {ι : Type} (r : ι → ℂ) (hr : ∀ j, r j ≠ 0)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f ≠ 0 := by
  intro h
  apply hf
  refine MvPolynomial.funext fun v => ?_
  have hv := eval_bind₁_scale r (fun j => v j / r j) f
  rw [h, map_zero] at hv
  have e : (fun j => r j * (v j / r j)) = v := by
    funext j
    first
      | exact mul_div_cancel₀ (v j) (hr j)
      | field_simp [hr j]
      | (rw [mul_comm]; exact div_mul_cancel₀ (v j) (hr j))
  rw [e] at hv
  rw [← hv, map_zero]

theorem integrable_scaled {ι : Type} [Fintype ι] (hBasic : TorusMeanBasicStatement)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ) (hr : ∀ j, r j ≠ 0) :
    Integrable (fun θ => Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖)
      (torusProb ι) := by
  have h := (hBasic ι).1 _ (bind1_C_mul_X_ne_zero_of_ne_zero r hr f hf)
  simpa only [eval_bind₁_scale] using h

theorem scaledTorusMean_le_update {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (i : ι) (hri : ‖r i‖ ≤ 1) :
    scaledTorusMean r f ≤ scaledTorusMean (Function.update r i 1) f := by
  have hr' : ∀ j, Function.update r i 1 j ≠ 0 := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hr j
  obtain ⟨hI1, hE1⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf r hr)
  obtain ⟨hI2, hE2⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf _ hr')
  unfold scaledTorusMean
  rw [hE1, hE2]
  refine integral_mono hI1 hI2 fun x => ?_
  set p : Polynomial ℂ := MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (r j * torusPoint x j)) f
  have key : ∀ (s : ι → ℂ), (∀ j, j ≠ i → s j = r j) → ∀ t : ℝ,
      MvPolynomial.eval (fun j => s j * torusPoint (Function.update x i t) j) f =
        p.eval (s i * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) := by
    intro s hs t
    rw [← eval_update_eq_eval_aeval]
    refine congrArg (fun w => MvPolynomial.eval w f) (funext fun j => ?_)
    by_cases h : j = i
    · subst h; simp [torusPoint]
    · simp [Function.update_of_ne h, hs j h, torusPoint]
  have k1 := key r (fun _ _ => rfl)
  have k2 := key (Function.update r i 1) (fun j h => Function.update_of_ne h _ _)
  simp only [Function.update_self, one_mul] at k2
  beta_reduce
  simp only [k1, k2]
  exact integral_log_eval_mul_le p (hr i) hri

theorem scaledTorusMean_le_torusMean {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, ‖r j‖ ≤ 1) :
    scaledTorusMean r f ≤ torusMean f := by
  classical
  have key : ∀ s : Finset ι, scaledTorusMean r f ≤
      scaledTorusMean (fun j => if j ∈ s then (1 : ℂ) else r j) f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      refine ih.trans ?_
      have hr' : ∀ j, (fun j => if j ∈ s then (1 : ℂ) else r j) j ≠ 0 := fun j => by
        dsimp only
        split_ifs <;> simp [hr j]
      have hra : ‖(fun j => if j ∈ s then (1 : ℂ) else r j) a‖ ≤ 1 := by
        simp [ha, hr1 a]
      have hle := scaledTorusMean_le_update hBasic f hf _ hr' a hra
      have e : Function.update (fun j => if j ∈ s then (1 : ℂ) else r j) a 1 =
          fun j => if j ∈ insert a s then (1 : ℂ) else r j := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp
        · simp [Finset.mem_insert, hj, Function.update_of_ne hj]
      rw [e] at hle
      exact hle
  have hu := key Finset.univ
  simp only [Finset.mem_univ, if_true] at hu
  rwa [scaledTorusMean_one] at hu

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory NumberField

theorem gauss_abs_log_support_finite {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbs w f)).Finite := by
  have hfin : (⋃ s ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f.coeff s)).Finite :=
    Set.Finite.biUnion f.support.finite_toSet fun s hs =>
      FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.1 hs)
  refine hfin.subset fun w hw => ?_
  by_contra hnot
  apply hw
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
  have h1 : gaussAbs w f = 1 := by
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w f zero_le_one fun s => ?_
      by_cases hs : s ∈ f.support
      · exact (hnot s hs).le
      · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
        exact zero_le_one
    · obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      rw [h, hnot s hs]
  simp [h1]

theorem isMultiHomogeneous_map_ring {K : Type*} [Field K] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : IsMultiHomogeneous a f) (φ : K →+* ℂ) :
    IsMultiHomogeneous a (MvPolynomial.map φ f) := by
  unfold IsMultiHomogeneous at hf ⊢
  first
  | exact fun d hd => hf d (by rwa [MvPolynomial.support_map_of_injective _ φ.injective] at hd)
  | exact fun b => (hf b).map φ
  | simpa [MvPolynomial.support_map_of_injective _ φ.injective] using hf
  | (intro d hd
     simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map, ne_eq, map_eq_zero] at hd
     exact hf d (by simpa using hd))

theorem sphere_mean_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) (B n : ℕ) (a a' : Fin B → ℕ)
    (F G : MvPolynomial (Fin B × Fin n) ℂ) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hF : IsMultiHomogeneous a F) (hG : IsMultiHomogeneous a' G) :
    blockSphereMean B n (F * G) = blockSphereMean B n F + blockSphereMean B n G := by
  unfold blockSphereMean
  rw [← integral_add (hInt B n a F hF0 hF) (hInt B n a' G hG0 hG)]
  refine integral_congr_ae ?_
  filter_upwards [ae_blockSphere_eval_ne_zero B n a F hF0 hF, ae_blockSphere_eval_ne_zero B n a' G hG0 hG]
    with z hz1 hz2
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hz1) (norm_ne_zero_iff.2 hz2)]

theorem gauss_height_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) {K : Type*} [Field K] [NumberField K]
    (B n : ℕ) (a a' : Fin B → ℕ) (f g : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0)
    (haf : IsMultiHomogeneous a f) (hbg : IsMultiHomogeneous a' g) :
    h0 (f * g) = h0 f + h0 g := by
  unfold h0
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w (f * g)) =
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) + ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w g) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite f hf) (gauss_abs_log_support_finite g hg)]
    refine finsum_congr fun w => ?_
    rw [gauss_abs_mul w f g hf hg, Real.log_mul (gauss_abs_pos_of_ne_zero w f hf).ne'
      (gauss_abs_pos_of_ne_zero w g hg).ne']
  have hinf : ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ (f * g)) =
      ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ f) +
        ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hinj := MvPolynomial.map_injective φ φ.injective (σ := Fin B × Fin n)
    rw [map_mul]
    exact sphere_mean_mul_multihomogeneous hInt B n a a' _ _
      (fun h => hf (hinj (by rw [h, map_zero])))
      (fun h => hg (hinj (by rw [h, map_zero])))
      (isMultiHomogeneous_map_ring a f haf φ) (isMultiHomogeneous_map_ring a' g hbg φ)
  rw [hfin, hinf]
  ring

theorem gauss_height_const_eq_zero {K : Type*} [Field K] [NumberField K] (B n : ℕ) (hn : 0 < n) (c : K)
    (hc : c ≠ 0) : h0 (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = 0 := by
  unfold h0

  have hG : ∀ w : FinitePlace K, gaussAbs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = w c := by
    intro w
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w _ (apply_nonneg w c) fun s => ?_
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact le_rfl
      · rw [map_zero]; exact apply_nonneg w c
    · have := coeff_le_gauss_abs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) 0
      rwa [MvPolynomial.coeff_C, if_pos rfl] at this
  simp_rw [hG]

  have hP : IsProbabilityMeasure (blockSphereProb B n) := by
    have : NeZero n := ⟨hn.ne'⟩
    have hne : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
      rw [Ne, Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    have : IsProbabilityMeasure (sphereProb n) := by
      unfold sphereProb
      exact ProbabilityTheory.cond_isProbabilityMeasure hne
    unfold blockSphereProb
    infer_instance
  have hM : ∀ φ : K →+* ℂ, blockSphereMean B n
      (MvPolynomial.map φ (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K)) = Real.log ‖φ c‖ := by
    intro φ
    unfold blockSphereMean
    simp [MvPolynomial.map_C, MvPolynomial.eval_C]
  simp_rw [hM]

  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel, zero_div]

theorem gauss_height_add_of_sphere (hInt : SphereLogIntegrableStatement) : HeightAdditiveStatement := by
  intro K _ _ B n a a' f g hn hf hg haf hbg
  refine ⟨gauss_height_mul_multihomogeneous hInt B n a a' f g hf hg haf hbg, fun c hc => ?_⟩
  have hC : IsMultiHomogeneous (fun _ : Fin B => 0) (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) := by
    intro s hs b
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hs
    split_ifs at hs with h
    · subst h; simp
    · exact absurd rfl hs
  have hC0 : (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) ≠ 0 := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  rw [gauss_height_mul_multihomogeneous hInt B n _ a _ f hC0 hf hC haf, gauss_height_const_eq_zero B n hn c hc, zero_add]

end ReciprocityTheory.MultiplicativeHeights
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Finset Pointwise

private lemma support_subset_of_mem_span_of_support_subset {ι : Type} (s : Set (ι →₀ ℕ))
    (G : Set (MvPolynomial ι ℂ)) (hG : ∀ g ∈ G, (g.support : Set (ι →₀ ℕ)) ⊆ s)
    {p : MvPolynomial ι ℂ} (hp : p ∈ Submodule.span ℂ G) : (p.support : Set (ι →₀ ℕ)) ⊆ s := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => simp
  | add x y _ _ hx hy =>
    intro t ht
    rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
    exacts [hx h, hy h]
  | smul a x _ hx => exact fun t ht => hx (MvPolynomial.support_smul ht)

theorem gram_of_linearOrder {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)) (hF : F ≠ 0) :
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re := by
  obtain ⟨m, hmS, hminj, hmlex⟩ := exists_lex_enum S
  let T : Finset (ι →₀ ℕ) := S.biUnion fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support
  have hPT : ∀ s ∈ S, (F * MvPolynomial.monomial s (1 : ℂ)).support ⊆ T := fun s hs =>
    Finset.subset_biUnion_of_mem (fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support) hs
  let v : Fin S.card → EuclideanSpace ℂ T := fun k => coeffVec T (F * MvPolynomial.monomial (m k) 1)

  have hbij : Function.Bijective (fun k : Fin S.card => (⟨m k, hmS k⟩ : S)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun a b h => hminj (congrArg Subtype.val h), by simp⟩
  let e : Fin S.card ≃ S := Equiv.ofBijective _ hbij
  have hdet : Matrix.det (Matrix.of fun a b : S =>
        polyInner (F * MvPolynomial.monomial (a : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (b : ι →₀ ℕ) 1)) = (Matrix.gram ℂ v).det := by
    rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose (Matrix.gram ℂ v)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply,
      e, Equiv.ofBijective_apply]
    exact polyInner_eq_inner T _ _ (hPT _ (hmS i))
  have hT : ∀ j, ((F * MvPolynomial.monomial (m j) (1 : ℂ)).support : Set (ι →₀ ℕ)) ⊆ T :=
    fun j => by exact_mod_cast hPT _ (hmS j)

  have hδ : ∀ k : Fin S.card, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k),
      Real.exp (2 * torusMean F) ≤ ‖v k - x‖ ^ 2 := by
    intro k x hx
    have hspan : Submodule.span ℂ (v '' Set.Iio k) =
        (Submodule.span ℂ ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)).map
          ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [hspan] at hx
    obtain ⟨Q, hQ, rfl⟩ := hx
    have hQsupp : ∀ t ∈ Q.support, toLex (m k) < toLex t := by
      have hs := support_subset_of_mem_span_of_support_subset {t | toLex (m k) < toLex t} _ (by
        rintro _ ⟨j, hj, rfl⟩ t ht
        have ht' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
        subst ht'
        exact hmlex j k hj) hQ
      intro t ht
      exact hs ht
    have hmain := exp_torus_mean_le_l2_of_lex hBasic hLex hL2 F hF (m k) Q hQsupp
    have hFQ : ((F * Q).support : Set (ι →₀ ℕ)) ⊆ T := by
      have hmemFQ : F * Q ∈ Submodule.span ℂ
          ((LinearMap.mulLeft ℂ F) '' ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map.mpr ⟨Q, hQ, rfl⟩
      refine support_subset_of_mem_span_of_support_subset _ _ ?_ hmemFQ
      rintro _ ⟨_, ⟨j, _, rfl⟩, rfl⟩
      exact hT j
    have hsupp : (F * (MvPolynomial.monomial (m k) 1 - Q)).support ⊆ T := by
      rw [mul_sub]
      intro t ht
      rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ ht) with h | h
      · exact_mod_cast hT k h
      · exact_mod_cast hFQ h
    have hsub : v k - ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) Q =
        coeffVec T (F * (MvPolynomial.monomial (m k) 1 - Q)) := by
      rw [mul_sub, map_sub] <;> rfl
    rw [hsub, norm_coeffVec T _ hsupp]
    calc Real.exp (2 * torusMean F) = Real.exp (torusMean F) ^ 2 := by
          rw [sq, ← Real.exp_add, two_mul]
      _ ≤ _ := by gcongr
  have hprod := prod_le_re_det_gram S.card v (fun _ => Real.exp (2 * torusMean F))
    (fun _ => (Real.exp_pos _).le) hδ
  rw [hdet]
  refine le_trans (le_of_eq ?_) hprod
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  congr 1
  ring

theorem gram_holds (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) : GramStatement := by
  unfold GramStatement
  intro ι _ _ F S hF
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  convert gram_of_linearOrder hBasic hLex hL2 F S hF

end ReciprocityTheory.MultiplicativeHeights
end
