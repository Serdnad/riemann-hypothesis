module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic.Continuity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.NumberTheory.NumberField.CMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem det_of_blockTriangular_injective {m α R : Type} [Fintype m] [DecidableEq m]
    [LinearOrder α] [CommRing R] (M : Matrix m m R) (f : m → α) (hf : Function.Injective f)
    (h : M.BlockTriangular f) : M.det = ∏ i, M i i := by
  letI : LinearOrder m := LinearOrder.lift' f hf
  exact Matrix.det_of_upperTriangular (M := M) (fun i j hij => h hij)

theorem prod_lowerPairs_fst {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.1 = ∏ a, d a ^ (a : ℕ) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Iio a]
  congr 1
  ext c; simp

theorem prod_lowerPairs_snd {r : ℕ} (d : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, d p.1.2 = ∏ a, d a ^ (r - 1 - (a : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1)
    (by simp) (fun p => d p.2), Finset.prod_filter, Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi a]
  congr 1
  ext c; simp

theorem det_conj_strictLower : (∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ), B.det ≠ 0 → (∀ a c : Fin r, c < a → B a c = 0) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2).det = ∏ a : Fin r, B a a ^ (2 * (a : ℤ) - ((r : ℤ) - 1))) := by
  intro r B hdet htri
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hu
  have hB : B.BlockTriangular id := fun a c h => htri a c h
  have hBi : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have hdiag : ∀ a, B a a * B⁻¹ a a = 1 := by
    intro a
    have h1 : (B * B⁻¹) a a = 1 := by rw [Matrix.mul_nonsing_inv B hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · exact h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [htri a c h, zero_mul]
      · rw [hBi (i := c) (j := a) h, mul_zero]
    · simp
  have hne : ∀ a, B a a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (hdiag a)
  have hinv : ∀ a, B⁻¹ a a = (B a a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (hdiag a)
  rw [det_of_blockTriangular_injective _
    (fun p : {p : Fin r × Fin r // p.2 < p.1} => toLex (p.1.1, OrderDual.toDual p.1.2))]
  · simp only [Matrix.of_apply, hinv]
    rw [Finset.prod_mul_distrib, prod_lowerPairs_fst (fun a => B a a),
      prod_lowerPairs_snd (fun a => (B a a)⁻¹), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hne a)]
    congr 1
    have := a.2
    omega
  · intro p q h
    have h' := toLex.injective h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
    exact Subtype.ext (Prod.ext h'.1 h'.2)
  · intro p q h
    simp only [Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at h
    rcases h with h | ⟨_, h⟩
    · simp [htri _ _ h]
    · simp [hBi (i := q.1.2) (j := p.1.2) h]

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

theorem span_image_inf_span_image_of_linearIndependent {R V ι : Type} [CommRing R]
    [AddCommGroup V] [Module R V] {w : ι → V} (hw : LinearIndependent R w) (s t : Set ι) :
    Submodule.span R (w '' s) ⊓ Submodule.span R (w '' t) = Submodule.span R (w '' (s ∩ t)) := by
  apply le_antisymm
  · rintro x ⟨hs, ht⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hs
    obtain ⟨m, hm, hmx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 ht
    have hlm : l = m := hw (hlx.trans hmx.symm)
    subst hlm
    refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨l, ?_, hlx⟩
    rw [Finsupp.mem_supported] at hl hm ⊢
    exact Set.subset_inter hl hm
  · exact le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Set.inter_subset_right))

theorem span_inf_sup_overlapping_parts :
    ∀ (R V α β γ : Type) [CommRing R] [AddCommGroup V] [Module R V] (w : α ⊕ β ⊕ γ → V),
      LinearIndependent R w →
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊓
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range (w ∘ Sum.inl)) ∧
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊔
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range w) := by
  intro R V α β γ _ _ _ w hw
  constructor
  · rw [Set.range_comp, Set.range_comp, Set.range_comp,
      span_image_inf_span_image_of_linearIndependent hw]
    congr 2
    ext x
    rcases x with a | b | c <;> simp
  · rw [← Submodule.span_union, Set.range_comp, Set.range_comp, ← Set.image_union,
      show (Set.range (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ) ∪
          Set.range (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) = Set.univ from by
        ext x
        rcases x with a | b | c <;> simp, Set.image_univ]

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
theorem _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent
    (K : Type) [Field K] (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → K)
    (hw : LinearIndependent K w) :
    ∃ e : ι → Fin r, Function.Injective e ∧ (Matrix.of fun k a => w a (e k)).det ≠ 0 := by
  classical
  set A : Matrix (Fin r) ι K := Matrix.of fun k a => w a k with hA
  have hcol : A.col = w := rfl
  have hrank : A.rank = Fintype.card ι := by
    rw [← Matrix.finrank_span_range_col, hcol, finrank_span_eq_card hw]
  have htop : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  haveI : Fintype κ := Fintype.ofInjective a ha
  let b := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K), Module.finrank_eq_card_basis b]
  let f : ι ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ f, ha.comp f.injective, ?_⟩
  have hrow : LinearIndependent K (Matrix.of fun k a' => w a' ((a ∘ f) k)).row :=
    hli.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrow)).ne_zero

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in
theorem _root_.GlobalTheory.index_range_mulVecLin_eq_abs_norm_det :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (𝓞 E)), A.det ≠ 0 →
      (((LinearMap.range A.mulVecLin).toAddSubgroup.index : ℕ) : ℚ) =
        |Algebra.norm ℚ ((A.det : 𝓞 E) : E)|) := by
  intro ι _ _ A hA
  classical
  set f := A.mulVecLin with hf
  have hinj : Function.Injective f := by
    intro u v huv
    have h : A.mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hA h)
  let b := Module.Free.chooseBasis ℤ (ι → 𝓞 E)
  let fZ : (ι → 𝓞 E) →ₗ[ℤ] (ι → 𝓞 E) := f.restrictScalars ℤ
  have hinjZ : Function.Injective fZ := hinj
  let e := LinearEquiv.ofInjective fZ hinjZ
  have key := AddSubgroup.index_eq_natAbs_det b (LinearMap.range f).toAddSubgroup (b.map e)
  rw [key]
  have hdet : (b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)) = LinearMap.det fZ := by
    rw [Module.Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, e]
  have h2 : (((b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)).natAbs : ℕ) : ℚ) =
      |Algebra.norm ℚ ((A.det : 𝓞 E) : E)| := by
    rw [hdet, LinearMap.det_restrictScalars, hf, ← Matrix.toLin'_apply', LinearMap.det_toLin',
      Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
  exact h2

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Filter Topology

namespace GlobalTheory.JacobianIndependence

theorem eq_zero_of_eventually_eval {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (a : EuclideanSpace ℂ (Fin n))
    (h : ∀ᶠ w in 𝓝 a, MvPolynomial.eval (fun k => w k) p = 0) : p = 0 := by
  have hc : Continuous (fun x : Fin n → ℂ => (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))) :=
    PiLp.continuous_toLp 2 _
  have h1 : ∀ᶠ x in 𝓝 (fun k => a k), MvPolynomial.eval x p = 0 :=
    (hc.tendsto (fun k => a k)).eventually h
  rw [nhds_pi, Filter.Eventually, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  refine MvPolynomial.funext_set t (fun i => infinite_of_mem_nhds _ (ht i)) ?_
  intro x hx
  rw [map_zero]
  exact hsub (fun i _ => hx i (Set.mem_univ i))

theorem eq_zero_of_det_fderiv_ne_zero :
    ∀ (n : ℕ) (f : Fin n → V n → ℂ), (∀ k, ∀ᶠ z in nhds (0 : V n), DifferentiableAt ℂ (f k) z) →
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => f k z : V n)) 0).det ≠ 0 →
      ∀ p : MvPolynomial (Fin n) ℂ,
        (∀ᶠ z in nhds (0 : V n), MvPolynomial.eval (fun k => f k z) p = 0) → p = 0 := by
  intro n f hf hdet p hp
  set F : V n → V n := fun z : V n => (WithLp.toLp 2 fun k => f k z : V n) with hF
  have hd : ∀ᶠ z in 𝓝 (0 : V n), DifferentiableAt ℂ F z := by
    filter_upwards [Filter.eventually_all.2 hf] with z hz
    exact differentiableAt_euclidean.2 hz
  have ha : AnalyticAt ℂ F 0 := GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hd
  have hs : HasStrictFDerivAt F
      (((fderiv ℂ F 0).toContinuousLinearEquivOfDetNeZero hdet : V n ≃L[ℂ] V n) :
        V n →L[ℂ] V n) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact ha.hasStrictFDerivAt
  refine eq_zero_of_eventually_eval p (F 0) ?_
  rw [← hs.map_nhds_eq_of_equiv, Filter.eventually_map]
  exact hp

end GlobalTheory.JacobianIndependence
end
