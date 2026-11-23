module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurveComplexPoint

theorem eval₂_smul_homog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Type*} [CommRing F] (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a)
    (c : K → F) (y : (Σ k, ι k) → F) :
    eval₂ (Int.castRingHom F) (fun p => c p.1 * y p) f =
      (∏ k, c k ^ a k) * eval₂ (Int.castRingHom F) y f := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), c i.1 ^ d i) = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem full : CurveComplexPoint.Statement := by
  intro K _ ι _ W hW
  classical
  obtain ⟨_, ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩, hhor, _⟩ := hW
  choose c hc using hrel
  let R := MRing ι ⧸ W
  let F := FractionRing R
  let x : (Σ k, ι k) → F := fun p => algebraMap R F (Ideal.Quotient.mk W (X p))
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k h => hc k
    (Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective R F (h.trans (map_zero _).symm)))
  have hxeval : ∀ f : MRing ι,
      eval₂ (Int.castRingHom F) x f = algebraMap R F (Ideal.Quotient.mk W f) := by
    intro f
    have h : eval₂Hom (Int.castRingHom F) x = (algebraMap R F).comp (Ideal.Quotient.mk W) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [x])
    exact RingHom.congr_fun h f
  have : CharZero F := charZero_of_inj_zero fun n hn => by
    have h1 : Ideal.Quotient.mk W (C (n : ℤ)) = 0 :=
      IsFractionRing.injective R F (by simpa using hn)
    have h2 : (n : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    rw [hhor, Ideal.mem_bot] at h2
    exact_mod_cast h2
  let y : (Σ k, ι k) → F := fun p => (x ⟨p.1, c p.1⟩)⁻¹ * x p
  let ψ : MvPolynomial (Σ k, ι k) ℚ →+* F := eval₂Hom (Rat.castHom F) y
  have hψmap : ∀ f : MRing ι,
      ψ (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom F) y f := by
    intro f
    simp only [ψ, coe_eval₂Hom, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have hWker : ∀ f ∈ W, map (Int.castRingHom ℚ) f ∈ RingHom.ker ψ := by
    intro f hf
    rw [hWS] at hf
    have hle : Ideal.span S ≤ (RingHom.ker ψ).comap (map (Int.castRingHom ℚ)) := by
      refine Ideal.span_le.mpr fun s hs => ?_
      obtain ⟨a, ha⟩ := hS s hs
      have hsW : s ∈ W := hWS ▸ Ideal.subset_span hs
      show ψ (map (Int.castRingHom ℚ) s) = 0
      rw [hψmap]
      refine (eval₂_smul_homog s a ha (fun k => (x ⟨k, c k⟩)⁻¹) x).trans ?_
      rw [hxeval, Ideal.Quotient.eq_zero_iff_mem.mpr hsW, map_zero, mul_zero]
    exact hle hf
  have hXker : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker ψ := by
    intro k
    rw [RingHom.mem_ker, map_sub, map_one]
    simp only [ψ, coe_eval₂Hom, eval₂_X, y]
    rw [inv_mul_cancel₀ (hx k), sub_self]
  obtain ⟨m, hm, hkm⟩ := Ideal.exists_le_maximal (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
  let L := MvPolynomial (Σ k, ι k) ℚ ⧸ m
  let : Field L := Ideal.Quotient.field m
  have : Module.Finite ℚ L := finite_of_finite_type_of_isJacobsonRing ℚ L
  have : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  let φ : L →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let z : (Σ k, ι k) → ℂ := fun p => φ (Ideal.Quotient.mk m (X p))
  have hz : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
      φ (Ideal.Quotient.mk m (map (Int.castRingHom ℚ) f)) := by
    intro f
    have h : eval₂Hom (Int.castRingHom ℂ) z =
        (φ : L →+* ℂ).comp ((Ideal.Quotient.mk m).comp (map (Int.castRingHom ℚ))) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [z])
    rw [eval_map]
    exact RingHom.congr_fun h f
  refine ⟨z, fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : Ideal.Quotient.mk m (X ⟨k, c k⟩) = Ideal.Quotient.mk m 1 :=
      Ideal.Quotient.eq.mpr (hkm (hXker k))
    simp only [z, h1, map_one]
    exact one_ne_zero
  · rw [hz, Ideal.Quotient.eq_zero_iff_mem.mpr (hkm (hWker f hf)), map_zero]

end CurveComplexPoint

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem finitePlace_le_one_of_isIntegral {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {x : K} (hx : IsIntegral ℤ x) : v x ≤ 1 := by
  let y : 𝓞 K := ⟨x, hx⟩
  have h := FinitePlace.norm_le_one K v.maximalIdeal y
  rw [FinitePlace.norm_embedding_eq] at h
  exact h

theorem finsum_log_finitePlace_natCast {K : Type*} [Field K] [NumberField K] {δ : ℕ} (hδ : 0 < δ) :
    ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = -(Module.finrank ℚ K * Real.log δ) := by
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w (δ : K)).Finite :=
    FinitePlace.hasFiniteMulSupport hne
  have hprod := FinitePlace.prod_eq_inv_abs_norm hne
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun x hx ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hx))] at hprod
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [← Real.log_prod (fun v _ ↦ (map_ne_zero _).mpr hne), hprod]
    have : Algebra.norm ℚ ((δ : ℕ) : K) = (δ : ℚ) ^ (Module.finrank ℚ K) := by
      have := Algebra.norm_algebraMap (S := K) (δ : ℚ)
      simpa using this
    rw [this]
    push_cast
    rw [abs_pow, Nat.abs_cast, Real.log_inv, Real.log_pow]
  · intro v hv
    have h1' : v (δ : K) ≠ 1 := fun h ↦ hv (by show Real.log (v (δ : K)) = 0; rw [h, Real.log_one])
    exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr h1')

theorem vectorL2Norm_le_sqrt_card_mul {m : ℕ} (w : Fin m → ℂ) {R : ℝ} (hR : 0 ≤ R) (hw : ∀ i, ‖w i‖ ≤ R) :
    l2Norm w ≤ Real.sqrt m * R := by
  rw [l2Norm, ← Real.sqrt_sq hR, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin m, R ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
    _ = m * R ^ 2 := by simp

theorem height_standard_le (z : Cone n (AlgebraicClosure ℚ)) (hz : BlockNonzero z) {δ : ℕ}
    (hδ : 0 < δ) {R : ℝ} (hR : 0 < R)
    (hint : ∀ k i, IsIntegral ℤ ((δ : AlgebraicClosure ℚ) * z k i))
    (harch : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) k i, ‖σ (z k i)‖ ≤ R) :
    height (HermLine.standard (n := n)) z ≤
      ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
  set K := coordField z
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd_def
  have hd : 0 < d := by rw [hd_def]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hne : ((δ : ℕ) : K) ≠ 0 := by exact_mod_cast hδ.ne'

  have hloc : ∀ (v : FinitePlace K) (k : ι),
      Real.log (⨆ i, v (coordVec z k i)) ≤ -Real.log (v (δ : K)) := by
    intro v k
    have hδv : 0 < v (δ : K) := FinitePlace.pos_iff.mpr hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
    have hi0' : coordVec z k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
    have hpos : 0 < ⨆ i, v (coordVec z k i) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.mpr hi0')
        (le_ciSup (f := fun i ↦ v (coordVec z k i)) (Set.finite_range _).bddAbove i0)
    rw [← Real.log_inv]
    refine Real.log_le_log hpos (ciSup_le fun i ↦ ?_)
    have hI : IsIntegral ℤ ((δ : K) * coordVec z k i) := by
      have h1 := hint k i
      have h2 : (K.val : K →+* AlgebraicClosure ℚ) ((δ : K) * coordVec z k i) =
          (δ : AlgebraicClosure ℚ) * z k i := by
        simp [coordVec]
      rw [← h2] at h1
      exact (isIntegral_algHom_iff ((K.val : K →+* AlgebraicClosure ℚ).toIntAlgHom)
        K.val.injective).mp h1
    have h3 := finitePlace_le_one_of_isIntegral v hI
    rw [map_mul] at h3
    calc v (coordVec z k i) = (v (δ : K))⁻¹ * (v (δ : K) * v (coordVec z k i)) := by
          field_simp
      _ ≤ (v (δ : K))⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hδv).le
      _ = (v (δ : K))⁻¹ := mul_one _
  have hsupp1 := finite_support_height (HermLine.standard (n := n)) z hz
  have hsupp2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (δ : K))).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hne).subset fun v hv h ↦ hv ?_
    have h' : v (δ : K) = 1 := h
    show Real.log (v (δ : K)) = 0
    rw [h', Real.log_one]
  set T := (hsupp1.union hsupp2).toFinset
  have hfin : (∑ᶠ v : FinitePlace K, ∑ k, ((HermLine.standard (n := n)).deg k : ℝ) *
      Real.log (⨆ i, v (coordVec z k i))) ≤ Fintype.card ι * (d * Real.log δ) := by
    rw [finsum_eq_sum_of_support_subset (s := T) _
      (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inl hv)))]
    have h2 : ∑ᶠ v : FinitePlace K, Real.log (v (δ : K)) = ∑ v ∈ T, Real.log (v (δ : K)) :=
      finsum_eq_sum_of_support_subset (s := T) _
        (fun v hv ↦ Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Or.inr hv)))
    have h3 := finsum_log_finitePlace_natCast (K := K) hδ
    rw [h2] at h3
    calc ∑ v ∈ T, ∑ k, ((HermLine.standard (n := n)).deg k : ℝ) * Real.log (⨆ i, v (coordVec z k i))
        ≤ ∑ v ∈ T, ∑ _k : ι, -Real.log (v (δ : K)) := by
          refine Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
          simp only [HermLine.standard, Int.cast_one, one_mul]
          exact hloc v k
      _ = Fintype.card ι * -(∑ v ∈ T, Real.log (v (δ : K))) := by
          simp [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = Fintype.card ι * (d * Real.log δ) := by rw [h3, neg_neg]

  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> rfl
  have : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have harchK : ∀ σ : K →+* ℂ, Real.log ((HermLine.standard (n := n)).metric
      fun k i ↦ σ (coordVec z k i)) ≤ ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    intro σ
    let σ' : AlgebraicClosure ℚ →+* ℂ := ComplexEmbedding.lift (AlgebraicClosure ℚ) σ
    have hσ : ∀ k i, σ (coordVec z k i) = σ' (z k i) := by
      intro k i
      have := ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure ℚ) σ (coordVec z k i)
      rw [← this]
      rfl
    have hpos : ∀ k, 0 < l2Norm (fun i ↦ σ (coordVec z k i)) := by
      intro k
      obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hz k)
      refine vectorL2Norm_pos (Function.ne_iff.mpr ⟨i0, ?_⟩)
      intro h
      apply hi0
      have h2 := (map_eq_zero σ).mp h
      have := congrArg Subtype.val h2
      simpa [coordVec] using this
    change Real.log (∏ k, l2Norm (fun i ↦ σ (coordVec z k i))) ≤ _
    rw [Real.log_prod (fun k _ ↦ (hpos k).ne')]
    refine Finset.sum_le_sum fun k _ ↦ Real.log_le_log (hpos k) ?_
    have := vectorL2Norm_le_sqrt_card_mul (fun i ↦ σ (coordVec z k i)) hR.le (fun i ↦ by rw [hσ]; exact harch σ' k i)
    simpa using this
  have harchSum : ∑ σ : K →+* ℂ, Real.log ((HermLine.standard (n := n)).metric
      fun k i ↦ σ (coordVec z k i)) ≤ d * ∑ k, Real.log (Real.sqrt (n k + 1) * R) := by
    refine (Finset.sum_le_sum fun σ _ ↦ harchK σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]

  set S := ∑ k, Real.log (Real.sqrt (n k + 1) * R) with hS
  unfold height
  rw [← hd_def]
  calc d⁻¹ * (_ + _) ≤ d⁻¹ * (Fintype.card ι * (d * Real.log δ) +
        d * ∑ k, Real.log (Real.sqrt (n k + 1) * R)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfin harchSum) (inv_pos.mpr hd).le
    _ = ∑ k, (Real.log δ + Real.log (Real.sqrt (n k + 1) * R)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hS]
        field_simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

noncomputable section

section GramGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem det_gram_sumElim_of_orthogonal {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (v : ι → V) (w : κ → V) (h : ∀ i j, inner ℂ (v i) (w j) = 0) :
    det (gram ℂ (Sum.elim v w)) = det (gram ℂ v) * det (gram ℂ w) := by
  have hg : gram ℂ (Sum.elim v w) = fromBlocks (gram ℂ v) 0 0 (gram ℂ w) := by
    ext (i | i) (j | j)
    · simp [gram_apply]
    · simp [gram_apply, h]
    · simp [gram_apply, inner_eq_zero_symm.mp (h j i)]
    · simp [gram_apply]
  rw [hg, det_fromBlocks_zero₂₁]

theorem det_gram_sumElim_sub {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) (M : Matrix ι κ ℂ) :
    det (gram ℂ (Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i))) = det (gram ℂ (Sum.elim v u)) := by
  set B : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 (-M) 0 1 with hBdef
  have hc : Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i) =
      fun b ↦ ∑ a, B a b • Sum.elim v u a := by
    funext b
    rcases b with i | j
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, ite_smul, sub_eq_add_neg, add_comm]
  have hB : det B = 1 := by simp [B]
  rw [hc, gram_comb, det_mul, det_mul, det_conjTranspose, hB]
  simp

end GramGeometry

section GramGeometry2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance hasOrthogonalProjection_span_range {ι : Type*} [Fintype ι] (v : ι → V) :
    (Submodule.span ℂ (Set.range v)).HasOrthogonalProjection := by
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  infer_instance

theorem det_gram_sumElim_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) :
    det (gram ℂ (Sum.elim v u)) = det (gram ℂ v) *
      det (gram ℂ (fun j ↦ u j - (Submodule.span ℂ (Set.range v)).starProjection (u j))) := by
  set U := Submodule.span ℂ (Set.range v)
  have hmem : ∀ j, ∃ c : ι → ℂ, ∑ i, c i • v i = U.starProjection (u j) := fun j ↦
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem (u j))
  choose c hc using hmem
  have hu : (fun j ↦ u j - U.starProjection (u j)) = fun j ↦ u j - ∑ i, (of fun i j ↦ c j i) i j • v i := by
    funext j
    simp [hc]
  rw [← det_gram_sumElim_sub v u (of fun i j ↦ c j i), ← hu]
  refine det_gram_sumElim_of_orthogonal v _ fun i j ↦ ?_
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i))
    (U.sub_starProjection_mem_orthogonal (u j))

theorem det_gram_unique {κ : Type*} [Unique κ] (w : κ → V) :
    det (gram ℂ w) = ((‖w default‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_unique, gram_apply, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem det_gram_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    0 ≤ det (gram ℂ w) :=
  (posSemidef_gram ℂ w).det_nonneg

theorem im_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    (det (gram ℂ w)).im = 0 :=
  ((Complex.nonneg_iff.mp (det_gram_nonneg w)).2).symm

theorem det_gram_re_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    0 ≤ (det (gram ℂ w)).re :=
  (Complex.nonneg_iff.mp (det_gram_nonneg w)).1

theorem det_gram_comp_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (w : ι → V) : det (gram ℂ (w ∘ e)) = det (gram ℂ w) := by
  have : gram ℂ (w ∘ e) = (gram ℂ w).submatrix e e := by ext i j; rfl
  rw [this, det_submatrix_equiv_self]

theorem norm_sub_proj_map_le {ι : Type*} [Fintype ι] (Y : Submodule ℂ V) [Y.HasOrthogonalProjection]
    (c : ι → V) (x : V) :
    ‖Y.starProjection x - (Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))).starProjection
        (Y.starProjection x)‖ ≤ ‖x - (Submodule.span ℂ (Set.range c)).starProjection x‖ := by
  set U := Submodule.span ℂ (Set.range c)
  set U' := Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem x)
  have hmem : Y.starProjection (U.starProjection x) ∈ U' := by

    rw [← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 : ‖Y.starProjection x - U'.starProjection (Y.starProjection x)‖ ≤
      ‖Y.starProjection x - Y.starProjection (U.starProjection x)‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (⟨_, hmem⟩ : U')
  refine h1.trans ?_
  rw [← map_sub]
  exact Y.norm_starProjection_apply_le _

theorem re_det_gram_proj_le_fin (Y : Submodule ℂ V) [Y.HasOrthogonalProjection] :
    ∀ (n : ℕ) (c : Fin n → V),
      (det (gram ℂ fun i ↦ Y.starProjection (c i))).re ≤ (det (gram ℂ c)).re := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
    have he : ∀ (w : Fin (n + 1) → V), w ∘ e =
        Sum.elim (fun i ↦ w i.castSucc) (fun _ : Unit ↦ w (Fin.last n)) := by
      intro w
      funext b
      rcases b with i | u
      · rfl
      · simp only [Function.comp_apply, Sum.elim_inr]
        congr 1
    have key : ∀ (w : Fin (n + 1) → V), det (gram ℂ w) = det (gram ℂ fun i : Fin n ↦ w i.castSucc) *
        ((‖w (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ w i.castSucc)).starProjection
          (w (Fin.last n))‖ ^ 2 : ℝ) : ℂ) := by
      intro w
      rw [← det_gram_comp_equiv e w, he, det_gram_sumElim_eq, det_gram_unique]
    rw [key c, key (fun i ↦ Y.starProjection (c i))]
    have hc' := ih (fun i : Fin n ↦ c i.castSucc)
    simp only [Complex.re_mul_ofReal]
    have hn := norm_sub_proj_map_le Y (fun i : Fin n ↦ c i.castSucc) (c (Fin.last n))
    exact mul_le_mul hc' (pow_le_pow_left₀ (norm_nonneg _) hn 2) (sq_nonneg _)
      (det_gram_re_nonneg _)

theorem re_det_gram_proj_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Submodule ℂ V)
    [Y.HasOrthogonalProjection] (c : ι → V) :
    (det (gram ℂ fun i ↦ Y.starProjection (c i))).re ≤ (det (gram ℂ c)).re := by
  let e := (Fintype.equivFin ι).symm
  have h := re_det_gram_proj_le_fin Y (Fintype.card ι) (c ∘ e)
  rwa [det_gram_comp_equiv e c, show (fun i ↦ Y.starProjection ((c ∘ e) i)) =
    (fun i ↦ Y.starProjection (c i)) ∘ e from rfl, det_gram_comp_equiv] at h

theorem re_det_gram_sumElim_ge {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (W : Submodule ℂ V) [W.HasOrthogonalProjection] (v : ι → V) (hv : ∀ i, v i ∈ W) (u : κ → V) :
    (det (gram ℂ v)).re * (det (gram ℂ fun j ↦ Wᗮ.starProjection (u j))).re ≤
      (det (gram ℂ (Sum.elim v u))).re := by
  set U := Submodule.span ℂ (Set.range v)
  have hUW : U ≤ W := Submodule.span_le.mpr (Set.range_subset_iff.mpr hv)
  rw [det_gram_sumElim_eq, Complex.mul_re, im_det_gram v, zero_mul, sub_zero]
  refine mul_le_mul_of_nonneg_left ?_ (det_gram_re_nonneg v)
  have hQ : (fun j ↦ Wᗮ.starProjection (u j)) =
      fun j ↦ Wᗮ.starProjection (u j - U.starProjection (u j)) := by
    funext j
    rw [map_sub, sub_eq_self.mpr]
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal W (hUW (U.starProjection_apply_mem (u j)))
  rw [hQ]
  exact re_det_gram_proj_le Wᗮ _

end GramGeometry2

end

end GroundTheory.Heights₂.Heights
end
