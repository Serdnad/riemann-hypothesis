module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSuppLemmas
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def ratioVec (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Coord n → ratioField x :=
  fun p ↦ ⟨x p.1 p.2 / x p.1 (c p.1), div_mem_ratioField x _ _ _⟩

theorem val_aeval_ratioVec (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    ((aeval (ratioVec x c) f : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f :=
  DFunLike.congr_fun (comp_aeval (ratioVec x c) (ratioField x).val) f

theorem aeval_ratioVec_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    Function.Surjective (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ratioField x) := by
  set S := Set.range fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)
  have hL : ratioField x = IntermediateField.adjoin ℚ S := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro _ ⟨⟨k, i, j⟩, rfl⟩
      dsimp only
      rw [← div_div_div_cancel_right₀ (hc k) (x k i) (x k j)]
      exact div_mem (IntermediateField.subset_adjoin ℚ S ⟨⟨k, i⟩, rfl⟩)
        (IntermediateField.subset_adjoin ℚ S ⟨⟨k, j⟩, rfl⟩)
    · rintro _ ⟨p, rfl⟩
      exact div_mem_ratioField x _ _ _
  intro a
  have ha : (a : AlgebraicClosure ℚ) ∈
      (aeval (R := ℚ) fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)).range := by
    have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    rw [aeval_range, ← IntermediateField.adjoin_toSubalgebra, ← hL]
    exact a.2
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, Subtype.ext ((val_aeval_ratioVec x c f).trans hf)⟩

theorem exists_extend_embedding (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (τ : L →+* ℂ) :
    ∃ σ : AlgebraicClosure ℚ →+* ℂ, ∀ a : L, σ a = τ a := by
  let : Algebra L ℂ := τ.toAlgebra
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact ⟨(IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).toRingHom, fun a ↦
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).commutes a⟩

theorem OrbitDegreeRatio.proof : OrbitDegreeRatio.Statement := by
  intro ι _ _ _ n x hx
  obtain ⟨c, hc⟩ := exists_chart hx
  set W := orbitIdeal x
  set L := ratioField x
  set Q := Quot fun z z' : Geo.mcPts (ι := blockIdx n) W ↦
    ∃ a : ι → ℂ, (∀ k, a k ≠ 0) ∧ (z' : Coord n → ℂ) = fun p ↦ a p.1 * (z : Coord n → ℂ) p
  show Nat.card Q = _
  choose σ hσ using exists_extend_embedding L
  have hpt : ∀ τ : L →+* ℂ, (fun p ↦ σ τ (flatCone x p)) ∈ Geo.mcPts (ι := blockIdx n) W := by
    intro τ
    refine ⟨fun k ↦ ?_, fun f hf ↦ eval_conj_eq_zero x (σ τ) hf⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  let Φ : (L →+* ℂ) → Q := fun τ ↦ Quot.mk _ ⟨_, hpt τ⟩

  let R : Q → Coord n → ℂ := Quot.lift
    (fun z p ↦ (z : Coord n → ℂ) p / (z : Coord n → ℂ) ⟨p.1, c p.1⟩) (by
      rintro z z' ⟨a, ha, e⟩
      funext p
      simp only [e]
      rw [mul_div_mul_left _ _ (ha p.1)])
  have hRΦ : ∀ τ p, R (Φ τ) p = τ (ratioVec x c p) := by
    intro τ p
    show σ τ (x p.1 p.2) / σ τ (x p.1 (c p.1)) = _
    rw [← map_div₀]
    exact hσ τ (ratioVec x c p)
  have hτ : ∀ (τ : L →+* ℂ) f, τ (aeval (ratioVec x c) f) =
      aeval (fun p ↦ τ (ratioVec x c p)) f := fun τ f ↦
    DFunLike.congr_fun (comp_aeval (ratioVec x c) τ.toRatAlgHom) f
  let ψ : MvPolynomial (Coord n) ℚ →+* L :=
    (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] L).toRingHom
  have hsurj : Function.Surjective ψ := aeval_ratioVec_surjective x c hc

  have hinj : Function.Injective Φ := by
    intro τ τ' h
    have e : (fun p ↦ τ (ratioVec x c p)) = fun p ↦ τ' (ratioVec x c p) := funext fun p ↦ by
      rw [← hRΦ, ← hRΦ, h]
    ext a
    obtain ⟨f, rfl⟩ := hsurj a
    show τ (aeval (ratioVec x c) f) = τ' (aeval (ratioVec x c) f)
    rw [hτ, hτ, e]

  have hΦ : Function.Surjective Φ := by
    refine Quot.ind fun z ↦ ?_
    obtain ⟨z, hz⟩ := z
    have hz0 := chart_ne_zero_of_mem_mcPts x c hc hz
    let g : {g : MvPolynomial (Coord n) ℚ →+* ℂ // RingHom.ker ψ ≤ RingHom.ker g} :=
      ⟨(aeval fun p ↦ z p / z ⟨p.1, c p.1⟩ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ).toRingHom,
        fun f hf ↦ by
          rw [RingHom.mem_ker] at hf ⊢
          refine aeval_ratio_eq_zero x c hc hz hz0 f ?_
          rw [← val_aeval_ratioVec]
          exact congrArg Subtype.val hf⟩
    have hτp : ∀ p, ψ.liftOfSurjective hsurj g (ratioVec x c p) =
        z p / z ⟨p.1, c p.1⟩ := fun p ↦ by
      have h := RingHom.liftOfSurjective_comp_apply ψ hsurj g (X p)
      simp only [ψ, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at h
      exact h
    set τ := ψ.liftOfSurjective hsurj g
    refine ⟨τ, (Quot.sound ⟨fun k ↦ σ τ (x k (c k)) / z ⟨k, c k⟩,
      fun k ↦ div_ne_zero ((map_ne_zero _).mpr (hc k)) (hz0 k), ?_⟩).symm⟩
    funext p
    have h1 : σ τ (x p.1 p.2) = σ τ (x p.1 p.2 / x p.1 (c p.1)) * σ τ (x p.1 (c p.1)) := by
      rw [← map_mul, div_mul_cancel₀ _ (hc p.1)]
    have h2 : σ τ (x p.1 p.2 / x p.1 (c p.1)) = z p / z ⟨p.1, c p.1⟩ :=
      (hσ τ (ratioVec x c p)).trans (hτp p)
    show σ τ (x p.1 p.2) = σ τ (x p.1 (c p.1)) / z ⟨p.1, c p.1⟩ * z p
    rw [h1, h2]
    ring
  rw [← Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hΦ⟩), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G OrbitChartMax

theorem OrbitCenterChart.proof : OrbitCenterChart.Statement := by
  classical
  intro ι _ _ _ n A x s hx hs V hV c hc v
  obtain ⟨hVmin, -⟩ := hV
  have : V.IsPrime := hVmin.1.1
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  obtain ⟨a, -, hsa, -⟩ := hs
  have hsa' : IsWeightedHomogeneous (coordDeg n) s a := (geoMultiHomog_iff s a).mp hsa

  have hVh : ∀ f ∈ V, ∀ b, weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
    have hJ : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x ⊔ Ideal.span {s}) := by
      intro f hf b
      obtain ⟨p, hp, t, ht, rfl⟩ := Submodule.mem_sup.mp hf
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hp b)
        (NumbersDVR.isMultiHomogIdeal_span_singleton (e := a) hsa' t ht b)
    exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hVmin

  have hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    refine hc k (hPV ?_)
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [h0]
  have hyc : ∀ k, genPt V ⟨k, c k⟩ ≠ 0 := fun k ↦ genPt_ne_zero V (hc k)

  have hVzero : ∀ f ∈ V, aeval (dehomCoords (genPt V) c) f = 0 := by
    intro f hf

    rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    exact (aeval_dehomCoords_of_homog (genPt V) c
      (weightedHomogeneousComponent_isWeightedHomogeneous b f)).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr (hVh f hf b)) _)
  have hker : ∀ F, chartEval x c F = 0 → aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F hF
    rw [chartEval_eq_zero_iff] at hF
    have hF' := (aeval_dehomCoords (flatCone x) c hxc F).symm.trans hF
    have hH := (mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hxc _)
    have hHV : homogenize c F ∈ V :=
      hPV (mem_orbitIdeal_of_aeval_eq_zero x (isWeightedHomogeneous_homogenize c F) hH)
    exact (aeval_dehomCoords (genPt V) c hyc F).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr hHV) _)
  have hmem : ∀ F, chartEval x c F ∈ chartPoint x c V ↔
      aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F
    constructor
    · intro hF
      obtain ⟨g, hg, hgF⟩ :=
        (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hF
      have h1 := hker (F - g) (by rw [map_sub, hgF, sub_self])
      rwa [map_sub, hVzero g hg, sub_zero] at h1
    · intro hF
      have hF' := (aeval_dehomCoords (genPt V) c hyc F).symm.trans hF
      have hH := (aeval_genPt_eq_zero_iff V _).mp
        ((mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hyc _))
      have e : chartEval x c (homogenize c F) = chartEval x c F :=
        map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F
      rw [← e]
      exact Ideal.mem_map_of_mem _ hH

  have hformV : ∀ G D, IsWeightedHomogeneous (coordDeg n) G D →
      (chartEval x c G ∈ chartPoint x c V ↔ G ∈ V) := fun G D hG ↦ by
    rw [hmem, aeval_dehomCoords_of_homog (genPt V) c hG, mul_eq_zero,
      or_iff_left (prod_inv_pow_ne_zero _ c hyc _), aeval_genPt_eq_zero_iff]

  have hhom : ∀ F, chartEval x c (homogenize c F) = chartEval x c F := fun F ↦
    map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F

  set M : ι → ℝ := fun k ↦ ⨆ i, v (coordVec x k i) with hMdef
  have hMle : ∀ k i, v (coordVec x k i) ≤ M k := fun k i ↦
    le_ciSup (Set.finite_range fun i ↦ v (coordVec x k i)).bddAbove i
  have hy0 : ∀ k, coordVec x k (c k) ≠ 0 := fun k h ↦ hxc k (congrArg Subtype.val h)
  have hvpos : ∀ k, 0 < v (coordVec x k (c k)) := fun k ↦ FinitePlace.pos_iff.mpr (hy0 k)
  let φ : MvPolynomial (Coord n) ℤ →ₐ[ℤ] coordField x :=
    aeval (dehomCoords (fun p : Coord n ↦ coordVec x p.1 p.2) c)
  have hincl : ∀ F, IntermediateField.inclusion (ratioField_le_coordField x)
      (chartEval x c F : ratioField x) = φ F := by
    intro F
    have h : (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.comp
        ((chartRing x c).val.toRingHom.comp (chartEval x c).toRingHom) =
        (φ : MvPolynomial (Coord n) ℤ →+* coordField x) :=
      MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun p ↦ by
        apply Subtype.ext
        simp [φ, chartEval, chartRatio, dehomCoords, coordVec, div_eq_inv_mul])
    exact DFunLike.congr_fun h F
  have hφG : ∀ G D, IsWeightedHomogeneous (coordDeg n) G D →
      φ G = evalCone (coordVec x) G * ∏ k, (coordVec x k (c k))⁻¹ ^ D k := fun G D hG ↦ by
    refine (aeval_dehomCoords_of_homog _ c hG).trans ?_
    rw [aeval_def, evalCone, Subsingleton.elim (algebraMap ℤ (coordField x)) (Int.castRingHom _)]

  have hle : (∀ k, v (coordVec x k (c k)) = M k) → ∀ F, v (φ F) ≤ 1 := fun hcM ↦
    finitePlace_aeval_le_one v _ fun p ↦ by
      simp only [dehomCoords, map_mul, map_inv₀]
      rw [inv_mul_le_one₀ (hvpos p.1), hcM]
      exact hMle p.1 p.2
  have hlt : (∀ k, v (coordVec x k (c k)) = M k) → ∀ G D,
      IsWeightedHomogeneous (coordDeg n) G D → (v (φ G) < 1 ↔ G ∈ orbitCenter x v) :=
    fun hcM G D hG ↦ by
      have hP : 0 < ∏ k, M k ^ D k :=
        Finset.prod_pos fun k _ ↦ pow_pos (hcM k ▸ hvpos k) _
      rw [OrbitCenterMemIff.proof ι n x hx v G D ((geoMultiHomog_iff G D).mpr hG), hφG G D hG,
        map_mul, map_prod]
      simp_rw [map_pow, map_inv₀, hcM, inv_pow]
      rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, div_lt_one hP]
  simp only [AbsCentredAt]
  constructor
  · intro h
    have hcM : ∀ k, v (coordVec x k (c k)) = M k := fun k ↦
      le_antisymm (hMle k (c k)) (not_lt.mp fun hlt' ↦ hc k (h ▸ X_mem_orbitCenter x v k (c k) hlt'))
    refine ⟨fun u ↦ ?_, fun u ↦ ?_⟩
    · obtain ⟨F, rfl⟩ := chartEval_surjective x c u
      rw [hincl]
      exact hle hcM F
    · obtain ⟨F, rfl⟩ := chartEval_surjective x c u
      rw [← hhom F, hincl, hlt hcM _ _ (isWeightedHomogeneous_homogenize c F), h,
        hformV _ _ (isWeightedHomogeneous_homogenize c F)]
  · rintro ⟨h1, h2⟩
    have hcM : ∀ k, v (coordVec x k (c k)) = M k := fun k ↦ by
      refine le_antisymm (hMle k (c k)) (ciSup_le fun i ↦ ?_)
      have := h1 (chartEval x c (X ⟨k, i⟩))
      rw [hincl] at this
      simpa [φ, dehomCoords, inv_mul_le_one₀ (hvpos k)] using this
    have hiff : ∀ G D, IsWeightedHomogeneous (coordDeg n) G D → (G ∈ orbitCenter x v ↔ G ∈ V) :=
      fun G D hG ↦ by
        rw [← hlt hcM G D hG, ← hformV G D hG, ← h2, hincl]
    refine le_antisymm (Ideal.span_le.mpr fun F ⟨d, hFd, hFlt⟩ ↦ ?_) fun f hf ↦ ?_
    · exact (hiff F d ((geoMultiHomog_iff F d).mp hFd)).mp (Ideal.subset_span ⟨d, hFd, hFlt⟩)
    · rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ ↦ (hiff _ b
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).mpr (hVh f hf b)

end GroundTheory.Heights₂.Heights
end
