module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSuppLemmas
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle006
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

abbrev chartOneIdeal (c : (k : ι) → Fin (n k + 1)) : Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1)

theorem weightedHomogeneousComponent_mem_of_mem_divSupp (x : Cone n (AlgebraicClosure ℚ))
    {s : MvPolynomial (Coord n) ℤ} {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : V ∈ Geo.divSupp (orbitIdeal x) s)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ V) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
  have hP : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (R := ℤ) (orbitIdeal x) :=
    fun g hg b ↦ OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hg b
  have hJ := NumbersDVR.SupSpanMultiHomog.proof ℤ ι (blockIdx n) (orbitIdeal x) s a hP hs
  exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hV.1 f hf b

variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]

def classFrac : MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  (IsScalarTower.toAlgHom ℤ (MvPolynomial (Coord n) ℤ ⧸ V) _).comp (Ideal.Quotient.mkₐ ℤ V)

def dehomFrac (c : (k : ι) → Fin (n k + 1)) :
    MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  aeval fun p ↦ classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩)

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in
theorem classFrac_eq_zero_iff (f : MvPolynomial (Coord n) ℤ) : classFrac V f = 0 ↔ f ∈ V := by
  change algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V)) (Ideal.Quotient.mk V f) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

variable {V}

theorem dehomFrac_of_isWeightedHomogeneous (c : (k : ι) → Fin (n k + 1))
    (G : MvPolynomial (Coord n) ℤ) (d : ι → ℕ) (hG : IsWeightedHomogeneous (coordDeg n) G d) :
    dehomFrac V c G = classFrac V G * ∏ k, (classFrac V (X ⟨k, c k⟩) ^ d k)⁻¹ := by
  have e : (aeval fun p ↦ classFrac V (X p)) = classFrac V := MvPolynomial.algHom_ext fun p ↦ aeval_X _ _
  rw [dehomFrac, aeval_div_chart (fun p ↦ classFrac V (X p)) c G d hG, DFunLike.congr_fun e G]

theorem ker_dehomFrac
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    RingHom.ker (dehomFrac V c) = V ⊔ chartOneIdeal c := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hle : V ⊔ chartOneIdeal c ≤ RingHom.ker (dehomFrac V c) := by
    refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)

    · rw [RingHom.mem_ker, ← sum_weightedHomogeneousComponent (w := coordDeg n) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      rw [dehomFrac_of_isWeightedHomogeneous c _ b
          (weightedHomogeneousComponent_isWeightedHomogeneous b f),
        (classFrac_eq_zero_iff V _).mpr (hVh f hf b), zero_mul]
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehomFrac, aeval_X]
      exact sub_eq_zero.mpr (div_self (hz k))
  refine le_antisymm (fun f hf ↦ ?_) hle
  rw [RingHom.mem_ker] at hf
  have hχ : ∀ k, Ideal.Quotient.mk (V ⊔ chartOneIdeal c) (X ⟨k, c k⟩) = 1 := fun k ↦ by
    rw [← map_one (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨D, G, hG, hGf⟩ := exists_isWeightedHomogeneous_eq_of_chart
    (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)) c hχ f
  have hd : G - f ∈ V ⊔ chartOneIdeal c := Ideal.Quotient.eq.mp hGf
  have h0 : dehomFrac V c G = 0 := by
    have := hle hd
    rwa [RingHom.mem_ker, map_sub, hf, sub_zero] at this
  rw [dehomFrac_of_isWeightedHomogeneous c G D hG, mul_eq_zero] at h0
  have hGV : G ∈ V := by
    refine (classFrac_eq_zero_iff V G).mp (h0.resolve_right ?_)
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ inv_ne_zero (pow_ne_zero _ (hz k))
  simpa using sub_mem (Ideal.mem_sup_left hGV) hd

theorem comap_sup_chartOneIdeal
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (V ⊔ chartOneIdeal c).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) =
      V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := by
  refine le_antisymm (fun a ha ↦ ?_) (Ideal.comap_mono le_sup_left)
  rw [Ideal.mem_comap, ← ker_dehomFrac hVh hc, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, ← classFrac_eq_zero_iff V]
  rw [← ha]
  exact ((classFrac V).commutes a).trans ((dehomFrac V c).commutes a).symm

def quotEquivRange
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (MvPolynomial (Coord n) ℤ ⧸ (V ⊔ chartOneIdeal c)) ≃+* (dehomFrac V c).range :=
  (Ideal.quotEquivOfEq (ker_dehomFrac hVh hc).symm).trans
    (Ideal.quotientKerEquivRange (dehomFrac V c)).toRingEquiv


omit [Fintype ι] [DecidableEq ι] in
theorem range_dehomFrac_le {c c' : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hF : IsField (dehomFrac V c).range) : (dehomFrac V c').range ≤ (dehomFrac V c).range := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hz' : ∀ k, classFrac V (X ⟨k, c' k⟩) ≠ 0 :=
    fun k h ↦ hc' k ((classFrac_eq_zero_iff V _).mp h)
  rw [dehomFrac, ← Algebra.adjoin_range_eq_range_aeval]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, rfl⟩
  have hmem : ∀ q : Coord n, classFrac V (X q) / classFrac V (X ⟨q.1, c q.1⟩) ∈ (dehomFrac V c).range :=
    fun q ↦ (AlgHom.mem_range _).mpr ⟨X q, by rw [dehomFrac, aeval_X]⟩
  let u : (dehomFrac V c).range := ⟨_, hmem ⟨p.1, c' p.1⟩⟩
  have hu : u ≠ 0 := fun h ↦ div_ne_zero (hz' p.1) (hz p.1) (congrArg Subtype.val h)
  obtain ⟨w, hw⟩ := hF.mul_inv_cancel hu
  have hinv : (u : FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))⁻¹ ∈ (dehomFrac V c).range := by
    rw [← eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)]
    exact w.2
  have e : classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) =
      classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩) * (u : FractionRing _)⁻¹ := by
    change _ = _ * (classFrac V (X ⟨p.1, c' p.1⟩) / classFrac V (X ⟨p.1, c p.1⟩))⁻¹
    field_simp [hz p.1, hz' p.1]
  change classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) ∈ (dehomFrac V c).range
  rw [e]
  exact mul_mem (hmem p) hinv

theorem OrbitChartDehom.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement) :
    OrbitChartDehom.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c c' hc hc'
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have : V.IsPrime := hV.1.1.1
  obtain ⟨a, -, hsa, -⟩ := id hs
  have hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V :=
    fun f hf b ↦ weightedHomogeneousComponent_mem_of_mem_divSupp x ((geoMultiHomog_iff s a).mp hsa)
      hV hf b
  refine ⟨comap_sup_chartOneIdeal hVh hc, ?_⟩
  have hfield : ∀ d : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, d k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → IsField (dehomFrac V d).range := by
    intro d hd
    have hxd : ∀ k, x k (d k) ≠ 0 := by
      intro k h0
      apply hd k
      apply hPV
      rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
      simp [flatCone, h0]
    obtain ⟨eQ⟩ := hQ ι n x d hxd V hPV
    have hmax := hM ι n A x s hx hs V hV d hd
    exact MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
      (eQ.trans (quotEquivRange hVh hd)).symm.toMulEquiv
  have hr : (dehomFrac V c).range = (dehomFrac V c').range :=
    le_antisymm (range_dehomFrac_le hc' hc (hfield c' hc')) (range_dehomFrac_le hc hc' (hfield c hc))
  exact ⟨(quotEquivRange hVh hc).trans
    ((Subalgebra.equivOfEq _ _ hr).toRingEquiv.trans (quotEquivRange hVh hc').symm)⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem OrbitArchSum.of_conjSum (hB : OrbitConjSum.Statement) : OrbitArchSum.Statement := by
  intro ι _ _ _ n A x s hx hs
  obtain ⟨a, ha, hsa, -⟩ := hs
  have hinv : ∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) →
      Geo.logNorm A.toGeo s (fun p ↦ c p.1 * z p) = Geo.logNorm A.toGeo s z := by
    intro c z hc _
    rw [Geo.logNorm, Geo.logNorm, A.toGeo.smul c z hc, eval_smul_of_isMultiHomog s a hsa c z,
      norm_mul, norm_prod]
    simp only [ha, zpow_natCast, norm_pow]
    rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦
      pow_ne_zero _ (norm_ne_zero_iff.mpr (hc k)))]
  have hfin := (Nat.card_pos_iff.mp (OrbitDegree.full ι n x hx)).2
  have e0 : (fun j z ↦ Real.log (((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j).h z)) =
      (Fin.elim0 : Fin 0 → (Coord n → ℂ) → ℝ) := funext fun j ↦ j.elim0
  have hB' := hB ι n x _ hx hinv
  rw [Geo.arInt, e0, PtsIntegralPoints.homogProof ι (blockIdx n) _ _
    (OrbitCurve.isMultiHomogIdeal_orbitIdeal x) hfin hinv]
  have hterm : ∀ σ : coordField x →+* ℂ,
      Geo.logNorm A.toGeo s (fun p ↦ σ (coordVec x p.1 p.2)) =
        Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
          A.metric (fun k i ↦ σ (coordVec x k i))) := by
    intro σ
    rw [Geo.logNorm, ← eval_map_flatCone]
    rw [A.toGeo_h_of_blockNonzero (w := fun p ↦ σ (coordVec x p.1 p.2)) (blockNonzero_sigma hx σ)]
    rfl
  simp only [hterm] at hB'
  have hK : (0 : ℝ) < Module.finrank ℚ (coordField x) := Nat.cast_pos.mpr Module.finrank_pos
  rw [div_mul_eq_mul_div, hB', mul_div_cancel_left₀ _ hK.ne']

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def chartHomogQ (c : (k : ι) → Fin (n k + 1)) (f : MvPolynomial (Coord n) ℚ)
    [Fintype ι] : MvPolynomial (Coord n) ℚ :=
  ∑ m ∈ f.support, C (AddMonoidAlgebra.coeff f m) * ∏ p : Coord n, (X p ^ m p * X ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p))

theorem le_totalDegree_of_mem_support {f : MvPolynomial (Coord n) ℚ} {m : Coord n →₀ ℕ}
    (hm : m ∈ f.support) (p : Coord n) : m p ≤ f.totalDegree :=
  (monomial_le_degreeOf p hm).trans (degreeOf_le_totalDegree f p)

variable [Fintype ι]

theorem aeval_chartHomogQ {S : Type*} [CommRing S] [Algebra ℚ S] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → S) :
    aeval y (chartHomogQ c f) = ∑ m ∈ f.support, algebraMap ℚ S (AddMonoidAlgebra.coeff f m) *
      ∏ p : Coord n, (y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) := by

  simp [chartHomogQ, map_sum, map_prod]

theorem aeval_chartHomogQ_field {K : Type*} [Field K] [Algebra ℚ K] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → K) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    aeval y (chartHomogQ c f) = (∏ p : Coord n, y ⟨p.1, c p.1⟩ ^ f.totalDegree) *
      aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) f := by
  rw [aeval_chartHomogQ, aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n, y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p) =
      y ⟨p.1, c p.1⟩ ^ f.totalDegree * (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    have hyp := hy p.1
    rw [he, Nat.add_sub_cancel_left, pow_add, div_pow]
    field_simp
  simp_rw [h, Finset.prod_mul_distrib]
  ring

theorem coneMapQ_chartHomogQ (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    OrbitCurve.coneMapQ x (chartHomogQ c f) =
      C (aeval (flatCone x) (chartHomogQ c f)) * ∏ p : Coord n, X p.1 ^ f.totalDegree := by

  rw [OrbitCurve.coneMapQ, aeval_chartHomogQ, aeval_chartHomogQ, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n,
      (C (flatCone x p) * X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m p *
        (C (flatCone x ⟨p.1, c p.1⟩) * X p.1) ^ (f.totalDegree - m p) =
      C (flatCone x p ^ m p * flatCone x ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) *
        X p.1 ^ f.totalDegree := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    rw [he, Nat.add_sub_cancel_left]
    simp only [mul_pow, map_mul, map_pow, pow_add]
    ring
  simp only [h, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.algebraMap_apply]
  ring

theorem aeval_ratio_eq_zero (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ} (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x))
    (hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0) (f : MvPolynomial (Coord n) ℚ)
    (hf : aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) f = 0 := by
  have hx : aeval (flatCone x) (chartHomogQ c f) = 0 := by
    rw [aeval_chartHomogQ_field c f (flatCone x) hc]
    exact mul_eq_zero_of_right _ hf
  have hker : chartHomogQ c f ∈ RingHom.ker (OrbitCurve.coneMapQ x) := by
    rw [RingHom.mem_ker, coneMapQ_chartHomogQ, hx, map_zero, zero_mul]
  classical
  rw [OrbitCurve.ker_coneMapQ] at hker
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤
      RingHom.ker (aeval z : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def,
      algebraMap_int_eq, ← eval_map]
    exact hz.2 g hg
  have h := hle hker
  rw [RingHom.mem_ker, aeval_chartHomogQ_field c f z hz0] at h
  exact (mul_eq_zero.mp h).resolve_left
    (Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _ (hz0 p.1))

variable [DecidableEq ι]

theorem chart_ne_zero_of_mem_mcPts (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hz.1 k
  obtain ⟨g, hg0, hg⟩ := exists_int_relation (flatCone x ⟨k, i⟩ / flatCone x ⟨k, c k⟩)
  have h := hz.2 _ (homogForm_mem_orbitIdeal x g ⟨k, i⟩ ⟨k, c k⟩ rfl (hc k) hg)
  rw [eval_homogForm, h0, homog_sum_zero] at h
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg0))
    (pow_ne_zero _ hi) h

end

end GroundTheory.Heights₂.Heights
end
