module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle002
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
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.RamificationInertia.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitLocalSum.proof (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement) :
    OrbitLocalSum.Statement := by
  intro ι _ _ _ n A x s hx hs V hV
  obtain ⟨hVmin, hVrel⟩ := id hV
  choose c hc using hVrel
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hxc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hc k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  obtain ⟨hft, hfr⟩ := hR ι n x c hxc
  have := hM ι n A x s hx hs V hV c hc
  obtain ⟨hf0, hterm⟩ := hT ι n A x s hs c hxc
  let _ : Algebra (ratioField x) (coordField x) :=
    (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.toAlgebra
  have hset : {v : FinitePlace (coordField x) | orbitCenter x v = V} =
      {v : FinitePlace (coordField x) | AbsCentredAt (chartRing x c) (chartPoint x c V)
        fun u ↦ v (algebraMap (ratioField x) (coordField x) u)} :=
    Set.ext fun v ↦ hC ι n A x s hx hs V hV c hc v
  have hsum : ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
        -Real.log (v (algebraMap (ratioField x) (coordField x) (chartEval x c s))) :=
    finsum_mem_congr rfl fun v hv ↦ hterm v fun k hk ↦ hc k (by
      rw [← (show orbitCenter x v = V from hv)]
      exact hk)
  have hdeg := (letI : Module.Free (ratioField x) (coordField x) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (ratioField x) (coordField x))
  rw [hsum, hset, hS (ratioField x) (coordField x) (chartRing x c) (chartPoint x c V),
    hU ι n A x s hx hs V hV c hc, hF ι n A x s hx hs V hV c hc,
    ← hP (ratioField x) (chartRing x c) hft hfr (chartPoint x c V) (chartEval x c s) hf0, ← hdeg]
  push_cast
  ring_nf
  rfl

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

theorem mem_closure_chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (z : ratioField x) :
    z ∈ Subfield.closure (Set.range (chartRatio x c)) := by
  set T := Subfield.closure (Set.range (chartRatio x c))
  let T' : Subfield (AlgebraicClosure ℚ) := T.map (ratioField x).val.toRingHom
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    T'.toIntermediateField fun q ↦ by
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem T' q
  have hE : ratioField x ≤ E := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    refine ⟨chartRatio x c ⟨k, i⟩ / chartRatio x c ⟨k, j⟩,
      div_mem (Subfield.subset_closure (Set.mem_range_self _))
        (Subfield.subset_closure (Set.mem_range_self _)), ?_⟩
    simp [chartRatio, div_div_div_cancel_right₀ (hc k)]
  obtain ⟨t, ht, hzt⟩ := hE z.2
  have : t = z := Subtype.ext hzt
  exact this ▸ ht

theorem OrbitChartRing.proof : OrbitChartRing.Statement := by
  intro ι _ _ n x c hc
  refine ⟨(Subalgebra.fg_iff_finiteType _).mp
    ⟨(Set.finite_range (chartRatio x c)).toFinset, by simp [chartRing]⟩, ?_⟩
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · refine isUnit_iff_ne_zero.mpr fun h ↦ nonZeroDivisors.coe_ne_zero y ?_
    exact Subtype.ext h
  · have hsub : Subring.closure (Set.range (chartRatio x c)) ≤ (chartRing x c).toSubring :=
      Subring.closure_le.mpr fun _ hp ↦ Algebra.subset_adjoin hp
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subfield.mem_closure_iff.mp (mem_closure_chartRatio x c hc z)
    by_cases hb0 : b = 0
    · refine ⟨(0, 1), ?_⟩
      rw [hb0, div_zero] at hab
      simp [← hab]
    · have hb' : (⟨b, hsub hb⟩ : chartRing x c) ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
      refine ⟨(⟨a, hsub ha⟩, ⟨⟨b, hsub hb⟩, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      change z * b = a
      rw [← hab, div_mul_cancel₀ _ hb0]
  · rw [Subtype.val_injective h]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval₂_mul_block_of_isMultiHomog {R : Type*} [CommRing R] (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (g : ℤ →+* R) (y : Coord n → R)
    (t : ι → R) :
    eval₂ g (fun p ↦ y p * t p.1) s = eval₂ g y s * ∏ k, t k ^ a k := by
  classical
  simp only [eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  change ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
  rw [Finset.prod_pow_eq_pow_sum, hs m hm k]


omit [Fintype ι] in
theorem coe_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  have h : (((ratioField x).val.restrictScalars ℤ).comp (chartRing x c).val).comp (chartEval x c) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) :=
    algHom_ext fun p ↦ by simp [chartEval, chartRatio]
  exact DFunLike.congr_fun h f

theorem evalCone_ne_zero_of_notMem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hW : s ∉ orbitIdeal x) : evalCone x s ≠ 0 := by
  intro h0
  apply hW
  have hC : ∀ g : ℤ →+* MvPolynomial ι (AlgebraicClosure ℚ),
      eval₂ g (fun p ↦ C (flatCone x p)) s = C (evalCone x s) := fun g ↦ by
    rw [evalCone, eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_def,
    eval₂_mul_block_of_isMultiHomog s a hs _ (fun p ↦ C (flatCone x p)) X, hC, h0, map_zero,
    zero_mul]


omit [Fintype ι] in
theorem coe_evalCone_coordVec (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ) :
    ((evalCone (coordVec x) s : coordField x) : AlgebraicClosure ℚ) = evalCone x s := by
  have h := eval₂_comp_left (algebraMap (coordField x) (AlgebraicClosure ℚ)) (Int.castRingHom _)
    (fun v ↦ coordVec x v.1 v.2) s
  rw [RingHom.ext_int ((algebraMap (coordField x) (AlgebraicClosure ℚ)).comp (Int.castRingHom _))
    (Int.castRingHom _)] at h
  exact h

theorem OrbitChartTerm.proof : OrbitChartTerm.Statement := by
  intro ι _ _ n A x s hs c hxc
  obtain ⟨a, ha, hhom, hW⟩ := hs
  have hfac : evalCone x s =
      ((chartEval x c s : ratioField x) : AlgebraicClosure ℚ) * ∏ k, x k (c k) ^ a k := by
    rw [coe_chartEval, aeval_def, ← eval₂_mul_block_of_isMultiHomog s a hhom _
      (fun p ↦ x p.1 p.2 / x p.1 (c p.1)) (fun k ↦ x k (c k)), evalCone]
    congr 1
    funext p
    exact (div_mul_cancel₀ _ (hxc p.1)).symm
  have hx0 : evalCone x s ≠ 0 := evalCone_ne_zero_of_notMem_orbitIdeal x s a hhom hW
  have hf0 : chartEval x c s ≠ 0 := by
    intro h
    rw [h] at hfac
    simp at hfac
    exact hx0 hfac
  refine ⟨hf0, fun v hv ↦ ?_⟩
  have hsup : ∀ k, ⨆ i, v (coordVec x k i) = v (coordVec x k (c k)) := fun k ↦
    le_antisymm (not_lt.mp fun h ↦ hv k (X_mem_orbitCenter x v k (c k) h))
      (le_ciSup (f := fun i ↦ v (coordVec x k i)) (Finite.bddAbove_range _) (c k))
  have hK : evalCone (coordVec x) s =
      IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s) *
        ∏ k, coordVec x k (c k) ^ a k := by
    apply Subtype.ext
    rw [coe_evalCone_coordVec, hfac, MulMemClass.coe_mul, IntermediateField.coe_prod,
      IntermediateField.coe_inclusion]
    simp only [SubmonoidClass.coe_pow]
    rfl
  have hc0 : ∀ k, 0 < v (coordVec x k (c k)) := fun k ↦
    FinitePlace.pos_iff.mpr fun h ↦ hxc k (congrArg Subtype.val h)
  have hv0 : 0 < v (IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s)) :=
    FinitePlace.pos_iff.mpr fun h ↦ hf0 (Subtype.ext
      ((IntermediateField.inclusion (ratioField_le_coordField x)).injective
        (h.trans (map_zero _).symm)))
  have ha' : ∀ k, (A.deg k : ℝ) = (a k : ℝ) := fun k ↦ by
    have h := ha k
    rw [HermLine.toGeo_a] at h
    exact_mod_cast h
  rw [hK, map_mul, map_prod, Real.log_mul hv0.ne' (Finset.prod_pos fun k _ ↦ (by
      rw [map_pow]; exact pow_pos (hc0 k) _)).ne',
    Real.log_prod fun k _ ↦ (by rw [map_pow]; exact (pow_pos (hc0 k) _).ne'), finiteTerm]
  simp only [map_pow, Real.log_pow, hsup, ha']
  ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LocalLengthPlaces.proof (hC : LocalQuotCard.Statement) (hF : CentredPlacesFinite.Statement)
    (hE : LocalQuotCentred.Statement) (hP : PlacesRingQuot.Statement) :
    LocalLengthPlaces.Statement := by
  intro L _ _ O hft hfr m _ f hf
  have hfS : (f : L) ∈ placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} :=
    fun w hw ↦ hw.1 f
  have hg : (⟨f, hfS⟩ : placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}) ≠ 0 :=
    fun h ↦ hf (Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [← Real.log_pow, ← Nat.cast_pow, ← hC L O hft hfr m f hf, hE L O hft hfr m f hf ⟨f, hfS⟩ rfl]
  exact hP L _ (hF L O hft hfr m) ⟨f, hfS⟩ hg

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsDedekindDomain Ideal

namespace PlaceCentredSum

variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

noncomputable def below (v : FinitePlace K) : HeightOneSpectrum (𝓞 L) where
  asIdeal := v.maximalIdeal.asIdeal.under (𝓞 L)
  isPrime := inferInstance
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    exact comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

instance (v : FinitePlace K) : v.maximalIdeal.asIdeal.LiesOver (below (L := L) v).asIdeal := ⟨rfl⟩

noncomputable def deg (L : Type) [Field L] [NumberField L] [Algebra L K] (v : FinitePlace K) : ℕ :=
  v.maximalIdeal.asIdeal.ramificationIdx (𝓞 L) * v.maximalIdeal.asIdeal.inertiaDeg (𝓞 L)

lemma toNNReal_pow {b c : NNReal} (hc : c ≠ 0) (hb : b ≠ 0) {f : ℕ} (hf : f ≠ 0) (h : c = b ^ f)
    (z : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal hc z = WithZeroMulInt.toNNReal hb z ^ f := by
  subst h
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hf]
  · rw [WithZeroMulInt.toNNReal_neg_apply _ hz, WithZeroMulInt.toNNReal_neg_apply _ hz,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem apply_algebraMap (v : FinitePlace K) (x : L) :
    v (algebraMap L K x) = FinitePlace.mk (below v) x ^ deg L v := by
  have hQ : (below (L := L) v).asIdeal ≠ ⊥ := (below v).ne_bot
  have hf : (below (L := L) v).asIdeal.inertiaDeg' v.maximalIdeal.asIdeal ≠ 0 :=
    (inertiaDeg'_pos' _ _).ne'
  have hN := absNorm_eq_pow_inertiaDeg'_of_liesOver v.maximalIdeal.asIdeal (below (L := L) v).asIdeal
    inferInstance hQ
  rw [← FinitePlace.norm_embedding_eq v, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    FinitePlace.norm_embedding', ← HeightOneSpectrum.valuation_liesOver K (below (L := L) v) v.maximalIdeal, map_pow,
    toNNReal_pow _ (NumberField.HeightOneSpectrum.absNorm_ne_zero (below (L := L) v)) hf (by rw [hN]; push_cast; rfl), deg,
    inertiaDeg'_eq_inertiaDeg, ← pow_mul]
  push_cast
  rw [mul_comm]

lemma deg_ne_zero (v : FinitePlace K) : deg L v ≠ 0 := by
  refine mul_ne_zero ?_ (inertiaDeg_pos _ _).ne'
  rw [← ramificationIdx'_eq_ramificationIdx _ _ (below (L := L) v).ne_bot]
  exact IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ (below v).ne_bot

theorem centred_iff (O : Subalgebra ℤ L) (m : Ideal O) (v : FinitePlace K) :
    AbsCentredAt O m (fun u ↦ v (algebraMap L K u)) ↔
      AbsCentredAt O m (fun u ↦ FinitePlace.mk (below v) u) := by
  have h1 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v ≤ 1 ↔ a ≤ 1) := fun a ha ↦
    pow_le_one_iff_of_nonneg ha (deg_ne_zero v)
  have h2 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v < 1 ↔ a < 1) := fun a ha ↦
    pow_lt_one_iff_of_nonneg ha (deg_ne_zero v)
  unfold AbsCentredAt
  simp only [apply_algebraMap]
  exact and_congr (forall_congr' fun u ↦ h1 _ (apply_nonneg _ _))
    (forall_congr' fun u ↦ by rw [h2 _ (apply_nonneg _ _)])

theorem neg_log_apply (v : FinitePlace K) (t : L) :
    -Real.log (v (algebraMap L K t)) = deg L v * -Real.log (FinitePlace.mk (below v) t) := by
  rw [apply_algebraMap, Real.log_pow]
  ring

noncomputable def fibreEquiv (Q : HeightOneSpectrum (𝓞 L)) :
    {v : FinitePlace K // below v = Q} ≃ Q.asIdeal.primesOver (𝓞 K) where
  toFun v := ⟨v.1.maximalIdeal.asIdeal, inferInstance, ⟨(congrArg HeightOneSpectrum.asIdeal v.2).symm⟩⟩
  invFun P := ⟨FinitePlace.mk ⟨P.1, P.2.1, ne_bot_of_liesOver_of_ne_bot Q.ne_bot P.1⟩, by
    ext1
    simp only [below, FinitePlace.maximalIdeal_mk]
    exact P.2.2.over.symm⟩
  left_inv v := Subtype.ext (FinitePlace.mk_maximalIdeal v.1)
  right_inv P := Subtype.ext (by simp only [FinitePlace.maximalIdeal_mk])

noncomputable instance (Q : HeightOneSpectrum (𝓞 L)) : Fintype {v : FinitePlace K // below v = Q} :=
  Fintype.ofEquiv _ (fibreEquiv Q).symm

theorem sum_fibre (Q : HeightOneSpectrum (𝓞 L)) :
    ∑ v : {v : FinitePlace K // below v = Q}, deg L v.1 = Module.finrank L K := by
  rw [← (fibreEquiv Q).symm.sum_comp, IsFractionRing.finrank_eq (𝓞 L) L (𝓞 K) K,
    ← sum_ramification_inertia_eq_finrank Q.asIdeal (𝓞 K)]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  simp only [deg, fibreEquiv, Equiv.coe_fn_symm_mk, FinitePlace.maximalIdeal_mk]

lemma finsum_fibre {α β : Type*} (π : α → β) [∀ b, Fintype {a // π a = b}] (n : α → ℕ) (N : ℕ)
    (g : β → ℝ) (hg : g.support.Finite) (hsum : ∀ b, ∑ a : {a // π a = b}, n a.1 = N) :
    ∑ᶠ a, (n a : ℝ) * g (π a) = N * ∑ᶠ b, g b := by
  classical
  have hfin : ∀ b, (π ⁻¹' {b}).Finite := fun b ↦
    Set.finite_coe_iff.mp (Finite.of_fintype {a // π a = b})
  have hA : (π ⁻¹' g.support).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact hg.biUnion fun b _ ↦ hfin b
  rw [finsum_eq_sum_of_support_subset _ (s := hA.toFinset) ?_,
    finsum_eq_sum_of_support_subset _ (s := hg.toFinset) (by simp), Finset.mul_sum]
  · rw [← Finset.sum_fiberwise_of_maps_to (s := hA.toFinset) (t := hg.toFinset) (g := π)
      (fun a ha ↦ by simpa using ha)]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [Finset.sum_subtype (p := fun a ↦ π a = b) _ (fun a ↦ by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact ⟨And.right, fun h ↦ ⟨by rw [h]; simpa using hb, h⟩⟩)]
    have : ∀ a : {a // π a = b}, (n a.1 : ℝ) * g (π a.1) = n a.1 * g b := fun a ↦ by rw [a.2]
    rw [Fintype.sum_congr _ _ this, ← Finset.sum_mul, ← Nat.cast_sum, hsum]
  · intro a ha
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Function.mem_support]
    exact right_ne_zero_of_mul ha

theorem proof : PlaceCentredSum.Statement := by
  intro L K _ _ _ _ _ O m t
  classical
  let g : HeightOneSpectrum (𝓞 L) → ℝ := fun Q ↦
    if AbsCentredAt O m (fun u ↦ FinitePlace.mk Q u) then -Real.log (FinitePlace.mk Q t) else 0
  have hL : ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun u ↦ w u}, -Real.log (w t) =
      ∑ᶠ Q, g Q := by
    rw [finsum_mem_def, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun Q ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, FinitePlace.equivHeightOneSpectrum,
      Equiv.coe_fn_symm_mk]
    exact if_congr Iff.rfl rfl rfl
  have hK : ∑ᶠ v ∈ {v : FinitePlace K | AbsCentredAt O m fun u ↦ v (algebraMap L K u)},
      -Real.log (v (algebraMap L K t)) = ∑ᶠ v : FinitePlace K, (deg L v : ℝ) * g (below v) := by
    rw [finsum_mem_def]
    refine finsum_congr fun v ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, centred_iff, neg_log_apply]
    split_ifs <;> simp
  have hg : g.support.Finite := by
    rcases eq_or_ne t 0 with rfl | ht
    · refine Set.finite_empty.subset fun Q hQ ↦ ?_
      simp [g] at hQ
    · refine ((FinitePlace.hasFiniteMulSupport ht).preimage
        (fun a _ b _ h ↦ FinitePlace.mk_eq_iff.mp h)).subset fun Q hQ ↦ ?_
      simp only [Function.mem_support, g] at hQ
      split_ifs at hQ
      · simp only [Set.mem_preimage, Function.mem_mulSupport]
        intro h1
        exact hQ (by simp [h1])
      · exact absurd rfl hQ
  rw [hK, hL]
  exact finsum_fibre below (deg L) _ g hg sum_fibre

end PlaceCentredSum

end GroundTheory.Heights₂.Heights
end
