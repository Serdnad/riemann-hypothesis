module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Algebra.Algebra.ZMod
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsLocalRing

theorem LocalQuotCard.proof : LocalQuotCard.Statement := by
  intro L _ _ O hft _ m _ f hf
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing ℤ O
  have hO : Ring.KrullDimLE 1 O := Ring.KrullDimLE.mk₁' fun q hq0 hq ↦
    SubringPrimeMaximal.proof L O q hq hq0
  let R := Localization.AtPrime m
  have : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m R]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.mp hO)
  have hf' : algebraMap O R f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective R m.primeCompl_le_nonZeroDivisors (by simpa using h)
  have hspan : Ideal.span {algebraMap O R f} = LinearMap.range (LinearMap.lsmul R R (algebraMap O R f)) := by
    ext z
    simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]
  have hfin : Module.length R (R ⧸ Ideal.span {algebraMap O R f}) ≠ ⊤ := by
    rw [hspan]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top R hf'
  unfold localQuotLength
  rw [Inter.card_eq_card_residueField_pow_length _ hfin]
  congr 1
  exact Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m R).toEquiv.symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  refine isJacobsonRing_iff_prime_eq.mpr fun P hP ↦ ?_
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun a ha ↦ ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at ha
    have h1 := Int.isUnit_iff.mp (ha 1)
    have h2 := Int.isUnit_iff.mp (ha (-1))
    rw [Ideal.mem_bot]
    omega
  · have := hP.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem natCard_eq_pow_length_of_finiteType (F : Type) [Field F] [Algebra.FiniteType ℤ F]
    (q : ℕ) [CharP F q] :
    q.Prime ∧ Nat.card F = q ^ (Module.length ℤ F).toNat := by
  have := int_isJacobsonRing
  have : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  have hq : q ≠ 0 := by
    rintro rfl
    have : CharZero F := CharP.charP_to_charZero F
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (fun a b h ↦ by simpa using h) (Field.toIsField F))
  have hqp : q.Prime := (CharP.char_is_prime_or_zero F q).resolve_right hq
  have : Fact q.Prime := ⟨hqp⟩
  let : Algebra (ZMod q) F := ZMod.algebra F q
  have : Module.Finite (ZMod q) F := Module.Finite.of_restrictScalars_finite ℤ (ZMod q) F
  have : Finite F := Module.finite_of_finite (ZMod q)
  have : Fintype F := Fintype.ofFinite F
  refine ⟨hqp, ?_⟩
  rw [Module.length_eq_of_surjective (S := ℤ) (R := ZMod q) (M := F) (ZMod.intCast_surjective),
    Module.length_eq_finrank, ENat.toNat_natCast, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]

theorem OrbitChartResidue.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement)
    (hD : OrbitChartDehom.Statement) : OrbitChartResidue.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have hrel : Geo.IsRelevant V := hV.2
  have hxc : ∀ c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → ∀ k, x k (c' k) ≠ 0 := by
    intro c' h k h0
    apply h k
    apply hPV
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h0]
  set i : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) ∉ V := fun k ↦ (hrel k).choose_spec
  obtain ⟨eQ⟩ := hQ ι n x c (hxc c hc) V hPV
  obtain ⟨hchar, ⟨eD⟩⟩ := hD ι n A x s hx hs V hV i c hi hc
  set J := V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) - 1)
  let e : (chartRing x c ⧸ chartPoint x c V) ≃+* (MvPolynomial (Coord n) ℤ ⧸ J) := eQ.trans eD.symm
  have := hM ι n A x s hx hs V hV c hc
  have hfield : IsField (MvPolynomial (Coord n) ℤ ⧸ J) :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      e.symm.toMulEquiv
  have : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  let : Field (MvPolynomial (Coord n) ℤ ⧸ J) := Ideal.Quotient.field J
  have hft : Algebra.FiniteType ℤ (MvPolynomial (Coord n) ℤ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ J)
      (Ideal.Quotient.mkₐ_surjective ℤ J)
  have : CharP (MvPolynomial (Coord n) ℤ ⧸ J) (Geo.charOf V) := by
    constructor
    intro a
    have hJC : ∀ b : ℤ, ((b : MvPolynomial (Coord n) ℤ ⧸ J) = 0 ↔ b ∈ V.comap (C : ℤ →+* _)) := by
      intro b
      rw [(map_intCast (Ideal.Quotient.mk J) b).symm.trans (congrArg _ (eq_intCast C b).symm),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hchar]
    rw [← Int.cast_natCast, hJC, Submodule.IsPrincipal.mem_iff_generator_dvd, ← Int.natAbs_dvd,
      Int.natCast_dvd_natCast]
    rfl
  obtain ⟨-, hcard⟩ := @natCard_eq_pow_length_of_finiteType (MvPolynomial (Coord n) ℤ ⧸ J) _
    (by convert hft using 1 <;> rfl) (Geo.charOf V) _
  have hgeo : Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 =
      ((Module.length ℤ (MvPolynomial (Coord n) ℤ ⧸ J)).toNat : ℤ) := by
    simp only [Geo.geoNum, dif_pos hrel]
    rfl
  rw [hgeo, Nat.card_congr e.toEquiv, hcard, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}


omit [Fintype ι] [DecidableEq ι] in
theorem val_chartEval_eq_aeval_div (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : chartRing x c) : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), Subalgebra.coe_add, IntermediateField.coe_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp]
    simp [chartEval, chartRatio]


omit [Fintype ι] [DecidableEq ι] in
theorem chartEval_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by
  rintro ⟨a, ha⟩
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  refine ⟨f, Subtype.ext ?_⟩
  have h : (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) :=
    MvPolynomial.algHom_ext fun p ↦ by simp [chartEval]
  exact AlgHom.congr_fun h f


omit [Fintype ι] [DecidableEq ι] in
theorem mem_ker_chartEval_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ RingHom.ker (chartEval x c) ↔ aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0 := by
  rw [RingHom.mem_ker, ← val_chartEval_eq_aeval_div]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)

theorem aeval_blockScale_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (t : ι → Ω) (w : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    aeval (fun p ↦ t p.1 * w p) g = (∏ k, t k ^ m k) * aeval w g := by
  have h : algebraMap ℤ Ω = Int.castRingHom Ω := Subsingleton.elim _ _
  rw [aeval_def, aeval_def, h]
  exact eval₂_scale_of_isWeightedHomogeneous t w hg

theorem ker_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    RingHom.ker (chartEval x c) = orbitIdeal x ⊔
      Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
  set J := Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) with hJ
  set z : Coord n → AlgebraicClosure ℚ := fun p ↦ x p.1 p.2 / x p.1 (c p.1) with hz
  apply le_antisymm
  · intro f hf
    rw [mem_ker_chartEval_iff] at hf
    set N : ι → ℕ := fun k ↦ (compDegs f).sup fun m ↦ m k with hN
    have hle : ∀ m ∈ compDegs f, m ≤ N := fun m hm k ↦ Finset.le_sup (f := fun m : ι → ℕ ↦ m k) hm
    set F := ∑ m ∈ compDegs f,
      weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m) with hF
    have hFJ : f - F ∈ J := by
      have h1 : ∀ d, Ideal.Quotient.mk J (chartMonomial c d) = 1 := by
        intro d
        rw [chartMonomial, map_prod]
        refine Finset.prod_eq_one fun k _ ↦ ?_
        have hk : Ideal.Quotient.mk J (X ⟨k, c k⟩) = 1 := by
          rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
          exact Ideal.subset_span ⟨k, rfl⟩
        rw [map_pow, hk, one_pow]

      rw [← Ideal.Quotient.eq, hF, map_sum]
      simp only [map_mul, h1, mul_one]
      conv_lhs => rw [← sum_compDegs f]

      rw [map_sum]
    have hFP : F ∈ orbitIdeal x := by
      have hhom : IsWeightedHomogeneous (coordDeg n) F N := by
        have : F ∈ weightedHomogeneousSubmodule ℤ (coordDeg n) N := by
          refine Submodule.sum_mem _ fun m hm ↦ ?_
          have h2 := (weightedHomogeneousComponent_isWeightedHomogeneous m f).mul
            (isWeightedHomogeneous_chartMonomial c (N - m))
          rwa [add_tsub_cancel_of_le (hle m hm)] at h2
        exact this
      rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hhom]
      have hy : flatCone x = fun p ↦ x p.1 (c p.1) * z p := by
        funext p
        simp only [hz, flatCone]
        rw [mul_div_cancel₀ _ (hc p.1)]
      have hterm : ∀ m ∈ compDegs f,
          aeval (flatCone x) (weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m)) =
            (∏ k, x k (c k) ^ N k) * aeval z (weightedHomogeneousComponent (coordDeg n) m f) := by
        intro m hm
        have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ x k (c k)) z
          (weightedHomogeneousComponent_isWeightedHomogeneous m f)
        have hmon : aeval (flatCone x) (chartMonomial c (N - m)) = ∏ k, x k (c k) ^ (N k - m k) := by
          simp [chartMonomial, map_prod, flatCone]
        have hpow : ∏ k, x k (c k) ^ N k = (∏ k, x k (c k) ^ m k) * ∏ k, x k (c k) ^ (N k - m k) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [← pow_add, Nat.add_sub_cancel' (hle m hm k)]
        rw [map_mul, hmon, hpow]
        rw [hy]
        rw [hs]
        ring

      rw [hF, map_sum]
      refine (Finset.sum_congr rfl hterm).trans ?_

      rw [← Finset.mul_sum, ← map_sum, sum_compDegs, show aeval z f = 0 from hf, mul_zero]
    have : f = F + (f - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hFJ)
  · refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    · rw [mem_ker_chartEval_iff]
      rw [orbitIdeal, mem_mCoordIdeal_iff] at hf

      rw [← sum_compDegs f, map_sum]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ (x k (c k))⁻¹) (flatCone x)
        (weightedHomogeneousComponent_isWeightedHomogeneous m f)
      have hz' : (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) =
          fun p ↦ (x p.1 (c p.1))⁻¹ * flatCone x p := by
        funext p
        rw [div_eq_inv_mul]
        rfl
      rw [hz', hs]
      refine mul_eq_zero_of_right _ ?_
      have h0 := hf m
      rw [aeval_def, Subsingleton.elim (algebraMap ℤ _) (Int.castRingHom _)] at h0 ⊢
      exact h0
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, mem_ker_chartEval_iff]
      simp [div_self (hc k)]

theorem OrbitChartQuot.proof : OrbitChartQuot.Statement := by
  intro ι _ _ n x c hc V hV
  have hsurj := chartEval_surjective x c
  let g : MvPolynomial (Coord n) ℤ →+* chartRing x c ⧸ chartPoint x c V :=
    (Ideal.Quotient.mk _).comp (chartEval x c : MvPolynomial (Coord n) ℤ →+* chartRing x c)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hsurj
  have hker : RingHom.ker g =
      V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
    ext f
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (chartEval x c f) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, chartPoint,
      Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, ker_chartEval x c hc,
      ← sup_assoc, sup_eq_left.mpr hV]
  exact ⟨(RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hker)⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem card_quot_span_eq_relIndex {L : Type*} [CommRing L] (R : Subring L) (x : R) :
    Nat.card (R ⧸ Ideal.span {x}) =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).relIndex R.toAddSubgroup := by
  have h : (Ideal.span {x}).toAddSubgroup =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).addSubgroupOf R.toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [mul_comm]⟩
    · rintro ⟨a, ha, hy⟩
      exact ⟨⟨a, ha⟩, Subtype.ext (by simpa [mul_comm] using hy)⟩
  rw [AddSubgroup.relIndex, ← h]
  rfl

theorem relIndex_mulLeft_eq {L : Type*} [CommRing L] [IsDomain L] (A B : Subring L) (hAB : A ≤ B)
    (hfin : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (f : L) (hf : f ≠ 0) (hfA : f ∈ A) :
    (A.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex A.toAddSubgroup =
      (B.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex B.toAddSubgroup := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hf
  have h1 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup.map (AddMonoidHom.mulLeft f) :=
    AddSubgroup.map_mono hAB
  have h2 : B.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact B.mul_mem (hAB hfA) hy
  have h3 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact A.mul_mem hfA hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ h3 (show A.toAddSubgroup ≤ B.toAddSubgroup from hAB)
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj, ← e2, mul_comm] at e1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin) e1).symm

theorem LocalQuotCentred.proof (hN : CentredRingNormal.Statement) (hI : LocalNormalIndex.Statement) :
    LocalQuotCentred.Statement := by
  intro L _ _ O hft hfr m _ f hf g hg
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hS := hN L O hft m
  have hAI := hI L O hft m
  set P := placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} with hPdef
  have hAP : A.toSubring ≤ P := by
    rw [hS]
    intro x hx
    exact (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  have hfin : A.toSubring.toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    rw [hS]
    exact hAI
  let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
  have h1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
      Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A f : A.toSubring)}) := by
    refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.commutes f).symm
  have hfL : ((algebraMap O A f : A.toSubring) : L) = (f : L) := rfl
  have hf0 : (f : L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  rw [h1, card_quot_span_eq_relIndex, card_quot_span_eq_relIndex, hfL, hg]
  exact relIndex_mulLeft_eq _ _ hAP hfin _ hf0 (algebraMap O A f).2

end GroundTheory.Heights₂.Heights
end
