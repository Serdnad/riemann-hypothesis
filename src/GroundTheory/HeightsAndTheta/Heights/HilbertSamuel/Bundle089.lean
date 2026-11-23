module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockVeronese
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle043
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiSandwichLower
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiSandwichUpper
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymGram
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle008

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section G1SpanProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartLat_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a m) : s * t ∈ chartLat y a (n + m) := by
  apply _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockVeronese.chartLat_mul <;> assumption

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {C C' : ℝ} {s : Ω}
    (h : IsBoundedH P y A τ C s) (hC : C ≤ C') : IsBoundedH P y A τ C' s := by
  intro dg dh g h' z hg hh hdeg he hz
  refine (h dg dh g h' z hg hh hdeg he hz).trans ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hC (mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt (A.pos z hz.1)) _))

theorem mul_monomial_bounded (hMul : SectionBoundedMul.Statement) {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {q : ℕ}
    {w : Fin q → Ω} (hw : ∀ j, w j ∈ chartLat y A.a 1)
    (hsmall : ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) {x : Ω} {n : ℕ} {C : ℝ}
    (hx : x ∈ chartLat y A.a n) (hb : IsBoundedH (mCoordIdeal y) y A n C x) (μ : Fin q → ℕ) :
    x * ∏ j, w j ^ μ j ∈ chartLat y A.a (n + ∑ j, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j, μ j) C (x * ∏ j, w j ^ μ j) := by
  have step : ∀ {x' : Ω} {n' : ℕ} (j : Fin q), x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ∈ chartLat y A.a (n' + 1) ∧ IsBoundedH (mCoordIdeal y) y A (n' + 1) C (x' * w j) := by
    intro x' n' j hx' hb'
    refine ⟨chartLat_mul hx' (hw j), ?_⟩
    have := hMul K ι Ω y A n' 1 C 1 x' (w j) hx' (hw j) hb' (isBoundedH_one_of_isSmallH (hsmall j))
    rwa [mul_one] at this
  have hpow : ∀ (j : Fin q) (k : ℕ) {x' : Ω} {n' : ℕ}, x' ∈ chartLat y A.a n' →
      IsBoundedH (mCoordIdeal y) y A n' C x' →
      x' * w j ^ k ∈ chartLat y A.a (n' + k) ∧ IsBoundedH (mCoordIdeal y) y A (n' + k) C (x' * w j ^ k) := by
    intro j k
    induction k with
    | zero => intro x' n' hx' hb'; simpa using ⟨hx', hb'⟩
    | succ k ih =>
      intro x' n' hx' hb'
      obtain ⟨h1, h2⟩ := ih hx' hb'
      have := step j h1 h2
      rw [pow_succ, ← mul_assoc, ← add_assoc]
      exact this
  have hS : ∀ S : Finset (Fin q), x * ∏ j ∈ S, w j ^ μ j ∈ chartLat y A.a (n + ∑ j ∈ S, μ j) ∧
      IsBoundedH (mCoordIdeal y) y A (n + ∑ j ∈ S, μ j) C (x * ∏ j ∈ S, w j ^ μ j) := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simpa using ⟨hx, hb⟩
    | insert a S ha ih =>
      obtain ⟨h1, h2⟩ := hpow a (μ a) ih.1 ih.2
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have e1 : x * (w a ^ μ a * ∏ j ∈ S, w j ^ μ j) = (x * ∏ j ∈ S, w j ^ μ j) * w a ^ μ a := by ring
      have e2 : n + (μ a + ∑ j ∈ S, μ j) = n + ∑ j ∈ S, μ j + μ a := by ring
      rw [e1, e2]
      exact ⟨h1, h2⟩
  exact hS Finset.univ

theorem exists_coord_ne_zero {y : (Σ k, ι k) → Ω} {d : ℕ} (hV : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := hV.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

end G1SpanProof

theorem SuccessiveMinimaSpan.proof (hFin : SectionRingFinite.Statement) (hBd : SectionBounded.Statement)
    (hMul : SectionBoundedMul.Statement) : SuccessiveMinimaSpan.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 _ hV _ hA
  obtain ⟨q, w, hw, hgen, hsmall⟩ := hA.gen
  obtain ⟨r, d, e, he, hspan⟩ :=
    hFin K ι Ω y A.a q w (exists_coord_ne_zero hV) hw hgen
  have hCe : ∀ i, ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A (d i) C (e i) := fun i =>
    hBd K ι Ω y A q w hw hgen hsmall (d i) (e i) (he i)
  choose Ce hCe using hCe
  refine ⟨∑ i, |Ce i|, fun n => le_antisymm ?_ ?_⟩
  · rw [AddSubgroup.closure_le]
    exact fun s hs => hs.1
  · refine (hspan n).trans (AddSubgroup.closure_mono ?_)
    rintro s ⟨i, μ, hn, rfl⟩
    obtain ⟨h1, h2⟩ := mul_monomial_bounded hMul hw hsmall (he i) (hCe i) μ
    rw [hn] at h1 h2
    refine ⟨h1, isBoundedH_mono h2 ?_⟩
    exact (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Ce i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SecMRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem finite_secM (y : (Σ k, ι k) → Ω) (d : K → ℕ) : Module.Finite ℤ (secM y d) := by
  have h := SectionLatticeFinite.secM_fg y d
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (secM y d), ← Submodule.fg_iff_addSubgroup_fg] at h
  exact Module.Finite.iff_fg.mpr h


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) :
    aeval y g = 0 := by
  have hext : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (mConeMap y) = aeval y :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  have h0 : mConeMap y g = 0 := hg
  rw [← hext, AlgHom.comp_apply, h0, map_zero]

variable [DecidableEq K]

theorem finrank_secM_le [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : K → ℕ) :
    Module.finrank ℤ (secM y d) ≤
      Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) d) := by
  have hI : ∀ f ∈ KH.genIdeal y, aeval y f = 0 := by
    have hle : KH.genIdeal y ≤ RingHom.ker (aeval y : MRingOver ℚ ι →ₐ[ℚ] Ω) := by
      unfold KH.genIdeal
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval y (map (algebraMap ℤ ℚ) g) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem hg
    exact fun f hf => hle hf
  let ψ : (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₗ[ℚ] Ω :=
    (Ideal.Quotient.liftₐ (KH.genIdeal y) (aeval y) hI).toLinearMap
  let V := NumbersDVR.gradedPiece (KH.genIdeal y) d
  have : FiniteDimensional ℚ V := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) d).1
  let R : Submodule ℚ Ω := V.map ψ
  have : FiniteDimensional ℚ R := Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map ψ)
  have hsub : ∀ s ∈ secM y d, s ∈ R := by
    intro s hs
    have hspan : Submodule.span ℤ {s | ∃ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ aeval y g = s} ≤
        R.restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨Ideal.Quotient.mk _ (map (Int.castRingHom ℚ) g), ⟨map (Int.castRingHom ℚ) g, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
        exact (Bridge.isMultiHomog_iff _ _).mpr fun m hm k => hg m (support_map_subset _ _ hm) k
      · change aeval y (map (Int.castRingHom ℚ) g) = aeval y g
        rw [← algebraMap_int_eq, aeval_map_algebraMap]
    exact hspan hs
  have := finite_secM y d
  have : Module.IsTorsionFree ℤ (secM y d) :=
    Function.Injective.moduleIsTorsionFree (secM y d).subtype Subtype.val_injective (fun _ _ => rfl)
  let bs := Module.Free.chooseBasis ℤ (secM y d)
  let v : Module.Free.ChooseBasisIndex ℤ (secM y d) → Ω := fun i => (bs i : Ω)
  have hliZ : LinearIndependent ℤ v :=
    bs.linearIndependent.map' (secM y d).subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_span_eq_card hliQ]
  calc Module.finrank ℚ (Submodule.span ℚ (Set.range v)) ≤ Module.finrank ℚ R :=
        Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => hsub _ (bs i).2))
    _ ≤ Module.finrank ℚ V := Submodule.finrank_map_le ψ V

theorem proof (h : GenericFibreVar.Statement) : SecMRankBound.Statement := by
  intro K _ ι _ Ω _ y D b hvar hb
  classical

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  refine ⟨fun m => finite_secM y _, ?_⟩

  obtain ⟨⟨hprime, hhom, -⟩, hdim⟩ := h K ι Ω y D hvar
  have hlt : ringKrullDim (MRingOver ℚ ι ⧸ KH.genIdeal y) <
      (((D + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : D + Fintype.card K < D + 1 + Fintype.card K)
  have hdeg := NumbersDVR.HilbDegBound.full ℚ K ι (D + 1) (KH.genIdeal y) hprime
    ((Bridge.isMultiHomogIdeal_iff _).mpr hhom) hlt
  obtain ⟨a₀, C, hC⟩ := DegLTGrowth.proof K (D + 1) _ hdeg
  have hexp : ((D + 1 : ℕ) : ℝ) - 1 = ((D : ℕ) : ℝ) := by push_cast; ring

  have hrank : ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤
      |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
    intro m
    have e := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) (fun k => m * b k)).2
    have hle := finrank_secM_le y (fun k => m * b k)
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ (Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) (fun k => m * b k)) : ℝ) := by
          exact_mod_cast hle
      _ = |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
          rw [e]; simp
  set B : ℝ := ∑ k, (b k : ℝ) with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  set M0 : ℝ := ∑ j ∈ Finset.range a₀, (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ) with hM0def
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg fun j _ => by positivity
  have hC1 : 0 ≤ max C 0 * (B + 1) ^ D := by positivity
  refine ⟨max C 0 * (B + 1) ^ D + M0, by positivity, fun m => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hpow1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ D := one_le_pow₀ (by linarith)
  rcases lt_or_ge m a₀ with hm | hm
  ·
    have h1 : (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ M0 :=
      Finset.single_le_sum (f := fun j => (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ))
        (fun j _ => by positivity) (Finset.mem_range.mpr hm)
    nlinarith
  ·
    have hg := hC (fun k => m * b k) (fun k => le_trans hm (Nat.le_mul_of_pos_right m (hb k)))
    rw [hexp, Real.rpow_natCast] at hg
    have hsum : (∑ k, (((m * b k : ℕ)) : ℝ)) = m * B := by
      rw [hBdef, Finset.mul_sum]; push_cast; rfl
    have hX : (m : ℝ) * B + 1 ≤ (B + 1) * ((m : ℝ) + 1) := by nlinarith
    have hXpow : ((m : ℝ) * B + 1) ^ D ≤ ((B + 1) * ((m : ℝ) + 1)) ^ D :=
      pow_le_pow_left₀ (by positivity) hX D
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := hrank m
      _ ≤ C * ((∑ k, (((m * b k : ℕ)) : ℝ)) + 1) ^ D := hg
      _ = C * ((m : ℝ) * B + 1) ^ D := by rw [hsum]
      _ ≤ max C 0 * ((m : ℝ) * B + 1) ^ D :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((B + 1) * ((m : ℝ) + 1)) ^ D :=
          mul_le_mul_of_nonneg_left hXpow (le_max_right _ _)
      _ = max C 0 * (B + 1) ^ D * ((m : ℝ) + 1) ^ D := by rw [mul_pow]; ring
      _ ≤ (max C 0 * (B + 1) ^ D + M0) * ((m : ℝ) + 1) ^ D := by nlinarith

theorem full : SecMRankBound.Statement := proof GenericFibreVar.proof

end SecMRankBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ComponentsMeetNull.proof (hA : ChartDimLt.Statement) (hB : ChartRatioImageNull.Statement) :
    ComponentsMeetNull.Statement := by
  classical
  intro K _ ι _ P e Ψ S hP _ hS
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC

  have hdimW : ∀ W ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
    have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
    have : PQ.IsPrime := hvar.1.isPrime
    have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
      rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
      congr 1
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C]
        congr 1
      · simp
    intro W hW
    rw [← hext] at hW
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ W hW]
    exact hvar.2

  have hPCh : IsMultiHomogIdeal PC := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPC, hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  have hWh : ∀ W ∈ PC.minimalPrimes, IsMultiHomogIdeal W := fun W hW =>
    (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
      (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι PC W
        ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff PC).mpr hPCh) hW)
  have hsuph : ∀ W ∈ PC.minimalPrimes, ∀ W' ∈ PC.minimalPrimes, IsMultiHomogIdeal (W ⊔ W') := by
    intro W hW W' hW'
    obtain ⟨T, hT, rfl⟩ := hWh W hW
    obtain ⟨T', hT', rfl⟩ := hWh W' hW'
    exact ⟨T ∪ T', fun f hf => hf.elim (hT f) (hT' f), (Ideal.span_union T T').symm⟩

  have hsup : ∀ W ∈ PC.minimalPrimes, ∀ W' ∈ PC.minimalPrimes, W ≠ W' →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ W')) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro W hW W' hW' hne
    have : W.IsPrime := hW.1.1
    obtain ⟨g, hgW', hgW⟩ : ∃ g ∈ W', g ∉ W := by
      by_contra hcon
      push_neg at hcon
      exact hne (le_antisymm (hW.2 hW'.1 hcon) hcon)
    have hg0 : Ideal.Quotient.mk W g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg0)
    have eqv : ((MvPolynomial (Σ k, ι k) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W g}) ≃+*
        MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g}) :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {g}))
    rw [ringKrullDim_eq_of_ringEquiv eqv, hdimW W hW] at h1
    have hle : W ⊔ Ideal.span {g} ≤ W ⊔ W' :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hgW') W
    have h2 := ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g})) = a at h1 h2
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ W')) = b at h2 ⊢
    refine lt_of_le_of_lt h2 ?_
    induction a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h1 (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) + 1 ≤ ((e + Fintype.card K : ℕ) : ℕ∞)) by simp))
      | coe a =>
        have : a + 1 ≤ e + Fintype.card K := by exact_mod_cast h1
        exact_mod_cast (show a < e + Fintype.card K by omega)

  refine measure_mono_null (t := ⋃ W ∈ (S : Set _), ⋃ W' ∈ (S : Set _), ⋃ (_ : W ≠ W'), ⋃ p : (k : K) → ι k,
      {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal (W ⊔ W') p), Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)}) ?_ ?_
  · rintro y ⟨z, hz, hzy, W, hWS, W', hW'S, hne, hzW, hzW'⟩
    choose p hp using hz.1
    simp only [Set.mem_iUnion, Finset.mem_coe]
    refine ⟨W, hWS, W', hW'S, hne, p, ReciprocityTheory.AnForm.R.affCoord p z, ?_, ?_⟩
    · have hcone : z ∈ ReciprocityTheory.AnForm.R.conePts (W ⊔ W') := by
        refine ⟨hz.1, fun f hf => ?_⟩
        have hker : W ⊔ W' ≤ RingHom.ker (eval z) := sup_le
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW f hf))
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW' f hf))
        exact RingHom.mem_ker.mp (hker hf)
      have h := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal
        (hsuph W (hS W hWS) W' (hS W' hW'S)) p z hp).1 hcone
      intro f hf
      have hf' := h f hf
      rwa [← MvPolynomial.coe_aeval_eq_eval] at hf'
    · have hc : (∏ k, z ⟨k, p k⟩)⁻¹ ≠ 0 := inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hp k)
      have hseg : segre (ReciprocityTheory.AnForm.R.affCoord p z) = (∏ k, z ⟨k, p k⟩)⁻¹ • segre z := by
        funext i
        simp only [segre, ReciprocityTheory.AnForm.R.affCoord, Pi.smul_apply, smul_eq_mul, Finset.prod_div_distrib]
        rw [div_eq_inv_mul]
      have hΨ : Ψ (segre (ReciprocityTheory.AnForm.R.affCoord p z)) =
          (∏ k, z ⟨k, p k⟩)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
        rw [hseg, map_smul, hzy]
      rw [hΨ, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact ⟨hc, rfl⟩
  · refine (measure_biUnion_null_iff S.countable_toSet).2 fun W hW => ?_
    refine (measure_biUnion_null_iff S.countable_toSet).2 fun W' hW' => ?_
    refine measure_iUnion_null fun hne => measure_iUnion_null fun p => ?_
    exact hB K ι _ e Ψ (hA K ι (W ⊔ W') e p (hsuph W (hS W hW) W' (hS W' hW'))
      (hsup W (hS W hW) W' (hS W' hW') hne))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section

theorem ResChiBounds.proof (hR : ResolutionSupBound.Statement) : ResChiBounds.Statement := by
  intro D Ω _ _ κ _ d e hfr hFS
  have hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ))
        (ResSym.symMeasure d) := fun n r b hb => ResSym.integrable_gram d hb.1
  have hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b →
      (bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).PosDef :=
    fun n r b hb => ResSym.posDef_gram d hb
  obtain ⟨k₁, C₁, h₁⟩ := ResChiSandwich.upper hfr hFS hint hpd (ResSym.sup_le_gram hR d)
  obtain ⟨k₂, C₂, h₂⟩ := ResChiSandwich.lower hfr hFS (ResSym.symMeasure_compl_pts d) hint hpd
  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hδ : (0 : ℝ) ≤ (projDeg d.x e : ℝ) := Nat.cast_nonneg _
  refine ⟨max k₁ k₂, max C₁ C₂, fun n hn => ?_⟩
  obtain ⟨b₀, hb₀⟩ := exists_isSecBasis d.x n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 := ⟨⟨_, b₀⟩, hb₀⟩
  rw [ResSym.resChi_eq d n h]
  have hX : 0 ≤ (n : ℝ) ^ D * Real.log (n + 1) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hu := h₁ n (by omega) _ _ h.choose_spec
  have hl := h₂ n (by omega) _ _ h.choose_spec
  constructor
  · have hm : chiP D (n - max k₁ k₂) ≤ chiP D (n - k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₂ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX
    linarith
  · have hm : chiP D (n + k₁) ≤ chiP D (n + max k₁ k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₁ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
