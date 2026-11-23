module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle006
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionProduct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_pow {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (j : ℕ) :
    IsMultiHomog (g ^ j) (j • d) := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.isMultiHomog_pow' <;> assumption

end SectionProduct


open SectionBoundedMul SectionProduct in
theorem SectionProduct.proof : SectionProduct.Statement := open SectionBoundedMul in by
  intro K _ ι _ Ω _ y A B C n j τ s t hdeg hmet hs ht
  have hdk : ∀ k, (τ : ℤ) * C.a k = (n : ℤ) * A.a k + (j : ℤ) * B.a k := fun k => by
    have := congrFun hdeg k
    simpa [smul_eq_mul] using this
  refine ⟨?_, ?_⟩
  ·
    intro c hc
    have hs' := hs c hc
    have ht' := ht c hc
    have heq : s * t ^ j * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k))) *
          (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := by
      have hp : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
          y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k)) * (y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := fun k => by
        have h0 := hc k
        rw [← zpow_natCast (y ⟨k, c k⟩ ^ _) j, ← zpow_mul, ← zpow_add₀ h0, hdk k]
        congr 1
        push_cast
        ring
      simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    rw [heq]
    exact mul_mem hs' (pow_mem ht' j)
  ·
    intro cc cc' hbs hbt dG dH G H z hG hH hdGH hrep hz
    choose c hc using hz.1
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      have hX := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
      rw [← X] at hX
      have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
      have hz0 := hz.2 _ hmem
      simp only [map_X, eval_X] at hz0
      exact hc k hz0
    obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a n hs c hy
    obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
    have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
    have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

    have hdeq : dgs + j • dgt + dH = dG + (N + j • M) := by
      funext k
      have e1 := hdgs k
      have e2 := hdgt k
      have e3 := hdGH k
      have e4 := hdk k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : ((dgs k + j * dgt k + dH k : ℕ) : ℤ) = ((dG k + (N k + j * M k) : ℕ) : ℤ) := by
        push_cast at e1 e2 e3 ⊢
        linear_combination e1 + (j : ℤ) * e2 - e3 - e4
      exact_mod_cast this
    have hF : IsMultiHomog (gs * gt ^ j * H - G * chartMono c (N + j • M)) (dgs + j • dgt + dH) := by
      refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs (isMultiHomog_pow hgt j)) hH) ?_
      rw [hdeq]
      exact isMultiHomog_mul hG (isMultiHomog_chartMono c (N + j • M))
    have hmono : ∀ {R : Type} [CommRing R] (w : (Σ k, ι k) → R),
        ∏ k, w ⟨k, c k⟩ ^ (N + j • M) k = (∏ k, w ⟨k, c k⟩ ^ N k) * (∏ k, w ⟨k, c k⟩ ^ M k) ^ j := by
      intro R _ w
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_add, pow_mul']
    have hF0 : aeval y (gs * gt ^ j * H - G * chartMono c (N + j • M)) = 0 := by
      rw [map_sub, map_mul, map_mul, map_pow, map_mul, hvs, hvt, hrep, aeval_chartMono, aeval_chartMono,
        aeval_chartMono, hmono]
      ring
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
    simp only [map_sub, map_mul, map_pow] at hz0
    rw [sub_eq_zero] at hz0

    set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
    have hmz : ev (chartMono c (N + j • M)) = ev (chartMono c N) * ev (chartMono c M) ^ j := by
      simp only [hev, eval_chartMono]
      exact hmono z
    have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j := by
      refine mul_pos (norm_pos_iff.mpr ?_) (pow_pos (norm_pos_iff.mpr ?_) j) <;>
      · simp only [hev, eval_chartMono]
        exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have key : ‖ev G‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) =
        ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖ := by
      rw [← norm_pow, ← norm_mul, ← hmz, ← norm_mul, ← norm_pow, ← norm_mul, ← norm_mul]
      exact congrArg norm hz0.symm
    have hprod : ‖ev gs‖ * ‖ev gt‖ ^ j ≤
        (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j :=
      mul_le_mul bs (pow_le_pow_left₀ (norm_nonneg _) bt j) (pow_nonneg (norm_nonneg _) j)
        ((norm_nonneg _).trans bs)
    rw [hmet z hz]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [key]
    calc ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖
        ≤ (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j * ‖ev H‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = cc * cc' ^ j * ‖ev H‖ * (A.h z ^ n * B.h z ^ j) *
            (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) := by
          ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SegreArithmetic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]


omit [DecidableEq K] in
theorem segreCoords_div (y : (Σ k, ι k) → Ω) (f c : (k : K) → ι k) :
    segreCoords y ⟨(), f⟩ / segreCoords y ⟨(), c⟩ = ∏ k, y ⟨k, f k⟩ / y ⟨k, c k⟩ := by
  simp only [segreCoords, Finset.prod_div_distrib]

theorem ratio_eq_segre (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ =
      segreCoords y ⟨(), Function.update c k i⟩ / segreCoords y ⟨(), c⟩ := by
  rw [segreCoords_div, Finset.prod_eq_single k]
  · rw [Function.update_self]
  · intro j _ hj
    rw [Function.update_of_ne hj]
    exact div_self (hc j)
  · intro h
    exact absurd (Finset.mem_univ k) h


omit [Fintype K] [DecidableEq K] in
theorem charZero_of_horizontal (y : (Σ k, ι k) → Ω)
    (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) (A := Ω) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro n hn
  have hmem : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply, C_eq_zero]
    exact hn
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from h] at hmem
  exact (Ideal.mem_bot).mp hmem

end SegreArithmetic


open SegreArithmetic BlockImageArithmetic in
theorem SegreArith.proof : SegreArith.Statement := by
  intro K _ _ ι _ Ω _ y D hY
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, hhor, hdim⟩ := hY
  have : CharZero Ω := charZero_of_horizontal y hhor
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  set x := segreCoords y with hx
  let c' : ∀ u, GlobalTheory ((k : K) → ι k) u := fun _ ↦ c
  have hx0 : x ⟨(), c⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  have hc' : ∀ u, x ⟨u, c' u⟩ ≠ 0 := fun _ ↦ hx0
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory ((k : K) → ι k)) x c' with hFx
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨u, f⟩, rfl⟩
    show x ⟨u, f⟩ / x ⟨u, c⟩ ∈ Fy
    rw [hx, segreCoords_div]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, f k⟩, rfl⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    rw [ratio_eq_segre y c hc k i]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨(), Function.update c k i⟩, rfl⟩
  have hLeq : Fy = Fx := le_antisymm hLy hLx
  have hdy := ringKrullDim_eq y c hc
  rw [hdim] at hdy
  rw [coordIdeal_eq_mCoordIdeal]
  refine ⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x,
    CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩
  rw [ringKrullDim_eq x c' hc']
  rw [← hFy, hLeq] at hdy
  generalize (Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢
  have h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1 := by exact_mod_cast hdy
  induction t using ENat.recTopCoe with
  | top => simp at h1
  | coe t =>
    have h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1 := by exact_mod_cast h1
    have h3 : t = D := by omega
    subst h3
    rw [Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace NormalLocusRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_zpow_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g d) : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ chartRingZ y c := by
  rw [NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  refine ⟨⟨_, aeval_mul_zpow_mem y c hg⟩, ⟨_, aeval_mul_zpow_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero_of_isHorizontal (y : (Σ k, ι k) → Ω) (hH : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [mConeMap, aeval_C, MvPolynomial.algebraMap_apply]
    simp [hn]
  rw [hH, Ideal.mem_bot] at hmem
  exact_mod_cast hmem


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : CharZero (chartRingZ y c) :=
  charZero_of_inj_zero fun n hn => by
    have : ((n : chartRingZ y c) : Ω) = 0 := by rw [hn]; rfl
    exact_mod_cast this

theorem finiteType_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Algebra.FiniteType ℤ (chartRingZ y c) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

theorem exists_conductor [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ a ∈ chartRingZ y c, a ≠ 0 ∧ ∀ t ∈ integralClosure (chartRingZ y c) Ω, a * t ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have := charZero_chartRingZ y c
  have := finiteType_chartRingZ y c
  have : Module.Finite A (integralClosure A Ω) :=
    Model.finite_integralClosure_fractionRing_of_charZero A Ω
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A (integralClosure A Ω)).FG)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (S.image ((↑) : integralClosure A Ω → Ω))
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  refine ⟨((b : A) : Ω), (b : A).2, hb0, fun t ht => ?_⟩
  have htop : (⟨t, ht⟩ : integralClosure A Ω) ∈ Submodule.span A (S : Set (integralClosure A Ω)) := by
    rw [hS]; trivial
  suffices key : ∀ x ∈ Submodule.span A (S : Set (integralClosure A Ω)), ((b : A) : Ω) * (x : Ω) ∈ A from
    key _ htop
  intro x hx
  set_option synthInstance.maxHeartbeats 200000 in
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr⟩ := hb (x : Ω) (Finset.mem_image_of_mem _ hx)
    rw [show ((b : A) : Ω) * (x : Ω) = (b : A) • (x : Ω) by rw [Algebra.smul_def]; rfl, ← hr]
    exact r.2
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [Subalgebra.coe_add, mul_add]
    exact add_mem hx hz
  | smul r x _ hx =>
    have : ((b : A) : Ω) * (((r : A) • x : integralClosure A Ω) : Ω) = (r : Ω) * (((b : A) : Ω) * (x : Ω)) := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]
      show _ * ((r : Ω) * _) = _
      ring
    rw [this]
    exact mul_mem r.2 hx


omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (H : J → MRing ι) (N : J → K → ℕ)
    (hH : ∀ j ∈ s, IsMultiHomog (H j) (N j)) : IsMultiHomog (∏ j ∈ s, H j) (∑ j ∈ s, N j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocalRep.isMultiHomog_C (ι := ι) 1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact LocalRep.isMultiHomog_mul (hH j (Finset.mem_insert_self j s))
      (ih fun i hi => hH i (Finset.mem_insert_of_mem hi))

theorem notMem_mCoordIdeal (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  have h := (RingHom.mem_ker).mp hmem
  erw [ConeTrdeg.mConeMap_of_isMultiHomog y hf] at h
  exact mul_ne_zero (MvPolynomial.C_ne_zero.2 h0)
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

end NormalLocusRep


open NormalLocusRep in
theorem NormalLocusRep.proof : NormalLocusRep.Statement := by
  intro K _ ι _ Ω _ y D hV hbir
  classical
  have := charZero_of_isHorizontal y hV.2.2.1

  have hchart : ∀ c : ∀ k, ι k, ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ integralClosure (chartRingZ y c) Ω,
        (aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ))) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨a, ha, ha0, hcond⟩ := exists_conductor y hbir c hc
      obtain ⟨N, H, hH, he⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hc ha
      have hP : ∀ N' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ N' k) ≠ 0 := fun N' =>
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
      have hHa : aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ)) = a := by
        rw [he, mul_assoc, ← Finset.prod_mul_distrib]
        rw [Finset.prod_eq_one fun k _ => by
          rw [← zpow_natCast, ← zpow_add₀ (hc k), add_neg_cancel, zpow_zero], mul_one]
      refine ⟨N, H, hH, ?_, fun _ t ht => ?_⟩
      · rw [he]
        exact mul_ne_zero ha0 (hP N)
      · rw [hHa]
        exact hcond t ht
    · exact ⟨0, C 1, LocalRep.isMultiHomog_C 1, by simp, fun h => absurd h hc⟩
  choose N H hH hH0 hcond using hchart
  refine ⟨∑ c, N c, ∏ c, H c, isMultiHomog_prod _ H N fun c _ => hH c,
    notMem_mCoordIdeal y (isMultiHomog_prod _ H N fun c _ => hH c)
      (by rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun c _ => hH0 c), ?_⟩
  intro a τ s hs z hz hfz

  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  have hHz : eval z (map (Int.castRingHom ℂ) (H c)) ≠ 0 := by
    rw [map_prod, map_prod] at hfz
    exact (Finset.prod_ne_zero_iff.mp hfz) c (Finset.mem_univ c)
  have hx := hcond c hyc _ (hs c hyc)
  obtain ⟨M, G, hG, hGe⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hyc hx
  refine ⟨M + (N c + fun k => ((τ : ℤ) * a k).toNat), N c + (M + fun k => (-((τ : ℤ) * a k)).toNat),
    G * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N c + fun k => ((τ : ℤ) * a k).toNat) k,
    H c * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M + fun k => (-((τ : ℤ) * a k)).toNat) k,
    LocalRep.isMultiHomog_mul hG (LocalRep.isMultiHomog_chartMono c _),
    LocalRep.isMultiHomog_mul (hH c) (LocalRep.isMultiHomog_chartMono c _), fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  ·
    have hz' : ∀ p q : K → ℤ, (∏ k, y ⟨k, c k⟩ ^ p k) * ∏ k, y ⟨k, c k⟩ ^ q k =
        ∏ k, y ⟨k, c k⟩ ^ (p k + q k) := fun p q => by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => (zpow_add₀ (hyc k) _ _).symm
    have hnat : ∀ p : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ p k) = ∏ k, y ⟨k, c k⟩ ^ (p k : ℤ) := fun p =>
      Finset.prod_congr rfl fun k _ => (zpow_natCast _ _).symm
    have key : (∏ k, y ⟨k, c k⟩ ^ (-(N c k : ℤ))) * (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
        (∏ k, y ⟨k, c k⟩ ^ M k) * (∏ k, y ⟨k, c k⟩ ^ (N c k + ((τ : ℤ) * a k).toNat)) =
        ∏ k, y ⟨k, c k⟩ ^ (M k + (-((τ : ℤ) * a k)).toNat) := by
      simp only [hnat]
      rw [hz', hz', hz']
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      push_cast
      omega
    simp only [map_mul, map_prod, map_pow, aeval_X, Pi.add_apply]
    rw [hGe]
    linear_combination (s * aeval y (H c)) * key
  · simp only [map_mul, map_prod, map_pow, map_X, eval_X]
    exact mul_ne_zero hHz (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
