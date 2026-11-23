module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle011
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ChartLatFull

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ratSat [CharZero Ω] (R : Subalgebra ℤ Ω) : Subalgebra ℚ Ω where
  carrier := {t | ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ R}
  mul_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t * u) = ((n : Ω) * t) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.mul_mem ht hu
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t + u) = (m : Ω) * ((n : Ω) * t) + (n : Ω) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.natCast_mem m) ht) (R.mul_mem (R.natCast_mem n) hu)
  zero_mem' := ⟨1, one_pos, by simp⟩
  algebraMap_mem' := by
    intro q
    refine ⟨q.den, q.den_pos, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [this]
    exact R.intCast_mem _

theorem exists_nat_mul_mem [NumberField Ω] {y : (Σ k, ι k) → Ω} (hy : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ chartRingZ y c := by
  obtain ⟨d, g, h, hg, hh, hh0, hgt⟩ := hy t
  have hX : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hG : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hg⟩
  have hH : aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hh⟩
  have hinv : (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ ∈ ratSat (chartRingZ y c) :=
    Subalgebra.inv_mem_of_algebraic (A := ratSat (chartRingZ y c)) (x := ⟨_, hH⟩)
      (Algebra.IsAlgebraic.isAlgebraic _)
  have ht : t = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) * (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ := by
    rw [hgt, inv_div, div_mul_div_comm, mul_comm (∏ k, y ⟨k, c k⟩ ^ d k), mul_assoc,
      mul_div_assoc, div_self (mul_ne_zero hh0 hX), mul_one]
  have := (ratSat (chartRingZ y c)).mul_mem hG hinv
  rw [← ht] at this
  exact this

end ChartLatFull

theorem ChartLatFull.proof : ChartLatFull.Statement := by
  intro K _ ι _ Ω _ _ y hy a τ s
  classical
  let t : (∀ k, ι k) → Ω := fun c => s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))
  let N : (∀ k, ι k) → ℕ := fun c =>
    if hc : ∀ k, y ⟨k, c k⟩ ≠ 0 then (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose else 1
  have hNpos : ∀ c, 0 < N c := by
    intro c
    simp only [N]
    split_ifs with hc
    · exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.1
    · exact one_pos
  refine ⟨∏ c, N c, Finset.prod_pos fun c _ => hNpos c, ?_⟩
  show ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → _
  intro c hc
  have hN : (N c : Ω) * t c ∈ chartRingZ y c := by
    simp only [N, dif_pos hc]
    exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.2
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = (m : Ω) * ((N c : Ω) * t c) := by
    rw [hm]; push_cast; simp only [t]; ring
  rw [this]
  exact (chartRingZ y c).mul_mem ((chartRingZ y c).natCast_mem m) hN

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_scale {S : Type} [CommRing S] {g : MRing ι} {a : K → ℕ} (hg : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a)
    (t : K → S) (x z : (Σ k, ι k) → S) (hz : ∀ p, z p = t p.1 * x p) :
    aeval z g = (∏ k, t k ^ a k) * aeval x g := by
  obtain rfl : z = fun p => t p.1 * x p := funext hz
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem eval_map_int {σ : Type} (z : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

def homogAt (c : ∀ k, ι k) (M : ℕ) (F : MRing ι) : MRing ι :=
  ∑ m ∈ F.support, monomial m (AddMonoidAlgebra.coeff F m) * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M - ∑ i, m ⟨k, i⟩)

theorem homogAt_isMultiHomog (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (homogAt c M F) (fun _ => M) := by
  classical
  intro m' hm' k
  obtain ⟨m, hm, hm'⟩ := Finset.mem_biUnion.mp (support_sum hm')
  have h := Inter.ThmIUnique.isMultiHomog_mul' (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial m (AddMonoidAlgebra.coeff F m))
    (Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun k => M - ∑ i, m ⟨k, i⟩)) m' hm' k
  simp only [Pi.add_apply] at h
  have := hM m hm k
  show _ = M
  omega

theorem aeval_homogAt {S : Type} [CommRing S] (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (x : (Σ k, ι k) → S) (hx : ∀ k, x ⟨k, c k⟩ = 1) : aeval x (homogAt c M F) = aeval x F := by
  conv_rhs => rw [F.as_sum]

  simp only [homogAt, map_sum, map_mul, map_prod, map_pow, aeval_X, hx, one_pow, Finset.prod_const_one, mul_one]

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal y)) (c : ∀ k, ι k) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) {F : MRing ι} (hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) F = 0) :
    aeval (fun p => w p / w ⟨p.1, c p.1⟩) F = 0 := by
  classical
  set M := ∑ m ∈ F.support, ∑ p, m p
  have hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M := by
    intro m hm k
    calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
          Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      _ = ∑ p, m p := (Fintype.sum_sigma _).symm
      _ ≤ M := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm
  have hG := homogAt_isMultiHomog c M F hM
  have hyG : aeval y (homogAt c M F) = 0 := by
    rw [aeval_scale hG (fun k => y ⟨k, c k⟩) (fun p => y p / y ⟨p.1, c p.1⟩) y
      (fun p => by field_simp [hyc p.1]), aeval_homogAt c M F _ (fun k => div_self (hyc k)), hF, mul_zero]
  have hmem : homogAt c M F ∈ mCoordIdeal y := (BlockImageInverse.mem_mCoordIdeal_iff y hG).mpr hyG
  have hwG := hw.2 _ hmem
  rw [eval_map_int, aeval_scale hG (fun k => w ⟨k, c k⟩) (fun p => w p / w ⟨p.1, c p.1⟩) w
    (fun p => by field_simp [hwc p.1]), aeval_homogAt c M F _ (fun k => div_self (hwc k))] at hwG
  exact (mul_eq_zero.mp hwG).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hwc k))

end LiftGraphPoints


open LiftGraphPoints in
theorem LiftGraphPoints.proof : LiftGraphPoints.Statement := by
  classical
  intro K _ ι _ Ω _ y n r v hv hgen w hw
  choose c hwc using hw.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hwc k
    have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
    simpa using hw.2 _ hX
  have hrange : chartRingZ y c = (aeval fun p => y p / y ⟨p.1, c p.1⟩).range := by
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  have hQ : ∀ j, ∃ Q : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) Q = v j * ∏ k, y ⟨k, c k⟩ ^ (-n k) := by
    intro j
    have h := hv j c hyc
    simp only [Nat.cast_one, one_mul] at h
    rw [hrange] at h
    exact (AlgHom.mem_range _).mp h
  choose Q hQ using hQ
  set σ : Fin r → ℂ := fun j => aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) with hσ
  refine ⟨addBlock w σ, ⟨fun k => ?_, fun f hf => ?_⟩, rfl⟩
  · cases k with
    | some k => exact ⟨c k, hwc k⟩
    | none =>
      obtain ⟨u, hu, hsum⟩ := hgen c hyc
      have hU : ∀ j, ∃ U : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) U = u j := fun j =>
        (AlgHom.mem_range _).mp (hrange ▸ hu j)
      choose U hU using hU
      by_contra hcon
      push Not at hcon
      have hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) (∑ j, U j * Q j - 1) = 0 := by

        simp only [map_sub, map_sum, map_mul, hU, hQ, map_one, hsum, sub_self]
      have h1 := aeval_ratio_eq_zero hw c hyc hwc hF
      have hσ0 : ∀ j, aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) = 0 := fun j => hcon j
      simp [hσ0] at h1
  · obtain ⟨S, hS, hspan⟩ := CoordinateConeArithVar.isMultiHomogIdeal (addBlock y v)
    rw [hspan] at hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha⟩ := hS g hg
      have hg0 : aeval (addBlock y v) g = 0 :=
        (BlockImageInverse.mem_mCoordIdeal_iff _ ha).mp (hspan ▸ Ideal.subset_span hg)
      have hP : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hyc k)
      have hY : ∀ o : Option K, (o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩) ≠ 0 := by
        intro o
        cases o with
        | none => exact inv_ne_zero hP
        | some k => exact hyc k
      rw [aeval_scale ha (fun o => o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩)
        (addBlock (fun p => y p / y ⟨p.1, c p.1⟩) fun j => aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j)) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none =>
            exact (show ∀ j : Fin r, v j = (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ *
                aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j) from fun j => by rw [hQ]; field_simp) i
          | some k =>
            show y ⟨k, i⟩ = y ⟨k, c k⟩ * (y ⟨k, i⟩ / y ⟨k, c k⟩)
            field_simp [hyc k])] at hg0
      have hg1 := (mul_eq_zero.mp hg0).resolve_left (Finset.prod_ne_zero_iff.mpr fun o _ => pow_ne_zero _ (hY o))
      have hsub : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (x : (Σ k, ι k) → T),
          aeval x (aeval (addBlock (fun p => (X p : MRing ι)) Q) g) =
            aeval (addBlock x fun j => aeval x (Q j)) g := by
        intro T _ _ x
        rw [comp_aeval_apply]
        have hfun : (fun q => aeval x (addBlock (fun p => (X p : MRing ι)) Q q)) =
            addBlock x fun j => aeval x (Q j) := by
          funext q
          obtain ⟨o, i⟩ := q
          cases o with
          | none => rfl
          | some k => exact aeval_X _ _
        rw [hfun]
      rw [← hsub] at hg1
      have h2 := aeval_ratio_eq_zero hw c hyc hwc hg1
      rw [hsub] at h2
      rw [eval_map_int, aeval_scale ha (fun o => o.elim 1 fun k => w ⟨k, c k⟩)
        (addBlock (fun p => w p / w ⟨p.1, c p.1⟩) σ) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none => exact (one_mul _).symm
          | some k =>
            show w ⟨k, i⟩ = w ⟨k, c k⟩ * (w ⟨k, i⟩ / w ⟨k, c k⟩)
            field_simp [hwc k]), h2, mul_zero]
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => simp [map_add (f := _), h₁, h₂]
    | smul a x _ hx => simp [smul_eq_mul, map_mul, hx]

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftBlockGraph

variable {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]

theorem generatesOn_liftCoords [Fintype K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω)
    (h : KH.GeneratesOn y n x') : KH.GeneratesOn y n (liftCoords x') := by
  intro c hc
  obtain ⟨u, hu, hs⟩ := h c hc
  refine ⟨fun j => u ((Fintype.equivFin ι').symm j), fun j => hu _, ?_⟩
  rw [← hs]
  exact Fintype.sum_equiv (Fintype.equivFin ι').symm _ _ (fun j => rfl)

theorem exists_ne_zero_of_generatesOn [Fintype K] {r : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (h : KH.GeneratesOn y n v) : ∃ j, v j ≠ 0 := by
  obtain ⟨u, -, hs⟩ := h c hc
  by_contra h0
  simp only [not_exists, not_not] at h0
  simp [h0] at hs

variable [CharZero Ω] [Fintype K] [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartRingZ_le_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingZ y c) :
    x ∈ blockFnField y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  | algebraMap m =>
    rw [eq_intCast]
    exact intCast_mem _ m
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem blockFnField_addBlock (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y n 1) :
    blockFnField (addBlock y v) = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨pk, pi⟩, ⟨qk, qi⟩, hpq, rfl⟩
    simp only at hpq
    subst hpq
    cases pk with
    | none =>
      set P : Ω := ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) with hP
      have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have h1 := chartRingZ_le_blockFnField y c (hv pi c hc)
      have h2 := chartRingZ_le_blockFnField y c (hv qi c hc)
      have : v pi / v qi = (v pi * P) / (v qi * P) := (mul_div_mul_right _ _ hP0).symm
      change v pi / v qi ∈ blockFnField y
      rw [this]
      exact div_mem h1 h2
    | some k =>
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, pi⟩, ⟨k, qi⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨⟨some p.1, p.2⟩, ⟨some q.1, q.2⟩, by simp [hpq], rfl⟩

theorem isArithVar_addBlock {D : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hv : ∀ j, v j ∈ chartLat y n 1) (hg : KH.GeneratesOn y n v) :
    IsArithVar (mCoordIdeal (addBlock y v)) (D + 1) := by
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hA.2.1.2.2
  refine CoordArithOfFnField.proof K ι (Option K) (addIdx ι r) Ω y (addBlock y v) (D + 1) ⟨none⟩ ?_
    (blockFnField_addBlock y n v c hc hv).symm hA
  rintro (_ | k)
  · obtain ⟨j, hj⟩ := exists_ne_zero_of_generatesOn y n v c hc hg
    exact ⟨j, hj⟩
  · exact ⟨c k, hc k⟩


omit [CharZero Ω] in
theorem isMultiHomog_rename_none [DecidableEq K] {ι' : Type} [Fintype ι'] {g : MRing (fun _ : Unit => ι')} {e : Unit → ℕ}
    (hg : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (fun p : Σ _ : Unit, ι' =>
      (⟨none, Fintype.equivFin ι' p.2⟩ : Σ k, addIdx ι (Fintype.card ι') k)) g)
      (blockDeg (none : Option K) (e ())) := by
  classical
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    obtain ⟨-, h2⟩ := Sigma.mk.inj h
    exact congrArg (Sigma.mk ()) ((Fintype.equivFin ι').injective (eq_of_heq h2))
  intro m hm k
  rw [support_rename_of_injective hinj] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  cases k with
  | none =>
    have hterm : ∀ i : Fin (Fintype.card ι'),
        (Finsupp.mapDomain φ m0) ⟨none, i⟩ = m0 ⟨(), (Fintype.equivFin ι').symm i⟩ := by
      intro i
      have : (⟨none, i⟩ : Σ k, addIdx ι (Fintype.card ι') k) = φ ⟨(), (Fintype.equivFin ι').symm i⟩ := by
        simp [hφ]
      rw [this, Finsupp.mapDomain_apply_of_injective hinj]
    change ∑ i : Fin (Fintype.card ι'), (Finsupp.mapDomain φ m0) ⟨none, i⟩ = _
    simp only [hterm]
    rw [Fintype.sum_equiv (Fintype.equivFin ι').symm (fun i => m0 ⟨(), (Fintype.equivFin ι').symm i⟩)
      (fun j => m0 ⟨(), j⟩) (fun _ => rfl)]
    have := hg m0 hm0 ()
    simp only [blockDeg, if_true]
    rw [← this]
  | some k =>
    have hterm : ∀ i, (Finsupp.mapDomain φ m0) ⟨some k, i⟩ = 0 := by
      intro i
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨p, hp⟩
      simp only [hφ] at hp
      exact absurd (congrArg Sigma.fst hp) (by simp)
    simp [hterm, blockDeg]


omit [CharZero Ω] in
theorem blockBirational_addBlock [DecidableEq K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (x' : ι' → Ω)
    (hb : Birational (fun p : Σ _ : Unit, ι' => x' p.2)) :
    BlockBirational (addBlock y (liftCoords x')) (none : Option K) := by
  intro d g h hg hh hne
  obtain ⟨e, g', h', hg', hh', hne', hs⟩ :=
    hb (aeval (addBlock y (liftCoords x')) g / aeval (addBlock y (liftCoords x')) h)
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hev : ∀ f : MRing (fun _ : Unit => ι'), aeval (addBlock y (liftCoords x')) (rename φ f) =
      aeval (fun p : Σ _ : Unit, ι' => x' p.2) f := by
    intro f
    have hc : addBlock y (liftCoords x') ∘ φ = fun p => x' p.2 := by
      funext p
      simp [hφ, addBlock, liftCoords]
    rw [aeval_rename, hc]
  refine ⟨e (), rename φ g', rename φ h', isMultiHomog_rename_none hg', isMultiHomog_rename_none hh', ?_, ?_⟩
  · rw [hev]
    exact hne'
  · rw [hev, hev, hs]
    field_simp


omit [CharZero Ω] in
theorem isMultiHomogIdeal_top : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
  ⟨{1}, fun f hf => ⟨0, by rw [Set.mem_singleton_iff.mp hf]; exact Inter.AvoidRing.isMultiHomog_one⟩,
    Ideal.span_singleton_one.symm⟩

end LiftBlockGraph

end

end GroundTheory.Heights₂.Heights.Targets
end
