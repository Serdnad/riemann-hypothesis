module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace ShiftedNefBig

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_one_add (W : Ideal (MRing ι)) (a b : K → ℤ) (q : ℤ) :
    geoNum 1 W (fun _ => q • a + b) = q * geoNum 1 W (fun _ => a) + geoNum 1 W (fun _ => b) := by
  simp only [geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]
  · simp

theorem geoNum_one_one_nonneg (W : Ideal (MRing ι)) : 0 ≤ geoNum 1 W (fun _ => (1 : K → ℤ)) := by
  simp only [geoNum]
  split_ifs with h
  · refine Finset.sum_nonneg fun k _ => mul_nonneg zero_le_one ?_
    refine finsum_nonneg fun W' => finsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) ?_
    split_ifs <;> positivity
  · exact le_rfl

end ShiftedNefBig


open ShiftedNefBig in
theorem ShiftNefBig.proof (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement)
    (hB : NefPlusAmpleDegree.Statement) : ShiftNefBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 _ har _ hP0 hs hnef hc q _
  have ha : (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a = (q : ℤ) • A.a + 1 := by
    show (q : ℤ) • A.a + (1 : ℤ) • (fsH ι).a = _
    rw [one_smul]
    rfl
  refine ⟨hP0, PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hs (Nat.cast_nonneg q) zero_le_one,
    HermLine.zcomb_isConjInvariantH hc (fsH_isConjInvariantH ι) _ _, ?_, ?_⟩
  · rw [ha]
    intro W hW hPW hch hdim
    rw [geoNum_one_add]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg q) (hnef W hW hPW hch hdim)) (geoNum_one_one_nonneg W)
  · rw [ha]
    exact hB K ι (mCoordIdeal y) D A.a har (nefOnGenericDeg_of_semipos NefOnGenericOfSemipos.proof hD hP0 hs) q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}


omit [Fintype K] in
theorem shift_succ_sub_one (b : K → ℤ) (j : ℕ) :
    (b + fun _ => ((j + 1 : ℕ) : ℤ)) - 1 = b + fun _ => (j : ℤ) := by
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
  push_cast
  ring


omit [∀ k, Fintype (ι k)] in
theorem pow_mul_mem_chartLatQ (c : ∀ k, ι k) (b : K → ℤ) {s : Ω} (hs : s ∈ chartLatQ y b 1) (j : ℕ) :
    (∏ k, y ⟨k, c k⟩) ^ j * s ∈ chartLatQ y (b + fun _ => (j : ℤ)) 1 := by
  induction j with
  | zero =>
    rw [pow_zero, one_mul]
    have h0 : (b + fun _ => ((0 : ℕ) : ℤ)) = b := by funext k; simp
    rw [h0]
    exact hs
  | succ j ih =>
    rw [← shift_succ_sub_one] at ih
    have h := mul_mem_chartLatQ (c := c) (b + fun _ => ((j + 1 : ℕ) : ℤ)) ih
    rwa [← mul_assoc, ← pow_succ'] at h

theorem finiteDimensional_chartLatQ (hfin : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (b : K → ℤ) : FiniteDimensional ℚ (chartLatQ y b 1) := by
  classical
  obtain ⟨S, hS⟩ := hfin K ι Ω y b 1 hy
  let T : Finset Ω := S.image Subtype.val
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ (T : Set Ω)) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  have ht : (⟨(N : Ω) * s, hNs⟩ : chartLat y b 1) ∈ AddSubsemigroup.closure (S : Set (chartLat y b 1)) := by
    rw [hS]
    trivial
  have hQ : (N : Ω) * s ∈ Submodule.span ℚ (T : Set Ω) := by
    have hall : ∀ x : chartLat y b 1, x ∈ AddSubsemigroup.closure (S : Set (chartLat y b 1)) → (x : Ω) ∈ Submodule.span ℚ (T : Set Ω) := by
      intro x hx
      induction hx using AddSubsemigroup.closure_induction with
      | mem x hx =>
        apply Submodule.subset_span
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      | add x z hx hz ihx ihz =>
        exact Submodule.add_mem _ ihx ihz
    exact hall _ ht
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hQ

theorem finrank_shift_le (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (j : ℕ) :
    Module.finrank ℚ (chartLatQ y (b + fun _ => (j : ℤ)) 1) ≤ Module.finrank ℚ (chartLatQ y b 1) +
      ∑ i ∈ Finset.range j, Module.finrank ℚ (chartLatQ y (b + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
        chartDivSec y c (b + fun _ => ((i + 1 : ℕ) : ℤ))) := by
  induction j with
  | zero =>
    have h0 : (b + fun _ => ((0 : ℕ) : ℤ)) = b := by funext k; simp
    rw [h0]
    simp
  | succ j ih =>
    have h := finrank_chartLatQ_le hc (b + fun _ => ((j + 1 : ℕ) : ℤ))
    rw [shift_succ_sub_one] at h
    rw [Finset.sum_range_succ]
    omega

end Shift

theorem ShiftSectionBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : ShiftQuotientBound.Statement) :
    ShiftSectionBound.Statement := by
  intro K _ ι _ Ω _ _ y D a m hD hV hB
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  choose c hc using hy
  have hC := fun i : ℕ => hQ K ι Ω y D a (fun _ => ((i + 1 : ℕ) : ℤ)) c hD hV hB hc
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range m, C i,
    ((Filter.eventually_all_finset (Finset.range m)).mpr fun i _ => hC i).mono fun n hn => ⟨?_, ?_⟩⟩
  ·
    have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) ((n : ℤ) • a + fun _ => (m : ℤ))
    have hh : (∏ k, y ⟨k, c k⟩) ^ m ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)
    let φ : chartLatQ y ((n : ℤ) • a) 1 →ₗ[ℚ] chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1 :=
      { toFun := fun s => ⟨(∏ k, y ⟨k, c k⟩) ^ m * s, pow_mul_mem_chartLatQ c _ s.2 m⟩
        map_add' := fun s t => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r s => Subtype.ext (mul_smul_comm r _ (s : Ω)) }
    have hinj : Function.Injective φ := fun s t hst =>
      Subtype.ext (mul_left_cancel₀ hh (congrArg Subtype.val hst))
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective hinj
  · have h := finrank_shift_le c hc ((n : ℤ) • a) m
    have h' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) +
          ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
            chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) := by
      exact_mod_cast h
    have hs : ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
          chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) ≤
        (∑ i ∈ Finset.range m, C i) * (n : ℝ) ^ (D - 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => hn i hi
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (m N : ℕ) (v : Fin N → Ω),
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    ∃ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N)) (P0' : Ideal (MRing (addIdx ι N))),
      B.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) ∧ IsConjInvariantH B ∧ P0' ≤ mCoordIdeal (addBlock y v) ∧
      IsSemipositiveRel P0' (mCoordIdeal (addBlock y v)) B ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
        secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockOldPartSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (m N : ℕ) (v : Fin N → Ω),
    (∀ j, v j ∈ chartLat y a m) → KH.GeneratesOn y (fun k => (m : ℤ) * a k) v →
    ∀ x ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal (addBlock y v)), basePart₂ z = x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def PowerBlockPointNorm.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N)),
    ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} → B.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) →
    (∀ j, v j ∈ chartLat y A.a m) →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    ∀ (q : ℕ) (F : MRing (addIdx ι N)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F (blockDeg (none : Option K) q) →
      ContinuousOn (secNormAt y A (m * q) (aeval (addBlock y v) F)) (mcPts (mCoordIdeal y)) ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)),
        secNormAt y A (m * q) (aeval (addBlock y v) F) (basePart₂ z) =
          ‖eval z (map (Int.castRingHom ℂ) F)‖ / B.h z ^ q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockVeronese.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (N : ℕ) (v : Fin N → Ω),
      AddSubgroup.closure (Set.range v) = chartLat y a m ∧
      KH.GeneratesOn y (fun k => (m : ℤ) * a k) v ∧
      ∀ n : ℕ, 1 ≤ n → chartLat y a (m * n) = secM (addBlock y v) (blockDeg (none : Option K) n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerHeightsirational.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, w j ∈ chartLat y a 1) →
    KH.GeneratesOn y a w → 0 < genDeg (mCoordIdeal y) D a →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (N : ℕ) (v : Fin N → Ω), AddSubgroup.closure (Set.range v) = chartLat y a m →
      BlockBirational (addBlock y v) (none : Option K)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionNormSqExtension.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω),
    IsSmoothHerm A → IsConjInvariantH A →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    ∃ S : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S {x | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} ∧
      (∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x) ∧
      (∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) ∧
      (∀ x : (Σ k, ι k) → ℂ, S (fun p => (starRingEnd ℂ) (x p)) = S x) ∧
      (∀ x ∈ mcPts (mCoordIdeal y), S x = ∑ j, secNormAt y A m (v j) x ^ 2) ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ w : (Σ k, addIdx ι N k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w →
        leviForm (fun z' : (Σ k, addIdx ι N k) → ℂ =>
            Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) z w =
          (m : ℝ) * leviForm (fun x => Real.log (A.h x)) (basePart₂ z) (basePart₂ w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def PowerBlockMeasure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N D : ℕ) (v : Fin N → Ω) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N))
    (J : Ideal (MRing (addIdx ι N))) (R : AnRes (mCoordIdeal (addBlock y v)) J D) [MeasurableSpace R.X]
    [BorelSpace R.X] (dV : Measure R.X),
    IsSmoothHerm A → IsSmoothHerm B → B.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) → IsSmoothVolume R.A dV →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    ∃ μ : Measure ((Σ k, ι k) → ℂ), IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧
      IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      ∀ (q : ℕ) (F : MRing (addIdx ι N)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F (blockDeg (none : Option K) q) →
        sectionL2Norm μ y A (m * q) (aeval (addBlock y v) F) =
          Real.sqrt ((1 / 2) *
            ((∫ x, (‖eval (R.lift x x) (map (Int.castRingHom ℂ) F)‖ / B.h (R.lift x x) ^ q) ^ 2 ∂dV) +
              ∫ x, (‖eval (conjPt (R.lift x x)) (map (Int.castRingHom ℂ) F)‖ /
                B.h (conjPt (R.lift x x)) ^ q) ^ 2 ∂dV))

namespace PowerBlockDiag

open ProjLine PowerBlockProjectiveLine

end PowerBlockDiag

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type} {ι : K → Type}

def oldV (N : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι N k) := fun p => ⟨some p.1, p.2⟩

theorem isBlockMap_oldV (N : ℕ) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (ι := ι) (ι' := addIdx ι N) some (oldV N) := by
  refine ⟨Option.some_injective K, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Option.some_injective K (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨_ | k, i⟩ ⟨k', hk'⟩
    · exact absurd hk' (Option.some_ne_none k')
    · exact ⟨⟨k, i⟩, rfl⟩

end Objects

def AddBlockIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N)),
    IsArithVar (mCoordIdeal y) (D + 1) → 1 ≤ m →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    B.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) →
    L.a = ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg some (fun k => (m : ℤ) * A.a k) →
    (∀ z, L.h z = A.h (basePart₂ z) ^ m) →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    IsIsometricOn (mCoordIdeal (addBlock y v)) B L

namespace PowerBlockProjectiveLine

open ProjLine

end PowerBlockProjectiveLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
