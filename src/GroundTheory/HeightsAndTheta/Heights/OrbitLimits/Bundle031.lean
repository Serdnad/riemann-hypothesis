module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
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
import Mathlib.Tactic.Linter.HaveILetI
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def liftCoords {ι' : Type} [Fintype ι'] {Ω : Type} (x' : ι' → Ω) : Fin (Fintype.card ι') → Ω :=
  fun j => x' ((Fintype.equivFin ι').symm j)

def LiftBlockDatum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a : ℕ)
    (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    1 ≤ a → (∀ j, x' j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) x' →
    Birational (fun p : Σ _ : Unit, ι' => x' p.2) →
    ∃ d : HSMBlockDatum D (Option K) (addIdx ι (Fintype.card ι')) Ω,
      d.y = addBlock y (liftCoords x') ∧ d.k₀ = none ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), ∀ j : Fin (Fintype.card ι'),
        secNormAt y N a (liftCoords x' j) (basePart₂ z) * d.A.h z = ‖z ⟨none, j⟩‖) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal d.y), basePart₂ z = w

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphFactor.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a r : ℕ) (v : Fin r → Ω),
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ Φ : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} ∧
      (∀ w : (Σ k, ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → 0 < Φ w) ∧
      (∀ (c : K → ℂ) (w : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
        Φ (fun p => c p.1 * w p) = (∏ k, ‖c k‖ ^ ((a • N.a) k)) ^ 2 * Φ w) ∧
      (∀ w : (Σ k, ι k) → ℂ, Φ (fun p => (starRingEnd ℂ) (w p)) = Φ w) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a * Real.sqrt (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2) =
          ‖z ⟨none, j⟩‖ * Real.sqrt (Φ (basePart₂ z))) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ ξ : (Σ k, addIdx ι r k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z ξ →
        leviForm (fun z => Real.log (Φ (basePart₂ z))) z ξ =
          leviForm (fun z : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2)) z ξ)

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a r : ℕ) (v : Fin r → Ω),
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r), A.a = _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) ∧ IsConjInvariantH A ∧
      IsSemipositiveRel (mCoordIdeal (addBlock y v)) (mCoordIdeal (addBlock y v)) A ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * A.h z = ‖z ⟨none, j⟩‖

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) (r : ℕ) (v : Fin r → Ω),
    (∀ j, v j ∈ chartLat y n 1) → KH.GeneratesOn y n v →
    ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal (addBlock y v)), basePart₂ z = w

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

noncomputable section

theorem CurveFieldNumber.proof (hR1 : RegularityFunctionFieldNumber.Statement) : CurveFieldNumber.Statement := by
  intro K _ ι _ Ω _ y hA hB
  set P := mCoordIdeal y with hPdef
  have : P.IsPrime := hA.2.1.1
  obtain ⟨hF, hN⟩ := hR1 K ι P hA
  let L := FractionRing (MvPolynomial K Ω)

  let j : MRing ι ⧸ P →+* L :=
    (algebraMap (MvPolynomial K Ω) L).comp (RingHom.kerLift (mConeMap y : MRing ι →+* MvPolynomial K Ω))
  have hj : Function.Injective j :=
    (IsFractionRing.injective (MvPolynomial K Ω) L).comp (RingHom.kerLift_injective _)
  let Φ : FractionRing (MRing ι ⧸ P) →+* L := IsFractionRing.lift hj
  let c : Ω →+* L := (algebraMap (MvPolynomial K Ω) L).comp MvPolynomial.C
  have hΦ : ∀ f, Φ (algebraMap _ _ (Ideal.Quotient.mk P f)) = algebraMap _ L (mConeMap y f) := fun f =>
    (IsFractionRing.lift_algebraMap hj _).trans (congrArg (algebraMap (MvPolynomial K Ω) L)
      (RingHom.kerLift_mk (mConeMap y : MRing ι →+* MvPolynomial K Ω) f))

  have hform : ∀ {g : MRing ι} {a : K → ℕ}, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a →
      Φ (algebraMap _ _ (Ideal.Quotient.mk P g)) = c (aeval y g) * algebraMap _ L (∏ k, (X k : MvPolynomial K Ω) ^ a k) := by
    intro g a hg
    rw [hΦ, LowerBoundFree.mConeMap_of_isMultiHomog y hg, map_mul]; rfl
  have hT : ∀ a : K → ℕ, algebraMap (MvPolynomial K Ω) L (∏ k, (X k : MvPolynomial K Ω) ^ a k) ≠ 0 := fun a =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ (X_ne_zero k))

  have hmem : ∀ {g : MRing ι} {a : K → ℕ}, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a → aeval y g = 0 → g ∈ P := by
    intro g a hg h0
    show mConeMap y g = 0
    rw [LowerBoundFree.mConeMap_of_isMultiHomog y hg, h0, map_zero, zero_mul]

  have heq : (funField P).map Φ = c.range := by
    apply le_antisymm
    · rw [Subring.map_le_iff_le_comap, funField, Subring.closure_le]
      rintro x ⟨u, v, a, hv, hu, hvf, rfl⟩
      have hvP : v ∉ P := fun h => nonZeroDivisors.ne_zero hv ((Ideal.Quotient.eq_zero_iff_mem).2 h)
      have hvy : aeval y v ≠ 0 := fun h => hvP (hmem hvf h)
      refine ⟨aeval y u / aeval y v, ?_⟩
      have h1 := congrArg Φ (IsLocalization.mk'_spec (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩)
      rw [map_mul, hform hvf, hform hu] at h1
      have hcv : c (aeval y v) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hvy
      rw [map_div₀, div_eq_iff hcv]
      exact mul_right_cancel₀ (hT a) (by rw [← h1]; ring)
    · rintro _ ⟨s, rfl⟩
      obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
      have hhP : h ∉ P := fun hP => by
        have : mConeMap y h = 0 := hP
        rw [LowerBoundFree.mConeMap_of_isMultiHomog y hh] at this
        exact mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective K Ω)).2 hh0)
          (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) this
      obtain ⟨x, hx⟩ := exists_funField_mul_eq hg hh hhP
      refine ⟨x, x.2, ?_⟩
      have h1 := congrArg Φ hx
      rw [map_mul, hform hh, hform hg, hgs, map_mul] at h1
      have hch : c (aeval y h) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hh0
      exact mul_right_cancel₀ (mul_ne_zero hch (hT d)) (by rw [h1]; ring)

  have hc : Function.Injective c.rangeRestrict := fun a b h => c.injective (congrArg Subtype.val h)
  let e : funField P ≃+* Ω :=
    ((Subring.equivMapOfInjective (funField P) Φ Φ.injective).trans (RingEquiv.subringCongr heq)).trans
      (RingEquiv.ofBijective c.rangeRestrict ⟨hc, c.rangeRestrict_surjective⟩).symm
  exact @NumberField.of_ringEquiv _ _ hF.toField _ e hN

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem log_regLine_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (s : MRing ι) {ε : ℝ} (hε : 0 < ε) {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((regLine A s ε ha hs).tensor A).h z) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2 := by
  have hh : 0 < A.h z := A.pos z hz
  have hreg : Real.log ((regLine A s ε ha hs).h z) = regLog A s ε z := congrFun (log_regLine A s ε ha hs) z
  have hpos : 0 < (regLine A s ε ha hs).h z := (regLine A s ε ha hs).pos z hz
  show Real.log ((regLine A s ε ha hs).h z * A.h z) = _
  rw [Real.log_mul hpos.ne' hh.ne', hreg]
  unfold regLog normSq
  set x := ‖eval z (map (Int.castRingHom ℂ) s)‖
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hnum : 0 < x ^ 2 + ε * A.h z ^ 2 := by positivity
  have hq : (x / A.h z) ^ 2 + ε = (x ^ 2 + ε * A.h z ^ 2) / A.h z ^ 2 := by
    field_simp
  rw [hq, Real.log_div hnum.ne' (pow_pos hh 2).ne', Real.log_pow]
  push_cast
  ring

theorem PoincareLelongLimit.proof (hInt : PtsIntegrableStatement) (hLel : LelongSectionLimit.Statement) :
    PoincareLelongLimit.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hAdd := Inter.PtsAddFirst.proof hInt
  have key : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) := by
    intro ε hε
    have h1 := Inter.ptsIntegral_add_first_log hAdd (Q := P) (e := n) (L := L)
      (M := regLine A s ε ha hsa) (N := A) (D := B) hP hL (isSmoothHerm_regLine hA hε ha hsa) hA hB hBa
    rw [log_regLine] at h1
    have h2 : ptsIntegral P (Fin.cons (fun z => Real.log (((regLine A s ε ha hsa).tensor A).h z)) (pot L))
          (fun z => Real.log (B.h z)) =
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) := by
      refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
      refine Fin.cases ?_ (fun i => ?_) j
      · intro z hz
        simp only [Fin.cons_zero]
        exact log_regLine_tensor A s hε ha hsa z hz.1
      · intro z _
        simp only [Fin.cons_succ]
    rw [← h2, h1]
    ring
  exact ((hLel K ι P n L A B s hP hL hA hB hBa hs).sub_const _).congr'
    (eventually_nhdsWithin_of_forall key)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem chartRadius_smul (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (d : K → ℂ) (hd : ∀ k, d k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => d p.1 * z p) = chartRadius A c z := by
  unfold chartRadius
  rw [A.smul d z hd]
  have hX : (∏ k, ‖d k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd k))
  simp only [norm_mul, mul_zpow, Finset.prod_mul_distrib]
  rw [mul_div_mul_left _ _ hX]


omit [∀ k, Fintype (ι k)] in
theorem chartRadius_conj (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : IsConjInvariantH A) (c : ∀ k, ι k)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => (starRingEnd ℂ) (z p)) = chartRadius A c z := by
  unfold chartRadius
  rw [hA z]
  simp only [Complex.norm_conj]


omit [∀ k, Fintype (ι k)] in
theorem chartRadius_pos (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) : 0 < chartRadius A c z :=
  div_pos (A.pos z fun k => ⟨c k, hz k⟩)
    (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hz k)) _)

end Lemmas

theorem genIndex_map_addEquiv {G : Type*} [AddCommGroup G] (m : G ≃+ G) (A B : AddSubgroup G) :
    genIndex (A.map m.toAddMonoidHom) (B.map m.toAddMonoidHom) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ m.injective,
    AddSubgroup.relIndex_map_map_of_injective _ _ m.injective]

theorem addSubgroup_fg_map {G H : Type*} [AddCommGroup G] [AddCommGroup H] {A : AddSubgroup G} (hA : A.FG)
    (f : G →+ H) : (A.map f).FG := by
  letI : A.FG := hA
  infer_instance

theorem CurveBoxLattice.proof (hF : CurveFieldNumber.Statement) (hE : CurveEmbedOrbit.Statement)
    (hL : ChartLatFull.Statement) (hN : NumberFieldBoxCount.Statement)
    (hG : HilbertSamuel.SectionLatticeFinite.Statement) : CurveBoxLattice.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  have : NumberField Ω := hF K ι Ω y hP hB
  obtain ⟨e, he⟩ := hE K ι Ω y R hP hB hR hRu
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have hBeq : (curveRing y).toAddSubgroup = chartLat y 0 0 := by
    ext s
    simp [mem_curveRing, chartLat]
  have hBfg : (curveRing y).toAddSubgroup.FG := hBeq ▸ hG K ι Ω y 0 0 hy
  have hBfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ (curveRing y).toAddSubgroup :=
    hBeq ▸ hL K ι Ω y hB 0 0
  obtain ⟨C, hC⟩ := hN Ω _ hBfg hBfull
  refine ⟨C, fun τ _ => ?_⟩
  have hu : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  set u := chartUnit y c A.a τ with hu_def
  let m : Ω ≃+ Ω :=
    { toFun := fun x => x / u
      invFun := fun x => x * u
      left_inv := fun x => div_mul_cancel₀ x hu
      right_inv := fun x => mul_div_cancel_right₀ x hu
      map_add' := fun x z => add_div x z u }
  set Λ := (chartLat y A.a τ).map m.toAddMonoidHom with hΛ
  have hΛfg : Λ.FG := addSubgroup_fg_map (hG K ι Ω y A.a τ hy) _
  have hΛfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ Λ := by
    intro x
    obtain ⟨n, hn, hmem⟩ := hL K ι Ω y hB A.a τ (x * u)
    refine ⟨n, hn, ?_⟩
    have : (n : Ω) * x = m ((n : Ω) * (x * u)) := by
      show (n : Ω) * x = (n : Ω) * (x * u) / u
      rw [mul_div_assoc, mul_div_cancel_right₀ x hu]
    rw [this]
    exact AddSubgroup.mem_map_of_mem _ hmem
  have hBmap : (curveMul y u).map m.toAddMonoidHom = (curveRing y).toAddSubgroup := by
    rw [curveMul, AddSubgroup.map_map]
    convert AddSubgroup.map_id _ using 2
    ext x
    show u * x / u = x
    rw [mul_div_cancel_left₀ x hu]
  have hidx : genIndex Λ (curveRing y).toAddSubgroup = genIndex (chartLat y A.a τ) (curveMul y u) := by
    rw [← hBmap, hΛ, genIndex_map_addEquiv]
  let ρ : (Ω →+* ℂ) → ℝ := fun σ => chartRadius A c (fun p => σ (y p)) ^ τ
  have hρpos : ∀ σ, 0 < ρ σ := fun σ =>
    pow_pos (chartRadius_pos A c _ fun k => (map_ne_zero σ).mpr (hc k)) τ
  have hρconj : ∀ σ, ρ (NumberField.ComplexEmbedding.conjugate σ) = ρ σ := by
    intro σ
    simp only [ρ, NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [chartRadius_conj A hA c]
  have hcount := hC Λ hΛfg hΛfull ρ hρpos hρconj
  have hsum : ∑ t ∈ R, Real.log (chartRadius A c t) =
      ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨d, hd, ht⟩ := he t
    rw [ht, chartRadius_smul A c d hd]
  have hρsum : ∑ σ : Ω →+* ℂ, Real.log (ρ σ) =
      (τ : ℝ) * ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Real.log_pow _ _
  have hcard : Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / u)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ} =
      Nat.card {x : Λ // ∀ σ : Ω →+* ℂ, ‖σ (x : Ω)‖ ≤ ρ σ} :=
    Nat.card_congr ((AddSubgroup.equivMapOfInjective _ m.toAddMonoidHom m.injective).toEquiv.subtypeEquiv
      fun s => Iff.rfl)
  rw [hcard, hsum, ← hρsum, chartIndexLog, ← hu_def, ← hidx]
  exact hcount

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxCount.proof (hS : CurveBoxSmall.Statement) (hL : CurveBoxLattice.Statement) :
    CurveBoxCount.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  obtain ⟨C, hC⟩ := hL K ι Ω y A c R hP hB hA hc hR hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have e : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ =
      Real.log (Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ}) := by
    unfold smallSectionCount
    rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun s : chartLat y A.a τ => IsSmallH (mCoordIdeal y) y A τ (s : Ω))
      fun s => hS K ι Ω y A c hP hB hc τ (s : Ω))]
  rw [e]
  exact hC τ hτ

end GroundTheory.Heights₂.Heights.Targets
end
