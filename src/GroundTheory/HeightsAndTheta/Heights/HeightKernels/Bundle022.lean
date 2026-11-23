module

public import Aesop.BuiltinRules
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
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
import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂]

def intCoordSubst (A : Matrix T T₂ ℤ) : MRing (dualBlocks T₂) →ₐ[ℤ] MRing (dualBlocks T) :=
  aeval fun p => ∑ t, C (A t p.2) * X (⟨(), t⟩ : Σ _ : Unit, T)

def intCoordPt (A : Matrix T T₂ ℤ) (z : (Σ _ : Unit, T) → ℂ) : (Σ _ : Unit, T₂) → ℂ :=
  fun p => ∑ t, z ⟨(), t⟩ * (A t p.2 : ℂ)

theorem intCoordPt_ne_zero {A : Matrix T T₂ ℤ} (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    {z : (Σ _ : Unit, T) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, intCoordPt A z ⟨k, i⟩ ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := hA
  rintro ⟨⟩
  obtain ⟨t, ht⟩ := hz ()
  by_contra h
  push Not at h
  apply ht
  have h1 : ∀ t', (((A * B) t' t : ℤ) : ℂ) = ∑ s, (A t' s : ℂ) * (B s t : ℂ) := by
    intro t'
    simp [Matrix.mul_apply]
  have key : z ⟨(), t⟩ = ∑ s, intCoordPt A z ⟨(), s⟩ * (B s t : ℂ) := by
    simp only [intCoordPt, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← h1, hB, Matrix.one_apply]
    simp
  rw [key]
  exact Finset.sum_eq_zero fun s _ => by rw [h s, zero_mul]

def intCoordLine (A : Matrix T T₂ ℤ) (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T) where
  a := L.a
  h z := L.h (intCoordPt A z)
  pos z hz := L.pos _ (intCoordPt_ne_zero hA hz)
  smul c z hc := by
    have hz : intCoordPt A (fun p => c p.1 * z p) = fun p => c p.1 * intCoordPt A z p := by
      funext p
      obtain ⟨⟨⟩, s⟩ := p
      simp only [intCoordPt, Finset.mul_sum, mul_assoc]
    rw [hz, L.smul c _ hc]

def IntCoordChange.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (hAB : A * B = 1), B * A = 1 → ∀ (II : IntersectionSystem),
    IsIntersectionSystem II → ∀ (P : Ideal (MRing (dualBlocks T₂))) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)), 1 ≤ n → IsArithVar P n → (∀ j, IsSmoothHerm (L j)) →
    II Unit (dualBlocks T) (P.map (intCoordSubst A)) n (fun j => intCoordLine A ⟨B, hAB⟩ (L j)) =
      II Unit (dualBlocks T₂) P n L

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

def DualGeomDegCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
        ∑ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ClosedPointAffineChart

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')


omit [Fintype T] in
theorem ratio_mem (t u : T) : y ⟨(), u⟩ / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨⟨(), u⟩, rfl⟩


omit [Fintype T] in
theorem mem_chart_of_mem_curveRing {b : K'} (hb : b ∈ curveRing y) (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    b ∈ chartRingZ y (fun _ => t) :=
  mem_curveRing.mp hb (fun _ => t) (fun _ => ht)


omit [Fintype T] in
theorem mem_curveRing_of_forall {b : K'}
    (h : ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t)) : b ∈ curveRing y := by
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := h (c ()) (hc ())
  rwa [← hc'] at h1


omit [Fintype T] in
theorem div_pow_mem_of_mem_chartLat {e : ℕ} {g : K'} (hg : g ∈ chartLat y 1 e) (t : T)
    (ht : y ⟨(), t⟩ ≠ 0) : g / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t) := by
  have h : g * ∏ k : Unit, y ⟨k, t⟩ ^ (-((e : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y (fun _ => t) :=
    hg (fun _ => t) (fun _ => ht)
  simpa [zpow_neg, zpow_natCast, div_eq_mul_inv] using h


omit [Fintype T] in
theorem exists_mul_inv_mem {m : Ideal (curveRing y)} [m.IsPrime] {e : ℕ} {g : K'} (hg0 : g ≠ 0)
    (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (y ⟨(), t⟩ ^ e / g) ∈ chartRingZ y (fun _ => t) := by
  by_contra hcon
  push Not at hcon
  let R : Subring K' := (chartRingZ y (fun _ => t)).toSubring
  have hBR : curveRing y ≤ R := fun b hb => mem_chart_of_mem_curveRing y hb t ht
  let S' : Submonoid R := m.primeCompl.map (Subring.inclusion hBR)
  let z : R := ⟨g / y ⟨(), t⟩ ^ e, div_pow_mem_of_mem_chartLat y hgL t ht⟩
  have hyt : y ⟨(), t⟩ ^ e ≠ 0 := pow_ne_zero _ ht
  have hdisj : Disjoint ((Ideal.span {z} : Ideal R) : Set R) (S' : Set R) := by
    rw [Set.disjoint_left]
    intro r hr hrS
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hrS
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : (w : K') * (g / y ⟨(), t⟩ ^ e) = (s : K') := congrArg Subtype.val hw
    apply hcon s hs
    rw [← h1, show (w : K') * (g / y ⟨(), t⟩ ^ e) * (y ⟨(), t⟩ ^ e / g) = (w : K') by field_simp]
    exact w.2
  obtain ⟨q, hq, hzq, hqS⟩ := Ideal.exists_le_prime_disjoint _ S' hdisj
  obtain ⟨W, hRW, hunit, hlt⟩ := ClosedPointUnitSection.exists_valuationSubring R q
  have hBW : ∀ b : curveRing y, (b : K') ∈ W := fun b => hRW (Subring.inclusion hBR b)
  have hBunit : ∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1 := by
    intro b hb
    apply hunit (Subring.inclusion hBR b)
    intro hbq
    exact Set.disjoint_left.mp hqS hbq (Submonoid.mem_map.mpr ⟨b, hb, rfl⟩)
  have h1 := hW W hBW hBunit t
  have h2 : W.valuation (z : K') < 1 := hlt z (hzq (Ideal.subset_span (Set.mem_singleton z)))
  have h3 : (z : K') * (y ⟨(), t⟩ ^ e / g) = 1 := by
    show g / y ⟨(), t⟩ ^ e * (y ⟨(), t⟩ ^ e / g) = 1
    field_simp
  have h4 := congrArg W.valuation h3
  rw [map_mul, map_one] at h4
  have h5 : W.valuation (y ⟨(), t⟩ ^ e / g) ≤ 1 := (W.valuation_le_one_iff _).mpr h1
  have h6 : W.valuation (z : K') * W.valuation (y ⟨(), t⟩ ^ e / g) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h5) h2
  exact ne_of_lt h6 h4

theorem exists_mul_div_mem_curveRing {m : Ideal (curveRing y)} (hm : m.IsMaximal) {e : ℕ} {g : K'}
    (hg0 : g ≠ 0) (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    {h : K'} (hh : ∀ t : T, y ⟨(), t⟩ ≠ 0 → h / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t)) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (h / g) ∈ curveRing y := by
  classical
  have := hm.isPrime
  have key : ∀ t : T, ∃ s : curveRing y, s ∉ m ∧
      (y ⟨(), t⟩ ≠ 0 → (s : K') * (h / g) ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, fun h1 => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun h' => (h' ht).elim⟩
    · obtain ⟨s, hs, hsm⟩ := exists_mul_inv_mem y hg0 hgL hW t ht
      refine ⟨s, hs, fun _ => ?_⟩
      have e1 : (s : K') * (h / g) = h / y ⟨(), t⟩ ^ e * ((s : K') * (y ⟨(), t⟩ ^ e / g)) := by
        field_simp
      rw [e1]
      exact mul_mem (hh t ht) hsm
  choose S hSm hS using key
  refine ⟨∏ t, S t, fun hmem => ?_, ?_⟩
  · obtain ⟨t, -, ht⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hSm t ht
  · apply mem_curveRing_of_forall
    intro t ht
    have e1 : ((∏ u, S u : curveRing y) : K') * (h / g) =
        (∏ u ∈ Finset.univ.erase t, (S u : K')) * ((S t : K') * (h / g)) := by
      push_cast
      rw [← Finset.mul_prod_erase Finset.univ (fun u => (S u : K')) (Finset.mem_univ t)]
      ring
    rw [e1]
    exact mul_mem (prod_mem fun u _ => mem_chart_of_mem_curveRing y (S u).2 t ht) (hS t ht)

end ClosedPointAffineChart

theorem ClosedPointChart.proof (hU : ClosedPointUnitSection.Statement) : ClosedPointChart.Statement := by
  intro T _ K' _ _ y hy m hm
  obtain ⟨e, g, he, hg0, hgL, hW⟩ := hU T K' y hy m hm
  have := hm.isPrime
  obtain ⟨W, hBW, hBunit, hBlt⟩ := ClosedPointUnitSection.exists_valuationSubring (curveRing y) m
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => W.valuation (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hratio : ∀ u, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ W := by
    intro u
    apply W.mem_of_valuation_le_one
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hyt))).mpr
      (ht u (Finset.mem_univ _))
  have hchartW : ∀ x ∈ chartRingZ y (fun _ => t), x ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
      exact hratio u
    | algebraMap r => rw [eq_intCast]; exact intCast_mem W r
    | add x z _ _ hx hz => exact add_mem hx hz
    | mul x z _ _ hx hz => exact mul_mem hx hz
  have hinv : y ⟨(), t⟩ ^ e / g ∈ W := hW W hBW hBunit t
  have hgt : g / y ⟨(), t⟩ ^ e ∈ W :=
    hchartW _ (ClosedPointAffineChart.div_pow_mem_of_mem_chartLat y hgL t hyt)
  have hval : W.valuation (y ⟨(), t⟩ ^ e / g) = 1 := by
    have h1 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) = 1 := by
      rw [← map_mul, show y ⟨(), t⟩ ^ e / g * (g / y ⟨(), t⟩ ^ e) = 1 by
        field_simp [pow_ne_zero e hyt]]
      exact map_one _
    have h2 := (W.valuation_le_one_iff _).mpr hinv
    have h3 := (W.valuation_le_one_iff _).mpr hgt
    by_contra hne
    have h4 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) (lt_of_le_of_ne h2 hne)
    exact ne_of_lt h4 h1
  have hmon : ∀ u t' : T, y ⟨(), t'⟩ ≠ 0 →
      y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e ∈ chartRingZ y (fun _ => t') := by
    intro u t' ht'
    have e1 : y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e =
        (y ⟨(), u⟩ / y ⟨(), t'⟩) * (y ⟨(), t⟩ / y ⟨(), t'⟩) ^ (e - 1) := by
      rw [div_pow, div_mul_div_comm, mul_pow_sub_one (by omega : e ≠ 0)]
    rw [e1]
    exact mul_mem (ClosedPointAffineChart.ratio_mem y t' u)
      (pow_mem (ClosedPointAffineChart.ratio_mem y t' t) _)
  have hpow : y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) = y ⟨(), t⟩ ^ e := mul_pow_sub_one (by omega) _
  obtain ⟨s0, hs0, hs0B⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon t)
  have ha0 : (⟨_, hs0B⟩ : curveRing y) ∉ m := by
    intro hmem
    have h1 := hBlt _ hmem
    change W.valuation ((s0 : K') * (y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) / g)) < 1 at h1
    rw [map_mul, hpow, hval, hBunit s0 hs0, one_mul] at h1
    exact lt_irrefl _ h1
  refine ⟨t, hyt, fun u => ?_⟩
  obtain ⟨su, hsu, hsuB⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon u)
  refine ⟨⟨_, hsuB⟩ * s0, su * ⟨_, hs0B⟩, fun hmem => ?_, ?_⟩
  · rcases hm.isPrime.mem_or_mem hmem with h | h
    · exact hsu h
    · exact ha0 h
  · push_cast
    field_simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace VerticalPointLength

theorem maximal_and_mult_eq (hCh : VertPointChart.Statement) (hMC : VertPointMultChart.Statement)
    (hSQ : SectionQuotLocal.Statement) {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} {s : MRing (fun _ : Unit => T)} (hP : IsArithVar (mCoordIdeal y) 1)
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {W : Ideal (MRing (fun _ : Unit => T))}
    (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W = locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) := by
  obtain ⟨t, ht⟩ := hW.2 ()
  obtain ⟨hmax, hrat, hmem⟩ := hCh T K' y s hP hs hsP W hW t ht
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨a, b, -, hb, hab⟩ := (hmem 1 s hs).mp hsW
  rw [pow_one] at hab
  refine ⟨hmax, ?_⟩
  rw [hMC T K' y s hP hs hsP W hW t ht a b hb hab,
    hSQ T K' y s hP hs hsP _ t hmax.isPrime hrat a b hb hab]

end VerticalPointLength

theorem VertPointLength.proof (hCh : VertPointChart.Statement)
    (hInj : VertPointInj.Statement) (hSurj : VertPointSurj.Statement)
    (hMC : VertPointMultChart.Statement) (hSQ : SectionQuotLocal.Statement) :
    VertPointLength.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj T K' y s hP hs hsP,
      fun m hm => hSurj T K' y s hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := VerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualStdBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) * II Unit (PBlk i) ⊥ i (fun _ => fsMulti (PBlk i))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField Matrix

noncomputable section

theorem single_mem_dualLattice_standard (K : Type) [Field K] [NumberField K] {i : ℕ} (j : Fin i) :
    (Pi.single j 1 : Fin i → K) ∈ dualLattice (HermLattice.standard K i) := by
  intro x hx
  rw [single_one_dotProduct]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    by_cases h : j = k
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul a y _ hy =>
    obtain ⟨c, hc⟩ := hy
    exact ⟨a * c, by simp [hc, Algebra.smul_def]⟩

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def dualStdCoordMat (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    ∀ _ : Unit, Fin i → T → ℤ :=
  fun _ j t => b.repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩ t


omit [DecidableEq T] in
theorem dualStdCoordMat_sum (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (j : Fin i) :
    ∑ t, dualStdCoordMat b () j t • (b t : Fin i → K) = Pi.single j 1 := by
  have h := congrArg (fun v : dualLattice (HermLattice.standard K i) => (v : Fin i → K))
    (b.sum_repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

def DualStdBasePtFree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))

def DualStdImageBot.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) = ⊥

def DualStdGenDeg.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (G : GenFibre (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))))
    (J : IFamily G.Φ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))),
    1 ≤ i → IsFieldIntersection J →
    J (fibreIdeal Sum.inr G) 0 Fin.elim0 = (Module.finrank ℚ K : ℤ)

def DualStdMetricPull.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ z ∈ mcPts (dualIdeal b),
      (dualLine (HermLattice.standard K i) b hb).h z =
        (fsMulti (PBlk i)).h (linApply (ι₂ := PBlk i) (dualStdCoordMat b) z)

end

end GroundTheory.Heights₂.Heights
end
