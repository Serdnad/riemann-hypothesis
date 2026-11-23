module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobenius
public import GroundTheory.GlobalFields.ComplexMultiplication.Uniformization
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
public import GroundTheory.GlobalFields.ComplexMultiplication.UniformizationAddition
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField GroundTheory.Arith.Abelian

universe u

section Twist

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusTwist : WeierstrassCurve F := E.map (frobenius F p)

instance [E.IsElliptic] : (frobeniusTwist E p).IsElliptic := by
  unfold frobeniusTwist; infer_instance

theorem j_frobeniusTwist [E.IsElliptic] : (frobeniusTwist E p).j = E.j ^ p := by
  show (E.map (frobenius F p)).j = _
  rw [map_j, frobenius_def]

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

theorem baseChange_frobeniusTwist :
    (frobeniusTwist E p).baseChange L = (E.baseChange L).map (frobenius L p) := by
  show (E.map (frobenius F p)).map (algebraMap F L) = (E.map (algebraMap F L)).map (frobenius L p)
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [frobenius_def]

theorem nonsingular_pow {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) := by
  rw [baseChange_frobeniusTwist]
  have := ((E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y).mpr h
  simpa only [frobenius_def] using this

theorem nonsingular_pow_iff {x y : L} :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) ↔
      (E.baseChange L).toAffine.Nonsingular x y := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y
  simpa only [frobenius_def] using this

theorem negY_pow (x y : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.negY (x ^ p) (y ^ p) =
      (E.baseChange L).toAffine.negY x y ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_negY (frobenius L p) x y
  simpa only [frobenius_def] using this

theorem addX_pow (x₁ x₂ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addX (x₁ ^ p) (x₂ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addX x₁ x₂ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addX (frobenius L p) x₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem addY_pow (x₁ x₂ y₁ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addY (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addY x₁ x₂ y₁ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addY (frobenius L p) x₁ y₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem slope_pow [DecidableEq L] (x₁ x₂ y₁ y₂ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.slope (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (y₂ ^ p) =
      (E.baseChange L).toAffine.slope x₁ x₂ y₁ y₂ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_slope (frobenius L p) x₁ x₂ y₁ y₂
  simpa only [frobenius_def] using this

end Twist

section PointMap

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusPoint (L : Type*) [Field L] [Algebra F L] [CharP L p] :
    (E.baseChange L).toAffine.Point → ((frobeniusTwist E p).baseChange L).toAffine.Point
  | .zero => 0
  | .some x y h => .some (x ^ p) (y ^ p) (nonsingular_pow E p h)

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

theorem frobeniusPoint_some {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    frobeniusPoint E p L (.some x y h) = .some (x ^ p) (y ^ p) (nonsingular_pow E p h) := rfl

theorem frobeniusPoint_add [DecidableEq L] (P Q : (E.baseChange L).toAffine.Point) :
    frobeniusPoint E p L (P + Q) = frobeniusPoint E p L P + frobeniusPoint E p L Q := by
  have hinj : Function.Injective fun z : L => z ^ p := by
    intro a b hab
    exact frobenius_inj L p (by simpa only [frobenius_def] using hab)
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · show frobeniusPoint E p L (0 + Q) = 0 + frobeniusPoint E p L Q
    rw [zero_add, zero_add]
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · show frobeniusPoint E p L (Point.some x₁ y₁ h₁ + 0) = frobeniusPoint E p L (Point.some x₁ y₁ h₁) + 0
    rw [add_zero, add_zero]
  rw [frobeniusPoint_some, frobeniusPoint_some]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E.baseChange L).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, Point.add_of_Y_eq (congrArg (· ^ p) hxy.1)
      (by rw [negY_pow, hxy.2])]
    rfl
  · have hxy' : ¬(x₁ ^ p = x₂ ^ p ∧
        y₁ ^ p = ((frobeniusTwist E p).baseChange L).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
      rintro ⟨hx, hy⟩
      rw [negY_pow] at hy
      exact hxy ⟨hinj hx, hinj hy⟩
    rw [Point.add_some hxy, Point.add_some hxy', frobeniusPoint_some, Point.some.injEq,
      slope_pow, addX_pow, addY_pow]
    exact ⟨rfl, rfl⟩

theorem isGenPt_frobeniusPoint_iff (P : (E.baseChange L).toAffine.Point) :
    IsGenPt (frobeniusTwist E p) (frobeniusPoint E p L P) ↔ IsGenPt E P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · exact Iff.rfl
  · rw [frobeniusPoint_some, isGenPt_some, isGenPt_some]
    exact ⟨fun ht hx => ht (hx.pow p), fun ht => ht.pow hp.out.pos⟩

end PointMap

section FrobeniusIsogeny

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] (p : ℕ) [hp : Fact p.Prime]
  [CharP F p]

omit [E.IsElliptic] in
theorem map_frobeniusPoint {L L' : Type*} [Field L] [Algebra F L] [CharP L p] [Field L']
    [Algebra F L'] [CharP L' p] [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L')
    (P : (E.baseChange L).toAffine.Point) :
    Point.map σ (frobeniusPoint E p L P) = frobeniusPoint E p L' (Point.map σ P) := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [frobeniusPoint_some, Point.map_some, map_pow]

noncomputable def frobeniusGenPt :
    ((frobeniusTwist E p).baseChange E.toAffine.FunctionField).toAffine.Point :=
  frobeniusPoint E p _ (genericPoint E)

theorem map_genEval_frobeniusGenPt {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    Point.map (genEval E P hP) (frobeniusGenPt E p) = frobeniusPoint E p L P := by
  classical
  rw [frobeniusGenPt, map_frobeniusPoint, map_genEval_genericPoint]

theorem isGenPt_frobeniusGenPt : IsGenPt (frobeniusTwist E p) (frobeniusGenPt E p) :=
  (isGenPt_frobeniusPoint_iff E p _).mpr (transcendental_genX E)

theorem respectsAdd_frobeniusGenPt : RespectsAdd E (frobeniusTwist E p) (frobeniusGenPt E p) := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  rw [map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt,
    frobeniusPoint_add]

noncomputable def frobeniusIsogeny : Isogeny E (frobeniusTwist E p) :=
  ⟨frobeniusGenPt E p, (isIsogeny_iff _).mpr
    ⟨isGenPt_frobeniusGenPt E p, respectsAdd_frobeniusGenPt E p⟩⟩

theorem frobeniusIsogeny_app {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    (frobeniusIsogeny E p).app P hP = frobeniusPoint E p L P :=
  map_genEval_frobeniusGenPt E p P hP

theorem comap_frobeniusIsogeny_genX :
    (frobeniusIsogeny E p).comap (genX (frobeniusTwist E p)) = genX E ^ p :=
  (frobeniusIsogeny E p).comap_genX

theorem comap_frobeniusIsogeny_genY :
    (frobeniusIsogeny E p).comap (genY (frobeniusTwist E p)) = genY E ^ p :=
  (frobeniusIsogeny E p).comap_genY

theorem fieldRange_comap_frobeniusIsogeny :
    (frobeniusIsogeny E p).comap.fieldRange = powField E p := by
  rw [← map_top_eq_fieldRange, ← adjoin_genX_genY (frobeniusTwist E p), adjoin_map, powField]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, comap_frobeniusIsogeny_genX,
    comap_frobeniusIsogeny_genY]

theorem degree_frobeniusIsogeny [PerfectRing F p] : (frobeniusIsogeny E p).degree = p := by
  have h := congrArg (fun M : IntermediateField F E.toAffine.FunctionField =>
    Module.finrank M E.toAffine.FunctionField) (fieldRange_comap_frobeniusIsogeny E p)
  rw [Isogeny.degree]
  exact h.trans (finrank_powField E p)

end FrobeniusIsogeny

end GroundTheory.Global
end

section

open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

open WeierstrassCurve.Affine

variable {L : PeriodPair}

theorem exists_weierstrassP_eq (c : ℂ) : ∃ z, z ∉ L.lattice ∧ ℘[L] z = c := by
  by_contra hcon
  push Not at hcon
  have h2 := finsum_toNat_torusOrder_weierstrassP_sub (L := L) c
  have h0 : ∀ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    rw [torusOrder_mk (isEllipticFunction_weierstrassP_sub c)]
    by_cases hz : z ∈ L.lattice
    · have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
      have e : (fun w ↦ ℘[L] w - c) = ℘[L] + fun _ ↦ -c := by
        funext w
        simp [sub_eq_add_neg]
      have hlt : meromorphicOrderAt ℘[L] z < meromorphicOrderAt (fun _ : ℂ ↦ -c) z := by
        rw [L.order_weierstrassP z hz]
        exact lt_of_lt_of_le (by decide) analyticAt_const.meromorphicOrderAt_nonneg
      rw [e, meromorphicOrderAt_add_eq_left_of_lt hc hlt, L.order_weierstrassP z hz]
      rfl
    · have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
        (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
      have h0 : analyticOrderAt (fun w ↦ ℘[L] w - c) z = 0 :=
        ha.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 (hcon z hz))
      rw [ha.meromorphicOrderAt_eq, h0]
      rfl
  simp [h0] at h2


variable (L) in
def toPoint (L : PeriodPair) (z : ℂ) : (weierstrassCurve L).toAffine.Point :=
  haveI := Classical.propDecidable (z ∈ L.lattice)
  if h : z ∈ L.lattice then 0 else
    .some (℘[L] z) (℘'[L] z / 2) (equation_iff_nonsingular.1 (equation_weierstrassP L h))

lemma toPoint_of_mem {z : ℂ} (h : z ∈ L.lattice) : toPoint L z = 0 := by
  rw [toPoint, dite_eq_left h]

lemma toPoint_of_notMem {z : ℂ} (h : z ∉ L.lattice) :
    toPoint L z = .some (℘[L] z) (℘'[L] z / 2)
      (equation_iff_nonsingular.1 (equation_weierstrassP L h)) := by
  rw [toPoint, dite_eq_right h]

lemma point_some_congr {x y x' y' : ℂ} {h : (weierstrassCurve L).toAffine.Nonsingular x y}
    {h' : (weierstrassCurve L).toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy
  rfl

@[simp]
lemma toPoint_zero : toPoint L 0 = 0 := toPoint_of_mem L.lattice.zero_mem

lemma toPoint_add_mem {z l : ℂ} (hl : l ∈ L.lattice) : toPoint L (z + l) = toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h hl)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hzl]
    exact point_some_congr (isPeriodic_weierstrassP z l hl)
      (by rw [isPeriodic_derivWeierstrassP z l hl])

lemma toPoint_eq_of_sub_mem {z w : ℂ} (h : z - w ∈ L.lattice) : toPoint L z = toPoint L w := by
  simpa using toPoint_add_mem (z := w) h

theorem toPoint_neg (z : ℂ) : toPoint L (-z) = -toPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, toPoint_of_mem (neg_mem hz), neg_zero]
  · have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
    rw [toPoint_of_notMem hz, toPoint_of_notMem hz', Point.neg_some]
    refine point_some_congr (L.weierstrassP_neg z) ?_
    simp [negY, L.derivWeierstrassP_neg]
    ring

theorem toPoint_eq_zero_iff {z : ℂ} : toPoint L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h ↦ ?_, toPoint_of_mem⟩
  by_contra hz
  rw [toPoint_of_notMem hz] at h
  exact Point.some_ne_zero _ h

theorem toPoint_add (z w : ℂ) : toPoint L (z + w) = toPoint L z + toPoint L w := by
  by_cases hz : z ∈ L.lattice
  · rw [toPoint_of_mem hz, zero_add, add_comm, toPoint_add_mem hz]
  by_cases hw : w ∈ L.lattice
  · rw [toPoint_of_mem hw, add_zero, toPoint_add_mem hw]
  by_cases hzw' : z + w ∈ L.lattice
  · have : toPoint L w = toPoint L (-z) := toPoint_eq_of_sub_mem (by rwa [sub_neg_eq_add, add_comm])
    rw [toPoint_of_mem hzw', this, toPoint_neg, add_neg_cancel]
  by_cases hzw : z - w ∈ L.lattice
  ·
    have hwz : toPoint L w = toPoint L z := toPoint_eq_of_sub_mem (by simpa using neg_mem hzw)
    have h2 : toPoint L (z + w) = toPoint L (2 * z) :=
      toPoint_eq_of_sub_mem (by rw [show z + w - 2 * z = -(z - w) by ring]; exact neg_mem hzw)
    have h2z : 2 * z ∉ L.lattice := fun h ↦ hzw' (by
      rw [show z + w = 2 * z - (z - w) by ring]; exact sub_mem h hzw)
    have hd : ℘'[L] z ≠ 0 := fun h ↦ h2z ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hz).2 h)
    have hy : ℘'[L] z / 2 ≠ (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) := by
      simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero]
      intro h
      apply hd
      linear_combination h
    rw [h2, hwz, toPoint_of_notMem hz, toPoint_of_notMem h2z, Point.add_self_of_Y_ne hy]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2) =
        tangentSlope L z / 2 := by
      have hden : ℘'[L] z / 2 - (weierstrassCurve L).toAffine.negY (℘[L] z) (℘'[L] z / 2) =
          ℘'[L] z := by
        simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
        ring
      rw [slope_of_Y_ne rfl hy, hden]
      simp only [tangentSlope, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₄]
      field_simp
      ring
    have hx : ℘[L] (2 * z) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] z)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] z) (℘'[L] z / 2) (℘'[L] z / 2)) := by
      rw [hsl, weierstrassP_two_mul hz h2z]
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_two_mul hz h2z]
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring
  ·
    have hne : ℘[L] z ≠ ℘[L] w := fun h ↦
      (sub_mem_or_add_mem_of_weierstrassP_eq hz hw h).elim hzw hzw'
    rw [toPoint_of_notMem hz, toPoint_of_notMem hw, toPoint_of_notMem hzw',
      Point.add_of_X_ne hne]
    have hsl : (weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        chordSlope L z w / 2 := by
      rw [slope_of_X_ne hne, chordSlope]
      ring
    have hx : ℘[L] (z + w) = (weierstrassCurve L).toAffine.addX (℘[L] z) (℘[L] w)
        ((weierstrassCurve L).toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2)) := by
      rw [hsl, weierstrassP_add hz hw hzw hzw']
      simp only [addX, weierstrassCurve_a₁, weierstrassCurve_a₂]
      ring
    refine point_some_congr hx ?_
    rw [addY, negAddY, ← hx, hsl, derivWeierstrassP_add hz hw hzw hzw']
    simp only [negY, weierstrassCurve_a₁, weierstrassCurve_a₃]
    ring

theorem toPoint_surjective : Function.Surjective (toPoint L) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, toPoint_zero⟩
  obtain ⟨z, hz, hx⟩ := exists_weierstrassP_eq (L := L) x
  have hE := (weierstrassCurve_equation_iff L x y).1 h.1
  have hP := L.derivWeierstrassP_sq z hz
  rw [hx] at hP
  have hz' : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
  have hy : (y - ℘'[L] z / 2) * (y + ℘'[L] z / 2) = 0 := by linear_combination hE / 4 - hP / 4
  rcases mul_eq_zero.1 hy with h1 | h1
  · refine ⟨z, ?_⟩
    rw [toPoint_of_notMem hz]
    exact point_some_congr hx (by linear_combination -h1)
  · refine ⟨-z, ?_⟩
    rw [toPoint_of_notMem hz']
    exact point_some_congr (by rw [L.weierstrassP_neg, hx])
      (by rw [L.derivWeierstrassP_neg]; linear_combination -h1)


variable (L) in
def toPointHom (L : PeriodPair) : ℂ →+ (weierstrassCurve L).toAffine.Point where
  toFun := toPoint L
  map_zero' := toPoint_zero
  map_add' := toPoint_add


variable (L) in
def torusToPoint (L : PeriodPair) : Torus L →+ (weierstrassCurve L).toAffine.Point :=
  QuotientAddGroup.lift L.lattice.toAddSubgroup (toPointHom L) fun _ hl ↦ toPoint_of_mem hl

@[simp]
lemma torusToPoint_mk (z : ℂ) : torusToPoint L (Torus.mk L z) = toPoint L z := rfl

lemma torusToPoint_injective : Function.Injective (torusToPoint L) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
  rw [torusToPoint_mk, toPoint_eq_zero_iff] at hx
  exact (QuotientAddGroup.eq_zero_iff z).2 hx


end Elliptic
end GroundTheory.Global
end
end
