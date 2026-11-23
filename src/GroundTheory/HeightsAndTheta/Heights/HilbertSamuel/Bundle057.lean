module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

namespace Veronese

abbrev Idx (D : ℕ) : Type := {p : Fin (D + 1) × Fin (D + 1) // p.1 ≤ p.2}

def Fld (D : ℕ) : Type := FractionRing (MvPolynomial (Fin (D + 1)) ℚ)

instance instField (D : ℕ) : Field (Fld D) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instCharZero (D : ℕ) : CharZero (Fld D) :=
  inferInstanceAs (CharZero (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instAlgebra (D : ℕ) : Algebra (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin (D + 1)) ℚ) (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instIsFractionRing (D : ℕ) : IsFractionRing (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) :=
  Localization.isLocalization

def t (D : ℕ) (i : Fin (D + 1)) : Fld D := algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) (X i)

def x (D : ℕ) : Ix (Idx D) → Fld D := fun q => t D q.2.1.1 * t D q.2.1.2

def map (D : ℕ) (w : Fin (D + 1) → ℂ) : Ix (Idx D) → ℂ := fun q => w q.2.1.1 * w q.2.1.2

def wt {D : ℕ} (q : Ix (Idx D)) : ℝ := if q.2.1.1 = q.2.1.2 then 1 else 2

def scale (D : ℕ) (z : Ix (Idx D) → ℂ) : Ix (Idx D) → ℂ := fun q => (Real.sqrt (wt q) : ℂ) * z q

theorem wt_pos {D : ℕ} (q : Ix (Idx D)) : 0 < wt q := by
  unfold wt
  split_ifs <;> norm_num

theorem scale_ne_zero {D : ℕ} {z : Ix (Idx D) → ℂ} (hz : z ≠ 0) : scale D z ≠ 0 := by
  intro h
  apply hz
  funext q
  have h1 := congrFun h q
  have h2 : (Real.sqrt (wt q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (wt_pos q)).ne'
  simpa [scale, h2] using h1

def metric (D : ℕ) : ConeMetric ℂ (Ix (Idx D)) where
  ρ z := (fsMetric (ι := Ix (Idx D))).ρ (scale D z)
  pos z hz := (fsMetric (ι := Ix (Idx D))).pos _ (scale_ne_zero hz)
  smul c z := by
    have : scale D (c • z) = c • scale D z := by
      funext q
      simp only [scale, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, (fsMetric (ι := Ix (Idx D))).smul]

def gram (D n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ) : Matrix (Fin r) (Fin r) ℝ :=
  fun k l => (1 / 2) *
    ((∫ p : CP D, pairVal (metric D) n (b k) (b l) (map D p.rep) ∂CP.fsMeasure D).re +
      (∫ p : CP D, pairVal (metric D) n (b k) (b l) (conjPt (map D p.rep)) ∂CP.fsMeasure D).re)


open Classical in
def chi (D n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Idx D)) ℚ), IsSecBasis (x D) n p.2 then
    -(1 / 2) * Real.log (gram D n h.choose.2).det
  else 0

end Veronese

open Veronese

def VeroneseArith.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → IsArithVar (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) (D + 1)

def VeroneseSemipos.Statement : Prop :=
  ∀ D : ℕ, IsSemipositiveRel (ι := GlobalTheory (Idx D)) ⊥ (coordIdeal ℤ (Veronese.x D))
    (HermLine.ofCone (Veronese.metric D))

def VeroneseResolution.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ (J : Ideal (MRing (GlobalTheory (Idx D))))
    (R : AnRes (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) J D)
    (_ : MeasurableSpace R.X) (_ : BorelSpace R.X) (dV : Measure R.X),
    IsSmoothVolume R.A dV ∧
    ∀ g : (Ix (Idx D) → ℂ) → ℂ, (∀ (c : ℂ) (z : Ix (Idx D) → ℂ), c ≠ 0 → g (c • z) = g z) →
      ∫ y, g (R.lift y y) ∂dV = ∫ p : CP D, g (Veronese.map D p.rep) ∂CP.fsMeasure D

def VeroneseChi.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ n : ℕ, Veronese.chi D n = chiP D (2 * n)

def VeroneseTop.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ I : AllFam, I.IsFamily →
    top I (Veronese.x D) (Veronese.metric D) D = 2 ^ (D + 1) * hhOf I D

def VeroneseGenDeg.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → genDeg (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) D 1 = 2 ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem constShift_a (A : HermLine ι) (η : ℝ) : (HermLine.constShift A η).a = A.a := by
  simp [HermLine.constShift, HermLine.tensor, HermLine.ofWeight]

omit [∀ k, Fintype (ι k)] in
theorem constShift_h (A : HermLine ι) (η : ℝ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.constShift A η).h z = A.h z * Real.exp (-η) := rfl

theorem isSmoothHerm_constShift {A : HermLine ι} (hA : IsSmoothHerm A) (η : ℝ) :
    IsSmoothHerm (HermLine.constShift A η) := by
  have : (HermLine.constShift A η).h = fun z => A.h z * Real.exp (-η) := rfl
  unfold IsSmoothHerm at hA ⊢
  rw [this]
  exact hA.mul contDiffOn_const

omit [∀ k, Fintype (ι k)] in
theorem isConjInvariantH_constShift {A : HermLine ι} (hA : IsConjInvariantH A) (η : ℝ) :
    IsConjInvariantH (HermLine.constShift A η) := by
  intro z
  rw [constShift_h, constShift_h, hA z]

theorem leviForm_constShift (A : HermLine ι) (η : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun x => Real.log ((HermLine.constShift A η).h x)) z w =
      leviForm (fun x => Real.log (A.h x)) z w := by
  have hU : IsOpen {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} := by
    have : {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {x | x ⟨k, i⟩ ≠ 0} := by
      ext x
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fun x => Real.log (A.h x) + (-η) := by
    filter_upwards [hU.mem_nhds hz] with x hx
    rw [constShift_h, Real.log_mul (A.pos x hx).ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fderiv ℝ (fun x => Real.log (A.h x)) := by
    filter_upwards [h1.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h2.fderiv_eq]

theorem isSemipositiveRel_constShift {P0 P : Ideal (MRing ι)} {A : HermLine ι}
    (hA : IsSemipositiveRel P0 P A) (η : ℝ) : IsSemipositiveRel P0 P (HermLine.constShift A η) := by
  refine ⟨isSmoothHerm_constShift hA.1 η, fun z hz w hw => ?_⟩
  rw [leviForm_constShift A η hz.1 w]
  exact hA.2 z hz w hw

end Shift

theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Pr La 1 D) : ∃ n, 1 ≤ n ∧ ∃ s ∈ La n, s ≠ 0 ∧ Pr n s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k, 1 ≤ k → smallSectionCount Pr La k = 0 := by
    intro k hk
    have hsub : Subsingleton {s : La k // Pr k (s : Ω)} := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha0 : (a : Ω) = 0 := by
        by_contra h0
        exact hne k hk a a.2 h0 ha
      have hb0 : (b : Ω) = 0 := by
        by_contra h0
        exact hne k hk b b.2 h0 hb
      exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
    have := hsub
    have hc : Nat.card {s : La k // Pr k (s : Ω)} ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    unfold smallSectionCount
    interval_cases Nat.card {s : La k // Pr k (s : Ω)} <;> simp
  have : arVolP Pr La 1 D = 0 := by
    unfold arVolP
    refine (limsup_congr ?_).trans (limsup_const 0)
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [one_mul, hzero k hk, zero_div]
  linarith

theorem G4.proof (hG6 : ArithmeticVolumeBig.Statement) (hCS : ConstantShift.Statement) : G4.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM hpos
  obtain ⟨η, hη0, hηlt⟩ : ∃ η : ℝ, 0 < η ∧ ((D : ℝ) + 1) * η * geomDeg (mCoordIdeal y) M D <
      II K ι (mCoordIdeal y) (D + 1) (fun _ => M) := by
    set T := II K ι (mCoordIdeal y) (D + 1) (fun _ => M)
    set g := geomDeg (mCoordIdeal y) M D
    have hden : 0 < 2 * (((D : ℝ) + 1) * |g| + 1) := by positivity
    refine ⟨T / (2 * (((D : ℝ) + 1) * |g| + 1)), div_pos hpos hden, ?_⟩
    set η := T / (2 * (((D : ℝ) + 1) * |g| + 1))
    have hη0 : 0 < η := div_pos hpos hden
    have he : η * (2 * (((D : ℝ) + 1) * |g| + 1)) = T := div_mul_cancel₀ T hden.ne'
    have h1 : ((D : ℝ) + 1) * η * g ≤ ((D : ℝ) + 1) * η * |g| :=
      mul_le_mul_of_nonneg_left (le_abs_self g) (by positivity)
    have h3 : 0 ≤ ((D : ℝ) + 1) * η * |g| := by positivity
    nlinarith
  have hshift := hCS K ι (II K ι) (mCoordIdeal y) D M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift M η) := by
    rw [hshift]
    linarith
  have hvol := hG6 K ι Ω y D (HermLine.constShift M η) P0 II hD hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g h z hg hh hdeg heq hz
    have hle := hsmall dg dh g h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def imageLattice {E V : Type*} [AddCommGroup E] [AddCommGroup V] (φ : E →+ V) : Submodule ℤ V :=
  AddSubgroup.toIntSubmodule φ.range

def EuclideanSections.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ [DiscreteTopology (imageLattice (φ n))] [IsZLattice ℝ (imageLattice (φ n))],
          -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
            (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
              ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def SmallSectionMixed.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M H : HermLine ι) (p q : ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (H.a = fun _ => (1 : ℤ)) → IsSemipositiveRel P0 P H → MonomialsBounded P H (fun _ => 1) → IsConjInvariantH H →
    1 ≤ p → 0 < II K ι P d (fun _ => HermLine.zcomb M H q p) →
    ∃ (n : ℕ) (f g : MRing ι), 1 ≤ n ∧ IsRatSectionOn P (HermLine.zcomb M H ((n * q : ℕ) : ℤ) ((n * p : ℕ) : ℤ)) f g ∧
      divCycle P g ≤ divCycle P f ∧
      ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * (HermLine.zcomb M H ((n * q : ℕ) : ℤ) ((n * p : ℕ) : ℤ)).h z

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable def scaledFSH {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  (fsH ι).tensor (constLine (-1))

def ScaledFSTopPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → 0 < II K ι P d (fun _ => scaledFSH ι)

theorem scaledFSH_a {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    (scaledFSH ι).a = fun _ => 1 := by
  funext k
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

theorem scaledFSH_h {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    (scaledFSH ι).h z = (∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 := by
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem brIntegrable_of (hLA : LogAbsLocIntStatement) (R : AnRes P J e)
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  intro j K hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  obtain ⟨a, ha, hsa, -⟩ := hs
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hu0V : u0 ∈ V := ⟨hu0, R.mem_U x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun u => R.lift x0 ((R.A.chart j).symm u) with hγdef
  have hγ : ∀ u ∈ V, AnalyticAt ℂ γ u := fun u hu => analyticAt_lift_chart R x0 j hu
  set f : (Fin e → ℂ) → ℂ := fun u => eval (γ u) (map (Int.castRingHom ℂ) s) with hfdef
  have hf : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_eval_poly _ fun p => analyticAt_pi_iff.mp (hγ u hu) p
  set H : (Fin e → ℂ) → ℝ := fun u => A.h (γ u) with hHdef
  have hblk : ∀ u ∈ V, ∀ k, ∃ i, γ u ⟨k, i⟩ ≠ 0 := fun u hu => (R.mem x0 _ hu.2).1
  have hHc : ContinuousOn H V := fun u hu =>
    ((hA.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds (hblk u hu))).comp
      (hγ u hu).continuousAt).continuousWithinAt
  have hHpos : ∀ u ∈ V, 0 < H u := fun u hu => A.pos _ (hblk u hu)
  have hF : ∀ u ∈ V, logNorm A s (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u)) =
      Real.log (‖f u‖ / H u) := by
    intro u hu
    obtain ⟨c, hc, hzc⟩ := R.compat _ x0 _ ⟨R.mem_U _, hu.2⟩
    rw [hzc]
    exact logNorm_bsmul A ha hsa hc (γ u)
  have hDc : ContinuousOn (locDens R.A (fun i => potOf R (L i)) j) B :=
    (locDensCont R.A _ (fun i => isPotential_potOf R (hL i)) j).mono
      (hBV.trans inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (hLA e V f hV hf).integrableOn_compact_subset hBV hBc
  have hlogH : IntegrableOn (fun u => Real.log (H u)) B :=
    ((hHc.mono hBV).log fun u hu => (hHpos u (hBV hu)).ne').integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ / H u) *
      locDens R.A (fun i => potOf R (L i)) j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ / H u) (volume.restrict B) :=
      (hfc.norm.div (hHc.mono hBV) fun u hu => (hHpos u (hBV hu)).ne').aestronglyMeasurable hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ / H u) *
      locDens R.A (fun i => potOf R (L i)) j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hlogH.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_div_le (norm_nonneg (f u)) (hHpos u (hBV hu))
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end
