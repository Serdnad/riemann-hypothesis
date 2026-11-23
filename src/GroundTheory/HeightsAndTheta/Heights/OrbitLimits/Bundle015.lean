module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents)

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

def chartSubst {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  bind₁ (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ))

theorem chartSubst_X {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (p : Σ k, ι k) :
    chartSubst σ i (X p) = X (σ.symm (Function.update i p.1 p.2)) := by
  exact MvPolynomial.bind₁_X_right _ _

theorem chartSection_eq_chartSubst [Fintype K] [∀ k, Fintype (ι k)] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) :
    chartSection σ i s = chartSubst σ i (map (Int.castRingHom ℂ) s) := rfl

def ChartConeComponent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiProjPrime W → ∀ W' ∈ segreChartComponents W σ i,
      ∃ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
        W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W'

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartComponents)

def ChartDivisorComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      (∀ J ∈ segreChartComponents P σ i, ∀ W' : Ideal (MvPolynomial (Fin m) ℂ),
        W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes ↔
          J ≤ W' ∧ ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W' ∈ segreChartComponents W σ i) ∧
      ∀ W₁ W₂, W₁ ∈ divSupp P s ∧ IsHorizontal W₁ → W₂ ∈ divSupp P s ∧ IsHorizontal W₂ →
        ∀ W' ∈ segreChartComponents W₁ σ i, W' ∈ segreChartComponents W₂ σ i → W₁ = W₂

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftCountAlongMultiples.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (a : ℕ) (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    1 ≤ a → (∀ j, x' j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) x' →
    Birational (fun p : Σ _ : Unit, ι' => x' p.2) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ((a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
          ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (a * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageCoord.mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : ∀ p, (v p).1 = κ p.1)
    {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) (f : MRing ι) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  have h : ((mConeMap y).comp (rename v : MRing ι →ₐ[ℤ] MRing ι')) =
      ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).restrictScalars ℤ).comp
        (mConeMap (y ∘ v)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, hv p]
  exact congrArg (fun φ => φ f) h

theorem ImageCoord.proof : ImageCoordStatement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ y hB
  obtain ⟨hκ, -, hv, -⟩ := hB
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ImageCoord.mConeMap_rename κ v hv y f]
  constructor
  · intro h
    exact rename_injective κ hκ (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PFCoord.of_found (hGD : GenDegStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hGF : GenFibreExistsStatement) (hFD : FibreDimStatement) (hCF : CoordFibreDeg.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hLL'
  obtain ⟨G⟩ := hGF K ι K' ι' κ v (mCoordIdeal y) d hv hP'
  obtain ⟨J, hJ, -⟩ := hR4 G.Φ (FibreBlock κ) (fibreIdx ι' κ)
  have hV : IsProjVarF (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hGD I hI K ι K' ι' κ v (mCoordIdeal y) d G J L L' hv hP' hP hJ hL hLL', h0,
    hCF K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section

variable {K : Type u} [Fintype K] {ι : K → Type v} [∀ k, Fintype (ι k)] {F : Type w} [Field F]

theorem exists_isChart_of_isProjVarF {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V n) :
    ∃ i, IsChart V i :=
  ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩

theorem ratDiv_one_eq_mapRange (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    ratDiv V f 1 = Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (_root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f) := by
  simp [ratDiv, divCycle_one]

theorem cycEval_ratDiv_one_nonneg (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (h : ∀ W ∈ divSupp V f, 0 ≤ J W) : 0 ≤ cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  exact Finset.sum_nonneg fun W hW => mul_nonneg (Nat.cast_nonneg _)
    (h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW)))

theorem cycEval_ratDiv_one_pos (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (hne : _root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f ≠ 0) (h : ∀ W ∈ divSupp V f, 0 < J W) :
    0 < cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  refine Finset.sum_pos (fun W hW => mul_pos ?_ ?_) (Finsupp.support_nonempty_iff.mpr hne)
  · exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)
  · exact h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW))

theorem ptDeg_pos {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i : ∀ k, ι k}
    (hi : IsChart V i) : 0 < ptDeg V i := by
  have := chart_finite hV hi
  have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) := ⟨(chart_isField hV hi).exists_pair_ne⟩
  exact Module.finrank_pos

theorem nonneg_of_isFieldIntersection {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n →
      ∀ L : Fin n → K → ℤ, (∀ j k, 0 ≤ L j k) → 0 ≤ I V n L := by
  intro n
  induction n with
  | zero =>
    intro V hV L _
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V L i hV hi]
    exact Nat.cast_nonneg _
  | succ n ih =>
    intro V hV L hL
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    have hf := isMultiHomog_coordProd (F := F) i (fun k => (L (Fin.last n) k).toNat)
    have hfV := coordProd_not_mem hV.1.1 i hi (fun k => (L (Fin.last n) k).toNat)
    have hsec : IsRatSection V (L (Fin.last n))
        (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (L (Fin.last n) k).toNat) 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h),
        fun k => by simp [Int.toNat_of_nonneg (hL _ k)]⟩
    rw [← Fin.snoc_init_self (α := fun _ => K → ℤ) L, hI.2 V n (Fin.init L) _ _ 1 hV hsec]
    exact cycEval_ratDiv_one_nonneg _ _ _ fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW) _ fun j k => hL _ k


omit [Fintype K] in
theorem const_one_eq_snoc (n : ℕ) :
    (fun _ _ => (1 : ℤ) : Fin (n + 1) → K → ℤ) =
      Fin.snoc (α := fun _ => K → ℤ) (fun _ _ => 1) (fun _ => 1) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem segre_pos_of_isFieldIntersection (hS : SegreDivisor.Statement.{u, v, w})
    {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n → 0 < I V n (fun _ _ => 1) := by
  intro n
  induction n with
  | zero =>
    intro V hV
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V _ i hV hi]
    exact_mod_cast ptDeg_pos hV hi
  | succ n ih =>
    intro V hV
    obtain ⟨f, hf, hfV, hne⟩ := hS K ι F V n hV
    have hsec : IsRatSection V (fun _ => 1) f 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h), fun k => by simp⟩
    rw [const_one_eq_snoc, hI.2 V n _ _ f 1 hV hsec]
    exact cycEval_ratDiv_one_pos _ _ _ hne fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW)

end

theorem Positivity.of_found (hS : SegreDivisor.Statement.{u, v, w}) {K : Type u} [Fintype K]
    (F : Type w) [Field F] (ι : K → Type v) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  fun _ hI V n hV =>
    ⟨fun L hL => nonneg_of_isFieldIntersection hI n V hV L hL,
      segre_pos_of_isFieldIntersection hS hI n V hV⟩

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def normSq (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) ^ 2

def regLog (A : HermLine ι) (s : MRing ι) (ε : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (normSq A s z + ε) / 2

omit [∀ k, Fintype (ι k)] in
theorem normSq_nonneg (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : 0 ≤ normSq A s z :=
  sq_nonneg _

theorem normSq_smul {A : HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    normSq A s (fun p => c p.1 * z p) = normSq A s z := by
  unfold normSq
  rw [eval_smul_of_isMultiHomog hs c z, A.smul c z hc, norm_mul, norm_prod]
  have hC : (∏ k, ‖c k‖ ^ A.a k) = ∏ k, ‖c k ^ a k‖ := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, norm_pow, zpow_natCast]
  rw [hC, mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ =>
    norm_ne_zero_iff.mpr (pow_ne_zero _ (hc k)))]

def regLine (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : HermLine ι :=
  HermLine.ofWeight (fun z => -regLog A s ε z) fun c z hc => by
    simp only [regLog, normSq_smul ha hs c z hc]

theorem regLine_a (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : (regLine A s ε ha hs).a = 0 := rfl

theorem log_regLine (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : (fun z => Real.log ((regLine A s ε ha hs).h z)) = regLog A s ε := by
  funext z
  simp [regLine, HermLine.ofWeight, Real.log_exp]

theorem contDiff_evalC (s : MRing ι) :
    ContDiff ℝ ∞ (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) s)) := by
  induction s using MvPolynomial.induction_on with
  | C a => simpa only [map_C, eval_C] using contDiff_const
  | add p q hp hq => simpa only [map_add (f := _), eval_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, map_X, eval_mul, eval_X] using hp.mul (contDiff_apply ℝ (fun _ => ℂ) i)

theorem contDiffOn_regLog {A : HermLine ι} (hA : IsSmoothHerm A) (s : MRing ι) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (regLog A s ε) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hN : ContDiffOn ℝ ∞ (normSq A s) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have h1 := (((contDiff_norm_sq ℝ).comp (contDiff_evalC s)).contDiffOn (s := {z : (Σ k, ι k) → ℂ |
      ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})).div (hA.pow 2) fun z hz => pow_ne_zero _ (A.pos z hz).ne'
    exact h1.congr fun z _ => by simp only [normSq, div_pow]; rfl
  exact ((hN.add contDiffOn_const).log fun z _ =>
    (add_pos_of_nonneg_of_pos (normSq_nonneg A s z) hε).ne').div_const 2

theorem isSmoothHerm_regLine {A : HermLine ι} (hA : IsSmoothHerm A) {s : MRing ι} {ε : ℝ} (hε : 0 < ε)
    {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    IsSmoothHerm (regLine A s ε ha hs) :=
  Real.contDiff_exp.comp_contDiffOn (contDiffOn_regLog hA s hε).neg.neg

end GroundTheory.Heights₂.Heights.Targets
end
end
