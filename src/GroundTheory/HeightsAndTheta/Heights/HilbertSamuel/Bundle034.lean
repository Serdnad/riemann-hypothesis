module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.RingTheory.Noetherian.Defs
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Ideal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.FiniteType
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameBasePtFree

theorem linForm_projMat {κ : Type} [Fintype κ] {D : ℕ} (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  generalize e k = q
  obtain ⟨⟨⟩, j⟩ := q
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem rename_mem_span {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) {h : MvPolynomial (Fin (D + 1)) ℤ} {n : ℕ}
    (hh : h.IsHomogeneous n) (hn : 0 < n) :
    rename e h ∈ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  have h1 : h ∈ Ideal.span ((X : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    have := hh (mem_support_iff.mp hm)
    rw [hm0, map_zero] at this
    omega
  have h2 := Ideal.mem_map_of_mem (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Ix κ) ℤ) h1
  rw [Ideal.map_span, Set.image_image, Set.image_univ] at h2
  simpa [rename_X] using h2

theorem pow_mem (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame x e) (p : Ix κ) :
    ∃ N : ℕ, (X p : MvPolynomial (Ix κ) ℤ) ^ N ∈
      coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  obtain ⟨q, hmon, hq⟩ := hfr.integral p
  set N := q.natDegree with hNdef
  have hcoef : ∀ j, ∃ f : MvPolynomial (Fin (D + 1)) ℤ,
      coneMap ℤ (x ∘ e) f = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose f hf using hcoef
  set F : MvPolynomial (Ix κ) ℤ := X p ^ N +
      ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j with hFdef
  have hFh : F.IsHomogeneous N := by
    refine (isHomogeneous_X_pow p N).add (IsHomogeneous.sum _ _ _ fun j hj => ?_)
    have hj' : N - j + j = N := Nat.sub_add_cancel (Finset.mem_range.mp hj).le
    have := ((homogeneousComponent_isHomogeneous (N - j) (f j)).rename_isHomogeneous (f := e)).mul
      (isHomogeneous_X_pow p j)
    rwa [hj'] at this
  have hFx : aeval x F = 0 := by
    have h0 := congrArg (fun r : Polynomial Ω => r.coeff N) hq
    simp only [Polynomial.coeff_zero] at h0
    rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.coeff_add,
      Polynomial.finsetSum_coeff] at h0

    rw [← h0, hFdef, map_add (f := _), map_sum]
    congr 1
    · rw [Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul_X_pow, if_pos rfl,
        map_pow, aeval_X]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N := (Finset.mem_range.mp hj).le
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow,
        ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hjN, Polynomial.coeff_mul_C]
      rw [map_mul, map_pow, aeval_X, aeval_rename]
      have : algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) (q.coeff j) = coneMap ℤ (x ∘ e) (f j) := (hf j).symm
      rw [this, coeff_coneMap]
  have hFP : F ∈ coordIdeal ℤ x := mem_coordIdeal_of_isHomogeneous ℤ x hFh hFx
  refine ⟨N, ?_⟩
  have hsum : (∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j) ∈
      Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    have hjN : j < N := Finset.mem_range.mp hj
    exact rename_mem_span e (homogeneousComponent_isHomogeneous (N - j) (f j)) (by omega)
  have : (X p : MvPolynomial (Ix κ) ℤ) ^ N =
      F - ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j := by
    rw [hFdef]; ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hsum)

end ProjFrameBasePtFree


open ProjFrameBasePtFree in
theorem ProjFrameBasePtFree.proof : ProjFrameBasePtFree.Statement := by
  intro D Ω _ _ κ _ x e hfr k₂ i
  obtain ⟨N, hN⟩ := pow_mem D Ω κ x e hfr ⟨(), i ()⟩
  refine ⟨N, ?_⟩
  have hspan : (Set.range fun j : GlobalTheory (Fin (D + 1)) k₂ =>
      linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨k₂, j⟩) =
      Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ) := by
    cases k₂
    ext
    simp [linForm_projMat]
  rw [hspan, Fintype.prod_unique]
  exact hN

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TopPullFS

variable {κ : Type} [Fintype κ] {D : ℕ}

theorem linApply_projMat (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) (k : Fin (D + 1)) :
    linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z ⟨(), k⟩ = z (e k) := by
  classical
  simp only [linApply, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

theorem fs_linApply (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))).h
        (linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z) =
      Real.sqrt (∑ k, ‖z (e k)‖ ^ 2) := by
  simp only [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [linApply_projMat]

end TopPullFS


open TopPullFS in
theorem TopPullFS.proof (hCM : ChangeOfModelStatement) (hBP : ProjFrameBasePtFree.Statement)
    (hIm : ProjFrameImage.Statement) (hDeg : ProjFrameGraphDeg.Statement) : TopPullFS.Statement := by
  intro D Ω _ _ κ _ I x m e hI hP hm hfr hFS
  obtain ⟨G, J, hJ, hJe⟩ := hDeg D Ω κ x e hP hfr
  have himg := hIm D Ω κ x e hfr
  have hSmoothFS : IsSmoothHerm (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) := by
    apply isSmoothHerm_ofCone
    intro z hz
    change ContDiffWithinAt ℝ _ (fun w : Ix (Fin (D + 1)) → ℂ => ‖WithLp.toLp 2 w‖) _ z
    have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (WithLp.toLp 2 : (Ix (Fin (D + 1)) → ℂ) → _) :=
      PiLp.contDiff_toLp
    have hz' : WithLp.toLp 2 z ≠ 0 := by simpa using hz
    exact (hL.contDiffAt.norm ℂ hz').contDiffWithinAt
  have key := hCM I hI Unit (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x) (D + 1) (projMat e) G J
    (fun _ => HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) (fun _ => HermLine.ofCone m) hP
    (hBP D Ω κ x e hfr) (by rw [himg]; exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot D) hJ
    (fun _ => hSmoothFS) (fun _ => isSmoothHerm_ofCone hm) (fun _ => rfl)
    (fun _ z hz => by
      rw [fs_linApply]
      exact hFS z ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩)
  rw [himg, hJe] at key
  simpa [top, hhOf] using key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : Submodule R Ω :=
  Submodule.span R ((fun μ : (Σ k, ι k) → ℕ => ∏ p, y p ^ μ p) '' {μ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k})

theorem monomial_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b : K → ℕ} (μ : (Σ k, ι k) → ℕ)
    (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k) : ∏ p, y p ^ μ p ∈ relSecM R y b :=
  Submodule.subset_span ⟨μ, hμ, rfl⟩

theorem relSecM_fg (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : (relSecM R y b).FG := by
  have hfin : {μ : (Σ k, ι k) → ℕ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k}.Finite := by
    refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (b p.1)) fun p => Set.finite_Iic _).subset ?_
    intro μ hμ p _
    simp only [Set.mem_Iic]
    rw [← hμ p.1]
    exact Finset.single_le_sum (f := fun i => μ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  exact Submodule.fg_span (hfin.image _)

theorem mul_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b b' : K → ℕ} {x x' : Ω}
    (hx : x ∈ relSecM R y b) (hx' : x' ∈ relSecM R y b') : x * x' ∈ relSecM R y (b + b') := by
  have hle : relSecM R y b * relSecM R y b' ≤ relSecM R y (b + b') := by
    rw [relSecM, relSecM, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨μ, hμ, rfl⟩, _, ⟨ν, hν, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨μ + ν, fun k => ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hμ k, hν k]
    · simp [pow_add, Finset.prod_mul_distrib]
  exact hle (Submodule.mul_mem_mul hx hx')

theorem adjoin_isNoetherianRing {m : ℕ} (g : Fin m → Ω) : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := by
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range g)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range g)
  exact Algebra.FiniteType.isNoetherianRing ℤ _


omit [∀ k, Fintype (ι k)] in
theorem mul_prod_mem_relChartLat (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {a a' : K → ℤ} {n : ℕ} (e : K → ℕ)
    (c0 : ∀ k, ι k) (h : ∀ k, a' k = n * a k + e k) {s : Ω} (hs : s ∈ relChartLat R y a n) :
    s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relChartLat R y a' 1 := by
  intro c hc
  have key : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
      y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) * (y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro k
    rw [h k, show -(((1 : ℕ) : ℤ) * ((n : ℤ) * a k + (e k : ℤ))) = -((n : ℤ) * a k) + -((e k : ℕ) : ℤ) by push_cast; ring,
      zpow_add₀ (hc k), zpow_neg (y ⟨k, c k⟩) ((e k : ℕ) : ℤ), zpow_natCast]
  rw [Finset.prod_congr rfl fun k _ => key k, Finset.prod_mul_distrib]
  have hmem : (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, (y ⟨k, c0 k⟩ / y ⟨k, c k⟩) ^ e k ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) :=
    mul_mem (hs c hc) (prod_mem fun k _ => pow_mem (Algebra.subset_adjoin
      (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ⟨k, c0 k⟩)) _)
  convert hmem using 1
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_inv_distrib]
  ring

end Objects

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockTop.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m 0) = top I x m D ∧
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m' 1) =
        top I (matAct B x) m' D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Cycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def vertCycleNum (P : Ideal (MRing ι)) (s : MRing ι) {n : ℕ} (e : Fin n → K → ℤ) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then 0 else (geoNum n W e : ℝ) * Real.log (charOf W))

theorem vertR_eq_vertCycleNum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.vertR P L s = vertCycleNum P s (fun j => (L j).a) :=
  rfl

end Cycle

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockDen (c : κ) : MRing (FinTwoTypeFamily κ) :=
  X ⟨0, c⟩

def twoBlockNum (l : Ix κ → ℤ) : MRing (FinTwoTypeFamily κ) :=
  ∑ j : Ix κ, MvPolynomial.C (l j) * X ⟨1, j.2⟩

def twoBlockVert (x x' : Ix κ → Ω) (c : κ) (l : Ix κ → ℤ) {n : ℕ} (e : Fin n → Fin 2 → ℤ) : ℝ :=
  vertCycleNum (twoBlockIdeal x x') (twoBlockNum l) e - vertCycleNum (twoBlockIdeal x x') (twoBlockDen c) e

def twoBlockDegList (D i : ℕ) : Fin D → Fin 2 → ℤ :=
  fun j => if (j : ℕ) < i then Pi.single 0 1 else Pi.single 1 1

theorem twoBlockDegList_eq (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) (j : Fin D) :
    twoBlockDegList D i j = (twoBlockList m m' D i (if (j : ℕ) < i then j.castSucc else j.succ)).a := by
  unfold twoBlockDegList twoBlockList
  split_ifs with h1 h2 h2 <;> simp_all [blockLine]
  omega

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def GraphIsometricForms.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ)
    (B₁ : HermLine ι) (B : HermLine ι₂) (B₁' B' : HermLine (Sum.elim ι ι₂)),
    IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → IsBasePtFree P g →
    (∀ k, B₁.a k = ∑ k₂, B.a k₂ * (δ k₂ k : ℤ)) →
    (∀ z ∈ mcPts P, B₁.h z = B.h (formApply g z)) →
    IsPullHerm Sum.inl inlV B₁ B₁' → IsPullHerm Sum.inr inrV B B' →
    IsIsometricOn (graphIdeal P g) B₁' B'

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def AnResNullForm.Statement : Prop :=
  ∀ (e : ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι))
    (R : AnRes P J e) (G : MRing ι) (dG : K → ℕ),
    IsArithVar P (e + 1) → IsMultiHomog G dG → G ∉ P →
      ∀ j, volume ((R.A.chart j).target ∩
        (R.A.chart j).symm ⁻¹' {a | eval (R.lift a a) (map (Int.castRingHom ℂ) G) = 0}) = 0

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resolutionVolumeL2Complex (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℂ) : ℝ :=
  Real.sqrt (∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV)

def ResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ z ∈ pts (coordIdeal ℤ d.x),
        ptNorm d.m (RingHom.id ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
