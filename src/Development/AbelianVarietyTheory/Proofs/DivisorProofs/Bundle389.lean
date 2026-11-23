module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle323
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle326
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006

@[expose] public section

section

open IsLocalRing

theorem _root_.GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' : ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], 2 ≤ ringKrullDim R → ReciprocityTheory.CA.ModDepthGE R A 2 := by
  first | exact @GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing | exact GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing | (intros; apply GlobalTheory.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory

theorem quot_jets_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  intro n
  refine ⟨1 / (4 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro p w0 w hw0 hw h0 hL0 hwp hLj
  set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set a := w0 p with ha_def
  have ha_norm : 3 / 4 ≤ ‖a‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖a‖ + ‖a - 1‖ := by
      have := norm_sub_le a (a - 1)
      simpa using this
    simp at h1
    linarith
  have ha : a ≠ 0 := by
    intro h; rw [h] at ha_norm; simp at ha_norm; linarith
  refine ⟨ha, ?_⟩
  set L0 := fderiv ℂ w0 p with hL0_def
  have hL0' : ‖L0‖ ≤ ε := by
    have := hL0; rwa [fderiv_sub_const] at this
  have hproj : ∀ j : Fin n, HasFDerivAt (fun v : V n => v j - p j) (EuclideanSpace.proj (𝕜 := ℂ) j) p := by
    intro j
    have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt (x := p)
    exact this.sub_const (p j)
  have hLj' : ∀ j : Fin n, ∀ ξ : V n, ‖fderiv ℂ (w j) p ξ - ξ j‖ ≤ ε * ‖ξ‖ := by
    intro j ξ
    have hd : fderiv ℂ (fun v : V n => w j v - (v j - p j)) p
        = fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j :=
      ((hw j).hasFDerivAt.sub (hproj j)).fderiv
    have := (fderiv ℂ (fun v : V n => w j v - (v j - p j)) p).le_opNorm ξ
    rw [hd] at this
    have h2 := hLj j
    rw [hd] at h2
    calc ‖fderiv ℂ (w j) p ξ - ξ j‖ = ‖(fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j) ξ‖ := by simp
      _ ≤ _ := this
      _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  set F : V n → V n := fun v => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) with hF
  have hq : ∀ j : Fin n, HasFDerivAt (fun v => w j v / w0 v)
      (w j p • ((-(a ^ 2)⁻¹) • L0) + a⁻¹ • fderiv ℂ (w j) p) p := by
    intro j
    have hinv : HasFDerivAt (fun v => (w0 v)⁻¹) ((-(a ^ 2)⁻¹) • L0) p :=
      (hasDerivAt_inv ha).comp_hasFDerivAt p hw0.hasFDerivAt
    have := HasFDerivAt.mul (hw j).hasFDerivAt hinv
    have e : (fun v => w j v / w0 v) = (w j * fun v => (w0 v)⁻¹) := by
      funext v; simp [div_eq_mul_inv]
    rw [e]; exact this
  have hFd : DifferentiableAt ℂ F p := by
    rw [differentiableAt_piLp]
    intro j
    simpa [hF] using (hq j).differentiableAt
  set D := fderiv ℂ F p with hD
  have hDj : ∀ j : Fin n, ∀ ξ : V n, (D ξ) j = w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ := by
    intro j ξ
    have h1 : HasFDerivAt (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) ((EuclideanSpace.proj (𝕜 := ℂ) j).comp D) p :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt.comp p hFd.hasFDerivAt
    have h2 : (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) = fun v => w j v / w0 v := by
      funext v; simp [hF]
    rw [h2] at h1
    have := congrArg (fun T : V n →L[ℂ] ℂ => T ξ) (h1.unique (hq j))
    simpa using this
  have hinj : ∀ ξ : V n, D ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have hcoord : ∀ j : Fin n, ‖ξ j‖ ≤ 2 * ε * ‖ξ‖ := by
      intro j
      have e := hDj j ξ
      rw [hξ] at e
      simp only [PiLp.zero_apply] at e
      have e2 : a * fderiv ℂ (w j) p ξ = w j p * L0 ξ := by
        have : a ^ 2 * (w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ) = 0 := by
          rw [← e]; ring
        field_simp at this
        linear_combination this
      have hL0ξ : ‖L0 ξ‖ ≤ ε * ‖ξ‖ := (L0.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hL0' (norm_nonneg _))
      have e3 : ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ ≤ ε * (ε * ‖ξ‖) := by
        rw [← norm_mul, e2, norm_mul]
        exact mul_le_mul (hwp j) hL0ξ (norm_nonneg _) hεpos.le
      have e4 : ‖fderiv ℂ (w j) p ξ‖ ≤ ε * ‖ξ‖ := by
        by_contra hc
        push_neg at hc
        have : (3/4) * (ε * ‖ξ‖) < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := by
          calc (3/4) * (ε * ‖ξ‖) ≤ ‖a‖ * (ε * ‖ξ‖) := mul_le_mul_of_nonneg_right ha_norm (by positivity)
            _ < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := mul_lt_mul_of_pos_left hc (by linarith)
        have : ε * (ε * ‖ξ‖) ≤ (3/4) * (ε * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      have e5 := hLj' j ξ
      have : ‖ξ j‖ ≤ ‖fderiv ℂ (w j) p ξ‖ + ‖fderiv ℂ (w j) p ξ - ξ j‖ := by
        have := norm_sub_le (fderiv ℂ (w j) p ξ) (fderiv ℂ (w j) p ξ - ξ j)
        simpa using this
      linarith
    have hsq : ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖ξ.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (2 * ε * ‖ξ‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
        _ = (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by simp
    have hc : (n : ℝ) * (2 * ε) ^ 2 ≤ 1 / 4 := by
      rw [hε]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [show (2 * (1 / (4 * ((n:ℝ) + 1)))) ^ 2 = 1 / (4 * ((n:ℝ)+1)^2) by field_simp; ring]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : ‖ξ‖ ^ 2 ≤ (1/4) * ‖ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := hsq
        _ = ((n : ℝ) * (2 * ε) ^ 2) * ‖ξ‖ ^ 2 := by ring
        _ ≤ (1/4) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have : ‖ξ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖ξ‖]
    simpa using this
  intro hdet
  have h := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (D : V n →ₗ[ℂ] V n))).1 hdet
  apply h
  rw [LinearMap.ker_eq_bot']
  intro m hm
  exact hinj m hm

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem exists_preconnected_infinite_nhds {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (hn : 1 ≤ n) (e : OpenPartialHomeomorph Y (V n)) (x : Y) (hx : x ∈ e.source) :
    ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ B.Infinite := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  refine ⟨e.symm '' ball (e x) r, ?_, ?_, ?_⟩
  · have h := e.symm.image_mem_nhds (x := e x) (e.map_source hx) (ball_mem_nhds (e x) hr)
    rwa [e.left_inv hx] at h
  · exact (convex_ball (e x) r).isPreconnected.image _ (e.continuousOn_symm.mono hsub)
  · refine Set.Infinite.image (e.symm.injOn.mono hsub) ?_
    haveI : NeBot (𝓝[≠] (e x)) := Module.punctured_nhds_neBot ℂ (V n) (e x)
    exact infinite_of_mem_nhds (e x) (ball_mem_nhds (e x) hr)

theorem exists_finite_disjoint_meets_components :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ S : Set Y, S.Finite → ∃ T : Set Y, T.Finite ∧ Disjoint T S ∧ ∀ y, ∃ P ∈ T, P ∈ connectedComponent y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn S hS
  have h1 : ∀ x : Y, ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ ∃ P ∈ B, P ∉ S := by
    intro x
    obtain ⟨B, hB, hc, hi⟩ :=
      exists_preconnected_infinite_nhds hn (A.chart (A.pick x)) x (A.mem_pick x)
    obtain ⟨P, hP, hPS⟩ := (hi.diff hS).nonempty
    exact ⟨B, hB, hc, P, hP, hPS⟩
  choose B hB hc P hP hPS using h1
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover B (fun x _ => hB x)
  refine ⟨P '' (t : Set Y), t.finite_toSet.image P, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩
    exact hPS x
  · intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨P x, ⟨x, hx, rfl⟩, (hc x).subset_connectedComponent hy (hP x)⟩

end GlobalTheory.OTY
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowFibre

section Pow

variable {S : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G₀ G j)

theorem over_ext {T : Over S} {a b : T ⟶ G₀} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem left_ext {T : Scheme.{0}} {a b : T ⟶ G₀.left} (h₀ : a ≫ G₀.hom = b ≫ G₀.hom)
    (h : ∀ i, a ≫ (p.pr i).left = b ≫ (p.pr i).left) : a = b := by
  have := over_ext p (T := Over.mk (b ≫ G₀.hom)) (a := Over.homMk a h₀) (b := Over.homMk b rfl)
    fun i => Over.OverMorphism.ext (h i)
  exact congrArg (·.left) this

theorem exists_left_lift {T : Scheme.{0}} (s : T ⟶ S) (a : Fin j → (T ⟶ G.left)) (ha : ∀ i, a i ≫ G.hom = s) :
    ∃ x : T ⟶ G₀.left, x ≫ G₀.hom = s ∧ ∀ i, x ≫ (p.pr i).left = a i := by
  let c : Fan (fun _ : Fin j => G) := Fan.mk (Over.mk s) fun i => Over.homMk (a i) (ha i)
  exact ⟨(p.lim.lift c).left, Over.w (p.lim.lift c), fun i => congrArg (·.left) (p.lim.fac c ⟨i⟩)⟩

end Pow

section Pull

variable {S S' : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {G₀' G' : Over S'} [GrpObj G₀'] [GrpObj G']
  {j : ℕ} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_pow_pullback (p : Out.IsPowGrp G₀ G j) (p' : Out.IsPowGrp G₀' G' j) (h : IsGrpPullback G' G f φ) :
    ∃ φ₀ : G₀'.left ⟶ G₀.left, IsGrpPullback G₀' G₀ f φ₀ ∧ ∀ i, φ₀ ≫ (p.pr i).left = (p'.pr i).left ≫ φ := by
  obtain ⟨φ₀, hw, hφ₀⟩ := exists_left_lift p (G₀'.hom ≫ f) (fun i => (p'.pr i).left ≫ φ) fun i => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
  refine ⟨φ₀, ⟨⟨⟨hw⟩, ⟨?_⟩⟩, fun T x y x₀ y₀ hx hy => ?_⟩, hφ₀⟩
  · have hs : ∀ (s : PullbackCone G₀.hom f) (i : Fin j), (s.fst ≫ (p.pr i).left) ≫ G.hom = s.snd ≫ f :=
      fun s i => by rw [Category.assoc, Over.w, s.condition]
    choose l hl₁ hl₂ using fun s : PullbackCone G₀.hom f =>
      exists_left_lift p' s.snd (fun i => h.1.lift _ _ (hs s i)) fun i => h.1.lift_snd _ _ _
    refine PullbackCone.IsLimit.mk _ l (fun s => left_ext p ?_ fun i => ?_) hl₁
      fun s m h₁ h₂ => left_ext p' (h₂.trans (hl₁ s).symm) fun i => ?_
    · rw [Category.assoc, hw, ← Category.assoc, hl₁, s.condition]
    · rw [Category.assoc, hφ₀, ← Category.assoc, hl₂, h.1.lift_fst]
    · rw [hl₂]
      refine h.1.hom_ext ?_ ?_
      · rw [h.1.lift_fst, Category.assoc, ← hφ₀, ← Category.assoc, h₁]
      · rw [h.1.lift_snd, Category.assoc, Over.w, h₂]
  · refine left_ext p ?_ fun i => ?_
    · rw [Over.w, Category.assoc, hw, ← Category.assoc, Over.w]
      rfl
    · have := p.hom i
      have := p'.hom i
      have e := h.2 T (x ≫ p'.pr i) (y ≫ p'.pr i) (x₀ ≫ p.pr i) (y₀ ≫ p.pr i)
        (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hφ₀])
        (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hφ₀])
      rw [← MonObj.mul_comp, ← MonObj.mul_comp, Over.comp_left, Over.comp_left] at e
      rw [e, Category.assoc, Category.assoc, hφ₀]

end Pull



end GlobalTheory.PowFibre

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem eq_unit_of_pullback_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ (T : Scheme.{0}) (t : T ⟶ S)
    (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → φ' ≫ u.left = φ' ≫ v.left →
    ∀ τ : T, ∀ x : A.left, A.hom x = t τ → (u * v⁻¹).left x = (η[B]).left (t τ) := by
  intro S A B _ _ _ _ u v _ _ _ _ T t A' _ φ' hp he τ x hx
  have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
  let P : Over.mk (A'.hom ≫ t) ⟶ A := Over.homMk φ' (by simpa using hw)
  have hPu : P ≫ u = P ≫ v := by
    ext1; simpa [P] using he
  have h1 : P ≫ (u * v⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hPu, mul_inv_cancel]
  have h2 : φ' ≫ (u * v⁻¹).left = A'.hom ≫ t ≫ (η[B]).left := by
    have := congrArg CommaMorphism.left h1
    simpa [P, Hom.one_def] using this
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x τ hx
  have hf : (hp.1.isoPullback.inv ≫ φ') z = x := by rw [hp.1.isoPullback_inv_fst]; exact hz1
  have hs : (hp.1.isoPullback.inv ≫ A'.hom) z = τ := by rw [hp.1.isoPullback_inv_snd]; exact hz2
  rw [Scheme.Hom.comp_apply] at hf hs
  rw [← hf, ← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs]

end GlobalTheory.EndLoc
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_finite_ext_point_lift_of_surjective_lft :
    ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π →
      ∀ (K : Type) [Field K] (x : Sp K ⟶ X),
        ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y),
          σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  intro X Y π hft hs K _ x
  haveI : Surjective π := ⟨hs⟩
  let P := Limits.pullback π x
  let s : P ⟶ Sp K := Limits.pullback.snd π x
  haveI : LocallyOfFiniteType s := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd π x))
  haveI : Surjective s := inferInstanceAs (Surjective (Limits.pullback.snd π x))
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨p₀, -⟩ := s.surjective (default : Sp K)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set P)) ⟨p₀, trivial⟩
    isClosed_univ.isLocallyClosed
  haveI : IsClosedImmersion (P.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  haveI : IsFinite (P.fromSpecResidueField z ≫ s) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  let φ := Spec.preimage (P.fromSpecResidueField z ≫ s)
  have hφ : Spec.map φ = P.fromSpecResidueField z ≫ s := Spec.map_preimage _
  refine ⟨P.residueField z, inferInstance, φ.hom,
    P.fromSpecResidueField z ≫ Limits.pullback.fst π x, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  · have h2 : spMap φ.hom = P.fromSpecResidueField z ≫ s := hφ
    rw [h2]
    exact (Category.assoc _ _ _).trans ((congrArg (P.fromSpecResidueField z ≫ ·)
      Limits.pullback.condition).trans (Category.assoc _ _ _).symm)

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem skew_transpose_mul_add_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    Xᵀ * G + G * X.map (fun x => cc x) = 0 := by
  ext i j
  have h := hX (Pi.single i 1) (Pi.single j 1)
  have c0 : cc (0 : E) = 0 := map_zero _
  have c1 : cc (1 : E) = 1 := map_one _
  have hc : ∀ b : Fin r, cc (if b = j then (1 : E) else 0) = if b = j then 1 else 0 := by
    intro b; split_ifs <;> simp [c0, c1]
  simp [herm, Matrix.mulVec_single, Pi.single_apply, c0, c1, hc, Matrix.mul_apply] at h ⊢
  exact h

theorem conj_eq_of_skew {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    X.map (fun x => cc x) = -(G⁻¹ * Xᵀ * G) := by
  have h := skew_transpose_mul_add_mul_conj G X hX
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have h2 : G * X.map (fun x => cc x) = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right h
  calc X.map (fun x => cc x) = G⁻¹ * (G * X.map (fun x => cc x)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = -(G⁻¹ * Xᵀ * G) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]

theorem trace_mul_skew_mem_maximalRealSubfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X Y : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace ∈ maximalRealSubfield E := by
  intro E _ _ _ r G X Y _ hG hX hY
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hXc := conj_eq_of_skew G X hG hX
  have hYc := conj_eq_of_skew G Y hG hY
  rw [← IsCMField.complexConj_eq_self_iff]
  change cc (X * Y).trace = (X * Y).trace
  have hmap : cc (X * Y).trace = ((X * Y).map (fun x => cc x)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum (IsCMField.complexConj E : E →+* E) _ _
  have hmul : (X * Y).map (fun x => cc x) = X.map (fun x => cc x) * Y.map (fun x => cc x) :=
    Matrix.map_mul (f := ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E))
  rw [hmap, hmul, hXc, hYc, neg_mul_neg]
  have e1 : G⁻¹ * Xᵀ * G * (G⁻¹ * Yᵀ * G) = G⁻¹ * (Xᵀ * Yᵀ * G) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  first | exact @GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | exact GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | (intros; apply GlobalTheory.UnitaryCongruenceDetAny.det_eq_one <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.low_count_all_bounds : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality := by
  first | exact @GlobalTheory.LowCount.lowC_all | exact GlobalTheory.LowCount.lowC_all | (intros; apply GlobalTheory.LowCount.lowC_all <;> assumption)
end
