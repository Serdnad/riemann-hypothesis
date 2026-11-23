module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter NumberField

section Host

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def LiesOver {F : Type*} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ)
    (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ (d : K → ℕ) (g h : MRing ι) (θ : F), IsMultiHomog g d → IsMultiHomog h d →
    aeval y g = algebraMap F Ω θ * aeval y h →
    eval z (map (Int.castRingHom ℂ) g) = sg θ * eval z (map (Int.castRingHom ℂ) h)

end Host

def ArithmeticHilbertSamuelUpperBoundNumberField : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    IsConjInvariantH A → (∀ sg, 0 < Λ sg) → (∀ sg, Λ (ComplexEmbedding.conjugate sg) = Λ sg) →
    ∑ sg, Real.log (Λ sg) ≤ 0 →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z) →
    limsup (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A)

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology

theorem ptsLocal : PtsLocalStatement := by
  intro K _ ι _ P e Ψ₀ φ φ' g g' hφ hg
  have hS : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ' g' y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · set γ := hγ.choose with hγdef
      have hev := hγ.choose_spec.2
      have hmem : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := hev.mono fun y' h => h.2.1
      have hy : γ y ∈ mcPts P := hmem.self_of_nhds
      rw [hg _ hy]
      have hH : ∀ k, cxHessian (fun y' => φ k (γ y')) y = cxHessian (fun y' => φ' k (γ y')) y := by
        intro k
        have hloc : (fun y' => φ k (γ y')) =ᶠ[𝓝 y] (fun y' => φ' k (γ y')) :=
          hmem.mono fun y' h => hφ k _ h
        have h2 := hloc.fderiv (𝕜 := ℝ)
        unfold cxHessian
        rw [h2.fderiv_eq]
      unfold maDensity
      simp only [hH]
    · rfl
  exact ⟨by simp only [ptsIntegralAt, hS], by simp only [ptsIntegral, ptsIntegralAt, hS]⟩

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

def secSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (B : Set (Fin e → ℂ)) : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) :=
  {G | (∀ y ∉ B, G y = 0) ∧ DifferentiableOn ℂ G B ∧ ∀ y ∈ B, G y ∈ fibre P Ψ y}

theorem coincide_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {c : Fin e → ℂ} {r : ℝ}
    {G G' : (Fin e → ℂ) → ((k : K) → ι k) → ℂ} (hG : G ∈ secSet P Ψ (ball c r))
    (hG' : G' ∈ secSet P Ψ (ball c r)) (hne : G ≠ G') :
    volume {y | y ∈ ball c r ∧ G y = G' y} = 0 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, G y0 ≠ G' y0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  have hy0b : y0 ∈ ball c r := by
    by_contra hb
    exact hy0 (by rw [hG.1 y0 hb, hG'.1 y0 hb])
  obtain ⟨i, hi⟩ : ∃ i, G y0 i ≠ G' y0 i := by
    by_contra hcon
    push_neg at hcon
    exact hy0 (funext hcon)
  set f : (Fin e → ℂ) → ℂ := fun y => G y i - G' y i with hf
  have hdiff : DifferentiableOn ℂ f (ball c r) := by
    have h1 : DifferentiableOn ℂ (fun y => G y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG.2.1 y hy)) i
    have h2 : DifferentiableOn ℂ (fun y => G' y i) (ball c r) := fun y hy =>
      (differentiableWithinAt_pi.1 (hG'.2.1 y hy)) i
    exact h1.sub h2
  have han : AnalyticOnNhd ℂ f (ball c r) := hA e (ball c r) f isOpen_ball hdiff
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball (convex_ball c r).isPreconnected han
    ⟨y0, hy0b, sub_ne_zero.2 hi⟩
  refine measure_mono_null ?_ hnull
  intro y hy
  exact ⟨hy.1, by simp [f, hy.2]⟩

theorem secSet_finite (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite)
    (c : Fin e → ℂ) {r : ℝ} (hr : 0 < r) : (secSet P Ψ (ball c r)).Finite := by
  by_contra hinf
  have hS : (secSet P Ψ (ball c r)).Infinite := hinf
  have key : ∀ m : ℕ, volume {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} = 0 := by
    intro m
    obtain ⟨F, hFS, hFc⟩ := hS.exists_subset_card_eq m
    have hnull : volume (⋃ G ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)), ⋃ G' ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)),
        {y | G ≠ G' ∧ y ∈ ball c r ∧ G y = G' y}) = 0 := by
      refine (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G hG =>
        (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA (hFS hG) (hFS hG') h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    refine measure_mono_null (fun y hy => ?_) hnull
    obtain ⟨hyb, hlt⟩ := hy
    by_contra hnot
    have hinj : Set.InjOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) := fun G hG G' hG' heq => by
      by_contra hne
      exact hnot (Set.mem_iUnion₂.2 ⟨G, hG, Set.mem_iUnion₂.2 ⟨G', hG', ⟨hne, hyb, heq⟩⟩⟩)
    have hmaps : Set.MapsTo (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) (fibre P Ψ y) := fun G hG => (hFS hG).2.2 y hyb
    have hle := Set.ncard_le_ncard_of_injOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) hmaps hinj (hfin y)
    rw [Set.ncard_coe_finset, hFc] at hle
    omega
  have hcover : ball c r ⊆ ⋃ m : ℕ, {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} := fun y hy =>
    Set.mem_iUnion.2 ⟨(fibre P Ψ y).ncard + 1, hy, Nat.lt_succ_self _⟩
  have h0 : volume (ball c r) = 0 := measure_mono_null hcover (measure_iUnion_null key)
  exact (Metric.measure_ball_pos volume c hr).ne' h0

def badSet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set (Fin e → ℂ) :=
  {y | ∃ w γ γ', IsSheet P Ψ y w γ ∧ IsSheet P Ψ y w γ' ∧
    ¬ ((fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y'))}

theorem segre_differentiableAt {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : DifferentiableAt ℂ γ y) : DifferentiableAt ℂ (fun y' => segre (γ y')) y := by
  rw [differentiableAt_pi]
  intro i
  simp only [segre]
  classical
  have key : ∀ s : Finset K, DifferentiableAt ℂ (fun x => ∏ k ∈ s, γ x ⟨k, i k⟩) y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact ((differentiableAt_pi.1 hγ) ⟨a, i a⟩).mul ih
  exact key Finset.univ

theorem mem_secSet_of_sheet {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {B : Set (Fin e → ℂ)}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : ∀ y' ∈ B, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y') :
    B.indicator (fun y' => segre (γ y')) ∈ secSet P Ψ B := by
  refine ⟨fun y hy => Set.indicator_of_notMem hy _, ?_, fun y hy => ?_⟩
  · have hd : DifferentiableOn ℂ (fun y' => segre (γ y')) B := fun y' hy' =>
      (segre_differentiableAt (h y' hy').1).differentiableWithinAt
    exact hd.congr (fun y' hy' => Set.indicator_of_mem hy' _)
  · rw [Set.indicator_of_mem hy]
    exact ⟨γ y, (h y hy).2.1, rfl, (h y hy).2.2⟩

theorem badSet_null (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite) :
    volume (badSet P Ψ) = 0 := by
  obtain ⟨Dc, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin e → ℂ)
  let S : (Fin e → ℂ) → ℚ → Set (Fin e → ℂ) := fun d q =>
    ⋃ G ∈ secSet P Ψ (ball d q), ⋃ G' ∈ secSet P Ψ (ball d q), {y | G ≠ G' ∧ y ∈ ball d (q : ℝ) ∧ G y = G' y}
  have hS : ∀ d q, volume (S d q) = 0 := by
    intro d q
    by_cases hq : (0 : ℝ) < q
    · have hfinS := secSet_finite hA hfin d hq
      refine (measure_biUnion_null_iff hfinS.countable).2 fun G hG =>
        (measure_biUnion_null_iff hfinS.countable).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA hG hG' h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    · have hempty : ball d (q : ℝ) = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hq)
      refine measure_mono_null ?_ measure_empty
      intro y hy
      simp only [S, Set.mem_iUnion] at hy
      obtain ⟨G, _, G', _, _, hyb, _⟩ := hy
      rw [hempty] at hyb
      exact hyb
  have hcount : volume (⋃ d ∈ Dc, ⋃ q : ℚ, S d q) = 0 :=
    (measure_biUnion_null_iff hDc).2 fun d _ => measure_iUnion_null fun q => hS d q
  refine measure_mono_null ?_ hcount
  intro y hy
  obtain ⟨w, γ, γ', ⟨hγw, hγev⟩, ⟨hγ'w, hγ'ev⟩, hne⟩ := hy
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hγev.and hγ'ev)
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < ε / 2 := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (half_pos hε)
    exact ⟨q, h1, h2⟩
  obtain ⟨d, hdD, hd⟩ := hDd.exists_mem_open isOpen_ball ⟨y, mem_ball_self hq0⟩
  have hdy : dist y d < q := by
    rw [dist_comm]
    exact hd
  have hyB : y ∈ ball d (q : ℝ) := by
    rw [mem_ball]
    exact hdy
  have hBsub : ball d (q : ℝ) ⊆ ball y ε := by
    intro y' hy'
    rw [mem_ball] at hy' ⊢
    calc dist y' y ≤ dist y' d + dist d y := dist_triangle _ _ _
      _ < q + q := by
        rw [dist_comm d y]
        exact add_lt_add hy' hdy
      _ < ε := by linarith
  have hG : (ball d (q : ℝ)).indicator (fun y' => segre (γ y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).1)
  have hG' : (ball d (q : ℝ)).indicator (fun y' => segre (γ' y')) ∈ secSet P Ψ (ball d (q : ℝ)) :=
    mem_secSet_of_sheet (fun y' hy' => (hball y' (hBsub hy')).2)
  refine Set.mem_iUnion₂.2 ⟨d, hdD, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨_, hG,
    Set.mem_iUnion₂.2 ⟨_, hG', ?_, hyB, ?_⟩⟩⟩⟩
  · intro heq
    apply hne
    filter_upwards [isOpen_ball.mem_nhds hyB] with y' hy'
    have h1 := congrFun heq y'
    simpa [Set.indicator_of_mem hy'] using h1
  · simp [Set.indicator_of_mem hyB, hγw, hγ'w]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def SameOrbit (z z' : (Σ k, ι k) → ℂ) : Prop :=
  ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = fun p => c p.1 * z' p

def affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => z q / z ⟨q.1, p q.1⟩

structure AnLogRes (P J : Ideal (MRing ι)) (e : ℕ) where

  homog : IsMultiHomogIdeal J

  nondeg : ¬ J ≤ P

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  lift : X → X → (Σ k, ι k) → ℂ
  holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p)
  mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P

  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)

  surj : ∀ z ∈ mcPts P, z ∉ mcPts J → ∃ x, SameOrbit (lift x x) z

  inj : ∀ x x', lift x x ∉ mcPts J → SameOrbit (lift x x) (lift x' x') → x = x'

  immersion : ∀ x, lift x x ∉ mcPts J → ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) →
    ∀ j, x ∈ (A.chart j).source →
      (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

  snc : ∀ (f : MRing ι) (a : K → ℕ), f ∉ P → IsMultiHomog f a →
    (∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 → z ∈ mcPts J) →
    ∃ (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set X),
      IsSNC A ⟨U, isOpen_U, mem_U, fun _ _ => 0⟩
        (fun x y => eval (lift x y) (map (Int.castRingHom ℂ) f)) m W

  null : ∀ j, MeasureTheory.volume
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts J}) = 0

attribute [instance] AnLogRes.top AnLogRes.compact AnLogRes.t2

def potOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (L : HermLine ι) : LocPot R.X where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  φ x y := Real.log (L.h (R.lift x y))

def ResExistsStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ P →
    ∃ J' : Ideal (MRing ι), J' ≤ J ∧ IsMultiHomogIdeal J' ∧ ¬ J' ≤ P ∧ Nonempty (AnLogRes P J' e)

def ResBridgeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    ptsIntegralAt P Ψ (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x))

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
