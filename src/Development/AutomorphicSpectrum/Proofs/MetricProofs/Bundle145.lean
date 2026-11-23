module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle140
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle142
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentFrameComparison
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentOrbitComparison
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle141
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepCols_ne_empty_of_le {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.stepCols_ne_empty <;> assumption

theorem exists_plk_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → ∃ I₀, IsStepRows N j p.2 I₀ ∧ plk M (BM.F l) k₀ z I₀ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hp hx hz hO
  obtain ⟨h, a, hb, -, ha, hpl, hzk⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx hz hO
  by_contra hcon
  push_neg at hcon
  have hmin : ∀ I, minorIJ h I (stepCols N j p.2) = 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · have e := hpl I hI
      rw [hcon I hI] at e
      exact (mul_eq_zero.1 e.symm).resolve_left ha
    · exact ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 h I hb hI).resolve_right
        (stepCols_ne_empty_of_le M.j_le p.2)
  obtain ⟨m, hm⟩ := hz.1 k₀
  exact hm (by rw [hzk m]; simp [hmin])

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.hodge_potential_smooth_off_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ a, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => phMu Hd ((D.chart a).γ t)) (offBd D a)) ∧ ∀ a, ∀ t₀ : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t₀‖ ≤ 1 / 2 → ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t ∈ offBd D a, ‖t - t₀‖ < ε → -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧ phMu Hd ((D.chart a).γ t) ≤ C ∧ ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤ C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary | exact GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SqFirst

theorem isSmoothHerm_of_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    {A : HermLine ι} {A' : HermLine ι'} (hb : IsBlockMap κ v) (hA : IsSmoothHerm A)
    (hp : IsPullHerm κ v A A') : IsSmoothHerm A' := by
  have hh : A'.h = A.h ∘ (fun (z' : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z' (v p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hh]
  refine ContDiffOn.comp hA ?_ ?_
  · exact (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn
  · intro z hz k
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨⟨k₁, i⟩, hp'⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have e : κ k₁ = κ k := by
      have := hb.2.2.1 ⟨k₁, i⟩
      rw [hp'] at this
      exact this.symm
    obtain rfl := hb.1 e
    exact ⟨i, by simpa [hp'] using hi'⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pull_one_of_base {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K} {xi2 : K → ℤ} (Q : AlgSq P d k₀ xi2)
    {A : HermLine ι} {A₀ : HermLine Q.ιW} (hb : FromBase k₀ A) (h : IsPullHerm (Q.κ 0) (Q.v 0) A A₀) :
    IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := by
  have hκ : ∀ k, k ≠ k₀ → Q.κ 0 k = Q.κ 1 k := fun k hk => by
    obtain ⟨i, -⟩ := Q.arithY.2.1.2.2 k
    have := congrArg Sigma.fst (Q.same ⟨k, i⟩ hk)
    rwa [(Q.block 0).2.2.1, (Q.block 1).2.2.1] at this
  refine ⟨?_, fun z' => ?_⟩
  · rw [h.1]
    funext k'
    rcases Q.all k' with ⟨k, rfl⟩ | rfl
    · by_cases hk : k = k₀
      · subst hk
        have hn : ¬ ∃ k', Q.κ 1 k' = Q.κ 0 k := by
          rintro ⟨k', hk'⟩
          by_cases h' : k' = k
          · subst h'
            exact Q.new ⟨k', hk'.symm⟩
          · exact h' ((Q.block 0).1 ((hκ k' h').trans hk'))
        rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
        rfl
      · rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hκ k hk, (Q.block 1).1.extend_apply]
    · have hn : ¬ ∃ k', Q.κ 0 k' = Q.κ 1 k₀ := Q.new
      rw [pullDeg, pullDeg, (Q.block 1).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
      rfl
  · rw [h.2]
    exact hb.2 _ _ fun p hp => by rw [Q.same p hp]

theorem swap_nat {V : Type*} {n : ℕ} (I : (Fin n → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin n → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin n), I (L ∘ σ) = I L)
    (f : ℕ → V) (hf : ∀ j, S (f j)) (a b : ℕ) (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by
  rw [← hI (fun j => f j) (fun j => hf j) (Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩)]
  congr 1
  funext j
  simp [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

theorem interp_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (k i j : ℕ) : S (interp k i x₁ x₂ a j) := by
  unfold interp
  split_ifs <;> assumption

theorem consWord_mem {V : Type*} {S : V → Prop} {x x₁ x₂ a : V} (h₀ : S x) (h₁ : S x₁) (h₂ : S x₂)
    (h₃ : S a) (k i j : ℕ) : S (consWord k i x x₁ x₂ a j) := by
  unfold consWord
  split_ifs <;> assumption

theorem word_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (D k i : ℕ) (j : Fin D) : S (word D k i x₁ x₂ a j) := by
  unfold word
  split_ifs <;> assumption

theorem consWord_left {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₁ x₁ x₂ a) (consWord_mem h₁ h₁ h₂ h₃ k i) 0 2 (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem consWord_right {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₂ x₁ x₂ a j) = I (fun j => interp k i x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₂ x₁ x₂ a) (consWord_mem h₂ h₁ h₂ h₃ k i) 1 (2 * i + 1)
      (by omega) (by omega),
    swap_nat I S hI (interp k i x₁ x₂ a) (interp_mem h₁ h₂ h₃ k i) 2 (2 * i + 2) (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem firstHalf : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ (A : HermLine ι) (A₀ : HermLine Q.ιW), IsSmoothHerm A → FromBase k₀ A → IsPullHerm (Q.κ 0) (Q.v 0) A A₀ → II K ι P (d + 2) (fun _ => A) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → II K ι P (d + 2) (mix (2 * k) Xi A) = -∑ i ∈ Finset.range k, (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1 A A₀ hAs hAb hA0
  have hR := GlobalTheory.T.algebraic_square_xi_intersection hIn II hII K ι P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1
  obtain ⟨hP1, hP0⟩ := GlobalTheory.T.algebraic_square_intersection_pullback hIn II hII K ι P d k₀ xi2 Q
  have hX0 : IsSmoothHerm X₀ := isSmoothHerm_of_pull (Q.block 0) hsm h0
  have hX1 : IsSmoothHerm X₁ := isSmoothHerm_of_pull (Q.block 1) hsm h1
  have hA0s : IsSmoothHerm A₀ := isSmoothHerm_of_pull (Q.block 0) hAs hA0
  have hA1 : IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := pull_one_of_base Q hAb hA0
  have hdeg : ((X₁.a (Q.κ 1 k₀) : ℤ) : ℝ) = -2 := by
    rw [h1.1, pullDeg, (Q.block 1).1.extend_apply, hxi, Q.xi_two_base_eq_neg_two]
    norm_num
  have hsym : ∀ L : Fin (d + 3) → HermLine Q.ιW, (∀ j, IsSmoothHerm (L j)) →
      ∀ σ : Equiv.Perm (Fin (d + 3)), II Q.KW Q.ιW Q.PW (d + 3) (L ∘ σ) = II Q.KW Q.ιW Q.PW (d + 3) L :=
    fun L hL σ => (hII.1 Q.KW Q.ιW).1 Q.PW (d + 3) L σ Q.arithW hL
  have hrot : ∀ (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L' j)) →
      IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) =
        II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons N L') := by
    intro L' N hL' hN
    rw [Fin.snoc_eq_cons_rotate]
    refine hsym (Fin.cons N L') (fun j => ?_) (finRotate _)
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hN
    · simpa using hL' j
  refine ⟨?_, ?_⟩
  · have e1 := hP1 (fun _ => A) (fun _ => A₀) X₁ (fun _ => hAs) (fun _ => hA0) hX1
    have e2 := hP0 (Fin.snoc (α := fun _ => HermLine ι) (fun _ => A) Xi)
      (Fin.snoc (α := fun _ => HermLine Q.ιW) (fun _ => A₀) X₁)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using hsm
        · simpa using hAs)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using h1
        · simpa using hA1)
    rw [e2, hdeg] at e1
    linarith
  · intro k hk hkD
    set g : ℕ → ℝ := fun i =>
      II Q.KW Q.ιW Q.PW (d + 3) (fun j : Fin (d + 3) => interp k i X₀ X₁ A₀ j) with hg
    have hstep : ∀ i ∈ Finset.range k,
        2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) = g (i + 1) - g i := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have e0 : (Fin.cons X₀ (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₀ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₀ X₀ X₁ A₀
      have e1 : (Fin.cons X₁ (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₁ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₁ X₀ X₁ A₀
      rw [← hR (word (d + 1) k i X₀ X₁ A₀) (word_mem hX0 hX1 hA0s _ _ _), e0, e1]
      have l := consWord_left (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      have r := consWord_right (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      rw [l, r]
    have h00 : g 0 = 0 := by
      rw [← hP0 (mix (1 + 2 * k) Xi A) (mix (1 + 2 * k) X₁ A₀)
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption)]
      simp only [hg]
      congr 1
      funext j
      simp only [interp, mix]
      split_ifs <;> first | rfl | omega | contradiction
    have hgk : g k = -2 * II K ι P (d + 2) (mix (2 * k) Xi A) := by
      have e := hP1 (mix (2 * k) Xi A) (mix (2 * k) X₀ A₀) X₁
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption) hX1
      rw [hrot _ X₁ (fun j => by unfold mix; split_ifs <;> assumption) hX1, hdeg] at e
      rw [← e]
      simp only [hg]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [interp]
      simp only [Fin.cons_succ, interp, mix, Fin.val_succ]
      split_ifs <;> first | rfl | omega | contradiction
    have hsum := Finset.sum_range_sub g k
    rw [← Finset.sum_congr rfl hstep, ← Finset.mul_sum, h00, hgk] at hsum
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.SqFirst
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  first | exact @GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic | exact GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic | (intros; apply GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.ample_on_generic_fibre_of_semipositive : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive | exact GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive | (intros; apply GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)


theorem _root_.GlobalTheory.T.integral_density_independent_projection : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) g y) =
      ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) g y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosIndep.cx_posPart_indep <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_boundary_normal_crossing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

private theorem zpow_finset_sum_divisor {α : Type*} (s : Finset α) (f : α → ℤ) {x : ℝ} (hx : x ≠ 0) :
    x ^ (∑ p ∈ s, f p) = ∏ p ∈ s, x ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

theorem log_muVert_h_of_mem : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (B : ℕ), ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muVert Hd B).h z) = Real.log ((muLine Hd).h z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd B z hz
  have hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal D.y) := D.arith.2.1.2.1
  have hpos := GroundTheory.Heights₂.Heights.LowerBoundFree.VertFactorPos.proof
  have hsmooth := GroundTheory.Heights₂.Heights.LowerBoundFree.VertFactorSmooth.proof hpos
  have hSB : ∀ p ∈ D.SB B, p ∈ D.S := fun p hp => (Finset.mem_filter.mp hp).1
  have hnz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  have hLpos : 0 < (muLine Hd).h z := (muLine Hd).pos z hnz
  have hVpos : ∀ p ∈ D.SB B, 0 < D.vertFactor p z := fun p hp => hpos II Ψ K J Ω W D p (hSB p hp) z hz
  have hPpos : 0 < ∏ p ∈ D.SB B, D.vertFactor p z := Finset.prod_pos hVpos
  have hF : (muVert Hd B).h z = (muLine Hd).h z * ∏ p ∈ D.SB B, D.vertFactor p z := by
    unfold muVert
    refine GroundTheory.Heights₂.Heights.LowerBoundFree.NbarSmooth.hermOfFun_h_of_mem hP ?_ hz (mul_pos hLpos hPpos)
    intro w hw c hc
    have hc' : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have h1 : (muLine Hd).h (torusSmul c w) = (∏ k, ‖c k‖ ^ Hd.aMu k) * (muLine Hd).h w :=
      (muLine Hd).smul c w hc
    have h2 : ∀ p ∈ D.SB B, D.vertFactor p (torusSmul c w) =
        (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p w :=
      fun p hp => (hsmooth II Ψ K J Ω W D p (hSB p hp)).1 w hw c hc
    have h3 : ∏ k, ‖c k‖ ^ muTwDeg Hd B k =
        (∏ k, ‖c k‖ ^ Hd.aMu k) * ∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k := by
      rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [muTwDeg, Pi.add_apply, Finset.sum_apply]
      rw [zpow_add₀ (hc' k), zpow_finset_sum_divisor _ _ (hc' k)]
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, h3]
    ring
  rw [hF, Real.log_mul hLpos.ne' hPpos.ne', Real.log_prod fun p hp => (hVpos p hp).ne']

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem _root_.GlobalTheory.T.flag_cover_block_field_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) [CharZero Φ'], (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y' = blockFnField (pairV (transPt Cv) y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.flag_adjacent_frame_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F₂ (mCoordIdeal (basePart M.blk z₀)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F₂ (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F₂ (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → ∃ (z₀' z₁' : (Σ k, ι k) → ℂ) (S : Matrix (Fin N) (Fin N) ℂ), SameOrbit z₀' z₀ ∧ SameOrbit z₁' z₁ ∧ IsBlockDiag j S ∧ S.det ≠ 0 ∧ (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F₁ (τ, i) z₀' (S * h)) ∧ (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F₁ (τ, i) z₁' (S * h * (1 + Matrix.single cb ca t))) ∧ normRhs M τ a F₁ z₀' z₁' (S * h) t = normRhs M τ a F₂ z₀ z₁ h t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.flag_adjacent_orbit_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F z₀' z₁' h' t' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_chart_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf <;> assumption)
end
