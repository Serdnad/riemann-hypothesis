module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.an_two

theorem locUnif {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (s : X → X → ℂ)
    (hO : IsOpen (bdry s)ᶜ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (h : IsRegFamilyC2 A s ph phT) :
    TendstoLocallyUniformlyOn phT ph (𝓝[>] 0) (bdry s)ᶜ := by
  intro u hu x hx
  obtain ⟨j, hj⟩ := A.cover x
  set c := A.chart j with hc
  have hO' : IsOpen (c.target ∩ c.symm ⁻¹' (bdry s)ᶜ) := c.isOpen_inter_preimage_symm hO
  have hz : c x ∈ c.target ∩ c.symm ⁻¹' (bdry s)ᶜ := by
    refine ⟨c.map_source hj, ?_⟩
    show c.symm (c x) ∈ (bdry s)ᶜ
    rw [c.left_inv hj]
    exact hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO' (c x) hz
  have hsub : Metric.closedBall (c x) (r / 2) ⊆ c.target ∩ c.symm ⁻¹' (bdry s)ᶜ :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hunif := (h j (Metric.closedBall (c x) (r / 2)) hsub (isCompact_closedBall _ _)).1
  refine ⟨c.source ∩ c ⁻¹' Metric.ball (c x) (r / 2), ?_, ?_⟩
  · apply nhdsWithin_le_nhds
    exact Filter.inter_mem (c.open_source.mem_nhds hj)
      ((c.continuousAt hj).preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hr)))
  · filter_upwards [hunif u hu] with t ht y hy
    have e : c.symm (c y) = y := c.left_inv hy.1
    have := ht (c y) (Metric.ball_subset_closedBall hy.2)
    simp only [Function.comp] at this
    rw [← hc, e] at this
    exact this

theorem mInt_zero {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) :
    mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt
  split_ifs
  · simp [integralWith]
  · rfl

end PositivityTheory.Xgp.an_two

theorem PositivityTheory.Xgp.t_an_two : ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e (σ ⊕ σ)) (d : σ → S.X → ℝ), (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → ∀ (a : σ) (w : Fin e → σ ⊕ σ), Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x)) (𝓝[>] 0) (𝓝 0) := by
  intro hC e σ S d hd hdiff a w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have ht0 : 0 < S.t₀ := (S.reg (Sum.inl a)).1
  let f : ℝ → S.X → ℝ := fun t x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x
  let gT : ℝ → S.X → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then f t else 0
  obtain ⟨M, hM⟩ := (isCompact_univ (X := S.X)).exists_bound_of_continuousOn
    (projLine_continuous_of_smooth S.A (hd a)).continuousOn
  set L : S.X → ℝ := fun y => Real.log (rW S.L S.s y) with hL
  have hL1 : ∀ y, 1 ≤ L y := by
    intro y
    have h1 : Real.exp 1 ≤ rW S.L S.s y := by
      have := S.norm_le y
      simp only [rW]
      linarith
    exact (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le h1)).mpr h1
  have hphT : ∀ b, ∀ t, 0 < t → t ≤ S.t₀ → ∀ y ∉ bdry S.s,
      |S.phT b t y| ≤ |S.C| + |S.C₅| * L y := by
    intro b t ht ht' y hy
    obtain ⟨-, -, hr⟩ := S.reg b
    obtain ⟨-, hup, hlow, -⟩ := hr t ht ht'
    obtain ⟨-, -, -, hsw⟩ := S.sing b
    have h1 := (hsw y hy).1
    have h2 := hlow y hy
    have h3 := hup y
    have hL0 : 0 ≤ L y := zero_le_one.trans (hL1 y)
    have h4 : -(|S.C₅| * L y) ≤ -S.C₅ * L y := by
      rw [neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self _) hL0)
    rw [abs_le]
    constructor
    · have := abs_nonneg S.C
      show -(|S.C| + |S.C₅| * L y) ≤ S.phT b t y
      linarith
    · have := le_abs_self S.C
      have := mul_nonneg (abs_nonneg S.C₅) hL0
      linarith
  set C₆ := 2 * |S.C| + 2 * |S.C₅| + |M| with hC₆
  have hcont : ∀ t, ContinuousOn (gT t) (bdry S.s)ᶜ := by
    intro t
    by_cases hp : 0 < t ∧ t ≤ S.t₀
    · have e1 : gT t = f t := if_pos hp
      rw [e1]
      have c1 := projLine_continuous_of_smooth S.A ((S.reg (Sum.inl a)).2.2 t hp.1 hp.2).1
      have c2 := projLine_continuous_of_smooth S.A ((S.reg (Sum.inr a)).2.2 t hp.1 hp.2).1
      have c3 := projLine_continuous_of_smooth S.A (hd a)
      exact ((c1.sub c2).sub c3).continuousOn
    · have e1 : gT t = 0 := if_neg hp
      rw [e1]
      exact continuousOn_const
  have hbound : ∀ t, ∀ y ∉ bdry S.s, |gT t y| ≤ C₆ * Real.log (rW S.L S.s y) := by
    intro t y hy
    have hLy := hL1 y
    have hC6 : 0 ≤ C₆ := by positivity
    show |gT t y| ≤ C₆ * L y
    by_cases hp : 0 < t ∧ t ≤ S.t₀
    · have e1 : gT t = f t := if_pos hp
      rw [e1]
      obtain ⟨l1, u1⟩ := abs_le.mp (hphT (Sum.inl a) t hp.1 hp.2 y hy)
      obtain ⟨l2, u2⟩ := abs_le.mp (hphT (Sum.inr a) t hp.1 hp.2 y hy)
      have a3 : |d a y| ≤ |M| := by
        have := hM y trivial
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self M)
      obtain ⟨l3, u3⟩ := abs_le.mp a3
      have m1 : |S.C| ≤ |S.C| * L y := le_mul_of_one_le_right (abs_nonneg _) hLy
      have m2 : |M| ≤ |M| * L y := le_mul_of_one_le_right (abs_nonneg _) hLy
      have hexp : C₆ * L y = 2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y := by
        rw [hC₆]
        ring
      rw [hexp, abs_le]
      constructor
      · show -(2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y) ≤
          S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y
        linarith
      · show S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y ≤
          2 * (|S.C| * L y) + 2 * (|S.C₅| * L y) + |M| * L y
        linarith
    · have e1 : gT t = 0 := if_neg hp
      rw [e1, Pi.zero_apply, abs_zero]
      exact mul_nonneg hC6 (zero_le_one.trans hLy)
  have hO : IsOpen (bdry S.s)ᶜ := (ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry S.sec).isOpen_compl
  have hlim : TendstoLocallyUniformlyOn gT 0 (𝓝[>] 0) (bdry S.s)ᶜ := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨t1, ht1, ev1⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp
      (PositivityTheory.Xgp.an_two.locUnif S.A S.s hO _ _ (S.c2 (Sum.inl a))) (ε / 2) (half_pos hε) x hx
    obtain ⟨t2, ht2, ev2⟩ := Metric.tendstoLocallyUniformlyOn_iff.mp
      (PositivityTheory.Xgp.an_two.locUnif S.A S.s hO _ _ (S.c2 (Sum.inr a))) (ε / 2) (half_pos hε) x hx
    refine ⟨t1 ∩ t2 ∩ (bdry S.s)ᶜ, Filter.inter_mem (Filter.inter_mem ht1 ht2) self_mem_nhdsWithin, ?_⟩
    filter_upwards [ev1, ev2, Ioo_mem_nhdsGT ht0] with t e1 e2 htt y hy
    have e3 : gT t = f t := if_pos ⟨htt.1, htt.2.le⟩
    have hdy := hdiff a y hy.2
    have d1 := e1 y hy.1.1
    have d2 := e2 y hy.1.2
    rw [Real.dist_eq] at d1 d2
    rw [e3, Pi.zero_apply, Real.dist_eq]
    obtain ⟨p1, q1⟩ := abs_lt.mp d1
    obtain ⟨p2, q2⟩ := abs_lt.mp d2
    rw [abs_lt]
    constructor
    · show -ε < 0 - (S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y)
      linarith
    · show 0 - (S.phT (Sum.inl a) t y - S.phT (Sum.inr a) t y - d a y) < ε
      linarith
  have key := (hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i)) 0 gT C₆ hcont hbound hlim).2
  have hz : mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) 0 = 0 :=
    PositivityTheory.Xgp.an_two.mInt_zero _ _
  rw [hz] at key
  refine key.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT ht0] with t ht
  have e1 : gT t = f t := if_pos ⟨ht.1, ht.2.le⟩
  rw [e1]
  rfl
end

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.gram_size

theorem one {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) (m : ℝ) (hm : 1 ≤ m) (hA : A.PosDef) (hB : B.PosDef)
    (h : ((m : ℂ) • B - A).PosSemidef) : Real.log A.det.re - Real.log B.det.re ≤ k * Real.log m := by
  have h1 : A.det.re ≤ ((m : ℂ) • B).det.re :=
    GroundTheory.Heights₂.Heights.FourB.HermitianDetMono.proof k ((m : ℂ) • B) A hA.posSemidef h
  have e : ((m : ℂ) • B).det.re = m ^ k * B.det.re := by
    rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hA' : 0 < A.det.re := by simpa using (Complex.lt_def.mp hA.det_pos).1
  have hB' : 0 < B.det.re := by simpa using (Complex.lt_def.mp hB.det_pos).1
  have hm' : 0 < m := by linarith
  rw [e] at h1
  have h2 := Real.log_le_log hA' h1
  rw [Real.log_mul (by positivity) hB'.ne', Real.log_pow] at h2
  linarith

end PositivityTheory.Xgp.gram_size

theorem PositivityTheory.Xgp.t_gram_size : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m := by
  intro n k G G₀ V m hm hG₀ hG h1 h2 hV
  have hinj : Function.Injective V.mulVec := Matrix.mulVec_injective_iff.mpr hV
  have hA : (Vᴴ * G * V).PosDef := hG.conjTranspose_mul_mul_same hinj
  have hB : (Vᴴ * G₀ * V).PosDef := hG₀.conjTranspose_mul_mul_same hinj
  have e1 : Vᴴ * ((m : ℂ) • G₀ - G) * V = (m : ℂ) • (Vᴴ * G₀ * V) - Vᴴ * G * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : Vᴴ * ((m : ℂ) • G - G₀) * V = (m : ℂ) • (Vᴴ * G * V) - Vᴴ * G₀ * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have p1 := h1.conjTranspose_mul_mul_same V
  have p2 := h2.conjTranspose_mul_mul_same V
  rw [e1] at p1
  rw [e2] at p2
  have a1 := PositivityTheory.Xgp.gram_size.one _ _ m hm hA hB p1
  have a2 := PositivityTheory.Xgp.gram_size.one _ _ m hm hB hA p2
  rw [abs_sub_le_iff]
  constructor <;> linarith
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.birat

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hom_mul {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k, Pi.add_apply]

theorem hom_add {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem hom_neg {f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (-f) a := by
  intro m hm k
  rw [support_neg] at hm
  exact hf m hm k

theorem hom_one : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hm
    exact hm rfl
  subst this
  simp

theorem hom_X (k : K) (i j : ι k) : ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) a ∧
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) a := by
  classical
  have key : ∀ i : ι k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)
      (fun k' => if k = k' then 1 else 0) := by
    intro i m hm k'
    rw [support_X, Finset.mem_singleton] at hm
    subst hm
    by_cases h : k = k'
    · subst h
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, h]
  exact ⟨_, key i, key j⟩

theorem ratio {Ω : Type} [Field Ω] (r : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, r ⟨k, c k⟩ = 1) (s : Ω)
    (hs : s ∈ Subfield.closure (Set.range r)) :
    ∃ (d : K → ℕ) (g h : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧ aeval r h ≠ 0 ∧ aeval r g = s * aeval r h := by
  induction hs using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    obtain ⟨a, h1, h2⟩ := hom_X k i (c k)
    exact ⟨a, _, _, h1, h2, by simp [hc], by simp [hc]⟩
  | one => exact ⟨0, 1, 1, hom_one, hom_one, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    obtain ⟨d', g', h', b1, b2, b3, b4⟩ := hy
    refine ⟨d + d', g * h' + h * g', h * h', hom_add (hom_mul a1 b2) (hom_mul a2 b1), hom_mul a2 b2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero a3 b3
    · rw [map_add (f := _), map_mul, map_mul, map_mul, a4, b4]; ring
  | neg x _ hx =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    exact ⟨d, -g, h, hom_neg a1, a2, a3, by rw [map_neg, a4]; ring⟩
  | inv x _ hx =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    by_cases h0 : x = 0
    · exact ⟨d, g, h, a1, a2, a3, by rw [a4, h0, inv_zero]⟩
    · exact ⟨d, h, g, a2, a1, by rw [a4]; exact mul_ne_zero h0 a3, by rw [a4, inv_mul_cancel_left₀ h0]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    obtain ⟨d', g', h', b1, b2, b3, b4⟩ := hy
    refine ⟨d + d', g * g', h * h', hom_mul a1 b1, hom_mul a2 b2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero a3 b3
    · rw [map_mul, map_mul, a4, b4]; ring

end PositivityTheory.Xgp.birat

open PositivityTheory.Xgp.birat in
theorem PositivityTheory.Xgp.t_birat : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∃ (Ω' : Type) (_ : Field Ω') (y' : (Σ k, ι k) → Ω'), mCoordIdeal y' = mCoordIdeal y ∧ Birational y' := by
  intro K _ ι _ Ω _ y hy
  choose c hc using hy
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  let F : Subfield Ω := Subfield.closure (Set.range r)
  let y' : (Σ k, ι k) → F := fun p => ⟨r p, Subfield.subset_closure ⟨p, rfl⟩⟩
  have hev : ∀ g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι, ((aeval y' g : F) : Ω) = aeval r g := fun g => by
    have : (F.subtype.toIntAlgHom).comp (aeval y') = aeval r := by
      ext p
      simp [y']
    exact AlgHom.congr_fun this g
  refine ⟨F, inferInstance, y', ?_, fun s => ?_⟩
  · let θ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩) * X k
    let θ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k
    have hθ : θ'.comp θ = AlgHom.id Ω _ := by
      refine MvPolynomial.algHom_ext fun k => ?_
      simp only [θ, θ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
    have hθi : Function.Injective θ := Function.LeftInverse.injective (g := θ') (AlgHom.congr_fun hθ)
    let ψ : MvPolynomial K F →+* MvPolynomial K Ω := θ.toRingHom.comp (MvPolynomial.map F.subtype)
    have hψ : Function.Injective ψ := hθi.comp (MvPolynomial.map_injective _ F.subtype.injective)
    have e : ψ.comp (mConeMap y').toRingHom = (mConeMap y).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
      have e1 : mConeMap y' (X p) = C (y' p) * X p.1 := aeval_X _ p
      have e2 : mConeMap y (X p) = C (y p) * X p.1 := aeval_X _ p
      show θ (MvPolynomial.map F.subtype (mConeMap y' (X p))) = mConeMap y (X p)
      rw [e1, e2]
      simp only [θ, map_mul, map_C, map_X, aeval_X, aeval_C, algebraMap_eq]
      rw [← mul_assoc, ← C_mul]
      congr 2
      exact div_mul_cancel₀ _ (hc _)
    ext g
    show mConeMap y' g = 0 ↔ mConeMap y g = 0
    rw [show mConeMap y g = ψ (mConeMap y' g) from (RingHom.congr_fun e g).symm]
    exact (map_eq_zero_iff ψ hψ).symm
  · obtain ⟨d, g, h, a1, a2, a3, a4⟩ := ratio r c (fun k => div_self (hc k)) s.1 s.2
    refine ⟨d, g, h, a1, a2, fun h0 => a3 (by rw [← hev, h0]; rfl), Subtype.ext ?_⟩
    rw [Subfield.coe_mul, hev, hev, a4]
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_pol_sec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 := by
  intro K _ ι _ Ω _ y α dβ hy hex
  obtain ⟨k, hk, e, he, hne⟩ := hex
  choose i hi using hy
  set D := ∑ κ, dβ κ with hDdef
  have hD : ∀ κ, dβ κ ≤ D := fun κ =>
    Finset.single_le_sum (f := dβ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)
  refine ⟨(D + 1) * k, le_trans hk (Nat.le_mul_of_pos_left k (Nat.succ_pos D)),
    e ^ (D + 1) * ∏ κ, y ⟨κ, i κ⟩ ^ (D - dβ κ), ?_, ?_⟩
  · intro c hc
    have h1 := he c hc
    have key : e ^ (D + 1) * (∏ κ, y ⟨κ, i κ⟩ ^ (D - dβ κ)) *
        ∏ κ, y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((((D + 1) * k : ℕ) : ℤ) * α κ - 1 - (dβ κ : ℤ))))
        = (e * ∏ κ, y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)))) ^ (D + 1) *
          ∏ κ, (y ⟨κ, i κ⟩ / y ⟨κ, c κ⟩) ^ (D - dβ κ) := by
      rw [mul_pow, ← Finset.prod_pow, mul_assoc, mul_assoc]
      congr 1
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun κ _ => ?_)
      have hyc : y ⟨κ, c κ⟩ ≠ 0 := hc κ
      rw [div_pow, ← zpow_natCast (y ⟨κ, c κ⟩) (D - dβ κ),
        ← zpow_natCast (y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)))) (D + 1), ← zpow_mul]
      have hexp : -(((1 : ℕ) : ℤ) * ((((D + 1) * k : ℕ) : ℤ) * α κ - 1 - (dβ κ : ℤ)))
          = -(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)) * ((D + 1 : ℕ) : ℤ) - ((D - dβ κ : ℕ) : ℤ) := by
        rw [Nat.cast_sub (hD κ)]
        push_cast
        ring
      rw [hexp, zpow_sub₀ hyc]
      ring
    rw [key]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ h1 _) (Subalgebra.prod_mem _ (fun κ _ => ?_))
    refine Subalgebra.pow_mem _ ?_ _
    unfold chartRingZ
    exact Algebra.subset_adjoin (Set.mem_range.2 ⟨⟨κ, i κ⟩, rfl⟩)
  · exact mul_ne_zero (pow_ne_zero _ hne)
      (Finset.prod_ne_zero_iff.2 fun κ _ => pow_ne_zero _ (hi κ))
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_line_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  intro K _ ι _ A hA
  have hne : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ∀ k, ∃ i, (fun p => starRingEnd ℂ (z p)) ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa using hi⟩
  refine ⟨⟨A.a, fun z => Real.sqrt (A.h z * A.h fun p => starRingEnd ℂ (z p)), ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · intro z hz
    exact Real.sqrt_pos.2 (mul_pos (A.pos z hz) (A.pos _ (hne z hz)))
  · intro c z hc
    have h1 := A.smul (fun k => starRingEnd ℂ (c k)) (fun p => starRingEnd ℂ (z p)) (fun k => by simpa using hc k)
    simp only [RCLike.norm_conj] at h1
    simp only [map_mul]
    rw [h1, A.smul c z hc]
    have h0 : 0 ≤ ∏ k, ‖c k‖ ^ A.a k := Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    rw [mul_mul_mul_comm, Real.sqrt_mul (mul_nonneg h0 h0), Real.sqrt_mul_self h0]
  · have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => fun p => starRingEnd ℂ (z p)) := by
      refine contDiff_pi.2 fun p => ?_
      exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) p)
    refine ContDiffOn.sqrt (ContDiffOn.mul hA (hA.comp hc.contDiffOn fun z hz => hne z hz)) ?_
    intro z hz
    exact (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).ne'
  · intro z
    simp only [Complex.conj_conj, mul_comm]
  · intro z hz
    show Real.log (Real.sqrt _) = _
    rw [Real.log_sqrt (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).le,
      Real.log_mul (A.pos z hz).ne' (A.pos _ (hne z hz)).ne']
end
