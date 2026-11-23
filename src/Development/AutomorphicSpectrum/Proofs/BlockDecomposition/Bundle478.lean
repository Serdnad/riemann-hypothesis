module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinearODE

noncomputable def companion (p : Polynomial ℂ) (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i =>
    if h : (i : ℕ) + 1 < n then LinearMap.proj ⟨i + 1, h⟩
    else - ∑ k : Fin n, p.coeff k • LinearMap.proj k

theorem top_eq {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) (s : ℝ) :
    F p.natDegree s = - ∑ k : Fin p.natDegree, p.coeff k * F k s := by
  have h := hrel s
  rw [Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h
  have e : ∑ k : Fin p.natDegree, p.coeff k * F k s =
      ∑ k ∈ Finset.range p.natDegree, p.coeff k * F k s :=
    (Finset.sum_range (fun k => p.coeff k * F k s)).symm
  rw [e]
  linear_combination h

theorem lower_eq_zero {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k < p.natDegree, F k = 0 := by
  let X : ℝ → (Fin p.natDegree → ℂ) := fun s i => F i s
  have hX : ∀ s, HasDerivAt X (companion p p.natDegree (X s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have e : companion p p.natDegree (X s) i = F (i + 1) s := by
      simp only [companion, LinearMap.pi_apply]
      split_ifs with h
      · rfl
      · have hi : (i : ℕ) + 1 = p.natDegree := by
          have := i.isLt
          omega
        rw [hi, top_eq hp hrel s]
        simp [X, LinearMap.sum_apply, smul_eq_mul]
    rw [e]
    exact hF i s
  have hA : LipschitzWith ‖LinearMap.toContinuousLinearMap (companion p p.natDegree)‖₊
      (companion p p.natDegree) := by
    have := (LinearMap.toContinuousLinearMap (companion p p.natDegree)).lipschitz
    simpa using this
  have hzero : ∀ s, X s = 0 := by
    intro s
    have key := ODE_solution_unique_of_mem_Icc (v := fun _ => companion p p.natDegree)
      (s := fun _ => Set.univ) (a := -(|s| + 1)) (b := |s| + 1) (t₀ := 0)
      (fun t _ => hA.lipschitzOnWith)
      ⟨by linarith [abs_nonneg s], by linarith [abs_nonneg s]⟩
      (fun t _ => (hX t).continuousAt.continuousWithinAt) (fun t _ => hX t)
      (fun _ _ => Set.mem_univ _)
      (continuousOn_const (c := (0 : Fin p.natDegree → ℂ)))
      (fun t _ => by simpa using hasDerivAt_const t (0 : Fin p.natDegree → ℂ))
      (fun _ _ => Set.mem_univ _)
      (by funext i; simpa [X] using h0 i i.isLt)
    exact key ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
  intro k hk
  funext s
  simpa [X] using congrFun (hzero s) ⟨k, hk⟩

theorem chain_zero {F : ℕ → ℝ → ℂ} (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    {m : ℕ} (h : F m = 0) : ∀ k, m ≤ k → F k = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k hmk ih =>
    funext s
    have h1 := hF k s
    rw [ih] at h1
    show F (k + 1) s = 0
    exact h1.unique (hasDerivAt_const s (0 : ℂ))

theorem eq_zero_of_initial {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k, F k = 0 := by
  have hlow := lower_eq_zero hp hF hrel h0
  have htop : F p.natDegree = 0 := by
    funext s
    rw [top_eq hp hrel s]
    have hz : ∀ k : Fin p.natDegree, p.coeff k * F k s = 0 := fun k => by
      rw [hlow k k.isLt]
      simp
    simp [hz]
  intro k
  rcases lt_or_ge k p.natDegree with hk | hk
  · exact hlow k hk
  · exact chain_zero hF htop k hk

def solSpace (p : Polynomial ℂ) : Submodule ℂ (ℕ → ℝ → ℂ) where
  carrier := {F | (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) ∧
    ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0}
  add_mem' := by
    rintro F G ⟨hF, rF⟩ ⟨hG, rG⟩
    refine ⟨fun k s => (hF k s).add (hG k s), fun s => ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, rF s, rG s, add_zero]
  zero_mem' := ⟨fun k s => hasDerivAt_const s (0 : ℂ), fun s => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, rF⟩
    refine ⟨fun k s => (hF k s).const_mul c, fun s => ?_⟩
    have h : ∀ k, p.coeff k * (c • F) k s = c * (p.coeff k * F k s) := fun k => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h, ← Finset.mul_sum, rF s, mul_zero]

theorem finiteDimensional_solSpace {p : Polynomial ℂ} (hp : p.Monic) :
    FiniteDimensional ℂ (solSpace p) := by
  let Φ : solSpace p →ₗ[ℂ] (Fin p.natDegree → ℂ) :=
    { toFun := fun F i => (F : ℕ → ℝ → ℂ) i 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun F hF => ?_)
  obtain ⟨hFd, hFr⟩ := F.2
  have hz := eq_zero_of_initial hp hFd hFr (fun k hk => congrFun hF ⟨k, hk⟩)
  exact Subtype.ext (funext hz)

theorem deriv_zero_eq_sum :
    ∀ p : Polynomial ℂ, p.Monic → ∃ (T : Finset ℝ) (w : ℝ → ℂ), ∀ F : ℕ → ℝ → ℂ,
      (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) →
      (∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) →
      F 1 0 = ∑ t ∈ T, w t * F 0 t := by
  intro p hp
  haveI := finiteDimensional_solSpace hp
  let ev : ℝ → Module.Dual ℂ (solSpace p) := fun t =>
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 0 t
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  let φ : Module.Dual ℂ (solSpace p) :=
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 1 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hco : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_dualCoannihilator] at hF
    have h0 : (F : ℕ → ℝ → ℂ) 0 = 0 :=
      funext fun t => hF (ev t) (Submodule.subset_span ⟨t, rfl⟩)
    obtain ⟨hFd, -⟩ := F.2
    have hall := chain_zero hFd h0
    rw [Submodule.mem_bot]
    exact Subtype.ext (funext fun k => hall k (Nat.zero_le k))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hco,
      Submodule.dualAnnihilator_bot]
  have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφ
  refine ⟨c.support, c, fun F hFd hFr => ?_⟩
  have hmem : F ∈ solSpace p := ⟨hFd, hFr⟩
  have key := LinearMap.congr_fun hc ⟨F, hmem⟩
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply] at key
  exact key.symm

end GlobalTheory.CompanionTheory.LinearODE
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem setIntegral_translate_of_iff {X : Type} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (m : Measure X)
    [m.IsAddHaarMeasure] {A D : Set X} (hA : MeasurableSet A) (hD : MeasurableSet D) (g : X)
    (h : ∀ y, g + y ∈ A ↔ y ∈ D) (f : X → ℂ) :
    ∫ x in A, f x ∂m = ∫ y in D, f (g + y) ∂m := by
  rw [← integral_indicator hA, ← integral_indicator hD,
    ← integral_add_left_eq_self (μ := m) (Set.indicator A f) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ D
  · simp [Set.indicator, hy, (h y).2 hy]
  · have : g + y ∉ A := fun hh => hy ((h y).1 hh)
    simp [Set.indicator, hy, this]

theorem weyl_sq_compact_open : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ) (B : X → X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) →
    (∀ x y, q (x + y) = q x * q y * B x y) →
    (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y y', B x (y + y') = B x y * B x y') →
    ∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤
      (m (L : Set X)).toReal * (m {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1}).toReal := by
  intro X _ _ _ _ _ _ _ m _ L hLc hLo q B hq hq1 hqB hB1 hB2 x₀
  set C : Set X := {y | y - x₀ ∈ L} with hCdef
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hCo : IsOpen C := hLo.preimage (continuous_id.sub continuous_const)
  have hCm : MeasurableSet C := hCo.measurableSet
  have hLfin : m (L : Set X) < ⊤ := hLc.measure_lt_top
  have hmC : m C = m (L : Set X) := by
    have : C = (fun h => -x₀ + h) ⁻¹' (L : Set X) := by
      ext y; simp [hCdef, sub_eq_neg_add]
    rw [this, measure_preimage_add]
  have hCfin : m C < ⊤ := hmC ▸ hLfin
  haveI : IsFiniteMeasure (m.restrict C) := ⟨by simpa using hCfin⟩
  haveI : IsFiniteMeasure (m.restrict (L : Set X)) := ⟨by simpa using hLfin⟩
  have hq0 : ∀ x, q x ≠ 0 := fun x h => by simpa [h] using hq1 x
  have hBnorm : ∀ x y, ‖B x y‖ = 1 := fun x y => by
    have := congrArg norm (hqB x y)
    simpa [hq1] using this.symm
  have hBform : ∀ x y, B x y = q (x + y) / (q x * q y) := fun x y => by
    rw [hqB x y]; field_simp [hq0 x, hq0 y]
  have hBc : Continuous (Function.uncurry B) := by
    have : Function.uncurry B = fun p : X × X => q (p.1 + p.2) / (q p.1 * q p.2) := by
      funext p; exact hBform p.1 p.2
    rw [this]
    exact (hq.comp (continuous_fst.add continuous_snd)).div
      ((hq.comp continuous_fst).mul (hq.comp continuous_snd)) fun p => mul_ne_zero (hq0 _) (hq0 _)
  have hconj : ∀ x, (starRingEnd ℂ) (q x) * q x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hq1]; simp
  set I : ℂ := ∫ x in C, q x ∂m with hI
  set J : X → ℂ := fun y => ∫ x in C, B x y ∂m with hJ

  have hstep : I * (starRingEnd ℂ) I = ∫ y in (L : Set X), q y * J y ∂m := by
    have h1 : I * (starRingEnd ℂ) I = ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m := by
      rw [integral_mul_const, integral_conj, mul_comm]
    have h2 : ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m
        = ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m := by
      refine setIntegral_congr_fun hCm fun x' hx' => ?_
      have hx'' : x' - x₀ ∈ L := hx'
      have ht : I = ∫ y in (L : Set X), q (x' + y) ∂m := by
        refine setIntegral_translate_of_iff m hCm hLm x' (fun y => ?_) q
        have e : x' + y - x₀ = (x' - x₀) + y := by abel
        simp only [hCdef, Set.mem_setOf_eq, e, SetLike.mem_coe]
        exact L.add_mem_cancel_left hx''
      rw [ht, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      rw [hqB x' y]
      calc _ = ((starRingEnd ℂ) (q x') * q x') * (q y * B x' y) := by ring
        _ = _ := by rw [hconj, one_mul]
    have h3 : ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m
        = ∫ y in (L : Set X), ∫ x' in C, q y * B x' y ∂m ∂m := by
      refine integral_integral_swap ?_
      have hc : Continuous (Function.uncurry fun x' y => q y * B x' y) :=
        (hq.comp continuous_snd).mul hBc
      refine Integrable.of_bound hc.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun p => ?_)
      simp [Function.uncurry, hq1, hBnorm]
    rw [h1, h2, h3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hJ]
    rw [integral_const_mul]
  have hJle : ∀ y, ‖J y‖ ≤ (m (L : Set X)).toReal := fun y => by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := C) (f := fun x => B x y) (C := 1)
      hCfin (fun x _ => (hBnorm x y).le)
    simpa [Measure.real, hmC] using this
  have hJ0 : ∀ y l, l ∈ L → B l y ≠ 1 → J y = 0 := fun y l hl hne => by
    have ht : J y = ∫ x in C, B (l + x) y ∂m := by
      refine setIntegral_translate_of_iff m hCm hCm l (fun x => ?_) (fun x => B x y)
      have e : l + x - x₀ = l + (x - x₀) := by abel
      simp only [hCdef, Set.mem_setOf_eq, e]
      exact L.add_mem_cancel_left hl
    have h2 : J y = B l y * J y := by
      conv_lhs => rw [ht]
      simp only [hJ, hB1, integral_const_mul]
    have h3 : (1 - B l y) * J y = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h
  set S : Set X := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hSL : S ⊆ (L : Set X) := fun y hy => hy.1
  have hSfin : m S < ⊤ := (measure_mono hSL).trans_lt hLfin
  have hcut : ∫ y in (L : Set X), q y * J y ∂m = ∫ y in S, q y * J y ∂m := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hLm hSL fun y hy => ?_
    have : ¬ ∀ l ∈ L, B l y = 1 := fun h => hy.2 ⟨hy.1, h⟩
    push_neg at this
    obtain ⟨l, hl, hne⟩ := this
    simp [hJ0 y l hl hne]
  have hbound : ‖∫ y in S, q y * J y ∂m‖ ≤ (m (L : Set X)).toReal * (m S).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := S) (f := fun y => q y * J y)
      (C := (m (L : Set X)).toReal) hSfin (fun y _ => by simpa [hq1] using hJle y)
    simpa [Measure.real] using this
  have hsq : ‖I‖ ^ 2 = ‖I * (starRingEnd ℂ) I‖ := by
    rw [norm_mul, RCLike.norm_conj, sq]
  rw [hsq, hstep, hcut]
  exact hbound

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound

theorem twisted_integral_finite_coset_combination_bound :
    ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) → ∀ K : ℝ,
    (∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤ K) →
    ∀ (Q : X → ℂ) (s : Finset X),
    (∀ x, Q x = ∑ a ∈ s, Q a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x) →
    ‖∫ x, Q x * q x ∂m‖ ≤ (∑ a ∈ s, ‖Q a‖) * √K := by
  intro X _ _ _ _ _ _ _ m _ L hc ho q hq hn K hK Q s hQ
  have hopen : ∀ a : X, IsOpen {y : X | y - a ∈ L} := fun a =>
    ho.preimage (continuous_id.sub continuous_const)
  have hmeas : ∀ a : X, MeasurableSet {y : X | y - a ∈ L} := fun a => (hopen a).measurableSet
  have hcomp : ∀ a : X, IsCompact {y : X | y - a ∈ L} := by
    intro a
    have himg : {y : X | y - a ∈ L} = (fun x => x + a) '' (L : Set X) := by
      ext y
      constructor
      · intro hy
        exact ⟨y - a, hy, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [himg]
    exact hc.image (continuous_id.add continuous_const)
  have hion : ∀ a : X, IntegrableOn q {y : X | y - a ∈ L} m := fun a =>
    hq.continuousOn.integrableOn_compact (hcomp a)
  have hterm : ∀ a : X, (fun x => Set.indicator {y : X | y - a ∈ L} (fun _ => (1 : ℂ)) x * q x)
      = Set.indicator {y : X | y - a ∈ L} q := by
    intro a
    funext x
    by_cases hx : x ∈ {y : X | y - a ∈ L}
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hint : ∀ a : X, Integrable (Set.indicator {y : X | y - a ∈ L} q) m := fun a =>
    (integrable_indicator_iff (hmeas a)).2 (hion a)
  have hfun : (fun x => Q x * q x)
      = fun x => ∑ a ∈ s, Q a * Set.indicator {y : X | y - a ∈ L} q x := by
    funext x
    conv_lhs => rw [hQ x]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, congrFun (hterm a) x]
  have hsum : ∫ x, Q x * q x ∂m = ∑ a ∈ s, Q a * ∫ x in {y : X | y - a ∈ L}, q x ∂m := by
    rw [hfun, integral_finsetSum s (fun a _ => (hint a).const_mul (Q a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, integral_indicator (hmeas a)]
  have hone : ∀ a : X, ‖∫ x in {y : X | y - a ∈ L}, q x ∂m‖ ≤ √K := by
    intro a
    have h := Real.abs_le_sqrt (hK a)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hone a) (norm_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound
end
