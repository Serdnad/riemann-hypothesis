module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle050
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle052
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle053
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle055
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle056
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
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Composition
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
import Formalism.RealPlaceAnalysis.Bundle001
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

section

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.AnalyticGermSlice

theorem isAnalyticNear_zeros_inter {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ}
    (hX : IsAnalyticNear X w) {m : ℕ} (g : Fin m → (σ → ℂ) → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) Set.univ) :
    IsAnalyticNear {z | z ∈ X ∧ ∀ i, g i z = 0} w := by
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  refine ⟨N, k + m, Fin.append f g, hN, hwN, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j => rw [Fin.append_left]; exact hf j
    | right j => rw [Fin.append_right]; exact (hg j).mono (Set.subset_univ N)
  · ext z
    have hz := Set.ext_iff.1 hXN z
    constructor
    · rintro ⟨⟨hzX, hg0⟩, hzN⟩
      refine ⟨hzN, (Fin.forall_fin_add _).2 ⟨fun j => ?_, fun j => ?_⟩⟩
      · rw [Fin.append_left]; exact (hz.1 ⟨hzX, hzN⟩).2 j
      · rw [Fin.append_right]; exact hg0 j
    · rintro ⟨hzN, hall⟩
      have h2 := (Fin.forall_fin_add _).1 hall
      refine ⟨⟨(hz.2 ⟨hzN, fun j => ?_⟩).1, fun j => ?_⟩, hzN⟩
      · have := h2.1 j
        rwa [Fin.append_left] at this
      · have := h2.2 j
        rwa [Fin.append_right] at this

private theorem exists_eventually_eq_zero_of_prod_analyticAt {n : ℕ} (a : ℂ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) a) (hP : ∀ᶠ t in 𝓝 a, ∏ i, f i t = 0) :
    ∃ i, ∀ᶠ t in 𝓝 a, f i t = 0 := by
  by_contra hcon
  have hcon' : ∀ i, ¬ ∀ᶠ t in 𝓝 a, f i t = 0 := fun i hi => hcon ⟨i, hi⟩
  have hne : ∀ i, ∀ᶠ t in 𝓝[≠] a, f i t ≠ 0 := fun i =>
    ((hf i).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hcon' i)
  have hall : ∀ᶠ t in 𝓝[≠] a, ∀ i, f i t ≠ 0 := Filter.eventually_all.2 hne
  have hP' : ∀ᶠ t in 𝓝[≠] a, ∏ i, f i t = 0 := nhdsWithin_le_nhds hP
  obtain ⟨t, ht1, ht2⟩ := (hall.and hP').exists
  exact (Finset.prod_ne_zero_iff.2 fun i _ => ht1 i) ht2

theorem exists_irreducible_slice :
    FiniteGermProjectionOpenAt.Statement → GermFiniteProjection.Statement → AnalyticGermComponents.Statement → ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) → ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧ IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧ ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  intro hFG hGF hAC σ _ X w hX hirr hacc
  obtain ⟨d, A, ⟨W0, hW0, hfib⟩, hdom⟩ := hGF σ X w hX hirr
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨y, ⟨hyW, hyX⟩, hyw⟩ := (accPt_iff_nhds.1 hacc) W0 hW0
      exact absurd (hfib y ⟨hyX, hyW⟩ (Subsingleton.elim _ _)) hyw
    · exact h0
  let i0 : Fin d := ⟨0, hd⟩
  let g : Fin d → (σ → ℂ) → ℂ := fun j z => if j = i0 then 0 else A z j - A w j
  have hgan : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ := by
    intro j
    by_cases hj : j = i0
    · simp only [g, hj, if_true]
      exact analyticOnNhd_const
    · simp only [g, hj, if_false]
      exact (((ContinuousLinearMap.proj j).comp A).analyticOnNhd _).sub analyticOnNhd_const
  let S : Set (σ → ℂ) := {z | z ∈ X ∧ ∀ j, g j z = 0}
  have hSan : IsAnalyticNear S w := isAnalyticNear_zeros_inter hX g hgan
  have hwS : w ∈ S := ⟨hirr.1, fun j => by by_cases hj : j = i0 <;> simp [g, hj]⟩
  obtain ⟨n, Y, hYi, W1, hW1, hYeq⟩ := hAC σ S w hSan hwS
  let A1 : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.proj i0).comp A
  have hA1 : ∀ z k, A1 z k = A z i0 := fun z k => rfl
  have hfibS : ∀ x ∈ S ∩ W0, A1 x = A1 w → x = w := by
    rintro x ⟨⟨hxX, hxg⟩, hxW⟩ hx
    refine hfib x ⟨hxX, hxW⟩ (funext fun j => ?_)
    by_cases hj : j = i0
    · subst hj
      have := congrFun hx 0
      simpa [hA1] using this
    · have := hxg j
      simp only [g, hj, if_false, sub_eq_zero] at this
      exact this
  have himg : ∀ V ∈ 𝓝 w, A1 '' (S ∩ V) ∈ 𝓝 (A1 w) := by
    intro V hV
    have hbig := hFG σ X w d A hX ⟨W0, hW0, hfib⟩ hdom V hV
    let ψ : (Fin 1 → ℂ) → (Fin d → ℂ) := fun y j => if j = i0 then y 0 else A w j
    have hψc : Continuous ψ := by
      refine continuous_pi fun j => ?_
      by_cases hj : j = i0
      · simp only [ψ, hj, if_true]
        exact continuous_apply 0
      · simp only [ψ, hj, if_false]
        exact continuous_const
    have hψw : ψ (A1 w) = A w := by
      funext j
      by_cases hj : j = i0
      · subst hj
        simp [ψ, hA1]
      · simp [ψ, hj]
    have hpre : ψ ⁻¹' (A '' (X ∩ V)) ∈ 𝓝 (A1 w) := by
      apply hψc.continuousAt.preimage_mem_nhds
      rw [hψw]
      exact hbig
    refine Filter.mem_of_superset hpre ?_
    rintro y ⟨x, ⟨hxX, hxV⟩, hxy⟩
    refine ⟨x, ⟨⟨hxX, fun j => ?_⟩, hxV⟩, ?_⟩
    · by_cases hj : j = i0
      · simp [g, hj]
      · have := congrFun hxy j
        simp only [ψ, hj, if_false] at this
        simp [g, hj, this]
    · funext k
      have := congrFun hxy i0
      simp only [ψ, if_true] at this
      rw [hA1, this, Subsingleton.elim k 0]
  have hdomi : ∃ i, ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) →
      (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) → ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
    by_contra hcon
    have hcon' : ∀ i, ∃ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) ∧
        (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) ∧ ¬ ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, fun h ha hz => by
        by_contra hy
        exact hi ⟨h, ha, hz, hy⟩⟩
    choose h hha hhz hhnz using hcon'
    let c : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
    let a : ℂ := A w i0
    have hca : c a = A1 w := by
      funext k
      rfl
    have hback : ∀ φ : (Fin 1 → ℂ) → ℂ, (∀ᶠ t in 𝓝 a, φ (c t) = 0) → ∀ᶠ y in 𝓝 (A1 w), φ y = 0 := by
      intro φ hφ
      have hev : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 (A1 w)) (𝓝 a) :=
        (continuous_apply 0).tendsto' _ _ rfl
      filter_upwards [hev.eventually hφ] with y hy
      have hyc : c (y 0) = y := by
        funext k
        rw [Subsingleton.elim k 0]
        rfl
      rwa [hyc] at hy
    have hfan : ∀ i, AnalyticAt ℂ (fun t => h i (c t)) a := by
      intro i
      have h1 : AnalyticAt ℂ (h i) (c a) := by
        rw [hca]
        exact hha i
      exact h1.comp (c.analyticAt a)
    have hPz : ∀ᶠ t in 𝓝 a, ∏ i, h i (c t) = 0 := by
      have hV : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y i → h i (A1 z) = 0 := Filter.eventually_all.2 hhz
      have hV' : {z | ∀ i, z ∈ Y i → h i (A1 z) = 0} ∩ W1 ∈ 𝓝 w := Filter.inter_mem hV hW1
      have hI := himg _ hV'
      have hy : ∀ᶠ y in 𝓝 (A1 w), ∏ i, h i y = 0 := by
        filter_upwards [hI] with y hy
        obtain ⟨x, ⟨hxS, hxV, hxW⟩, rfl⟩ := hy
        have hxU : x ∈ (⋃ i, Y i) ∩ W1 := by
          rw [← hYeq]
          exact ⟨hxS, hxW⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxU.1
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hxV i hi)
      have hev : Tendsto c (𝓝 a) (𝓝 (A1 w)) := by
        rw [← hca]
        exact c.continuous.tendsto a
      exact hev.eventually hy
    obtain ⟨i, hi⟩ := exists_eventually_eq_zero_of_prod_analyticAt a (fun i t => h i (c t)) hfan hPz
    exact hhnz i (hback (h i) hi)
  obtain ⟨i, hi⟩ := hdomi
  refine ⟨Y i, W1, A1, hW1, ?_, (hYi i).1, (hYi i).2, ⟨W1 ∩ W0, Filter.inter_mem hW1 hW0, ?_⟩, hi⟩
  · rintro z ⟨hzY, hzW⟩
    have hzU : z ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hzY⟩, hzW⟩
    rw [← hYeq] at hzU
    exact hzU.1.1
  · rintro x ⟨hxY, hxW1, hxW0⟩ hx
    have hxU : x ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hxY⟩, hxW1⟩
    rw [← hYeq] at hxU
    exact hfibS x ⟨hxU.1, hxW0⟩ hx

end GlobalTheory.CompanionTheory.AnalyticGermSlice
end

section

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.ComplexSets

variable {σ : Type} [Fintype σ]

theorem exists_equation_not_vanishing {Y Z : Set (σ → ℂ)} {w : σ → ℂ} (hZ : IsAnalyticNear Z w)
    (hYZ : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) :
    ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (∀ᶠ z in 𝓝 w, z ∈ Z → φ z = 0) ∧
      ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 := by
  obtain ⟨N, k, f, hN, hwN, hf, hZN⟩ := hZ
  by_contra hcon
  push_neg at hcon
  apply hYZ
  have hall : ∀ i, ∀ᶠ z in 𝓝 w, z ∈ Y → f i z = 0 := by
    intro i
    apply hcon (f i) (hf i w hwN)
    filter_upwards [hN.mem_nhds hwN] with z hzN hzZ
    have hz : z ∈ Z ∩ N := ⟨hzZ, hzN⟩
    rw [hZN] at hz
    exact hz.2 i
  have hall' : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y → f i z = 0 := Filter.eventually_all.mpr hall
  filter_upwards [hall', hN.mem_nhds hwN] with z hz hzN hzY
  have hz' : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
  rw [← hZN] at hz'
  exact hz'.1

theorem not_eventually_prod_eq_zero {ι : Type} {Y : Set (σ → ℂ)} {w : σ → ℂ}
    (hY : GermIrreducibleAt Y w) (φ : ι → (σ → ℂ) → ℂ) (s : Finset ι)
    (hφ : ∀ j ∈ s, AnalyticAt ℂ (φ j) w)
    (hne : ∀ j ∈ s, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ j z = 0) :
    ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → ∏ j ∈ s, φ j z = 0 := by
  classical
  obtain ⟨hwY, hirr⟩ := hY
  revert hφ hne
  refine Finset.induction_on s ?_ ?_
  · intro _ _ h
    have h0 := h.self_of_nhds hwY
    simp at h0
  · intro a s has ih hφ hne h
    simp_rw [Finset.prod_insert has] at h
    rcases hirr (φ a) (fun z => ∏ j ∈ s, φ j z) (hφ a (Finset.mem_insert_self a s))
        (by simpa only [Finset.prod_fn] using
          Finset.analyticAt_prod s fun j hj => hφ j (Finset.mem_insert_of_mem hj)) h with h1 | h1
    · exact hne a (Finset.mem_insert_self a s) h1
    · exact ih (fun j hj => hφ j (Finset.mem_insert_of_mem hj))
        (fun j hj => hne j (Finset.mem_insert_of_mem hj)) h1

theorem exists_subfamily_no_containment {ι : Type} [Finite ι] (Y : ι → Set (σ → ℂ)) (w : σ → ℂ) :
    ∃ T : Finset ι, (∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i) ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  let P : Finset ι → Prop := fun T => ∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i
  have hP : P Finset.univ := Filter.Eventually.of_forall fun z => by simp
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P) Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩⟩
  rw [Finset.mem_filter] at hT
  refine ⟨T, hT.2, ?_⟩
  intro i hi j hj hij hsub
  have hP' : P (T.erase i) := by
    filter_upwards [hT.2, hsub] with z hz hzs
    rw [hz]
    constructor
    · rintro ⟨m, hm, hzm⟩
      by_cases hmi : m = i
      · rw [hmi] at hzm
        exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hzs hzm⟩
      · exact ⟨m, Finset.mem_erase.mpr ⟨hmi, hm⟩, hzm⟩
    · rintro ⟨m, hm, hzm⟩
      exact ⟨m, Finset.mem_of_mem_erase hm, hzm⟩
  have hle := hmin (T.erase i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)
  have hlt := Finset.card_erase_lt_of_mem hi
  omega

theorem dominant_of_open {ι : Type} [Fintype ι] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    {S W : Set (σ → ℂ)} {w : σ → ℂ} (Y : ι → Set (σ → ℂ))
    (hopen : ∀ x ∈ S, ∀ V ∈ 𝓝 x, A '' (S ∩ V) ∈ 𝓝 (A x))
    (hYan : ∀ i, IsAnalyticNear (Y i) w) (hYirr : ∀ i, GermIrreducibleAt (Y i) w)
    (hno : ∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j)
    (hW : W ∈ 𝓝 w) (hS : S ∩ W = (⋃ i, Y i) ∩ W) (i : ι)
    (h : (Fin d → ℂ) → ℂ) (hh : AnalyticAt ℂ h (A w))
    (hv : ∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) :
    ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  classical
  have hsep : ∀ j, ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (j ≠ i →
      (∀ᶠ z in 𝓝 w, z ∈ Y j → φ z = 0) ∧ ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → φ z = 0) := by
    intro j
    by_cases hj : j = i
    · exact ⟨fun _ => 1, analyticAt_const, fun h' => absurd hj h'⟩
    · obtain ⟨φ, h1, h2, h3⟩ := exists_equation_not_vanishing (hYan j) (hno i j (Ne.symm hj))
      exact ⟨φ, h1, fun _ => ⟨h2, h3⟩⟩
  choose φ hφan hφ using hsep
  have hΦan : AnalyticAt ℂ (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) w :=
    by simpa only [Finset.prod_fn] using Finset.analyticAt_prod (Finset.univ.erase i) fun j _ => hφan j
  have hΦne : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → ∏ j ∈ Finset.univ.erase i, φ j z = 0 :=
    not_eventually_prod_eq_zero (hYirr i) φ _ (fun j _ => hφan j)
      (fun j hj => (hφ j (Finset.ne_of_mem_erase hj)).2)
  have hΦY : ∀ᶠ z in 𝓝 w, ∀ j, j ≠ i → z ∈ Y j → ∏ j ∈ Finset.univ.erase i, φ j z = 0 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun z h' => absurd hj h'
    · filter_upwards [(hφ j hj).1] with z hz _ hzj
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (hz hzj)
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  have hcont : ∀ᶠ z in 𝓝 w, ContinuousAt (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) z :=
    hΦan.eventually_analyticAt.mono fun z hz => hz.continuousAt
  have hAball : ∀ᶠ z in 𝓝 w, A z ∈ Metric.ball (A w) ε :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  have hgood := hcont.and (hΦY.and (hv.and (hAball.and (show ∀ᶠ z in 𝓝 w, z ∈ W from hW))))
  have hfreq := Filter.not_eventually.mp hΦne
  obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually hgood.eventually_nhds).exists
  push_neg at hx1
  obtain ⟨hxY, hxΦ⟩ := hx1
  obtain ⟨hxc, -, -, hxA, hxW⟩ := hx2.self_of_nhds
  have hxS : x ∈ S := by
    have hx' : x ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.mpr ⟨i, hxY⟩, hxW⟩
    rw [← hS] at hx'
    exact hx'.1
  have hV := hx2.and (hxc.eventually_ne hxΦ)
  have himg := hopen x hxS _ hV
  have hzero : ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    filter_upwards [himg] with y hy
    obtain ⟨z, ⟨hzS, ⟨⟨-, hzY, hzh, -, hzW⟩, hzΦ⟩⟩, rfl⟩ := hy
    have hz' : z ∈ (⋃ j, Y j) ∩ W := by rw [← hS]; exact ⟨hzS, hzW⟩
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz'.1
    by_cases hji : j = i
    · rw [hji] at hzj
      exact hzh hzj
    · exact absurd (hzY j hji hzj) hzΦ
  have hEq := hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hxA hzero
  filter_upwards [Metric.ball_mem_nhds (A w) hε] with y hy
  exact hEq hy

theorem openProjectionDominantComponents_of_analyticGermComponents :
    AnalyticGermComponents.Statement → OpenProjectionDominantComponents.Statement := by
  intro hAGC
  unfold AnalyticGermComponents.Statement at hAGC
  unfold OpenProjectionDominantComponents.Statement
  intro σ _ X B k f d A hB hf hXB hopen w hw
  have hAN : IsAnalyticNear (X ∩ B) w := by
    unfold IsAnalyticNear
    exact ⟨B, k, f, hB, hw.2, hf, by rw [Set.inter_assoc, Set.inter_self, hXB]⟩
  obtain ⟨n₀, Y₀, hY₀, W, hW, hXW⟩ := hAGC σ (X ∩ B) w hAN hw
  obtain ⟨T, hT, hTno⟩ := exists_subfamily_no_containment Y₀ w
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hno : ∀ i j : Fin T.card, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y₀ (e i) → z ∈ Y₀ (e j) := by
    intro i j hij
    exact hTno _ (e i).2 _ (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  have hW' : W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i} ∈ 𝓝 w := Filter.inter_mem hW hT
  have hS : X ∩ B ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) =
      (⋃ i, Y₀ (e i)) ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) := by
    ext z
    constructor
    · rintro ⟨hzXB, hzW, hzT⟩
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := by rw [← hXW]; exact ⟨hzXB, hzW⟩
      obtain ⟨i, hiT, hzi⟩ := hzT.mp h1.1
      refine ⟨Set.mem_iUnion.mpr ⟨e.symm ⟨i, hiT⟩, ?_⟩, hzW, hzT⟩
      simpa using hzi
    · rintro ⟨hzU, hzW, hzT⟩
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzU
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := ⟨Set.mem_iUnion.mpr ⟨_, hzi⟩, hzW⟩
      rw [← hXW] at h1
      exact ⟨h1.1, hzW, hzT⟩
  refine ⟨T.card, fun i => Y₀ (e i), fun i => ⟨(hY₀ _).1, (hY₀ _).2, fun h hh hv => ?_⟩, hno,
    _, hW', hS⟩
  exact dominant_of_open A (fun j => Y₀ (e j)) hopen (fun j => (hY₀ _).1) (fun j => (hY₀ _).2)
    hno hW' hS i h hh hv

end GlobalTheory.CompanionTheory.ComplexSets
end

section

open Formalism.REAL

theorem _root_.GlobalTheory.T.multiset_conjugate_neg_of_prod : ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n → (∀ u : ℂ, (m.map (u + ·)).prod = (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | exact GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | (intros; apply GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq <;> assumption)
end

section

open Topology Filter

theorem _root_.GlobalTheory.T.automorphic_functional_holomorphic_derivative : ∀ {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ), (∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f') → (∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M) → ∀ (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) → DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧ ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv | exact GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv | (intros; apply GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv <;> assumption)
end

section

open MeasureTheory
open scoped Matrix

theorem _root_.GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ → (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) → ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ) → (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) → ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧ ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧ Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧ ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | exact GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | (intros; apply GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.iteratedDeriv_integral_gaussian_exponential : ∀ (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ), Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral | exact GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral | (intros; apply GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral <;> assumption)
end

section

open scoped Matrix SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_fourier_transform_matrix : ∀ (m n : ℕ) (C s : ℂ), s ≠ 0 → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * φ v := by
  first | exact @GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform | exact GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform | (intros; apply GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.commuting_hermitian_simultaneous_diag : ∀ {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)), (∀ A ∈ S, Aᴴ = A) → (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | exact GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | (intros; apply GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag <;> assumption)
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.commutant_annihilating_vector_zero : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (v : Fin m → ℂ), IsUnit g.det → Function.Injective d → (∀ i, (g⁻¹ *ᵥ v) i ≠ 0) → ∀ A : Matrix (Fin m) (Fin m) ℂ, A * (g * diagonal d * g⁻¹) = (g * diagonal d * g⁻¹) * A → A *ᵥ v = 0 → A = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | exact GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero <;> assumption)
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.trace_diagonal_block_conjugate_formula : ∀ (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnit g.det → X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) → (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) → ∀ Y : Matrix (Fin n) (Fin n) ℂ, trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g)) = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | exact GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate <;> assumption)
end
