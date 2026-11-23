module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

namespace ReciprocityTheory.AnForm.M

open FinHolAtlas Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isClosed_of_isAnalyticSubset' (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  unfold FinHolAtlas.IsAnalyticSubset at hS
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have hxSW : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hcon⟩
    exact hxSW.1
  obtain ⟨i, hi⟩ := hne
  have hca : ContinuousAt (f i) x := by
    obtain ⟨j, hxj⟩ := A.cover x
    have h : ∀ k, AnalyticOnNhd ℂ ((f i) ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf i
    have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hxj, ?_⟩
      show (A.chart j).symm ((A.chart j) x) ∈ W
      rw [(A.chart j).left_inv hxj]
      exact hxW
    have h1 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
      ((h j _ hmem).continuousAt).comp ((A.chart j).continuousAt hxj)
    refine h1.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hxj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hW.mem_nhds hxW, hca.eventually_ne hi] with y hyW hyi hyS
  have hy : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hy
  exact hyi (hy.2 i)

theorem exists_localHomeomorph_of_isDegreeOff {A : FinHolAtlas e X} {B : FinHolAtlas e Y}
    {h : Y → X} (hh : HoloMap B A h) {d : ℕ} {S : Set X} (hd : IsDegreeOff A B h d S) (y : Y)
    (hy : h y ∉ S) :
    ∃ E : OpenPartialHomeomorph Y X, y ∈ E.source ∧ Set.EqOn h E E.source ∧
      ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := by
  obtain ⟨j, hyj⟩ := B.cover y
  obtain ⟨k, hk⟩ := A.cover (h y)
  have hb : (B.chart j) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) := by
    refine ⟨(B.chart j).map_source hyj, ?_⟩
    show h ((B.chart j).symm ((B.chart j) y)) ∈ (A.chart k).source
    rw [(B.chart j).left_inv hyj]
    exact hk
  have han := hh.2 j k ((B.chart j) y) hb
  have hdet := hd.2.2.2.2.2 j k ((B.chart j) y) ((B.chart j).map_source hyj)
    (by rw [(B.chart j).left_inv hyj]; exact hy) (by rw [(B.chart j).left_inv hyj]; exact hk)
  set L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv with hL
  have hstrict : HasStrictFDerivAt ((A.chart k) ∘ h ∘ (B.chart j).symm)
      (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) ((B.chart j) y) :=
    han.hasStrictFDerivAt.congr_fderiv (by ext v; rfl)
  set Φ := hstrict.toOpenPartialHomeomorph ((A.chart k) ∘ h ∘ (B.chart j).symm) with hΦ
  have hcoe : (Φ : (Fin e → ℂ) → (Fin e → ℂ)) = (A.chart k) ∘ h ∘ (B.chart j).symm :=
    hstrict.toOpenPartialHomeomorph_coe
  have hsrc : (B.chart j) y ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hU : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  refine ⟨(((B.chart j).trans Φ).trans (A.chart k).symm).restrOpen _ hU, ?_, ?_, j, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨⟨hyj, hsrc⟩, ?_⟩, hk⟩
    show Φ ((B.chart j) y) ∈ (A.chart k).target
    rw [hcoe]
    show (A.chart k) (h ((B.chart j).symm ((B.chart j) y))) ∈ (A.chart k).target
    rw [(B.chart j).left_inv hyj]
    exact (A.chart k).map_source hk
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    obtain ⟨⟨⟨hy1, -⟩, -⟩, hy4⟩ := hy'
    show h y' = (A.chart k).symm (Φ ((B.chart j) y'))
    rw [hcoe]
    show h y' = (A.chart k).symm ((A.chart k) (h ((B.chart j).symm ((B.chart j) y'))))
    rw [(B.chart j).left_inv hy1, (A.chart k).left_inv hy4]
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    exact hy'.1.1.1

end

end ReciprocityTheory.AnForm.M
end

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem pa_holoSmooth {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ))
    (hF : AnalyticOnNhd ℂ F U) : ContDiffOn ℝ ∞ F U :=
  fun x hx => ((hF x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

def pa_aff {e : ℕ} (a : ℂ) (ha : a ≠ 0) (b : Fin e → ℂ) : (Fin e → ℂ) ≃ₜ (Fin e → ℂ) where
  toFun y := a • (y - b)
  invFun z := a⁻¹ • z + b
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ ha]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem pa_aff_analytic {e : ℕ} (a : ℂ) (b : Fin e → ℂ) (y : Fin e → ℂ) :
    AnalyticAt ℂ (fun y : Fin e → ℂ => a • (y - b)) y :=
  by fun_prop

theorem pa_compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (s : Set X)
    (hs : IsOpen s) : IsCompatChart A (ψ.restrOpen s hs) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1, hx2.1⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.1, hx2⟩

theorem pa_compat_aff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (a : ℂ) (ha : a ≠ 0)
    (b : Fin e → ℂ) : IsCompatChart A (ψ.transHomeomorph (pa_aff a ha b)) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨fun z hz => (pa_aff_analytic a b _).comp (h1 z hz), fun z hz => ?_⟩
  have hinv : AnalyticAt ℂ (fun z : Fin e → ℂ => a⁻¹ • z + b) z :=
    by fun_prop
  exact AnalyticAt.comp (f := fun w : Fin e → ℂ => a⁻¹ • w + b) (h2 (a⁻¹ • z + b) hz) hinv

theorem existsPartition : ExistsPartitionStatement := by
  intro e X _ _ _ A
  obtain ⟨χ, h0, h1, h2, h3⟩ := ReciprocityTheory.AnForm.exists_chart_partition A.chart A.cover
    (fun i j => pa_holoSmooth _ _ (A.holo i j))
  exact ⟨⟨χ, fun j k => (h3 j k).mono Set.inter_subset_left, h0, h2, h1⟩⟩

def AtlasOfCompatStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (ψ : Fin m → OpenPartialHomeomorph X (Fin e → ℂ)), (∀ i, IsCompatChart A (ψ i)) →
    (∀ x, ∃ i, x ∈ (ψ i).source) →
    ∃ B : FinHolAtlas e X, A.Compatible B ∧ (∀ i, ∃ j, B.chart j = ψ i) ∧ ∀ j, ∃ i, B.chart j = ψ i

theorem atlasOfCompat : AtlasOfCompatStatement := by
  intro e X _ A m ψ hψ hcov
  refine ⟨⟨m, ψ, hcov, ?_⟩, ⟨fun j k => (hψ k j).1, fun j k => (hψ j k).2⟩, fun i => ⟨i, rfl⟩,
    fun j => ⟨j, rfl⟩⟩
  intro j k z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨l, hx⟩ := A.cover ((ψ j).symm z)
  have hev : ∀ᶠ w in nhds z, (ψ j).symm w ∈ (A.chart l).source :=
    ((ψ j).continuousAt_symm hz1).preimage_mem_nhds ((A.chart l).open_source.mem_nhds hx)
  have ha1 := (hψ k l).1 (A.chart l ((ψ j).symm z))
    ⟨(A.chart l).map_source hx, by rw [Set.mem_preimage, (A.chart l).left_inv hx]; exact hz2⟩
  have ha2 := (hψ j l).2 z ⟨hz1, hx⟩
  exact (AnalyticAt.comp (f := ⇑(A.chart l) ∘ ⇑(ψ j).symm) ha1 ha2).congr (hev.mono fun w hw => by
    simp only [Function.comp, (A.chart l).left_inv hw])

end

end ReciprocityTheory.AnForm.M
end
