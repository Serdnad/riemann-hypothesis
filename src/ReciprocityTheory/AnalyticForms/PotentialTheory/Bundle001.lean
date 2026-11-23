module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem st_trans_smooth (A : FinHolAtlas e X) (j k : Fin A.n) :
    ContDiffOn ℝ ∞ (A.chart k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) := by
  exact fun y hy => (((A.holo j k y hy).contDiffAt (n := ∞)).restrict_scalars ℝ).contDiffWithinAt

theorem st_exists_good_partition [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) {r : ℕ}
    (Φ : Fin r → LocPot X) :
    ∃ (M : ℕ) (θ : Fin M → X → ℝ) (G : Fin M → Set X) (j : Fin M → Fin A.n)
      (x0 : Fin M → Fin r → X),
      (∀ m, A.Smooth (θ m)) ∧ (∀ m x, 0 ≤ θ m x) ∧ (∀ x, ∑ m, θ m x = 1) ∧
      (∀ m, tsupport (θ m) ⊆ G m) ∧ (∀ m, IsOpen (G m)) ∧
      (∀ m, G m ⊆ (A.chart (j m)).source) ∧ (∀ m i, G m ⊆ (Φ i).U (x0 m i)) := by
  classical
  choose jx hjx using A.cover
  let G : X → Set X := fun x => (A.chart (jx x)).source ∩ ⋂ i, (Φ i).U x
  have hGo : ∀ x, IsOpen (G x) := fun x =>
    (A.chart (jx x)).open_source.inter (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U x)
  have hGx : ∀ x, x ∈ G x := fun x => ⟨hjx x, Set.mem_iInter.mpr fun i => (Φ i).mem_U x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover G hGo
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hGx x⟩)
  let pt : Fin t.card → X := fun m => (t.equivFin.symm m : X)
  let ch : Fin t.card → OpenPartialHomeomorph X (Fin e → ℂ) := fun m =>
    (A.chart (jx (pt m))).restr (G (pt m))
  have hsrc : ∀ m, (ch m).source = G (pt m) := by
    intro m
    simp only [ch, OpenPartialHomeomorph.restr_source, (hGo _).interior_eq]
    exact Set.inter_eq_right.mpr Set.inter_subset_left
  have hcov : ∀ x, ∃ m, x ∈ (ch m).source := by
    intro x
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ∈ G y := by simpa using ht (Set.mem_univ x)
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    rw [hsrc]
    simpa [pt] using hxy
  have htr : ∀ a b, ContDiffOn ℝ ∞ (ch b ∘ (ch a).symm)
      ((ch a).target ∩ (ch a).symm ⁻¹' (ch b).source) := by
    intro a b
    simp only [ch, OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.restr_symm_apply,
      OpenPartialHomeomorph.restr_target, OpenPartialHomeomorph.restr_source]
    exact (st_trans_smooth A _ _).mono fun y hy => ⟨hy.1.1, hy.2.1⟩
  obtain ⟨χ, hχ0, hχ1, hχs, hχsm⟩ := exists_chart_partition ch hcov htr
  refine ⟨t.card, χ, fun m => G (pt m), fun m => jx (pt m), fun m _ => pt m, ?_, hχ0, hχ1,
    fun m => (hχs m).trans (hsrc m).subset, fun m => hGo _, fun m => Set.inter_subset_left,
    fun m i x hx => Set.mem_iInter.mp hx.2 i⟩
  intro m k y hy
  obtain ⟨n, hn⟩ := hcov ((A.chart k).symm y)
  have hyk : y ∈ (A.chart k).target := hy.1
  have hxs : (A.chart k).symm y ∈ (A.chart (jx (pt n))).source := by
    have hn' := hn
    rw [hsrc] at hn'
    exact hn'.1
  have hx_in : (A.chart (jx (pt n))) ((A.chart k).symm y) ∈ (ch n).target := (ch n).map_source hn
  have hsm := hχsm m n
  simp only [ch, OpenPartialHomeomorph.restr_symm_apply] at hsm
  have hf := hsm.contDiffAt (((A.chart (jx (pt n))).restr (G (pt n))).open_target.mem_nhds hx_in)
  have hW : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart (jx (pt n))).source) :=
    (A.chart k).isOpen_inter_preimage_symm (A.chart (jx (pt n))).open_source
  have hg := (st_trans_smooth A k (jx (pt n))).contDiffAt (hW.mem_nhds ⟨hyk, hxs⟩)
  have hc := hf.comp y hg
  refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW.mem_nhds ⟨hyk, hxs⟩] with z hz
  simp only [Function.comp_apply]
  rw [(A.chart (jx (pt n))).left_inv hz.2]

end

end ReciprocityTheory.AnForm.M
end

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section

variable {e e' : ℕ}

def J1 (e e' : ℕ) : Matrix (Fin e) (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.castAdd e' a then 1 else 0

def J2 (e e' : ℕ) : Matrix (Fin e') (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.natAdd e a then 1 else 0

theorem natAdd_ne_castAdd' (a : Fin e) (b : Fin e') : (Fin.natAdd e b : Fin (e + e')) ≠ Fin.castAdd e' a := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem castAdd_ne_natAdd' (a : Fin e) (b : Fin e') : (Fin.castAdd e' a : Fin (e + e')) ≠ Fin.natAdd e b :=
  fun h => natAdd_ne_castAdd' a b h.symm

theorem block_eq (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    (J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e' =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M1 0 0 M2) := by
  ext k l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
    refine Fin.addCases (fun c => ?_) (fun d => ?_) l <;>
    simp [Matrix.mul_apply, J1, J2, Matrix.fromBlocks, ite_mul, mul_ite, Finset.sum_ite_eq, natAdd_ne_castAdd', castAdd_ne_natAdd']

theorem det_block (M1 : Matrix (Fin e) (Fin e) ℂ) (M2 : Matrix (Fin e') (Fin e') ℂ) :
    ((J1 e e')ᵀ * M1 * J1 e e' + (J2 e e')ᵀ * M2 * J2 e e').det = M1.det * M2.det := by
  rw [block_eq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem pot_contDiffAt {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hmem : (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x ∈ 𝓝 z :=
    ((A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hz, hzU⟩
  exact ((hP.1 x k).contDiffAt hmem).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

end

end ReciprocityTheory.AnForm.M
end

section

namespace ReciprocityTheory.AnForm.M

open OnePoint

noncomputable section

section Alg

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem FinHolAtlas.HoloOn.mul' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x * g x) :=
  fun j => (hf j).mul (hg j)

end Alg

namespace CompatibleChartOperations







end CompatibleChartOperations

end

end ReciprocityTheory.AnForm.M
end
