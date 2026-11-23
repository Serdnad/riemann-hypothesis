module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder

noncomputable section

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem potential_contDiffAt (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    ContDiffAt ℝ 2 (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
  have h := hP.1 ((A.chart j).symm y) j
  have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U ((A.chart j).symm y) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)).mem_nhds ⟨hy, P.mem_U _⟩
  exact (h.contDiffAt hmem).of_le (by norm_cast)

theorem locDens_cons (A : FinHolAtlas (e + 1) X) (P : LocPot X) (Φ : Fin e → LocPot X)
    (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) j y = ((e + 1).factorial : ℝ) * (2 / Real.pi) ^ (e + 1) *
      (mdisc (Fin.cons (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)
        (fun i => hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) :
          Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)).re := by
  unfold locDens maDens
  congr 3
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

theorem locDens_cons_rsmul (A : FinHolAtlas (e + 1) X) (c : ℝ) (P : LocPot X)
    (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons (P.rsmul c) Φ) j y = c * locDens A (Fin.cons P Φ) j y := by
  rw [locDens_cons, locDens_cons]
  have : (fun y' => (P.rsmul c).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => c * P.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_const_mul', mdisc_cons_smul, Complex.re_ofReal_mul]
  ring

theorem locDens_cons_add (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A (Fin.cons (P + Q) Φ) j y =
      locDens A (Fin.cons P Φ) j y + locDens A (Fin.cons Q Φ) j y := by
  rw [locDens_cons, locDens_cons, locDens_cons]
  have : (fun y' => (P + Q).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y') +
        Q.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_add' _ _ _ (potential_contDiffAt A P hP j hy) (potential_contDiffAt A Q hQ j hy),
    mdisc_cons_add, Complex.add_re]
  ring

theorem locDens_nonneg (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hψ : ∀ i, IsPsh A (Φ i)) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : 0 ≤ locDens A Φ j y := by
  unfold locDens
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  exact hessC_posSemidef _ _ (potential_contDiffAt A (Φ k) (hΦ k) j hy)
    fun w => hψ k ((A.chart j).symm y) j y ⟨hy, (Φ k).mem_U _⟩ w

theorem integrableOn_weight [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by
  set K := (A.chart j) '' tsupport (P.χ j)
  have hKc : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    ((A.chart j).continuousOn.mono (P.tsupport_subset j))
  have hKt : K ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart j).map_source (P.tsupport_subset j hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K :=
    (hg j K hKt hKc).continuousOn_mul (hχc.mono hKt) hKc
  have h2 := h1.of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet (by
    rintro y ⟨hy, hyK⟩
    have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h =>
      hyK ⟨_, h, (A.chart j).right_inv hy⟩
    simp [image_eq_zero_of_notMem_tsupport this])
  simpa only [mul_assoc] using h2

end Chart

private theorem mdisc_comp_perm_potential {D : ℕ} (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    ReciprocityTheory.AnForm.mdisc (B ∘ σ) = ReciprocityTheory.AnForm.mdisc B := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_
  simp [Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]

theorem mIntSymm : MIntSymmStatement := by
  intro e X _ A Φ σ g
  have hloc : ∀ j y, locDens A (Φ ∘ σ) j y = locDens A Φ j y := by
    intro j y
    unfold locDens maDens
    congr 2
    exact mdisc_comp_perm_potential (fun k => ReciprocityTheory.AnForm.hessC
      (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) σ
  unfold mInt integralWith
  simp only [hloc]

theorem mIntAdd : MIntAddStatement := by
  intro e X _ _ _ A P Q Φ hP hQ hΦ g hgP hgQ
  unfold mInt integralWith
  split_ifs with h
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some (Fin.cons P Φ) g hgP j
    have i2 := integrableOn_weight A h.some (Fin.cons Q Φ) g hgQ j
    rw [← integral_add i1 i2]
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    show _ = _ + _
    rw [locDens_cons_add A P Q Φ hP hQ j hy]
    ring
  · simp

theorem mIntRsmul : MIntRsmulStatement := by
  intro e X _ A c P Φ hP hΦ g
  unfold mInt integralWith
  split_ifs with h
  · simp only [locDens_cons_rsmul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · simp

theorem mIntZsmul : MIntZsmulStatement := by
  intro e X _ A m P Φ hP hΦ g
  exact mIntRsmul A (m : ℝ) P Φ hP hΦ g

theorem mIntLinear : MIntLinearStatement := by
  intro e X _ _ _ A Φ hΦ c g g' hg hg'
  unfold mInt integralWith
  split_ifs with h
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some Φ g hg j
    have i2 := integrableOn_weight A h.some Φ g' hg' j
    rw [← integral_const_mul, ← integral_add (i1.const_mul c) i2]
    congr 1
    funext y
    ring
  · simp

theorem mIntNonneg : MIntNonnegStatement := by
  intro e X _ A Φ hΦ hψ g hg
  unfold mInt integralWith
  split_ifs with h
  · exact Finset.sum_nonneg fun j _ => setIntegral_nonneg (A.chart j).open_target.measurableSet
      fun y hy => mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg _)) (locDens_nonneg A Φ hΦ hψ j hy)
  · exact le_rfl

end

end ReciprocityTheory.AnForm.M
end

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

theorem maDens_congr_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) y = fderiv ℝ (fderiv ℝ (ψ i)) y := (h i).fderiv.fderiv_eq
    unfold hessC
    simp only [h2]
    rfl
  simp only [maDens, hH]

theorem holoMap_preimage_mem_nhds {e e' : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) ∈ 𝓝 y := by
  have hs : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  exact ((B.chart j).isOpen_inter_preimage_symm hs).mem_nhds ⟨hy, hk⟩

theorem potential_contDiffAt_chart {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hS : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) :=
    (A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)
  refine ((hP.1 x k).contDiffAt (hS.mem_nhds ⟨hz, hzU⟩)).of_le ?_
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

theorem pullback_local_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h)
    (P : LocPot X) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (fun y' => P.φ (h ((B.chart j).symm y)) (h ((B.chart j).symm y'))) =ᶠ[𝓝 y]
      (P.φ (h ((B.chart j).symm y)) ∘ (A.chart k).symm) ∘
        (A.chart k ∘ h ∘ (B.chart j).symm) := by
  filter_upwards [holoMap_preimage_mem_nhds hh j k hy hk] with y' hy'
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv hy'.2]

theorem locDensPullback : LocDensPullbackStatement := by
  intro e X Y _ _ A B h hh Φ hΦ j k y hy hk
  set x0 := h ((B.chart j).symm y) with hx0
  set τ := A.chart k ∘ h ∘ (B.chart j).symm with hτ
  have hτa : AnalyticAt ℂ τ y := hh.2 j k y ⟨hy, hk⟩
  have hτy : τ y = A.chart k x0 := rfl
  have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
  have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm) (τ y) := by
    intro i
    rw [hτy]
    exact potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
      (by rw [hsymm]; exact (Φ i).mem_U x0)
  unfold locDens
  refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
  rw [hsymm]
  refine (ReciprocityTheory.AnForm.A.maDens_comp (fun i => (Φ i).φ x0 ∘ (A.chart k).symm) τ y hτa hφ).trans ?_
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hτy]
  rfl

theorem rankDrop : RankDropStatement := by
  intro e e' X Y _ _ A B h hh hrk Φ hΦ g
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_eq_zero fun j _ => ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
    set x0 := h ((B.chart j).symm y) with hx0
    have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
    have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm)
        ((A.chart k ∘ h ∘ (B.chart j).symm) y) := fun i =>
      potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
        (by simp only [Function.comp_apply]; rw [hsymm]; exact (Φ i).mem_U x0)
    have h0 : locDens B (fun i => (Φ i).pullback h hh.1) j y = 0 := by
      unfold locDens
      refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
      exact maDens_comp_eq_zero_of_rank_lt _ _ y (hh.2 j k y ⟨hy, hk⟩) hφ (hrk j k y hy hk)
    rw [h0, mul_zero]
  · rfl

end

end ReciprocityTheory.AnForm.M
end
