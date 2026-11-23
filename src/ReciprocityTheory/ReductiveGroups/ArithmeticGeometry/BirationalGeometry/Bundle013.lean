module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.brGood R.toAnRes Ψ

theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J := fun h => hx (Or.inl (Or.inl h))

theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))

theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.brW_mem_fibre R.toAnRes Ψ hK hPh h0

theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.brW_injOn R.toAnRes Ψ

theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.brFib_finite R.toAnRes Ψ hP hΨ y

theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge.exists_of_mem_fibre R.toAnRes Ψ hw hy

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem pushForward_null' [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  rw [mInt, dite_eq_left hne, integralWith]
  generalize hne.some = Pt
  have hnull : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume) ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null
        (show goodT A q j ∩ (A.chart j).symm ⁻¹' S ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' S from
          fun u hu => ⟨hu.1.1, hu.2⟩) (hS j)
  have hfinj : ∀ j, ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)),
      (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [compl_mem_ae_iff.2 (hnull j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u)) ∧
      ∫ u in goodT A q j, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u = ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y := fun j =>
    area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ g hg j).mono_set (fun u hu => hu.1)) (hfinj j)
  have htarget : ∀ j, ∫ u in (A.chart j).target, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u = ∫ u in goodT A q j, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u := by
    intro j
    apply setIntegral_congr_set
    rw [ae_eq_set]
    refine ⟨measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j), ?_⟩
    rw [diff_eq_empty.2 (show goodT A q j ⊆ (A.chart j).target from fun u hu => hu.1)]
    exact measure_empty
  have hj : ∀ j y, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) →
      fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y =
        ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * (g x * pushDens A Φ q x) := by
    intro j y hy
    unfold fibSum
    rw [goodT_fibre_eq A q S hq j hy, finsum_mem_image ((A.chart j).injOn.mono inter_subset_left)]
    calc _ = ∑ᶠ x ∈ (A.chart j).source ∩ (q ⁻¹' {y} \ S), Pt.χ j x * (g x * pushDens A Φ q x) :=
          finsum_mem_congr rfl (fun x hx => fib_term A Φ hΦ q S hq Pt g j hx.1 hx.2.2)
      _ = _ := by
          apply finsum_mem_inter_support_eq
          ext x
          simp only [mem_inter_iff, Function.mem_support]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩
            exact ⟨h2, h3⟩
          · rintro ⟨h2, h3⟩
            exact ⟨⟨Pt.tsupport_subset j (subset_tsupport _ (left_ne_zero_of_mul h3)), h2⟩, h3⟩
  have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)),
      ∀ j, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) := by
    rw [ae_all_iff]
    intro j
    exact compl_mem_ae_iff.2 (hnull j)
  calc ∑ j, ∫ u in (A.chart j).target, Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u
      = ∑ j, ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y :=
        Finset.sum_congr rfl (fun j _ => (htarget j).trans (harea j).2)
    _ = ∫ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y :=
        (MeasureTheory.integral_finsetSum _ (fun j _ => (harea j).1)).symm
    _ = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
        apply integral_congr_ae
        filter_upwards [hae] with y hy
        have hF := hfin y
        calc ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (fun u => Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u) y
            = ∑ j, ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * (g x * pushDens A Φ q x) :=
              Finset.sum_congr rfl (fun j _ => hj j y (hy j))
          _ = ∑ j, ∑ x ∈ hF.toFinset, Pt.χ j x * (g x * pushDens A Φ q x) :=
              Finset.sum_congr rfl (fun j _ => finsum_mem_eq_finite_toFinset_sum _ hF)
          _ = ∑ x ∈ hF.toFinset, g x * pushDens A Φ q x := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun x _ => ?_)
              rw [← Finset.sum_mul, Pt.sum_eq_one, one_mul]
          _ = ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x :=
              (finsum_mem_eq_finite_toFinset_sum _ hF).symm

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial
open scoped Pointwise

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

private theorem isMultiHomog_mul_birational_geometry {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomogIdeal_mul {I I' : Ideal (MRing ι)} (hI : IsMultiHomogIdeal I)
    (hI' : IsMultiHomogIdeal I') : IsMultiHomogIdeal (I * I') := by
  obtain ⟨S, hS, rfl⟩ := hI
  obtain ⟨S', hS', rfl⟩ := hI'
  refine ⟨S * S', ?_, Ideal.span_mul_span' S S'⟩
  rintro f ⟨x, hx, y, hy, rfl⟩
  obtain ⟨a, ha⟩ := hS x hx
  obtain ⟨b, hb⟩ := hS' y hy
  exact ⟨a + b, isMultiHomog_mul_birational_geometry ha hb⟩

private theorem isMultiHomog_finset_prod' {β : Type} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ x ∈ s, IsMultiHomog (f x) (a x)) : IsMultiHomog (∏ x ∈ s, f x) (∑ x ∈ s, a x) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _ m hm k
    rw [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
      exact hm rfl
    subst hm0
    simp
  · intro x s hx ih h
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact isMultiHomog_mul_birational_geometry (h x (Finset.mem_insert_self x s))
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

private theorem isMultiHomog_finset_sum {β : Type} (s : Finset β) (f : β → MRing ι) (a : K → ℕ)
    (h : ∀ x ∈ s, IsMultiHomog (f x) a) : IsMultiHomog (∑ x ∈ s, f x) a := by
  classical
  intro m hm k
  obtain ⟨x, hx, hm'⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact h x hx m hm' k

private theorem isMultiHomog_zsmul (c : ℤ) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    IsMultiHomog (c • f) a := fun m hm k => h m (MvPolynomial.support_smul hm) k

private theorem isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero [DecidableEq K] (v : Σ k, ι k) {p : MRing ι} {d : K → ℕ}
    (h : IsMultiHomog p d) :
    IsMultiHomog (MvPolynomial.pderiv v p) (fun k => d k - if k = v.1 then 1 else 0) ∧
      (MvPolynomial.pderiv v p ≠ 0 → 1 ≤ d v.1) := by
  classical
  have key : ∀ m, m ∈ (MvPolynomial.pderiv v p).support → ∀ k, ∑ i, m ⟨k, i⟩ + (if k = v.1 then 1 else 0) = d k := by
    intro m hm k
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hm' : m + Finsupp.single v 1 ∈ p.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      exact hm (by rw [h0, zero_mul])
    rw [← h _ hm' k]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    congr 1
    obtain ⟨k0, i0⟩ := v
    by_cases hk : k = k0
    · subst hk
      simp [Finsupp.single_apply, Sigma.mk.inj_iff]
    · simp [Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hk, hk]
  refine ⟨fun m hm k => ?_, fun hne => ?_⟩
  · have := key m hm k
    beta_reduce
    omega
  · obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
    have := key m (MvPolynomial.mem_support_iff.mpr hm) v.1
    rw [if_pos rfl] at this
    omega

theorem isMultiHomog_det_pderiv {s c : ℕ} (G : Fin s → MRing ι) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
    (a : Fin c → Fin s) (b : Fin c → Σ k, ι k) :
    ∃ d, IsMultiHomog (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv (b j) (G (a i)))) d := by
  classical
  choose d hd using hG
  refine ⟨fun k => (∑ i, d (a i) k) - ∑ j, (if k = (b j).1 then 1 else 0), ?_⟩
  rw [Matrix.det_apply]
  refine isMultiHomog_finset_sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  refine isMultiHomog_zsmul _ ?_
  simp only [Matrix.of_apply]
  by_cases h0 : ∃ i, MvPolynomial.pderiv (b i) (G (a (σ i))) = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    intro m hm
    simp at hm
  · push_neg at h0
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin c)), ∀ k,
        (if k = (b i).1 then 1 else 0) ≤ d (a (σ i)) k := by
      intro i _ k
      split_ifs with hk
      · subst hk
        exact (isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).2 (h0 i)
      · exact Nat.zero_le _
    have hp := isMultiHomog_finset_prod' Finset.univ (fun i => MvPolynomial.pderiv (b i) (G (a (σ i))))
      (fun i k => d (a (σ i)) k - if k = (b i).1 then 1 else 0)
      (fun i _ => (isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).1)
    convert hp using 1
    funext k
    rw [Finset.sum_apply, Finset.sum_tsub_distrib _ (fun i hi => hle i hi k)]
    congr 1
    exact (Equiv.sum_comp σ (fun i => d (a i) k)).symm

theorem isMultiHomogIdeal_pC {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨map (Int.castRingHom ℂ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · exact Ideal.map_span (map (Int.castRingHom ℂ)) S

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem maDens_congr_fderiv {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, fderiv ℝ (φ i) =ᶠ[𝓝 z] fderiv ℝ (ψ i)) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have h2 : ∀ i, fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
    fun i => (h i).fderiv_eq
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.hessC
  simp only [h2]

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := by
  unfold IsSmoothHerm at *
  exact hA.mul hB

theorem isSectionOn_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn P B 1 := by
  refine ⟨0, fun k => by simp [hB], ?_, ?_⟩
  · intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  · exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

def oneLine : HermLine ι := HermLine.ofWeight (fun _ => 1) (fun _ _ _ => rfl)

theorem logNorm_oneLine (z : (Σ k, ι k) → ℂ) : logNorm (oneLine (ι := ι)) 1 z = 1 := by
  simp [logNorm, oneLine, HermLine.ofWeight, Real.exp_neg]

theorem isSmoothHerm_oneLine : IsSmoothHerm (oneLine (ι := ι)) := by
  simp only [IsSmoothHerm, oneLine, HermLine.ofWeight]
  exact contDiffOn_const

def HermLine.sqMetric (b : K → ℕ) : HermLine ι where
  a k := b k
  h z := ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    refine pow_pos (Real.sqrt_pos.mpr ?_) _
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : ∑ i, ‖c k * z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
      simp [mul_pow, Finset.mul_sum]
    simp only
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), mul_pow, zpow_natCast]

theorem isSmoothHerm_sqMetric (b : K → ℕ) : IsSmoothHerm (HermLine.sqMetric (ι := ι) b) := by
  unfold IsSmoothHerm
  have hs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
    intro k
    apply ContDiff.sum
    intro i _
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))
  show ContDiffOn ℝ _ (fun z : (Σ k, ι k) → ℂ => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k) _
  apply contDiffOn_prod
  intro k _
  apply ContDiffOn.pow
  apply ContDiffOn.sqrt (hs k).contDiffOn
  intro z hz
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ‖z ⟨k, i⟩‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact (lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ i))).ne'

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem germ_of_eqOn (R : AnLogRes P J e) {Q Q' : LocPot R.X}
    (h : ∀ x, ∀ y ∈ R.U x, Q.φ x y = Q'.φ x y) (j : Fin R.A.n) (y : Fin e → ℂ)
    (hy : y ∈ (R.A.chart j).target) :
    (fun y' => Q.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q'.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y') := by
  have hc : ContinuousAt (R.A.chart j).symm y := (R.A.chart j).continuousAt_symm hy
  have hU : R.U ((R.A.chart j).symm y) ∈ 𝓝 ((R.A.chart j).symm y) :=
    (R.isOpen_U _).mem_nhds (R.mem_U _)
  filter_upwards [hc hU] with y' hy'
  exact h _ _ hy'

theorem locDens_congr_of_eqOn (R : AnLogRes P J e) {Φ Φ' : Fin e → LocPot R.X}
    (h : ∀ i x, ∀ y ∈ R.U x, (Φ i).φ x y = (Φ' i).φ x y) :
    ∀ j, ∀ y ∈ (R.A.chart j).target, locDens R.A Φ j y = locDens R.A Φ' j y := by
  intro j y hy
  unfold locDens
  apply maDens_congr_fderiv
  intro i
  exact (germ_of_eqOn R (h i) j y hy).fderiv

theorem potOf_cons {n : ℕ} (R : AnLogRes P J e) (C : HermLine ι) (L : Fin n → HermLine ι) :
    (fun j => potOf R ((Fin.cons C L : Fin (n + 1) → HermLine ι) j)) =
      Fin.cons (potOf R C) (fun j => potOf R (L j)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem ptsIntegral_one_eq_mInt (hE : ResExistsStatement) (hB : ResBridgeStatement) {e : ℕ}
    (R : AnLogRes P J e) {L : Fin e → HermLine ι} (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (pot L) (fun _ => 1) = mInt R.A (fun j => potOf R (L j)) (fun _ => 1) := by
  have h1 : (fun _ : (Σ k, ι k) → ℂ => (1 : ℝ)) = logNorm oneLine 1 :=
    funext fun z => (logNorm_oneLine z).symm
  rw [h1, ptsIntegral_eq_mInt' hE hB R hP hL isSmoothHerm_oneLine (isSectionOn_one hP.2.1.1 rfl)]
  exact mInt_congr _ (fun _ _ _ => rfl) fun x => logNorm_oneLine _

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
