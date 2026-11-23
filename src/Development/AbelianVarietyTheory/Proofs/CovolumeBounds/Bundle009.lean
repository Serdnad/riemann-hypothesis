module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle004
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pi
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Matrix.Order

@[expose] public section

section

open Filter Topology

namespace GlobalTheory

section Def

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

noncomputable def pderivList (l : List ι) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  lineDerivList 𝕜 (l.map fun k => Pi.single k (1 : 𝕜)) F

noncomputable def pderivIter (α : ι →₀ ℕ) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  pderivList α.toMultiset.toList F

noncomputable def polyDeriv (P : MvPolynomial ι 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) : V :=
  ∑ α ∈ P.support, P.coeff α • pderivIter α F a

theorem pderivList_append (l₁ l₂ : List ι) (F : (ι → 𝕜) → V) :
    pderivList (l₁ ++ l₂) F = pderivList l₁ (pderivList l₂ F) := by
  simp only [pderivList, List.map_append, lineDerivList_append]

@[simp] theorem pderivIter_zero (F : (ι → 𝕜) → V) : pderivIter 0 F = F := by
  simp [pderivIter, pderivList, lineDerivList]

theorem update_eq_add_smul_single (z : ι → 𝕜) (k : ι) (t : 𝕜) :
    Function.update z k t = z + (t - z k) • (Pi.single k 1 : ι → 𝕜) := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem pderivList_replicate (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivList (List.replicate n k) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  have h := lineDerivList_replicate n (Pi.single k (1 : 𝕜) : ι → 𝕜) F z (0 : 𝕜)
  rw [zero_smul, add_zero] at h
  rw [pderivList, List.map_replicate, h]
  simp only [update_eq_add_smul_single]
  rw [iteratedDeriv_comp_sub_const (f := fun s : 𝕜 => F (z + s • (Pi.single k 1 : ι → 𝕜)))]
  simp

theorem pderivIter_single (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivIter (Finsupp.single k n) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  rw [← pderivList_replicate, pderivIter, Finsupp.toMultiset_single]
  congr 1
  rw [← List.perm_replicate, ← Multiset.coe_eq_coe, Multiset.coe_toList,
    Multiset.nsmul_singleton, Multiset.coe_replicate]

theorem polyDeriv_eq_sum_of_subset (P : MvPolynomial ι 𝕜) {s : Finset (ι →₀ ℕ)}
    (hs : P.support ⊆ s) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv P F a = ∑ α ∈ s, P.coeff α • pderivIter α F a := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.1 hα, zero_smul]

@[simp] theorem polyDeriv_monomial (α : ι →₀ ℕ) (c : 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (MvPolynomial.monomial α c) F a = c • pderivIter α F a := by
  rw [polyDeriv_eq_sum_of_subset _ (s := {α}) MvPolynomial.support_monomial_subset]
  simp

@[simp] theorem polyDeriv_C (c : 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (MvPolynomial.C c) F a = c • F a := by
  rw [← MvPolynomial.monomial_zero', polyDeriv_monomial, pderivIter_zero]

@[simp] theorem polyDeriv_one (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (1 : MvPolynomial ι 𝕜) F a = F a := by
  rw [← MvPolynomial.C_1, polyDeriv_C, one_smul]

end Def

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable [CompleteSpace V]

theorem analyticAt_pderivIter {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α : ι →₀ ℕ) : AnalyticAt 𝕜 (pderivIter α F) a :=
  analyticAt_lineDerivList h _

theorem pderivList_perm {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List ι}
    (hl : l₁.Perm l₂) : pderivList l₁ F a = pderivList l₂ F a :=
  lineDerivList_perm h (hl.map _)

theorem pderivIter_add_index {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α β : ι →₀ ℕ) : pderivIter (α + β) F a = pderivIter α (pderivIter β F) a := by
  rw [pderivIter, pderivIter, pderivIter, ← pderivList_append]
  refine pderivList_perm h ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [Multiset.coe_toList, map_add (f := _)]

end Analytic

section Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]

theorem hasDerivAt_eval_line (Q : MvPolynomial ι 𝕜) (z : ι → 𝕜) (k : ι) :
    HasDerivAt (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) Q)
      (MvPolynomial.eval z (MvPolynomial.pderiv k Q)) 0 := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (0 : 𝕜) c
  | add P Q hP hQ => simpa using hP.fun_add hQ
  | mul_X P j hP =>
    have hj : HasDerivAt (fun t : 𝕜 => z j + t * (Pi.single k 1 : ι → 𝕜) j)
        ((Pi.single k 1 : ι → 𝕜) j) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const ((Pi.single k 1 : ι → 𝕜) j)).const_add (z j)
    have := hP.fun_mul hj
    have e : (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜))
        (P * MvPolynomial.X j)) = fun t : 𝕜 =>
          MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) P
            * (z j + t * (Pi.single k 1 : ι → 𝕜) j) := by
      funext t; simp
    rw [e]
    refine this.congr_deriv ?_
    by_cases h : j = k
    · subst h; simp [add_comm, mul_comm]
    · simp [h, mul_comm]

end Polynomial

section Cauchy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

private theorem cauchy_estimate_iterated_pderiv {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ} (α : ι →₀ ℕ)
    (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) (s : Finset ι) :
    ∀ z : ι → ℂ, (∀ k ∈ s, z k = a k) → (∀ k ∉ s, ‖z k - a k‖ = r k) →
      ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F z‖
        ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
  induction s using Finset.induction_on with
  | empty => intro z _ hz; simpa using hM z fun k => hz k (by simp)
  | insert j s hj ih =>
    intro z hz hz'
    have hzj : z j = a j := hz j (Finset.mem_insert_self _ _)
    have hup : ∀ t : ℂ, ‖t - a j‖ ≤ r j → AnalyticAt ℂ F (Function.update z j t) := by
      intro t ht
      refine hF _ fun k => ?_
      by_cases hk : k = j
      · subst hk; simpa using ht
      · rw [Function.update_of_ne hk]
        by_cases hks : k ∈ s
        · simpa [hz k (Finset.mem_insert_of_mem hks)] using hr k
        · exact (hz' k (by simp [hk, hks])).le
    have hb : ∀ t : ℂ, ‖t - a j‖ = r j →
        ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F (Function.update z j t)‖
          ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
      intro t ht
      refine ih _ (fun k hk => ?_) (fun k hk => ?_)
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
        exact hz k (Finset.mem_insert_of_mem hk)
      · by_cases hkj : k = j
        · subst hkj; simpa using ht
        · rw [Function.update_of_ne hkj]
          exact hz' k (by simp [hkj, hk])
    have hza : AnalyticAt ℂ F z := by
      have := hup (z j) (by simpa [hzj] using hr j)
      rwa [Function.update_eq_self] at this
    rw [Finset.sum_insert hj, pderivIter_add_index hza, pderivIter_single, Finset.prod_insert hj,
      Finset.prod_insert hj, hzj]
    rcases (hr j).eq_or_lt with h0 | hpos
    · have hαj : α j = 0 := by
        by_contra hne
        exact (hα j hne).ne h0
      simpa [hαj] using hb (a j) (by simpa using h0)
    · have hd : DiffContOnCl ℂ (fun t => pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F
          (Function.update z j t)) (Metric.ball (a j) (r j)) := by
        refine DifferentiableOn.diffContOnCl fun t ht => ?_
        rw [closure_ball _ hpos.ne', mem_closedBall_iff_norm] at ht
        exact ((analyticAt_pderivIter (hup t ht) _).differentiableAt.comp t
          (hasDerivAt_update z j t).differentiableAt).differentiableWithinAt
      refine (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (α j) hpos hd
        fun t ht => hb t (mem_sphere_iff_norm.1 ht)).trans_eq ?_
      ring

theorem norm_pderivIter_le_of_analyticAt {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k := by
  have h := cauchy_estimate_iterated_pderiv α hr hα hF hM Finset.univ a (fun _ _ => rfl) (by simp)
  rwa [Finsupp.univ_sum_single] at h

end Cauchy

end GlobalTheory
end

section

open Matrix Set
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory

section

open Filter Metric Function
open scoped Topology

theorem differentiableOn_intervalIntegral_comp_clm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) {h : E → ℂ}
    (hh : DifferentiableOn ℂ h U) {L : ℝ → E →L[ℂ] E} (hL : Continuous L)
    (hLU : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (L s) U U) :
    DifferentiableOn ℂ (fun z => ∫ s in (0 : ℝ)..1, h (L s z)) U := by
  intro z₀ hz₀
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨K, hK, hKU, hc⟩ := local_compact_nhds (hU.mem_nhds hz₀)
  have hA : Continuous fun p : E × ℝ => L p.2 p.1 := (hL.comp continuous_snd).clm_apply continuous_fst
  have hM : MapsTo (fun p : E × ℝ => L p.2 p.1) (U ×ˢ Icc 0 1) U := fun p hp => hLU _ hp.2 hp.1
  have h1 : ContinuousOn (fun p : E × ℝ => h (L p.2 p.1)) (U ×ˢ Icc 0 1) :=
    hh.continuousOn.comp hA.continuousOn hM
  have h2 : ContinuousOn (fun p : E × ℝ => (fderiv ℂ h (L p.2 p.1)).comp (L p.2)) (U ×ˢ Icc 0 1) :=
    ((SCV.differentiableOn_fderiv hU hh).continuousOn.comp hA.continuousOn hM).clm_comp
      (hL.comp continuous_snd).continuousOn
  have hI : Set.uIoc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have h3 : ∀ z ∈ U, ContinuousOn (fun s => h (L s z)) (Icc 0 1) := fun z hz =>
    h1.comp (Continuous.prodMk_right z).continuousOn fun s hs => ⟨hz, hs⟩
  obtain ⟨C, hC⟩ := (hc.prod isCompact_Icc).exists_bound_of_continuousOn
    (h2.mono (prod_mono hKU Subset.rfl))
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (F := fun z s => h (L s z)) (F' := fun z s => (fderiv ℂ h (L s z)).comp (L s))
    (bound := fun _ => C) hK ?_ ?_ ?_ ?_ ?_ ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hU.mem_nhds hz₀] with z hz
    exact ((h3 z hz).mono hI).aestronglyMeasurable measurableSet_uIoc
  · exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one (h3 z₀ hz₀)
  · exact ((h2.comp (Continuous.prodMk_right z₀).continuousOn fun s hs => ⟨hz₀, hs⟩).mono
      hI).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall fun s hs z hz => hC (z, s) ⟨hz, hI hs⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun s hs z hz =>
      (hh.differentiableAt (hU.mem_nhds (hLU s (hI hs) (hKU hz)))).hasFDerivAt.comp z
        (L s).hasFDerivAt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ}


omit [Fintype ι] in
theorem update_mem_polydisc {z : ι → ℂ} (hz : z ∈ univ.pi fun j => ball (0 : ℂ) (r j)) {i : ι}
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) (r i)) : update z i t ∈ univ.pi fun j => ball (0 : ℂ) (r j) := by
  intro j _
  rcases eq_or_ne j i with rfl | hj
  · simpa using ht
  · simpa [hj] using hz j trivial

theorem exists_eq_coord_mul_of_vanishing {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (univ.pi fun j => ball 0 (r j))) (i : ι)
    (h0 : ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f (update z i 0) = 0) :
    ∃ g : (ι → ℂ) → ℂ, DifferentiableOn ℂ g (univ.pi fun j => ball 0 (r j)) ∧
      ∀ z ∈ univ.pi fun j => ball (0 : ℂ) (r j), f z = z i * g z := by
  have hU : IsOpen (univ.pi fun j => ball (0 : ℂ) (r j)) :=
    isOpen_set_pi finite_univ fun _ _ => isOpen_ball
  let e : ι → ℂ := Pi.single i 1
  let L : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ) := fun s =>
    ContinuousLinearMap.id ℂ _ + ((s : ℂ) - 1) • (ContinuousLinearMap.proj i).smulRight e
  have hL : ∀ s z, L s z = z + ((s : ℂ) - 1) • z i • e := fun s z => rfl
  have hL' : ∀ (s : ℝ) z, L s z = update z i (s * z i) := by
    intro s z
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp [hL, e]; ring
    · simp [hL, e, hj]
  have hLU : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (L s) (univ.pi fun j => ball (0 : ℂ) (r j))
      (univ.pi fun j => ball (0 : ℂ) (r j)) := by
    intro s hs z hz
    rw [hL']
    refine update_mem_polydisc hz ?_
    have := hz i trivial
    rw [mem_ball_zero_iff] at this ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans_lt this
  have hLc : Continuous L := by fun_prop
  have hd := SCV.differentiableOn_fderiv_apply hU hf e
  refine ⟨_, differentiableOn_intervalIntegral_comp_clm hU hd hLc hLU, fun z hz => ?_⟩
  have hc : ContinuousOn (fun s => fderiv ℂ f (L s z) e) (Icc 0 1) :=
    hd.continuousOn.comp (hLc.clm_apply continuous_const).continuousOn fun s hs => hLU s hs hz
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => f (L s z))]
  · simp [hL', h0 z hz]
  · intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun t : ℂ => z + (t - 1) • z i • e) (z i • e) s := by
      simpa using (((hasDerivAt_id (s : ℂ)).sub_const 1).smul_const (z i • e)).const_add z
    have h2 : HasFDerivAt f (fderiv ℂ f (L s z)) (z + ((s : ℂ) - 1) • z i • e) :=
      (hf.differentiableAt (hU.mem_nhds (hLU s hs hz))).hasFDerivAt
    have h3 := (h2.comp_hasDerivAt (s : ℂ) h1).comp_ofReal
    rw [map_smul, smul_eq_mul] at h3
    exact h3
  · exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one (continuousOn_const.mul hc)

end

end GlobalTheory
end

section

open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise

namespace GlobalTheory

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨circleMap 0 1 θ • (x : E), by simp [norm_smul]⟩

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem coe_sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) :
    (sphereRotation θ x : E) = circleMap 0 1 θ • (x : E) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_sphereRotation :
    Continuous (Function.uncurry (sphereRotation (E := E))) := by
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ Function.uncurry (sphereRotation (E := E))) =
      fun q : ℝ × sphere (0 : E) 1 => circleMap 0 1 q.1 • (q.2 : E) := by
    funext q
    exact coe_sphereRotation q.1 q.2
  rw [e]
  exact ((continuous_circleMap 0 1).comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem measurePreserving_sphereRotation [FiniteDimensional ℂ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (θ : ℝ) :
    MeasurePreserving (sphereRotation θ) μ.toSphere μ.toSphere := by
  set ζ : ℂ := circleMap 0 1 θ with hζ_def
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_circleMap_zero]
  have hζ0 : ζ ≠ 0 := by
    rw [← norm_ne_zero_iff, hζ]; exact one_ne_zero
  have hm : Measurable (sphereRotation (E := E) θ) :=
    (continuous_sphereRotation.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' μ (hm hs), Measure.toSphere_apply' μ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereRotation θ ⁻¹' s) : Set E) =
      (fun v : E => ζ • v) ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext v
    constructor
    · rintro ⟨t, ht, _, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereRotation θ w, hw, rfl⟩, ?_⟩
      show t • ((sphereRotation θ w : sphere (0 : E) 1) : E) = ζ • (t • (w : E))
      rw [coe_sphereRotation]
      exact smul_comm t ζ (w : E)
    · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, huv⟩
      have hwmem : ζ⁻¹ • (u : E) ∈ sphere (0 : E) 1 := by
        simp [norm_smul, hζ]
      set w : sphere (0 : E) 1 := ⟨ζ⁻¹ • (u : E), hwmem⟩ with hw_def
      have hw : sphereRotation θ w = u := by
        apply Subtype.ext
        rw [coe_sphereRotation]
        show ζ • ζ⁻¹ • (u : E) = u
        rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul]
      refine ⟨t, ht, _, ⟨w, ?_, rfl⟩, ?_⟩
      · show sphereRotation θ w ∈ s
        rw [hw]; exact hu
      · have huv' : t • (u : E) = ζ • v := huv
        show t • (ζ⁻¹ • (u : E)) = v
        rw [smul_comm t ζ⁻¹, huv', smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  rw [hset]
  exact (measurePreserving_smul_of_norm_eq_one μ hζ).measure_preimage_emb
    (MeasurableEquiv.smul₀ ζ hζ0).measurableEmbedding _

end Rotation

section Torus

variable {ι : Type*} [Fintype ι]

end Torus

section Concavity

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

end Concavity

end GlobalTheory
end
