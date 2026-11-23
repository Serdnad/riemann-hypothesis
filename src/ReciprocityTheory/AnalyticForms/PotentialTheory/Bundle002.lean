module

public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001

@[expose] public section

section

namespace ReciprocityTheory.AnForm.M

open Filter Topology
open scoped ContDiff ComplexOrder

noncomputable section

section SlopeTestRemainingChoices

variable {D : ℕ}

theorem hessC_const_mul' (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    hessC (fun w => c * φ w) z = (c : ℂ) • hessC φ z := by
  have h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ := by
    show fderiv ℝ (c • φ) = _
    exact fderiv_const_smul_field c
  have h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ) := by
    rw [h1]; exact fderiv_const_smul_field c
  ext i j
  simp only [hessC, h2, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  push_cast
  ring

theorem hessC_add' (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have e1 : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
    filter_upwards [hφ.eventually (by simp), hψ.eventually (by simp)] with w h1 h2
    exact fderiv_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))
  have d1 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have d2 : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have e2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [e1.fderiv_eq]; exact fderiv_add d1 d2
  ext i j
  simp only [hessC, e2, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

theorem mdisc_cons_add {e : ℕ} (B C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (F : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    mdisc (Fin.cons (B + C) F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      mdisc (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) +
        mdisc (Fin.cons C F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have := ReciprocityTheory.AnForm.A.mdisc_update_add
    (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 B C
  simpa only [Fin.update_cons_zero] using this

theorem mdisc_cons_smul {e : ℕ} (c : ℂ) (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (F : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    mdisc (Fin.cons (c • B) F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      c * mdisc (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have := ReciprocityTheory.AnForm.A.mdisc_update_smul
    (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 c B
  simpa only [Fin.update_cons_zero] using this

theorem hessC_isHermitian' (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  ext i j
  simp only [Matrix.conjTranspose_apply, hessC]
  rw [hs (Pi.single j 1) (Pi.single i 1), hs (Complex.I • Pi.single j 1) (Complex.I • Pi.single i 1),
    hs (Pi.single j 1) (Complex.I • Pi.single i 1), hs (Complex.I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

theorem leviC_add_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a b b' : Fin D → ℂ) :
    leviC H a (b + b') = leviC H a b + leviC H a b' := by
  simp only [leviC, smul_add, map_add (f := _)]
  push_cast
  ring

theorem leviC_smul_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin D → ℂ) :
    leviC H a (c • b) = starRingEnd ℂ c * leviC H a b := by
  have h1 : c • b = c.re • b + c.im • (Complex.I • b) := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have h2 : Complex.I • (c • b) = c.re • (Complex.I • b) - c.im • b := by
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination ((c.im : ℂ) * b k) * Complex.I_sq
  unfold leviC
  rw [h2, h1]
  simp only [map_add (f := _), map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem sum_leviC_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a x : Fin D → ℂ) :
    ∑ j, leviC H a (Pi.single j 1) * x j = leviC H a (star x) := by
  let ℓ : (Fin D → ℂ) →+ ℂ :=
    { toFun := leviC H a
      map_zero' := by simp [leviC]
      map_add' := leviC_add_right H a }
  have hx : star x = ∑ j, star (x j) • (Pi.single j 1 : Fin D → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single (star x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have := map_sum ℓ (fun j => star (x j) • (Pi.single j 1 : Fin D → ℂ)) Finset.univ
  rw [← hx] at this
  change leviC H a (star x) = ∑ j, leviC H a (star (x j) • Pi.single j 1) at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviC_smul_right]
  simp [mul_comm]

theorem hessC_posSemidef (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (h : ∀ w, 0 ≤ levi φ z w) : (hessC φ z).PosSemidef := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hessC_isHermitian' φ z hφ) fun x => ?_
  have hq : star x ⬝ᵥ ((hessC φ z).mulVec x) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star x) (star x) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul, dotProduct, hessC_eq_leviC, sum_mul_leviC]
    exact sum_leviC_right _ _ _
  rw [hq, Complex.nonneg_iff]
  constructor
  · have := h (star x)
    simp only [levi] at this
    simpa [leviC] using this
  · simp [leviC, hs (star x) (Complex.I • star x)]

end SlopeTestRemainingChoices

end

end ReciprocityTheory.AnForm.M
end

section

namespace ReciprocityTheory.AnForm.M

open Filter Topology FinHolAtlas
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact WithTop.coe_le_coe.2 le_top
  | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤))
  | norm_num
  | simp
  | decide

theorem pshShift_local (A : FinHolAtlas e X) (Ω : LocPot X) (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (w : X → ℝ) (hw : A.Smooth w) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin e → ℂ,
        m * levi (Ω.φ p ∘ (A.chart j).symm) y u ≤ levi (w ∘ (A.chart j).symm) y u := by
  classical
  set φ : (Fin e → ℂ) → ℝ := Ω.φ p ∘ (A.chart j).symm with hφdef
  set ψ : (Fin e → ℂ) → ℝ := w ∘ (A.chart j).symm with hψdef
  set S : Set (Fin e → ℂ) := (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p with hSdef
  have hSo : IsOpen S := (A.chart j).isOpen_inter_preimage_symm (Ω.isOpen_U p)
  have hz0 : A.chart j p ∈ S := by
    refine ⟨(A.chart j).map_source hp, ?_⟩
    show (A.chart j).symm (A.chart j p) ∈ Ω.U p
    rw [(A.chart j).left_inv hp]
    exact Ω.mem_U p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo _ hz0
  have hsub : Metric.closedBall (A.chart j p) (ε / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hφc : ContDiffOn ℝ 2 φ S := (hΩ.1 p j).of_le two_le_infty
  have hψc : ContDiffOn ℝ 2 ψ S :=
    ((hw j).of_le two_le_infty).mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩)
  have hLφ := continuousOn_levi hSo hφc
  have hLψ := continuousOn_levi hSo hψc
  set K : Set ((Fin e → ℂ) × (Fin e → ℂ)) :=
    Metric.closedBall (A.chart j p) (ε / 2) ×ˢ Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKS : K ⊆ S ×ˢ Set.univ := Set.prod_mono hsub (Set.subset_univ _)
  have hposK : ∀ q ∈ K, 0 < levi φ q.1 q.2 := by
    intro q hq
    refine hpos p j q.1 (hsub hq.1) q.2 ?_
    intro h0
    have h1 := hq.2
    rw [h0] at h1
    simp at h1
  have hg : ContinuousOn
      (fun q : (Fin e → ℂ) × (Fin e → ℂ) => levi ψ q.1 q.2 / levi φ q.1 q.2) K :=
    (hLψ.mono hKS).div (hLφ.mono hKS) (fun q hq => (hposK q hq).ne')
  obtain ⟨M, hM⟩ := hK.bddBelow_image hg
  refine ⟨ε / 2, by positivity, M, hsub, ?_⟩
  intro y hy u
  by_cases hu : u = 0
  · subst hu
    simp [levi_zero]
  · have ht : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨s, v, hv, rfl⟩ : ∃ s : ℝ, ∃ v ∈ Metric.sphere (0 : Fin e → ℂ) 1, u = s • v := by
      refine ⟨‖u‖, ‖u‖⁻¹ • u, ?_, ?_⟩
      · simp [norm_smul, hu, ht.ne']
      · simp [smul_smul, hu, ht.ne']
    have hq : ((y, v) : (Fin e → ℂ) × (Fin e → ℂ)) ∈ K := ⟨hy, hv⟩
    have h1 := hM ⟨(y, v), hq, rfl⟩
    have h2 := hposK _ hq
    simp only at h1 h2
    have h3 : M * levi φ y v ≤ levi ψ y v := by
      rwa [le_div_iff₀ h2] at h1
    rw [levi_smul_dir, levi_smul_dir]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]

theorem plurisubharmonicShift_proof : PshShiftStatement := by
  intro e X _ _ _ A Ω hΩ hpos w hw
  classical
  choose jq hjq using A.cover
  choose r hr m hsubq hlocq using fun q => pshShift_local A Ω hΩ hpos w hw q (jq q) (hjq q)
  have hVo : ∀ q, IsOpen ((A.chart (jq q)).source ∩
      A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q)) := fun q =>
    (A.chart (jq q)).continuousOn.isOpen_inter_preimage (A.chart (jq q)).open_source
      Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun q => (A.chart (jq q)).source ∩ A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q))
    hVo (fun q _ => Set.mem_iUnion.2 ⟨q, hjq q, Set.mem_preimage.mpr (Metric.mem_ball_self (hr q))⟩)
  refine ⟨∑ q ∈ t, |m q|, ?_⟩
  intro x k y hy u
  show 0 ≤ levi ((fun z => w z + (∑ q ∈ t, |m q|) * Ω.φ x z) ∘ (A.chart k).symm) y u
  have hyk : y ∈ (A.chart k).target := hy.1
  have hzx : (A.chart k).symm y ∈ Ω.U x :=
    (show (A.chart k).symm y ∈ Set.univ ∩ Ω.U x from hy.2).2
  obtain ⟨q, hqt, hzq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((A.chart k).symm y)))
  have hzq1 : (A.chart k).symm y ∈ (A.chart (jq q)).source ∩
      A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q) := hzq
  have hsub1 := hsubq q
  have hloc1 := hlocq q
  have hC : -m q ≤ ∑ q ∈ t, |m q| :=
    (neg_le_abs (m q)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hqt)
  generalize ∑ q ∈ t, |m q| = C at hC ⊢
  generalize jq q = jj at hzq1 hsub1 hloc1
  obtain ⟨hzj, hzb⟩ := hzq1
  have hτS : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' Ω.U q :=
    hsub1 (Metric.ball_subset_closedBall hzb)
  have hzq' : (A.chart k).symm y ∈ Ω.U q := by
    have h := hτS.2
    rwa [Set.mem_preimage, (A.chart jj).left_inv hzj] at h
  have hτx : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' Ω.U x := by
    refine ⟨(A.chart jj).map_source hzj, ?_⟩
    rw [Set.mem_preimage, (A.chart jj).left_inv hzj]
    exact hzx
  have hψ2 : ContDiffAt ℝ 2 (w ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hw jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm isOpen_univ).mem_nhds
      ⟨(A.chart jj).map_source hzj, Set.mem_univ _⟩)).of_le two_le_infty
  have hΦx2 : ContDiffAt ℝ 2 (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hΩ.1 x jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm (Ω.isOpen_U x)).mem_nhds
      hτx)).of_le two_le_infty
  have hΦq2 : ContDiffAt ℝ 2 (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hΩ.1 q jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm (Ω.isOpen_U q)).mem_nhds
      hτS)).of_le two_le_infty
  have hτa : AnalyticAt ℂ (A.chart jj ∘ (A.chart k).symm) y := A.holo k jj y ⟨hyk, hzj⟩
  have hf2 : ContDiffAt ℝ 2 ((fun z => w z + C * Ω.φ x z) ∘ (A.chart jj).symm)
      ((A.chart jj ∘ (A.chart k).symm) y) := hψ2.add (contDiffAt_const.mul hΦx2)
  have hev1 : (fun z => w z + C * Ω.φ x z) ∘ (A.chart k).symm =ᶠ[𝓝 y]
      ((fun z => w z + C * Ω.φ x z) ∘ (A.chart jj).symm) ∘ (A.chart jj ∘ (A.chart k).symm) := by
    refine Filter.eventuallyEq_of_mem
      (((A.chart k).isOpen_inter_preimage_symm (A.chart jj).open_source).mem_nhds ⟨hyk, hzj⟩) ?_
    intro y' hy'
    simp only [Function.comp_apply]
    rw [(A.chart jj).left_inv hy'.2]
  have hpt : (A.chart jj ∘ (A.chart k).symm) y = A.chart jj ((A.chart k).symm y) := rfl
  set v := fderiv ℂ (A.chart jj ∘ (A.chart k).symm) y u with hvdef
  have hL : levi ((fun z => w z + C * Ω.φ x z) ∘ (A.chart k).symm) y u =
      levi (w ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v +
        C * levi (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    rw [levi_congr hev1, levi_comp u hτa hf2, hpt]
    exact levi_add_smul C hψ2 hΦx2 v
  obtain ⟨W, hWo, hzW, G, hG, hGeq⟩ := hΩ.2 x q ((A.chart k).symm y) ⟨hzx, hzq'⟩
  have hτW : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' (W ∩ Ω.U x ∩ Ω.U q) := by
    refine ⟨(A.chart jj).map_source hzj, ?_⟩
    rw [Set.mem_preimage, (A.chart jj).left_inv hzj]
    exact ⟨⟨hzW, hzx⟩, hzq'⟩
  have hN2 := ((A.chart jj).isOpen_inter_preimage_symm
    ((hWo.inter (Ω.isOpen_U x)).inter (Ω.isOpen_U q))).mem_nhds hτW
  have hGa : AnalyticAt ℂ (G ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    hG jj _ ⟨hτW.1, hτW.2.1.1⟩
  have hev2 : Ω.φ x ∘ (A.chart jj).symm =ᶠ[𝓝 (A.chart jj ((A.chart k).symm y))]
      fun y' => (Ω.φ q ∘ (A.chart jj).symm) y' + 1 * ((G ∘ (A.chart jj).symm) y').re := by
    refine Filter.eventuallyEq_of_mem hN2 ?_
    intro y' hy'
    have := hGeq _ hy'.2
    simp only [Function.comp_apply]
    linarith
  have hev3 : (fun y' => ((G ∘ (A.chart jj).symm) y').re)
      =ᶠ[𝓝 (A.chart jj ((A.chart k).symm y))]
      fun y' => (Ω.φ x ∘ (A.chart jj).symm) y' - (Ω.φ q ∘ (A.chart jj).symm) y' := by
    refine Filter.eventuallyEq_of_mem hN2 ?_
    intro y' hy'
    have := hGeq _ hy'.2
    simp only [Function.comp_apply]
    linarith
  have hRe2 : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart jj).symm) y').re)
      (A.chart jj ((A.chart k).symm y)) :=
    (hΦx2.sub hΦq2).congr_of_eventuallyEq hev3
  have hLx : levi (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v =
      levi (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    rw [levi_congr hev2, levi_add_smul 1 hΦq2 hRe2 v, levi_re_analytic hGa v]
    ring
  have hloc2 := hloc1 (A.chart jj ((A.chart k).symm y)) (Metric.ball_subset_closedBall hzb) v
  have hnn : 0 ≤ levi (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    by_cases hv0 : v = 0
    · rw [hv0, levi_zero]
    · exact (hpos q jj _ hτS v hv0).le
  rw [hL, hLx]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m q + C) hnn]

end

end ReciprocityTheory.AnForm.M
end

section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

theorem analyticSubset_chart_local {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {S : Set X} (hS : A.IsAnalyticSubset S) (hint : interior S = ∅) (j : Fin A.n)
    {z : Fin e → ℂ} (hz : z ∈ (A.chart j) '' (S ∩ (A.chart j).source)) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ (A.chart j) '' (S ∩ (A.chart j).source) ∩ W, f w = 0 := by
  obtain ⟨x, ⟨-, hxs⟩, rfl⟩ := hz
  obtain ⟨W₀, hW₀, hxW₀, r, f, hf, hSW⟩ := hS x
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀) :=
    (A.chart j).isOpen_inter_preimage_symm hW₀
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀ := by
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ W₀
    rw [(A.chart j).left_inv hxs]
    exact hxW₀
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hopen _ hmem

  have hex : ∃ i, ∃ w ∈ Metric.ball ((A.chart j) x) ε, f i ((A.chart j).symm w) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (A.chart j).symm '' Metric.ball ((A.chart j) x) ε ⊆ S := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' := hε hw
      have hin : (A.chart j).symm w ∈ S ∩ W₀ := by
        rw [hSW]
        exact ⟨hw'.2, fun i => hcon i w hw⟩
      exact hin.1
    have hop : IsOpen ((A.chart j).symm '' Metric.ball ((A.chart j) x) ε) :=
      (A.chart j).symm.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun w hw => (hε hw).1)
    have hint' : (A.chart j).symm ((A.chart j) x) ∈ interior S :=
      interior_maximal hsub hop ⟨_, Metric.mem_ball_self hε0, rfl⟩
    rw [hint] at hint'
    exact hint'
  obtain ⟨i, w₀, hw₀, hfw₀⟩ := hex
  refine ⟨Metric.ball ((A.chart j) x) ε, Metric.isOpen_ball, Metric.mem_ball_self hε0,
    (convex_ball _ _).isPreconnected, f i ∘ (A.chart j).symm, ?_, ⟨w₀, hw₀, hfw₀⟩, ?_⟩
  · exact (hf i j).mono hε
  · rintro w ⟨⟨y, ⟨hyS, hys⟩, rfl⟩, hw⟩
    have hw' := hε hw
    have hin : (A.chart j).symm ((A.chart j) y) ∈ S ∩ W₀ :=
      ⟨by rw [(A.chart j).left_inv hys]; exact hyS, hw'.2⟩
    rw [hSW] at hin
    exact hin.2 i

theorem analyticNull : AnalyticNullStatement := by
  intro e X _ A S hS hint j
  exact ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _
    (fun z hz => analyticSubset_chart_local A hS hint j hz)

theorem integralWith_congr_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) {S : Set X} (hS : A.IsAnalyticSubset S)
    (hint : interior S = ∅) {g g' : X → ℝ} (hg : ∀ x ∉ S, g x = g' x) :
    integralWith A P Φ g = integralWith A P Φ g' := by
  first
  | unfold integralWith
  | simp only [integralWith]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hnull : volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0 :=
    analyticNull A S hS hint j
  have hsub : {y | ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y)} ∩
      (A.chart j).target ⊆ (A.chart j) '' (S ∩ (A.chart j).source) := by
    intro y hy
    have hne : ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
        P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y) := hy.1
    have hyt : y ∈ (A.chart j).target := hy.2
    refine ⟨(A.chart j).symm y, ⟨?_, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩
    by_contra hnS
    apply hne
    rw [hg _ hnS]
  have hae : ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y := by
    rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply' hT]
    exact MeasureTheory.measure_mono_null hsub hnull
  exact MeasureTheory.integral_congr_ae hae

theorem mIntCongrNull : MIntCongrNullStatement := by
  unfold MIntCongrNullStatement
  intro e X _ A Φ S hS hint g g' hg
  unfold mInt
  split_ifs with h
  · exact integralWith_congr_null A h.some Φ hS hint hg
  · rfl

end

end ReciprocityTheory.AnForm.M
end
