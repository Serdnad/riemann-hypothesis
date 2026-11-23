module

public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

theorem ck_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (hph : CkR n z k ph) :
    Ck n z k (fun x => (Real.exp (-ph x) : ℂ)) := by
  intro e he
  have hg : ContDiff ℝ k (fun c : ℂ => ((Real.exp (-c.re) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff.neg)
  refine (hg.comp_contDiffOn (hph e he)).congr fun w _ => ?_
  simp

private theorem differentiableAt_comp_chart_symm_of_ck_one {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) : DifferentiableAt ℝ (f ∘ e.symm) (z x) := by
  rw [he hx]
  exact ((hf e he).differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))

theorem db_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n)
    (x : M) :
    db n z j (fun y => (Real.exp (-ph y) : ℂ)) x =
      -((Real.exp (-ph x) : ℂ) * db n z j (fun y => (ph y : ℂ)) x) := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hex : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hP := differentiableAt_comp_chart_symm_of_ck_one n z (fun y => (ph y : ℂ)) hph e he x hx
    have hQ : DifferentiableAt ℝ (fun w => ph (e.symm w)) (z x) := by
      have := Complex.reCLM.differentiableAt.comp (z x) hP
      simpa [Function.comp_def] using this
    have h1 : fderiv ℝ ((fun y => (Real.exp (-ph y) : ℂ)) ∘ e.symm) (z x) =
        Complex.ofRealCLM.comp (Real.exp (-ph (e.symm (z x))) •
          -(fderiv ℝ (fun w => ph (e.symm w)) (z x))) :=
      (Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt.neg.exp).fderiv
    have h2 : fderiv ℝ ((fun y => (ph y : ℂ)) ∘ e.symm) (z x) =
        Complex.ofRealCLM.comp (fderiv ℝ (fun w => ph (e.symm w)) (z x)) :=
      (Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt).fderiv
    simp only [wdb]
    rw [h1, h2]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Complex.ofRealCLM_apply, smul_eq_mul, hex]
    push_cast
    ring
  · simp [db, dif_neg h]

private theorem d_eq_wd_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) : d n z j u x = wd n j (u ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  rw [d, dif_pos h]
  obtain ⟨he', hx'⟩ := Classical.choose_spec h
  set e' := Classical.choose h

  have hzx : z x = e x := he hx
  have hzx' : z x = e' x := he' hx'
  have hev : ∀ᶠ w in nhds (z x), e'.symm w = e.symm w := by
    have ht : ∀ᶠ w in nhds (z x), w ∈ e.target := by
      rw [hzx]
      exact e.open_target.mem_nhds (e.map_source hx)
    have ht' : ∀ᶠ w in nhds (z x), w ∈ e'.target := by
      rw [hzx']
      exact e'.open_target.mem_nhds (e'.map_source hx')
    have hsrc : ∀ᶠ w in nhds (z x), e'.symm w ∈ e.source := by
      have hc : ContinuousAt e'.symm (z x) := by
        rw [hzx']
        exact e'.continuousAt_symm (e'.map_source hx')
      have hx0 : e'.symm (z x) = x := by
        rw [hzx']
        exact e'.left_inv hx'
      exact hc.preimage_mem_nhds (by rw [hx0]; exact e.open_source.mem_nhds hx)
    filter_upwards [ht, ht', hsrc] with w hw hw' hws
    apply e.injOn hws (e.map_target hw)
    rw [e.right_inv hw, ← he hws, he' (e'.map_target hw'), e'.right_inv hw']
  have hf : u ∘ e'.symm =ᶠ[nhds (z x)] u ∘ e.symm := hev.mono fun w hw => by
    simp only [Function.comp_apply, hw]
  simp only [wd, hf.fderiv_eq]

private theorem contDiffOn_wd_of_contDiffOn_succ (n : ℕ) (j : Fin n) (k : ℕ) (U : V n → ℂ) (s : Set (V n))
    (hs : IsOpen s) (hU : ContDiffOn ℝ ((k + 1 : ℕ)) U s) : ContDiffOn ℝ k (wd n j U) s := by
  have hD : ContDiffOn ℝ k (fun y => fderiv ℝ U y) s :=
    hU.fderiv_of_isOpen hs (by exact_mod_cast le_rfl)
  have h1 := hD.clm_apply (contDiffOn_const (c := bas n j))
  have h2 := hD.clm_apply (contDiffOn_const (c := Complex.I • bas n j))
  exact (h1.sub (contDiffOn_const.mul h2)).div_const 2

theorem ck_dTw {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (j : Fin n) (u : M → ℂ)
    (hph : CkR n z (k + 1) ph) (hu : Ck n z (k + 1) u) : Ck n z k (dTw n z ph j u) := by
  intro e he
  have key : ∀ w ∈ e.target, (dTw n z ph j u ∘ e.symm) w =
      wd n j (u ∘ e.symm) w - (u ∘ e.symm) w * wd n j ((fun y => (ph y : ℂ)) ∘ e.symm) w := by
    intro w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    have hz : z (e.symm w) = w := by
      rw [he hs]
      exact e.right_inv hw
    simp only [Function.comp_apply, dTw]
    rw [d_eq_wd_comp_chart_symm n z j u e he _ hs, d_eq_wd_comp_chart_symm n z j _ e he _ hs, hz]
  refine ContDiffOn.congr ?_ key
  exact (contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hu e he)).sub
    (((hu e he).of_le (by exact_mod_cast Nat.le_succ k)).mul
      (contDiffOn_wd_of_contDiffOn_succ n j k _ _ e.open_target (hph e he)))

private theorem d_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (x : M) (hu : u =ᶠ[nhds x] 0) : d n z j u x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · rw [d, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hc : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    have hx0 : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hev : u ∘ e.symm =ᶠ[nhds (z x)] fun _ => (0 : ℂ) := by
      have ht := hc.tendsto
      rw [hx0] at ht
      exact ht.eventually hu
    simp only [wd, hev.fderiv_eq]
    simp
  · rw [d, dif_neg h]

private theorem db_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (x : M) (hu : u =ᶠ[nhds x] 0) : db n z j u x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · rw [db, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hc : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    have hx0 : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hev : u ∘ e.symm =ᶠ[nhds (z x)] fun _ => (0 : ℂ) := by
      have ht := hc.tendsto
      rw [hx0] at ht
      exact ht.eventually hu
    simp only [wdb, hev.fderiv_eq]
    simp
  · rw [db, dif_neg h]

theorem tsupport_dTw_subset {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (u : M → ℂ) :
    tsupport (dTw n z ph j u) ⊆ tsupport u := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport u)
  by_contra hxu
  apply hx
  have hu0 : u =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxu
  simp only [dTw]
  rw [d_eq_zero_of_eventuallyEq_zero n z j u x hu0, hu0.eq_of_nhds]
  simp

theorem hasCompactSupport_d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (d n z j u) := by
  refine hu.mono' fun x hx => ?_
  by_contra hxu
  exact hx (d_eq_zero_of_eventuallyEq_zero n z j u x (notMem_tsupport_iff_eventuallyEq.1 hxu))

theorem hasCompactSupport_db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (db n z j u) := by
  refine hu.mono' fun x hx => ?_
  by_contra hxu
  exact hx (db_eq_zero_of_eventuallyEq_zero n z j u x (notMem_tsupport_iff_eventuallyEq.1 hxu))

theorem hasCompactSupport_dTw {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (dTw n z ph j u) := by
  exact hu.mono' ((subset_tsupport _).trans (tsupport_dTw_subset n z ph j u))

end

end ReciprocityTheory.L2DbarEstimates.E
end

section

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[nhds (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ nhds (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2

private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dite_eq_left hex]
  unfold wdb
  rw [hE.fderiv_eq]

private lemma d_apply_eq_wd_of_mem_source {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : d n z k g p = wd n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [d, dite_eq_left hex]
  unfold wd
  rw [hE.fderiv_eq]

private lemma differentiableAt_wdb_and_fderiv_wdb_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wdb n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hW' : HasFDerivAt (wdb n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

private lemma differentiableAt_wd_and_fderiv_wd_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wd n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wd n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) -
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.sub hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wd n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) - Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wd, div_eq_inv_mul]
  have hW' : HasFDerivAt (wd n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) -
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  ring

theorem comm (n : ℕ) (M : Type*) [TopologicalSpace M] : CommStatement n M := by
  intro z hz ph j k u x hph hu
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ nhds (z x) := e0.open_target.mem_nhds hy0
  have hcH : ContDiffAt ℝ 2 (u ∘ e0.symm) (z x) := by
    have := (hu e0 he0).contDiffAt hnb
    simpa using this
  have hcP : ContDiffAt ℝ 2 ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) := by
    have := (hph e0 he0).contDiffAt hnb
    simpa using this
  have hdH : DifferentiableAt ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) :=
    (hcH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdP : DifferentiableAt ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) :=
    (hcP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : DifferentiableAt ℝ (u ∘ e0.symm) (z x) := hcH.differentiableAt (by norm_num)
  have hsymH : ∀ v w : V n, fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcH.isSymmSndFDerivAt (by simp) v w
      | exact hcH.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hsymP : ∀ v w : V n, fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcP.isSymmSndFDerivAt (by simp) v w
      | exact hcP.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hloc1 : ((db n z j u) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j (u ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j u _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc2 : ((db n z j (fun y => ((ph y : ℝ) : ℂ))) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j _ _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc3 : ((fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) ∘ e0.symm) =ᶠ[nhds (z x)]
      (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) := by
    filter_upwards [hnb] with y hy
    have hp := e0.map_target hy
    rw [Function.comp_apply, d_apply_eq_wd_of_mem_source z e0 he0 k u _ hp, d_apply_eq_wd_of_mem_source z e0 he0 k _ _ hp,
      he0' hp, e0.right_inv hy]
    rfl
  have hux : u x = (u ∘ e0.symm) (z x) := by
    rw [Function.comp_apply, he0' hx0, e0.left_inv hx0]
  have hW1 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdH).2
  have hW2 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdH
  have hW3 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdP
  have hW4 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdP).2
  have hFG : fderiv ℝ (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) (z x) =
      fderiv ℝ (wd n k (u ∘ e0.symm)) (z x) - ((u ∘ e0.symm) (z x) • fderiv ℝ (wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) +
        wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) • fderiv ℝ (u ∘ e0.symm) (z x)) := by
    have h1 := HasFDerivAt.sub (DifferentiableAt.hasFDerivAt hW2.1)
      (HasFDerivAt.mul (DifferentiableAt.hasFDerivAt hH) (DifferentiableAt.hasFDerivAt hW3.1))
    exact HasFDerivAt.fderiv h1
  show (d n z k (db n z j u) x - db n z j u x * d n z k (fun y => ((ph y : ℝ) : ℂ)) x) -
      db n z j (fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) x =
    d n z k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x * u x
  rw [d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j u) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j u x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (fun y => ((ph y : ℝ) : ℂ)) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x hx0, hux]
  unfold wd wdb
  rw [hloc1.fderiv_eq, hloc2.fderiv_eq, hloc3.fderiv_eq, hFG]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hW1 (bas n k), hW1 (Complex.I • bas n k), hW2.2 (bas n j), hW2.2 (Complex.I • bas n j),
    hW3.2 (bas n j), hW3.2 (Complex.I • bas n j), hW4 (bas n k), hW4 (Complex.I • bas n k)]
  unfold wd
  rw [hsymH (bas n k) (bas n j), hsymH (bas n k) (Complex.I • bas n j),
    hsymH (Complex.I • bas n k) (bas n j), hsymH (Complex.I • bas n k) (Complex.I • bas n j),
    hsymP (bas n k) (bas n j), hsymP (bas n k) (Complex.I • bas n j),
    hsymP (Complex.I • bas n k) (bas n j), hsymP (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.E
end
