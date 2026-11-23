module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem absProj_ext {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : D → H) (hd : ∀ w : H, (∀ v : D, inner ℂ w (e v) = 0) → w = 0) (L : H →L[ℂ] H)
    (hL : ∀ v, L (e v) = 0) (w : H) : L w = 0 := by
  have hperp : (Submodule.span ℂ (Set.range e))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    apply hd u
    intro v
    rw [inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ u).1 hu (e v) (Submodule.subset_span ⟨v, rfl⟩)
  have hcl : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]
  have hle : Submodule.span ℂ (Set.range e) ≤ LinearMap.ker (L : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hL v
  have hle' : (Submodule.span ℂ (Set.range e)).topologicalClosure ≤ LinearMap.ker (L : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hle L.isClosed_ker
  have hw : w ∈ LinearMap.ker (L : H →ₗ[ℂ] H) := hle' (hcl ▸ Submodule.mem_top)
  exact hw

theorem UpperTheory.V.Cj.H.absProj :
    UpperTheory.V.Cj.H.AbsProj := by
  intro G H _ _ _ _ R D A hD hiso hAR hsym hirr
  set s : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hsdef
  have hs : ∀ k : ℕ, s k ≠ 0 := fun k ↦ by
    simp only [hsdef]
    positivity
  have hs0 : Filter.Tendsto s Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdense : ∀ (t : ℝ), t ≠ 0 → ∀ (w : H),
      (∀ (v : ↥D), inner ℂ w (↑(A v) + (Complex.I * ↑t) • ↑v) = 0) → w = 0 :=
    absDense G H R D A hD hiso hAR hsym hirr
  have hdense' : ∀ (k : ℕ) (w : H),
      (∀ v : ↥D, inner ℂ w (↑(A v) - (Complex.I * ↑(s k)) • ↑v) = 0) → w = 0 := by
    intro k w hw
    refine hdense (-(s k)) (neg_ne_zero.2 (hs k)) w fun v ↦ ?_
    have h : (↑(A v) : H) + (Complex.I * ((-(s k) : ℝ) : ℂ)) • (↑v : H)
        = ↑(A v) - (Complex.I * ↑(s k)) • ↑v := by
      push_cast
      rw [mul_neg, neg_smul, ← sub_eq_add_neg]
    rw [h]
    exact hw v
  have hT : ∀ k : ℕ, ∃ T : H →L[ℂ] H,
      (∀ v : ↥D, T (↑(A v) + (Complex.I * ↑(s k)) • ↑v) = ↑v) ∧ ∀ w : H, |s k| * ‖T w‖ ≤ ‖w‖ :=
    fun k ↦ absInv H D A hsym (s k) (hs k) (hdense (s k) (hs k))
  choose T hTinv hTbd using hT
  have hTR : ∀ (k : ℕ) (g : G) (w : H), T k (R g w) = R g (T k w) := by
    intro k g w
    have key := absProj_ext (fun v : ↥D ↦ (↑(A v) + (Complex.I * ↑(s k)) • ↑v : H))
      (hdense (s k) (hs k)) ((T k).comp (R g) - (R g).comp (T k)) ?_ w
    · simpa [sub_eq_zero] using key
    · intro v
      have hv : (R g) ↑v ∈ D := hD g v v.2
      have h1 : (R g) (↑(A v) + (Complex.I * ↑(s k)) • ↑v)
          = ↑(A ⟨(R g) ↑v, hv⟩) + (Complex.I * ↑(s k)) • ↑(⟨(R g) ↑v, hv⟩ : ↥D) := by
        rw [map_add (f := _), map_smul, hAR g v]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      rw [h1, hTinv k ⟨(R g) ↑v, hv⟩, hTinv k v]
      simp
  set K : Submodule ℂ H := (D.subtype ∘ₗ A).range.topologicalClosure with hKdef
  set P : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - K.starProjection with hPdef
  have hPperp : ∀ (w : H) (v : ↥D), inner ℂ (P w) ↑(A v) = 0 := by
    intro w v
    have hAv : (↑(A v) : H) ∈ K :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (D.subtype ∘ₗ A) v)
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    exact Submodule.inner_left_of_mem_orthogonal hAv (K.sub_starProjection_mem_orthogonal w)
  have hclose : ∀ w : H, w - P w ∈ (D.subtype ∘ₗ A).range.topologicalClosure := by
    intro w
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_sub_cancel]
    exact K.starProjection_apply_mem w
  have hlim := absLim H D A hsym s hs0 (fun k ↦ hdense (s k) (hs k)) hdense' T hTinv hTbd P
    hPperp hclose
  refine ⟨P, fun k ↦ (Complex.I * ↑(s k)) • T k, T, ?_, ?_, ?_, ?_, hPperp, ?_⟩
  · intro g w
    have h2 : Filter.Tendsto (fun k ↦ (Complex.I * ↑(s k)) • T k (R g w)) Filter.atTop
        (𝓝 (R g (P w))) := by
      refine (((R g).continuous.tendsto _).comp (hlim w)).congr fun k ↦ ?_
      simp [Function.comp_apply, map_smul, hTR k g w]
    exact tendsto_nhds_unique (hlim (R g w)) h2
  · intro k g w
    simp [ContinuousLinearMap.smul_apply, map_smul, hTR k g w]
  · intro k g w
    exact hTR k g w
  · intro k v
    have h := hTinv k v
    rw [map_add (f := _), map_smul] at h
    rw [ContinuousLinearMap.smul_apply]
    exact (eq_sub_of_add_eq h).symm
  · intro w
    simpa only [ContinuousLinearMap.smul_apply] using hlim w
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.cvGrow :
    UpperTheory.V.Cj.H.CvGrow := by
  intro E _ _ _ a ha μ _ _ ψ hψc hψs F g
  obtain ⟨B, hB0, hB⟩ := cvCount (GA E a) (latticeGL E a) μ ψ hψc hψs
  have hKc : IsCompact (tsupport ψ) := hψs.isCompact
  obtain ⟨C, N, hC⟩ := latCount E a ha ((tsupport ψ)⁻¹ * tsupport ψ) (hKc.inv.mul hKc) g
  refine ⟨B * ‖F‖ * C, N, fun y => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hC y
  have key : ∀ h : GA E a,
      {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.encard ≤ (M : ℕ∞) := by
    intro h
    by_cases hne : {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.Nonempty
    · obtain ⟨γ₀, hγ₀⟩ := hne
      refine le_trans (Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_ ?_) hcard
      · intro γ hγ
        simp only [Set.mem_setOf_eq] at hγ hγ₀ ⊢
        have h₁ := subset_tsupport ψ hγ
        have h₂ := subset_tsupport ψ hγ₀
        have e : (g * infGL E a y)⁻¹ * ↑(γ * γ₀⁻¹) * (g * infGL E a y)
            = ((↑γ * h)⁻¹ * (g * infGL E a y))⁻¹ * ((↑γ₀ * h)⁻¹ * (g * infGL E a y)) := by
          push_cast
          group
        rw [e]
        exact Set.mul_mem_mul (Set.inv_mem_inv.mpr h₁) h₂
      · intro γ _ δ _ hγδ
        simpa using hγδ
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hx := hB (g * infGL E a y) M key F
  calc ‖cv ψ F (g * infGL E a y)‖ ≤ B * M * ‖F‖ := hx
    _ = B * ‖F‖ * M := by ring
    _ ≤ B * ‖F‖ * (C * height y ^ N) :=
        mul_le_mul_of_nonneg_left hM (mul_nonneg hB0 (norm_nonneg _))
    _ = B * ‖F‖ * C * height y ^ N := by ring
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.cvAlg :
    UpperTheory.V.Cj.H.CvAlg := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs
  obtain ⟨hloc, hcnt⟩ := locInt G Γ μ
  obtain ⟨B, hB, hbd⟩ := cvCount G Γ μ ψ hψ hψs
  have hint : ∀ (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (x : G),
      MeasureTheory.Integrable (fun y ↦ GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) μ := by
    intro F x
    have hc : Continuous fun y : G ↦ ψ (y⁻¹ * x) :=
      hψ.comp (continuous_inv.mul continuous_const)
    have hs : HasCompactSupport fun y : G ↦ ψ (y⁻¹ * x) :=
      hψs.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
    simpa [smul_eq_mul] using (hloc F).integrable_smul_right_of_hasCompactSupport hc hs
  refine ⟨hint, ?_, ?_, ?_⟩
  · intro F F' s t
    funext x
    have hae : ∀ᵐ y ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑(s • F + t • F')) y
        = s * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y + t * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y := by
      have h := Filter.Eventually.and (MeasureTheory.Lp.coeFn_add (s • F) (t • F'))
        (Filter.Eventually.and (MeasureTheory.Lp.coeFn_smul s F)
          (MeasureTheory.Lp.coeFn_smul t F'))
      have h' := (GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff (μ := μ)).1 h
      filter_upwards [h'] with y hy
      obtain ⟨e1, e2, e3⟩ := hy
      simp only [GlobalTheory.AutomorphicL2Unitary.lift]
      rw [e1, Pi.add_apply, e2, e3]
      simp [smul_eq_mul]
    calc cv ψ (s • F + t • F') x
        = ∫ y, (s * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x))
            + t * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y * ψ (y⁻¹ * x))) ∂μ := by
          unfold UpperTheory.V.Cj.H.cv
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [hy]
          ring
      _ = (s • cv ψ F + t • cv ψ F') x := by
          rw [MeasureTheory.integral_add ((hint F x).const_mul s) ((hint F' x).const_mul t),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          simp [UpperTheory.V.Cj.H.cv, smul_eq_mul]
  · intro F γ hγ g
    unfold UpperTheory.V.Cj.H.cv
    rw [← MeasureTheory.integral_mul_left_eq_self _ γ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [GlobalTheory.AutomorphicL2Unitary.leftInv_lift _ γ hγ y, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · intro C hC
    have hK : IsCompact (tsupport ψ) := hψs
    obtain ⟨N, hN⟩ := hcnt (C * (tsupport ψ)⁻¹) (hC.mul hK.inv)
    refine ⟨B * (N : ℝ), fun F x hx ↦ ?_⟩
    refine hbd x N (fun g ↦ le_trans (Set.encard_le_encard ?_) (hN g)) F
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    have hmem : ((γ : G) * g)⁻¹ * x ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hγ)
    have heq : (γ : G) * g = x * (((γ : G) * g)⁻¹ * x)⁻¹ := by group
    rw [heq]
    exact Set.mul_mem_mul hx (Set.inv_mem_inv.2 hmem)
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def Fty {I : Type} (f : (I → ℂ) → ℂ) : Prop :=
  ∃ L : I →₀ ℂ, ∀ b : I → ℂ, Finsupp.linearCombination ℂ b L = f b

private theorem fty_ev {I : Type} (a : ℂ) (i : I) : Fty fun b : I → ℂ => a * b i :=
  ⟨Finsupp.single i a, fun b => by rw [Finsupp.linearCombination_single, smul_eq_mul]⟩

private theorem fty_sub {I : Type} {f g : (I → ℂ) → ℂ} (hf : Fty f) (hg : Fty g) : Fty fun b => f b - g b := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨L - M, fun b => by rw [map_sub, hL, hM]⟩

private theorem fty_sum {I K : Type} (t : Finset K) (f : K → (I → ℂ) → ℂ) (hf : ∀ k, Fty (f k)) :
    Fty fun b => ∑ k ∈ t, f k b := by
  choose L hL using hf
  exact ⟨∑ k ∈ t, L k, fun b => by rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hL k b⟩

private theorem fty_solve {I J : Type} (f : J → (I → ℂ) → ℂ) (hf : ∀ j, Fty (f j)) (c : J → ℂ) (cn : ℕ → J → ℂ)
    (h : ∀ k, ∃ b, ∀ j, f j b = cn k j) (hl : ∀ j, Tendsto (fun k => cn k j) atTop (𝓝 (c j))) :
    ∃ b, ∀ j, f j b = c j := by
  choose L hL using hf
  have hs : ∀ (b : I → ℂ) j, (L j).sum (fun i x => x * b i) = f j b := by
    intro b j
    rw [← hL, Finsupp.linearCombination_apply]
    rfl
  obtain ⟨b, hb⟩ := absSolve I J L c cn (fun k => by
    obtain ⟨b, hb⟩ := h k
    exact ⟨b, fun j => by rw [hs, hb]⟩) hl
  exact ⟨b, fun j => by rw [← hs, hb]⟩

theorem UpperTheory.V.Cj.H.hCobLim :
    UpperTheory.V.Cj.H.HCobLim := by
  intro Γ S _ d ρ hρ q c cn h hl
  have hlim : ∀ x : List Γ, x.length = q + 1 → ∀ s i,
      Tendsto (fun k => (c - cn k) x s i) atTop (𝓝 (c x s i)) := by
    intro x hx s i
    have h1 : Tendsto (fun k => cn k x s i) atTop (𝓝 0) := tendsto_pi_nhds.1 (hl x hx s) i
    simpa using (tendsto_const_nhds (x := c x s i)).sub h1
  cases q with
  | zero =>
    intro x hx
    funext s i
    have h1 := hlim x hx s i
    have h2 : (fun k => (c - cn k) x s i) = fun _ => (0 : ℂ) := by
      funext k
      rw [h k x hx]
      rfl
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  | succ q =>
    let cur : (List Γ × S × Fin d → ℂ) → List Γ → S → Fin d → ℂ := fun b x s i => b (x, s, i)
    let f : (Γ × {x : List Γ // x.length = q + 1} × S × Fin d) ⊕ ({x : List Γ // x.length = q + 2} × S × Fin d) →
        (List Γ × S × Fin d → ℂ) → ℂ :=
      Sum.elim (fun p b => cur b (p.2.1.1.map (p.1 * ·)) p.2.2.1 p.2.2.2 - ρ p.1 (cur b p.2.1.1) p.2.2.1 p.2.2.2)
        (fun p b => hd (cur b) p.1.1 p.2.1 p.2.2)
    have hf : ∀ j, Fty (f j) := by
      rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
      · obtain ⟨s', B, hB⟩ := hρ γ s
        have e : f (Sum.inl (γ, x, s, i)) =
            fun b => 1 * b (x.1.map (γ * ·), s, i) - ∑ j, B i j * b (x.1, s', j) := by
          funext b
          simp only [f, Sum.elim_inl, hB, one_mul]
          rfl
        rw [e]
        exact fty_sub (fty_ev _ _) (fty_sum _ _ fun j => fty_ev _ _)
      · have e : f (Sum.inr (x, s, i)) =
            fun b => ∑ j ∈ Finset.range x.1.length, ((-1 : ℂ) ^ j) * b (x.1.eraseIdx j, s, i) := by
          funext b
          simp [f, cur, hd, Finset.sum_apply]
        rw [e]
        exact fty_sum _ _ fun j => fty_ev _ _
    obtain ⟨b, hb⟩ := fty_solve f hf (Sum.elim (fun _ => 0) fun p => c p.1.1 p.2.1 p.2.2)
      (fun k => Sum.elim (fun _ => 0) fun p => (c - cn k) p.1.1 p.2.1 p.2.2) (fun k => by
        obtain ⟨b, h1, h2⟩ := h k
        refine ⟨fun p => b p.1 p.2.1 p.2.2, ?_⟩
        rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
        · change b (x.1.map (γ * ·)) s i - ρ γ (b x.1) s i = 0
          rw [h1 γ x.1 x.2, sub_self]
        · change hd b x.1 s i = (c - cn k) x.1 s i
          rw [h2 x.1 x.2]) (by
        rintro (p | ⟨x, s, i⟩)
        · exact tendsto_const_nhds
        · exact hlim x.1 x.2 s i)
    refine ⟨cur b, fun γ x hx => ?_, fun x hx => ?_⟩
    · funext s i
      exact sub_eq_zero.1 (hb (Sum.inl (γ, ⟨x, hx⟩, s, i)))
    · funext s i
      exact (hb (Sum.inr (⟨x, hx⟩, s, i))).symm
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.WignerSubquotient

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem relQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (S : Subalgebra ℂ (A × B)) {n : ℕ}
    (X : Fin n → Fin n → A) (Y : Fin n → Fin n → B) (h : ∀ p q, (X p q, Y p q) ∈ S) (v : ℂ) :
    (Formalism.REAL.qdet X v, Formalism.REAL.qdet Y v) ∈ S := by
  let Z : Fin n → Fin n → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : A × B).1 = Formalism.REAL.qdet X v := mapQ ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : A × B).2 = Formalism.REAL.qdet Y v := mapQ ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

section

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

private theorem intQ {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R (Formalism.REAL.qdet X v m) = Formalism.REAL.qdet Y v (R m) := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | ∀ m, R (z.1 m) = z.2 (R m)}
      mul_mem' := fun {x y} hx hy m => (hx _).trans (congrArg x.2 (hy m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S X Y h v m

private theorem intQop {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R ((Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) v).unop m) =
      (Formalism.REAL.qdet (fun i j => -MulOpposite.op (Y i j)) v).unop (R m) := by
  let S : Subalgebra ℂ ((Module.End ℂ M)ᵐᵒᵖ × (Module.End ℂ M')ᵐᵒᵖ) :=
    { carrier := {z | ∀ m, R (z.1.unop m) = z.2.unop (R m)}
      mul_mem' := fun {x y} hx hy m => (hy _).trans (congrArg y.2.unop (hx m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S (fun i j => -MulOpposite.op (X i j)) (fun i j => -MulOpposite.op (Y i j))
    (fun p q m => (map_neg R _).trans (congrArg Neg.neg (h p q m))) v m

end

variable {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private noncomputable def res (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (N : Submodule ℂ M) (h : ∀ X, ∀ m ∈ N, L X m ∈ N) :
    Lie E a →ₗ[ℝ] Module.End ℂ N where
  toFun X := (L X).restrict (h X)
  map_add' X Y := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_add L X Y) m.1)
  map_smul' c X := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_smul L c X) m.1)

private theorem res_hom {L : Lie E a →ₗ[ℝ] Module.End ℂ M} (hL : IsLieHom L) (N : Submodule ℂ M)
    (h : ∀ X, ∀ m ∈ N, L X m ∈ N) : IsLieHom (res L N h) :=
  fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hL X Y) m.1)

private theorem res_dCo {L : Lie E a →ₗ[ℝ] Module.End ℂ M} {N : Submodule ℂ M} {L' : Lie E a →ₗ[ℝ] Module.End ℂ N}
    (h : ∀ X m, (L' X m : M) = L X m) {q : ℕ} (ω' : Herm E a [⋀^Fin q]→ₗ[ℝ] N) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ Y, (ω' Y : M) = ω Y) (Y : Fin (q + 1) → Herm E a) : (dCo L' ω' Y : M) = dCo L ω Y := by
  rw [dCo_apply, dCo_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hω, ← h]
  exact map_zsmul N.subtype _ _

end UpperTheory.V.Cj.H.WignerSubquotient

open UpperTheory.V.Cj.H.WignerSubquotient in
theorem UpperTheory.V.Cj.H.wigSub :
    UpperTheory.V.Cj.H.WigSub := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hAB N sA sB τ x z hz
  subst hz
  refine ⟨?_, fun q ω h1 h2 hN => ?_⟩
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a M LA LB hA hB hAB τ x
    exact (wigHom E a M (LA + LB) α _ p1 p2).1
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a N (res LA N sA) (res LB N sB) (res_hom hA N sA) (res_hom hB N sB)
      (fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hAB X Y) m.1)) τ x
    let ω' : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] N :=
      { toFun := fun Y => ⟨ω Y, hN Y⟩
        map_update_add' := fun Y i u v => Subtype.ext (ω.map_update_add Y i u v)
        map_update_smul' := fun Y i c u => Subtype.ext (ω.map_update_smul Y i c u)
        map_eq_zero_of_eq' := fun Y i j e hij => Subtype.ext (ω.map_eq_zero_of_eq Y e hij) }
    have hL : ∀ X (m : N), ((res LA N sA + res LB N sB) X m : M) = (LA + LB) X m := fun _ _ => rfl
    obtain ⟨η, hη⟩ := (wigHom E a N (res LA N sA + res LB N sB) α _ p1 p2).2 q ω'
      (fun Z hZ Y => Subtype.ext ((h1 Z hZ Y).trans
        (Submodule.coe_sum N (fun i => ω' (Function.update Y i (brH Z hZ (Y i)))) Finset.univ).symm))
      (AlternatingMap.ext fun Y => Subtype.ext ((res_dCo hL ω' ω (fun _ => rfl) Y).trans (by rw [h2]; rfl)))
    refine ⟨(N.subtype.restrictScalars ℝ).compAlternatingMap η, fun Y => (η Y).2, fun Y => ?_⟩
    rw [← res_dCo hL η _ (fun _ => rfl) Y, hη, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub]
    exact congrArg₂ (· - ·) (intQ N.subtype _ (eL LA τ) (fun _ _ _ => rfl) x (ω' Y))
      (intQop N.subtype _ (eL LB τ) (fun _ _ _ => rfl) x (ω' Y))
end
