module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem sz_fderiv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} {f : V → F} {x : V} {b : ℝ} (h : Sz (k + 1) f x b) : Sz k (fderiv ℝ f) x b :=
  fun i hi => by
    rw [norm_iteratedFDeriv_fderiv]
    exact h (i + 1) (Nat.succ_le_succ hi)

private theorem sum_deriv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {Y : Set V} (hY : IsOpen Y) {y : ℕ → V → F}
    (hy : ∀ j, ContDiffOn ℝ ∞ (y j) Y)
    (hb : ∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j))
    {p : V} (hp : p ∈ Y) :
    Summable (fun j => fderiv ℝ (y j) p) ∧
      HasFDerivAt (fun x => ∑' j, y j x) (∑' j, fderiv ℝ (y j) p) p := by
  obtain ⟨N, hN, b, hs, hle⟩ := hb 1 p hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hN (hY.mem_nhds hp))
  have hpN : p ∈ N := mem_of_mem_nhds hN
  have h1 : ∀ j, ∀ x ∈ N, ‖fderiv ℝ (y j) x‖ ≤ b j := fun j x hx => (sz_fderiv (k := 0) (hle j x hx)).norm_le
  refine ⟨Summable.of_norm_bounded hs fun j => h1 j p hpN, ?_⟩
  refine hasFDerivAt_tsum_of_isPreconnected (u := b) (s := Metric.ball p r) (f := y)
    (f' := fun j x => fderiv ℝ (y j) x) (x₀ := p) hs Metric.isOpen_ball (convex_ball p r).isPreconnected
    (fun j x hx => ?_) (fun j x hx => h1 j x (hball hx).1) (Metric.mem_ball_self hr) ?_ (Metric.mem_ball_self hr)
  · exact (((hy j).contDiffAt (hY.mem_nhds (hball hx).2)).differentiableAt (by simp)).hasFDerivAt
  · exact Summable.of_norm_bounded hs fun j => (hle j p hpN).norm_le

private theorem sum_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (y : ℕ → V → F),
    (∀ j, ContDiffOn ℝ ∞ (y j) Y) →
    (∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j)) →
    ContDiffOn ℝ n (fun x => ∑' j, y j x) Y := by
  induction n with
  | zero =>
    intro F _ _ _ y hy hb
    simp only [CharP.cast_eq_zero, Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (sum_deriv hY hy hb hp).2.continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ _ y hy hb
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hY]
    refine ⟨fun p hp => (sum_deriv hY hy hb hp).2.differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have h := ih (V →L[ℝ] F) (fun j => fderiv ℝ (y j))
      (fun j => (hy j).fderiv_of_isOpen hY (by simp)) (fun k p hp => by
        obtain ⟨N, hN, b, hs, hle⟩ := hb (k + 1) p hp
        exact ⟨N, hN, b, hs, fun j x hx => sz_fderiv (hle j x hx)⟩)
    exact h.congr fun p hp => (sum_deriv hY hy hb hp).2.fderiv

theorem UpperTheory.V.Lit.Geo.Cs.sumSm :
    SumSm := by
  intro V F _ _ _ _ _ Y hY y hy hb
  refine ⟨contDiffOn_infty.2 fun n => sum_smooth hY n F y hy hb, fun p hp => ?_⟩
  rw [(sum_deriv hY hy hb hp).2.fderiv]
  exact (sum_deriv hY hy hb hp).1.hasSum
end

section

open UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.Cs.geoRet :
    GeoRet := by
  intro Γ V S _ _ _ _ d G hc l hl Φ hΦ R q w z hw hb hz h
  have hB := fun s => pullB V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s) q (z.1 s) (z.2 s).1
  have hA := fun s => pullA V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s)
  have hs : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pull (l s) (z.1 s)) G.Y := fun s => (hB s).1
  have hv := fun s p (hp : p ∈ G.Y) => UpperTheory.V.Lit.Geo.toOm_apply G hs s hp
  have hd : ∀ s, ∀ p ∈ G.Y, (G.dOm q (UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s))).1 s p =
      pull (l s) (extDeriv (z.1 s)) p := fun s p hp => by
    rw [G.dOm_apply _ s hp, ← (hB s).2 p hp]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [G.isOpen.mem_nhds hp] with y hy using hv s y hy
  refine ⟨UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s), ⟨fun γ => ?_, fun s p hp v i hi => ?_,
    fun s p hp v i hi => ?_⟩, fun s p hp hR => ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [hv s p hp, ← pullEquiv Γ V S d G hc l hl q z hz γ s p hp, ← hv _ _ (G.maps _ _ hp)]
      rfl
    · rw [((G.act q γ _).2 s).2 p hp, (Subtype.prop (p := fun x => x ∈ G.Om q) _ s).2 p hp]
  · rw [hv s p hp]
    exact (hA s q _).1 p hp v i hi
  · rw [hd s p hp]
    exact (hA s (q + 1) _).1 p hp v i hi
  · have hcl : ∀ x ∈ G.Y, extDeriv (w.1 s) x = 0 := fun x hx => by
      rw [← G.dOm_apply w s hx, hw]
      rfl
    have hH := homog V (Fin d → ℂ) G.Y G.isOpen hc (q + 1) _ (w.2 s).1 (hb s) hcl
    have hpos := (hl.1 s).2.1 p hp
    have hm := hc _ hpos p hp
    rw [hd s p hp, ← (hA s (q + 1) _).2 (hb s) hH p hp]
    unfold pull
    rw [← G.dOm_apply z s hm, h s _ hm (by rw [hΦ.2.2 s _ hpos p hp]; exact hR)]
end

section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem parametric_integral_deriv_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : V)
    (O : Set (V × ℝ)) (hO : IsOpen O) (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ O) (b : ℝ) (i : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Φ : V × ℝ → F), ContDiffOn ℝ ∞ Φ O →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i (fun x => Φ (x, t)) p‖ ≤ b) →
      ‖iteratedFDeriv ℝ i (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) p‖ ≤ b := by
  induction i with
  | zero =>
    intro F _ _ _ Φ _ h
    simp only [norm_iteratedFDeriv_zero] at h ⊢
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := b) (f := fun t => Φ (p, t))
      (fun t ht => h t (by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact Set.Ioc_subset_Icc_self ht))
    simpa using this
  | succ i ih =>
    intro F _ _ _ Φ hΦ h
    let Ψ : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ)
    have hΨ : ContDiffOn ℝ ∞ Ψ O :=
      (hΦ.fderiv_of_isOpen hO (by simp)).clm_comp contDiffOn_const
    have hd : ∀ x t, (x, t) ∈ O → fderiv ℝ (fun y => Φ (y, t)) x = Ψ (x, t) := fun x t hx => by
      have h1 : DifferentiableAt ℝ Φ (x, t) := (hΦ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
      exact (h1.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)).fderiv
    have htube : ∀ᶠ x in 𝓝 p, ∀ t ∈ Set.Icc (0 : ℝ) 1, (x, t) ∈ O :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun t ht => hO.mem_nhds (hp t ht)
    have e : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) =ᶠ[𝓝 p] fun x => ∫ t in (0 : ℝ)..1, Ψ (x, t) := by
      filter_upwards [htube] with x hx
      rw [(UpperTheory.V.Lit.Dr.paramDeriv V F x O Φ hO hx hΦ).2.fderiv]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hd x t (hx t ht)
    rw [← norm_iteratedFDeriv_fderiv, (e.iteratedFDeriv ℝ i).eq_of_nhds]
    refine ih _ Ψ hΨ fun t ht => ?_
    have e' : fderiv ℝ (fun y => Φ (y, t)) =ᶠ[𝓝 p] fun x => Ψ (x, t) := by
      filter_upwards [htube] with x hx using hd x t (hx t ht)
    rw [← (e'.iteratedFDeriv ℝ i).eq_of_nhds, norm_iteratedFDeriv_fderiv]
    exact h t ht

theorem UpperTheory.V.Lit.Geo.Cs.intSz :
    IntSz := by
  intro V F _ _ _ _ _ _ k p O Φ b hO hp hΦ h i hi
  exact parametric_integral_deriv_bound V p O hO hp b i F Φ hΦ fun t ht => h t ht i hi
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_pt (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    pt (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * pt g x := by
  unfold pt
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem centre_zero : splitCentre E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext w
    simp [expU]
  rw [splitCentre, h, map_one, map_one]

private theorem scal_ex (r : ℝ) (hr : 0 < r) : ∃ (t : ℝ) (c : GL (Fin a) (Cinf E)),
    infGL E a c = splitCentre E a t ∧ ∀ p : HV E a, sand c p = r • p := by
  refine ⟨Real.log r / 2, _, rfl, fun p => Subtype.ext ?_⟩
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((Real.log r / 2 : ℝ) : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp (Real.log r / 2) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  have e : Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) = r := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  change Matrix.of (sand _ p).1 = r • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, e]

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.descFun :
    DescFun := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS Φ hΦ
  refine ⟨fun s p₀ hp₀ => ?_, ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
    refine ContDiffAt.contDiffWithinAt ?_
    obtain ⟨φ, hφ, -⟩ := hS.f_sm
    have h0 := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at h0
    have h1 := Complex.reCLM.contDiff.contDiffAt.comp p₀ h0
    refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
    have := hΦ (τ p) x
    rw [hp] at this
    rw [this, pt, infGL_comm]
    simp
  · rintro γ s p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ (sand g p) =
        sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1) * g) p := fun p => by
      rw [geo_ρ, map_mul]; rfl
    have hσ : (geo ho U Ξ).σ γ (x : GL (Fin a) (Af E) ⧸ U) =
        ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
    have hl := hS.f_left γ.1 0 (pt g x)
    rw [centre_zero, mul_one] at hl
    rw [hσ, hs, hΦ, hΦ, rat_pt, hl]
  · rintro s r hr p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨t, c, hc, hp⟩ := scal_ex (E := E) (a := a) r hr
    have hl := hS.f_left 1 t (pt g x)
    rw [map_one, one_mul, ← hc, pt, ← mul_assoc, ← map_mul] at hl
    have hs : ∀ p : HV E a, r • sand g p = sand (c * g) p := fun p => by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    rw [hs, hΦ, hΦ]
    exact hl
end
end

section

open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr Filter Topology

theorem UpperTheory.V.Lit.Geo.Cs.locBd :
    LocBd := by
  intro E _ _ a p₀ hp
  obtain ⟨τ, h1, h2⟩ := locSec E a p₀ hp
  have c1 : ContinuousAt (fun p => toL (τ p).val) p₀ := h1.continuousAt
  have c1' : ContinuousAt (fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := c1
  have hi : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (τ p₀).val := by
    apply continuousAt_matrix_inv
    have := NormedRing.inverse_continuousAt (GeneralLinearGroup.det (τ p₀))
    simpa using this
  have c2' : ContinuousAt (fun p => (((τ p)⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E))) p₀ := by
    have := ContinuousAt.comp (f := fun p => ((τ p).val : Matrix (Fin a) (Fin a) (Cinf E))) hi c1'
    simpa only [Matrix.coe_units_inv, Function.comp_def] using this
  have c2 : ContinuousAt (fun p => toL ((τ p)⁻¹).val) p₀ := c2'
  refine ⟨max (‖toL (τ p₀).val‖ + 1) (‖toL ((τ p₀)⁻¹).val‖ + 1), ?_⟩
  filter_upwards [h2, c1.norm.eventually_lt_const (lt_add_one _), c2.norm.eventually_lt_const (lt_add_one _)]
    with p e b1 b2
  exact ⟨τ p, ⟨b1.le.trans (le_max_left _ _), b2.le.trans (le_max_right _ _)⟩, e⟩
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem inv_smooth {τ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ContDiffAt ℝ ∞ (fun y => toL (τ y).val) x) (i j : Fin a) :
    ContDiffAt ℝ ∞ (fun y => (τ y)⁻¹.val i j) x := by
  have hd : ContDiffAt ℝ ∞ (fun y => (τ y).val.det) x := (contDiff_det (E := E) (a := a)).contDiffAt.comp x h
  have hu : IsUnit (τ x).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (τ x).isUnit
  have hi : ContDiffAt ℝ ∞ (fun y => Ring.inverse (τ y).val.det) x := by
    have := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    rw [hu.unit_spec] at this
    exact this.comp x hd
  have ha : ContDiffAt ℝ ∞ (fun y => (τ y).val.adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    refine (contDiff_det (E := E) (a := a)).contDiffAt.comp x
      (f := fun y => toL ((τ y).val.updateRow j (Pi.single i 1))) ?_
    refine contDiffAt_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      have : (fun y => toL ((τ y).val.updateRow k (Pi.single i 1)) k) = fun _ => Pi.single i 1 :=
        funext fun y => Matrix.updateRow_self
      rw [this]; exact contDiffAt_const
    · have : (fun y => toL ((τ y).val.updateRow j (Pi.single i 1)) k) = fun y => toL (τ y).val k :=
        funext fun y => Matrix.updateRow_ne hk
      rw [this]; exact contDiffAt_pi.1 h k
  have e : (fun y => (τ y)⁻¹.val i j) = fun y => Ring.inverse (τ y).val.det * (τ y).val.adjugate i j := by
    funext y
    rw [Matrix.coe_units_inv, Matrix.inv_def]; rfl
  rw [e]
  exact hi.mul ha

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (v : HV E a) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) v) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) v).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * v.1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of v.1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul contDiffAt_const).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

private theorem clm_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : X → V →L[ℝ] V} {x : X} (h : ∀ v, ContDiffAt ℝ ∞ (fun y => f y v) x) : ContDiffAt ℝ ∞ f x := by
  let e₁ : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := .ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : V ≃L[ℝ] V)).trans (ContinuousLinearEquiv.piRing (Fin (Module.finrank ℝ V)))
  have e : f = fun y => e₂.symm (e₂ (f y)) := funext fun y => (e₂.symm_apply_apply _).symm
  rw [e]
  exact e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.2 fun i => h _)

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.secOne :
    SecOne := by
  intro E _ _ a
  obtain ⟨σ, hσ, hs⟩ := locSec E a (hOne E a) hOne_mem_cone
  set k := σ (hOne E a) with hk
  have hk1 : sand k⁻¹ (hOne E a) = hOne E a := by
    have h0 : sand k (hOne E a) = hOne E a := hs.self_of_nhds
    conv_lhs => rw [← h0]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have h1 : ∀ i j, ContDiffAt ℝ ∞ (fun p => (σ p * k⁻¹).val i j) (hOne E a) := fun i j => by
    simp only [Units.val_mul, Matrix.mul_apply]
    exact ContDiffAt.sum fun l _ => (contDiffAt_pi.1 (contDiffAt_pi.1 hσ i) l).mul contDiffAt_const
  have h2 : ContDiffAt ℝ ∞ (fun p => toL (σ p * k⁻¹).val) (hOne E a) :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h1 i j
  have h3 := inv_smooth (τ := fun p => σ p * k⁻¹) h2
  refine ⟨fun p => σ p * k⁻¹, mul_inv_cancel k, h2,
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => h3 i j, ?_, ?_, ?_⟩
  · exact clm_smooth fun v => sand_smooth h1 v
  · exact clm_smooth fun v => sand_smooth (σ := fun p => (σ p * k⁻¹)⁻¹) h3 v
  · filter_upwards [hs] with p hp
    rw [map_mul, ContinuousLinearMap.mul_apply, hk1, hp]
end
end
