module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
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
public import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section

section

open Filter Topology

namespace GlobalTheory

theorem germSections_glue {Y ι : Type} (G : ℂ → (ℂ → Y) → Prop)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') (i₀ : ι)
    (U : ι → Set ℂ) (s : ι → ℂ → Y) (hU : ∀ i, IsOpen (U i))
    (hs : ∀ i, ∀ z ∈ U i, G z (s i))
    (hag : ∀ i j, Set.EqOn (s i) (s j) (U i ∩ U j)) :
    ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
  classical
  refine ⟨fun z => if h : ∃ i, z ∈ U i then s h.choose z else s i₀ z, fun i z hz => ?_⟩
  refine h1 z (s i) _ ?_ (hs i z hz)
  filter_upwards [(hU i).mem_nhds hz] with w hw
  have h : ∃ i, w ∈ U i := ⟨i, hw⟩
  rw [dite_eq_left h]
  exact hag i _ ⟨hw, h.choose_spec⟩

theorem germSections_halfPlane_global (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s')
    (h2 : ∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s)
    (h3 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U)
    (h4 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) :
    ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  have hH : IsOpen {z : ℂ | T < z.im} := isOpen_lt continuous_const Complex.continuous_im

  have glue : ∀ {ι : Type} (_ : ι) (U : ι → Set ℂ) (p : ℂ), (∀ i, IsOpen (U i)) →
      (∀ i, Convex ℝ (U i)) → (∀ i, ∀ z ∈ U i, T < z.im) → (∀ i, p ∈ U i) →
      (∀ i, ∃ s, ∀ z ∈ U i, G z s) → ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
    intro ι i₀ U p ho hc hT hp hs
    obtain ⟨s₀, hs₀⟩ := hs i₀
    have : ∀ i, ∃ s : ℂ → Y, (∀ z ∈ U i, G z s) ∧ s p = s₀ p := fun i => by
      obtain ⟨s, hs⟩ := hs i
      exact h4 (U i) s s₀ (ho i) (hc i) (hT i) hs p (hp i) (hs₀ p (hp i₀))
    choose s hs hsp using this
    refine germSections_glue G h1 i₀ U s ho hs fun i j => ?_
    exact h3 (U i ∩ U j) (s i) (s j) ((ho i).inter (ho j)) ((hc i).inter (hc j))
      (fun z hz => hT i z hz.1) (fun z hz => hs i z hz.1) (fun z hz => hs j z hz.2) p
      ⟨hp i, hp j⟩ ((hsp i).trans (hsp j).symm)
  have loc : ∀ w : ℂ, T < w.im → ∃ D : Set ℂ, IsOpen D ∧ Convex ℝ D ∧ (∀ z ∈ D, T < z.im) ∧
      w ∈ D ∧ ∃ s, ∀ z ∈ D, G z s := by
    intro w hw
    obtain ⟨s, hs⟩ := h2 w hw
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hs.and (hH.mem_nhds hw))
    exact ⟨Metric.ball w ε, Metric.isOpen_ball, convex_ball w ε, fun z hz => (hb z hz).2,
      Metric.mem_ball_self hε, s, fun z hz => (hb z hz).1⟩
  set p : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hpdef
  have hp : T < p.im := by simp [hpdef]
  let good : ℂ → Prop := fun w => ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ (∀ z ∈ U, T < z.im) ∧
      p ∈ U ∧ w ∈ U ∧ ∃ s, ∀ z ∈ U, G z s
  have hgood : ∀ w : ℂ, T < w.im → good w := by
    intro w hw
    let γ : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap p w
    have hγc : Continuous γ := AffineMap.lineMap_continuous
    have hγ0 : γ 0 = p := AffineMap.lineMap_apply_zero p w
    have hγ1 : γ 1 = w := AffineMap.lineMap_apply_one p w
    have hγH : ∀ t ∈ Set.Icc (0 : ℝ) 1, T < (γ t).im := by
      intro t ht
      have hc := ((convex_halfSpace_im_gt T).affine_preimage γ).ordConnected
      exact hc.out (x := 0) (y := 1) (by simpa [hγ0] using hp) (by simpa [hγ1] using hw) ht
    have step : ∀ D : Set ℂ, IsOpen D → Convex ℝ D → (∀ z ∈ D, T < z.im) →
        (∃ s, ∀ z ∈ D, G z s) → ∀ a b : ℝ, 0 ≤ b → γ a ∈ D → γ b ∈ D →
        good (γ a) → good (γ b) := by
      rintro D hDo hDc hDT hDs a b hb ha hbD ⟨U, hUo, hUc, hUT, hpU, haU, hUs⟩
      obtain ⟨t, ht⟩ := glue true (fun i : Bool => cond i U D) (γ a)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption)
      have hK : IsCompact (γ '' Set.Icc 0 b) := isCompact_Icc.image hγc
      have hKc : Convex ℝ (γ '' Set.Icc 0 b) := (convex_Icc 0 b).affine_image γ
      have hsub : γ '' Set.Icc 0 b ⊆ U ∪ D := by
        rintro _ ⟨r, hr, rfl⟩
        rcases le_total r a with h | h
        · left
          exact (hUc.affine_preimage γ).ordConnected.out (x := 0) (y := a)
            (by simpa [hγ0] using hpU) haU ⟨hr.1, h⟩
        · right
          exact (hDc.affine_preimage γ).ordConnected.out (x := a) (y := b) ha hbD ⟨h, hr.2⟩
      obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open (hUo.union hDo) hsub
      refine ⟨Metric.thickening δ (γ '' Set.Icc 0 b), Metric.isOpen_thickening,
        hKc.thickening δ, fun z hz => ?_, ?_, ?_, t, fun z hz => ?_⟩
      · rcases hth hz with h | h
        · exact hUT z h
        · exact hDT z h
      · exact Metric.self_subset_thickening hδ _ ⟨0, ⟨le_rfl, hb⟩, hγ0⟩
      · exact Metric.self_subset_thickening hδ _ ⟨b, ⟨hb, le_rfl⟩, rfl⟩
      · rcases hth hz with h | h
        · exact ht true z h
        · exact ht false z h
    have key := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).induction₂'
      (fun a b => good (γ a) → good (γ b)) (by
        intro x hx
        obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc (γ x) (hγH x hx)
        have : ∀ᶠ y in 𝓝 x, γ y ∈ D := hγc.continuousAt.eventually (hDo.mem_nhds hxD)
        filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with y hy hyI
        exact ⟨step D hDo hDc hDT hDs x y hyI.1 hxD hy, step D hDo hDc hDT hDs y x hx.1 hy hxD⟩)
      (fun _ _ _ _ _ _ h h' hh => h' (h hh)) (x := 0) (y := 1) (by simp) (by simp)
    rw [hγ0, hγ1] at key
    apply key
    obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc p hp
    exact ⟨D, hDo, hDc, hDT, hxD, hxD, hDs⟩
  choose U hUo hUc hUT hpU hwU hUs using hgood
  obtain ⟨t, ht⟩ := glue (ι := {w : ℂ // T < w.im}) ⟨p, hp⟩ (fun w => U w.1 w.2) p
    (fun w => hUo w.1 w.2) (fun w => hUc w.1 w.2) (fun w => hUT w.1 w.2) (fun w => hpU w.1 w.2)
    (fun w => hUs w.1 w.2)
  exact ⟨t, fun w hw => ht ⟨w, hw⟩ w (hwU w hw)⟩

end GlobalTheory
end

section

namespace GlobalTheory

private theorem exists_real_scalar_of_selfAdjoint_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (σ g)) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have key : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, x < y → False := by
    intro x hx y hy hxy
    obtain ⟨m, hxm, hmy⟩ : ∃ m : ℝ, x < m ∧ m < y := ⟨(x + y) / 2, by linarith, by linarith⟩
    have hfc : ContinuousOn (fun t : ℝ => max (t - m) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (t - m) 0).continuousOn
    have hkc : ContinuousOn (fun t : ℝ => max (m - t) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (m - t) 0).continuousOn
    have hprod : cfc (fun t : ℝ => max (t - m) 0) A * cfc (fun t : ℝ => max (m - t) 0) A = 0 := by
      rw [← cfc_mul _ _ A hfc hkc]
      have h0 : (fun t : ℝ => max (t - m) 0 * max (m - t) 0) = (0 : ℝ → ℝ) := by
        funext t
        rcases le_total t m with h | h
        · rw [max_eq_right (by linarith), zero_mul, Pi.zero_apply]
        · rw [max_eq_right (by linarith : m - t ≤ 0), mul_zero, Pi.zero_apply]
      rw [h0, cfc_zero]
    have hk0 : cfc (fun t : ℝ => max (m - t) 0) A ≠ 0 := by
      intro h0
      rw [← cfc_zero ℝ A] at h0
      have h1 := eqOn_of_cfc_eq_cfc h0 hkc continuousOn_const hA hx
      simp only [Pi.zero_apply] at h1
      have h2 : m - x ≤ max (m - x) 0 := le_max_left _ _
      linarith
    obtain ⟨w, hw⟩ : ∃ w, cfc (fun t : ℝ => max (m - t) 0) A w ≠ 0 := by
      by_contra hnot
      simp only [not_exists, not_not] at hnot
      exact hk0 (ContinuousLinearMap.ext hnot)
    let F := cfc (fun t : ℝ => max (t - m) 0) A
    let S : Submodule ℂ H := LinearMap.ker (F : H →ₗ[ℂ] H)
    have hS : IsClosed (S : Set H) := F.isClosed_ker
    have hinv : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
      intro g v hv
      have hv' : F v = 0 := hv
      have hcg : F * σ g = σ g * F := ((hc g).cfc_real _).eq
      change F (σ g v) = 0
      have := congrArg (fun L : H →L[ℂ] H => L v) hcg
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at this
      rw [this, hv', map_zero]
    have hmem : cfc (fun t : ℝ => max (m - t) 0) A w ∈ S := by
      change F (cfc (fun t : ℝ => max (m - t) 0) A w) = 0
      simpa [F] using congrArg (fun L : H →L[ℂ] H => L w) hprod
    rcases hirr S hS hinv with hbot | htop
    · rw [hbot, Submodule.mem_bot] at hmem
      exact hw hmem
    · have hF : F = 0 := by
        ext v
        have hv : v ∈ S := by rw [htop]; exact Submodule.mem_top
        exact hv
      rw [← cfc_zero ℝ A] at hF
      have h1 := eqOn_of_cfc_eq_cfc hF hfc continuousOn_const hA hy
      simp only [Pi.zero_apply] at h1
      have h2 : y - m ≤ max (y - m) 0 := le_max_left _ _
      linarith
  have hsub : ∃ c : ℝ, ∀ x ∈ spectrum ℝ A, x = c := by
    by_cases hne : (spectrum ℝ A).Nonempty
    · obtain ⟨c, hc'⟩ := hne
      refine ⟨c, fun x hx => ?_⟩
      rcases lt_trichotomy x c with h | h | h
      · exact (key x hx c hc' h).elim
      · exact h
      · exact (key c hc' x hx h).elim
    · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨c, hc'⟩ := hsub
  refine ⟨c, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A hA).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hc' x hx
    _ = algebraMap ℝ (H →L[ℂ] H) c := cfc_const c A hA

theorem hilbert_schur_of_adjoint_closed :
    ∀ (G H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)), (∀ g, ∃ g', σ g' = ContinuousLinearMap.adjoint (σ g)) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ T : H →L[ℂ] H, (∀ g, T ∘L σ g = σ g ∘L T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  intro G H _ _ _ σ hadj hirr T hT
  have hcomm : ∀ g, Commute T (σ g) := fun g => hT g
  have hcomm' : ∀ g, Commute (star T) (σ g) := by
    intro g
    obtain ⟨g', hg'⟩ := hadj g
    have h1 := congrArg star (hcomm g').eq
    rw [star_mul, star_mul, hg', ← ContinuousLinearMap.star_eq_adjoint, star_star] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (realPart T : H →L[ℂ] H)
    (realPart T).prop fun g => by
      rw [realPart_apply_coe]
      exact ((hcomm g).add_left (hcomm' g)).smul_left _
  obtain ⟨b, hb⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (imaginaryPart T : H →L[ℂ] H)
    (imaginaryPart T).prop fun g => by
      rw [imaginaryPart_apply_coe]
      exact (((hcomm g).sub_left (hcomm' g)).smul_left _).smul_left _
  refine ⟨(a : ℂ) + Complex.I * b, ?_⟩
  calc T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
        (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((a : ℂ) + Complex.I * b) • (1 : H →L[ℂ] H) := by
        rw [ha, hb, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul,
          mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem norm_sq_toLp_two_eq_integral_norm_sq {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (g : C(K, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp μ g g
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [Complex.mul_conj'] at h
  have h2 : (∫ x, ((‖g x‖ : ℂ)) ^ 2 ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; simp
  rw [h2] at h
  apply Complex.ofReal_injective
  rw [← h, Complex.ofReal_pow]
  rfl

theorem finiteDimensional_of_uniformly_almost_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)),
      (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K),
      (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) →
      FiniteDimensional ℂ E := by
  intro K _ _ _ _ _ _ _ μ _ _ _ E hE U hU hinv
  classical
  obtain ⟨β, hβ1, -, hβU, hβ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := (1 : K))) isOpen_interior
    (Set.singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU))
  have hβ0 : ∀ x, 0 ≤ β x := fun x => (hβ01 x).1
  have hβU' : ∀ u, β u ≠ 0 → u ∈ U := fun u hu =>
    interior_subset (hβU (subset_tsupport _ hu))
  set c : ℝ := ∫ u, β u ∂μ with hc
  have hcpos : 0 < c := β.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 1) (HasCompactSupport.of_compactSpace _) hβ0 (by simp [hβ1 (Set.mem_singleton _)])
  set L := ContinuousMap.toLp (α := K) (E := ℂ) 2 μ ℂ with hL

  let b : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => (β (p.1⁻¹ * p.2) : ℂ), by fun_prop⟩
  have hb : Continuous fun x => L (b x) := L.continuous.comp b.continuous
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x : K => (fun y => L (b y)) ⁻¹' Metric.ball (L (b x)) (c / 4))
    (fun x _ => hb.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity)))
  let ι : E →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨f.1, hE f.1 f.2⟩
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  let Φ : E →ₗ[ℂ] (t → ℂ) := LinearMap.pi fun j : t =>
    (innerSL ℂ (L (b j.1))).toLinearMap ∘ₗ L.toLinearMap ∘ₗ ι
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  have hf0 : ∀ j ∈ t, inner ℂ (L (b j)) (L (ι f)) = 0 := fun j hj => by
    simpa [Φ] using congrFun hf ⟨j, hj⟩
  set g : C(K, ℂ) := ι f with hg
  let R : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => g (p.2 * p.1), by fun_prop⟩
  have hint : ∀ {V : Type} [NormedAddCommGroup V] {F : K → V}, Continuous F → Integrable F μ :=
    fun hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun u => β u • R u) μ := hint (by fun_prop)
  set T : C(K, ℂ) := ∫ u, β u • R u ∂μ with hT
  have hTx : ∀ x, T x = inner ℂ (L (b x)) (L g) := fun x => by
    rw [hT, ContinuousMap.integral_apply hi1, hL, ContinuousMap.inner_toLp,
      ← integral_mul_left_eq_self (μ := μ) (fun z => g z * (starRingEnd ℂ) (b x z)) x]
    congr 1
    ext u
    simp [R, b, mul_comm]
  have hTb : ∀ x, ‖T x‖ ≤ c / 4 * ‖L g‖ := fun x => by
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hx' : ‖L (b x) - L (b j)‖ ≤ c / 4 := by
      rw [← dist_eq_norm]; exact le_of_lt hx
    have : T x = inner ℂ (L (b x) - L (b j)) (L g) := by
      rw [inner_sub_left, hf0 j hj, sub_zero, hTx]
    rw [this]
    exact (norm_inner_le_norm _ _).trans (by gcongr)
  have hLT : ‖L T‖ ≤ c / 4 * ‖L g‖ := by
    have := Lp.norm_le_of_ae_bound (f := L T) (C := c / 4 * ‖L g‖) (by positivity)
      (by
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ T] with x hx
        rw [hL, hx]; exact hTb x)
    simpa [measureUnivNNReal] using this
  have hmove : ∀ u ∈ U, ‖L (R u) - L g‖ ≤ 1 / 2 * ‖L g‖ := fun u hu => by
    have h1 := hinv f.1 f.2 u hu
    have h2 : ‖L (R u - g)‖ ^ 2 ≤ (1 / 2 * ‖L g‖) ^ 2 := by
      rw [mul_pow, hL, norm_sq_toLp_two_eq_integral_norm_sq, norm_sq_toLp_two_eq_integral_norm_sq]
      norm_num
      simpa [R, hg, ι] using h1
    rw [← map_sub]
    exact le_of_sq_le_sq h2 (by positivity)
  have hdiff : L T - c • L g = ∫ u, β u • (L (R u) - L g) ∂μ := by
    rw [hT, ← L.integral_comp_comm hi1, hc, ← integral_smul_const, ← integral_sub]
    · congr 1
      ext1 u
      rw [smul_sub, L.map_smul_of_tower]
    · exact L.integrable_comp hi1
    · exact hint (by fun_prop)
  have hdn : ‖L T - c • L g‖ ≤ c * (1 / 2 * ‖L g‖) := by
    rw [hdiff, hc, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hint (by fun_prop)) (Eventually.of_forall fun u => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hβ0 u)]
    by_cases hu : β u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left (hmove u (hβU' u hu)) (hβ0 u)
  have hfin : c * ‖L g‖ ≤ c / 4 * ‖L g‖ + c * (1 / 2 * ‖L g‖) := by
    have : ‖c • L g‖ ≤ ‖L T‖ + ‖L T - c • L g‖ := by
      simpa using norm_sub_le (L T) (L T - c • L g)
    rw [norm_smul, Real.norm_of_nonneg hcpos.le] at this
    linarith
  have hg0 : ‖L g‖ = 0 := by
    have := norm_nonneg (L g)
    nlinarith
  have hg1 : g = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ
    (by rw [map_zero]; exact norm_eq_zero.1 hg0)
  ext x
  simpa [hg, ι] using congrArg (fun h : C(K, ℂ) => h x) hg1

end GlobalTheory
end

section

open MeasureTheory
namespace GlobalTheory.FinsetSumSmulCoe

theorem coeFn_finset_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type}
    (c : ι → ℂ) (u : ι → Lp ℂ (2 : ENNReal) μ) (s : Finset ι) :
    (((∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * (((u i : α →ₘ[μ] ℂ)) : α → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • u a) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c a) (u a), ih]
      with x h1 h2 h3
    rw [Finset.sum_insert ha]
    change (((c a • u a + ∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ)) : α → ℂ) x = _
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type} [inst_1 : Fintype ι] (c : ι → ℂ) (u : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) μ)), (↑(↑(∑ i : ι, c i • u i) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ] fun (x : α) ↦ ∑ i : ι, c i * (↑(↑(u i) : α →ₘ[μ] ℂ) : α → ℂ) x := by
  intro α _ μ ι _ c u
  exact coeFn_finset_sum_smul c u Finset.univ

end GlobalTheory.FinsetSumSmulCoe
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_eq_const_mul_prod_inner_of_positionwise (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ)
    (h : ∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i,
      B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) :
    ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  by_cases h0 : ∃ i, ∀ w : Hs i, w = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun v v' => ?_⟩
    obtain ⟨c, hc⟩ := h i v v'
    have h1 := hc (v i) (v' i)
    rw [Function.update_eq_self, Function.update_eq_self, hi (v i)] at h1
    simpa using h1
  · have h1 : ∀ i, ∃ e : Hs i, ⟪e, e⟫_ℂ = 1 := by
      intro i
      have : ∃ w : Hs i, w ≠ 0 := by
        by_contra hn
        exact h0 ⟨i, fun w => by_contra fun hw => hn ⟨w, hw⟩⟩
      obtain ⟨w, hw⟩ := this
      refine ⟨((‖w‖ : ℂ))⁻¹ • w, ?_⟩
      have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
      rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp only [map_inv₀, Complex.conj_ofReal]
      change ((‖w‖ : ℂ))⁻¹ * (((‖w‖ : ℂ))⁻¹ * (‖w‖ : ℂ) ^ 2) = 1
      field_simp
    choose e he using h1
    have step : ∀ i v v', B v v' =
        B (Function.update v i (e i)) (Function.update v' i (e i)) * ⟪v i, v' i⟫_ℂ := by
      intro i v v'
      obtain ⟨c, hc⟩ := h i v v'
      have h2 := hc (v i) (v' i)
      rw [Function.update_eq_self, Function.update_eq_self] at h2
      rw [h2, hc, he, mul_one]
    have key : ∀ (s : Finset ι) v v', B v v' =
        B (s.piecewise e v) (s.piecewise e v') * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro v v'; simp
      | insert a s ha ih =>
        intro v v'
        rw [ih v v', step a (s.piecewise e v) (s.piecewise e v'), Finset.prod_insert ha,
          Finset.piecewise_insert, Finset.piecewise_insert,
          Finset.piecewise_eq_of_notMem _ _ _ ha, Finset.piecewise_eq_of_notMem _ _ _ ha,
          mul_assoc]
    refine ⟨B e e, fun v v' => ?_⟩
    have := key Finset.univ v v'
    rwa [Finset.piecewise_univ, Finset.piecewise_univ] at this

end GlobalTheory
end
