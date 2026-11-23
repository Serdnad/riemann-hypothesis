module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {G H : Type} [Group G] [Group H]

private def stab (ι : H →* G) (f : G → ℂ) : Subgroup H where
  carrier := {k | ∀ g, f (g * ι k) = f g}
  one_mem' := fun g => by rw [map_one, mul_one]
  mul_mem' := fun {k l} hk hl g => by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' := fun {k} hk g => by
    rw [← hk (g * ι k⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]

private theorem summ (u : G → ℂ) (hu : HasCompactSupport u) (g : G) : Summable fun γ : Γ => u (γ * g) := by
  have hd : _root_.IsDiscrete (Γ : Set G) := ⟨inferInstanceAs (DiscreteTopology Γ)⟩
  have ht := Subgroup.tendsto_coe_cofinite_of_discrete Γ hd
  have hK : IsCompact ((fun x => x * g⁻¹) '' tsupport u) := IsCompact.image hu (by fun_prop)
  have hf := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hf
  refine summable_of_hasFiniteSupport (hf.subset fun γ hγ => ?_)
  simp only [Set.mem_compl_iff, Set.mem_preimage, not_not]
  exact ⟨γ * g, subset_tsupport _ hγ, by simp⟩

private theorem orb_ne (u : G → ℂ) (hu : HasCompactSupport u) (hp : ∀ g, ∃ t : ℝ, 0 ≤ t ∧ u g = t) (g : G)
    (γ : G) (hγ : γ ∈ Γ) (h : u (γ * g) ≠ 0) : GlobalTheory.AutomorphicL2Unitary.orbitSum Γ u g ≠ 0 := by
  have hs := summ Γ u hu g
  have h0 : ∀ x, 0 ≤ (u x).re := fun x => by
    obtain ⟨t, ht, e⟩ := hp x
    rw [e, Complex.ofReal_re]; exact ht
  have h1 : 0 < (u (γ * g)).re := by
    obtain ⟨t, ht, e⟩ := hp (γ * g)
    rw [e] at h ⊢
    rw [Complex.ofReal_re]
    exact lt_of_le_of_ne ht fun e' => h (by rw [← e', Complex.ofReal_zero])
  intro hz
  have h2 := congrArg Complex.re hz
  rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, Complex.re_tsum hs, Complex.zero_re] at h2
  exact (Summable.tsum_pos (Complex.hasSum_re hs.hasSum).summable (fun δ => h0 _) ⟨γ, hγ⟩ h1).ne' h2

end

private theorem lev_iff {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (φ : Sm E a) :
    HasLev φ ↔ IsOpen (stab (finGL E a) φ.1 : Set (GL (Fin a) (Af E))) := by
  have : {k | act (.fin k) φ = φ} = (stab (finGL E a) φ.1 : Set (GL (Fin a) (Af E))) := by
    ext k
    exact ⟨fun h g => congrFun (congrArg Subtype.val h) g, fun h => Subtype.ext (funext h)⟩
  rw [HasLev, this]

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.orbLift :
    UpperTheory.V.Cj.H.OrbLift := by
  intro E _ _ _ a φ hφ hL C hC hs
  obtain ⟨u, hu, hp, hne, -⟩ := testBump E a C Set.univ hC isOpen_univ (Set.subset_univ _)
  obtain ⟨w, hw, ew⟩ := orbSm E a u hu
  have hZ : IsClosed ((latticeGL E a : Set (GA E a)) * C) :=
    by
      set_option synthInstance.maxHeartbeats 200000 in
        exact IsClosed.mul_right_of_isCompact Subgroup.isClosed_of_discrete hC
  have hwZ : ∀ g ∈ (latticeGL E a : Set (GA E a)) * C, w.1 g ≠ 0 := by
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    rw [ew]
    refine orb_ne _ u.1 hu.1 hp _ γ⁻¹ (inv_mem hγ) ?_
    rw [inv_mul_cancel_left]
    exact hne c hc
  have hφZ : ∀ g ∉ (latticeGL E a : Set (GA E a)) * C, φ.1 g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨γ, hγ, hc⟩ := hs g h
    exact hg ⟨γ⁻¹, inv_mem hγ, γ * g, hc, inv_mul_cancel_left γ g⟩
  have hq := (smDiv E a φ u w).2 _ hZ hφZ hwZ
  have hf := (smDiv E a ⟨_, hq⟩ u w).1
  refine ⟨⟨_, hf⟩, ⟨HasCompactSupport.mul_left hu.1, ?_⟩, ?_⟩
  · rw [lev_iff]
    refine Subgroup.isOpen_mono
      (H₁ := stab (finGL E a) φ.1 ⊓ (stab (finGL E a) w.1 ⊓ stab (finGL E a) u.1)) ?_ ?_
    · rintro k ⟨h1, h2, h3⟩ g
      show φ.1 _ / w.1 _ * u.1 _ = φ.1 _ / w.1 _ * u.1 _
      rw [h1 g, h2 g, h3 g]
    · exact ((lev_iff φ).1 hφ).inter (((lev_iff w).1 hw).inter ((lev_iff u).1 hu.2))
  · funext g
    have hwL : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) w.1 := ew ▸ GlobalTheory.AutomorphicL2Unitary.leftInv_orbitSum u.1
    have e : GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) (fun g => φ.1 g / w.1 g * u.1 g) g = φ.1 g / w.1 g * w.1 g := by
      conv_rhs => rw [congrFun ew g]
      rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, GlobalTheory.AutomorphicL2Unitary.orbitSum, ← tsum_mul_left]
      refine tsum_congr fun γ => ?_
      rw [hL γ γ.2, hwL γ γ.2, congrFun ew g, GlobalTheory.AutomorphicL2Unitary.orbitSum]
    refine Eq.trans ?_ e.symm
    by_cases h : g ∈ (latticeGL E a : Set (GA E a)) * C
    · rw [div_mul_cancel₀ _ (hwZ g h)]
    · rw [hφZ g h, zero_div, zero_mul]
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem hasDerivAt_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f ψ ψ' : G → ℂ) (hf : LocallyIntegrable f μ)
    (h' : Continuous ψ') (hs' : HasCompactSupport ψ')
    (hi : ∀ x, Integrable (fun y => f y * ψ (y⁻¹ * x)) μ) (hi' : ∀ x, Integrable (fun y => f y * ψ' (y⁻¹ * x)) μ)
    (c : ℝ → G) (hc : Continuous c) (c0 : c 0 = 1) (cadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => ψ (g * c t)) (ψ' g) 0) (x : G) :
    HasDerivAt (fun t => ∫ y, f y * ψ (y⁻¹ * (x * c t)) ∂μ) (∫ y, f y * ψ' (y⁻¹ * x) ∂μ) 0 := by
  obtain ⟨M, hM⟩ := h'.bounded_above_of_compact_support hs'
  let K : Set G := (fun p : ℝ × G => x * c p.1 * p.2⁻¹) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport ψ')
  have hK : IsCompact K := (isCompact_Icc.prod hs').image (by fun_prop)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hb : Integrable (K.indicator fun y => ‖f y‖ * M) μ :=
    (integrable_indicator_iff hKm).2 ((hf.integrableOn_isCompact hK).norm.mul_const M)
  have hdt : ∀ g t, HasDerivAt (fun s => ψ (g * c s)) (ψ' (g * c t)) t := fun g t => by
    have h1 : HasDerivAt (fun s => ψ (g * c t * c s)) (ψ' (g * c t)) (t - t) := by
      rw [sub_self]; exact hd _
    have h2 := h1.comp_sub_const t t
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← cadd, add_sub_cancel]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun t y => f y * ψ (y⁻¹ * (x * c t))) (F' := fun t y => f y * ψ' (y⁻¹ * (x * c t)))
    (x₀ := (0 : ℝ)) (s := Set.Icc (-1 : ℝ) 1) (bound := K.indicator fun y => ‖f y‖ * M)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hi _).aestronglyMeasurable) (hi _) (hi' _).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hy]
        have : ψ' (y⁻¹ * (x * c t)) = 0 := by
          by_contra hne
          exact hy ⟨(t, y⁻¹ * (x * c t)), ⟨ht, subset_tsupport _ hne⟩, by simp [mul_assoc]⟩
        simp [this]) hb
    (Eventually.of_forall fun y t _ => by
      simpa only [mul_assoc] using (hdt (y⁻¹ * x) t).const_mul (f y))
  simpa only [c0, mul_one] using key.2

theorem UpperTheory.V.Cj.H.cvLie :
    UpperTheory.V.Cj.H.CvLie := by
  intro E _ _ _ a μ _ _ ψ φ hψ F hφ X
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have t1 := UpperTheory.V.Cj.H.testOps E a ψ
  have hψ' : IsTest (lie E a X ψ) := (t1.2 hψ).1 X
  have k1 : Continuous ψ.1 := (t1.1 hψ.2).1
  have k2 : Continuous (lie E a X ψ).1 := ((UpperTheory.V.Cj.H.testOps E a _).1 hψ'.2).1
  funext x
  have d := hasDerivAt_conv μ (GlobalTheory.AutomorphicL2Unitary.lift (latticeGL E a) F) ψ.1 (lie E a X ψ).1
    ((UpperTheory.V.Cj.H.locInt (GA E a) (latticeGL E a) μ).1 F) k2 hψ'.1
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ ψ.1 k1 hψ.1).1 F)
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ _ k2 hψ'.1).1 F)
    (fun s => infGL E a (c s)) ccont (by rw [c0, map_one]) (fun s t => by rw [cadd, map_mul])
    (fun g => hasDerivAt_curve ψ g c X c0 cder) x
  have d' := hasDerivAt_curve φ x c X c0 cder
  exact d'.unique (d.congr_of_eventuallyEq (Eventually.of_forall fun t => congrFun hφ _))
end
