module

public import GroundTheory.GlobalFields.ComplexMultiplication.Residue
public import GroundTheory.GlobalFields.ComplexMultiplication.RectangleIntegral
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle001
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
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

@[expose] public section

section

open Complex Filter Topology Set
open scoped Interval Real

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

lemma swap_dslope_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) :
    Function.swap dslope w₀ (fun w ↦ G (w + a)) =
      fun w ↦ Function.swap dslope (w₀ + a) G (w + a) := by
  funext w
  show dslope (fun w ↦ G (w + a)) w₀ w = dslope G (w₀ + a) (w + a)
  rcases eq_or_ne w w₀ with rfl | hw
  · rw [dslope_same, dslope_same]
    exact deriv_comp_add_const _ _ _
  · have hw' : w + a ≠ w₀ + a := fun h ↦ hw (add_right_cancel h)
    rw [dslope_of_ne _ hw, dslope_of_ne _ hw', slope_def_field, slope_def_field]
    congr 1
    ring

lemma dslopeIter_comp_add (G : ℂ → ℂ) (a w₀ : ℂ) (k : ℕ) :
    dslopeIter w₀ k (fun w ↦ G (w + a)) = fun w ↦ dslopeIter (w₀ + a) k G (w + a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dslopeIter_succ', ih, swap_dslope_comp_add]
    funext w
    rw [dslopeIter_succ']

theorem residue_comp_add {f : ℂ → ℂ} {a w₀ : ℂ} (hf : MeromorphicAt f (w₀ + a)) :
    residue (fun w ↦ f (w + a)) w₀ = residue f (w₀ + a) := by
  set n := meromorphicShift f (w₀ + a)
  set G : ℂ → ℂ := fun z ↦ (z - (w₀ + a)) ^ (n + 1) * f z with hGdef
  have hG : AnalyticAt ℂ G (w₀ + a) :=
    analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ n)
  have e : (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) = fun w ↦ G (w + a) := by
    funext w
    simp only [hGdef]
    congr 2
    ring
  have hana : AnalyticAt ℂ (fun w ↦ (w - w₀) ^ (n + 1) * f (w + a)) w₀ := by
    rw [e]
    have : AnalyticAt ℂ (fun w ↦ w + a) w₀ := by fun_prop
    exact hG.comp_of_eq this rfl
  rw [residue_eq_dslopeIter hana, e, dslopeIter_comp_add]
  rfl

theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (h : 0 ≤ meromorphicOrderAt f p) : residue f p = 0 := by
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [meromorphicOrderAt_eq_top_iff] at htop
    rw [residue_congr hf htop]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    have hn0 : 0 ≤ n := by rw [← hn] at h; exact_mod_cast h
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
    simp only [smul_eq_mul] at hfg
    lift n to ℕ using hn0
    rw [residue_congr hf hfg]
    apply residue_eq_zero_of_analyticAt
    simp only [zpow_natCast]
    fun_prop

lemma analyticAt_principalPart (f : ℂ → ℂ) {p u : ℂ} (hu : u ≠ p) :
    AnalyticAt ℂ (principalPart f p) u := by
  have h : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ((z - p) ^ k)⁻¹) u := fun k ↦
    ((analyticAt_id.sub analyticAt_const).pow k).inv (pow_ne_zero _ (sub_ne_zero.2 hu))
  have : principalPart f p = fun z ↦ ∑ j ∈ Finset.range (meromorphicShift f p + 1),
      laurentCoeff f p j * ((z - p) ^ (meromorphicShift f p + 1 - j))⁻¹ := rfl
  rw [this]
  exact Finset.analyticAt_fun_sum _ fun j _ ↦ analyticAt_const.mul (h _)

theorem rectIntegral_principalPart (f : ℂ → ℂ) {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectIntegral (principalPart f p) z w = 2 * π * I * residue f p := by
  have hp : p ∉ rectBoundary z w := notMem_rectBoundary_of_mem_Ioo
    ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
    ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hne : ∀ u ∈ rectBoundary z w, u ≠ p := fun u hu h ↦ hp (h ▸ hu)
  have hc : ∀ k : ℕ, ContinuousOn (fun u ↦ ((u - p) ^ k)⁻¹) (rectBoundary z w) := fun k u hu ↦
    ((((continuous_id.sub continuous_const).pow k).continuousAt).inv₀
      (pow_ne_zero _ (sub_ne_zero.2 (hne u hu)))).continuousWithinAt
  set n := meromorphicShift f p
  have e : principalPart f p = fun u ↦ ∑ j ∈ Finset.range (n + 1),
      laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹ := rfl
  rw [e, rectIntegral_finset_sum (Finset.range (n + 1))
    (f := fun j u ↦ laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹)
    (fun j _ ↦ continuousOn_const.mul (hc _))]
  simp_rw [rectIntegral_const_mul]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · rw [Nat.add_sub_cancel_left]
    simp_rw [pow_one]
    rw [rectIntegral_sub_inv h1 h2 h3 h4]
    exact mul_comm _ _
  · intro j hj
    have hj' : j < n := Finset.mem_range.1 hj
    have e2 : (fun u ↦ ((u - p) ^ (n + 1 - j))⁻¹) = fun u ↦ (u - p) ^ (-((n + 1 - j : ℕ) : ℤ)) := by
      funext u
      rw [zpow_neg, zpow_natCast]
    rw [e2, rectIntegral_zpow_sub _ hp, mul_zero]
    omega

theorem rectIntegral_eq_sum_residue {f : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ)
    (hS : ∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)
    (hmero : ∀ p ∈ S, MeromorphicAt f p)
    (hana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], u ∉ S → AnalyticAt ℂ f u) :
    rectIntegral f z w = 2 * π * I * ∑ p ∈ S, residue f p := by
  classical
  set F : ℂ → ℂ := fun u ↦ f u - ∑ q ∈ S, principalPart f q u with hF
  set E : ℂ → ℂ → ℂ := fun p u ↦ regularPart f p u - ∑ q ∈ S.erase p, principalPart f q u
    with hE
  set G : ℂ → ℂ := fun u ↦ if u ∈ S then E u u else F u with hG
  have hFE : ∀ p ∈ S, ∀ u, u ≠ p → F u = E p u := by
    intro p hp u hu
    simp only [hF, hE]
    rw [eq_principalPart_add_regularPart f p hu, ← Finset.add_sum_erase S _ hp]
    ring
  have hEana : ∀ p ∈ S, AnalyticAt ℂ (E p) p := by
    intro p hp
    exact (analyticAt_regularPart (hmero p hp)).sub
      (Finset.analyticAt_fun_sum _ fun q hq ↦
        analyticAt_principalPart f (Finset.ne_of_mem_erase hq).symm)
  have hGana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], AnalyticAt ℂ G u := by
    intro u hu
    by_cases huS : u ∈ S
    · have hnhds : ((S.erase u : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 u :=
        (S.erase u).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine (hEana u huS).congr ?_
      filter_upwards [hnhds] with v hv
      simp only [hG]
      rcases eq_or_ne v u with rfl | hvu
      · simp [huS]
      · have hvS : v ∉ S := fun h ↦ hv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvu, h⟩))
        rw [if_neg hvS, hFE u huS v hvu]
    · have hnhds : ((S : Set ℂ))ᶜ ∈ 𝓝 u :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using huS)
      have hFana : AnalyticAt ℂ F u :=
        (hana u hu huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
          analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))
      refine hFana.congr ?_
      filter_upwards [hnhds] with v hv
      have hvS : v ∉ S := by simpa using hv
      simp only [hG, if_neg hvS]
  have hSb : ∀ p ∈ S, p ∉ rectBoundary z w := fun p hp ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hS p hp
    exact notMem_rectBoundary_of_mem_Ioo
      ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
      ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hbK : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := rectBoundary_subset
  have hG0 : rectIntegral G z w = 0 := by
    apply rectIntegral_eq_zero_of_differentiable_on_off_countable G z w ∅ countable_empty
    · exact fun u hu ↦ (hGana u hu).continuousAt.continuousWithinAt
    · intro u hu
      apply (hGana u _).differentiableAt
      have h' := hu.1
      rw [mem_reProdIm] at h' ⊢
      exact ⟨Ioo_subset_Icc_self h'.1, Ioo_subset_Icc_self h'.2⟩
  have hGF : rectIntegral G z w = rectIntegral F z w := by
    apply rectIntegral_congr
    intro u hu
    have huS : u ∉ S := fun h ↦ hSb u h hu
    simp only [hG, if_neg huS]
  have hPc : ∀ q ∈ S, ContinuousOn (principalPart f q) (rectBoundary z w) := fun q hq u hu ↦
    (analyticAt_principalPart f (fun (h : u = q) ↦ hSb q hq (h ▸ hu))).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (rectBoundary z w) := fun u hu ↦ by
    have huS : u ∉ S := fun h ↦ hSb u h hu
    exact ((hana u (hbK hu) huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
      analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))).continuousAt.continuousWithinAt
  have hsplit : rectIntegral f z w =
      rectIntegral F z w + ∑ q ∈ S, rectIntegral (principalPart f q) z w := by
    rw [← rectIntegral_finset_sum S hPc, ← rectIntegral_add hFc (continuousOn_finsetSum S hPc)]
    congr 1
    funext u
    rw [hF]
    ring
  rw [hsplit, ← hGF, hG0, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hS q hq
  exact rectIntegral_principalPart f h1 h2 h3 h4

end Elliptic
end GroundTheory.Global
end
end

section

namespace GroundTheory.Global

open Polynomial IntermediateField

section General

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]


omit [IsAlgClosed Ω] in
theorem IsTranscendenceBasis.extendScalars_of_isAlgebraic {E : Type*} [Field E] [Algebra F E]
    [Algebra E Ω] [IsScalarTower F E Ω] [Algebra.IsAlgebraic F E] {ι : Type*} {v : ι → Ω}
    (hv : IsTranscendenceBasis F v) : IsTranscendenceBasis E v := by
  refine (hv.1.extendScalars E).isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun z => ?_⟩
  have le : Algebra.adjoin F (Set.range v) ≤ (Algebra.adjoin E (Set.range v)).restrictScalars F :=
    Algebra.adjoin_le fun z hz => (Subalgebra.mem_restrictScalars _).mpr (Algebra.subset_adjoin hz)
  exact (hv.isAlgebraic.isAlgebraic z).tower_top_of_subalgebra_le le

theorem exists_algEquiv_apply_eq_of_transcendental {x y : Ω} (hx : Transcendental F x)
    (hy : Transcendental F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  classical
  have ind : ∀ z : Ω, Transcendental F z → AlgebraicIndepOn F id ({z} : Set Ω) := fun z hz =>
    (algebraicIndependent_singleton_iff (⟨z, rfl⟩ : ({z} : Set Ω))).mpr hz
  obtain ⟨t₁, hxt, ht₁⟩ := exists_isTranscendenceBasis_superset (ind x hx)
  obtain ⟨t₂, hyt, ht₂⟩ := exists_isTranscendenceBasis_superset (ind y hy)
  have hx₁ : x ∈ t₁ := Set.singleton_subset_iff.mp hxt
  have hy₂ : y ∈ t₂ := Set.singleton_subset_iff.mp hyt
  obtain ⟨f⟩ := Cardinal.eq.1 (ht₁.cardinalMk_eq_trdeg.trans ht₂.cardinalMk_eq_trdeg.symm)
  let φ : t₁ ≃ t₂ := f.trans (Equiv.swap (f ⟨x, hx₁⟩) ⟨y, hy₂⟩)
  obtain ⟨σ, hσF, hσv⟩ :=
    exists_ringEquiv_extend_of_isTranscendenceBasis (RingEquiv.refl F) ht₁ ht₂ φ
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => hσF a, ?_⟩
  have := hσv ⟨x, hx₁⟩
  simp only [φ, Equiv.trans_apply, Equiv.swap_apply_left] at this
  exact this

theorem exists_algEquiv_apply_eq_of_minpoly_eq {x y : Ω} (hx : IsAlgebraic F x)
    (h : minpoly F x = minpoly F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  have hy : IsAlgebraic F y := ⟨minpoly F x, minpoly.ne_zero hx.isIntegral, h ▸ minpoly.aeval _ _⟩
  have := isAlgebraic_adjoin_simple hx.isIntegral
  have := isAlgebraic_adjoin_simple hy.isIntegral
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  obtain ⟨σ, hσ, -⟩ := exists_ringEquiv_extend_of_isTranscendenceBasis
    (minpoly.algEquiv hx h).toRingEquiv
    (IsTranscendenceBasis.extendScalars_of_isAlgebraic (E := F⟮x⟯) hs)
    (IsTranscendenceBasis.extendScalars_of_isAlgebraic (E := F⟮y⟯) hs) (Equiv.refl s)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => ?_, ?_⟩
  · have h1 := hσ (algebraMap F F⟮x⟯ a)
    rw [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes] at h1
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  · have := hσ (AdjoinSimple.gen F x)
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_apply] at this
    simpa using this

theorem mem_bot_iff_forall_algEquiv_apply_eq [PerfectField F] {x : Ω} :
    x ∈ (⊥ : IntermediateField F Ω) ↔ ∀ σ : Ω ≃ₐ[F] Ω, σ x = x := by
  refine ⟨fun hx σ => ?_, fun h => ?_⟩
  · obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact σ.commutes a
  by_contra hx
  by_cases halg : IsAlgebraic F x
  · have hsep : IsSeparable F x :=
      PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)
    have hx' : x ∉ (⊥ : Subalgebra F Ω) := by
      rwa [Algebra.mem_bot, ← IntermediateField.mem_bot]
    obtain ⟨y, hne, hy⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot hsep (IsAlgClosed.splits _)).mp hx'
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq halg hy
    exact hne (hσ ▸ h σ).symm
  · have htr : Transcendental F x := halg
    have htr' : Transcendental F (x + 1) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub isIntegral_one).isAlgebraic)
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_transcendental htr htr'
    have := hσ.symm.trans (h σ)
    simp at this

variable [CharZero Ω]

theorem infinite_range_apply_of_transcendental {x : Ω} (hx : Transcendental ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Infinite := by
  have hx' : Transcendental ℚ (x + 1) := fun h' =>
    hx (by simpa using (h'.isIntegral.sub isIntegral_one).isAlgebraic)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_transcendental hx hx'
  have hpow : ∀ n : ℕ, (σ ^ n) x = x + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_add (f := _), hσ, map_natCast]
      push_cast; ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => x + n) ?_ fun n =>
    ⟨(σ ^ n).toRingEquiv, hpow n⟩
  intro m n hmn
  exact_mod_cast add_left_cancel hmn


omit [IsAlgClosed Ω] in
theorem finite_range_apply_of_isAlgebraic {x : Ω} (hx : IsAlgebraic ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite := by
  refine ((minpoly ℚ x).rootSet_finite Ω).subset ?_
  rintro _ ⟨σ, rfl⟩
  rw [mem_rootSet]
  refine ⟨minpoly.ne_zero hx.isIntegral, ?_⟩
  have := Polynomial.aeval_algHom_apply (σ : Ω →+* Ω).toRatAlgHom x (minpoly ℚ x)
  rw [minpoly.aeval, map_zero] at this
  simpa using this

theorem finite_range_apply_iff_isAlgebraic {x : Ω} :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite ↔ IsAlgebraic ℚ x :=
  ⟨fun h => by_contra fun hx => infinite_range_apply_of_transcendental hx h,
    finite_range_apply_of_isAlgebraic⟩

end General

theorem Complex.isAlgebraic_of_finite_conjugates {x : ℂ}
    (hx : (Set.range fun σ : ℂ ≃+* ℂ => σ x).Finite) : IsAlgebraic ℚ x :=
  finite_range_apply_iff_isAlgebraic.mp hx

end GroundTheory.Global
end
