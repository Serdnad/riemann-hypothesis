module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle021
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle026
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

namespace GlobalTheory

open Finset

local notation "MultilinearMap " R:arg M:arg N:arg => _root_.MultilinearMap (RingHom.id R) M N

theorem multilinear_sum_eq_of_prod_fun_eq
    {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : MultilinearMap ℂ (fun l => V l) ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l) :
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) =
        a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  classical
  intro h
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ V l) ∧
      ∀ u ∈ (a.support.image (fun c => (f c l : X l → ℂ)) ∪
        a.support.image (fun c => (g c l : X l → ℂ))), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule (V l) _ (by
      intro u hu
      simp only [Finset.mem_union, Finset.mem_image] at hu
      rcases hu with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (f c l).2
      · exact (g c l).2)
  choose s E hEV hE using hkey
  let e : ∀ l, X l → V l := fun l x => ⟨E l x, hEV l x⟩
  have expand : ∀ (u : ∀ l, V l),
      (∀ l, (u l : X l → ℂ) = ∑ x ∈ s l, (u l : X l → ℂ) x • E l x) →
      Φ u = ∑ ξ ∈ Fintype.piFinset s, (∏ l, (u l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
    intro u hu
    have hu' : u = fun l => ∑ x ∈ s l, (u l : X l → ℂ) x • e l x := by
      funext l
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hu l
    conv_lhs => rw [hu', MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    simp only [RingHom.id_apply]
  have gen : ∀ f' : κ → ∀ l, V l,
      (∀ c ∈ a.support, ∀ l, (f' c l : X l → ℂ) = ∑ x ∈ s l, (f' c l : X l → ℂ) x • E l x) →
      (a.sum fun c b => b * Φ (f' c)) = ∑ ξ ∈ Fintype.piFinset s,
        (a.sum fun c b => b * ∏ l, (f' c l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
    intro f' hf'
    calc (a.sum fun c b => b * Φ (f' c))
        = ∑ c ∈ a.support, a c * ∑ ξ ∈ Fintype.piFinset s,
            (∏ l, (f' c l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
          unfold Finsupp.sum
          refine Finset.sum_congr rfl fun c hc => ?_
          show a c * Φ (f' c) = _
          rw [expand (f' c) (hf' c hc)]
      _ = _ := by
          simp only [Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun c _ => ?_
          ring
  rw [gen f (fun c hc l => hE l _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))),
    gen g (fun c hc l => hE l _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)))]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [h ξ]

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

open MeasureTheory in
open scoped Pointwise in
private lemma exists_norm_le_of_continuous_periodic_compact_cover {G : Type} [AddCommGroup G] [TopologicalSpace G]
    (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {Φ : G → ℂ} (hΦ : Continuous Φ) (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
  refine ⟨M, fun x => ?_⟩
  obtain ⟨γ, hγ, hx⟩ := hcov x
  rw [← hper γ hγ x]
  exact hM ⟨_, hx, rfl⟩


open MeasureTheory in
open scoped Pointwise in
theorem _root_.GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ χ : G → ℂ, Continuous χ → (∀ x y, χ (x + y) = χ x * χ y) → (∀ x, ‖χ x‖ = 1) → (∀ γ ∈ Γ, χ γ = 1) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ z, (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ z = ∫ y in 𝓕, Φ (z + y) * starRingEnd ℂ (χ y) ∂μ) ∧ ∀ (L : ℝ →+ G) (Φ' : G → ℂ), Continuous Φ' → (∀ γ ∈ Γ, ∀ x, Φ' (γ + x) = Φ' x) → (∀ x, HasDerivAt (fun t : ℝ => Φ (x + L t)) (Φ' x) 0) → ∀ x, HasDerivAt (fun t : ℝ => (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ (x + L t)) ((∫ y in 𝓕, Φ' y * starRingEnd ℂ (χ y) ∂μ) * χ x) 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ 𝓕 hμ h𝓕 χ hχ hmul hnorm hχΓ Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hcc : ∀ x, starRingEnd ℂ (χ x) * χ x = 1 := by
    intro x
    rw [Complex.conj_mul', hnorm x]
    simp
  have conv : ∀ Ψ : G → ℂ, (∀ γ ∈ Γ, ∀ x, Ψ (γ + x) = Ψ x) → ∀ z,
      (∫ y in 𝓕, Ψ y * starRingEnd ℂ (χ y) ∂μ) * χ z = ∫ y in 𝓕, Ψ (z + y) * starRingEnd ℂ (χ y) ∂μ := by
    intro Ψ hΨ z
    set g : G → ℂ := fun y => Ψ y * starRingEnd ℂ (χ y) with hg
    have hgper : ∀ (γ : Γ) (y : G), g (γ +ᵥ y) = g y := by
      intro γ y
      simp only [hg, AddSubgroup.vadd_def, vadd_eq_add, hmul, map_mul, hχΓ γ γ.2, map_one, one_mul,
        hΨ γ γ.2]
    have hpt : ∀ y, Ψ (z + y) * starRingEnd ℂ (χ y) = g (z + y) * χ z := by
      intro y
      simp only [hg, hmul, map_mul]
      linear_combination -(Ψ (z + y) * starRingEnd ℂ (χ y)) * hcc z
    have hS : IsAddFundamentalDomain Γ ((fun y => -z + y) ⁻¹' 𝓕) μ := by
      have hset : (fun y => -z + y) ⁻¹' 𝓕 = z +ᵥ 𝓕 := by
        ext y
        simp only [Set.mem_preimage, Set.mem_vadd_set, vadd_eq_add]
        constructor
        · intro h
          exact ⟨_, h, add_neg_cancel_left z y⟩
        · rintro ⟨w, hw, rfl⟩
          simpa using hw
      rw [hset]
      exact h𝓕.vadd_of_comm z
    have hpre : (fun y => z + y) ⁻¹' ((fun y => -z + y) ⁻¹' 𝓕) = 𝓕 := by
      ext y; simp
    calc (∫ y in 𝓕, g y ∂μ) * χ z
        = (∫ y in (fun y => -z + y) ⁻¹' 𝓕, g y ∂μ) * χ z := by rw [h𝓕.setIntegral_eq hS hgper]
      _ = (∫ y in 𝓕, g (z + y) ∂μ) * χ z := by
          rw [← (measurePreserving_add_left μ z).setIntegral_preimage_emb
            (measurableEmbedding_addLeft z), hpre]
      _ = ∫ y in 𝓕, g (z + y) * χ z ∂μ := (integral_mul_const _ _).symm
      _ = ∫ y in 𝓕, Ψ (z + y) * starRingEnd ℂ (χ y) ∂μ := by simp_rw [hpt]
  refine ⟨conv Φ hper, ?_⟩
  intro L Φ' hΦ' hper' hderiv x
  obtain ⟨M, hM⟩ := exists_norm_le_of_continuous_periodic_compact_cover Γ hK hcov hΦ hper
  obtain ⟨M', hM'⟩ := exists_norm_le_of_continuous_periodic_compact_cover Γ hK hcov hΦ' hper'
  have hfin : μ 𝓕 < ⊤ := _root_.GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne
  have hfun : (fun t : ℝ => (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ (x + L t)) =
      fun t : ℝ => ∫ y in 𝓕, Φ (x + L t + y) * starRingEnd ℂ (χ y) ∂μ := by
    funext t; exact conv Φ hper (x + L t)
  rw [hfun, conv Φ' hper' x]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ)
    (F := fun (t : ℝ) y => Φ (x + L t + y) * starRingEnd ℂ (χ y))
    (F' := fun (t : ℝ) y => Φ' (x + L t + y) * starRingEnd ℂ (χ y)) (x₀ := 0) (s := Set.univ)
    (bound := fun _ => M') Filter.univ_mem
    (Filter.Eventually.of_forall fun t => by fun_prop)
    (Integrable.of_bound (by fun_prop) M (Filter.Eventually.of_forall fun y => by
      simp [hnorm, hM]))
    (by fun_prop)
    (Filter.Eventually.of_forall fun y t _ => by simp [hnorm, hM'])
    (integrable_const _)
    (Filter.Eventually.of_forall fun y t _ => by
      have h := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hderiv (x + L t + y))
      have h' : HasDerivAt (fun s : ℝ => Φ (x + L s + y)) (Φ' (x + L t + y)) t := by
        have e : (fun s : ℝ => Φ (x + L s + y)) = fun s : ℝ => Φ (x + L t + y + L (s - t)) := by
          funext s
          congr 1
          rw [show L s = L t + L (s - t) by rw [← map_add (f := _)]; congr 1; ring]
          abel
        rw [e]
        exact h
      exact h'.mul_const _)
  simpa using key.2

end GlobalTheory
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff

namespace GlobalTheory

theorem conj_apply_conj_of_entire (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z)
    (h : ∀ s : ℂ, 1 < s.re → starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s) (s : ℂ) :
    starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
  have hZ' : Differentiable ℂ (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) := by
    intro s
    have := (hZ (starRingEnd ℂ s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hev : (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) =ᶠ[nhds (2 : ℂ)] Z := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
    exact h s hs
  have := AnalyticOnNhd.eq_of_eventuallyEq
    (hZ'.differentiableOn.analyticOnNhd isOpen_univ)
    (hZ.differentiableOn.analyticOnNhd isOpen_univ) hev
  exact congrFun this s

theorem zetaEulerProduct_ne_zero_one_add_mul_I : ∀ (ι : Type) (N : ι → ℕ), (∀ i, 2 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z : ℂ → ℂ, Differentiable ℂ Z → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → ∀ t : ℝ, t ≠ 0 → Z (1 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro ι N hN hsum hne Z hZ hZs t ht ha
  obtain ⟨i₀⟩ := hne
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hN0 : ∀ i, ((N i : ℕ) : ℂ) ≠ 0 := fun i => by exact_mod_cast (hpos i).ne'
  have hconj : ∀ s, starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
    refine conj_apply_conj_of_entire Z hZ fun s hs => ?_
    have hs' : 1 < (starRingEnd ℂ s).re := by simpa using hs
    rw [hZs _ hs', hZs s hs, map_mul, map_sub, Complex.conj_conj, map_one, ← Complex.exp_conj,
      Complex.conj_tsum]
    simp only [conj_neg_log_euler_factor _ (hN _) 1 (by simp) s hs, map_one]
  set u : ℂ := (t : ℂ) * Complex.I with hu
  have hu0 : u ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have hure : u.re = 0 := by simp [hu]
  have huc : starRingEnd ℂ u = -u := by simp [hu]
  have hb : Z (1 - u) = 0 := by
    rw [← hconj, map_sub, map_one, huc, sub_neg_eq_add, ha, map_zero]
  have hds : ∀ (f : ℂ → ℂ) (a : ℂ), Differentiable ℂ f → Differentiable ℂ (dslope f a) := by
    intro f a hf
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hf.differentiableOn
  have hmul : ∀ (f : ℂ → ℂ) (a : ℂ), f a = 0 → ∀ s, (s - a) * dslope f a s = f s := by
    intro f a h0 s
    have := sub_smul_dslope f a s
    rw [smul_eq_mul, h0, sub_zero] at this
    exact this
  have hD1 := hds Z (1 + u) hZ
  have hD2 := hds Z (1 - u) hZ
  have hG := hds _ (1 - u) hD1
  have hD1b : dslope Z (1 + u) (1 - u) = 0 := by
    have := hmul Z (1 + u) ha (1 - u)
    rw [hb, mul_eq_zero] at this
    refine this.resolve_left fun h => hu0 ?_
    linear_combination (-1 / 2 : ℂ) * h
  set c : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-u) with hcdef
  have hc : ∀ i, ‖c i‖ ≤ 1 := fun i => by
    simp only [hcdef]
    rw [Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re, hure]
    simp
  have hcc : ∀ i, starRingEnd ℂ (c i) = ((N i : ℕ) : ℂ) ^ u := fun i => by
    have harg' : ((N i : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj ((N i : ℕ) : ℂ) (-u) harg'
    rw [map_neg, huc, neg_neg, map_natCast] at this
    exact this.symm
  have key := GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s * dslope (dslope Z (1 + u)) (1 - u) s * dslope Z (1 + u) (s + u) *
      dslope Z (1 - u) (s - u))
    (fun p => by
      have hw : ‖c p.1 ^ (p.2 + 1)‖ ≤ 1 := by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc _)
      have h1 := Complex.abs_re_le_norm (c p.1 ^ (p.2 + 1))
      have h2 := neg_abs_le (c p.1 ^ (p.2 + 1)).re
      apply div_nonneg (by linarith) (by positivity))
    (fun p => mul_nonneg (by positivity) (Real.log_natCast_nonneg _))
    (((hZ.mul hG).mul (hD1.comp (differentiable_id.add_const u))).mul
      (hD2.comp (differentiable_id.sub_const u)))
    (fun s hs => by
      refine ⟨_, GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have e1 : ∀ i, c i * ((N i : ℕ) : ℂ) ^ (-s) = 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)) := by
        intro i
        simp only [hcdef]
        rw [one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      have e2 : ∀ i, starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s) =
          1 * ((N i : ℕ) : ℂ) ^ (-(s - u)) := by
        intro i
        rw [hcc, one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      simp only [e1, e2]
      rw [Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      have h0 := hZs s hs
      have h1 := hZs (s + u) (by simpa [hure] using hs)
      have h2 := hZs (s - u) (by simpa [hure] using hs)
      have g0 := hmul Z (1 + u) ha s
      have g0' := hmul _ (1 - u) hD1b s
      have g1 := hmul Z (1 + u) ha (s + u)
      have g2 := hmul Z (1 - u) hb (s - u)
      have n1 : s - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp at this; linarith
      have n2 : s - (1 + u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      have n3 : s - (1 - u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) = E at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)))) = E1 at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s - u)))) = E2 at *
      generalize dslope (dslope Z (1 + u)) (1 - u) s = G at *
      generalize dslope Z (1 + u) (s + u) = A at *
      generalize dslope Z (1 - u) (s - u) = B at *
      have k0 : (s - (1 + u)) * (s - (1 - u)) * G = (s - 1) * E := by
        rw [← h0, ← g0, ← g0']; ring
      have k1 : (s - 1) * A = (s - (1 - u)) * E1 := by
        linear_combination g1 + h1
      have k2 : (s - 1) * B = (s - (1 + u)) * E2 := by
        linear_combination g2 + h2
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) n3)
      rw [h0]
      calc (s - 1) * (s - (1 + u)) * (s - (1 - u)) * ((s - 1) * E * G * A * B)
          = E * ((s - (1 + u)) * (s - (1 - u)) * G) * ((s - 1) * A) * ((s - 1) * B) := by ring
        _ = _ := by rw [k0, k1, k2]; ring)
  exact not_summable_two_add_two_re_pow_div (c i₀) (hc i₀) (key.prod_factor i₀)

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem rightConv_eq_smul_of_inner_translates : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ {H : Subgroup G} (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → (∀ γ ∈ Γ, ∀ x, φ (γ * x) = φ x) → ∀ c : ℂ, (∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = c * ∫ x in 𝓕, star (φ (x * (h' : G))) * φ x ∂μ) → ∀ x, ∫ h, α h * φ (x * (h : G)) ∂m = c * φ x := by
  intro G _ _ _ _ _ _ Γ _ μ _ 𝓕 hF hμ H m _ α hα φ hφ B hB hinv c hc
  set Φ : G → ℂ := fun x => ∫ h, α h * φ (x * (h : G)) ∂m with hΦdef

  have intOn : ∀ f : G → ℂ, Continuous f → ∀ C : ℝ, (∀ g, ‖f g‖ ≤ C) → IntegrableOn f 𝓕 μ :=
    fun f hf C hC => Measure.integrableOn_of_bounded hμ.ne hf.aestronglyMeasurable (ae_of_all _ hC)
  have hΦc : Continuous Φ := GlobalTheory.T.continuous_right_convolution_bounded_integrable m α hα φ hφ B hB
  set K : ℝ := ∫ h, ‖α h‖ * B ∂m
  have hΦb : ∀ x, ‖Φ x‖ ≤ K := by
    intro x
    refine norm_integral_le_of_norm_le (hα.norm.mul_const B) (ae_of_all _ fun h => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  set D : G → ℂ := fun x => Φ x - c * φ x with hDdef
  have hDc : Continuous D := hΦc.sub (continuous_const.mul hφ)
  have hDb : ∀ x, ‖D x‖ ≤ K + ‖c‖ * B := by
    intro x
    refine (norm_sub_le _ _).trans (add_le_add (hΦb x) ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  have hsφc : Continuous (fun x => star (φ x)) := hφ.star
  have hsφb : ∀ x, ‖star (φ x)‖ ≤ B := fun x => by rw [norm_star]; exact hB x

  have h1 : ∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * D x ∂μ = 0 := by
    intro h'
    have hc1 : Continuous (fun x => star (φ (x * (h' : G)))) :=
      hsφc.comp (continuous_id.mul continuous_const)
    have hb1 : ∀ x, ‖star (φ (x * (h' : G)))‖ ≤ B := fun x => hsφb _
    have i1 : IntegrableOn (fun x => star (φ (x * (h' : G))) * Φ x) 𝓕 μ :=
      intOn _ (hc1.mul hΦc) (B * K) fun x => by
        rw [norm_mul]; exact mul_le_mul (hb1 x) (hΦb x) (norm_nonneg _) ((norm_nonneg _).trans (hB 1))
    have i2 : IntegrableOn (fun x => star (φ (x * (h' : G))) * (c * φ x)) 𝓕 μ :=
      intOn _ (hc1.mul (continuous_const.mul hφ)) (B * (‖c‖ * B)) fun x => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (hb1 x) (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)) (by positivity) ((norm_nonneg _).trans (hB 1))
    have : (fun x => star (φ (x * (h' : G))) * D x) = fun x => star (φ (x * (h' : G))) * Φ x - star (φ (x * (h' : G))) * (c * φ x) := by
      funext x; simp only [hDdef]; ring
    rw [this, integral_sub i1 i2, hc h']
    have : (fun x => star (φ (x * (h' : G))) * (c * φ x)) = fun x => c * (star (φ (x * (h' : G))) * φ x) := by
      funext x; ring
    rw [this, integral_const_mul]
    simp [Φ]

  have hsα : Integrable (fun h => star (α h)) m := by
    simpa using Complex.conjCLE.toContinuousLinearMap.integrable_comp hα
  have F := GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded (H := H) μ 𝓕 hμ m (fun h => star (α h)) hsα D (fun x => star (φ x)) hDc hsφc
    (K + ‖c‖ * B) B hDb hsφb
  have hstarΦ : ∀ x, star (Φ x) = ∫ h, star (α h) * star (φ (x * (h : G))) ∂m := by
    intro x
    simp only [Φ, ← starRingEnd_apply, ← integral_conj, map_mul]
  have h3 : ∫ x in 𝓕, D x * star (Φ x) ∂μ = 0 := by
    simp_rw [hstarΦ]
    rw [F.2.2]
    refine integral_eq_zero_of_ae (ae_of_all _ fun h => ?_)
    have := h1 h
    have e : (fun x => D x * star (φ (x * (h : G)))) = fun x => star (φ (x * (h : G))) * D x := by
      funext x; ring
    simp only [Pi.zero_apply, e, this, mul_zero]

  have h4 : ∫ x in 𝓕, D x * star (φ x) ∂μ = 0 := by
    have := h1 1
    simp only [OneMemClass.coe_one, mul_one] at this
    rw [← this]; congr 1; funext x; ring

  have iDΦ : IntegrableOn (fun x => D x * star (Φ x)) 𝓕 μ :=
    intOn _ (hDc.mul hΦc.star) ((K + ‖c‖ * B) * K) fun x => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (hDb x) (hΦb x) (norm_nonneg _) ((norm_nonneg _).trans (hDb x))
  have iDφ : IntegrableOn (fun x => star c * (D x * star (φ x))) 𝓕 μ :=
    intOn _ (continuous_const.mul (hDc.mul hsφc)) (‖c‖ * ((K + ‖c‖ * B) * B)) fun x => by
      rw [norm_mul, norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hDb x) (hsφb x) (norm_nonneg _) ((norm_nonneg _).trans (hDb x))) (norm_nonneg _)
  have h5 : ∫ x in 𝓕, ((‖D x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
    have e : (fun x => ((‖D x‖ ^ 2 : ℝ) : ℂ)) = fun x => D x * star (Φ x) - star c * (D x * star (φ x)) := by
      funext x
      rw [Complex.ofReal_pow, ← Complex.mul_conj', starRingEnd_apply]
      simp only [hDdef, star_sub, star_mul']
      ring
    rw [e, integral_sub iDΦ iDφ, integral_const_mul, h3, h4, mul_zero, sub_zero]
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h5
  have indexDSecond : IntegrableOn (fun x => ‖D x‖ ^ 2) 𝓕 μ :=
    Measure.integrableOn_of_bounded hμ.ne (hDc.norm.pow 2).aestronglyMeasurable
      (M := (K + ‖c‖ * B) ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hDb x) 2)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => by positivity) indexDSecond).1 h5
  have hae' : ∀ᵐ x ∂(μ.restrict 𝓕), D x = 0 := hae.mono fun x hx => by
    simpa using hx

  have hDinv : ∀ γ ∈ Γ, ∀ x, D (γ * x) = D x := by
    intro γ hγ x
    simp only [hDdef, Φ, mul_assoc, hinv γ hγ]
  have := GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain Γ μ 𝓕 hF D hDc hDinv hae'
  intro x
  exact sub_eq_zero.1 (this x)

end GlobalTheory
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) → ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  first | exact @GlobalTheory.matrix_oneParamGroup_eq_exp | exact GlobalTheory.matrix_oneParamGroup_eq_exp | (intros; apply GlobalTheory.matrix_oneParamGroup_eq_exp <;> assumption)
end
