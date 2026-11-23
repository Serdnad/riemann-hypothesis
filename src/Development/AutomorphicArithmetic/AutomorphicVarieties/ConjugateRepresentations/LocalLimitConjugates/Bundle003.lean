module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle002
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

theorem UpperTheory.V.Cj.H.approx :
    UpperTheory.V.Cj.H.Approx := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F hF
  by_contra hF0
  have hpos : 0 < ‖F‖ := norm_pos_iff.mpr hF0
  have hcont := GlobalTheory.AutomorphicL2Unitary.continuous_R (Γ := Γ) (μ := μ) F
  obtain ⟨f, hfc, hfs, hfr, hf1, hfW, hfF⟩ :=
    hF {g | ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2} (by
      apply (isOpen_lt (continuous_norm.comp (hcont.sub continuous_const))
        continuous_const).mem_nhds
      show ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ 1 F - F‖ < ‖F‖ / 2
      rw [map_one, ContinuousLinearMap.one_apply, sub_self, norm_zero]
      positivity)
  have hfre : ∀ y, f y = ((f y).re : ℂ) := by
    intro y
    obtain ⟨t, _, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
  have hfnn : ∀ y, 0 ≤ (f y).re := by
    intro y
    obtain ⟨t, ht0, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
    exact ht0
  have hint : MeasureTheory.Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hrep := (GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hint) F
  have hφ := hrep.1
  have hzero : ∫ g, f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F ∂μ = 0 := hrep.2.symm.trans hfF
  have hI : ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ = 0 := by
    rw [integral_re (hφ.const_inner F), integral_inner hφ F, hzero, inner_zero_right]
    simp
  have hbound : ∀ g, ‖F‖ ^ 2 / 2 * (f g).re
      ≤ RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) := by
    intro g
    have hre : RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F))
        = (f g).re * (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
      rw [inner_smul_right]
      conv_lhs => rw [hfre g]
      simp
    rw [hre]
    by_cases hg : ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2
    · have e1 : inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
          = inner ℂ F F - inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F) := by
        rw [inner_sub_right]
        ring
      have e2 : (inner ℂ F F).re = ‖F‖ ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) F
      have e3 := re_inner_le_norm (𝕜 := ℂ) F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
      rw [norm_sub_rev] at e3
      have e4 : ‖F‖ ^ 2 / 2 ≤ (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
        rw [e1, Complex.sub_re, e2]
        have e3' : (inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re ≤ ‖F‖ * (‖F‖ / 2) := by
          simp only [RCLike.re_to_complex] at e3
          exact e3.trans (mul_le_mul_of_nonneg_left hg.le (norm_nonneg F))
        nlinarith
      have h5 := mul_le_mul_of_nonneg_left e4 (hfnn g)
      linarith
    · have h0 : f g = 0 := hfW g hg
      rw [h0]
      simp
  have hpos2 : 0 < ∫ g, (f g).re ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hfc) (hfs.comp_left Complex.zero_re) (fun y => hfnn y)
      (by
        intro h
        apply hf1
        rw [hfre 1, h, Complex.ofReal_zero])
  have hmono : ∫ g, ‖F‖ ^ 2 / 2 * (f g).re ∂μ
      ≤ ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ :=
    MeasureTheory.integral_mono (hint.re.const_mul _) ((hφ.const_inner F).re) hbound
  rw [hI, MeasureTheory.integral_const_mul] at hmono
  have h6 : 0 < ‖F‖ ^ 2 / 2 * ∫ g, (f g).re ∂μ := mul_pos (by positivity) hpos2
  linarith
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem inf_cont (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ ((continuous_const.sub continuous_const).add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem val_nhds (E : Type) [Field E] [NumberField E] (a : ℕ) (y : GL (Fin a) (Cinf E))
    {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 y) : (fun z : GL (Fin a) (Cinf E) => toL z.val) '' N ∈ 𝓝 (toL y.val) :=
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

open scoped Pointwise in
private theorem loc_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (x : G) :
    ∃ s : Finset Γ, ∀ᶠ z in 𝓝 x, GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f z = ∑ γ ∈ s, f (γ * z) := by
  obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
  have hS : {γ : Γ | (γ : G) ∈ tsupport f * K⁻¹}.Finite := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (hf.isCompact.mul hK.inv)
  refine ⟨hS.toFinset, Filter.mem_of_superset hx fun z hz => tsum_eq_sum fun γ hγ => ?_⟩
  by_contra h
  exact hγ (hS.mem_toFinset.2 ⟨_, subset_tsupport f h, z⁻¹, Set.inv_mem_inv.2 hz, by simp⟩)

theorem UpperTheory.V.Cj.H.orbSm :
    UpperTheory.V.Cj.H.OrbSm := by
  intro E _ _ _ a u hu
  have hm : GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) u.1 ∈ Sm E a := by
    intro g x hx
    obtain ⟨y, hy⟩ := hx
    obtain rfl : x = toL y.val := hy.symm
    obtain ⟨s, hs⟩ := loc_fin (latticeGL E a) hu.1 (g * infGL E a y)
    have hc : Continuous fun z => g * infGL E a z := continuous_const.mul (inf_cont E a)
    have h1 := val_nhds E a y (hc.continuousAt.preimage_mem_nhds hs)
    refine ((ContDiffAt.sum (s := s) fun γ _ =>
      contDiffAt_chart u.2 (γ.1 * g) (val_mem_invSet y)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [h1]
    rintro _ ⟨z, hz, rfl⟩
    simp only [chart_val, mul_assoc]
    exact hz
  refine ⟨⟨_, hm⟩, ?_, rfl⟩
  have key : ∀ k, act (.fin k) u = u → act (.fin k) (⟨_, hm⟩ : Sm E a) = ⟨_, hm⟩ := fun k hk =>
    Subtype.ext (funext fun g => tsum_congr fun γ => by
      have h : u.1 (γ.1 * g * finGL E a k) = u.1 (γ.1 * g) := congrFun (congrArg Subtype.val hk) _
      rw [← h, mul_assoc])
  let S : ∀ φ : Sm E a, Subgroup (GL (Fin a) (Af E)) := fun φ =>
    { carrier := {k | act (.fin k) φ = φ}
      one_mem' := Subtype.ext (funext fun g => by
        change φ.1 (g * finGL E a 1) = φ.1 g
        rw [map_one, mul_one])
      mul_mem' := fun {k l} hk hl => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k) = φ.1 g := congrFun (congrArg Subtype.val hk) _
        have h2 : φ.1 (g * finGL E a k * finGL E a l) = φ.1 (g * finGL E a k) := congrFun (congrArg Subtype.val hl) _
        change φ.1 (g * finGL E a (k * l)) = φ.1 g
        rw [map_mul, ← mul_assoc, h2, h1])
      inv_mem' := fun {k} hk => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k⁻¹ * finGL E a k) = φ.1 (g * finGL E a k⁻¹) :=
          congrFun (congrArg Subtype.val hk) _
        change φ.1 (g * finGL E a k⁻¹) = φ.1 g
        rw [← h1, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]) }
  exact Subgroup.isOpen_mono (H₁ := S u) (H₂ := S ⟨_, hm⟩) key hu.2
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneLim :
    UpperTheory.V.Cj.H.ConeLim := by
  intro V F _ _ _ _ Y hY p hp q w hw K hKY hK
  obtain ⟨C, hC⟩ := (hK.image (continuous_id.sub continuous_const :
    Continuous fun x : V => x - p)).isBounded.exists_norm_le
  set K' : Set V := (fun z : ℝ × V => p + z.1 • (z.2 - p)) '' (Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hK'c : IsCompact K' := (isCompact_Icc.prod hK).image (by fun_prop)
  have hK'Y : K' ⊆ Y := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact hY.add_smul_sub_mem hp (hKY hx) ht
  have hwK := hw K' hK'Y hK'c
  rw [Metric.tendstoUniformlyOn_iff] at hwK ⊢
  intro ε hε
  have hR : 0 < |C| + 1 := by positivity
  filter_upwards [hwK (ε / 2 / (|C| + 1)) (by positivity)] with k hk x hx
  simp only [Pi.zero_apply, dist_zero_left] at hk ⊢
  have hxp : ‖x - p‖ ≤ |C| + 1 := by
    have h0 := hC (x - p) ⟨x, hx, rfl⟩
    linarith [le_abs_self C]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hy : p + t • (x - p) ∈ K' := ⟨(t, x), ⟨⟨ht.1.le, ht.2⟩, hx⟩, rfl⟩
    have h1 := hk _ hy
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
    have h2 : t ^ q ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have h3 : ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ ‖w k (p + t • (x - p))‖ * ‖x - p‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
      rw [ContinuousAlternatingMap.norm_curryLeft]
    have h4 : ‖w k (p + t • (x - p))‖ * ‖x - p‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) :=
      mul_le_mul h1.le hxp (norm_nonneg _) (by positivity)
    calc t ^ q * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ 1 * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
          rw [one_mul]
          exact h3.trans h4
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have e : ε / 2 / (|C| + 1) * (|C| + 1) = ε / 2 := by field_simp
  rw [e] at hint
  simp only [sub_zero, abs_one, mul_one] at hint
  calc ‖UpperTheory.V.Cj.H.coneOp p (w k) x‖
      = ‖∫ t in (0 : ℝ)..1, t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ := rfl
    _ ≤ ε / 2 := hint
    _ < ε := by linarith
end

section

noncomputable section

open Filter Topology

namespace UpperTheory.V.Cj.H


theorem absSolve : AbsSolve := by
  intro I J L c cn hcn hlim
  classical
  let ψ : (J →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ) := Finsupp.linearCombination ℂ L
  let φ : (J →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c
  have hsum : ∀ (b : I → ℂ) (v : I →₀ ℂ),
      (v.sum fun i x => x * b i) = Finsupp.linearCombination ℂ b v := by
    intro b v
    rw [Finsupp.linearCombination_apply]
    rfl
  have hcomp : ∀ (b : I → ℂ), (Finsupp.linearCombination ℂ b) ∘ₗ ψ
      = Finsupp.linearCombination ℂ (fun j => Finsupp.linearCombination ℂ b (L j)) := by
    intro b
    apply Finsupp.lhom_ext
    intro j x
    simp [ψ, Finsupp.linearCombination_single]
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : ∀ k, Finsupp.linearCombination ℂ (cn k) a = 0 := by
      intro k
      obtain ⟨b, hb⟩ := hcn k
      have h1 := congrArg (fun m => m a) (hcomp b)
      simp only [LinearMap.comp_apply, ha, map_zero] at h1
      rw [show cn k = fun j => Finsupp.linearCombination ℂ b (L j) from
        funext fun j => ((hsum b (L j)).symm.trans (hb j)).symm]
      exact h1.symm
    have hT : Tendsto (fun k => Finsupp.linearCombination ℂ (cn k) a) atTop (𝓝 (φ a)) := by
      simp only [φ, Finsupp.linearCombination_apply, Finsupp.sum]
      apply tendsto_finsetSum
      intro j _
      exact (hlim j).const_smul (a j)
    simp only [h0] at hT
    exact tendsto_nhds_unique hT tendsto_const_nhds
  let f0 : LinearMap.range ψ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker ψ).liftQ φ hker) ∘ₗ
      (ψ.quotKerEquivRange.symm : LinearMap.range ψ →ₗ[ℂ] (J →₀ ℂ) ⧸ LinearMap.ker ψ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgψ : ∀ a, g (ψ a) = φ a := by
    intro a
    have h2 := congrArg (fun m => m ⟨ψ a, LinearMap.mem_range_self ψ a⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [f0, LinearMap.quotKerEquivRange_symm_apply_image]
  have hgb : Finsupp.linearCombination ℂ (fun i => g (Finsupp.single i 1)) = g := by
    apply Finsupp.lhom_ext
    intro i x
    rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
  refine ⟨fun i => g (Finsupp.single i 1), fun j => ?_⟩
  refine (hsum (fun i => g (Finsupp.single i 1)) (L j)).trans ?_
  rw [hgb]
  have h3 := hgψ (Finsupp.single j 1)
  simpa [ψ, φ, Finsupp.linearCombination_single] using h3

end UpperTheory.V.Cj.H
end
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem tendsto_zero_on_closure_of_lipschitz_family {H : Type} [NormedAddCommGroup H] (Q : ℕ → H → H)
    (hQ : ∀ k x y, ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖) (S : Set H)
    (hS : ∀ x ∈ S, Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0)) (x : H)
    (hx : x ∈ closure S) :
    Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hS y hyS) (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [dist_zero_right] at h1 ⊢
  rw [dist_eq_norm] at hxy
  calc ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖ := hQ k x y
    _ < ε / 2 + ε / 2 := add_lt_add h1 hxy
    _ = ε := by ring

theorem UpperTheory.V.Cj.H.absLim :
    UpperTheory.V.Cj.H.AbsLim := by
  intro H _ _ _ D A hA s hs hplus hminus T hT hTb P hP hPr w
  have hc : ∀ k, ‖(Complex.I * (s k : ℂ))‖ = |s k| := by
    intro k
    simp
  have hadj : ∀ k (v' : D), ContinuousLinearMap.adjoint (T k)
      ((A v' : H) - (Complex.I * (s k : ℂ)) • (v' : H)) = (v' : H) := by
    intro k v'
    apply sub_eq_zero.mp
    apply hplus k
    intro v
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hT k v]
    rw [inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right, hA v' v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hPfix : ∀ k, (Complex.I * (s k : ℂ)) • T k (P w) = P w := by
    intro k
    apply sub_eq_zero.mp
    apply hminus k
    intro v
    have h1 : inner ℂ (T k (P w)) ((A v : H) - (Complex.I * (s k : ℂ)) • (v : H))
        = inner ℂ (P w) (v : H) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hadj k v]
    rw [inner_sub_left, inner_smul_left, h1, inner_sub_right, inner_smul_right, hP w v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hr : Filter.Tendsto (fun k => (Complex.I * (s k : ℂ)) • T k (w - P w)) Filter.atTop
      (nhds 0) := by
    refine tendsto_zero_on_closure_of_lipschitz_family (fun k x => (Complex.I * (s k : ℂ)) • T k x) ?_
      (Set.range fun v : D => (A v : H)) ?_ (w - P w) ?_
    · intro k x y
      have e : (Complex.I * (s k : ℂ)) • T k x = (Complex.I * (s k : ℂ)) • T k y
          + (Complex.I * (s k : ℂ)) • T k (x - y) := by
        rw [map_sub, smul_sub]
        abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, hc]
      exact hTb k (x - y)
    · rintro _ ⟨v, rfl⟩
      have e : ∀ k, (Complex.I * (s k : ℂ)) • T k (A v : H) = (Complex.I * (s k : ℂ)) • (v : H)
          - (Complex.I * (s k : ℂ)) • ((Complex.I * (s k : ℂ)) • T k (v : H)) := by
        intro k
        have h := hT k v
        rw [map_add (f := _), map_smul] at h
        rw [eq_sub_iff_add_eq, ← smul_add, h]
      apply squeeze_zero_norm (a := fun k => 2 * |s k| * ‖(v : H)‖)
      · intro k
        rw [e k]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, norm_smul, hc]
        have h2 := mul_le_mul_of_nonneg_left (hTb k (v : H)) (abs_nonneg (s k))
        linarith
      · have h3 : Filter.Tendsto (fun k => |s k|) Filter.atTop (nhds 0) := by
          simpa using hs.abs
        have h4 := (h3.const_mul 2).mul_const ‖(v : H)‖
        rwa [mul_zero, zero_mul] at h4
    · have h := hPr w
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at h
      exact h
  have hsum : ∀ k, (Complex.I * (s k : ℂ)) • T k w
      = P w + (Complex.I * (s k : ℂ)) • T k (w - P w) := by
    intro k
    rw [map_sub, smul_sub, hPfix k]
    abel
  have h5 := (tendsto_const_nhds (x := P w) (f := Filter.atTop)).add hr
  rw [add_zero] at h5
  exact h5.congr (fun k => (hsum k).symm)
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.latCount :
    UpperTheory.V.Cj.H.LatCount := by
  intro E _ _ _ a _ S hS g
  obtain ⟨A, hA⟩ := GlobalTheory.card_latticeGL_conj_le E a
  set c : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g with hc
  set f : GA E a := finGL E a (GeneralLinearGroup.map (pFin E) g) with hf
  obtain ⟨C, hC0, hC⟩ := hA ((fun s => f * s * f⁻¹) '' S) (hS.image (by fun_prop))
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c))
  refine ⟨C * B ^ (2 * A), 2 * A, fun y => ?_⟩
  obtain ⟨hfin, hle⟩ := hC (c * y)
  have hg : g * infGL E a y = infGL E a (c * y) * f := by
    refine ga_ext ?_ ?_
    · simp only [map_mul, hf, pInf_infGL, pInf_finGL, mul_one, hc]
    · simp only [map_mul, hf, pFin_infGL, pFin_finGL, mul_one, one_mul]
  refine ⟨_, hle.trans ?_, ?_⟩
  · have h0 : 0 ≤ GlobalTheory.CuspRep.height (c * y) := zero_le_one.trans (one_le_height _)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hB c rfl y) _) hC0
  · rw [hfin.cast_ncard_eq]
    refine Set.encard_le_encard fun γ hγ => ⟨_, hγ, ?_⟩
    rw [hg]
    group
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.convolution_L2_class :
    UpperTheory.V.Cj.H.ConvolutionL2Class := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs F
  set f : G → ℂ := fun y => ψ y⁻¹ with hfdef
  have hfi : Integrable f μ :=
    (hψ.comp continuous_inv).integrable_of_hasCompactSupport
      (hψs.comp_homeomorph (Homeomorph.inv G))
  have hconv : cv ψ F = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F) := by
    funext x
    show ∫ y, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x) ∂μ = ∫ y, f y * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) (x * y) ∂μ
    rw [← MeasureTheory.integral_mul_left_eq_self
      (fun y => GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) x]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfdef, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact mul_comm _ _
  obtain ⟨-, hae⟩ := GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR G Γ μ f hfi F
  rw [hconv]
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    (GlobalTheory.AutomorphicL2Unitary.leftInv_lift _).convR f
  have hdesc : GlobalTheory.AutomorphicL2Unitary.descend Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F))
      =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] ↑↑(GlobalTheory.AutomorphicL2Unitary.Rop Γ μ f F) := by
    refine GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.2 ?_
    filter_upwards [hae] with g hg
    have hl := congrFun hinv.lift_descend g
    simp only [GlobalTheory.AutomorphicL2Unitary.lift] at hg hl
    rw [hl, hg]
  have hm : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    ⟨hinv, (MeasureTheory.Lp.memLp _).ae_eq hdesc.symm⟩
  exact ⟨hm, GlobalTheory.AutomorphicL2Unitary.l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hm.lift_toL2_ae_eq.trans hae.symm)⟩
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneCpt :
    UpperTheory.V.Cj.H.ConeCpt := by
  intro E _ _ a K hK hKc
  refine ⟨_, (UpperTheory.V.Cj.A.sandCpt E a).2 K hK hKc, fun p hp => ?_⟩
  obtain ⟨g, rfl⟩ := hK hp
  exact ⟨g, hp, rfl⟩
end
