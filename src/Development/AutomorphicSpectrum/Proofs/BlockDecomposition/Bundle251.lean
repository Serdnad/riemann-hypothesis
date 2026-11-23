module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import GroundTheory.AutomorphicForms.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing Pointwise
open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

namespace GlobalTheory.CompanionTheory.EisTestK

theorem nhd_choice {K K₀ : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [Group K₀] [TopologicalSpace K₀] [IsTopologicalGroup K₀] [CompactSpace K₀] [T2Space K₀]
    (j : K →* K₀) (hj : Continuous j) (S : Subgroup K₀) (hS : IsClosed (S : Set K₀))
    (N₁ : Set K₀) (hN : N₁ ∈ 𝓝 (1 : K₀)) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∃ U ∈ 𝓝 (1 : K₀), ∀ (κ : K) (p u : K₀), p ∈ S → u ∈ U → j κ = p * u →
      ∃ r v : K, j r ∈ S ∧ v ∈ V ∧ κ = r * v ∧ ∀ u' ∈ U, j v * u'⁻¹ ∈ N₁ := by
  have hcont : Tendsto (fun x : K₀ × K₀ => x.1 * x.2⁻¹) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1) := by
    have h : Continuous (fun x : K₀ × K₀ => x.1 * x.2⁻¹) := by fun_prop
    have := h.tendsto ((1 : K₀), (1 : K₀))
    simpa [nhds_prod_eq] using this
  obtain ⟨W, hW, hWN⟩ := Filter.mem_prod_self_iff.1 (hcont hN)
  have hjW : j ⁻¹' W ∈ 𝓝 (1 : K) := hj.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨V₀, hV₀sub, hV₀o, h1⟩ := mem_nhds_iff.1 (Filter.inter_mem hV hjW)
  let Q : Subgroup K := S.comap j
  let A : Set K := (Q : Set K) * V₀
  have hAo : IsOpen A := hV₀o.mul_left
  have hC : IsCompact (j '' Aᶜ) := (hAo.isClosed_compl.isCompact).image hj
  have hScpt : IsCompact (S : Set K₀) := hS.isCompact
  let T : Set K₀ := (S : Set K₀) * (j '' Aᶜ)
  have hT : IsCompact T := hScpt.mul hC
  have h1T : (1 : K₀) ∉ T := by
    rintro ⟨p, hp, c, ⟨x, hx, rfl⟩, hpc⟩
    apply hx
    have hjx : j x ∈ S := by
      have : j x = p⁻¹ := eq_inv_of_mul_eq_one_right hpc
      rw [this]; exact S.inv_mem hp
    exact ⟨x, hjx, 1, h1, by simp⟩
  refine ⟨W ∩ Tᶜ, Filter.inter_mem hW (hT.isClosed.isOpen_compl.mem_nhds h1T), ?_⟩
  intro κ p u hp hu hκ
  by_cases hκA : κ ∈ A
  · obtain ⟨r, hr, v, hv, rfl⟩ := hκA
    refine ⟨r, v, hr, (hV₀sub hv).1, rfl, fun u' hu' => ?_⟩
    exact hWN (Set.mk_mem_prod (hV₀sub hv).2 hu'.1)
  · exfalso
    apply hu.2
    refine ⟨p⁻¹, S.inv_mem hp, j κ, ⟨κ, hκA, rfl⟩, ?_⟩
    simp [hκ]

section Concrete

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

theorem dgl_mem_stab (d : ι → IdeleGroup k) (i : ι) : dgl d ∈ stab 𝔸[k] ({i} : Set ι) := by
  intro r hr c hc
  have hrc : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hrc, Matrix.diagonal_apply_ne _ hrc⟩

theorem kap_mem_stab_iff (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    kap π d g ∈ stab 𝔸[k] ({i} : Set ι) ↔ π g ∈ stab 𝔸[k] ({i} : Set ι) := by
  have hD := dgl_mem_stab d i
  constructor
  · intro h
    have e : π g = dgl d * kap π d g * (dgl d)⁻¹ := by simp [kap, mul_assoc]
    rw [e]
    exact mul_mem (mul_mem hD h) (inv_mem hD)
  · intro h
    exact mul_mem (mul_mem (inv_mem hD) h) hD

theorem bdet_congr {R : Type} [CommRing R] {s : Set ι} {g g' : GL ι R}
    (h : (g : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      (g' : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) : bdet s g = bdet s g' := by
  unfold bdet
  split_ifs with h1 h2 h2
  · exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])
  · exact absurd (by rwa [h] at h1) h2
  · exact absurd (by rwa [← h] at h2) h1
  · rfl

theorem bdet_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    bdet ({i} : Set ι) (kap π d g) = bdet ({i} : Set ι) (π g) := by
  apply bdet_congr
  ext ⟨a, ha⟩ ⟨b, hb⟩
  obtain rfl : a = i := ha
  obtain rfl : b = a := hb
  have e : (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) =
      Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) := rfl
  have e' : ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.diagonal fun i => (d i : 𝔸[k]) := rfl
  simp only [Matrix.submatrix_apply, kap, Units.val_mul, e, e', Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_right_comm, Units.inv_mul, one_mul]

end Concrete

theorem testK : StdGood → BdetLaw → TestFun → TestK := by
  intro hStd hB hT G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hSide V hV
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.1 ((hStd k).kcpt ι)
  obtain ⟨hcl, hmul, hcb, -, -, -⟩ := hB k 𝔸[k] (adStd k) (hStd k) ι ({i} : Set ι)
  let j : K →* (adStd k).kGL ι :=
    { toFun := fun κ => ⟨kap π d κ, hSide.piK κ κ.2⟩
      map_one' := by apply Subtype.ext; simp [kap]
      map_mul' := fun a b => by apply Subtype.ext; simp [kap, mul_assoc] }
  have hj : Continuous j := by
    refine Continuous.subtype_mk ?_ _
    unfold kap
    exact (continuous_const.mul (hSide.cont.comp continuous_subtype_val)).mul continuous_const
  let S : Subgroup ((adStd k).kGL ι) := (stab 𝔸[k] ({i} : Set ι)).comap ((adStd k).kGL ι).subtype
  have hS : IsClosed (S : Set ((adStd k).kGL ι)) := hcl.preimage continuous_subtype_val
  have hb1 : bdet ({i} : Set ι) (1 : GL ι 𝔸[k]) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    simpa using this
  let f : (adStd k).kGL ι → ℂ := fun p => (ω.toIdele (bdet ({i} : Set ι) p.1) : ℂ)
  have hf1 : f 1 = 1 := by
    show (ω.toIdele (bdet ({i} : Set ι) (1 : GL ι 𝔸[k])) : ℂ) = 1
    rw [hb1]
    simp [HeckeCharacter.toIdele_apply]
  have hfc : ContinuousOn f (S : Set ((adStd k).kGL ι)) := by
    have h1 : ContinuousOn (fun p : (adStd k).kGL ι => bdet ({i} : Set ι) p.1) (S : Set ((adStd k).kGL ι)) :=
      hcb.comp continuous_subtype_val.continuousOn fun p hp => hp
    exact continuous_subtype_val.comp_continuousOn (ω.continuous_toIdele.comp_continuousOn h1)
  obtain ⟨N₁, hN₁, hNf⟩ : ∃ N₁ ∈ 𝓝 (1 : (adStd k).kGL ι), ∀ p ∈ S, p ∈ N₁ → ‖f p - 1‖ ≤ 1 / 4 := by
    have h := hfc 1 (one_mem S)
    have hm : f ⁻¹' Metric.closedBall 1 (1 / 4) ∈ 𝓝[(S : Set ((adStd k).kGL ι))] (1 : (adStd k).kGL ι) :=
      h (by rw [hf1]; exact Metric.closedBall_mem_nhds _ (by norm_num))
    obtain ⟨u, huo, hu1, hus⟩ := mem_nhdsWithin.1 hm
    refine ⟨u, huo.mem_nhds hu1, fun p hp hpu => ?_⟩
    have := hus ⟨hpu, hp⟩
    simpa [dist_eq_norm] using this
  obtain ⟨U, hU, hUmain⟩ := nhd_choice j hj S hS N₁ hN₁ V hV
  obtain ⟨Ψ, Ψ₁, ψ, hΨ, hΨ₁, hψc, hψ1, hfac, hsupp, hlaw, hz, hone⟩ := hT k ι i ω hSide.sq U hU
  refine ⟨Ψ, Ψ₁, ψ ∘ j, hΨ, hΨ₁, hψc.comp hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hψ1
  · intro r κ hr
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := (kap_mem_stab_iff π d i r).2 ((hSide.mem _).1 hr)
    show ψ (j (r * κ)) = c r * ψ (j κ)
    rw [map_mul, hlaw _ _ hrS, (hSide.val _ hr).1]
    rw [show (j r).1 = kap π d r from rfl, bdet_kap]
  · intro κ hκ
    obtain ⟨p, hp, u, hu, hκe, -⟩ := hsupp (j κ) hκ
    obtain ⟨r, v, hr, hv, rfl, hvN⟩ := hUmain κ p u hp hu hκe
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := hr
    have hrP : (r : G) ∈ P := (hSide.mem _).2 ((kap_mem_stab_iff π d i r).1 hr)
    refine ⟨r, v, hrP, hv, rfl, ?_⟩
    have hl := hlaw (j r) (j v) hrS
    have hφv : ψ (j v) ≠ 0 := fun h => hκ (by
      show ψ (j (r * v)) = 0
      rw [map_mul, hl, h, mul_zero])
    obtain ⟨p', hp', u', hu', hve, hval⟩ := hsupp (j v) hφv
    have hpN : p' ∈ N₁ := by
      have := hvN u' hu'
      rwa [hve, mul_inv_cancel_right] at this
    have hb : ‖f p' - 1‖ ≤ 1 / 4 := hNf p' hp' hpN
    show ‖ψ (j v) - (‖ψ (j v)‖ : ℂ)‖ ≤ ‖ψ (j v)‖ / 4
    generalize ψ (j v) = a at hval
    have e : a - (‖a‖ : ℂ) = (f p' - 1) * (‖a‖ : ℂ) := by
      rw [sub_mul, one_mul]
      exact congrArg (· - (‖a‖ : ℂ)) hval
    rw [e, norm_mul, Complex.norm_real, norm_norm]
    nlinarith [norm_nonneg a]
  · intro s κ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) ω s = globalZeta (fun t => Ψ₁ fun _ => t) ω s * ψ (j κ)
    have hfun : (fun t => Ψ (t • vec (kap π d κ) i)) = fun t => (Ψ₁ fun _ => t) * ψ (j κ) :=
      funext fun t => hfac t (j κ)
    rw [hfun]
    unfold globalZeta
    rw [← integral_mul_const]
    congr 1
    ext x
    ring
  · obtain ⟨z, hz1, hz2⟩ := hz
    exact ⟨z, by linarith, hz2⟩
  · exact hone

end GlobalTheory.CompanionTheory.EisTestK
end
end

section

noncomputable section

open MeasureTheory Filter Topology Metric
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open scoped NNReal Real Pointwise

namespace GlobalTheory.CompanionTheory.RgEisHGood

theorem differentiable_of_pointwise {K : Type} [TopologicalSpace K] [CompactSpace K] (F : ℂ → C(K, ℂ))
    (hc : Continuous F) (hp : ∀ κ, Differentiable ℂ fun z => F z κ) : Differentiable ℂ F := by
  intro c
  have hint : CircleIntegrable F c ((1 : ℝ≥0) : ℝ) := hc.continuousOn.circleIntegrable'
  have hfp := hasFPowerSeriesOn_cauchy_integral hint one_pos
  simp only [NNReal.coe_one] at hfp
  have heq : ∀ w ∈ ball c (1 : ℝ), ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) = F w := by
    intro w hw
    ext κ
    have hcau := ((hp κ).diffContOnCl (s := ball c 1)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
    have hne : ∀ θ : ℝ, circleMap c 1 θ - w ≠ 0 := fun θ h => by
      have h1 : circleMap c 1 θ ∈ sphere c (1 : ℝ) := circleMap_mem_sphere c zero_le_one θ
      rw [sub_eq_zero.1 h] at h1
      exact (ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 h1)
    have hcont : Continuous (fun θ : ℝ => deriv (circleMap c 1) θ • (circleMap c 1 θ - w)⁻¹ • F (circleMap c 1 θ)) := by
      have e : deriv (circleMap c 1) = fun θ => circleMap 0 1 θ * Complex.I := funext (deriv_circleMap c 1)
      rw [e]
      exact ((continuous_circleMap 0 1).mul continuous_const).smul
        ((((continuous_circleMap c 1).sub continuous_const).inv₀ hne).smul (hc.comp (continuous_circleMap c 1)))
    have hcomm : (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ = ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z κ := by
      have e2 := (ContinuousMap.evalCLM ℂ κ : C(K, ℂ) →L[ℂ] ℂ).intervalIntegral_comp_comm
        (hcont.intervalIntegrable (μ := volume) 0 (2 * π))
      simp only [circleIntegral]
      refine e2.symm.trans ?_
      simp [ContinuousMap.evalCLM]
    have hfin : ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ
        = (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ := rfl
    rw [hfin, hcomm]
    exact hcau
  have han : AnalyticAt ℂ F c := by
    have h1 := hfp.analyticAt
    refine h1.congr ?_
    filter_upwards [ball_mem_nhds c (one_pos : (0:ℝ) < 1)] with w hw using heq w hw
  exact han.differentiableAt

theorem exists_integralCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (μ : Measure K) [IsProbabilityMeasure μ]
    (r : K → E) (hr : Continuous r) : ∃ L : C(K, ℂ) →L[ℂ] E, ∀ f : C(K, ℂ), L f = ∫ κ, f κ • r κ ∂μ := by
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • r κ) μ := fun f =>
    (f.continuous.smul hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let rc : C(K, E) := ⟨r, hr⟩
  let L₀ : C(K, ℂ) →ₗ[ℂ] E :=
    { toFun := fun f => ∫ κ, f κ • r κ ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨L₀.mkContinuous ‖rc‖ fun f => ?_, fun f => rfl⟩
  have hb : ∀ κ, ‖f κ • r κ‖ ≤ ‖rc‖ * ‖f‖ := fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (rc.norm_coe_le_norm κ) (f.norm_coe_le_norm κ) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)
  change ‖∫ κ, f κ • r κ ∂μ‖ ≤ _
  simpa using this

theorem gauss_bound (b a : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ a →
    ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2 ≤ M := by
  set B : ℝ := |a| + |b| with hB
  have hB0 : 0 ≤ B := by positivity
  set c : ℝ := 3 + B with hc
  refine ⟨Real.exp (B ^ 2) * (6 * Real.exp c), by positivity, fun z h1 h2 => ?_⟩
  have hx : |z.re| ≤ B := by
    rw [abs_le]; constructor
    · have := neg_abs_le b; have := abs_nonneg a; linarith
    · have := le_abs_self a; have := abs_nonneg b; linarith
  set t : ℝ := |z.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hz : ‖z‖ ≤ B + t := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hexp : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]; congr 1
    simp [pow_two, Complex.mul_re]
  have h1z : ‖z - 1‖ ≤ 1 + ‖z‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp [add_comm]
  have hs : 1 + ‖z‖ ≤ c + t ^ 2 - 1 := by nlinarith [sq_nonneg (t - 1)]
  have hn0 : 0 ≤ 1 + ‖z‖ := by positivity
  have hc0 : 0 ≤ c + t ^ 2 := by positivity
  have hcube : (1 + ‖z‖) ^ 3 ≤ 6 * Real.exp (c + t ^ 2) := by
    have h3 := Real.pow_div_factorial_le_exp (c + t ^ 2) hc0 3
    have h4 : (1 + ‖z‖) ^ 3 ≤ (c + t ^ 2) ^ 3 := pow_le_pow_left₀ hn0 (by linarith) 3
    have h5 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h5] at h3
    linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 6)).1 h3]
  have hre : z.re ^ 2 ≤ B ^ 2 := by
    have := sq_le_sq' (by linarith [(abs_le.1 hx).1]) (abs_le.1 hx).2
    exact this
  have him : z.im ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2
      = Real.exp (z.re ^ 2 - z.im ^ 2) * (‖z - 1‖ * (1 + ‖z‖) ^ 2) := by
        rw [norm_mul, hexp]; ring
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * ((1 + ‖z‖) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : (1 + ‖z‖) ^ 3 = (1 + ‖z‖) * (1 + ‖z‖) ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h1z (by positivity)
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (6 * Real.exp (c + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hcube (Real.exp_pos _).le
    _ = Real.exp (z.re ^ 2) * (6 * Real.exp c) := by
        rw [him, Real.exp_add, Real.exp_sub, Real.exp_add]
        have := (Real.exp_pos (t ^ 2)).ne'
        field_simp
    _ ≤ Real.exp (B ^ 2) * (6 * Real.exp c) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hre) (by positivity)

theorem hGood : HGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hprob Φ hΦ
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨L, hL⟩ := exists_integralCLM μ (fun κ => ρ κ) hρ
  let Ψ₀ : C((ℂ × G) × K, ℂ) := ⟨fun p => Φ p.1.1 (p.1.2 * p.2),
    hΦ.cont.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)))⟩
  let Ψ : C(ℂ × G, C(K, ℂ)) := Ψ₀.curry
  have hA : ∀ (z : ℂ) (g : G), avg μ ρ (fun κ => Φ z (g * κ)) = L (Ψ (z, g)) := by
    intro z g
    rw [hL]
    rfl
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · simp only [hA]
    have hF : Differentiable ℂ fun z : ℂ => Ψ (z, g) :=
      differentiable_of_pointwise _ (Ψ.continuous.comp (by fun_prop)) fun κ => hΦ.ent (g * κ)
    exact ((Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul
      (differentiable_id.sub_const 1)).smul (L.differentiable.comp hF)
  · simp only [hA, Prod.mk.eta]
    exact (by fun_prop : Continuous fun y : ℂ × G => Complex.exp (y.1 ^ 2) * (y.1 - 1)).smul
      (L.continuous.comp Ψ.continuous)
  · obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g
    obtain ⟨M, hM⟩ := hΦ.strip b a (U * (K : Set G)) (hUc.mul hK)
    obtain ⟨M2, hM2, hg⟩ := gauss_bound b a
    refine ⟨U, hU, ‖L‖ * |M| * M2, fun z h1 h2 g' hg' => ?_⟩
    rw [hA, norm_smul]
    have hΨ : ‖Ψ (z, g')‖ ≤ |M| * (1 + ‖z‖) ^ 2 := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun κ => ?_
      have h := hM z h1 h2 (g' * κ) (Set.mul_mem_mul hg' κ.2)
      exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
    calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * ‖L (Ψ (z, g'))‖
        ≤ ‖Complex.exp (z ^ 2) * (z - 1)‖ * (‖L‖ * (|M| * (1 + ‖z‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left ((L.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hΨ (norm_nonneg _))) (norm_nonneg _)
      _ = ‖L‖ * |M| * (‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2) := by ring
      _ ≤ ‖L‖ * |M| * M2 := mul_le_mul_of_nonneg_left (hg z h1 h2) (by positivity)

end GlobalTheory.CompanionTheory.RgEisHGood
end
end

section

noncomputable section

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMG

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

variable {k : Type} [Field k] [NumberField k]

theorem lineZeta_ratV_unit (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (ξ : Unit → k) (hξ : ξ ≠ 0) : lineZeta Ψ₁ ω z (ratV ξ) = tate Ψ₁ ω z := by
  have h0 : ξ () ≠ 0 := fun h => hξ (funext fun i => by cases i; exact h)
  haveI := isHaarMeasure_ideleMeasure k
  haveI := IdeleGroup.borelSpace k
  have key := integral_mul_left_eq_self (μ := ideleMeasure k)
    (fun x : IdeleGroup k => Ψ₁ (fun _ => (x : 𝔸[k])) * ((ω.toIdele x : Circle) : ℂ) *
      ((((IdeleGroup.ideleModule k x : {r : ℝ // 0 < r}) : ℝ) : ℂ) ^ z))
    (IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0))
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ((x : 𝔸[k]) • ratV ξ) =
      fun _ => ((IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0) * x : IdeleGroup k) : 𝔸[k]) := by
    funext i
    cases i
    simp [ratV, IdeleGroup.diagonal, mul_comm]
  simp only [hx, map_mul, HeckeCharacter.toIdele_diagonal, IdeleGroup.ideleModule_diagonal, one_mul]

theorem proj_unit_eq (l l' : Projectivization k (Unit → k)) : l = l' := by
  induction l using Projectivization.ind
  rename_i v hv
  induction l' using Projectivization.ind
  rename_i w hw
  rw [Projectivization.mk_eq_mk_iff']
  have hw0 : w () ≠ 0 := fun h => hw (funext fun i => by cases i; exact h)
  exact ⟨v () / w (), funext fun i => by cases i; simp [div_mul_cancel₀ _ hw0]⟩

theorem epstein_unit_one (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) :
    epstein Ψ₁ ω z 1 = tate Ψ₁ ω z := by
  have hne : (fun _ : Unit => (1 : k)) ≠ 0 := fun h => one_ne_zero (congrFun h ())
  unfold epstein
  rw [tsum_eq_single (Projectivization.mk k (fun _ : Unit => (1 : k)) hne)
    (fun b hb => absurd (proj_unit_eq b _) hb)]
  simp only [inv_one, Units.val_one, Matrix.one_mulVec]
  exact lineZeta_ratV_unit Ψ₁ ω z _ (Projectivization.rep_nonzero _)

theorem zetaOne_of_epMain : EpMain → ZetaOne := by
  intro h
  unfold EpMain at h
  unfold ZetaOne
  intro k _ _ Ψ₁ ω hΨ hω
  obtain ⟨V, -, hV⟩ := h k
  obtain ⟨F, F', hF, -, -, -⟩ := hV Unit Ψ₁ ω hΨ hω
  refine ⟨fun z => F z 1, ?_, fun z hz => ?_⟩
  · unfold PolyEnt
    refine ⟨hF.entire 1, fun b c => ?_⟩
    obtain ⟨M, hM⟩ := hF.strip b c {1} isCompact_singleton
    exact ⟨M, fun z h1 h2 => hM z h1 h2 1 rfl⟩
  · show F z 1 = _
    rw [hF.eq z (by simpa using hz) 1, epstein_unit_one]
    simp

end GlobalTheory.CompanionTheory.EisMG
end
end

section

open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMirGen

theorem avgMem : AvgMem := by
  unfold AvgMem ForRep
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar _ _Γ P c _ φ hφ hLaw w
  haveI := hHaar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  change ∀ r : K, (r : G) ∈ P → c r • ρ r (avg μ ρ φ w) = avg μ ρ φ w
  intro r hr
  have hcont : Continuous fun κ : K => φ κ • ρ κ := hφ.smul hρ
  have hint : Integrable (fun κ : K => φ κ • ρ κ) μ :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have key : avg μ ρ φ = c r • (ρ r).comp (avg μ ρ φ) := by
    show ∫ κ, φ κ • ρ κ ∂μ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ)
    calc ∫ κ, φ κ • ρ κ ∂μ = ∫ κ, φ (r * κ) • ρ (r * κ) ∂μ :=
          (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) r).symm
      _ = ∫ κ, c r • (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := by
          congr 1
          funext κ
          rw [hLaw r κ hr, map_mul]
          ext x
          simp [mul_smul]
      _ = c r • ∫ κ, (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := integral_smul _ _
      _ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ) := by
          rw [(ContinuousLinearMap.compL ℂ W W W (ρ r)).integral_comp_comm hint]
          rfl
  have hw := congrArg (fun T : W →L[ℂ] W => T w) key
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at hw
  exact hw.symm

end GlobalTheory.CompanionTheory.EisMirGen
end
