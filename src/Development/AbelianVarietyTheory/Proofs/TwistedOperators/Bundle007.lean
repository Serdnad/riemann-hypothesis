module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.CompletePartialOrder
import Aesop.Main
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

open MeasureTheory DoubleCoset

namespace GlobalTheory.TwistedOperatorMainTheorem

theorem main_thm : ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (m : MeasureTheory.Measure G) [MeasureTheory.Measure.IsHaarMeasure m] (J : Subgroup G), IsOpen (↑J : Set G) → IsCompact (↑J : Set G) → ∀ (ι : Type) [Countable ι] (x : ι → G), Pairwise (Function.onFun Disjoint fun (i : ι) ↦ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → ∀ (F : G → ℂ), (∀ (g j : G), j ∈ J → ∀ j' ∈ J, F (j * g * j') = F g) → (∀ (g : G), F g ≠ (0 : ℂ) → ∃ (i : ι), g ∈ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → (Summable fun (i : ι) ↦ MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) * ‖F (x i)‖) → MeasureTheory.Integrable F m ∧ HasSum (fun (i : ι) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G))) : ℂ) * F (x i)) (∫ (g : G), F g ∂m) ∧ HasSum (fun (c : DoubleCoset.Quotient (↑J : Set G) (↑J : Set G)) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (Quotient.out c) (↑J : Set G) (↑J : Set G))) : ℂ) * F (Quotient.out c)) (∫ (g : G), F g ∂m) := by
  intro G _ _ _ _ _ m _ J hJo hJc ι _ x hdisj F hF hsupp hsum

  have hmeas : ∀ a : G, MeasurableSet (doubleCoset a (J : Set G) J) := fun a =>
    (IsOpen.mul_left hJo).measurableSet
  have hfin : ∀ a : G, m (doubleCoset a (J : Set G) J) < ⊤ := fun a =>
    ((hJc.mul isCompact_singleton).mul hJc).measure_lt_top

  have hconst : ∀ a g, g ∈ doubleCoset a (J : Set G) J → F g = F a := by
    intro a g hg
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset.1 hg
    exact hF a u hu w hw
  have hint : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, F g ∂m =
      (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i) := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => hconst (x i) g hg), setIntegral_const, Complex.real_smul]
  have hnorm : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, ‖F g‖ ∂m =
      m.real (doubleCoset (x i) (J : Set G) J) * ‖F (x i)‖ := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => by rw [hconst (x i) g hg]), setIntegral_const, smul_eq_mul]
  have hon : ∀ i, IntegrableOn F (doubleCoset (x i) (J : Set G) J) m := fun i =>
    (integrableOn_const (hfin (x i)).ne).congr_fun (fun g hg => (hconst (x i) g hg).symm) (hmeas _)

  have hU : IntegrableOn F (⋃ i, doubleCoset (x i) (J : Set G) J) m :=
    integrableOn_iUnion_of_summable_integral_norm hon (by simpa only [hnorm] using hsum)
  have hout : ∀ g, g ∉ ⋃ i, doubleCoset (x i) (J : Set G) J → F g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨i, hi⟩ := hsupp g h
    exact hg (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hsumI : HasSum (fun i => (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i)) (∫ g, F g ∂m) := by
    have h := hasSum_integral_iUnion (fun i => hmeas (x i)) hdisj hU
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at h
    simp only [hint] at h
    exact h
  refine ⟨hU.integrable_of_forall_notMem_eq_zero hout, hsumI, ?_⟩

  have hinj : Function.Injective (fun i => DoubleCoset.mk J J (x i)) := by
    intro i j hij
    by_contra hne
    have hj : x j ∈ doubleCoset (x i) (J : Set G) J := by
      obtain ⟨u, hu, w, hw, e⟩ := (@DoubleCoset.eq _ _ J J (x i) (x j)).1 hij
      exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
    exact Set.disjoint_left.1 (hdisj hne) hj (mem_doubleCoset_self J J (x j))
  have hcls : ∀ i, Quotient.out (DoubleCoset.mk J J (x i)) ∈ doubleCoset (x i) (J : Set G) J := by
    intro i
    obtain ⟨u, hu, w, hw, e⟩ := DoubleCoset.mk_out_eq_mul J J (x i)
    exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
  have hzero : ∀ c ∉ Set.range (fun i => DoubleCoset.mk J J (x i)),
      (m.real (doubleCoset (Quotient.out c) (J : Set G) J) : ℂ) * F (Quotient.out c) = 0 := by
    intro c hc
    by_contra h
    obtain ⟨i, hi⟩ := hsupp _ (right_ne_zero_of_mul h)
    refine hc ⟨i, ?_⟩
    show DoubleCoset.mk J J (x i) = c
    rw [← DoubleCoset.out_eq' c]
    exact (DoubleCoset.mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hi)).symm
  refine (hinj.hasSum_iff hzero).1 ?_
  convert hsumI using 1
  funext i
  show (m.real (doubleCoset (Quotient.out (DoubleCoset.mk J J (x i))) (J : Set G) J) : ℂ) *
      F (Quotient.out (DoubleCoset.mk J J (x i))) = _
  rw [doubleCoset_eq_of_mem (hcls i), hconst (x i) _ (hcls i)]

end GlobalTheory.TwistedOperatorMainTheorem
end

section

open MeasureTheory

namespace GlobalTheory

theorem quadForm_eventually_unif_negDef {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hc : Continuous (fun p : ℝ × V => M p.1 p.2 p.2))
    (hneg : ∀ t v, v ≠ 0 → (M t v v).re < 0) (t₀ : ℝ) :
    ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  have hF : Continuous (fun p : ℝ × V => (M p.1 p.2 p.2).re) := Complex.continuous_re.comp hc
  have hscale : ∀ t (c : ℝ) (u : V), (M t (c • u) (c • u)).re = c ^ 2 * (M t u u).re := by
    intro t c u
    simp only [map_smul, LinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
    ring
  have key : ∀ (ε : ℝ) (t : ℝ), (∀ u ∈ Metric.sphere (0:V) 1, (M t u u).re < -ε) →
      ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
    intro ε t ht x
    by_cases hx : x = 0
    · subst hx; simp
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0:V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have h1 := ht _ hu
      have hx' : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      have h2 : (M t x x).re = ‖x‖ ^ 2 * (M t (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := by
        conv_lhs => rw [hx']
        exact hscale t _ _
      rw [h2]
      have hp : 0 ≤ ‖x‖ ^ 2 := by positivity
      nlinarith
  have hS : IsCompact (Metric.sphere (0:V) 1) := isCompact_sphere 0 1
  rcases (Metric.sphere (0:V) 1).eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, Filter.Eventually.of_forall fun t => key 1 t ?_⟩
    intro u hu
    rw [hE] at hu
    exact absurd hu (Set.notMem_empty _)
  · have hcont0 : ContinuousOn (fun u : V => (M t₀ u u).re) (Metric.sphere 0 1) :=
      (hF.comp (Continuous.prodMk_right t₀)).continuousOn
    obtain ⟨u₀, hu₀, hmax⟩ := hS.exists_isMaxOn hNE hcont0
    have hu₀0 : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀
    have hm : (M t₀ u₀ u₀).re < 0 := hneg t₀ u₀ hu₀0
    refine ⟨-(M t₀ u₀ u₀).re / 2, by linarith, ?_⟩
    have hev : ∀ᶠ t in nhds t₀, ∀ u ∈ Metric.sphere (0:V) 1,
        (M t u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
      apply hS.eventually_forall_of_forall_eventually
      intro u hu
      have hlt : (M t₀ u u).re < -(-(M t₀ u₀ u₀).re / 2) := by
        have := hmax hu
        simp only [Set.mem_setOf_eq] at this
        linarith
      exact hF.continuousAt.eventually_lt continuousAt_const hlt
    exact hev.mono fun t ht => key _ t ht

theorem quadForm_unif_target : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) :=
  fun M hc hneg t₀ => quadForm_eventually_unif_negDef M hc hneg t₀

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem unfold_tsum_along_subgroup : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain (Γ.comap ι) 𝓕 ν → ∀ (f : G → ℂ) (φ : H → ℂ), (∀ γ : G, Measurable fun h => f (γ * ι h)) → Measurable φ → (∀ γ ∈ Γ.comap ι, ∀ h, φ (γ * h) = φ h) → (∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, ‖f ((q.out : Γ) * ι h) * φ h‖ₑ ∂ν) ≠ ⊤ → IntegrableOn (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) 𝓕 ν ∧ HasSum (fun q : Γ ⧸ ι.range.subgroupOf Γ => ∫ h, f ((q.out : Γ) * ι h) * φ h ∂ν) (∫ h in 𝓕, (∑' γ : Γ, f (γ * ι h)) * φ h ∂ν) := by
  intro G H _ _ _ _ ν _ ι hι Γ _ 𝓕 h𝓕 f φ hf hφ hφinv hT
  haveI : MeasurableConstSMul (Γ.comap ι) H := ⟨fun g => measurable_const_mul (g : H)⟩
  haveI : SMulInvariantMeasure (Γ.comap ι) H ν := ⟨fun g s _ => measure_preimage_mul ν (g : H) s⟩
  haveI : Countable (Γ.comap ι) := by
    refine Function.Injective.countable (f := fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) ?_
    intro a b hab
    exact Subtype.ext (hι (congrArg Subtype.val hab))
  let e : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p => (p.1.out : Γ) * ⟨ι p.2, p.2.2⟩
  have hmemK : ∀ δ : Γ.comap ι, (⟨ι δ, δ.2⟩ : Γ) ∈ ι.range.subgroupOf Γ := fun δ => by
    rw [Subgroup.mem_subgroupOf]; exact ⟨δ, rfl⟩
  have he_inj : Function.Injective e := by
    rintro ⟨q, δ⟩ ⟨q', δ'⟩ h
    have hq : ∀ q δ, (QuotientGroup.mk (e (q, δ)) : Γ ⧸ ι.range.subgroupOf Γ) = q := by
      intro q δ
      show (QuotientGroup.mk ((q.out : Γ) * ⟨ι δ, δ.2⟩) : Γ ⧸ ι.range.subgroupOf Γ) = q
      rw [QuotientGroup.mk_mul_of_mem _ (hmemK δ)]
      exact QuotientGroup.out_eq' q
    have hqq : q = q' := by rw [← hq q δ, ← hq q' δ', h]
    subst hqq
    have h2 := mul_left_cancel h
    have h3 : ι δ = ι δ' := congrArg Subtype.val h2
    rw [Prod.mk.injEq]
    exact ⟨rfl, Subtype.ext (hι h3)⟩
  have he_surj : Function.Surjective e := by
    intro γ
    set q : Γ ⧸ ι.range.subgroupOf Γ := QuotientGroup.mk γ with hqdef
    have hm : (q.out : Γ)⁻¹ * γ ∈ ι.range.subgroupOf Γ := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hm
    obtain ⟨y, hy⟩ := hm
    have hyΓ : ι y ∈ Γ := by rw [hy]; exact ((q.out : Γ)⁻¹ * γ).2
    refine ⟨(q, ⟨y, hyΓ⟩), ?_⟩
    apply Subtype.ext
    show ((q.out : Γ) : G) * ι y = γ
    rw [hy]
    simp
  let eq := Equiv.ofBijective e ⟨he_inj, he_surj⟩
  let F : Γ → H → ℂ := fun γ h => f ((γ : G) * ι h) * φ h
  let g : Γ ⧸ ι.range.subgroupOf Γ → H → ℂ := fun q h => f (((q.out : Γ) : G) * ι h) * φ h
  have hkey : ∀ q (δ : Γ.comap ι) h, F (e (q, δ)) h = g q (δ • h) := by
    intro q δ h
    show f ((((q.out : Γ) : G) * ι δ) * ι h) * φ h = f (((q.out : Γ) : G) * ι ((δ : H) * h)) * φ ((δ : H) * h)
    rw [map_mul, mul_assoc, hφinv δ δ.2 h]
  have hFm : ∀ γ, Measurable (F γ) := fun γ => (hf γ).mul hφ
  have hgm : ∀ q, Measurable (g q) := fun q => (hf _).mul hφ
  have hA : ∀ q, ∫⁻ h, ‖g q h‖ₑ ∂ν = ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν := by
    intro q
    rw [h𝓕.lintegral_eq_tsum'' (fun h => ‖g q h‖ₑ)]
    simp_rw [hkey]
  have hsumF : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν = ∑' q, ∫⁻ h, ‖g q h‖ₑ ∂ν := by
    rw [← eq.tsum_eq]
    calc ∑' p, ∫⁻ h in 𝓕, ‖F (eq p) h‖ₑ ∂ν
        = ∑' q, ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν :=
          ENNReal.tsum_prod (f := fun q δ => ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν)
      _ = _ := by simp_rw [hA]
  have hT' : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν ≠ ⊤ := by rw [hsumF]; exact hT
  have hfun : (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) = fun h => ∑' γ : Γ, F γ h :=
    funext fun h => tsum_mul_right.symm
  have hint : IntegrableOn (fun h => ∑' γ : Γ, F γ h) 𝓕 ν := by
    refine ⟨(AEMeasurable.tsum fun γ => (hFm γ).aemeasurable).aestronglyMeasurable, ?_⟩
    show ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν < ⊤
    calc ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν ≤ ∫⁻ h in 𝓕, ∑' γ, ‖F γ h‖ₑ ∂ν :=
          lintegral_mono fun h => enorm_tsum_le_tsum_enorm
      _ = ∑' γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν := lintegral_tsum fun γ => (hFm γ).aemeasurable.enorm
      _ < ⊤ := lt_top_iff_ne_top.2 hT'
  have hsumm : Summable fun γ : Γ => ∫ h in 𝓕, F γ h ∂ν := by
    refine Summable.of_norm ?_
    have h1 : ∑' γ : Γ, ‖∫ h in 𝓕, F γ h ∂ν‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top hT' (ENNReal.tsum_le_tsum fun γ => enorm_integral_le_lintegral_enorm _)
    simp only [enorm_eq_nnnorm] at h1
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hI : ∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν = ∑' γ : Γ, ∫ h in 𝓕, F γ h ∂ν :=
    integral_tsum (fun γ => (hFm γ).aestronglyMeasurable) hT'
  have hgint : ∀ q, Integrable (g q) ν := fun q =>
    ⟨(hgm q).aestronglyMeasurable,
      lt_of_le_of_lt (ENNReal.le_tsum (f := fun q => ∫⁻ h, ‖g q h‖ₑ ∂ν) q) (lt_top_iff_ne_top.2 hT)⟩
  have hs : Summable (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν) :=
    (eq.summable_iff).2 hsumm
  have hinner : ∀ q, HasSum (fun δ : Γ.comap ι => ∫ h in 𝓕, F (e (q, δ)) h ∂ν) (∫ h, g q h ∂ν) := by
    intro q
    have h1 := (hs.prod_factor q).hasSum
    rw [h𝓕.integral_eq_tsum'' (g q) (hgint q)]
    simp_rw [← hkey]
    exact h1
  have htot : HasSum (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν)
      (∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν) := by
    rw [hI]; exact (eq.hasSum_iff).2 hsumm.hasSum
  rw [hfun]
  exact ⟨hint, htot.prod_fiberwise hinner⟩

end GlobalTheory
end

section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace OrbitUnfold

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}

def pull (𝓕 : Set H) (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull (hF : IsFundamentalDomain Γ 𝓕 ν) (g : H) :
    NullMeasurableSet (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 g) ν :=
  hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull (hF : IsFundamentalDomain Γ 𝓕 ν) {a b : Γ}
    (hab : a ≠ b) :
    AEDisjoint ν (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (a : H)) (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (b : H)) := by
  have key : ∀ c : Γ, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (c : H) = c⁻¹ • 𝓕 := fun c => by
    ext x
    simp [_root_.GlobalTheory.OrbitUnfold.pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  rw [key, key]
  exact hF.aedisjoint (inv_injective.ne hab)

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (g : H) (f : H → ℂ) :
    ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setIntegral_preimage_emb (measurableEmbedding_mulLeft g) f 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (g : H) (f : H → ℝ≥0∞) :
    ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫⁻ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft g) f 𝓕


open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull (hF : IsFundamentalDomain Γ 𝓕 ν)
    (y₀ : Y) {O : Set Y}
    [Countable O] (hO : ∀ γ : Γ, γ • y₀ ∈ O) (σ : O → Γ) (hσ : ∀ a : O, σ a • y₀ = a) :
    IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype)
      (⋃ a : O, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
  refine ⟨.iUnion (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _), ?_, ?_⟩
  ·
    filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
    let a : O := ⟨γ • y₀, hO γ⟩
    have hs : (σ a)⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ a]
    refine ⟨⟨Γ.subtype ((σ a)⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩, Set.mem_iUnion.2 ⟨a, ?_⟩⟩
    simpa [_root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def, mul_assoc] using hγ
  ·
    rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
    have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : O),
        (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ :
            (MulAction.stabilizer Γ y₀).map Γ.subtype) •
          _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H) = (σ a * u⁻¹)⁻¹ • 𝓕 := by
      intro u hu a
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem, _root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def,
        mul_assoc]
    simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
    refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
    refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
    have hab : a = b := by
      apply Subtype.ext
      have h1 := congrArg (· • y₀) h
      simp only [mul_smul] at h1
      rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
    subst hab
    have : s = t := inv_injective (mul_left_cancel h)
    subst this
    rfl

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
private theorem selfEquivSigmaOrbits_symm_mk {G X : Type} [Group G] [MulAction G X]
    (ω : MulAction.orbitRel.Quotient G X) (x : MulAction.orbit G ω.out) :
    (MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, x⟩ = x := rfl


open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H)
      [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y]
      [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ,
      (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) →
      ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ →
      (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν →
        IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) →
      ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  intro H _ _ _ ν _ Γ _ Y _ _ 𝓕 hF Φ hmeas hinv hfin hzero
  have horbit : ∀ y₀ : Y, ∑' a : MulAction.orbit Γ y₀, ∫ h in 𝓕, Φ a h ∂ν = 0 := by
    intro y₀
    have hO : ∀ γ : Γ, γ • y₀ ∈ MulAction.orbit Γ y₀ := fun γ => MulAction.mem_orbit y₀ γ
    choose σ hσ using fun a : MulAction.orbit Γ y₀ =>
      (MulAction.mem_orbit_iff.1 a.2 : ∃ g : Γ, g • y₀ = a)
    have hT := _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO σ hσ
    have hshift : ∀ a : MulAction.orbit Γ y₀, ∀ h, Φ a ((σ a : H) * h) = Φ y₀ h := fun a h => by
      rw [← hinv (σ a) y₀ h, hσ]
    have hpt : ∀ a : MulAction.orbit Γ y₀,
        ∫ h in 𝓕, Φ a h ∂ν = ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), Φ y₀ h ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (σ a : H) (Φ a)]
      simp only [hshift]
    have hlpt : ∀ a : MulAction.orbit Γ y₀,
        ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (σ a : H) (fun h => ‖Φ a h‖ₑ)]
      simp only [hshift]
    have hσinj : Function.Injective σ := fun a b hab =>
      Subtype.ext (by rw [← hσ a, ← hσ b, hab])
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν)
        fun a : MulAction.orbit Γ y₀ => _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) :=
      fun a b hab => _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull hF (hσinj.ne hab)
    have hint : IntegrableOn (Φ y₀)
        (⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
      refine ⟨(hmeas y₀).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ h in ⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν
          ≤ ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν :=
            lintegral_iUnion_le _ _
        _ = ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by simp only [hlpt]
        _ ≤ ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
            (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective Subtype.val_injective _); exact _root_.le_rfl)
        _ < ⊤ := lt_top_iff_ne_top.2 hfin
    simp only [hpt]
    rw [← integral_iUnion_ae (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hdisj hint]
    exact hzero y₀ _ hT hint
  have hsum : Summable fun y => ∫ h in 𝓕, Φ y h ∂ν := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun y => ?_
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono (ENNReal.ne_top_of_tsum_ne_top hfin y)
      (enorm_integral_le_lintegral_enorm _)
  have hs' := ((MulAction.selfEquivSigmaOrbits Γ Y).symm.summable_iff
    (f := fun y => ∫ h in 𝓕, Φ y h ∂ν)).2 hsum
  rw [← (MulAction.selfEquivSigmaOrbits Γ Y).symm.tsum_eq (fun y => ∫ h in 𝓕, Φ y h ∂ν)]
  simp only [Function.comp_def] at hs'
  rw [Summable.tsum_sigma hs']
  simp only [Function.comp_apply, selfEquivSigmaOrbits_symm_mk, horbit, tsum_zero]

end OrbitUnfold
end GlobalTheory
end

section

namespace GlobalTheory

theorem trace_matrix_pi_operator : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  intro W _ _ _ m h A
  have key : ∀ k j : Fin m, LinearMap.trace ℂ (Fin m → W)
      (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ LinearMap.proj j)
      = if k = j then LinearMap.trace ℂ W A else 0 := by
    intro k j
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    by_cases hkj : k = j
    · subst hkj
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id, if_pos rfl]
    · rw [LinearMap.proj_comp_single_ne (R := ℂ) (φ := fun _ : Fin m => W) j k (Ne.symm hkj), LinearMap.comp_zero, map_zero, if_neg hkj]

  simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
  Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_mul]

end GlobalTheory
end
