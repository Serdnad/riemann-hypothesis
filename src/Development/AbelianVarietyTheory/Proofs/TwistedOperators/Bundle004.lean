module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Order.Floor

@[expose] public section

section

open Finset

namespace GlobalTheory

theorem hasSum_eq_sum_of_matching_family : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  intro C n m t m' c R s hs h1 h2 h3 h4 h5
  classical
  set P : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => m' i ≠ 0) with hPdef
  let g : P → C := fun i => Classical.choose (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have hg : ∀ i : P, R (g i) i.1 := fun i => Classical.choose_spec (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have ginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    have hj := hg j
    rw [← hij] at hj
    exact h4 _ _ _ (hg i) hj
  have hT : ∀ x ∉ (Finset.univ.image g), (m x : ℂ) * t x = 0 := by
    intro x hx
    by_contra hne
    have hm : m x ≠ 0 := by intro h; apply hne; simp [h]
    have ht : t x ≠ 0 := by intro h; apply hne; simp [h]
    obtain ⟨i, hi⟩ := h1 x hm ht
    have hmi : m' i ≠ 0 := by rw [← (h3 x i hi).1]; exact hm
    have hiP : i ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmi⟩
    apply hx
    rw [Finset.mem_image]
    exact ⟨⟨i, hiP⟩, Finset.mem_univ _, h5 _ _ _ (hg ⟨i, hiP⟩) hi⟩
  have hs2 : HasSum (fun x => (m x : ℂ) * t x) (∑ x ∈ Finset.univ.image g, (m x : ℂ) * t x) := hasSum_sum_of_ne_finset_zero hT
  rw [hs.unique hs2, Finset.sum_image (fun i _ j _ h => ginj h)]
  rw [← Finset.sum_filter_of_ne (p := fun i => m' i ≠ 0) (fun i _ hne => by intro h; apply hne; simp [h])]
  rw [← hPdef, ← Finset.sum_attach P (fun i => (m' i : ℂ) * c i), Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro i _
  rw [(h3 _ _ (hg i)).1, (h3 _ _ (hg i)).2]

end GlobalTheory
end

section

namespace GlobalTheory

open QuotientGroup

theorem hasSum_comp_fst_card_mul_of_fintype {α β : Type} [Fintype β] (f : α → ℂ) (a : ℂ) (hf : HasSum f a) :
    HasSum (fun p : α × β => f p.1) ((Fintype.card β : ℂ) * a) := by
  classical
  have hdec : (fun p : α × β => f p.1) = fun p => ∑ b : β, (if p.2 = b then f p.1 else 0) := by
    funext p
    simp
  rw [hdec]
  have hterm : ∀ b ∈ (Finset.univ : Finset β),
      HasSum (fun p : α × β => if p.2 = b then f p.1 else 0) a := by
    intro b _
    have hinj : Function.Injective (fun x : α => (x, b)) := fun x y h => by
      simpa using congrArg Prod.fst h
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def] using hf
    · intro p hp
      by_cases h : p.2 = b
      · exact absurd ⟨p.1, by ext <;> simp [h]⟩ hp
      · simp [h]
  have := hasSum_sum hterm
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

theorem hasSum_cosets_smaller_level_relIndex_mul : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  intro G _ K J H Γ hKJ hJH hHΓ hidx Ψ z hvan hinv hsum
  classical

  set f : Γ ⧸ J.subgroupOf Γ → ℂ := fun x => Ψ (x.out : Γ) with hf
  have hfmk : ∀ g : Γ, f (mk g) = Ψ (g : G) := by
    intro g
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf Γ) g
    simp only [hf, hj, Subgroup.coe_mul]
    exact hinv _ g.2 _ (Subgroup.mem_subgroupOf.mp j.2)

  let ι : H ⧸ J.subgroupOf H → Γ ⧸ J.subgroupOf Γ := fun y => mk (Subgroup.inclusion hHΓ y.out)
  have hιmk : ∀ a : H, ι (mk a) = mk (Subgroup.inclusion hHΓ a) := by
    intro a
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) a
    show (mk (Subgroup.inclusion hHΓ (mk a : H ⧸ J.subgroupOf H).out) : Γ ⧸ J.subgroupOf Γ) = _
    rw [hj, QuotientGroup.eq]
    simp [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp j.2
  have hιinj : Function.Injective ι := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [hιmk, hιmk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hxy
  have h1 : HasSum f z := by
    rw [← hιinj.hasSum_iff]
    · convert hsum using 1
      funext y
      show f (mk (Subgroup.inclusion hHΓ y.out)) = _
      rw [hfmk]
      rfl
    · intro x hx
      show Ψ (x.out : G) = 0
      apply hvan _ x.out.2
      intro hH
      apply hx
      refine ⟨mk ⟨(x.out : G), hH⟩, ?_⟩
      rw [hιmk]
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rfl

  have hle : K.subgroupOf Γ ≤ J.subgroupOf Γ := fun x hx => by
    simpa [Subgroup.mem_subgroupOf] using hKJ (Subgroup.mem_subgroupOf.mp hx)
  let e := Subgroup.quotientEquivProdOfLE hle
  have hJΓ : J ≤ Γ := hJH.trans hHΓ
  have hrel : (K.subgroupOf Γ).relIndex (J.subgroupOf Γ) = K.relIndex J :=
    Subgroup.relIndex_subgroupOf hJΓ
  haveI : (((K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))).FiniteIndex := ⟨by
    rw [← Subgroup.relIndex, hrel]; exact hidx⟩
  haveI : Finite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))
  have hcard : (Fintype.card (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) : ℂ)
      = (K.relIndex J : ℂ) := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index, ← Subgroup.relIndex, hrel]
  have h2 := hasSum_comp_fst_card_mul_of_fintype (β := J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) f z h1
  rw [hcard, ← e.hasSum_iff] at h2
  convert h2 using 1
  funext y
  have he1 : (e y).1 = mk y.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  simp only [Function.comp_apply, he1, hfmk]

end GlobalTheory
end

section

namespace GlobalTheory

theorem hasSum_quotient_transport :
    ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H),
      (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ,
      HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  intro G H _ _ e K K' hK f hf s hs
  have hrel : ∀ a b : G, (QuotientGroup.leftRel K) a b ↔ (QuotientGroup.leftRel K') (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK, map_mul, map_inv]

  let ψ : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv hrel
  have hψ : ∀ q : G ⧸ K, f (e.symm (ψ q).out) = f q.out := by
    intro q
    have h2 : ψ q = QuotientGroup.mk (e q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h3 : (e q.out)⁻¹ * (ψ q).out ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', h2]
    have h4 : e.symm (ψ q).out = q.out * e.symm ((e q.out)⁻¹ * (ψ q).out) := by
      rw [map_mul, map_inv, MulEquiv.symm_apply_apply, mul_inv_cancel_left]
    rw [h4, hf _ _ ((hK _).2 (by simpa using h3))]
  have hcomp : (fun a : G ⧸ K => f a.out) = (fun b : H ⧸ K' => f (e.symm b.out)) ∘ ψ := by
    funext q
    exact (hψ q).symm
  rw [hcomp]
  exact (Equiv.hasSum_iff ψ).2 hs

end GlobalTheory
end

section

open MeasureTheory

open Metric Set Filter Topology Convolution

namespace GlobalTheory.FuncEqSmooth

theorem contDiff_of_func_eq (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hc : Continuous c)
    (hc0 : c 0 ≠ 0) (hU : IsOpen U) (hUs : ∀ s, (s, 0) ∈ U)
    (hE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U)
    (hfe : ∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  have h00 : ((0:ℝ), (0:ℝ)) ∈ U := hUs 0
  have hw0 : c 0 * E 0 0 = 1 := by
    have h1 := hfe (0,0) h00
    simp only [add_zero] at h1
    have h2 : c 0 * (c 0 * E 0 0) = c 0 * 1 := by rw [mul_one, ← mul_assoc]; exact h1.symm
    exact mul_left_cancel₀ hc0 h2
  have hEcont : ContinuousAt (fun p : ℝ × ℝ => E p.1 p.2) (0,0) :=
    hE.continuousOn.continuousAt (hU.mem_nhds h00)
  have hwcont : ContinuousAt (fun v : ℝ => c v * E 0 v) 0 := by
    have h1 : ContinuousAt (fun v : ℝ => E (0:ℝ) v) 0 :=
      hEcont.comp (f := fun v : ℝ => ((0:ℝ), v)) (by fun_prop)
    exact hc.continuousAt.mul h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ h00
  obtain ⟨δ, hδ, hwδ⟩ := Metric.continuousAt_iff.1 hwcont (1/2) (by norm_num)
  set r := min ε δ with hr
  have hr0 : 0 < r := lt_min hε hδ
  have hbox : ∀ a b : ℝ, |a| < r → |b| < r → (a, b) ∈ U := by
    intro a b ha hb
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    simp only [Real.dist_eq, sub_zero]
    exact ⟨lt_of_lt_of_le ha (min_le_left _ _), lt_of_lt_of_le hb (min_le_left _ _)⟩

  let ψ : ContDiffBump (0:ℝ) := ⟨r/4, r/2, by positivity, by linarith⟩
  set φ : ℝ → ℝ := ψ.normed volume with hφdef
  have hφ0 : ∀ x : ℝ, r/2 ≤ |x| → φ x = 0 := by
    intro x hx
    rw [← Function.notMem_support, hφdef, ψ.support_normed_eq, mem_ball, Real.dist_eq, sub_zero]
    show ¬ |x| < r/2
    linarith
  have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := ψ.contDiff_normed
  let φr : ℝ → ℂ := fun y => ((φ y : ℝ) : ℂ)
  have hφr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φr := Complex.ofRealCLM.contDiff.comp hφs
  have hφr0 : ∀ x : ℝ, r/2 ≤ |x| → φr x = 0 := by
    intro x hx; simp [φr, hφ0 x hx]

  let A : ℝ → ℂ := c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    have hcs : HasCompactSupport (fun y => φr (-y)) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) (r/2)) (fun y hy => ?_)
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hy
      exact hφr0 _ (by rw [abs_neg]; exact hy.le)
    exact hcs.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℂ) hc.locallyIntegrable
      (hφr.comp contDiff_neg)

  let G : ℝ → ℝ → ℂ := fun t y => φr (-y) * E t (-y)
  let h : ℝ → ℂ := fun t => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry G) (ball (0:ℝ) r ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    have hq1 : |q.1| < r := by
      have := hq.1; rw [mem_ball, Real.dist_eq, sub_zero] at this; exact this
    by_cases hq2 : |q.2| < r
    · have hmem : (q.1, -q.2) ∈ U := hbox _ _ hq1 (by rw [abs_neg]; exact hq2)
      have hEat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) (q.1, -q.2) :=
        hE.contDiffAt (hU.mem_nhds hmem)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => E q.1 (-q.2)) q :=
        hEat.comp (f := fun q : ℝ × ℝ => (q.1, -q.2)) q (by fun_prop)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => φr (-q.2)) q :=
        (hφr.comp (contDiff_snd.neg)).contDiffAt
      exact h1.mul h2
    · push_neg at hq2
      have hev : ∀ᶠ q' in 𝓝 q, r/2 < |q'.2| :=
        continuousAt_const.eventually_lt (by fun_prop) (by linarith)
      refine contDiffAt_const (c := (0:ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with q' hq'
      show φr (-q'.2) * E q'.1 (-q'.2) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hq'.le), zero_mul]
  have hparam := contDiffOn_convolution_right_with_param (μ := volume) (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℂ) (f := c) (g := G) (s := ball (0:ℝ) r) (k := closedBall (0:ℝ) (r/2))
    isOpen_ball (isCompact_closedBall _ _)
    (fun p x _ hx => by
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
      show φr (-x) * E p (-x) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hx.le), zero_mul])
    hc.locallyIntegrable hG
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (ball (0:ℝ) r) := by
    have hemb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t, (0:ℝ))) (ball (0:ℝ) r) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have h3 := ContDiffOn.comp (g := fun q : ℝ × ℝ => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G q.1) q.2)
      hparam hemb (fun t ht => ⟨ht, mem_univ _⟩)
    exact h3
  have hrδ : r ≤ δ := min_le_right _ _

  let cl : ℝ → ℝ := fun v => max (-(r/2)) (min v (r/2))
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hcl : ∀ v, cl v ∈ Icc (-(r/2)) (r/2) := fun v =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hclid : ∀ v, |v| ≤ r/2 → cl v = v := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    show max (-(r/2)) (min v (r/2)) = v
    rw [min_eq_left h2, max_eq_right h1]
  have hE0on : ContinuousOn (fun v : ℝ => E 0 v) (Icc (-(r/2)) (r/2)) := by
    have h3 := hE.continuousOn.comp (f := fun v : ℝ => ((0:ℝ), v))
      (by fun_prop : Continuous fun v : ℝ => ((0:ℝ), v)).continuousOn
      (fun v (hv : v ∈ Icc (-(r/2)) (r/2)) => hbox 0 v (by simp [hr0]) (abs_lt.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩))
    exact h3
  let Ehat : ℝ → ℂ := fun v => E 0 (cl v)
  have hEhat : Continuous Ehat := hE0on.comp_continuous hclc hcl
  let g : ℝ → ℂ := fun x => c (-x) * Ehat (-x)
  have hgc : Continuous g := (hc.comp continuous_neg).mul (hEhat.comp continuous_neg)
  have hg0 : g 0 = 1 := by
    show c (-0) * E 0 (cl (-0)) = 1
    rw [neg_zero, hclid 0 (by simp; positivity), hw0]
  have hdist := ψ.dist_normed_convolution_le (μ := volume) (x₀ := 0) (ε := 1/2) hgc.aestronglyMeasurable
    (fun x hx => by
      have hx' : |x| < r/2 := by
        have h6 := hx; rw [mem_ball, Real.dist_eq, sub_zero] at h6; exact h6
      have e1 : g x = c (-x) * E 0 (-x) := by
        show c (-x) * E 0 (cl (-x)) = _
        rw [hclid _ (by rw [abs_neg]; exact hx'.le)]
      rw [e1, hg0, ← hw0]
      exact (hwδ (by rw [Real.dist_eq, sub_zero, abs_neg]; linarith)).le)
  have hconv : (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 0 = h 0 := by
    show _ = (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G 0) 0
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g, G, Ehat, φr]
    by_cases hu : |u| < r/2
    · rw [hclid u hu.le, Complex.real_smul]; ring
    · have hz : ψ.normed volume u = 0 := hφ0 u (not_lt.1 hu)
      have hz' : φ u = 0 := hφ0 u (not_lt.1 hu)
      rw [hz, hz']; simp
  have h0ne : h 0 ≠ 0 := by
    intro h0
    rw [hconv, hg0, h0] at hdist
    norm_num at hdist

  have hAh : ∀ t, |t| < r → A t = c t * h t := by
    intro t ht
    show (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))) t
      = c t * (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
    rw [convolution_def, convolution_def, ← integral_const_mul,
      ← integral_add_right_eq_self (μ := volume)
        (fun u => (ContinuousLinearMap.mul ℝ ℂ) (c u) (φr (-(t - u)))) t]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [ContinuousLinearMap.mul_apply', G, zero_sub, neg_neg]
    have e : -(t - (s + t)) = s := by ring
    rw [e]
    by_cases hs : |s| < r/2
    · have h7 := hfe (t, s) (hbox t s ht (by linarith))
      simp only at h7
      rw [add_comm s t, h7]; ring
    · rw [hφr0 s (not_lt.1 hs)]; ring

  have hcont_h : ContinuousOn h (ball (0:ℝ) r) := hh.continuousOn
  set V := ball (0:ℝ) r ∩ h ⁻¹' {0}ᶜ with hV
  have hVo : IsOpen V := hcont_h.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have h0V : (0:ℝ) ∈ V := ⟨mem_ball_self hr0, h0ne⟩
  have hcV : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c V := by
    have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => A t * (h t)⁻¹) V :=
      hA.contDiffOn.mul ((hh.mono inter_subset_left).inv (fun t ht => ht.2))
    refine h4.congr (fun t ht => ?_)
    have ht1 : |t| < r := by
      have h8 := ht.1; rw [mem_ball, Real.dist_eq, sub_zero] at h8; exact h8
    have hne : h t ≠ 0 := ht.2
    show c t = A t * (h t)⁻¹
    rw [hAh t ht1, mul_inv_cancel_right₀ hne]

  rw [contDiff_iff_contDiffAt]
  intro t₀
  set W := (fun t : ℝ => (t₀, t)) ⁻¹' U ∩ V with hW
  have hWo : IsOpen W := (hU.preimage (by fun_prop)).inter hVo
  have h0W : (0:ℝ) ∈ W := ⟨hUs t₀, h0V⟩
  have hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) W := by
    have hE' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => E t₀ t) W :=
      hE.comp (f := fun t : ℝ => (t₀, t)) (contDiff_const.prodMk contDiff_id).contDiffOn (fun t ht => ht.1)
    have h5 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c t₀ * c t * E t₀ t) W :=
      (contDiffOn_const.mul (hcV.mono inter_subset_right)).mul hE'
    refine h5.congr (fun t ht => ?_)
    exact hfe (t₀, t) ht.1
  have hF0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) 0 := hFW.contDiffAt (hWo.mem_nhds h0W)
  have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x - t₀) t₀ := (contDiff_id.sub contDiff_const).contDiffAt
  have hF0' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) ((fun x : ℝ => x - t₀) t₀) := by
    simpa using hF0
  have h9 := ContDiffAt.comp (f := fun x : ℝ => x - t₀) t₀ hF0' hsub
  simpa [Function.comp_def, add_sub_cancel_left] using h9

end GlobalTheory.FuncEqSmooth
end

section

open scoped InnerProductSpace

namespace GlobalTheory

open Set Filter Topology

theorem vanish_at_one_of_derivs_vanish_of_growth (φ : ℕ → ℝ → ℂ) (a b : ℝ)
    (hd : ∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) (h0 : ∀ k, φ k 0 = 0)
    (hb : ∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) : φ 0 1 = 0 := by
  set M : ℕ → ℝ := fun n => Real.sqrt (b * a ^ n * n.factorial) with hM
  have base : ∀ k t, ‖φ k t‖ ≤ M k := by
    intro k t
    have := Real.abs_le_sqrt (hb k t)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have key : ∀ m k, ∀ t ∈ Icc (0:ℝ) 1, ‖φ k t‖ ≤ M (k + m) * t ^ m / m.factorial := by
    intro m
    induction m with
    | zero => intro k t _; simpa using base k t
    | succ m ih =>
      intro k
      have hB : ∀ x, HasDerivAt (fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
          (M ((k + 1) + m) * x ^ m / m.factorial) x := by
        intro x
        have h1 := ((hasDerivAt_pow (m + 1) x).const_mul (M (k + (m + 1)))).div_const
          ((m + 1).factorial : ℝ)
        refine h1.congr_deriv ?_
        rw [show k + 1 + m = k + (m + 1) by ring]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
        have : (m.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ k)
        (f' := φ (k + 1)) (a := 0) (b := 1)
        (fun x _ => (hd k x).continuousAt.continuousWithinAt)
        (fun x _ => (hd k x).hasDerivWithinAt)
        (B := fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
        (by simp [h0 k]) hB
        (fun x hx => ih (k + 1) x (Ico_subset_Icc_self hx))
      exact this
  have hn : ∀ n : ℕ, ‖φ 0 1‖ ^ 2 ≤ b * (a ^ n / n.factorial) := by
    intro n
    have h := key n 0 1 (by simp)
    simp only [zero_add, one_pow, mul_one] at h
    have hX : 0 ≤ b * a ^ n * n.factorial := le_trans (by positivity) (hb n 1)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [div_pow, hM, Real.sq_sqrt hX] at h2
    refine h2.trans (le_of_eq ?_)
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have ht : Tendsto (fun n : ℕ => b * (a ^ n / n.factorial)) atTop (𝓝 (b * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop a).const_mul b
  rw [mul_zero] at ht
  have hle : ‖φ 0 1‖ ^ 2 ≤ 0 := ge_of_tendsto' ht hn
  have : ‖φ 0 1‖ = 0 := by nlinarith [norm_nonneg (φ 0 1)]
  exact norm_eq_zero.mp this

end GlobalTheory
end
