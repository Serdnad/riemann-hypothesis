module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle066
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle026
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace EuclideanSections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact mul_mem (hs c hc) (ht c hc)

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {s : Ω}
    {c c' : ℝ} (hs : IsBoundedH P y A τ c s) (hc : c ≤ c') : IsBoundedH P y A τ c' s := by
  intro dg dh g h z hg hh hd he hz
  refine (hs dg dh g h z hg hh hd he hz).trans ?_
  have h0 : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg (eval z (map (Int.castRingHom ℂ) h)))) h0

theorem eventually_shift_le (D m : ℕ) (b E δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n ≤ N → N ≤ n + m →
      b * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) + E * ((N : ℝ) + 1) ^ D ≤
        (b + δ) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF0 : 0 < F := by positivity
  have hlin : ∀ c : ℝ, (fun n : ℕ => (n : ℝ) + c) ~[atTop] fun n : ℕ => (n : ℝ) := fun c =>
    IsEquivalent.refl.add_isLittleO ((isLittleO_const_id_atTop c).comp_tendsto tendsto_natCast_atTop_atTop)
  have hu : (fun n : ℕ => ((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := (hlin m).pow (D + 1)
  have hv : (fun n : ℕ => ((n : ℝ) + (m + 1)) ^ D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    ((hlin (m + 1)).pow D).isBigO.trans_isLittleO
      ((isLittleO_pow_pow_atTop_of_lt (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop)
  set c₁ := δ / (2 * (|b| + 1)) with hc₁
  set c₂ := δ / (2 * F * (|E| + 1)) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  have hbc : |b| * c₁ ≤ δ / 2 := by
    rw [hc₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg b]
  have hEc : F * (|E| * c₂) ≤ δ / 2 := by
    rw [hc₂, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg E]
  filter_upwards [hu.def hc₁0, hv.def hc₂0] with n h1 h2
  intro N hnN hNn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hN1 : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN2 : (N : ℝ) ≤ n + m := by exact_mod_cast hNn
  have hw : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
  have hpow : (N : ℝ) ^ (D + 1) ≤ ((n : ℝ) + m) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hN2 _
  have hpow' : (n : ℝ) ^ (D + 1) ≤ (N : ℝ) ^ (D + 1) := pow_le_pow_left₀ hn0 hN1 _
  have hv' : ((N : ℝ) + 1) ^ D ≤ ((n : ℝ) + (m + 1)) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by linarith)] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by positivity)] at h2
  have hb : b * (N : ℝ) ^ (D + 1) ≤
      b * (n : ℝ) ^ (D + 1) + |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) := by
    rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg hb]; nlinarith
    · nlinarith [abs_nonneg b, mul_le_mul_of_nonpos_left hpow' hb]
  have hE : E * ((N : ℝ) + 1) ^ D ≤ |E| * ((n : ℝ) + (m + 1)) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hv' (abs_nonneg E))
  have hb2 : |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) ≤ δ / 2 * (n : ℝ) ^ (D + 1) :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg b)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbc hw)
  have hE2 : |E| * F * ((n : ℝ) + (m + 1)) ^ D ≤ δ / 2 * (n : ℝ) ^ (D + 1) := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg E) hF0.le)
    nlinarith [mul_le_mul_of_nonneg_right hEc hw]
  have key : b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D) ≤ (b + δ) * (n : ℝ) ^ (D + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hE hF0.le]
  rw [show b * ((N : ℝ) ^ (D + 1) / F) + E * ((N : ℝ) + 1) ^ D =
      (b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D)) / F by field_simp, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right key hF0.le

end EuclideanSections


open EuclideanSections in
theorem EuclideanSections.proof (hP : EuclideanSectionsPower.Statement) (hS : SmallSectionsNonzero.Statement)
    (hL : SublatticeDegree.Statement) (hG : SuccessiveMinimaSpan.Statement) : EuclideanSections.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hconj
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hcon, ⟨Cr, hr⟩, m, hm, hdeg⟩ :=
    hP K ι Ω y D A P0 II hD hII har hb hA hconj
  obtain ⟨C, hC⟩ := hG K ι Ω y D A P0 hD har hb hA
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, ⟨Cr, hr⟩, fun ε hε => ?_⟩
  set C₁ := max C 1 with hC₁
  have hC₁1 : (1 : ℝ) ≤ C₁ := le_max_right _ _
  have hlog : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁1
  set I := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hI
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hdeg (ε / 2) (half_pos hε))
  filter_upwards [eventually_shift_le D m (I + ε / 2) (Cr * Real.log C₁) (ε / 2) (half_pos hε),
    eventually_ge_atTop (m * Q)] with n hn hnQ
  intro _ _
  have hqQ : Q ≤ n / m + 1 := Nat.le_succ_of_le ((Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hnQ))
  have hnN : n ≤ m * (n / m + 1) := (Nat.lt_mul_div_succ n hm).le
  have hNn : m * (n / m + 1) ≤ n + m := by
    have := Nat.mul_div_le n m
    rw [mul_add, mul_one]
    omega
  suffices main : ∀ N : ℕ, n ≤ N → N ≤ n + m →
      -Real.log (ZLattice.covolume (imageLattice (φ N))) ≤
        (I + ε / 2) * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) →
      -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
        (I + ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) from
    main _ hnN hNn (hQ (n / m + 1) hqQ)
  intro N hnN hNn h1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnN
  obtain ⟨t, ht, ht0, hts⟩ := hS K ι Ω y D A P0 har hb hA j

  let ψ : chartLat y A.a n →+ chartLat y A.a (n + j) :=
    { toFun := fun s => ⟨(s : Ω) * t, mul_mem_chartLat s.2 ht⟩
      map_zero' := by ext; simp
      map_add' := fun s s' => by ext; simp [add_mul] }
  have hψ : Function.Injective ψ := fun s s' h =>
    Subtype.ext (mul_right_cancel₀ ht0 (congrArg Subtype.val h))
  have hψn : ∀ s, ‖φ (n + j) (ψ s)‖ ≤ ‖φ n s‖ := fun s => hcon n j s ⟨t, ht⟩ (ψ s) hts rfl

  have hclos : AddSubgroup.closure
      {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro x
    have hx : (x : Ω) ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s} := by
      rw [hC (n + j)]; exact x.2
    have key : ∀ z (hz : z ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s}),
        ∃ hz' : z ∈ chartLat y A.a (n + j), (⟨z, hz'⟩ : chartLat y A.a (n + j)) ∈ AddSubgroup.closure
          {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz => exact ⟨hz.1, AddSubgroup.subset_closure (isBoundedH_mono hz.2 (le_max_left _ _))⟩
      | zero => exact ⟨zero_mem _, zero_mem _⟩
      | add z w _ _ hz hw =>
        obtain ⟨hz', hz''⟩ := hz
        obtain ⟨hw', hw''⟩ := hw
        exact ⟨add_mem hz' hw', add_mem hz'' hw''⟩
      | neg z _ hz =>
        obtain ⟨hz', hz''⟩ := hz
        exact ⟨neg_mem hz', neg_mem hz''⟩
    obtain ⟨_, hx'⟩ := key x hx
    exact hx'
  have hbound : ∀ s ∈ {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)},
      ‖φ (n + j) s‖ ≤ C₁ := fun s hs => hsup (n + j) C₁ s (by linarith) hs
  have h2 := hL (chartLat y A.a (n + j)) (chartLat y A.a n) (r (n + j)) (r n) (φ (n + j)) (φ n) ψ _ C₁
    (hinj _) (hinj _) hψ hψn hclos hbound hC₁1
  have h3 : (r (n + j) : ℝ) * Real.log C₁ ≤ Cr * Real.log C₁ * (((n + j : ℕ) : ℝ) + 1) ^ D := by
    have := mul_le_mul_of_nonneg_right (hr (n + j)) hlog
    linarith
  have h4 := hn (n + j) (Nat.le_add_right n j) hNn
  have h5 : I + ε / 2 + ε / 2 = I + ε := by ring
  rw [h5] at h4
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VeroneseGraphImage.proof : VeroneseGraphImage.Statement := by
  intro D

  let f₀ : MRing (GlobalTheory (Fin (D + 1))) →+* Veronese.Fld D :=
    (Veronese.polyMap D).comp
      (rename (fun p : Σ _ : Unit, Fin (D + 1) => p.2) : MvPolynomial _ ℤ →ₐ[ℤ] _).toRingHom
  have hf₀ : Function.Injective f₀ := by
    refine (Veronese.polyMap_injective D).comp (rename_injective _ ?_)
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  have hf₀X : ∀ i, f₀ (X ⟨(), i⟩) = Veronese.t D i := by
    intro i
    simp [f₀, Veronese.polyMap, Veronese.t]
  let P : Ideal (MRing (GlobalTheory (Fin (D + 1)))) := ⊥
  let φ : MRing (GlobalTheory (Fin (D + 1))) ⧸ P →+* Veronese.Fld D :=
    Ideal.Quotient.lift P f₀ fun a ha => by
      rw [Ideal.mem_bot] at ha
      simp [ha]
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a = 0 := hf₀ (by rw [map_zero]; exact (Ideal.Quotient.lift_mk _ _ _).symm.trans ha)
    rw [this, map_zero]

  let ψ : Polynomial (Veronese.Fld D) →+* MvPolynomial Unit (Veronese.Fld D) :=
    Polynomial.eval₂RingHom C (X ())
  let ev : MvPolynomial Unit (Veronese.Fld D) →+* Polynomial (Veronese.Fld D) :=
    eval₂Hom Polynomial.C fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p
  let G : MRing (GlobalTheory (Veronese.Idx D)) →+* MvPolynomial Unit (Veronese.Fld D) :=
    (MvPolynomial.map φ).comp ((graphMap P (Veronese.forms D)).comp
      (rename (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) :
        MRing (GlobalTheory (Veronese.Idx D)) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ (Veronese.x D) f) := by
    have h : G = ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun
          (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom).comp C)) n
      · rintro ⟨u, q⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          rename_X]
        rw [show (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D)) ⟨(), q⟩) = ⟨Sum.inr (), q⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk P (Veronese.forms D ⟨(), q⟩)) = Veronese.x D ⟨(), q⟩ from by
          rw [Ideal.Quotient.lift_mk]
          simp only [Veronese.forms, map_mul, hf₀X, Veronese.x]]
        simp [ψ]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap P (Veronese.forms D)) ↔
    f ∈ RingHom.ker (coneMap ℤ (Veronese.x D))
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap P (Veronese.forms D) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ (Veronese.x D) f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace VeroneseGraphDeg

theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

def xc {D : ℕ} (i : Fin (D + 1)) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k := ⟨Sum.inl (), i⟩

def yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k :=
  ⟨Sum.inr (), ⟨(i, j), h⟩⟩

abbrev Γ (D : ℕ) : Ideal (MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) :=
  graphIdeal ⊥ (Veronese.forms D)

theorem graphMap_xc {D : ℕ} (i : Fin (D + 1)) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (xc i)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩)) :=
  eval₂Hom_X' _ _ _

theorem graphMap_yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (yc i j h)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩ * X ⟨(), j⟩)) * X () :=
  eval₂Hom_X' _ _ _

theorem rel_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∈ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_xc, graphMap_xc, graphMap_yc,
    graphMap_yc]
  simp only [map_mul]
  ring

theorem veroneseFirstCoordinate_not_mem_graph (D : ℕ) :
    (X (yc 0 0 le_rfl) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_yc]
  refine mul_ne_zero ?_ (X_ne_zero _)
  rw [Ne, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)

theorem x_not_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc i) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_xc, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero _

theorem x'_ne_zero {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (p : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k) (hp : (X p : MRing _) ∉ Γ D) :
    G.x' p ≠ 0 := by
  intro h
  apply hp
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
  exact h

theorem ratio_mem {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (i : Fin (D + 1)) : G.x' (xc i) / G.x' (xc 0) ∈ (⊥ : IntermediateField G.Φ G.Φ') := by
  have h0 := x'_ne_zero G _ (x_not_mem D 0)
  have h00 := x'_ne_zero G _ (veroneseFirstCoordinate_not_mem_graph D)
  have hr : aeval G.x' (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) = 0 := by
    rw [← RingHom.mem_ker, G.genericFibre_ker_target]
    exact rel_mem D i
  simp only [map_sub, map_mul, aeval_X, sub_eq_zero] at hr
  have c1 : G.x' (yc 0 i (Fin.zero_le i)) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩) :=
    G.compat ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩
  have c2 : G.x' (yc 0 0 le_rfl) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩) :=
    G.compat ⟨(), ⟨(0, 0), le_rfl⟩⟩
  rw [IntermediateField.mem_bot]
  refine ⟨G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩ / G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩, ?_⟩
  rw [map_div₀, ← c1, ← c2, div_eq_div_iff h00 h0]
  rw [mul_comm] at hr
  rw [hr, mul_comm]

end VeroneseGraphDeg


open VeroneseGraphDeg in
theorem VeroneseGraphDeg.proof (hGr : GraphStatement) (hImg : VeroneseGraphImage.Statement)
    (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    VeroneseGraphDeg.Statement := by
  intro D hD
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have hnv : ∀ u : Unit, ∃ j, Veronese.forms D ⟨u, j⟩ ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) := by
    intro u
    refine ⟨⟨(0, 0), le_rfl⟩, ?_⟩
    rw [Ideal.mem_bot]
    exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)
  have hΓ : IsArithVar (Γ D) (D + 1) :=
    (hGr Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D) (fun _ _ => 2) hP
      (isMultiHomog_forms D) hnv).1
  have hIm : IsArithVar (imageZ (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D)) (D + 1) := by
    rw [Γ, hImg D]
    exact VeroneseArith.proof D hD
  have : (Γ D).IsPrime := hΓ.2.1.1
  let G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D) := Inter.genFibreOf _ _
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory (Veronese.Idx D)) (Unit ⊕ Unit) (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr
      inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  let ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) →
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k := fun
    | ⟨Sum.inl _, _⟩ => (0 : Fin (D + 1))
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(u | u), h⟩
    · cases u
      exact x'_ne_zero G _ (x_not_mem D 0)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(u | u), h⟩, i⟩, rfl⟩
    · cases u
      exact ratio_mem G i
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end
