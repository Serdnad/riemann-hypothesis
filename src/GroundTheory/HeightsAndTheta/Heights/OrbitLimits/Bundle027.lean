module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle023
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section

namespace CurveVerticalPointSurjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ringHom_aeval {A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] (f : A →+* A')
    (z : (Σ k, ι k) → A) (g : MRing ι) : f (aeval z g) = aeval (fun p => f (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; rw [eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap_homog y hg, mul_eq_zero, C_eq_zero]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ}
    (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) (hg : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) (h : aeval y f = aeval y g) :
    f - g ∈ mCoordIdeal y := by
  rw [mem_mCoordIdeal_iff y (homog_sub hf hg), map_sub, h, sub_self]


omit [Fintype K] in
theorem homogD {f : MRing ι} {a b : K → ℕ} (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (h : a = b) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b :=
  h ▸ hf


omit [∀ k, Fintype (ι k)] in
theorem prod_pow_add {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e₁ e₂ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e₁ + e₂) k = (∏ k, y ⟨k, c k⟩ ^ e₁ k) * ∏ k, y ⟨k, c k⟩ ^ e₂ k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]


omit [∀ k, Fintype (ι k)] in
theorem chartMon_notMem {Q : Ideal (MRing ι)} (hQ : Q.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ Q) (n : K → ℕ) : chartMon c n ∉ Q := by
  intro h
  rw [chartMon] at h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ)).mp h
  exact hc k (hQ.mem_of_pow_mem _ hk)

theorem exists_form {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (b : curveRing y) :
    ∃ (e : K → ℕ) (g : MRing ι), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e ∧ aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k :=
  exists_form_of_mem_chartRingZ y c hc (mem_curveRing.mp b.2 c hc)

def formSet {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (Q : Ideal (MRing ι)) :
    Set (curveRing y) :=
  {b | ∃ (e : K → ℕ) (g : MRing ι), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e ∧
    aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q}

def formIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (Q : Ideal (MRing ι)) : Ideal (curveRing y) where
  carrier := formSet y c Q
  add_mem' := by
    classical
    rintro b₁ b₂ ⟨e₁, g₁, hg₁, hv₁, hQ₁⟩ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    refine ⟨e₁ + e₂, g₁ * chartMon c e₂ + g₂ * chartMon c e₁,
      homog_add (homog_mul hg₁ (homog_chartMon c e₂))
        (homogD (homog_mul hg₂ (homog_chartMon c e₁)) (add_comm _ _)), ?_,
      Q.add_mem (Q.mul_mem_right _ hQ₁) (Q.mul_mem_right _ hQ₂)⟩
    rw [map_add (f := _), map_mul, map_mul, aeval_chartMon, aeval_chartMon, hv₁, hv₂, prod_pow_add,
      Subring.coe_add]
    ring
  zero_mem' := ⟨0, 0, homog_zero _, by simp, Q.zero_mem⟩
  smul_mem' := by
    rintro b b₂ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine ⟨e + e₂, h * g₂, homog_mul hh hg₂, ?_, Q.mul_mem_left _ hQ₂⟩
    rw [map_mul, hv, hv₂, prod_pow_add, smul_eq_mul, Subring.coe_mul]
    ring

theorem mem_formIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {hc : ∀ k, y ⟨k, c k⟩ ≠ 0}
    {Q : Ideal (MRing ι)} {b : curveRing y} :
    b ∈ formIdeal y c hc Q ↔ ∃ (e : K → ℕ) (g : MRing ι), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e ∧
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q :=
  Iff.rfl

theorem le_of_minimal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hfin : Module.Finite ℤ (curveRing y)) (m : Ideal (curveRing y)) (hm : m.IsMaximal)
    (W Q : Ideal (MRing ι)) (hQ : Q.IsPrime) (hPQ : mCoordIdeal y ≤ Q) (hQW : Q ≤ W)
    (hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hWB : ∀ {g : MRing ι} {e : K → ℕ} (b : curveRing y), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ W ↔ b ∈ m))
    (hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n → f ∈ W →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧ (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k)
    (hWforms : IsMultiHomogIdeal W) {a b : curveRing y} (ha0 : a ≠ 0) {s : MRing ι} {d : K → ℕ}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d) (hsQ : s ∈ Q) (hbx : (b : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k) :
    W ≤ Q := by
  classical
  have hmonQ : ∀ n, chartMon c n ∉ Q := chartMon_notMem hQ fun k h => hXc k (hQW h)
  have htr : ∀ {f g : MRing ι} {n : K → ℕ}, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g n →
      aeval y f = aeval y g → g ∈ Q → f ∈ Q := by
    intro f g n hf hg he hgQ
    have h1 := Q.add_mem (hPQ (sub_mem_mCoordIdeal y hf hg he)) hgQ
    rwa [sub_add_cancel] at h1
  have hIQm : formIdeal y c hc Q ≤ m := by
    intro x hx
    obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp hx
    exact (hWB x hg hv).mp (hQW hgQ)
  have haIQ : a ∈ formIdeal y c hc Q := by
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine mem_formIdeal.mpr ⟨e + d, h * s, homog_mul hh hs, ?_, Q.mul_mem_left _ hsQ⟩
    rw [map_mul, hv, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ e k) * hbx
  have hIQprime : (formIdeal y c hc Q).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      intro h1
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h1
      refine hmonQ e (htr (homog_chartMon c e) hg ?_ hgQ)
      rw [aeval_chartMon, hv]
      simp
    · intro x₁ x₂ h12
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h12
      obtain ⟨e₁, h₁, hh₁, hv₁⟩ := exists_form y c hc x₁
      obtain ⟨e₂, h₂, hh₂, hv₂⟩ := exists_form y c hc x₂
      have hf : h₁ * h₂ * chartMon c e ∈ Q := by
        refine htr (homog_mul (homog_mul hh₁ hh₂) (homog_chartMon c e))
          (homogD (homog_mul hg (homog_chartMon c (e₁ + e₂))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (e₁ + e₂)) hgQ)
        simp only [map_mul, aeval_chartMon, hv₁, hv₂, hv, prod_pow_add, Subring.coe_mul]
        ring
      rcases hQ.mem_or_mem hf with h12 | h3
      · rcases hQ.mem_or_mem h12 with h1Q | h2Q
        · exact Or.inl (mem_formIdeal.mpr ⟨e₁, h₁, hh₁, hv₁, h1Q⟩)
        · exact Or.inr (mem_formIdeal.mpr ⟨e₂, h₂, hh₂, hv₂, h2Q⟩)
      · exact absurd h3 (hmonQ e)
  have hIQmax : (formIdeal y c hc Q).IsMaximal := by
    have : Algebra.IsIntegral ℤ (curveRing y) := Algebra.IsIntegral.of_finite ℤ _
    have hcomap : (formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 haIQ (Algebra.IsIntegral.isIntegral a)
    have : ((formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y))).IsPrime := Ideal.IsPrime.comap _
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (formIdeal y c hc Q)
      (IsPrime.to_maximal_ideal hcomap)
  have hIQeq : formIdeal y c hc Q = m := hIQmax.eq_of_le hm.ne_top hIQm

  obtain ⟨S, hS, hWS⟩ := hWforms
  intro f hfW
  rw [hWS] at hfW
  refine (Ideal.span_le.mpr ?_) hfW
  intro f hf
  obtain ⟨δ, hδ⟩ := hS f hf
  have hfW' : f ∈ W := by rw [hWS]; exact Ideal.subset_span hf
  obtain ⟨a', b', ha'm, hb'm, hv'⟩ := hWfrac hδ hfW'
  have ha'IQ : a' ∈ formIdeal y c hc Q := by rw [hIQeq]; exact ha'm
  obtain ⟨ea, ga, hga, hva, hgaQ⟩ := mem_formIdeal.mp ha'IQ
  obtain ⟨eb, hb, hhb, hvb⟩ := exists_form y c hc b'
  have hbQ : hb ∉ Q := by
    intro h
    have hbIQ : b' ∈ formIdeal y c hc Q := mem_formIdeal.mpr ⟨eb, hb, hhb, hvb, h⟩
    rw [hIQeq] at hbIQ
    exact hb'm hbIQ
  have h1 : hb * f * chartMon c ea ∈ Q := by
    refine htr (homog_mul (homog_mul hhb hδ) (homog_chartMon c ea))
      (homogD (homog_mul hga (homog_chartMon c (eb + δ))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (eb + δ)) hgaQ)
    simp only [map_mul, aeval_chartMon, hvb, hva, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ eb k) * (∏ k, y ⟨k, c k⟩ ^ ea k) * hv'
  rcases hQ.mem_or_mem h1 with h2 | h3
  · rcases hQ.mem_or_mem h2 with h4 | h5
    · exact absurd h4 hbQ
    · exact h5
  · exact absurd h3 (hmonQ ea)

theorem locLen_quot_eq_zero {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime] {a : R} (ha : a ∉ m) :
    locLen m (R ⧸ Ideal.span {a}) = 0 := by
  have key : ∀ w : LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}), w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h x t =>
      rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨a, ha⟩, ?_⟩
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  have hsub : Subsingleton (LocalizedModule m.primeCompl (R ⧸ Ideal.span {a})) :=
    ⟨fun u v => by rw [key u, key v]⟩
  rw [locLen, dite_eq_left ‹m.IsPrime›, Module.length_eq_zero_iff.mpr hsub]
  rfl

end CurveVerticalPointSurjective

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ConeSliceIdeal.proof : ConeSliceIdeal.Statement := by
  intro n C t V hC hV f hf
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  obtain ⟨G, D, hG, hGf⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) f hℓ
  have hLG : linForm t * G ∈ V := by
    refine hV ?_
    rw [mem_vanishingIdeal_iff]
    intro c hc
    show eval c (linForm t * G) = 0
    rw [map_mul]
    by_cases hl : eval c (linForm t) = 0
    · rw [hl, zero_mul]
    · set l := eval c (linForm t)
      have hsl : eval (l⁻¹ • c) (linForm t) = 1 := by
        rw [GoodChartZeroSet.eval_smul_of_isHomogeneous hℓ, pow_one, inv_mul_cancel₀ hl]
      have hmem : l⁻¹ • c ∈ {x | x ∈ C ∧ eval x (linForm t) = 1} :=
        ⟨hC c hc _ (inv_ne_zero hl), hsl⟩
      have hf0 : eval (l⁻¹ • c) f = 0 := (mem_vanishingIdeal_iff.mp hf) _ hmem
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hGf
      have hGv : eval (l⁻¹ • c) G = 0 := by
        have h := congrArg (eval (l⁻¹ • c)) hq
        rw [map_sub, map_mul, map_sub, hsl, hf0, map_one] at h
        simpa using h
      have hc' : c = l • (l⁻¹ • c) := by rw [smul_smul, mul_inv_cancel₀ hl, one_smul]
      rw [hc', GoodChartZeroSet.eval_smul_of_isHomogeneous hG, hGv, mul_zero, mul_zero]
  have e : f = linForm t * G - (linForm t - 1) * G - (G - f) := by ring
  rw [e]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mem_sup_left hLG) ?_) (Ideal.mem_sup_right hGf)
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

theorem ConeVanishingHomog.proof : ConeVanishingHomog.Statement := by
  intro n C hC f hf d
  rw [mem_vanishingIdeal_iff] at hf ⊢
  intro c hc
  replace hf : ∀ x ∈ C, eval x f = 0 := hf
  show eval c (homogeneousComponent d f) = 0

  set p : Polynomial ℂ := ∑ i ∈ range (f.totalDegree + 1),
    Polynomial.C (eval c (homogeneousComponent i f)) * Polynomial.X ^ i with hp
  have hroot : ∀ a : ℂ, a ≠ 0 → p.IsRoot a := by
    intro a ha
    have h0 := hf (a • c) (hC c hc a ha)

    rw [← sum_homogeneousComponent f, map_sum] at h0
    rw [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GoodChartZeroSet.eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i f)]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hinf : Set.Infinite {x | p.IsRoot x} := by
    refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_
      (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    exact hroot x (by simpa using hx)
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hinf
  by_cases hd : d ≤ f.totalDegree
  · have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hp0
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_ite_eq] at hcoeff
    simpa [Finset.mem_range, Nat.lt_succ_of_le hd] using hcoeff
  · rw [homogeneousComponent_eq_zero d f (by omega), map_zero]

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)

theorem ptsPosDens_split {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) → ∀ z ∈ mcPts P, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (ptsPosDens P Ψ φ g y) =
      ∑' k, ENNReal.ofReal (ptsPosDens P Ψ φ ((E k).indicator g) y) := by
  classical
  unfold ptsPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (sheetDensity P Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (sheetDensity P Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (sheetDensity P Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSheet P Ψ y w γ
    · have hz : hs.choose y ∈ mcPts P := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [sheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [sheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [sheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

theorem PtsPosPartProjIndep.proof (hS : PtsSheetSimpleNull.Statement) (hO : PtsSheetOnlyNull.Statement)
    (hL : PtsPosPartLocal.Statement) (hM : PtsPosDensMeasurable.Statement) :
    PtsPosPartProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Q : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ mcPts P ∧
    IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hQ
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Q z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Q z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := hL K ι P e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [ptsPosDens, sheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Q z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B → IsGoodProj P B' →
      (∀ z ∈ mcPts P, IsSimpleSheetPt P B ((B (segre z) 0)⁻¹ • segre z) →
        IsSimpleSheetPt P B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (hS K ι P e B hP hB) (hO K ι P e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine ptsPosDens_split _ _ E y (fibreFinite K ι P e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : IsSimpleSheetPt P B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : IsSimpleSheetPt P B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B →
      (∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (hM K ι P e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveIndexLinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    IsArithVar (mCoordIdeal y) 1 → (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ a a' : K → ℤ, chartIndexLog y c (a + a') 1 = chartIndexLog y c a 1 + chartIndexLog y c a' 1) ∧
      ∀ (a : K → ℤ) (τ : ℕ), chartIndexLog y c a τ = τ * chartIndexLog y c a 1

namespace CurveIndexLinear

end CurveIndexLinear

end GroundTheory.Heights₂.Heights.Targets
end
