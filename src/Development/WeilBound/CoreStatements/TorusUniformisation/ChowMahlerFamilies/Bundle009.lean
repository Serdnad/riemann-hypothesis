module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle005
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.PointOverExistence

theorem exists_algHom (F R : Type) [Field F] [CommRing R] [Nontrivial R] [Algebra F R]
    [Algebra.FiniteType F R] [Algebra F ℂ] : Nonempty (R →ₐ[F] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (R ⧸ m)
  exact ⟨(IsAlgClosed.lift : (R ⧸ m) →ₐ[F] ℂ).comp (Ideal.Quotient.mkₐ F m)⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem scale {S : Type} [CommRing S] (t : K → S) (u : (Σ k, ι k) → S) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    aeval (fun p : Σ k, ι k => t p.1 * u p) g = (∏ k, t k ^ d k) * aeval u g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h : ∏ p : Σ k, ι k, t p.1 ^ m p = ∏ k, t k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hg m hm k]
    exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m ⟨k, i⟩) (t k)
  simp only [mul_pow, Finset.prod_mul_distrib, h]
  ring

theorem map_aeval' {S T : Type} [CommRing S] [CommRing T] (j : S →+* T) (u : (Σ k, ι k) → S)
    (g : MRing ι) : j (aeval u g) = aeval (fun p => j (u p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, aeval_X]

theorem evC_eq (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p i hp => simp only [evC, map_mul, map_X, eval_X, aeval_X] at *; rw [hp]

variable {Ω : Type} [Field Ω]

theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) : mConeMap y g =
    @aeval ℤ (MvPolynomial K Ω) _ _ _ (Ring.toIntAlgebra _) (fun p : Σ k, ι k => X p.1 * C (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, mConeMap, aeval_X, mul_comm (C _)]

theorem aeval_ne_zero {y : (Σ k, ι k) → Ω} {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hn : g ∉ mCoordIdeal y) : aeval y g ≠ 0 := by
  intro h0
  apply hn
  have h := scale (S := MvPolynomial K Ω) (fun k => X k) (fun p => C (y p)) hg
  rw [← map_aeval' (C : Ω →+* MvPolynomial K Ω) y g, h0, map_zero, mul_zero] at h
  show mConeMap y g = 0
  rw [cone_eq, h]

theorem aeval_eq_zero {y : (Σ k, ι k) → Ω} (t : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, ι k => t p.1 * y p) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h := map_aeval' (eval t : MvPolynomial K Ω →+* Ω)
    (fun p : Σ k, ι k => X p.1 * C (y p)) f
  rw [← cone_eq, h0, map_zero] at h
  rw [h]
  simp only [map_mul, eval_C, eval_X]

end PositivityTheory.Xgn.PointOverExistence

open PositivityTheory.Xgn.PointOverExistence in
theorem PositivityTheory.Xgn.exists_point_over_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (g : MRing ι) (d : K → ℕ), OverInt y φ → IsMultiHomog g d → g ∉ mCoordIdeal y → ∃ z, PtOver y φ σ z ∧ evC z g ≠ 0 := by
  intro K _ ι _ Ω _ F _ _ y φ σ g d hO hg hn
  choose c hc using hO.1
  letI : Algebra F Ω := φ.toAlgebra
  letI : Algebra F ℂ := σ.toAlgebra
  let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  let w : (Σ k, ι k) → Ω := fun p => t p.1 * y p
  have hγ : aeval w g ≠ 0 := by
    rw [scale t y hg]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k)))
      (aeval_ne_zero hg hn)
  let A : Subalgebra F Ω := Algebra.adjoin F (insert (aeval w g)⁻¹ (Set.range w))
  haveI : Algebra.FiniteType F A :=
    Algebra.FiniteType.adjoin_of_finite ((Set.finite_range w).insert _)
  obtain ⟨ψ⟩ := exists_algHom F A
  let wA : (Σ k, ι k) → A := fun p => ⟨w p, Algebra.subset_adjoin (Or.inr ⟨p, rfl⟩)⟩
  let δ : A := ⟨(aeval w g)⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩
  have hco : ∀ f : MRing ι, ((aeval wA f : A) : Ω) = aeval w f := fun f =>
    map_aeval' (A.val : A →+* Ω) wA f
  have hev : ∀ f : MRing ι, evC (fun p => ψ (wA p)) f = ψ (aeval wA f) := fun f => by
    rw [evC_eq]
    exact (map_aeval' (ψ : A →+* ℂ) wA f).symm
  refine ⟨fun p => ψ (wA p), ⟨⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩, fun a e f h hf hh H => ?_⟩, ?_⟩
  · have : wA ⟨k, c k⟩ = 1 := Subtype.ext (inv_mul_cancel₀ (hc k))
    simp only [this, map_one]
    exact one_ne_zero
  · have : aeval wA f = 0 := Subtype.ext ((hco f).trans (aeval_eq_zero t hf))
    exact (hev f).trans (by rw [this, map_zero])
  · have : aeval wA f = algebraMap F A a * aeval wA h := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hco, hco, scale t y hf, scale t y hh, H]
      show _ = φ a * _
      ring
    rw [hev, hev, this, map_mul, ψ.commutes]
    rfl
  · have : aeval wA g * δ = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hco]
      exact mul_inv_cancel₀ hγ
    rw [hev]
    exact left_ne_zero_of_mul_eq_one (b := ψ δ) (by rw [← map_mul, this, map_one])
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.RepresentativeAvoidance

section General

variable {σ M R : Type*} [CommRing R] [AddCommGroup M] (w : σ → M)

theorem comp_mul (u f : MvPolynomial σ R) (d n : M) (hf : IsWeightedHomogeneous w f d) :
    weightedHomogeneousComponent w (n + d) (u * f) = weightedHomogeneousComponent w n u * f := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial s a =>
    have h1 : IsWeightedHomogeneous w (monomial s a : MvPolynomial σ R) (Finsupp.weight w s) :=
      isWeightedHomogeneous_monomial w s a rfl
    have h2 := h1.mul hf
    by_cases hn : n = Finsupp.weight w s
    · subst hn
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne n hn,
        h2.weightedHomogeneousComponent_ne (n + d) (fun h => hn (add_right_cancel h)), zero_mul]
  | add p q hp hq => rw [add_mul, map_add (f := _), map_add (f := _), hp, hq, add_mul]

theorem comp_mem_span (S : Set (MvPolynomial σ R))
    (hS : ∀ f ∈ S, ∃ d, IsWeightedHomogeneous w f d) (x : MvPolynomial σ R)
    (hx : x ∈ Ideal.span S) (n : M) : weightedHomogeneousComponent w n x ∈ Ideal.span S := by
  have key : ∀ r n, weightedHomogeneousComponent w n (r * x) ∈ Ideal.span S := by
    induction hx using Submodule.span_induction with
    | mem x h =>
      intro r n
      obtain ⟨d, hd⟩ := hS x h
      have := comp_mul w r x d (n - d) hd
      rw [sub_add_cancel] at this
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span h)
    | zero => intro r n; simp
    | add x y _ _ hx hy => intro r n; rw [mul_add, map_add (f := _)]; exact add_mem (hx r n) (hy r n)
    | smul a x _ hx => intro r n; rw [smul_eq_mul, ← mul_assoc]; exact hx _ n
  simpa using key 1 n

theorem exists_comp_notMem (W : Ideal (MvPolynomial σ R)) (u : MvPolynomial σ R) (hu : u ∉ W) :
    ∃ n, weightedHomogeneousComponent w n u ∉ W := by
  by_contra h
  push Not at h
  apply hu
  rw [← sum_weightedHomogeneousComponent (w := w) u,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp u)]
  exact W.sum_mem fun n _ => h n

end General

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def wt (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun p => Pi.single p.1 1

theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (wt ι) m k = ((∑ i, m ⟨k, i⟩ : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [wt]
  · intro j _ hj
    simp [wt, Pi.single_eq_of_ne hj.symm]
  · simp

theorem wh_of_mh {f : MRing ι} {d : K → ℕ} (h : IsMultiHomog f d) :
    IsWeightedHomogeneous (wt ι) f (fun k => (d k : ℤ)) := by
  intro m hm
  funext k
  rw [weight_wt, h m (mem_support_iff.mpr hm) k]

theorem mh_of_wh {f : MRing ι} {d : K → ℤ} (h : IsWeightedHomogeneous (wt ι) f d) (h0 : f ≠ 0) :
    ∃ e : K → ℕ, IsMultiHomog f e ∧ ∀ k, (e k : ℤ) = d k := by
  obtain ⟨m0, hm0⟩ := exists_coeff_ne_zero h0
  refine ⟨fun k => ∑ i, m0 ⟨k, i⟩, fun m hm k => ?_, fun k => ?_⟩
  · have h1 := congrFun ((h (mem_support_iff.mp hm)).trans (h hm0).symm) k
    rw [weight_wt, weight_wt] at h1
    exact_mod_cast h1
  · rw [← weight_wt, h hm0]

theorem exists_mono (W : Ideal (MRing ι)) (hW : W.IsPrime) (hr : IsRelevant W) (e : K → ℕ) :
    ∃ m : MRing ι, m ∉ W ∧ IsWeightedHomogeneous (wt ι) m (fun k => (e k : ℤ)) := by
  choose c hc using hr
  refine ⟨∏ k, X ⟨k, c k⟩ ^ e k, fun h => ?_, ?_⟩
  · obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k (hW.mem_of_pow_mem _ hk)
  · have := IsWeightedHomogeneous.prod (w := wt ι) Finset.univ
      (fun k => (X ⟨k, c k⟩ : MRing ι) ^ e k) (fun k => e k • wt ι ⟨k, c k⟩)
      (fun k _ => (isWeightedHomogeneous_X ℤ (wt ι) _).pow _)
    convert this using 1
    funext k
    simp [wt, Finset.sum_apply, Pi.single_apply]

theorem exists_pair (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ)
    (hP : IsMultiProjPrime P) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (hf : IsMultiHomog f df)
    (hg : IsMultiHomog g dg) (hu : IsUnitSec P f g) :
    ∃ (U V : MRing ι) (c : K → ℤ), IsWeightedHomogeneous (wt ι) U c ∧
      IsWeightedHomogeneous (wt ι) V (c + ((fun k => (df k : ℤ)) - fun k => (dg k : ℤ))) ∧
      U ∉ W ∧ V ∉ W ∧ U * f - V * g ∈ P := by
  obtain ⟨u, v, hu, hv, huv⟩ := hu W hW.1 hPW hW.2.2
  set δ : K → ℤ := (fun k => (df k : ℤ)) - fun k => (dg k : ℤ) with hδ
  have hpair : ∀ a : K → ℤ, weightedHomogeneousComponent (wt ι) a u * f -
      weightedHomogeneousComponent (wt ι) (a + δ) v * g ∈ P := by
    intro a
    obtain ⟨S, hS, rfl⟩ := hP.2.1
    have := comp_mem_span (wt ι) S (fun x hx => (hS x hx).elim fun d hd => ⟨_, wh_of_mh hd⟩) _ huv
      (a + fun k => (df k : ℤ))
    rw [map_sub, comp_mul _ u f _ a (wh_of_mh hf)] at this
    rw [← comp_mul _ v g _ (a + δ) (wh_of_mh hg)]
    convert this using 4
    rw [hδ]; abel
  have hA : ∀ a, IsWeightedHomogeneous (wt ι) (weightedHomogeneousComponent (wt ι) a u) a :=
    fun a => weightedHomogeneousComponent_isWeightedHomogeneous a u
  have hB : ∀ a, IsWeightedHomogeneous (wt ι) (weightedHomogeneousComponent (wt ι) a v) a :=
    fun a => weightedHomogeneousComponent_isWeightedHomogeneous a v
  obtain ⟨a, ha⟩ := exists_comp_notMem (wt ι) W u hu
  obtain ⟨b, hb⟩ := exists_comp_notMem (wt ι) W v hv
  obtain ⟨a', rfl⟩ : ∃ a', b = a' + δ := ⟨b - δ, by abel⟩
  by_cases h1 : weightedHomogeneousComponent (wt ι) (a + δ) v ∈ W
  swap
  · exact ⟨_, _, a, hA a, hB _, ha, h1, hpair a⟩
  by_cases h2 : weightedHomogeneousComponent (wt ι) a' u ∈ W
  swap
  · exact ⟨_, _, a', hA a', hB _, h2, hb, hpair a'⟩
  obtain ⟨m, hm, hmd⟩ := exists_mono W hW.1 hW.2.2 (fun k => (a' k - a k).toNat)
  obtain ⟨m', hm', hmd'⟩ := exists_mono W hW.1 hW.2.2 (fun k => (a k - a' k).toNat)
  have he : (fun k => (((a k - a' k).toNat : ℕ) : ℤ)) + a' =
      (fun k => (((a' k - a k).toNat : ℕ) : ℤ)) + a := by
    funext k
    simp only [Pi.add_apply]
    omega
  refine ⟨m * weightedHomogeneousComponent (wt ι) a u + m' * weightedHomogeneousComponent (wt ι) a' u,
    m * weightedHomogeneousComponent (wt ι) (a + δ) v +
      m' * weightedHomogeneousComponent (wt ι) (a' + δ) v,
    (fun k => (((a' k - a k).toNat : ℕ) : ℤ)) + a, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hmd.mul (hA a)).add (he ▸ hmd'.mul (hA a'))
  · refine IsWeightedHomogeneous.add ?_ ?_
    · rw [add_assoc]; exact hmd.mul (hB _)
    · rw [← he, add_assoc]; exact hmd'.mul (hB _)
  · intro h
    rw [W.add_mem_iff_left (W.mul_mem_left _ h2)] at h
    exact (hW.1.mem_or_mem h).elim hm ha
  · intro h
    rw [W.add_mem_iff_right (W.mul_mem_left _ h1)] at h
    exact (hW.1.mem_or_mem h).elim hm' hb
  · convert add_mem (P.mul_mem_left m (hpair a)) (P.mul_mem_left m' (hpair a')) using 1
    ring

end PositivityTheory.Xgn.RepresentativeAvoidance

theorem PositivityTheory.Xgn.exists_representative_avoiding_ideal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ), IsMultiProjPrime P → IsMultiProjPrime W → P ≤ W → IsMultiHomog f df → IsMultiHomog g dg → g ∉ P → IsUnitSec P f g → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = (df k : ℤ) - dg k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * g - g' * f ∈ P ∧ IsUnitSec P f' g' := by
  intro K _ ι _ P W f g df dg hP hW hPW hf hg hgP hu
  classical
  obtain ⟨U, V, c, hU, hV, hUW, hVW, hUV⟩ :=
    PositivityTheory.Xgn.RepresentativeAvoidance.exists_pair P W f g df dg hP hW hPW hf hg hu
  obtain ⟨eU, heU, hcU⟩ := PositivityTheory.Xgn.RepresentativeAvoidance.mh_of_wh hU
    (fun h => hUW (h ▸ W.zero_mem))
  obtain ⟨eV, heV, hcV⟩ := PositivityTheory.Xgn.RepresentativeAvoidance.mh_of_wh hV
    (fun h => hVW (h ▸ W.zero_mem))
  refine ⟨V, U, eV, eU, heV, heU, fun k => ?_, hVW, hUW, ?_, fun W' hW' hPW' hr => ?_⟩
  · rw [hcU, hcV]; simp
  · convert neg_mem hUV using 1
    ring
  · obtain ⟨u, v, hu', hv', huv⟩ := hu W' hW' hPW' hr
    refine ⟨u, v, hu', hv', (hP.1.mem_or_mem (x := g) ?_).resolve_left hgP⟩
    convert sub_mem (P.mul_mem_left U huv) (P.mul_mem_left u hUV) using 1
    ring
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ValuationOrder

theorem specializes_comp {X : Scheme.{0}} {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S]
    (z : Spec R ⟶ X) (φ : R ⟶ S) :
    (Spec.map φ ≫ z) (IsLocalRing.closedPoint S) ⤳ z (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint
    ((Spec.map φ) (IsLocalRing.closedPoint S))).map z.continuous
  exact (Scheme.Hom.comp_apply (Spec.map φ) z (IsLocalRing.closedPoint S)).symm ▸ h

theorem stalk_comp {X : Scheme.{0}} {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S]
    (z : Spec R ⟶ X) (φ : R ⟶ S) :
    X.presheaf.stalkSpecializes (specializes_comp z φ) ≫ Scheme.stalkClosedPointTo (Spec.map φ ≫ z) =
      Scheme.stalkClosedPointTo z ≫ φ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (z (IsLocalRing.closedPoint R))), Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_spec {p q : X} (hp : genPt ξ ⤳ p) (hpq : p ⤳ q) (s : X.presheaf.stalk q) :
    genMap ξ ⟨p, hp⟩ ((X.presheaf.stalkSpecializes hpq).hom s) = genMap ξ ⟨q, hp.trans hpq⟩ s := by
  have h1 : X.presheaf.stalkSpecializes hpq ≫ X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ =
      X.presheaf.stalkSpecializes (hp.trans hpq) ≫ Scheme.stalkClosedPointTo ξ := by
    rw [← X.presheaf.stalkSpecializes_comp hp hpq]
    exact (Category.assoc _ _ _).symm
  have h2 := congrArg (fun f => CommRingCat.Hom.hom f s) h1
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

theorem valAt_comp {V C : Type} [CommRing V] [IsLocalRing V] [CommRing C] [IsLocalRing C]
    (φ : V →+* C) {z : Spec (CommRingCat.of V) ⟶ X}
    (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) {a : Ω} {r : V} (hv : ValAt ξ z a r) :
    ValAt ξ (Spec.map (CommRingCat.ofHom φ) ≫ z) a (φ r) := by
  obtain ⟨_, s, rfl, rfl⟩ := hv
  refine ⟨h, (X.presheaf.stalkSpecializes (specializes_comp z (CommRingCat.ofHom φ))).hom s,
    genMap_spec h _ s, ?_⟩
  exact congrArg (fun f => f.hom s) (stalk_comp z (CommRingCat.ofHom φ))

section

variable {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') :
    r = r' := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  obtain ⟨_, s', e, rfl⟩ := h'
  rw [hξ.inj ⟨centre z, hz⟩ e]

theorem valAt_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t * t', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_pow {a : Ω} {r : R} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  exact ⟨hz, t ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem ne_zero_of_valAt {a : Ω} {r : R} (h : ValAt ξ z a r) (hr : IsUnit r) : a ≠ 0 := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  have ht : IsUnit t := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit t hr
  exact (ht.map (genMap ξ ⟨centre z, hz⟩)).ne_zero

theorem exists_unit_val (hξ : IsCptGen ξ) {h : genPt ξ ⤳ centre z} {b : Ω} (hb : unitAt ξ ⟨centre z, h⟩ b) :
    ∃ u : Rˣ, ValAt ξ z b u := by
  obtain ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩ := hb
  have h1 : ValAt ξ z b _ := ⟨h, s, hs, rfl⟩
  have h2 : ValAt ξ z b⁻¹ _ := ⟨h, t, ht, rfl⟩
  have h3 := valAt_mul h1 h2
  rw [mul_inv_cancel₀ h0] at h3
  have h4 : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩
  exact ⟨Units.mkOfMulEqOne _ _ (valAt_unique hξ h3 h4), h1⟩

end

end PositivityTheory.Xgn.ValuationOrder

open PositivityTheory.Xgn.ValuationOrder in
theorem PositivityTheory.Xgn.valuation_at_centre_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u := by
  intro X Ω _ ξ L σ ϖ M a V C _ _ _ _ z h e γ π hξ hord hgen hγ hπ hπ0
  have hu : unitAt ξ ⟨centre z, h⟩ ((σ / e) ^ M / ϖ ^ a) := (orderAt_iff_div hgen.1 hgen.2).1 hord
  obtain ⟨u, hval⟩ := exists_unit_val hξ hu
  have hc := valAt_comp (algebraMap V C) hγ.1 hval
  have hϖ : ϖ ≠ 0 := ne_zero_of_valAt hπ hπ0.isUnit
  have hM := valAt_pow hγ M
  refine ⟨u, ?_⟩
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · have h1 := valAt_mul (valAt_pow hπ n) hc
    rw [zpow_natCast, mul_div_cancel₀ _ (pow_ne_zero n hϖ)] at h1
    rw [zpow_natCast]
    exact valAt_unique hξ hM h1
  · have h1 := valAt_mul hM (valAt_pow hπ n)
    rw [zpow_neg, zpow_natCast, div_inv_eq_mul] at hc
    rw [← valAt_unique hξ h1 hc, zpow_neg, zpow_natCast]
    field_simp
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.nonvanishing_points_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof)
end
