module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PowerSeries.Trunc
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormSign

open NumberField.InfinitePlace

variable {K : Type} [Field K] [NumberField K]

noncomputable def snorm (x : mixedSpace K) : ℝ :=
  (∏ w, x.1 w) * ∏ w, ‖x.2 w‖ ^ 2

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.snorm_mul {K : Type} [Field K] [NumberField K]
    (x y : NumberField.mixedEmbedding.mixedSpace K) :
    _root_.GlobalTheory.NormSign.snorm (x * y) = _root_.GlobalTheory.NormSign.snorm x * _root_.GlobalTheory.NormSign.snorm y := by
  simp only [_root_.GlobalTheory.NormSign.snorm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]
  ring

theorem snorm_smul (t : ℝ) (ht : 0 < t) (x : mixedSpace K) :
    ∃ c : ℝ, 0 < c ∧ snorm (t • x) = c * snorm x := by
  refine ⟨(∏ _w : {w : InfinitePlace K // IsReal w}, t) *
    ∏ _w : {w : InfinitePlace K // IsComplex w}, t ^ 2, by positivity, ?_⟩
  simp only [snorm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, _root_.norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow, Finset.prod_mul_distrib]
  ring

theorem continuous_snorm : Continuous (snorm : mixedSpace K → ℝ) := by
  unfold snorm
  fun_prop

theorem abs_snorm (x : mixedSpace K) : |snorm x| = mixedEmbedding.norm x := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, snorm, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (by positivity)]

theorem snorm_mixedEmbedding (x : K) :
    snorm (mixedEmbedding K x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x)
      (fun φ => φ x) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [Complex.ofReal_ratCast, h, ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x),
    prod_eq_prod_mul_prod, snorm, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod]
  have key : ∀ w : InfinitePlace K, (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w)
      = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    intro w
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
      star_involutive.eq_iff]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [key, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp w.2), Finset.pair_eq_singleton,
      Finset.prod_singleton, mixedEmbedding_apply_isReal, embedding_of_isReal_apply]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hne : w.1.embedding ≠ ComplexEmbedding.conjugate w.1.embedding := by
      rw [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
      exact not_isReal_iff_isComplex.mpr w.2
    rw [key, Finset.prod_pair hne, mixedEmbedding_apply_isComplex,
      ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

noncomputable def sgn (ε : ℂ) (t : ℝ) : ℂ := if 0 < t then 1 else if t < 0 then ε else 0

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.sgn_mul {ε : ℂ} (hε : ε * ε = 1) (a b : ℝ) :
    _root_.GlobalTheory.NormSign.sgn ε (a * b) = _root_.GlobalTheory.NormSign.sgn ε a * _root_.GlobalTheory.NormSign.sgn ε b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_pos_of_neg_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, hb.not_gt, hε]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_neg_of_neg_of_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, h.not_gt]
  · simp [_root_.GlobalTheory.NormSign.sgn]
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_neg_of_pos_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, hb.not_gt, h.not_gt]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h]

theorem norm_sgn {ε : ℂ} (hε : ε * ε = 1) {a : ℝ} (ha : a ≠ 0) : ‖sgn ε a‖ = 1 := by
  have h : ‖ε‖ = 1 := by
    rcases mul_self_eq_one_iff.mp hε with h | h <;> simp [h]
  rcases lt_or_gt_of_ne ha with h' | h'
  · simp [sgn, h', h'.not_gt, h]
  · simp [sgn, h']

theorem exists_normSign (K : Type) [Field K] [NumberField K] (ε : ℂ) (hε : ε * ε = 1) :
    ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧
      (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧
      ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧
      (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧
      ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  have hne : ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 → snorm x ≠ 0 := fun x hx => by
    rwa [← abs_snorm, abs_ne_zero] at hx
  refine ⟨fun x => sgn ε (snorm x), fun x y => ?_, fun t x ht => ?_, fun x hx => ?_,
    fun x hx => norm_sgn hε (hne x hx), fun β hβ => ?_⟩
  · simp only [snorm_mul, sgn_mul hε]
  · obtain ⟨c, hc, h⟩ := snorm_smul t ht x
    simp only [h, sgn_mul hε]
    simp [sgn, hc]
  · refine ContDiffAt.contDiffWithinAt ?_
    refine (contDiffAt_const (c := sgn ε (snorm x))).congr_of_eventuallyEq ?_
    rcases lt_or_gt_of_ne (hne x hx) with h | h
    · filter_upwards [continuous_snorm.continuousAt.eventually (gt_mem_nhds h)] with y hy
      simp [sgn, h, hy, h.not_gt, hy.not_gt]
    · filter_upwards [continuous_snorm.continuousAt.eventually (lt_mem_nhds h)] with y hy
      simp [sgn, h, hy]
  · have h0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    simp only [snorm_mixedEmbedding, ← Algebra.coe_norm_int, Rat.cast_intCast, sgn,
      Int.cast_pos, Int.cast_lt_zero]
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [h, h.not_gt]
    · simp [h]

end GlobalTheory.NormSign
end

section

noncomputable section

namespace GlobalTheory.JSW

open PowerSeries

theorem hasSum_coeff_mk_mul_polynomial (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (p : Polynomial ℂ) :
    HasSum (fun d => coeff d (mk c * (p : PowerSeries ℂ))) ((∑' d, c d) * p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [Polynomial.coe_add, mul_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    have hf : (fun d => coeff d (mk c * ((Polynomial.monomial n a : Polynomial ℂ) : PowerSeries ℂ)))
        = fun d => if n ≤ d then c (d - n) * a else 0 := by
      funext d
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc,
        PowerSeries.coeff_mul_X_pow']
      split_ifs <;> simp [PowerSeries.coeff_mul_C]
    rw [hf, Polynomial.eval_monomial, one_pow, mul_one]
    refine (hasSum_nat_add_iff' n).mp ?_
    have h0 : ∑ i ∈ Finset.range n, (if n ≤ i then c (i - n) * a else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp [not_le.mpr hi]
    rw [h0, sub_zero]
    simpa using (Summable.of_norm hc).hasSum.mul_right a

theorem eulerInverse_eval_one {ι : Type} [Fintype ι] (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (Q : ι → ℂ)
    (h : PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1) :
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  set P : Polynomial ℂ := ∏ p, (1 - Polynomial.C (Q p) * Polynomial.X) with hPdef
  have hP : (P : PowerSeries ℂ) = ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) := by
    have := map_prod (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
      (fun p => 1 - Polynomial.C (Q p) * Polynomial.X) Finset.univ
    rw [hPdef]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply] at this
    rw [this]
    simp
  have h1 := hasSum_coeff_mk_mul_polynomial c hc P
  rw [hP, h] at h1
  have h2 : HasSum (fun d => coeff d (1 : PowerSeries ℂ)) 1 := by
    simpa [PowerSeries.coeff_one] using hasSum_ite_eq 0 (1 : ℂ)
  have h3 := h1.unique h2
  have hev : P.eval 1 = ∏ p, (1 - Q p) := by simp [hPdef, Polynomial.eval_prod]
  rw [hev] at h3
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  · rw [← eq_inv_of_mul_eq_one_left h3]
    exact (Summable.of_norm hc).hasSum

end GlobalTheory.JSW
end
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem adjoint_injective_surjective_and_positive_scalar :
    ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] F),
      (Function.Injective (LinearMap.adjoint A) → Function.Surjective A) ∧
      (∀ (U : Submodule ℂ F) (l : ℂ), l ≠ 0 →
        (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = l * ⟪x, y⟫_ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x) := by
  intro E F _ _ _ _ _ _ A
  constructor
  · intro hinj
    have hbot : (LinearMap.range A)ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have h0 : LinearMap.adjoint A v = 0 := by
        apply ext_inner_right ℂ
        intro e
        rw [LinearMap.adjoint_inner_left, inner_zero_left]
        exact (Submodule.mem_orthogonal' _ _).mp hv (A e) ⟨e, rfl⟩
      exact hinj (h0.trans (map_zero _).symm)
    have htop : LinearMap.range A = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
    exact LinearMap.range_eq_top.mp htop
  · intro U l hl h
    have key : ∀ l' : ℝ, 0 < l' → l = (l' : ℂ) →
        ∃ l' : ℝ, 0 < l' ∧
          (∀ x ∈ U, ∀ y, ⟪LinearMap.adjoint A x, LinearMap.adjoint A y⟫_ℂ = (l' : ℂ) * ⟪x, y⟫_ℂ) ∧
          ∀ x ∈ U, A (LinearMap.adjoint A x) = (l' : ℂ) • x := by
      intro l' hpos hl'
      subst hl'
      refine ⟨l', hpos, h, ?_⟩
      intro x hx
      apply ext_inner_right ℂ
      intro v
      rw [← LinearMap.adjoint_inner_right, h x hx v, inner_smul_left, Complex.conj_ofReal]
    by_cases hU : U = ⊥
    · refine ⟨1, one_pos, ?_, ?_⟩
      · intro x hx y
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
      · intro x hx
        rw [hU, Submodule.mem_bot] at hx
        subst hx
        simp
    · obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hxx := h x hxU x
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hxx
      have hn : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      have hlval : l = ((‖LinearMap.adjoint A x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) := by
        have hne : ((‖x‖ : ℂ)) ^ 2 ≠ 0 := by
          have : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx0)
          exact pow_ne_zero _ this
        push_cast
        rw [eq_div_iff hne]
        exact hxx.symm
      apply key _ _ hlval
      rcases (div_nonneg (sq_nonneg ‖LinearMap.adjoint A x‖) hn.le).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply hl; rw [hlval, ← heq]; simp

end GlobalTheory
end

section

namespace GlobalTheory

open Submodule

section SchurIsotypic
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma schur_act_inv (act : G →* Module.End ℂ H) (g : G) (y : H) : act g (act g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma schur_orth_stable (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (P : Submodule ℂ H) (hP : ∀ g, ∀ p ∈ P, act g p ∈ P) :
    ∀ g, ∀ e ∈ Pᗮ, act g e ∈ Pᗮ := by
  intro g e he
  rw [Submodule.mem_orthogonal] at he ⊢
  intro u hu
  have := hact g _ _ (he _ (hP g⁻¹ u hu))
  rwa [schur_act_inv] at this

lemma schur_decomp [FiniteDimensional ℂ H] (P : Submodule ℂ H) (x : H) :
    ∃ p ∈ P, x - p ∈ Pᗮ := by
  exact ⟨P.starProjection x, P.starProjection_apply_mem x, P.sub_starProjection_mem_orthogonal x⟩

lemma schur_vanish {W : Type} [AddCommGroup W] [Module ℂ W] [Nontrivial W] [FiniteDimensional ℂ H]
    (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (ρ : G →* Module.End ℂ W)
    (hirr : ∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (E : Submodule ℂ H) (hE : ∀ g, ∀ e ∈ E, act g e ∈ E)
    (hEorth : ∀ χ : W →ₗ[ℂ] H, (∀ g w, χ (ρ g w) = act g (χ w)) →
      ∀ w, ∀ e ∈ E, inner ℂ (χ w) e = 0)
    (φ : H →ₗ[ℂ] W) (hφ : ∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) : ∀ e ∈ E, φ e = 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨e₀, he₀E, he₀⟩ := hne
  let K : Submodule ℂ H := LinearMap.ker φ ⊓ E
  have hK : ∀ g, ∀ k ∈ K, act g k ∈ K := by
    intro g k hk
    obtain ⟨hk1, hk2⟩ := Submodule.mem_inf.1 hk
    refine Submodule.mem_inf.2 ⟨?_, hE g k hk2⟩
    rw [LinearMap.mem_ker] at hk1 ⊢
    rw [hφ g k hk2, hk1, map_zero]
  let C : Submodule ℂ H := Kᗮ ⊓ E
  have hC : ∀ g, ∀ c ∈ C, act g c ∈ C := fun g c hc =>
    Submodule.mem_inf.2 ⟨schur_orth_stable act hact K hK g c (Submodule.mem_inf.1 hc).1,
      hE g c (Submodule.mem_inf.1 hc).2⟩
  have hCE : ∀ c ∈ C, c ∈ E := fun c hc => (Submodule.mem_inf.1 hc).2
  have hinj : ∀ c ∈ C, φ c = 0 → c = 0 := by
    intro c hc h0
    have hcK : c ∈ K := Submodule.mem_inf.2 ⟨h0, hCE c hc⟩
    have := (Submodule.mem_orthogonal _ _).1 (Submodule.mem_inf.1 hc).1 c hcK
    exact inner_self_eq_zero.1 this
  have hU : C.map φ = ⊤ := by
    rcases hirr (C.map φ) (by
      intro g
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨act g c, hC g c hc, hφ g c (hCE c hc)⟩) with h | h
    · exfalso
      obtain ⟨p, hp, hr⟩ := schur_decomp K e₀
      have hrE : e₀ - p ∈ E := E.sub_mem he₀E (Submodule.mem_inf.1 hp).2
      have hrC : e₀ - p ∈ C := Submodule.mem_inf.2 ⟨hr, hrE⟩
      have hm : φ (e₀ - p) ∈ C.map φ := Submodule.mem_map_of_mem hrC
      rw [h, Submodule.mem_bot, map_sub, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hp).1,
        sub_zero] at hm
      exact he₀ hm
    · exact h
  let ψ : C →ₗ[ℂ] W := φ.comp C.subtype
  have hψi : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    exact Subtype.ext (hinj c c.2 (LinearMap.mem_ker.1 hc))
  have hψs : Function.Surjective ψ := by
    intro w
    have hw : w ∈ C.map φ := hU ▸ Submodule.mem_top
    obtain ⟨c, hc, hcw⟩ := hw
    exact ⟨⟨c, hc⟩, hcw⟩
  let e := LinearEquiv.ofBijective ψ ⟨hψi, hψs⟩
  let χ : W →ₗ[ℂ] H := C.subtype.comp e.symm.toLinearMap
  have hχC : ∀ w, χ w ∈ C := fun w => (e.symm w).2
  have hφχ : ∀ w, φ (χ w) = w := fun w => by
    show ψ (e.symm w) = w
    exact e.apply_symm_apply w
  have hχ : ∀ g w, χ (ρ g w) = act g (χ w) := by
    intro g w
    have hd : χ (ρ g w) - act g (χ w) ∈ C := C.sub_mem (hχC _) (hC g _ (hχC w))
    have := hinj _ hd (by rw [map_sub, hφχ, hφ g _ (hCE _ (hχC w)), hφχ, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h0 : χ w = 0 := inner_self_eq_zero.1 (hEorth χ hχ w (χ w) (hCE _ (hχC w)))
  exact hw (by rw [← hφχ w, h0, map_zero])

end SchurIsotypic

theorem schur_isotypic_splitting : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := by
  intro G W H _ _ _ _ _ _ _ act hact ρ hirr x
  let S : Set H := {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}
  let I : Submodule ℂ H := Submodule.span ℂ S
  have hI : ∀ g, ∀ y ∈ I, act g y ∈ I := by
    intro g y hy
    have hle : I.map (act g) ≤ I := by
      rw [Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨φ, ρ g w, hφ, (hφ g w).symm⟩
    exact hle (Submodule.mem_map_of_mem hy)
  obtain ⟨q, hq, hxq⟩ := schur_decomp I x
  refine ⟨q, hq, Iᗮ, schur_orth_stable act hact I hI, ?_, hxq⟩
  intro φ hφ
  refine schur_vanish act hact ρ hirr Iᗮ (schur_orth_stable act hact I hI) ?_ φ hφ
  intro χ hχ w e he
  exact (Submodule.mem_orthogonal _ _).1 he _ (Submodule.subset_span ⟨χ, w, hχ, rfl⟩)

end GlobalTheory
end

section

universe u_1

namespace GlobalTheory.NatCastUnitNorm

theorem norm_natCast_eq_one_of_not_dvd {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K]
    {l m : ℕ} (hl : Nat.Prime l) (hlt : ‖(l : K)‖ < (1 : ℝ)) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = (1 : ℝ) := by
  have hle : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  by_contra hne
  have hmlt : ‖(m : K)‖ < 1 := lt_of_le_of_ne hle hne
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hK : (a : K) * (l : K) + (b : K) * (m : K) = 1 := by
    have h := congrArg (fun z : ℤ => (z : K)) hab
    simpa using h
  have key : ∀ (c : ℤ) (x : K), ‖x‖ < 1 → ‖(c : K) * x‖ < 1 := by
    intro c x hx
    rw [norm_mul]
    have hc : ‖(c : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K c
    calc ‖(c : K)‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < 1 := hx
  have h1 := IsUltrametricDist.norm_add_le_max ((a : K) * (l : K)) ((b : K) * (m : K))
  rw [hK, norm_one] at h1
  exact absurd h1 (not_le.2 (max_lt (key a _ hlt) (key b _ hmlt)))

end GlobalTheory.NatCastUnitNorm
end

section

namespace GlobalTheory.JR.WeilProd

def tensorRep {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    G × H → (X × Y → ℂ) → X × Y → ℂ :=
  fun g f p => W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1

theorem tensorRep_apply {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) (g : G × H)
    (f : X × Y → ℂ) (p : X × Y) :
    tensorRep W₁ W₂ g f p = W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1 := rfl

end GlobalTheory.JR.WeilProd
end
