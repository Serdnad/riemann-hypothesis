module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.SpecificDegree
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

@[expose] public section

section

open NumberField

namespace GlobalTheory.UnitReal

theorem unit_real_of_congr_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  intro E _ _ _ q hq hqt u hu φ
  set I : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with hI
  set c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hc
  set v : (𝓞 E)ˣ := IsCMField.unitsComplexConj E u with hv
  have hvc : (v : 𝓞 E) = c u := rfl
  have hv1 : (v : 𝓞 E) - 1 ∈ I := by
    rw [hI, Ideal.mem_span_singleton] at hu ⊢
    obtain ⟨y, hy⟩ := hu
    refine ⟨c y, ?_⟩
    rw [hvc, ← map_one c, ← map_sub, hy, map_mul, map_natCast]
  set ζ : (𝓞 E)ˣ := (IsCMField.unitsMulComplexConjInv E u : (𝓞 E)ˣ) with hζ
  have hζv : ζ * v = u := by rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]
  have hζ1 : Ideal.Quotient.mk I (ζ : 𝓞 E) = 1 := by
    have a1 : Ideal.Quotient.mk I (u : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
    have a2 : Ideal.Quotient.mk I (v : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hv1
    have := congrArg (fun x : (𝓞 E)ˣ => Ideal.Quotient.mk I (x : 𝓞 E)) hζv
    simp only [Units.val_mul, map_mul, a1, a2, mul_one] at this
    exact this
  have ht : ζ ^ Nat.card (Units.torsion E) = 1 := by
    have h4 : (IsCMField.unitsMulComplexConjInv E u) ^ Nat.card (Units.torsion E) = 1 := pow_card_eq_one'
    have := congrArg Subtype.val h4
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    exact this
  have hζeq : ζ = 1 := by
    by_contra hne
    have hne' : (ζ : 𝓞 E) - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hne (Units.ext h)
    have hsum : ∑ j ∈ Finset.range (Nat.card (Units.torsion E)), (ζ : 𝓞 E) ^ j = 0 := by
      have := mul_geom_sum ((ζ : 𝓞 E)) (Nat.card (Units.torsion E))
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_left hne'
    have hmod := congrArg (Ideal.Quotient.mk I) hsum

    simp only [map_sum, map_pow, hζ1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, map_zero] at hmod
    have hmem : ((Nat.card (Units.torsion E) : ℕ) : 𝓞 E) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hmod
    rw [hI, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hn := congrArg (Algebra.norm ℤ) hy
    rw [map_mul] at hn
    have e1 : ∀ n : ℕ, Algebra.norm ℤ ((n : 𝓞 E)) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      intro n
      rw [← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
    rw [e1, e1] at hn
    have hd : 0 < Module.finrank ℤ (𝓞 E) := by
      rw [RingOfIntegers.rank]; exact Module.finrank_pos
    have hdvd : (q : ℤ) ∣ (Nat.card (Units.torsion E) : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [hn]; exact Dvd.dvd.mul_right (dvd_pow_self _ hd.ne') _
    have hdvd' : q ∣ Nat.card (Units.torsion E) ^ Module.finrank ℤ (𝓞 E) := by exact_mod_cast hdvd
    exact hqt (hq.dvd_of_dvd_pow hdvd')
  have huv : (v : 𝓞 E) = u := by rw [← hζv, hζeq, one_mul]
  have hE : IsCMField.complexConj E ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huv
    exact this
  rw [← IsCMField.complexEmbedding_complexConj, hE]

end GlobalTheory.UnitReal
end

section

open NumberField

namespace GlobalTheory.Div.CMAlgChar

theorem place_factor (z : ℂ) (hz : z ≠ 0) (a b w0 : ℤ) (hab : a + b = w0) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * a - w0) *
      (((‖z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖(starRingEnd ℂ) z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ a * (starRingEnd ℂ z) ^ b := by
  rw [Complex.norm_conj]
  set r : ℂ := ((‖z‖ : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by simp [hr, hz]
  rw [← Complex.cpow_add _ _ hr0]
  have hsum : ((((w0 : ℝ) / 2 : ℝ)) : ℂ) + ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ((w0 : ℤ) : ℂ) := by
    push_cast; ring
  rw [hsum, Complex.cpow_intCast]
  have hc : starRingEnd ℂ z = r ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hr]
    push_cast; rfl
  rw [hc]
  subst hab
  have he : 2 * a - (a + b) = a - b := by ring
  rw [he, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hr0, zpow_add₀ hr0, pow_two, mul_zpow]
  field_simp

theorem fiber_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] [DecidableEq (E →+* ℂ)]
    [DecidableEq (InfinitePlace E)]
    (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  have h1 : InfinitePlace.mk φ = w ↔ InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
    rw [w.mk_embedding]
  rw [h1, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [← h, ComplexEmbedding.involutive_conjugate E]
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h, ComplexEmbedding.involutive_conjugate E]

theorem embedding_ne_conjugate {E : Type} [Field E] [IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc := IsTotallyComplex.isComplex w
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
    ComplexEmbedding.isReal_iff] at hc
  exact hc h.symm

theorem algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  intro E _ _ _ n w0 hn k hk
  classical
  have hfib : ∀ f : (E →+* ℂ) → ℂ, ∏ φ, f φ =
      ∏ w : InfinitePlace E, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
    intro f
    rw [← Finset.prod_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [fiber_eq w, Finset.prod_pair (embedding_ne_conjugate w)]
  rw [hfib (fun φ => ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)),
    hfib (fun φ => φ k ^ n φ), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hz : w.embedding k ≠ 0 := (map_ne_zero _).2 hk
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact place_factor _ hz _ _ _ (hn _)

end GlobalTheory.Div.CMAlgChar
end

section

namespace GlobalTheory

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem discr_mul_isIntegral_of_traceDual :
    ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by
  intro K _ _ x hx
  classical
  have hmem : ((NumberField.discr K).natAbs : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    rw [← NumberField.absNorm_differentIdeal K (𝓞 K)]
    exact Ideal.absNorm_mem _
  have hdual : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨k, hk⟩ := hx b
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk, mul_comm]
  have hprod := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hmem) hdual
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ
    (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))] at hprod
  obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  rw [map_natCast] at hα
  have hint : IsIntegral ℤ (((NumberField.discr K).natAbs : K) * x) := by
    rw [← hα]
    exact α.isIntegral_coe
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h]
    simpa using hint
  · rw [h]
    simpa using hint.neg

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem ringOfIntegers_ringHom_injective {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : 𝓞 E →+* 𝓞 K) : Function.Injective σ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem sum_log_norm_embeddings {K : Type} [Field K] [NumberField K] (y : K) :
    ∑ s : K →+* ℂ, Real.log ‖s y‖ = Real.log |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
  by_cases hy : y = 0
  · subst hy
    simp
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have h2 : ∏ s : K →+* ℂ, s y = ∏ s : K →ₐ[ℚ] ℂ, s y :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun s => rfl)
  rw [← Real.log_prod (fun s _ => by simpa using hy), ← norm_prod, h2, ← h]
  congr 1
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem mean_log_norm_embeddings_ringHom :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  intro E K _ _ _ _ σ x
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp σ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_ringHom_injective σ)
  let τ : E →+* K := IsFractionRing.lift hinj
  have hτ : τ (x : E) = (σ x : K) := IsFractionRing.lift_algebraMap hinj x
  letI : Algebra E K := τ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  have hx : (σ x : K) = algebraMap E K (x : E) := hτ.symm
  rw [sum_log_norm_embeddings, hx, ← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow,
    ← Module.finrank_mul_finrank ℚ E K]
  have h1 : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h2 : (Module.finrank E K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  rw [abs_pow, Real.log_pow]
  field_simp

end GlobalTheory
end

section

noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.LipschitzTR

variable (F : Type) [Field F] [NumberField F]

abbrev RSp := EuclideanSpace ℝ (F →+* ℝ)

def remb : F →+ RSp F where
  toFun a := WithLp.toLp 2 (fun τ : F →+* ℝ => τ a)
  map_zero' := by ext τ; simp
  map_add' a b := by ext τ; simp

variable {F}

@[simp] theorem remb_apply (a : F) (τ : F →+* ℝ) : remb F a τ = τ a := rfl

def latOf (N : FractionalIdeal (𝓞 F)⁰ F) : Submodule ℤ (RSp F) :=
  Submodule.map (remb F).toIntLinearMap ((N : Submodule (𝓞 F) F).restrictScalars ℤ)

theorem mem_latOf (N : FractionalIdeal (𝓞 F)⁰ F) (x : RSp F) :
    x ∈ latOf N ↔ ∃ a ∈ N, remb F a = x := by
  simp [latOf]

def phi1 (k : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w)
  else 0

def Phi (k : ℕ) (z : (F →+* ℝ) → ℂ) (ξ : RSp F) : ℂ :=
  ∏ τ : F →+* ℝ, phi1 k (z τ) (ξ τ)

end GlobalTheory.LipschitzTR
end
end

section

open NumberField Polynomial

noncomputable section

namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : F[X]) := by
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg]) (by rw [hdeg]; norm_num)).2 ?_
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [mem_roots (Monic.ne_zero (by monicity!)), IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
    exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
  have := congrArg τ hr
  simp at this
  nlinarith [sq_nonneg (τ r)]

instance : Fact (Irreducible (X ^ 2 + 1 : F[X])) := ⟨irreducible_X_sq_add_one F⟩

abbrev Ext : Type := AdjoinRoot (X ^ 2 + 1 : F[X])

instance : Module.Finite F (Ext F) :=
  (AdjoinRoot.powerBasis (Monic.ne_zero (by monicity!) : (X ^ 2 + 1 : F[X]) ≠ 0)).finite

instance : NumberField (Ext F) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap F (Ext F)).injective
  to_finiteDimensional := Module.Finite.trans F (Ext F)

def ii : Ext F := AdjoinRoot.root _

theorem ii_sq : ii F ^ 2 = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : F[X])
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  rw [ii]; linear_combination h

def gEmb (p : F × F) : Ext F := algebraMap F (Ext F) p.1 + algebraMap F (Ext F) p.2 * ii F

end GlobalTheory.GaussExt
end
end

section

open NumberField MeasureTheory Filter Topology

namespace GlobalTheory.Shintani

theorem denseRange_realEmbeddings :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
      DenseRange (fun (x : F) (σ : F →+* ℝ) => σ x) := by
  intro F _ _ _
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  let E : ∀ w : InfinitePlace F, w.Completion → ℝ := fun w z =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) z
  have hs : Function.Surjective (Pi.map E) := by
    intro y
    refine ⟨fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y w), ?_⟩
    funext w
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  have hc : Continuous (Pi.map E) := by
    refine continuous_pi fun w => ?_
    have : (E w) = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) := by
      funext z; exact InfinitePlace.Completion.ringEquivRealOfIsReal_apply _ z
    change Continuous fun a : (∀ v : InfinitePlace F, v.Completion) => E w (a w)
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have h2 := hs.denseRange.comp h1 hc
  let g : (F →+* ℝ) → InfinitePlace F := fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)
  have hreal : ∀ σ : F →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    intro σ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hemb : ∀ σ : F →+* ℝ, (g σ).embedding = Complex.ofRealHom.comp σ := fun σ =>
    InfinitePlace.embedding_mk_eq_of_isReal (hreal σ)
  have hg : Function.Injective g := by
    intro σ τ h
    have := hemb σ
    rw [h, hemb τ] at this
    ext x
    have h3 := congrArg (fun f : F →+* ℂ => f x) this
    simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at h3
    exact h3.symm
  have hval : ∀ (x : F) (σ : F →+* ℝ), Pi.map E (algebraMap F (InfiniteAdeleRing F) x) (g σ) = σ x := by
    intro x σ
    change E (g σ) (algebraMap F (InfiniteAdeleRing F) x (g σ)) = σ x
    rw [InfiniteAdeleRing.algebraMap_apply]
    apply Complex.ofReal_injective
    simp only [E, InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    change InfinitePlace.Completion.extensionEmbedding (g σ)
      (↑((WithAbs.equiv (g σ).1).symm x)) = (σ x : ℂ)
    rw [InfinitePlace.Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply, hemb σ]
    rfl

  let P : (InfinitePlace F → ℝ) → ((F →+* ℝ) → ℝ) := fun y σ => y (g σ)
  have hPs : Function.Surjective P := fun z => ⟨Function.extend g z 0, funext fun σ => hg.extend_apply z 0 σ⟩
  have hPc : Continuous P := continuous_pi fun σ => continuous_apply (g σ)
  convert hPs.denseRange.comp h2 hPc using 1
  funext x σ
  exact (hval x σ).symm

end GlobalTheory.Shintani
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem padicInt_ringHom_ext_of_isHausdorff : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  (f g : ℤ_[p] →+* O), f = g := by
  intro p _ O _ hH f g
  ext z
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hH _ fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (p : ℤ_[p]) ^ n * w + (z.appr n : ℕ) := by rw [mul_comm, hw]; ring
  have key : f z - g z = (p : O) ^ n * (f w - g w) := by
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, mul_sub]
    abel
  rw [SModEq.zero, key, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory
end
