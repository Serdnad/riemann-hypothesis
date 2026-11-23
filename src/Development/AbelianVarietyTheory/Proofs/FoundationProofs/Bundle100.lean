module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

open Polynomial

theorem exists_valuation_pow_eq (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f)
    (hnt : f.IsNontrivial) (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      (∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1) ∧
      ∀ x : Ω, (v x : ℝ) ^ (minpoly K x).natDegree = f ((minpoly K x).coeff 0) := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤
          max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  have hco : ∀ (x : Ω) (i : ℕ), ‖(minpoly (WithAbs f) x).coeff i‖ = f ((minpoly K x).coeff i) := by
    intro x i
    rw [hmin x, Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl
  refine ⟨v, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx)]
    exact forall_congr' fun i => by rw [hco]
  · have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hd : (minpoly (WithAbs f) x).natDegree = (minpoly K x).natDegree := by
      rw [hmin x, (minpoly.monic hx).natDegree_map]
    rw [hv, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (WithAbs f) Ω x, hco, hd, one_div]
    exact Real.rpow_inv_natCast_pow (f.nonneg _) (minpoly.natDegree_pos hx).ne'

theorem exists_pow_div_zpow_isIntegral (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsAlgebraic K Ω] (π : R) (hπ : Irreducible π) (x : Ω) (hx : x ≠ 0) :
    ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsIntegral R (x ^ b / (algebraMap R Ω π) ^ a) ∧
      IsIntegral R ((algebraMap R Ω π) ^ a / x ^ b) := by
  obtain ⟨f, hna, hnt, hball, hc⟩ :=
    GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing R K
  obtain ⟨v, hext, hle, hpow⟩ := exists_valuation_pow_eq K Ω f hna hnt hc
  have hint : ∀ z : Ω, v z ≤ 1 → IsIntegral R z := by
    intro z hz
    have hzK : IsIntegral K z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
    have hl : minpoly K z ∈ Polynomial.lifts (algebraMap R K) :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun i => (hball _).1 ((hle z).1 hz i)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hzK)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]
  have hR : ∀ r : R, v (algebraMap R Ω r) ≤ 1 := by
    intro r
    rw [IsScalarTower.algebraMap_apply R K Ω, ← NNReal.coe_le_coe, hext]
    exact (hball _).2 ⟨r, rfl⟩
  have hU : ∀ u : Rˣ, v (algebraMap R Ω u) = 1 := by
    intro u
    have h1 : v (algebraMap R Ω u) * v (algebraMap R Ω (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm (hR _) ?_
    calc 1 = _ := h1.symm
      _ ≤ v (algebraMap R Ω u) * 1 := by gcongr; exact hR _
      _ = _ := mul_one _
  have hxK : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hπ0 : v (algebraMap R Ω π) ≠ 0 :=
    (map_ne_zero v).2 ((map_ne_zero_iff _ hinj).2 hπ.ne_zero)
  have hc0 : (minpoly K x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hxK hx
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) ((minpoly K x).coeff 0)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hrs]; simp)
  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hπ
  obtain ⟨j, w, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hπ
  have key : v (x ^ (minpoly K x).natDegree) = v (algebraMap R Ω π ^ ((i : ℤ) - j)) := by
    have h1 : v x ^ (minpoly K x).natDegree = v (algebraMap K Ω ((minpoly K x).coeff 0)) := by
      apply NNReal.coe_injective
      rw [NNReal.coe_pow, hpow, hext]
    rw [map_pow, h1, ← hrs, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, map_zpow₀, zpow_sub₀ hπ0]
    simp [hU]
  have hx0 : v (x ^ (minpoly K x).natDegree) ≠ 0 := (map_ne_zero v).2 (pow_ne_zero _ hx)
  refine ⟨(i : ℤ) - j, (minpoly K x).natDegree, minpoly.natDegree_pos hxK, hint _ ?_, hint _ ?_⟩
  · rw [map_div₀, ← key, div_self hx0]
  · rw [map_div₀, ← key, div_self hx0]

theorem exists_pow_div_p_zpow_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧
    IsInt (p := p) ((p : Ω) ^ a / x ^ b) := by
  intro p _ Ω _ _ hΩ x hx
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]; exact o0_isAdicComplete_span_p p
  haveI : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hΩ.inj
  letI : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hΩ.alg
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  have := exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx
  rwa [map_natCast] at this

end GlobalTheory.K5
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.SqCount

theorem sq_mul_unique {k : Type} [Field k] {a b c d : k[X]} (ha : a.Monic) (hc : c.Monic)
    (hb : Squarefree b) (hd : Squarefree d) (h : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  obtain ⟨a1, c1, e, hco, rfl, rfl⟩ : ∃ a1 c1 e : k[X], IsCoprime a1 c1 ∧ a = e * a1 ∧ c = e * c1 := by
    obtain ⟨a1, c1, h1, h2, h3⟩ := extract_gcd a c
    exact ⟨a1, c1, GCDMonoid.gcd a c, (gcd_isUnit_iff _ _).1 h3, h1, h2⟩
  have he : e ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have h' : a1 ^ 2 * b = c1 ^ 2 * d := by
    apply mul_left_cancel₀ (pow_ne_zero 2 he)
    linear_combination h
  have u1 : IsUnit a1 := by
    apply hd
    rw [← sq]
    exact (hco.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨b, h'.symm⟩
  have u2 : IsUnit c1 := by
    apply hb
    rw [← sq]
    exact (hco.symm.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨d, h'⟩
  have hac : e * a1 = e * c1 :=
    eq_of_monic_of_associated ha hc ((associated_mul_unit_left e a1 u1).trans (associated_mul_unit_left e c1 u2).symm)
  refine ⟨hac, ?_⟩
  rw [hac] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hc.ne_zero) h

theorem exists_sq_mul {k : Type} [Field k] {f : k[X]} (hf : f.Monic) :
    ∃ a b : k[X], a.Monic ∧ b.Monic ∧ Squarefree b ∧ f = a ^ 2 * b := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hs : Squarefree f
  · exact ⟨1, f, monic_one, hf, hs, by simp⟩
  obtain ⟨x, hx, hu⟩ : ∃ x, x * x ∣ f ∧ ¬ IsUnit x := by
    by_contra hc
    exact hs fun x hx => by_contra fun hu => hc ⟨x, hx, hu⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hx)
  have hy : (normalize x).Monic := monic_normalize hx0
  have hass : Associated (normalize x) x := normalize_associated x
  obtain ⟨h, rfl⟩ := (hass.mul_mul hass).dvd.trans hx
  have hh : h.Monic := (hy.mul hy).of_mul_monic_left hf
  have hpos : 0 < (normalize x).natDegree :=
    natDegree_pos_of_not_isUnit_of_dvd_monic hy (fun hu' => hu (hass.isUnit hu')) dvd_rfl
  rw [(hy.mul hy).natDegree_mul hh, hy.natDegree_mul hy] at hn
  obtain ⟨a, b, ha, hb, hsq, rfl⟩ := ih h.natDegree (by omega) hh rfl
  exact ⟨normalize x * a, b, hy.mul ha, hb, hsq, by ring⟩

variable (g : ℕ) [Fact g.Prime]

noncomputable def monicSet (N : ℕ) : Finset (ZMod g)[X] :=
  Finset.univ.image fun c : Fin N → ZMod g => (X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X])

variable {g}

theorem mem_monicSet {N : ℕ} {f : (ZMod g)[X]} : f ∈ monicSet g N ↔ f.Monic ∧ f.natDegree = N := by
  unfold monicSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    have hlt : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < (N : WithBot ℕ) := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hlt, ?_⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [hm.as_sum]
    rw [Finset.sum_range fun i => C (f.coeff i) * X ^ i]

theorem card_monicSet (N : ℕ) : (monicSet g N).card = g ^ N := by
  unfold monicSet
  rw [Finset.card_image_of_injective]
  · simp [ZMod.card]
  · intro c d h
    have h' := add_left_cancel h
    funext i
    have := congrArg (fun p : (ZMod g)[X] => p.coeff i) h'
    simpa [Polynomial.finsetSum_coeff, coeff_X_pow, Fin.val_inj] using this

theorem monic_divX {k : Type} [Field k] {a : k[X]} (ha : a.Monic) (hd : 1 ≤ a.natDegree) : a.divX.Monic := by
  rw [Monic, leadingCoeff, natDegree_divX_eq_natDegree_tsub_one, coeff_divX, Nat.sub_add_cancel hd]
  exact ha

theorem card_zero_const (n : ℕ) : ((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0).card ≤ g ^ n := by
  rw [← card_monicSet]
  refine Finset.card_le_card_of_injOn divX ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_monicSet, Finset.mem_coe] at hf ⊢
    refine ⟨monic_divX hf.1.1 (by omega), ?_⟩
    rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  · intro f hf f' hf' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_monicSet] at hf hf'
    rw [← divX_mul_X_add f, ← divX_mul_X_add f', h, hf.2, hf'.2]

theorem card_not_squarefree (n : ℕ) : ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f).card ≤ g ^ n := by
  rcases n with _ | n
  · rw [Finset.filter_eq_empty_iff.2]
    · simp
    · intro f hf
      rw [mem_monicSet] at hf
      rw [not_not]
      exact (irreducible_of_degree_eq_one (by rw [degree_eq_natDegree hf.1.ne_zero, hf.2]; rfl)).squarefree
  have hc : ((Finset.univ : Finset (ZMod g)) ×ˢ monicSet g n).card = g ^ (n + 1) := by
    rw [Finset.card_product, card_monicSet, Finset.card_univ, ZMod.card, pow_succ']
  rw [← hc]
  refine Finset.card_le_card_of_forall_subsingleton
    (fun f p => ∃ a b : (ZMod g)[X], a.Monic ∧ Squarefree b ∧ p.2 = a ^ 2 * b ∧ f = (a * X + C p.1) ^ 2 * b) ?_ ?_
  · intro f hf
    rw [Finset.mem_filter, mem_monicSet] at hf
    obtain ⟨⟨hm, hd⟩, hs⟩ := hf
    obtain ⟨a, b, ha, hb, hsq, rfl⟩ := exists_sq_mul hm
    have h1 : 1 ≤ a.natDegree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [ha.natDegree_eq_zero] at h0
      subst h0
      exact hs (by simpa using hsq)
    have ha' := monic_divX ha h1
    refine ⟨(a.coeff 0, a.divX ^ 2 * b), ?_, a.divX, b, ha', hsq, rfl, by rw [divX_mul_X_add]⟩
    rw [Finset.mem_product, mem_monicSet]
    refine ⟨Finset.mem_univ _, (ha'.pow 2).mul hb, ?_⟩
    rw [(ha.pow 2).natDegree_mul hb, ha.natDegree_pow] at hd
    show (a.divX ^ 2 * b).natDegree = n
    rw [(ha'.pow 2).natDegree_mul hb, ha'.natDegree_pow, natDegree_divX_eq_natDegree_tsub_one]
    omega
  · rintro p - f ⟨-, a, b, ha, hb, h1, rfl⟩ f' ⟨-, c, d, hc, hd, h2, rfl⟩
    obtain ⟨rfl, rfl⟩ := sq_mul_unique ha hc hb hd (h1.symm.trans h2)
    rfl

end GlobalTheory.BadShare.SqCount


open GlobalTheory.BadShare.SqCount in
theorem GlobalTheory.BadShare.card_sqSet_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N →
    (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  intro g _ N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsub : monicSet g (n + 1) ⊆ sqSet g (n + 1) ∪ (((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0) ∪
      ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f)) := by
    intro f hf
    simp only [Finset.mem_union, Finset.mem_filter, mem_sqSet]
    have := mem_monicSet.1 hf
    tauto
  have h1 := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_zero_const n) (card_not_squarefree n))) _))
  rw [card_monicSet] at h1
  have h2 : ((g : ℝ)) ^ (n + 1) ≤ ((sqSet g (n + 1)).card : ℝ) + ((g : ℝ) ^ n + (g : ℝ) ^ n) := by exact_mod_cast h1
  rw [Nat.add_sub_cancel]
  linarith
end

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem pow_padicVal_eq_one_of_primePow {k : Type} [Field k] {n l : ℕ} (hn : 0 < n) (hl : l.Prime) {y : k}
    (h1 : y ^ n = 1) {a : ℕ} (h2 : y ^ (l ^ a) = 1) : y ^ (l ^ padicValNat l n) = 1 := by
  have := Fact.mk hl
  have d1 : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one h1
  have d2 : orderOf y ∣ l ^ a := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl).1 d2
  rw [hi] at d1
  have hle : i ≤ padicValNat l n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn.ne').1 d1
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hi]
  exact pow_dvd_pow l hle

theorem primePowRoots_finite_ncard (k : Type) [Field k] (n l : ℕ) (hn : 0 < n) (hl : l.Prime) :
    {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
      {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n := by
  have hm : 0 < l ^ padicValNat l n := pow_pos hl.pos _
  have hsub : {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} ⊆
      ((nthRoots (l ^ padicValNat l n) (1 : k)).toFinset : Set k) := by
    rintro y ⟨h1, a, h2⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hm]
    exact pow_padicVal_eq_one_of_primePow hn hl h1 h2
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)

theorem samePart_roots_finite_ncard :
    ∀ (k : Type) [Field k] (n l : ℕ), 0 < n → l.Prime →
      ({y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
        {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n) ∧
      ∀ z : k, {x : k | x ^ n = 1 ∧ SamePart l x z}.Finite ∧
        {x : k | x ^ n = 1 ∧ SamePart l x z}.ncard ≤ l ^ padicValNat l n := by
  intro k _ n l hn hl
  obtain ⟨hf, hc⟩ := primePowRoots_finite_ncard k n l hn hl
  refine ⟨⟨hf, hc⟩, fun z => ?_⟩
  rcases Set.eq_empty_or_nonempty {x : k | x ^ n = 1 ∧ SamePart l x z} with he | ⟨x₀, hx₀, hb⟩
  · rw [he]; simp
  have hsub : {x : k | x ^ n = 1 ∧ SamePart l x z} ⊆
      (fun y => y * x₀) '' {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} := by
    rintro x ⟨hx, ha⟩
    have hs : SamePart l x x₀ := Eq.trans ha (Eq.symm hb)
    obtain ⟨a, ha⟩ := (samePart_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx⟩)
      (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx₀⟩)).1 hs
    have h0 : x₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hx₀
      exact zero_ne_one hx₀
    refine ⟨x / x₀, ⟨?_, a, ?_⟩, div_mul_cancel₀ x h0⟩
    · rw [div_pow, hx, hx₀, div_one]
    · rw [div_pow, ha, div_self (pow_ne_zero _ h0)]
  refine ⟨(hf.image _).subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans hc)

end GlobalTheory.BadShare
end

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem degType_pos (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : ∀ d ∈ degType g f, 0 < d := by
  intro d hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hd
  exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP).natDegree_pos

theorem degType_sum (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) (hf : f ≠ 0) :
    (degType g f).sum = f.natDegree := by
  unfold degType
  rw [← natDegree_multiset_prod _ (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f)]
  exact natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))

theorem prod_pow_sub_one_le (g : ℕ) (s : Multiset ℕ) :
    (s.map fun d => g ^ d - 1).prod ≤ g ^ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add]
    exact Nat.mul_le_mul (Nat.sub_le _ _) ih

theorem ne_zero_natDegree_of_mem_sqSet (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X])
    (hf : f ∈ sqSet g N) : f ≠ 0 ∧ f.natDegree = N := by
  unfold sqSet at hf
  rw [Finset.mem_filter, Finset.mem_image] at hf
  obtain ⟨⟨c, -, rfl⟩, -⟩ := hf
  have h : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
  refine ⟨(monic_X_pow_add h).ne_zero, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

theorem torusCard_bounds_mul : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  intro g hg
  refine ⟨fun N f hf => ?_, fun h f hh hf => ?_, fun P hP => ?_⟩
  · obtain ⟨h0, hN⟩ := ne_zero_natDegree_of_mem_sqSet g N f hf
    have hs : (degType g f).sum = N := (degType_sum g f h0).trans hN
    refine ⟨?_, ?_, hs, degType_pos g f⟩
    · unfold torusCard
      apply Multiset.prod_pos
      intro a ha
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.1 ha
      exact Nat.sub_pos_of_lt (Nat.one_lt_pow (degType_pos g f d hd).ne' hg.out.one_lt)
    · rw [← hs]
      exact prod_pow_sub_one_le g _
  · have hd : degType g (h * f) = degType g h + degType g f := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hh hf, Multiset.map_add (f := _)]
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_add (f := _), Multiset.prod_add]
  · have hd : degType g P = {P.natDegree} := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP, Multiset.map_singleton]
      congr 1
      exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (normalize_associated P))
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_singleton, Multiset.prod_singleton]

end GlobalTheory.BadShare
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → idx B A = idx A B ∧ ∀ v, Fixes W A v → sumOp W B A (sumOp W A B v) = (idx A B : ℂ) • v := by
  first | exact @GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | exact GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | (intros; apply GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul <;> assumption)
end
