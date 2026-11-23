module

public import Mathlib.MeasureTheory.Measure.Prod
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoSublevelDensityProdMeasure
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.tendsto_sublevel_density_prod_measure : ∀ (A₁ E₁ A₂ E₂ : Type) [MeasurableSpace A₁] [MeasurableSpace E₁] [MeasurableSpace A₂] [MeasurableSpace E₂] (m₁ : Measure A₁) (l₁ : Measure E₁) (m₂ : Measure A₂) (l₂ : Measure E₂) [SFinite m₁] [SFinite l₁] [SFinite m₂] [SFinite l₂] (n₁ : A₁ → ℝ) (N₁ : E₁ → ℝ) (n₂ : A₂ → ℝ) (N₂ : E₂ → ℝ) (c₁ c₂ : ℝ≥0∞), Measurable n₁ → Measurable N₁ → Measurable n₂ → Measurable N₂ → (∀ x, 0 ≤ n₁ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ n₂ x) → (∀ x, 0 ≤ N₂ x) → c₁ ≠ ⊤ → c₂ ≠ ⊤ → (∀ r : ℝ, 0 < r → l₁ {x | N₁ x < r} ≠ 0 ∧ l₁ {x | N₁ x < r} ≠ ⊤) → (∀ r : ℝ, 0 < r → l₂ {x | N₂ x < r} ≠ 0 ∧ l₂ {x | N₂ x < r} ≠ ⊤) → Tendsto (fun r : ℝ => m₁ {x | n₁ x < r} / l₁ {x | N₁ x < r}) (𝓝[>] 0) (𝓝 c₁) → Tendsto (fun r : ℝ => m₂ {x | n₂ x < r} / l₂ {x | N₂ x < r}) (𝓝[>] 0) (𝓝 c₂) → Tendsto (fun r : ℝ => (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} / (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
  first | exact @GlobalTheory.SublevelDensity.tendsto_prod_density | exact GlobalTheory.SublevelDensity.tendsto_prod_density | (intros; apply GlobalTheory.SublevelDensity.tendsto_prod_density <;> assumption)
end

section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

namespace GlobalTheory.CompletionAut

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem exists_natCast_valued_lt_one :
    ∃ p : ℕ, (p : v.adicCompletion F) ≠ 0 ∧ Valued.v (p : v.adicCompletion F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, ?_⟩
  · haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · have h := Ideal.absNorm_mem v.asIdeal
    have h2 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F)
          (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) := by simp
    rw [h2]
    erw [valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem v _).2 h

theorem exists_pow_eq_of_mem {p : ℕ} (hp : Valued.v (p : v.adicCompletion F) < 1) (e : ℕ)
    {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ y : v.adicCompletion F, y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1) := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set R := v.adicCompletionIntegers F
  have hpm : (p : R) ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h
    have h' : Valued.v (p : v.adicCompletion F) = 1 := by simpa using h
    exact hp.ne h'
  let c : R := 1 + p * (⟨x, hx⟩ : R) ^ (p * e + 1)
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R)
    (X ^ (p * e + 1) - C c) (monic_X_pow_sub_C c (Nat.succ_ne_zero _)) 1
    (by
      simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow, c]
      have : (1 : R) - (1 + p * (⟨x, hx⟩ : R) ^ (p * e + 1)) =
          p * (-(⟨x, hx⟩ : R) ^ (p * e + 1)) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hpm)
    (by
      have h0 : Ideal.Quotient.mk (maximalIdeal R) (p : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 hpm
      rw [map_natCast] at h0
      simp [derivative_X_pow, h0])
  refine ⟨a, ?_⟩
  have h1 : a ^ (p * e + 1) = c := by
    simpa [IsRoot, sub_eq_zero] using ha
  have := congrArg (fun z : R => (z : v.adicCompletion F)) h1
  simpa [c] using this

theorem mem_of_pow_eq {p e : ℕ} (he : 0 < e)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-(e : ℤ))) (hp0 : p ≠ 0)
    {x y : v.adicCompletion F} (h : y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1)) :
    x ∈ v.adicCompletionIntegers F := by
  rw [mem_adicCompletionIntegers]
  by_contra hx
  push Not at hx
  have hx0 : Valued.v x ≠ 0 := (zero_lt_one.trans hx).ne'
  set l := p * e + 1 with hl
  have hle : e < l := by
    have : e ≤ p * e := Nat.le_mul_of_pos_left e (Nat.pos_of_ne_zero hp0)
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hm0 : 0 < m := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx; exact hx
  have h1 : Valued.v ((p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [map_mul, map_pow, hp, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]
  have hpos : 0 < -(e : ℤ) + l * m := by
    have : (e : ℤ) < l := by exact_mod_cast hle
    nlinarith
  have h2 : Valued.v (1 + (p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [← h1]
    apply Valuation.map_add_eq_of_lt_right
    rw [h1, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact hpos
  rw [← h, map_pow] at h2
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h2
    exact WithZero.exp_ne_zero h2.symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v y = WithZero.exp k := ⟨_, (WithZero.exp_log hy0).symm⟩
  rw [hk, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  have hd : (l : ℤ) ∣ (e : ℤ) := ⟨m - k, by linear_combination h2⟩
  have := Nat.le_of_dvd he (Int.natCast_dvd_natCast.1 hd)
  omega

theorem map_mem (θ : v.adicCompletion F →+* v.adicCompletion F) {x : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) : θ x ∈ v.adicCompletionIntegers F := by
  obtain ⟨p, hp0, hp⟩ := exists_natCast_valued_lt_one v
  have hv0 : Valued.v (p : v.adicCompletion F) ≠ 0 := by simpa using hp0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (p : v.adicCompletion F) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  have hm0 : m < 0 := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hp; exact hp
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m by omega)
  obtain ⟨y, hy⟩ := exists_pow_eq_of_mem v hp e hx
  refine mem_of_pow_eq v (p := p) (e := e) (y := θ y) (by omega) (by rw [hm, ← he, neg_neg])
    (by rintro rfl; simp at hp0) ?_
  simpa using congrArg θ hy

end GlobalTheory.CompletionAut

namespace GlobalTheory

theorem ringEquiv_adicCompletion_mem_integers_iff (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (θ : v.adicCompletion F ≃+* v.adicCompletion F)
    (x : v.adicCompletion F) :
    θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F :=
  ⟨fun h => by simpa using CompletionAut.map_mem v θ.symm.toRingHom h,
    fun h => CompletionAut.map_mem v θ.toRingHom h⟩

end GlobalTheory
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SplitPlace

open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
private lemma isMaximal_and_algebraMap_mem_iff_of_mem_primesOver (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (h : P ∈ v.asIdeal.primesOver (𝓞 E)) :
    P.IsMaximal ∧ ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ P ↔ a ∈ v.asIdeal := by
  obtain ⟨hp, ho⟩ := h
  haveI := hp; haveI := ho; haveI := v.isMaximal
  refine ⟨Ideal.IsMaximal.of_liesOver_isMaximal P v.asIdeal, fun a => ?_⟩
  rw [Ideal.over_def P v.asIdeal, Ideal.under_def, Ideal.mem_comap]

open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
private lemma exists_root_quadratic_of_isUnit_of_mem_maximalIdeal (R : Type) [CommRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (b c : R)
    (hb : IsUnit b) (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ β : R, β ^ 2 + b * β + c = 0 := by
  have hmon : (X ^ 2 + C b * X + C c : R[X]).Monic := by monicity!
  obtain ⟨β, hβ, -⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal R)
    (X ^ 2 + C b * X + C c) hmon 0 (by simpa using hc) (by simpa using hb.map _)
  exact ⟨β, by simpa using hβ⟩


open scoped TensorProduct in
open NumberField IsDedekindDomain Polynomial in
theorem _root_.GlobalTheory.SplitPlace.not_isField_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F),
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 → ¬ IsField (v.adicCompletion F ⊗[F] E) := by
  intro F E _ _ _ _ _ hrank v hsplit hfield
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp hsplit
  obtain ⟨hPmax, hPmem⟩ := isMaximal_and_algebraMap_mem_iff_of_mem_primesOver F E v P
    (by rw [hset]; exact Set.mem_insert _ _)
  obtain ⟨hQmax, hQmem⟩ := isMaximal_and_algebraMap_mem_iff_of_mem_primesOver F E v Q
    (by rw [hset]; exact Set.mem_insert_of_mem _ rfl)
  obtain ⟨α, hαP, hαQ⟩ := SetLike.not_le_iff_exists.mp
    (fun h => hPQ (hPmax.eq_of_le hQmax.ne_top h))
  have hαF : (α : E) ∉ (algebraMap F E).range := by
    rintro ⟨a, ha⟩
    have hint : IsIntegral ℤ a := by
      have h1 : IsIntegral ℤ (algebraMap F E a) := ha ▸ RingOfIntegers.isIntegral_coe α
      exact (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars ℤ)
        (algebraMap F E).injective).mp h1
    have hα : algebraMap (𝓞 F) (𝓞 E) ⟨a, hint⟩ = α := RingOfIntegers.ext (by rw [← ha]; rfl)
    have hav : (⟨a, hint⟩ : 𝓞 F) ∈ v.asIdeal := (hPmem _).mp (hα ▸ hαP)
    exact hαQ (hα ▸ (hQmem _).mpr hav)
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hrank
  have hint : IsIntegral (𝓞 F) α := Algebra.IsIntegral.isIntegral α
  have hdeg : (minpoly (𝓞 F) α).natDegree = 2 := by
    have hE : minpoly (𝓞 F) (α : E) = minpoly (𝓞 F) α :=
      minpoly.algHom_eq (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E) Subtype.val_injective α
    have hF : minpoly F (α : E) = (minpoly (𝓞 F) α).map (algebraMap (𝓞 F) F) := by
      rw [← hE]
      exact minpoly.isIntegrallyClosed_eq_field_fractions' F (hint.map (IsScalarTower.toAlgHom (𝓞 F) (𝓞 E) E))
    have hle : (minpoly F (α : E)).natDegree ≤ 2 := hrank ▸ minpoly.natDegree_le (α : E)
    have hne1 : (minpoly F (α : E)).natDegree ≠ 1 := fun h => hαF (minpoly.natDegree_eq_one_iff.mp h)
    have hpos : 0 < (minpoly F (α : E)).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
    rw [hF, (minpoly.monic hint).natDegree_map] at hle hne1 hpos
    omega
  set b := (minpoly (𝓞 F) α).coeff 1 with hb
  set c := (minpoly (𝓞 F) α).coeff 0 with hc
  have hα2 : α ^ 2 + algebraMap (𝓞 F) (𝓞 E) b * α + algebraMap (𝓞 F) (𝓞 E) c = 0 := by
    have h := minpoly.aeval (𝓞 F) α
    have h2 : (minpoly (𝓞 F) α).coeff 2 = 1 := by
      rw [← hdeg]; exact (minpoly.monic hint).coeff_natDegree
    rw [aeval_eq_sum_range, hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      h2] at h
    simp only [Algebra.smul_def, map_one, one_mul, pow_zero, pow_one, mul_one] at h
    linear_combination h
  have hcv : c ∈ v.asIdeal := by
    rw [← hPmem]
    have hce : algebraMap (𝓞 F) (𝓞 E) c = -(α ^ 2 + algebraMap (𝓞 F) (𝓞 E) b * α) := by
      linear_combination hα2
    rw [hce]
    exact P.neg_mem (P.add_mem (P.pow_mem_of_mem hαP 2 two_pos) (P.mul_mem_left _ hαP))
  have hbv : b ∉ v.asIdeal := by
    intro hbv
    have hsq : α ^ 2 = -(algebraMap (𝓞 F) (𝓞 E) b * α + algebraMap (𝓞 F) (𝓞 E) c) := by
      linear_combination hα2
    have hmem : α ^ 2 ∈ Q := by
      rw [hsq]
      exact Q.neg_mem (Q.add_mem (Q.mul_mem_right _ ((hQmem b).mpr hbv)) ((hQmem c).mpr hcv))
    exact hαQ (hQmax.isPrime.mem_of_pow_mem 2 hmem)
  haveI := _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  obtain ⟨β, hβ⟩ := exists_root_quadratic_of_isUnit_of_mem_maximalIdeal
    (v.adicCompletionIntegers F) (algebraMap (𝓞 F) _ b) (algebraMap (𝓞 F) _ c)
    ((_root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v b).mpr hbv)
    (by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, _root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
      exact not_not.mpr hcv)
  have hβF : (β : v.adicCompletion F) ^ 2 + algebraMap F (v.adicCompletion F) (b : F) * β
      + algebraMap F (v.adicCompletion F) (c : F) = 0 := by
    have h := congrArg (v.adicCompletionIntegers F).subtype hβ
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, map_zero] at h
    exact h
  have hαE : (α : E) ^ 2 + algebraMap F E (b : F) * α + algebraMap F E (c : F) = 0 := by
    have h := congrArg (algebraMap (𝓞 E) E) hα2
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, map_zero] at h
    exact h
  set x : v.adicCompletion F ⊗[F] E :=
    Algebra.TensorProduct.includeLeft (S := F) (B := E) (β : v.adicCompletion F) with hx
  set y : v.adicCompletion F ⊗[F] E :=
    Algebra.TensorProduct.includeRight (A := v.adicCompletion F) (α : E) with hy
  have hxeq : x ^ 2 + algebraMap F _ (b : F) * x + algebraMap F _ (c : F) = 0 := by
    have h := congrArg (Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := E)) hβF
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_zero] at h
    exact h
  have hyeq : y ^ 2 + algebraMap F _ (b : F) * y + algebraMap F _ (c : F) = 0 := by
    have h := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := v.adicCompletion F)) hαE
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, AlgHom.commutes, AlgHom.commutes, map_zero] at h
    exact h
  have hprod : (x - y) * (x + y + algebraMap F _ (b : F)) = 0 := by
    linear_combination hxeq - hyeq
  haveI := hfield.isDomain
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletion F,
      y = Algebra.TensorProduct.includeLeft (S := F) (B := E) z := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact ⟨β, (sub_eq_zero.mp h).symm⟩
    · refine ⟨-(β : v.adicCompletion F) - algebraMap F _ (b : F), ?_⟩
      rw [map_sub, map_neg, AlgHom.commutes, ← hx]
      linear_combination h
  obtain ⟨ℓ, hℓ1, hℓα⟩ : ∃ ℓ : E →ₗ[F] F, ℓ 1 = 0 ∧ ℓ α = 1 := by
    have hnot : (α : E) ∉ Submodule.span F {(1 : E)} := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, ha⟩
      exact hαF ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩
    obtain ⟨ℓ, hℓ, hℓα⟩ :=
      LinearMap.exists_extend_of_notMem (0 : Submodule.span F {(1 : E)} →ₗ[F] F) hnot 1
    refine ⟨ℓ, ?_, hℓα⟩
    have h := LinearMap.congr_fun hℓ ⟨1, Submodule.mem_span_singleton_self 1⟩
    simpa using h
  have key := congrArg ((TensorProduct.rid F (v.adicCompletion F)).toLinearMap ∘ₗ
    LinearMap.lTensor (v.adicCompletion F) ℓ) hz
  simp [hy, hℓ1, hℓα, Algebra.TensorProduct.includeLeft_apply] at key

end GlobalTheory.SplitPlace
end
