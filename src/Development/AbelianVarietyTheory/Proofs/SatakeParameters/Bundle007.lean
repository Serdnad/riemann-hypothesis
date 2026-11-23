module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

section

open NumberField IsDedekindDomain WithZero

namespace GlobalTheory

theorem ordIdeal_of_ringHom {R W : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (P : HeightOneSpectrum R) (p : W) (hp : Irreducible p) (f : R →+* W)
    (hP : ∀ x : R, x ∈ P.asIdeal ↔ p ∣ f x)
    (hd : ∀ (y : W) (n : ℕ), ∃ (x : R) (z : W), f x = y + p ^ n * z)
    (x : R) (k : ℕ) : x ∈ P.asIdeal ^ k ↔ p ^ k ∣ f x := by

  have hpp : Prime p := hp.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨π, z, hπ⟩ := hd p 2
  have hπP : π ∈ P.asIdeal := (hP π).2 ⟨1 + p * z, by rw [hπ]; ring⟩
  set Q : Ideal R := Ideal.comap f (Ideal.span {p ^ k}) with hQdef
  have hQ : ∀ y : R, y ∈ Q ↔ p ^ k ∣ f y := fun y => by
    rw [hQdef, Ideal.mem_comap, Ideal.mem_span_singleton]
  have hle : P.asIdeal ^ k ≤ Q := by
    have h1 : P.asIdeal ≤ Ideal.comap f (Ideal.span {p}) := fun y hy => by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact (hP y).1 hy
    calc P.asIdeal ^ k ≤ (Ideal.comap f (Ideal.span {p})) ^ k := Ideal.pow_right_mono h1 k
      _ ≤ Ideal.comap f ((Ideal.span {p}) ^ k) := Ideal.le_comap_pow f k
      _ = Q := by rw [Ideal.span_singleton_pow]
  obtain ⟨j, hj, hassoc⟩ := (dvd_prime_pow P.prime k).1 (Ideal.dvd_iff_le.2 hle)
  have hQj : Q = P.asIdeal ^ j := associated_iff_eq.1 hassoc
  have hjk : j = k := by
    by_contra hne
    have hjk' : j ≤ k - 1 := by omega
    have hmem : π ^ (k - 1) ∈ Q := by
      rw [hQj]
      exact Ideal.pow_le_pow_right hjk' (Ideal.pow_mem_pow hπP _)
    rw [hQ, map_pow, hπ] at hmem
    have hfac : (p + p ^ 2 * z) ^ (k - 1) = p ^ (k - 1) * (1 + p * z) ^ (k - 1) := by
      rw [← mul_pow]; ring
    have hk' : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hfac, hk'] at hmem
    have hdiv := (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hp0)).1 hmem
    have hdiv' := hpp.dvd_of_dvd_pow hdiv
    have hone : p ∣ 1 := (dvd_add_left (dvd_mul_right p z)).1 hdiv'
    exact hp.not_isUnit (isUnit_of_dvd_one hone)
  rw [← hQ, hQj, hjk]

theorem ordIdeal_of_embedding {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ) : ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by

  intro hxy
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  choose F hF using h1
  let f : 𝓞 E →+* W :=
    { toFun := F
      map_one' := hinj (by rw [← (hF 1).1]; simp)
      map_mul' := fun a b => hinj (by
        rw [map_mul, ← (hF (a * b)).1, ← (hF a).1, ← (hF b).1]; simp)
      map_zero' := hinj (by rw [← (hF 0).1]; simp)
      map_add' := fun a b => hinj (by
        rw [map_add (f := _), ← (hF (a + b)).1, ← (hF a).1, ← (hF b).1]; simp) }
  have hfx : ∀ a : 𝓞 E, algebraMap W Qq (f a) = ρ a := fun a => ((hF a).1).symm
  have hP : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ (p : W) ∣ f a := fun a => (hF a).2
  have hd : ∀ (b : W) (n : ℕ), ∃ (a : 𝓞 E) (c : W), f a = b + (p : W) ^ n * c := by
    intro b n
    obtain ⟨a, c, hac⟩ := h2 b n
    exact ⟨a, c, hinj (by rw [hfx, hac])⟩
  have hy : f x = y := hinj (by rw [hfx, hxy])
  rw [ordIdeal_of_ringHom P (p : W) hp f hP hd x k, hy]

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

open NumberField in
private theorem exists_integral_generator_common_denom_of_finrank_two
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra! hx
    have htop : (⊤ : IntermediateField F E) = ⊥ := by
      ext x
      simp only [IntermediateField.mem_top, true_iff]
      exact IntermediateField.mem_bot.mpr (hx x)
    have h1 := IntermediateField.finrank_eq_one_iff.mpr htop
    rw [IntermediateField.finrank_top'] at h1
    omega
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have hint : IsIntegral ℤ (n • x) := hnx x (Finset.mem_singleton_self x)
  obtain ⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x :=
    ⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hθ : (θ : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hx
    refine ⟨a / n, ?_⟩
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
    rw [map_div₀, map_intCast, ha, hθx]
    field_simp
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  obtain ⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Fin.sum_univ_two, hb1]
    simp [Algebra.smul_def]
  set B := RingOfIntegers.basis E
  obtain ⟨d, hd, hdint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 =>
      b.repr (B p.1 : E) p.2)
  have hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k) := fun i k =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  refine ⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩
  let M : Submodule ℤ (𝓞 E) :=
    { carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ}
      add_mem' := by
        rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
        exact ⟨u + u', v + v', by simp only [map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨u, v, rfl⟩
        exact ⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }
  have hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M := by
    intro y
    have hspan : y ∈ Submodule.span ℤ (Set.range B) := by rw [B.span_eq]; trivial
    induction hspan using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩
      rw [RingOfIntegers.ext_iff]
      have e := hb (B i : E)
      have key : algebraMap F E (d : F) * (B i : E) =
          algebraMap F E (d • b.repr (B i : E) 0) +
            algebraMap F E (d • b.repr (B i : E) 1) * θ := by
        simp only [zsmul_eq_mul, map_mul, map_intCast]
        linear_combination (d : E) * e
      exact key
    | zero => simpa using M.zero_mem
    | add z w _ _ hz hw => rw [mul_add]; exact M.add_mem hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact M.smul_mem c hz
  intro y
  obtain ⟨u, v, huv⟩ := hall y
  exact ⟨u, v, huv⟩


open NumberField in
theorem _root_.GlobalTheory.quadratic_exists_integral_generator_common_denominator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  intro F E _ _ _ _ _ _
  exact exists_integral_generator_common_denom_of_finrank_two F E
    (Algebra.IsQuadraticExtension.finrank_eq_two F E)

end GlobalTheory
end

section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace GlobalTheory

theorem exists_realPlace_embedding {F : Type} [Field F] [NumberField F] (τ : F →+* ℝ) :
    ∃ (P : InfinitePlace F) (hP : P.IsReal), embedding_of_isReal hP = τ := by
  have hreal : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hP : (InfinitePlace.mk (Complex.ofRealHom.comp τ)).IsReal := isReal_mk_iff.2 hreal
  refine ⟨_, hP, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal hreal]
  simp

theorem exists_integer_near (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ w : (F →+* ℝ) → ℝ, ∃ z : 𝓞 F, ∀ τ : F →+* ℝ, |τ (z : F) - w τ| ≤ C := by
  classical
  have hfin : Finite (F →+* ℝ) := by
    refine Finite.of_injective (fun τ => (Complex.ofRealHom.comp τ : F →+* ℂ)) ?_
    intro a b h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h
    simpa using this
  have := Fintype.ofFinite (F →+* ℝ)
  let b := RingOfIntegers.basis F
  refine ⟨∑ τ : F →+* ℝ, ∑ i, |τ ((b i : 𝓞 F) : F)|, fun w => ?_⟩
  let v : mixedSpace F := (fun w' => w (embedding_of_isReal w'.2), 0)
  let c := (latticeBasis F).repr v
  refine ⟨∑ i, round (c i) • b i, fun τ => ?_⟩
  obtain ⟨P, hP, hτ⟩ := exists_realPlace_embedding τ
  have hv : v = ∑ i, c i • latticeBasis F i := ((latticeBasis F).sum_repr v).symm
  have hw : w τ = ∑ i, c i * τ ((b i : 𝓞 F) : F) := by
    have h1 := congrArg (fun u : mixedSpace F => u.1 ⟨P, hP⟩) hv
    simp only [v, hτ] at h1
    rw [h1]
    simp [Prod.fst_sum, Finset.sum_apply, latticeBasis_apply, integralBasis_apply,
      mixedEmbedding_apply_isReal, hτ, b, c, v]
  have hz : τ (((∑ i, round (c i) • b i : 𝓞 F)) : F)
      = ∑ i, (round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  rw [hz, hw, ← Finset.sum_sub_distrib]
  calc |∑ i, ((round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) - c i * τ ((b i : 𝓞 F) : F))|
      ≤ ∑ i, |(round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) - c i * τ ((b i : 𝓞 F) : F)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |τ ((b i : 𝓞 F) : F)| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sub_mul, abs_mul]
        have h2 : |(round (c i) : ℝ) - c i| ≤ 1 := by
          have := abs_sub_round (c i)
          rw [abs_sub_comm]
          linarith
        exact mul_le_of_le_one_left (abs_nonneg _) h2
    _ ≤ ∑ τ' : F →+* ℝ, ∑ i, |τ' ((b i : 𝓞 F) : F)| :=
        Finset.single_le_sum (f := fun τ' : F →+* ℝ => ∑ i, |τ' ((b i : 𝓞 F) : F)|)
          (fun τ' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ τ)

theorem residueClass_relativelyDense : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (m : Ideal (𝓞 F)) (a₀ : 𝓞 F), m ≠ ⊥ →
    ∃ C : ℝ, ∀ y : (F →+* ℝ) → ℝ, ∃ a : 𝓞 F, a - a₀ ∈ m ∧
      ∀ τ : F →+* ℝ, |τ (a : F) - y τ| ≤ C := by
  intro F _ _ _ m a₀ hm
  obtain ⟨C, hC⟩ := exists_integer_near F
  have hMpos : 0 < Ideal.absNorm m := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.1 h))
  set M : ℕ := Ideal.absNorm m with hMdef
  have hMmem : ((M : ℕ) : 𝓞 F) ∈ m := Ideal.absNorm_mem m
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMpos
  refine ⟨M * C, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hC (fun τ => (y τ - τ (a₀ : F)) / M)
  refine ⟨a₀ + (M : 𝓞 F) * z, ?_, fun τ => ?_⟩
  · simpa using m.mul_mem_right z hMmem
  · have h := hz τ
    have h3 : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) - y τ
        = M * (τ (z : F) - (y τ - τ (a₀ : F)) / M) := by
      have : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) = τ (a₀ : F) + M * τ (z : F) := by
        simp
      rw [this]
      field_simp
      ring
    rw [h3, abs_mul, abs_of_pos hM0]
    exact mul_le_mul_of_nonneg_left h hM0.le

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E]
    (w : InfinitePlace E) (θ : E) (hθ : θ ∉ Set.range (algebraMap F E)) :
    (w.embedding θ).im ≠ 0 := by
  intro h
  set φ := w.embedding with hφ
  have hF : ∀ c : F, (φ (algebraMap F E c)).im = 0 := by
    intro c
    have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have := ComplexEmbedding.isReal_iff.1 hr
    have h2 := RingHom.congr_fun this c
    exact Complex.conj_eq_iff_im.1 h2
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-(s / t), ?_⟩
      have : t • θ = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      rw [mul_comm] at this
      linear_combination -this
  have hspan : Submodule.span F (Set.range ![(1 : E), θ]) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [Algebra.IsQuadraticExtension.finrank_eq_two F E]
  have hall : ∀ z : E, (φ z).im = 0 := by
    intro z
    have hz : z ∈ Submodule.span F (Set.range ![(1 : E), θ]) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hz
    rw [← hc, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def,
      mul_one, map_add, map_mul, Complex.add_im, Complex.mul_im, hF, h, zero_mul, mul_zero,
      add_zero]
  have hreal : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext1 z
    exact Complex.conj_eq_iff_im.2 (hall z)
  exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 hreal)

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem infinitePlace_eq_of_embedding_comp_algebraMap_eq (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E)
    (h : w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E)) : w₁ = w₂ := by
  classical
  set τ : F →+* ℂ := w₁.embedding.comp (algebraMap F E) with hτ
  have hτreal : ComplexEmbedding.IsReal τ := by
    have := IsTotallyReal.isReal (InfinitePlace.mk τ)
    exact InfinitePlace.isReal_mk_iff.mp this
  letI : Algebra F ℂ := τ.toAlgebra
  have mkAlg : ∀ σ : E →+* ℂ, σ.comp (algebraMap F E) = τ → ∃ a : E →ₐ[F] ℂ, (a : E →+* ℂ) = σ :=
    fun σ hσ => ⟨{ σ with
      commutes' := fun r => by
        change σ (algebraMap F E r) = τ r
        rw [← hσ]; rfl }, rfl⟩
  obtain ⟨a, ha⟩ := mkAlg w₁.embedding rfl
  obtain ⟨b, hb⟩ := mkAlg (ComplexEmbedding.conjugate w₁.embedding) (by
    ext r
    have := RingHom.congr_fun hτreal r
    simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply]
    simpa [ComplexEmbedding.conjugate_coe_eq, hτ] using this)
  obtain ⟨c, hc⟩ := mkAlg w₂.embedding h.symm
  have hab : a ≠ b := by
    intro hab
    have hc1 : ¬ ComplexEmbedding.IsReal w₁.embedding := by
      rw [← InfinitePlace.isReal_iff]
      exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w₁)
    apply hc1
    rw [ComplexEmbedding.isReal_iff, ← hb, ← ha, hab]
  have hcard : Fintype.card (E →ₐ[F] ℂ) = 2 := by
    rw [AlgHom.card, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hcab : c = a ∨ c = b := by
    by_contra hne
    push_neg at hne
    have h3 : ({a, b, c} : Finset (E →ₐ[F] ℂ)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact fun e => hne.2 e.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, fun e => hne.1 e.symm⟩
    have := Finset.card_le_univ ({a, b, c} : Finset (E →ₐ[F] ℂ))
    omega
  rw [← InfinitePlace.mk_embedding w₁, ← InfinitePlace.mk_embedding w₂, InfinitePlace.mk_eq_iff]
  rcases hcab with e | e
  · left; rw [← ha, ← hc, e]
  · right; rw [← hb, ← hc, e]

end GlobalTheory
end

section

namespace GlobalTheory

theorem endo_indecomposable_finite_length_nilpotent_or_bijective :
    ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
      (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) →
      ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  intro R P _ _ _ _ _ hind f
  obtain ⟨n, hn⟩ := (LinearMap.eventually_isCompl_ker_pow_range_pow f).exists_forall_of_atTop
  have hc := hn (n + 1) (Nat.le_succ n)
  rcases hind _ _ hc with hk | hr
  · right
    have hk1 : LinearMap.ker f = ⊥ := by
      rw [eq_bot_iff, ← hk]
      intro x hx
      have hx' : f x = 0 := hx
      rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hx', map_zero]
    have hr1 : LinearMap.range (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hk, bot_sup_eq] at this
    have hs : LinearMap.range f = ⊤ := by
      rw [eq_top_iff, ← hr1]
      rintro _ ⟨x, rfl⟩
      rw [pow_succ', Module.End.mul_apply]
      exact ⟨_, rfl⟩
    exact ⟨LinearMap.ker_eq_bot.mp hk1, LinearMap.range_eq_top.mp hs⟩
  · left
    refine ⟨n + 1, ?_⟩
    have hk1 : LinearMap.ker (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hr, sup_bot_eq] at this
    exact LinearMap.ker_eq_top.mp hk1

end GlobalTheory
end
