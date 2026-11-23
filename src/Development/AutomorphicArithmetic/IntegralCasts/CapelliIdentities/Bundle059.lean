module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Qk67.pow_sub_mem :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (x : NumberField.RingOfIntegers E),
    x ^ (Ideal.absNorm : Ideal (NumberField.RingOfIntegers E) → ℕ) w.asIdeal - x ∈ w.asIdeal := by
  intro E _ _ w x
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Ideal.absNorm w.asIdeal
      = Fintype.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← Ideal.Quotient.eq, map_pow, hcard]
  exact FiniteField.pow_card _
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.ExistsPlace.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.ExistsPlace.exists_place :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (q : ℕ),
      Nat.Prime q → ∃ (w : UpperTheory.Reformulated.B.ExistsPlace.Plc E), (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ q hq
  have hne : (q : NumberField.RingOfIntegers E) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hnu : ¬ IsUnit (q : NumberField.RingOfIntegers E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ (S := NumberField.RingOfIntegers E))
    have h2 : Algebra.norm ℤ (q : NumberField.RingOfIntegers E) =
        (q : ℤ) ^ Module.finrank ℤ (NumberField.RingOfIntegers E) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers E) (q : ℤ)
      simpa using this
    rw [h2] at h1
    have hpos : Module.finrank ℤ (NumberField.RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (q : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact hq.not_isUnit (Int.ofNat_isUnit.1 h3)
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits hnu
  refine ⟨⟨M, hM.isPrime, ?_⟩, hqM⟩
  intro h
  rw [h] at hqM
  exact hne (by simpa using hqM)
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

private theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ^ 2 = -(r : ℂ)) : starRingEnd ℂ z = -z := by
  have hre : z.re * z.re - z.im * z.im = -r := by
    simpa [pow_two] using congrArg Complex.re hz
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im hz
  have hprod : z.re * z.im = 0 := by linarith
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {d : ℕ} {x : E},
      (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  change φ (NumberField.IsCMField.complexConj E x) = φ (-x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  refine UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq (r := (d : ℝ)) (Nat.cast_pos.mpr hd) ?_
  rw [← map_pow, hx, map_neg, map_natCast, Complex.ofReal_natCast]
end

section

open NumberField

theorem UpperTheory.Reformulated.B.Qh9.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice inferInstance
  have hfix : ∀ x : K, c x = x ↔ x ∈ maximalRealSubfield K := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx φ
      have := hc x φ
      rw [hx] at this
      exact this.symm
    · intro hx
      apply φ₀.injective
      rw [hc]
      exact hx φ₀
  have hinv : ∀ x : K, c (c x) = x := by
    intro x
    apply φ₀.injective
    simp [hc]
  let σ : K ≃ₐ[maximalRealSubfield K] K :=
    { toFun := c
      invFun := c
      left_inv := hinv
      right_inv := hinv
      map_mul' := fun x y => φ₀.injective (by simp [hc])
      map_add' := fun x y => φ₀.injective (by simp [hc])
      commutes' := fun x => (hfix _).mpr x.2 }
  have hσ : ∀ x, σ x = c x := fun _ => rfl
  have hne : σ ≠ 1 := by
    intro h1
    apply IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x = x := by rw [← hσ, h1]; rfl
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, hx]
  have hord : orderOf σ = 2 :=
    orderOf_eq_prime (by ext x; simp [pow_two, hσ, hinv]) hne
  have hbot : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.mpr
      ⟨⟨x, (hfix x).mp (hx σ (Subgroup.mem_zpowers σ))⟩, rfl⟩
  have hrank := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers, hord] at hrank
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := ⟨hrank⟩
  exact ⟨⟩
end

section

theorem UpperTheory.Reformulated.B.Qh8.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨x, hx⟩ : ∃ x : K, starRingEnd ℂ (φ₀ x) ≠ φ₀ x := by
    by_contra hne
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    by_contra hz
    exact hne ⟨z, hz⟩
  have hanti : ∀ (z : K) (φ : K →+* ℂ), starRingEnd ℂ (φ (z - c z)) = -φ (z - c z) := by
    intro z φ
    simp [hc]
  obtain ⟨d, hd0, hd⟩ : ∃ d : K, d ≠ 0 ∧ ∀ φ : K →+* ℂ, starRingEnd ℂ (φ d) = -φ d := by
    refine ⟨x - c x, fun h0 => hx ?_, hanti x⟩
    rw [← hc, ← sub_eq_zero.mp h0]
  have hli : LinearIndependent (NumberField.maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    have h1 : s * 1 + t * d = 0 := hst
    have h2 := congrArg φ₀ h1
    have h3 := congrArg (starRingEnd ℂ) h2
    have hs' : starRingEnd ℂ (φ₀ s) = φ₀ s := hs φ₀
    have ht' : starRingEnd ℂ (φ₀ t) = φ₀ t := ht φ₀
    simp only [map_add (f := _), map_mul, map_one, map_zero, hs', ht', hd] at h2 h3
    have hs0 : s = 0 := by
      apply φ₀.injective
      rw [map_zero]
      linear_combination (h2 + h3) / 2
    have ht0 : t = 0 := by
      rw [hs0, zero_mul, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_right hd0
    exact ⟨Subtype.ext hs0, Subtype.ext ht0⟩
  have hsp : ⊤ ≤ Submodule.span (NumberField.maximalRealSubfield K)
      (Set.range ![(1 : K), d]) := by
    intro z _
    have ha : (z + c z) / 2 ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      simp [hc, add_comm, map_ofNat]
    have hb : (z - c z) / (2 * d) ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      rw [map_div₀, map_div₀, hanti, map_mul, map_mul, hd, map_ofNat, map_ofNat, mul_neg,
        neg_div_neg_eq]
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
    change (z + c z) / 2 * 1 + (z - c z) / (2 * d) * d = z
    field_simp
    ring
  have hfin : Module.finrank (NumberField.maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]
  haveI : Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K :=
    { finrank_eq_two' := hfin }
  exact ⟨⟩
end

section

noncomputable def UpperTheory.Reformulated.B.Qh29.cE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

theorem UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] [inst_2 : NumberField.IsCMField K] (y : K),
      (Algebra.algebraMap (↥(NumberField.maximalRealSubfield K)) K : ↥(NumberField.maximalRealSubfield K) → K)
          ((Algebra.norm ↥(NumberField.maximalRealSubfield K) : K → ↥(NumberField.maximalRealSubfield K)) y) =
        y * (UpperTheory.Reformulated.B.Qh29.cE K : K → K) y := by
  intro K _ _ _ y
  classical
  have hne := NumberField.IsCMField.complexConj_ne_one K
  have hcard : Nat.card (K ≃ₐ[NumberField.maximalRealSubfield K] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have huniv : (Finset.univ : Finset (K ≃ₐ[NumberField.maximalRealSubfield K] K)) =
      {1, NumberField.IsCMField.complexConj K} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne.symm, ← Nat.card_eq_fintype_card, hcard]
  have h := Algebra.norm_eq_prod_automorphisms (NumberField.maximalRealSubfield K) y
  rw [huniv, Finset.prod_pair hne.symm] at h
  exact h
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk68.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.Qk68.exists_prime_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (w : UpperTheory.Reformulated.B.Qk68.Plc E),
      ∃ (q : ℕ), Nat.Prime q ∧ (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ w
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  refine ⟨ringChar (NumberField.RingOfIntegers E ⧸ w.asIdeal), ?_, ?_⟩
  · exact (CharP.char_is_prime_or_zero (NumberField.RingOfIntegers E ⧸ w.asIdeal) _).resolve_right
      (CharP.ringChar_ne_zero_of_finite _)
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _
end

section

theorem UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le.{u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (v : NumberField.FinitePlace K) {α : Type u_2} (s : Finset α)
      (f : α → K) {B : ℝ}, (0 : ℝ) ≤ B → (∀ a ∈ s, (v : K → ℝ) (f a) ≤ B) → (v : K → ℝ) (∑ a ∈ s, f a) ≤ B := by
  intro K _ _ v α s f B hB h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.FinitePlace.add_le v _ _).trans
      (max_le (h a (Finset.mem_insert_self a s))
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb)))
end

section

theorem UpperTheory.Reformulated.B.Qh34.aux1.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],
      ∑ x : NumberField.InfinitePlace K,
          (↑x.mult : ℝ) *
            ((NumberField.InfinitePlace.Completion.extensionEmbedding x : x.Completion → ℂ)
                ((0 : NumberField.InfiniteAdeleRing K) x)).re =
        (0 : ℝ) := by
  intro K _ _
  refine Finset.sum_eq_zero fun w _ => ?_
  have h : (0 : NumberField.InfiniteAdeleRing K) w = 0 := rfl
  rw [h, map_zero, Complex.zero_re, mul_zero]

theorem UpperTheory.Reformulated.B.Qh34.aux2.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x y : NumberField.InfiniteAdeleRing K),
      ∑ w : NumberField.InfinitePlace K,
          (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) ((x + y) w)).re =
        ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re +
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (y w)).re := by
  intro K _ _ x y
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (x + y) w = x w + y w := rfl
  rw [h, map_add (f := _), Complex.add_re, mul_add]

noncomputable def UpperTheory.Reformulated.B.Qh34.infiniteTrace.{u_1} :
    (K : Type u_1) → [inst : Field K] → [NumberField K] → NumberField.InfiniteAdeleRing K →+ ℝ :=
    fun (K : Type u_1) [Field K] [NumberField K] ↦
      {
        toFun := fun (x : NumberField.InfiniteAdeleRing K) ↦
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re,
        map_zero' := UpperTheory.Reformulated.B.Qh34.aux1 K, map_add' := UpperTheory.Reformulated.B.Qh34.aux2 K : NumberField.InfiniteAdeleRing K →+ ℝ }

theorem UpperTheory.Reformulated.B.Qh34.infiniteTrace_algebraMap.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (k : K),
      (UpperTheory.Reformulated.B.Qh34.infiniteTrace K : NumberField.InfiniteAdeleRing K → ℝ)
          ((Algebra.algebraMap K (NumberField.InfiniteAdeleRing K) : K → NumberField.InfiniteAdeleRing K) k) =
        (↑((Algebra.trace ℚ K : K → ℚ) k) : ℝ) := by
  classical
  intro K _ _ k
  have h1 : ((Algebra.trace ℚ K k : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ k).re := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := k)
    have h' : ∑ φ : K →+* ℂ, φ k = ∑ σ : K →ₐ[ℚ] ℂ, σ k :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ => rfl)
    rw [← Complex.re_sum, h', ← h]
    simp
  rw [h1, ← Finset.sum_fiberwise Finset.univ NumberField.InfinitePlace.mk]
  change ∑ w : NumberField.InfinitePlace K, (↑w.mult : ℝ) *
    (NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w)).re = _
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w) = w.embedding k := by
    simp
  have h3 : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      (φ k).re = (w.embedding k).re := by
    intro φ hφ
    rw [← (Finset.mem_filter.1 hφ).2]
    rcases NumberField.InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, NumberField.InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]
end

section

open NumberField in
theorem UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le :
    ∀ (E : Type) [inst : Field E] [NumberField E],
    ∃ (C : ℝ) (N : ℕ),
      ∀ (R : ℝ),
        (1 : ℝ) ≤ R →
          {r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.Finite ∧
            (↑{r : NumberField.RingOfIntegers E | ∀ (w : NumberField.InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R}.ncard :
                ℝ) ≤
              C * R ^ N := by
  intro E _ _
  classical
  let L := LinearMap.toContinuousLinearMap (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap
  let c : ℝ := ‖L‖
  have hc : 0 ≤ c := norm_nonneg _
  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E))
  refine ⟨(2 * c + 3) ^ n, n, fun R hR => ?_⟩
  let M : ℕ := ⌈c * R⌉₊
  have hM : c * R ≤ M := Nat.le_ceil _
  have hM' : (M : ℝ) ≤ c * R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  let f : RingOfIntegers E → (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E) → ℤ) :=
    (RingOfIntegers.basis E).equivFun
  have hf : Function.Injective f := (RingOfIntegers.basis E).equivFun.injective
  let T : Finset (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers E) → ℤ) :=
    Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  have hT : T.card = (2 * M + 1) ^ n := by
    have h1 : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]; omega
    simp only [T, n, Fintype.card_piFinset, h1, Finset.prod_const, Finset.card_univ]
  have hmaps : ∀ r ∈ {r : RingOfIntegers E | ∀ (w : InfinitePlace E), (w : E → ℝ) (↑r : E) ≤ R},
      f r ∈ (T : Set _) := by
    intro r hr
    have h1 : ‖canonicalEmbedding E (r : E)‖ ≤ R := by
      rw [canonicalEmbedding.norm_le_iff]
      intro φ
      have := hr (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h2 : ‖L (canonicalEmbedding E (r : E))‖ ≤ M :=
      (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left h1 hc).trans hM)
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h3 := (norm_le_pi_norm _ i).trans h2
    have h4 : L (canonicalEmbedding E (r : E)) i = ((f r i : ℤ) : ℂ) := by
      change (canonicalEmbedding.latticeBasis E).repr (canonicalEmbedding E (r : E)) i = _
      rw [canonicalEmbedding.integralBasis_repr_apply]
      have := integralBasis_repr_apply E r i
      rw [RingOfIntegers.coe_eq_algebraMap, this]
      simp [f]
    rw [h4, Complex.norm_intCast] at h3
    have h5 : |f r i| ≤ (M : ℤ) := by exact_mod_cast h3
    exact abs_le.mp h5
  refine ⟨Set.Finite.of_finite_image (T.finite_toSet.subset ?_) hf.injOn, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact hmaps r hr
  · have h := Set.ncard_le_ncard_of_injOn f hmaps hf.injOn T.finite_toSet
    rw [Set.ncard_coe_finset, hT] at h
    calc _ ≤ (((2 * M + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2 * (M : ℝ) + 1) ^ n := by push_cast; rfl
      _ ≤ ((2 * c + 3) * R) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          nlinarith
      _ = _ := mul_pow _ _ _
end

section

theorem UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
    [inst_4 : Algebra K L] (τ : K →+* ℂ),
    (open Classical in Finset.filter (fun σ : L →+* ℂ => σ.comp (Algebra.algebraMap K L) = τ) Finset.univ).card = Module.finrank K L := by
  intro K L _ _ _ _ _ τ
  classical
  letI : Algebra K ℂ := τ.toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rw [← AlgHom.card K L ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun (f : L →ₐ[K] ℂ) _ => (f : L →+* ℂ)) ?_ ?_ ?_
  · intro f _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, RingHom.ext fun x => f.commutes x⟩
  · intro f _ g _ h
    exact AlgHom.ext fun x => RingHom.congr_fun h x
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact ⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ.2 x }, Finset.mem_univ _, rfl⟩
end

section

theorem UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], ‖(↑p : PadicAlgCl p)‖ = (↑p : ℝ)⁻¹ := by
  intro p _
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends p (p : ℚ_[p])).trans Padic.norm_p
end
