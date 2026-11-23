module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle082
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.FieldTheory.IsSepClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle077
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle086
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle084
public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle145
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

section

open Polynomial

namespace GlobalTheory.PicDiv

theorem classGroup_nthPower_of_codim_one_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  intro k A _ _ _ _ _ _ N _hN hyp hf c
  obtain ⟨f, hf0, hfm⟩ := hf
  obtain ⟨_hfin, hmax, hadd, _hle⟩ := GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A
  have nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A) := fun I hI =>
    mem_nonZeroDivisors_of_ne_zero hI
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI0 : (I : Ideal A) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  by_cases hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥
  swap
  · push_neg at hex
    have htop : (I : Ideal A) = ⊤ := by
      by_contra h
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ h
      exact hI0 (le_bot_iff.mp (hex M hM ▸ hIM))
    refine ⟨1, ?_⟩
    have : I = 1 := Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)
    rw [this, map_one, one_pow]
  obtain ⟨P₀, hP₀, hP₀ne⟩ := hex
  let H : Subgroup (ClassGroup A) := (powMonoidHom N : ClassGroup A →* ClassGroup A).range
  let π : ClassGroup A →* ClassGroup A ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ d : ClassGroup A, π (d ^ N) = 1 := fun d =>
    (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩
  let γ : ClassGroup A := ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩
  have hbot : ¬ (⊥ : Ideal A).IsMaximal := fun h =>
    hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm
  have hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q := by
    intro x hx
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
    have hj : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical
    by_contra hne
    push_neg at hne
    apply hx
    have : x ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson]
      exact Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2
    rw [hj] at this
    exact (Submodule.mem_bot A).mp this
  have hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥),
      π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ := by
    intro P hP hPne
    obtain ⟨a₀, ha₀, H0⟩ := hyp P₀ hP₀ (nz P₀ hP₀ne)
    obtain ⟨a₁, ha₁, H1⟩ := hyp P hP (nz P hPne)
    obtain ⟨Q, hQ, hQa⟩ := hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)
    have hQne : Q ≠ ⊥ := by rintro rfl; exact hbot hQ
    obtain ⟨d, hd⟩ := H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)
    obtain ⟨e, he⟩ := H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)
    have h1 := congrArg π hd
    have h2 := congrArg π he
    rw [map_mul, hπ, mul_one] at h1 h2
    rw [← h2, h1]
  have hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_
    · intro h; exact absurd rfl (nonZeroDivisors.ne_zero h)
    · intro x hx h
      have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx'
      have e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1 := Subtype.ext Ideal.one_eq_top.symm
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]
    · intro a p ha hp ih h
      have hpne : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpne
      have e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩ := rfl
      rw [e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha,
        (hmax p hpmax).1, pow_add, pow_one]
  have hγN : π γ ^ N = 1 := by rw [← map_pow]; exact hπ γ
  have hspan : Ideal.span {f} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hf0
  have hγ1 : π γ = 1 := by
    have e := hall _ (nz _ hspan)
    have e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1 :=
      (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩
    rw [e0, map_one] at e
    calc π γ = π γ ^ (1 % N) := by rw [← pow_eq_pow_mod 1 hγN, pow_one]
      _ = π γ ^ (Module.finrank k (A ⧸ Ideal.span {f}) % N) := by rw [hfm]
      _ = 1 := by rw [← pow_eq_pow_mod _ hγN, ← e]
  have hc := hall I.1 I.2
  rw [hγ1, one_pow] at hc
  have hmem : ClassGroup.mk0 I ∈ H := (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, hd.symm⟩

end GlobalTheory.PicDiv
end

section

open Polynomial GlobalTheory.EtC

namespace GlobalTheory

theorem exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [hP : P.IsMaximal] (b : B) :
    ∃ c : k, b - algebraMap k B c ∈ P := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  let φ : (B ⧸ P) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ (Ideal.Quotient.mk P b), ?_⟩
  have h : algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) = Ideal.Quotient.mk P b := by
    apply φ.toRingHom.injective
    simp
  have h2 : Ideal.Quotient.mk P (algebraMap k B (φ (Ideal.Quotient.mk P b))) =
      algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) := rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h2, h, sub_self]

theorem exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ) (hq : IsUnit (q : k))
    (P : Ideal B) [hP : P.IsMaximal] (b : B) (hb : b ∉ P) :
    ∀ m : ℕ, ∃ r : B, b - r ^ q ∈ P ^ (m + 1) := by
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hq
    · exact h
  have hqB : IsUnit (q : B) := by
    have := hq.map (algebraMap k B); simpa using this
  intro m
  induction m with
  | zero =>
    obtain ⟨c, hc⟩ := exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed k B P b
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hq0
    refine ⟨algebraMap k B z, ?_⟩
    rw [← map_pow, hz]; simpa using hc
  | succ m ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, e = b - r ^ q := ⟨_, rfl⟩
    rw [← he] at hr
    have hrP : r ∉ P := by
      intro h
      apply hb
      have h1 : r ^ q ∈ P := P.pow_mem_of_mem h q hq0
      have h2 : e ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero m) hr
      have : b = e + r ^ q := by rw [he]; ring
      rw [this]; exact P.add_mem h2 h1
    have hderP : (q : B) * r ^ (q - 1) ∉ P := by
      intro h
      rcases hP.isPrime.mem_or_mem h with h | h
      · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P h hqB)
      · exact hrP (hP.isPrime.mem_of_pow_mem _ h)
    obtain ⟨w, i, hi, hw⟩ := hP.exists_inv hderP
    obtain ⟨t, ht⟩ := binomExpansion (X ^ q : B[X]) r (e * w)
    simp [derivative_X_pow] at ht
    refine ⟨r + e * w, ?_⟩
    have key : b - (r + e * w) ^ q = e * i - t * w ^ 2 * e ^ 2 := by
      rw [ht]; linear_combination (-e) * hw - he
    rw [key]
    refine Ideal.sub_mem _ ?_ ?_
    · rw [pow_succ]; exact Ideal.mul_mem_mul hr hi
    · apply Ideal.mul_mem_left
      have h3 : e ^ 2 ∈ (P ^ (m + 1)) ^ 2 := Ideal.pow_mem_pow hr 2
      rw [← pow_mul] at h3
      exact Ideal.pow_le_pow_right (by omega) h3

theorem exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ),
    IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b c : B, b * c - 1 ∈ Ideal.span {f} →
      ∃ r : B, b - r ^ q ∈ Ideal.span {f} := by
  intro k B _ _ _ _ _ _ q hq f hf b c hbc
  classical
  have hI : Ideal.span {f} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf
  have hroot : ∀ P : (UniqueFactorizationMonoid.factors (Ideal.span {f})).toFinset, ∃ r : B,
      b - r ^ q ∈ (P : Ideal B) ^ Multiset.count (P : Ideal B)
        (UniqueFactorizationMonoid.factors (Ideal.span {f})) := by
    intro P
    have hmem := Multiset.mem_toFinset.mp P.prop
    have hprime : Prime (P : Ideal B) := UniqueFactorizationMonoid.prime_of_factor _ hmem
    have hne : (P : Ideal B) ≠ ⊥ := hprime.ne_zero
    haveI hmax : (P : Ideal B).IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hne
    have hle : Ideal.span {f} ≤ (P : Ideal B) :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hmem)
    have hb : b ∉ (P : Ideal B) := by
      intro h
      apply hmax.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 := hle hbc
      have : (1 : B) = b * c - (b * c - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h) h1
    obtain ⟨r, hr⟩ := exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed k B q hq (P : Ideal B) b hb
      (Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors (Ideal.span {f})))
    exact ⟨r, Ideal.pow_le_pow_right (Nat.le_succ _) hr⟩
  choose r hr using hroot
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    ((IsDedekindDomain.quotientEquivPiFactors hI).symm (fun P => Ideal.Quotient.mk _ (r P)))
  refine ⟨s, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (IsDedekindDomain.quotientEquivPiFactors hI).injective
  rw [map_zero]
  funext P
  have h1 := congrFun (congrArg (IsDedekindDomain.quotientEquivPiFactors hI) hs) P
  rw [RingEquiv.apply_symm_apply, IsDedekindDomain.quotientEquivPiFactors_mk] at h1
  simp only at h1
  rw [IsDedekindDomain.quotientEquivPiFactors_mk]
  show Ideal.Quotient.mk _ (b - s ^ q) = 0
  rw [map_sub, map_pow, h1, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hr P

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.PicDiv

theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A).2.1 P₀ hP).2
  set α : k := φ (algebraMap k[X] A X) with hα
  have hC : algebraMap k[X] A (C α) = algebraMap k A α := by
    rw [IsScalarTower.algebraMap_apply k k[X] A]; rfl
  have hlin : algebraMap k[X] A (X - C α) ∈ P₀ := by
    rw [hφ, map_sub, map_sub, hC, φ.commutes, ← hα]
    simp
  have hne : algebraMap k[X] A (X - C α) ≠ 0 := by
    intro h0
    have h1 : (X - C α) • (1 : A) = 0 := by rw [Algebra.smul_def, h0, zero_mul]
    have h3 : b.repr (1 : A) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp h3
    have h4 := congrArg (fun a => b.repr a i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact mul_ne_zero (X_sub_C_ne_zero α) hi h4
  have hbot : P₀ ≠ ⊥ := fun h => hne (by rw [h] at hlin; simpa using hlin)
  have hlt := Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  set q : k[X] := (X - C α) ^ 2 with hq
  have hmon : q.Monic := (monic_X_sub_C α).pow 2
  have hqdeg : q.degree = (2 : ℕ) := by
    rw [hq, degree_pow, degree_X_sub_C]; rfl
  have hqmem : algebraMap k[X] A q ∈ P₀ ^ 2 := by
    rw [hq, map_pow]; exact Ideal.pow_mem_pow hlin 2
  let c : Fin n → k[X] := fun i => b.repr (π - w) i
  let p : Fin n → k[X] := fun i => c i %ₘ q
  let d : Fin n → k[X] := fun i => c i /ₘ q
  have hs : ∑ i, c i • b i = π - w := b.sum_repr (π - w)
  have h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_smul, ← add_smul]
    exact congrArg (· • b i) (modByMonic_add_div (c i) q).symm
  have key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i := by
    linear_combination hs - h2
  have hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2 := Ideal.mul_mem_right _ _ hqmem
  refine ⟨p, fun i => ?_, ?_, ?_⟩
  · rw [← hqdeg]; exact degree_modByMonic_lt _ hmon
  · rw [key]; exact P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)
  · intro h
    apply hπ2
    have : π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i := by
      rw [key]; ring
    rw [this]; exact (P₀ ^ 2).add_mem h hM

end GlobalTheory.PicDiv
end

section

open Polynomial

namespace GlobalTheory.PicDiv

theorem degree_count_generates : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  intro k A _ _ _ _ _ _ N I _ D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hQ'P hDQ' hDP hf₀ hf hspan hfD hfP hfQ' hdeg
  obtain ⟨_hfin, hmax, hmul, hle⟩ := GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A
  have hPne : P ≠ ⊥ := by
    intro h; apply hf; rw [h] at hfP; simpa using hfP
  have hmaxne : ∀ M : Ideal A, M.IsMaximal → M ≠ ⊥ := by
    intro M hM h
    subst h
    exact hPne (hM.eq_of_le hP.ne_top bot_le).symm
  have hDne : D ≠ ⊥ := by
    intro h; exact hDP (h ▸ bot_le)
  have hprodne : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → (∏ i ∈ s, g i) ≠ ⊥ := by
    intro s g hg
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro i _; rw [Ideal.zero_eq_bot]; exact hg i
  have hpowne : ∀ (M : Ideal A) (n : ℕ), M ≠ ⊥ → M ^ n ≠ ⊥ := by
    intro M n hM
    rw [← Ideal.zero_eq_bot] at hM ⊢
    exact pow_ne_zero n hM
  have hmulne : ∀ (M M' : Ideal A), M ≠ ⊥ → M' ≠ ⊥ → M * M' ≠ ⊥ := by
    intro M M' hM hM'
    rw [← Ideal.zero_eq_bot] at hM hM' ⊢
    exact mul_ne_zero hM hM'
  have htop : Module.finrank k (A ⧸ (⊤ : Ideal A)) = 0 := by
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hpow : ∀ (M : Ideal A) (n : ℕ), M.IsMaximal → Module.finrank k (A ⧸ M ^ n) = n := by
    intro M n hM
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, htop]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (hpowne M n (hmaxne M hM)) (hmaxne M hM), ih, (hmax M hM).1]
  have hprod : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) →
      Module.finrank k (A ⧸ ∏ i ∈ s, g i) = ∑ i ∈ s, Module.finrank k (A ⧸ g i) := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, htop]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hg a) (hprodne s g hg), ih]
  have hPowProd : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) →
      Module.finrank k (A ⧸ ∏ i, R i ^ N) = N * Fintype.card I := by
    intro R hR
    rw [hprod _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))]
    simp only [hpow _ _ (hR _), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hPowNe : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → (∏ i, R i ^ N) ≠ ⊥ :=
    fun R hR => hprodne _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))
  have h0 : Module.finrank k (A ⧸ Ideal.span {f₀}) =
      1 + Module.finrank k (A ⧸ D) + N * Fintype.card I := by
    rw [hspan, hmul _ _ (hmulne _ _ (hmaxne _ hP₀) hDne) (hPowNe Q hQ),
      hmul _ _ (hmaxne _ hP₀) hDne, (hmax _ hP₀).1, hPowProd Q hQ]
  have hcop_max : ∀ M M' : Ideal A, M.IsMaximal → M'.IsMaximal → M ≠ M' → IsCoprime M M' := by
    intro M M' hM hM' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 := hM.eq_of_le h le_sup_left
    have h2 := hM'.eq_of_le h le_sup_right
    exact hne (h1.trans h2.symm)
  have hcopD : ∀ M : Ideal A, M.IsMaximal → ¬ D ≤ M → IsCoprime M D := by
    intro M hM hDM
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hDM (le_sup_right.trans (hM.eq_of_le h le_sup_left).ge)
  have hdvd : ∀ M : Ideal A, f ∈ M → M ∣ Ideal.span {f} := fun M hM =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hM)
  have hX : (∏ i, Q' i ^ N) ∣ Ideal.span {f} := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (hcop_max _ _ (hQ' i) (hQ' j) (hinj.ne hij)).pow
    · intro i _; exact hdvd _ (hfQ' i)
  have hPD : P * D ∣ Ideal.span {f} := (hcopD P hP hDP).mul_dvd (hdvd _ hfP) (hdvd _ hfD)
  have hPDX : IsCoprime (P * D) (∏ i, Q' i ^ N) :=
    IsCoprime.mul_left
      (IsCoprime.prod_right fun i _ => (hcop_max P (Q' i) hP (hQ' i) (hQ'P i).symm).pow_right)
      (IsCoprime.prod_right fun i _ => (hcopD (Q' i) (hQ' i) (hDQ' i)).symm.pow_right)
  have hJ : P * D * ∏ i, Q' i ^ N ∣ Ideal.span {f} := hPDX.mul_dvd hPD hX
  apply hle _ _ _ (Ideal.le_of_dvd hJ)
  · rw [hmul _ _ (hmulne _ _ hPne hDne) (hPowNe Q' hQ'), hmul _ _ hPne hDne, (hmax _ hP).1,
      hPowProd Q' hQ']
    rw [h0] at hdeg; exact hdeg
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hf

end GlobalTheory.PicDiv
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → Nonempty (B →ₐ[k] SeparableClosure k) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.exists_finite_separable_point_of_separableClosure_point | exact GlobalTheory.exists_finite_separable_point_of_separableClosure_point | (intros; apply GlobalTheory.exists_finite_separable_point_of_separableClosure_point <;> assumption)
end

section


theorem _root_.GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (exact GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (intros; apply GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType <;> assumption)
end

section

open Polynomial IsLocalRing

theorem _root_.GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction : ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) (q : Polynomial V), q.Monic → (q.map (IsLocalRing.residue V)).Separable → ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.monic_splits_of_separable_residue | exact GlobalTheory.monic_splits_of_separable_residue | (intros; apply GlobalTheory.monic_splits_of_separable_residue <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ → ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 → ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω, ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))), ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  first | exact @GlobalTheory.extend_alg_hom_adjoin_integral_root | exact GlobalTheory.extend_alg_hom_adjoin_integral_root | (intros; apply GlobalTheory.extend_alg_hom_adjoin_integral_root <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.frobeniusSubalgebra_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  first | exact @GlobalTheory.frobSubalgebra_counit | exact GlobalTheory.frobSubalgebra_counit | (intros; apply GlobalTheory.frobSubalgebra_counit <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_flat_lift_mod_p_sq_perfect_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectField k], ∃ (Λ : Type) (_ : CommRing Λ) (π : Λ →+* k), Function.Surjective π ∧ RingHom.ker π = Ideal.span {(p : Λ)} ∧ (p : Λ) ^ 2 = 0 ∧ ∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)} := by
  first | exact @GlobalTheory.exists_flat_lift_mod_p_sq | exact GlobalTheory.exists_flat_lift_mod_p_sq | (intros; apply GlobalTheory.exists_flat_lift_mod_p_sq <;> assumption)
end
