module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTrace
public import Mathlib.GroupTheory.Perm.Cycle.Type
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.FieldTheory.Galois.GaloisClosure

@[expose] public section

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem sum_le_prod_of_two_le_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, 2 ≤ f i) : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have key : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i ∧ 2 ≤ ∏ i ∈ s, f i := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using h a (by simp)
    | cons a s ha hs ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_cons_of_mem hi))
      have h3 := h a (Finset.mem_cons_self _ _)
      constructor
      · have := Nat.add_le_mul h3 h2
        omega
      · nlinarith
  exact key.1

private theorem arith_four (a b c R m : ℕ) (ha : 16 ≤ a) (hb : m ≤ b) (hc : m ≤ c)
    (hbc : 16 * m ≤ b * c) (hR : 1 ≤ R) : 4 * m * (a + b + c + R) ≤ a * b * c * R := by
  have h1 : 16 * m * a ≤ b * c * a := Nat.mul_le_mul_right _ hbc
  have h2 : 16 * m * b ≤ a * c * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hc)
  have h3 : 16 * m * c ≤ a * b * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hb)
  have h4 : 16 * m * R ≤ a * b * c * R := by
    apply Nat.mul_le_mul_right
    calc 16 * m ≤ b * c := hbc
      _ ≤ a * (b * c) := Nat.le_mul_of_pos_left _ (by omega)
      _ = a * b * c := by ring
  have h5 : a * b * c ≤ a * b * c * R := Nat.le_mul_of_pos_right _ hR
  nlinarith

theorem sum_primePowerParts_le :
    ∀ n q d : ℕ, 0 < n → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → 16 ≤ max q d →
      16 * q * d ∣ n → (∑ l ∈ n.primeFactors, ((l ^ padicValNat l n : ℕ) : ℝ)) ≤
        (n : ℝ) / (4 * ((min q d : ℕ) : ℝ)) := by
  intro n q d hn hq hd hq2 hd2 hqd hmax hdvd
  set f : ℕ → ℕ := fun l => l ^ padicValNat l n with hf
  have hpow : ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ f p := by
    intro p k hp hk
    haveI := Fact.mk hp
    exact Nat.pow_le_pow_right hp.pos (((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn.ne').1 hk)
  have hge : ∀ p ∈ n.primeFactors, p ≤ f p := by
    intro p hp
    have := hpow p 1 (Nat.prime_of_mem_primeFactors hp)
      (by simpa using Nat.dvd_of_mem_primeFactors hp)
    simpa using this
  have h16 : 2 ^ 4 ∣ n := Dvd.dvd.trans ⟨q * d, by ring⟩ hdvd
  have hqn : q ∣ n := Dvd.dvd.trans ⟨16 * d, by ring⟩ hdvd
  have hdn : d ∣ n := Dvd.dvd.trans ⟨16 * q, by ring⟩ hdvd
  have m2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, Dvd.dvd.trans ⟨8, by norm_num⟩ h16, hn.ne'⟩
  have mq : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn.ne'⟩
  have md : d ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdn, hn.ne'⟩
  have ha : 16 ≤ f 2 := by simpa using hpow 2 4 Nat.prime_two h16
  have hb := hge q mq
  have hc := hge d md
  have hsub : ({2, q, d} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hn2 : (2 : ℕ) ∉ ({q, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hprod : ∏ l ∈ n.primeFactors, f l = n := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
    simp [f, Nat.padicValNat_def]
  set s := n.primeFactors \ {2, q, d} with hs
  have hs2 : ∀ i ∈ s, 2 ≤ f i := fun i hi =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hi).1).two_le.trans
      (hge i (Finset.mem_sdiff.1 hi).1)
  have hSP := sum_le_prod_of_two_le_nat s f hs2
  have hR : 1 ≤ ∏ i ∈ s, f i :=
    Finset.prod_pos (f := f) fun i hi => lt_of_lt_of_le (by norm_num) (hs2 i hi)
  have e1 : n = f 2 * f q * f d * ∏ i ∈ s, f i := by
    rw [← hprod, ← Finset.prod_sdiff hsub, Finset.prod_insert hn2, Finset.prod_pair hqd]
    ring
  have e2 : ∑ l ∈ n.primeFactors, f l = f 2 + f q + f d + ∑ i ∈ s, f i := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_insert hn2, Finset.sum_pair hqd]
    ring
  have hbc : 16 * min q d ≤ f q * f d := by
    calc 16 * min q d ≤ max q d * min q d := Nat.mul_le_mul_right _ hmax
      _ = q * d := max_mul_min q d
      _ ≤ f q * f d := Nat.mul_le_mul hb hc
  have key := arith_four (f 2) (f q) (f d) (∏ i ∈ s, f i) (min q d) ha
    ((min_le_left _ _).trans hb) ((min_le_right _ _).trans hc) hbc hR
  rw [← e1] at key
  have key2 : (∑ l ∈ n.primeFactors, f l) * (4 * min q d) ≤ n := by
    rw [e2, mul_comm]
    exact (Nat.mul_le_mul_left _ (by omega)).trans key
  have hm : 0 < min q d := lt_min hq.pos hd.pos
  rw [le_div_iff₀ (by positivity), ← Nat.cast_sum]
  exact_mod_cast key2

end GlobalTheory.BadShare
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_ne_zero_point_extends_to_subalgebra : ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R), Function.Injective ξ → ∀ T : Finset R,
 ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧ ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  first | exact @GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra | exact GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra | (intros; apply GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.classGroup_nthPower_of_congruent_points_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  first | exact @GlobalTheory.classGroup_nthPower_of_codim_one_mod | exact GlobalTheory.classGroup_nthPower_of_codim_one_mod | (intros; apply GlobalTheory.classGroup_nthPower_of_codim_one_mod <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.degree_count_maximalIdeal_generates_product : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  first | exact @GlobalTheory.degree_count_generates | exact GlobalTheory.degree_count_generates | (intros; apply GlobalTheory.degree_count_generates <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_degree_lt_two_correction_simple_zero : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A), P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧ w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  first | exact @GlobalTheory.exists_deg_lt_two_correction_simple | exact GlobalTheory.exists_deg_lt_two_correction_simple | (intros; apply GlobalTheory.exists_deg_lt_two_correction_simple <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_squarefree_poly_distinct_zeros_on_curve : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  first | exact @GlobalTheory.SquarefreeFibre.main | exact GlobalTheory.SquarefreeFibre.main | (intros; apply GlobalTheory.SquarefreeFibre.main <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.BertiniNoether

theorem gauss_extension_unique : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.T.exists_monic_irreducible_integral_primitive_element t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation Φ hmon hirr
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_primes_mem_valuationSubring_over s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have conv : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) :=
    fun W h => ⟨h.1, fun P hP ⟨i, h0, hv, hinv⟩ => h.2 P hP ⟨i, hv, h0, hinv⟩⟩
  have key : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.T.gaussExtension_coeff_mem_nonunits_alt t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (GlobalTheory.T.valuationSubring_le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ (conv W₁ h₁) (conv W₂ h₂) (key W₁ (conv W₁ h₁)))
    (GlobalTheory.T.valuationSubring_le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ (conv W₂ h₂) (conv W₁ h₁) (key W₂ (conv W₂ h₂)))

end GlobalTheory.BertiniNoether
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.ValConjClosure

theorem valuation_intCast_eq_one {Ω : Type} [Field Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : A.valuation (n : Ω) = 1 := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  refine le_antisymm (hle n) (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hn
  have hab' : (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have h1 : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : Ω) * A.valuation (p : Ω) ≤ 1 * A.valuation (p : Ω) :=
          mul_le_mul' (hle a) le_rfl
      _ < 1 := by rwa [one_mul]
  have h2 : A.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) :=
          mul_le_mul' (hle b) le_rfl
      _ < 1 := by rwa [one_mul]
  have hadd := A.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
  rw [hab', map_one] at hadd
  exact absurd hadd (not_le.mpr (max_lt h1 h2))

theorem ratCast_mem_iff {Ω : Type} [Field Ω] [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (a : ℚ) : (a : Ω) ∈ A ↔ ¬ p ∣ a.den := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hden0 : (a.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  rw [Rat.cast_def, ← A.valuation_le_one_iff]
  constructor
  · intro ha hd
    have hnum : ¬ (p : ℤ) ∣ a.num := by
      intro h
      have h1 : p ∣ a.num.natAbs := Int.natCast_dvd.mp h
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 a.reduced) hd)
    have hv1 := valuation_intCast_eq_one hp A hA a.num hnum
    obtain ⟨k, hk⟩ := hd
    have hdlt : A.valuation (a.den : Ω) < 1 := by
      rw [hk, Nat.cast_mul, map_mul]
      calc A.valuation (p : Ω) * A.valuation (k : Ω) ≤ A.valuation (p : Ω) * 1 :=
            mul_le_mul' le_rfl (by exact_mod_cast hle k)
        _ < 1 := by rwa [mul_one]
    have hnd : A.valuation (a.num : Ω) ≤ A.valuation (a.den : Ω) := by
      rw [← div_mul_cancel₀ (a.num : Ω) hden0, map_mul]
      calc A.valuation ((a.num : Ω) / (a.den : Ω)) * A.valuation (a.den : Ω) ≤
            1 * A.valuation (a.den : Ω) := mul_le_mul' ha le_rfl
        _ = A.valuation (a.den : Ω) := one_mul _
    rw [hv1] at hnd
    exact absurd (lt_of_le_of_lt hnd hdlt) (lt_irrefl 1)
  · intro hd
    have hv1 : A.valuation (a.den : Ω) = 1 := by
      have h := valuation_intCast_eq_one hp A hA (a.den : ℤ) (by exact_mod_cast hd)
      exact_mod_cast h
    rw [map_div₀, hv1, div_one]
    exact hle a.num

theorem isClosed_apply_mem {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
    (x : Ω) (T : Set Ω) : IsClosed {σ : Ω ≃ₐ[F] Ω | σ x ∈ T} := by
  let E := IntermediateField.adjoin F ({x} : Set Ω)
  haveI : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (E.fixingSubgroup : Set (Ω ≃ₐ[F] Ω)), ?_,
    E.fixingSubgroup_isOpen.preimage (continuous_const_mul σ⁻¹), ?_⟩
  · intro τ hτ hT
    apply hσ
    have hfix : (σ⁻¹ * τ) x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x
      (IntermediateField.mem_adjoin_simple_self F x)
    have hinv : ∀ y, σ (σ⁻¹ y) = y := fun y => by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [AlgEquiv.mul_apply] at hfix
    have he : τ x = σ x :=
      calc τ x = σ (σ⁻¹ (τ x)) := (hinv _).symm
        _ = σ x := by rw [hfix]
    change σ x ∈ T
    rw [← he]
    exact hT
  · show σ⁻¹ * σ ∈ E.fixingSubgroup
    rw [inv_mul_cancel]
    exact E.fixingSubgroup.one_mem

theorem exists_conj_of_isGalois {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (A B : ValuationSubring Ω) (h : ∀ a : F, algebraMap F Ω a ∈ A ↔ algebraMap F Ω a ∈ B) :
    ∃ σ : Ω ≃ₐ[F] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  let C : Finset Ω → Set (Ω ≃ₐ[F] Ω) := fun s => {σ | ∀ x ∈ s, σ x ∈ B ↔ x ∈ A}
  have hclosed : ∀ s, IsClosed (C s) := by
    intro s
    have hC : C s = ⋂ x ∈ s, {σ : Ω ≃ₐ[F] Ω | σ x ∈ {y : Ω | y ∈ B ↔ x ∈ A}} := by
      ext σ
      simp [C]
    rw [hC]
    exact isClosed_biInter fun x _ => isClosed_apply_mem x _
  have hne : ∀ s, (C s).Nonempty := by
    intro s
    let L := (FiniteGaloisIntermediateField.adjoin F (s : Set Ω)).toIntermediateField
    have hsL : (s : Set Ω) ⊆ L := FiniteGaloisIntermediateField.subset_adjoin F (s : Set Ω)
    obtain ⟨τ, hτ⟩ := GlobalTheory.KZ.ES.exists_conj_of_same_trace F L (A.comap (algebraMap L Ω))
      (B.comap (algebraMap L Ω)) (by
        intro a
        rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
          ← IsScalarTower.algebraMap_apply]
        exact h a)
    refine ⟨τ.liftNormal Ω, fun x hx => ?_⟩
    have hxL : x ∈ L := hsL hx
    have key := hτ ⟨x, hxL⟩
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at key
    have he : (τ.liftNormal Ω) x = algebraMap L Ω (τ ⟨x, hxL⟩) :=
      AlgEquiv.liftNormal_commutes τ Ω ⟨x, hxL⟩
    rw [he]
    exact key
  have hdir : Directed (fun s t => s ⊇ t) C := by
    intro s t
    exact ⟨s ∪ t, fun σ hσ x hx => hσ x (Finset.mem_union_left _ hx),
      fun σ hσ x hx => hσ x (Finset.mem_union_right _ hx)⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun s => (hclosed s).isCompact) hclosed
  refine ⟨σ, fun x => ?_⟩
  exact Set.mem_iInter.mp hσ {x} x (Finset.mem_singleton_self x)

theorem exists_conj_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  intro Ω _ _ _ p _ A B hA hB
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : p.Prime := Fact.out
  have hA' := (A.mem_nonunits_iff).mp hA
  have hB' := (B.mem_nonunits_iff).mp hB
  apply exists_conj_of_isGalois A B
  intro a
  rw [eq_ratCast, ratCast_mem_iff hp A hA', ratCast_mem_iff hp B hB']

end GlobalTheory.ValConjClosure
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

private lemma eq_filter_add_replicate (μ : Multiset ℕ) (h : ∀ d ∈ μ, 0 < d) :
    μ = μ.filter (fun n => 2 ≤ n) + Multiset.replicate (μ.count 1) 1 := by
  ext d
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases h2 : 2 ≤ d
  · rw [if_pos h2, if_neg (by omega)]; rfl
  · rw [if_neg h2]
    by_cases h1 : 1 = d
    · subst h1; simp
    · rw [if_neg h1]
      have : d ∉ μ := fun hd => by have := h d hd; omega
      simpa using this

theorem card_perm_partition_parts_mul :
    ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N →
      (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card *
        ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by
  intro N μ hpos hsum
  set m := μ.filter (fun n => 2 ≤ n) with hm
  have hμ : μ = m + Multiset.replicate (μ.count 1) 1 := eq_filter_add_replicate μ hpos
  have hs : m.sum + μ.count 1 = N := by
    rw [← hsum]
    conv_rhs => rw [hμ]
    simp
  have key := Equiv.Perm.card_of_cycleType_mul_eq (Fin N) m
  rw [if_pos ⟨by rw [Fintype.card_fin]; omega, fun a ha => (Multiset.mem_filter.1 ha).2⟩,
    Fintype.card_fin] at key
  have hN : N - m.sum = μ.count 1 := by omega
  rw [hN] at key
  have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ) =
      Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.cycleType = m := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← Equiv.Perm.filter_parts_partition_eq_cycleType, h]
    · intro h
      rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, h, Fintype.card_fin, hN]
      exact hμ.symm
  have hprod : ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) =
      (μ.count 1).factorial * m.prod * ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [← Finset.prod_filter_mul_prod_filter_not μ.toFinset (fun n => 2 ≤ n)]
    have h1 : μ.toFinset.filter (fun n => 2 ≤ n) = m.toFinset := by
      ext n; simp [hm]
    have h2 : ∏ d ∈ μ.toFinset.filter (fun n => ¬ 2 ≤ n),
        (d ^ μ.count d * (μ.count d).factorial) = (μ.count 1).factorial := by
      rw [Finset.prod_eq_single 1]
      · simp
      · intro b hb hb1
        simp only [Finset.mem_filter, Multiset.mem_toFinset] at hb
        have := hpos b hb.1
        omega
      · intro h
        have : (1 : ℕ) ∉ μ := fun h1 => h (by simpa using h1)
        simp [Multiset.count_eq_zero_of_notMem this]
    rw [h1, h2, Finset.prod_multiset_count m, mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hn)).2
    have : m.count n = μ.count n := by rw [hm, Multiset.count_filter, if_pos hn2]
    rw [this]
  rw [hset, hprod]
  convert key

end GlobalTheory.BadShare
end
