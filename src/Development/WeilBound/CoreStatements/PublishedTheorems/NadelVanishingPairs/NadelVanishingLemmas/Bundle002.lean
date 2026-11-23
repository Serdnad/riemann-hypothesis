module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle254
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AlternatingProductCocycle
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle320
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
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
public import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem Dtot_cup : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 →
    (∀ s, Dtot d (Φ (c s)) = 0) → Dtot d (cup Φ c) = cup Φ (delta c) := by
  intro ι _ E _ d Φ c hΦ hc hD
  funext u
  have key := delta_cup_eq Φ c hΦ hc u
  suffices hS : (∑ j ∈ u, ((-1 : ℤ) ^ ({x ∈ u | x < j}).card) • delta (Φ (c ({x ∈ u | x ≤ j}))) ({x ∈ u | j ≤ x}))
      + ((-1 : ℤ) ^ u.card) • d (cup Φ c u) = 0 by
    simp only [Dtot]
    rw [key, add_assoc, hS, add_zero]

  simp only [cup, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have h := congrFun (hD ({x ∈ u | x ≤ j})) ({x ∈ u | j ≤ x})
  simp only [Dtot, Pi.zero_apply] at h
  rw [eq_neg_of_add_eq_zero_left h]
  have hcard : ({x ∈ u | x < j}).card + ({x ∈ u | j ≤ x}).card = u.card := by
    have := Finset.card_filter_add_card_filter_not (s := u) (fun x => x < j)
    simpa only [not_lt] using this
  rw [smul_neg, smul_smul, ← pow_add, hcard, neg_add_cancel]

end GlobalTheory.DI
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.PhiClosed

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem d_alg_pow (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) (c : K) (n : ℕ) :
    d (algebraMap K (ExteriorAlgebra K V) c ^ (n + 1)) =
      (n + 1) • (algebraMap K (ExteriorAlgebra K V) c ^ n * d (algebraMap K (ExteriorAlgebra K V) c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' _ (n + 1), hd.mul, ih, AlgHom.commutes]
    have hc : d (algebraMap K (ExteriorAlgebra K V) c) * algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) =
        algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) * d (algebraMap K (ExteriorAlgebra K V) c) := by
      rw [← map_pow]
      exact (Algebra.commutes _ _).symm
    rw [hc, mul_smul_comm, ← mul_assoc, ← pow_succ', succ_nsmul' _ (n + 1)]

theorem d_alg_pow_char (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) : d (algebraMap K (ExteriorAlgebra K V) (c ^ p)) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  rw [map_pow, hk, d_alg_pow d hd c k, ← hk, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem d_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (y : ExteriorAlgebra K V) : d (c ^ p • y) = c ^ p • d y := by
  rw [Algebra.smul_def, hd.mul, AlgHom.commutes, d_alg_pow_char p d hd c, zero_mul, zero_add,
    ← Algebra.smul_def]

theorem Dtot_add (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (a b : Finset ι → ExteriorAlgebra K V) :
    Dtot d (a + b) = Dtot d a + Dtot d b := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add (f := _)]
  abel

theorem Dtot_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (a : Finset ι → ExteriorAlgebra K V) :
    Dtot d (c ^ p • a) = c ^ p • Dtot d a := by
  funext t
  simp only [Dtot, delta, Pi.smul_apply, d_smul_pow p d hd, Finset.smul_sum, smul_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact smul_comm _ _ _

end GlobalTheory.DI.PhiClosed

open GlobalTheory.DI.PhiClosed in
theorem GlobalTheory.DI.phi_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  intro K _ V _ _ ι _ p _ _ d f h Φ hd hD hΦ
  have hA := (prodL_alt_closed p d f h hd hD).2
  have hz0 : Dtot d (0 : Finset ι → ExteriorAlgebra K V) = 0 := by
    funext t
    simp [Dtot, delta]
  have key : ∀ x : ExteriorAlgebra K V, ∀ c : K, Φ (c • x) ∅ = 0 ∧ Dtot d (Φ (c • x)) = 0 := by
    intro x
    have hx : x ∈ Submodule.span K
        (Set.range fun x : (n : ℕ) × (Fin n → V) => ExteriorAlgebra.ιMulti K x.1 x.2) := by
      rw [ExteriorAlgebra.ιMulti_span]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, v⟩, rfl⟩ := hy
      intro c
      rw [hΦ c a v]
      exact ⟨by rw [Pi.smul_apply, (hA a v).2, smul_zero],
        by rw [PhiClosed.Dtot_smul_pow p d hd, (hA a v).1, smul_zero]⟩
    | zero =>
      intro c
      simp [hz0]
    | add y z _ _ hy hz =>
      intro c
      rw [smul_add, map_add (f := _)]
      exact ⟨by rw [Pi.add_apply, (hy c).1, (hz c).1, add_zero],
        by rw [PhiClosed.Dtot_add, (hy c).2, (hz c).2, add_zero]⟩
    | smul a y _ hy =>
      intro c
      rw [smul_smul]
      exact hy (c * a)
  exact ⟨fun x => by simpa using (key x 1).1, fun x => by simpa using (key x 1).2⟩
end

section

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.exists_frobenius_splitting_datum : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  first | exact @_root_.GlobalTheory.DI.exists_isPhi | exact _root_.GlobalTheory.DI.exists_isPhi | (intros; apply _root_.GlobalTheory.DI.exists_isPhi <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.residue_field_formally_smooth :
    ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k)
      [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U),
      IsClosed ({x} : Set X) →
        (letI : Algebra k (X.presheaf.stalk x) :=
          ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
         Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  intro k _ _ X f _ U x hxU _
  let : Algebra k (X.presheaf.stalk x) :=
    ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have hgerm : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hstalk : algebraMap k (X.presheaf.stalk x) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk k (f x)).hom := by
    change (X.presheaf.germ U x hxU).hom.comp (cstOn f U) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, hgerm, ← Category.assoc,
      Scheme.ΓSpecIso_inv]
    rfl
  have hbase (p : PrimeSpectrum k) : (StructureSheaf.toStalk k p).hom.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  have hresidue : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
    apply RingHom.essFiniteType_algebraMap.mp
    change ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      (algebraMap k (X.presheaf.stalk x))).EssFiniteType
    rw [hstalk]
    exact ((hbase (f x)).comp (LocallyOfFiniteType.stalkMap f x)).comp hresidue.essFiniteType
  exact Algebra.FormallySmooth.of_perfectField
end

section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.regular_local_differentials_linearIndependent : ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by
  first | exact @_root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system | exact _root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system | (intros; apply _root_.GlobalTheory.linearIndependent_tmul_D_of_regular_system <;> assumption)
end

section

theorem _root_.GlobalTheory.T.regular_quotient_prime_element : ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P → IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  first | exact @_root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | exact _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | (intros; apply _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient <;> assumption)
end
