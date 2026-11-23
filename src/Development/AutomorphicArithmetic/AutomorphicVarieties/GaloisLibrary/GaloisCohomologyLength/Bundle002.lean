module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement
public import Mathlib.Algebra.Algebra.Hom.Rat
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.classFix :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K) (g : Ω ≃+* Ω) (h : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) → ((∀ x : F, g (algebraMap F Ω x) = algebraMap F Ω x) ↔ h ∈ KStar.TotallyRealRoots.fieldSubgroup N K φ.fieldRange) := by
  intro F Ω _ _ _ _ _ N _ K _ _ _ φ g h hg
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap F Ω).injective).mp inferInstance
  letI : Algebra F K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F K := inferInstance
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  let ι : K →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hι : ∀ x : F, ι (φ x) = algebraMap F Ω x := fun x => ι.commutes x
  set σ : Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm h with hσ
  have hσζ : ∀ y : K, y ^ N = 1 → σ y = y ^ (h : ZMod N).val := by
    intro y hy
    have := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ hy
    rw [this, hσ, MulEquiv.apply_symm_apply]
  have hcomm : ∀ y : K, g (ι y) = ι (σ y) := by
    have key : (g.toRingHom.toRatAlgHom).comp (ι.toRingHom.toRatAlgHom) =
        (ι.toRingHom.toRatAlgHom).comp σ.toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top (s := {b : K | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ b ^ n = 1})
        (Algebra.eq_top_iff.mpr IsCyclotomicExtension.adjoin_roots) ?_
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      subst hn
      simp only [AlgHom.coe_comp, Function.comp_apply, RingHom.toRatAlgHom_apply,
        AlgEquiv.coe_algHom]
      rw [hσζ b hb, map_pow]
      apply hg
      rw [← map_pow, hb, map_one]
    intro y
    exact congrArg (fun f => f y) key
  unfold KStar.TotallyRealRoots.fieldSubgroup
  rw [Subgroup.mem_map_equiv, ← hσ, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro H y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    apply ι.toRingHom.injective
    change ι (σ (φ x)) = ι (φ x)
    rw [← hcomm, hι, H]
  · intro H x
    rw [← hι, hcomm, H _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)]
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem ci_pow {Ω : Type*} [Monoid Ω] {m M : ℕ} [NeZero m] [NeZero M] (hm : m ∣ M)
    (a : (ZMod M)ˣ) (ζ : Ω) (hζ : ζ ^ m = 1) :
    ζ ^ (a : ZMod M).val = ζ ^ ((ZMod.unitsMap hm a : (ZMod m)ˣ) : ZMod m).val := by
  rw [ZMod.unitsMap_val, ← ZMod.natCast_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]

private theorem ci_hen (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (i : ℕ) :
    HasEnoughRootsOfUnity Ω (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  infer_instance

private theorem ci_spec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : Ω ≃+* Ω) (ζ : Ω) (hζ : ζ ^ l ^ n = 1) :
    g ζ = ζ ^ ((KStar.TotallyRealRoots.redPow l n (cyclotomicCharacter Ω l g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  have hen := ci_hen Ω l
  exact cyclotomicCharacter.spec l g ζ hζ

private theorem ci_red {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : Ω ≃+* Ω) (w : (ZMod (l ^ n))ˣ)
    (h : ∀ ζ : Ω, ζ ^ l ^ n = 1 → g ζ = ζ ^ (w : ZMod (l ^ n)).val) :
    w = KStar.TotallyRealRoots.redPow l n (cyclotomicCharacter Ω l g) := by
  have hen := ci_hen Ω l n
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := ci_spec l n g ζ hζ.pow_eq_one
  rw [h ζ hζ.pow_eq_one] at h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ n, Nat.pos_of_neZero _, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
  exact Units.ext h1

private theorem ci_eq {Ω : Type} [Field Ω] {x y : Ω} (hy : y ≠ 0) {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a = y ^ a) (hb : x ^ b = y ^ b) : x = y := by
  have h1 : (x / y) ^ a = 1 := by rw [div_pow, ha, div_self (pow_ne_zero _ hy)]
  have h2 : (x / y) ^ b = 1 := by rw [div_pow, hb, div_self (pow_ne_zero _ hy)]
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hab.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact (div_eq_one_iff_eq hy).1 h3

theorem UpperTheory.V.LDataCardLeFinrank.classIff :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (g : Ω ≃+* Ω) (h : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) ↔
      ((∀ ζ : Ω, ζ ^ ordCompl[l] N = 1 → g ζ = ζ ^ ((ZMod.unitsMap (Nat.ordCompl_dvd N l) h : (ZMod (ordCompl[l] N))ˣ) : ZMod (ordCompl[l] N)).val) ∧
        ZMod.unitsMap (Nat.ordProj_dvd N l) h = KStar.TotallyRealRoots.redPow l (N.factorization l) (cyclotomicCharacter Ω l g)) := by
  intro Ω _ _ _ l _ N _ g h
  have hl : l.Prime := Fact.out
  have hN : N ≠ 0 := NeZero.ne N
  have : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l hN).ne'⟩
  have hmul : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  constructor
  · intro H
    refine ⟨fun ζ hζ => ?_, ci_red l _ g _ fun ζ hζ => ?_⟩
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, mul_comm, pow_mul, hζ, one_pow])
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, pow_mul, hζ, one_pow])
  · rintro ⟨H1, H2⟩ ζ hζ
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN] at hζ
      exact zero_ne_one hζ
    have hcop : (ordProj[l] N).Coprime (ordCompl[l] N) :=
      (Nat.coprime_ordCompl hl hN).pow_left _
    have e1 : (ζ ^ ordProj[l] N) ^ ordCompl[l] N = 1 := by rw [← pow_mul, hmul, hζ]
    have e2 : (ζ ^ ordCompl[l] N) ^ ordProj[l] N = 1 := by rw [← pow_mul, mul_comm, hmul, hζ]
    refine ci_eq (pow_ne_zero _ hζ0) hcop ?_ ?_
    · rw [← map_pow, H1 _ e1, ← ci_pow _ h _ e1, ← pow_mul, ← pow_mul, mul_comm]
    · rw [← map_pow, ci_spec l _ g _ e2, ← H2, ← ci_pow _ h _ e2, ← pow_mul, ← pow_mul, mul_comm]
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.ineFixRoots :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (m : ℕ), m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 →
      (∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ) ∧ ∀ g ∈ Ine (F := F) A, g ζ = ζ := by
  intro F Ω _ _ _ _ _ l _ A hl m hm ζ hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hm)
  have hv1 : ∀ x : Ω, x ^ m = 1 → A.valuation x = 1 := by
    intro x hx
    have h := congrArg A.valuation hx
    rw [map_pow, map_one] at h
    rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
    · exact absurd h (pow_lt_one₀ zero_le' h1 hm0).ne
    · exact h1
    · exact absurd h (one_lt_pow₀ h1 hm0).ne'
  have hint : ∀ a : ℤ, A.valuation (a : Ω) ≤ 1 := fun a => by
    simpa using A.valuation_le_one (a : A)
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hg : ((Nat.gcd m l : ℕ) : ℤ) = m * Nat.gcdA m l + l * Nat.gcdB m l := Nat.gcd_eq_gcd_ab m l
    rw [Nat.Coprime.gcd_eq_one hm] at hg
    have hΩ := congrArg (Int.cast : ℤ → Ω) hg
    push_cast at hΩ
    have h1 : A.valuation (1 : Ω) < 1 := by
      rw [hΩ]
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl
    simp at h1
  have part1 : ∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ := by
    intro ξ hξ hlt
    by_contra hne
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      simp [zero_pow hm0] at hζ
    set η := ξ / ζ with hηdef
    have hη : η ^ m = 1 := by rw [hηdef, div_pow, hξ, hζ, div_one]
    have hη1 : η ≠ 1 := fun h => hne ((div_eq_one_iff_eq hζ0).mp h)
    have hvη : A.valuation (η - 1) < 1 := by
      have e : η - 1 = (ξ - ζ) / ζ := by rw [hηdef, sub_div, div_self hζ0]
      rw [e, map_div₀, hv1 ζ hζ, div_one]
      exact hlt
    have hpow1 : ∀ j, A.valuation (η ^ j) = 1 := fun j => by rw [map_pow, hv1 η hη, one_pow]
    have hterm : ∀ i, A.valuation (1 - η ^ i) < 1 := by
      intro i
      have e : 1 - η ^ i = -((∑ j ∈ Finset.range i, η ^ j) * (η - 1)) := by
        rw [geom_sum_mul]
        ring
      rw [e, Valuation.map_neg, map_mul]
      have hs : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 :=
        A.valuation.map_sum_le (fun j _ => (hpow1 j).le)
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hvη
    have hsum0 : ∑ i ∈ Finset.range m, η ^ i = 0 := by
      rw [geom_sum_eq hη1, hη, sub_self, zero_div]
    have hmΩ : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum0, sub_zero]
      simp
    apply hmv
    rw [hmΩ]
    exact A.valuation.map_sum_lt one_ne_zero (fun i _ => hterm i)
  refine ⟨part1, ?_⟩
  intro g hg
  have hg2 := (mem_Ine.mp hg).2
  apply part1
  · rw [← map_pow, hζ, map_one]
  · exact hg2 ζ (hv1 ζ hζ).le
end
