module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle075
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Pi.Hom
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.Continuity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle078
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.PicardGroup
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
import ReciprocityTheory.GaloisValuations.GlobalA
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle005

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem _root_.GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z)) (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal → (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w → ∀ σ : G Z Ω, IsFrob B (normV w) σ → Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧ IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  first | exact @GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | exact GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | (intros; apply GlobalTheory.isFrob_restrictScalars_of_prime_absNorm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem _root_.GlobalTheory.T.exists_cyclotomic_crossing_field_deciding_frobenius : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by
  first | exact @GlobalTheory.ChebCross.cross | exact GlobalTheory.ChebCross.cross | (intros; apply GlobalTheory.ChebCross.cross <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem conj_places_of_same_prime_below : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  intro E Ω _ _ _ _ _ K _ A B h
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : NumberField K := ⟨⟩
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 K)
    (G := Ω ≃ₐ[K] Ω) (primeBelow (F := K) A) (primeBelow (F := K) B) (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
      have hK : ((algebraMap (𝓞 K) (IntCl K Ω) x : IntCl K Ω) : Ω) = ((x : K) : Ω) := rfl
      rw [hK]
      refine h _ (x : K).2 ?_
      exact (x.2.map (IsScalarTower.toAlgHom ℤ K Ω)))
  have hgA : g • A = B := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (g • A) ↔ b' ∈ primeBelow (F := K) B
    rw [primeBelow_smul, hg]
  refine ⟨g.restrictScalars E, fun x hx => ?_, ?_⟩
  · show g x = x
    exact g.commutes ⟨x, hx⟩
  · rw [← hgA]
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem crt_approx_integral : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A : ValuationSubring Ω)
    (c : ℕ), c ≠ 0 →
    ∃ t ∈ K, IsIntegral ℤ t ∧ A.valuation (t - 1) ≤ A.valuation (c : Ω) ∧
      ∀ σ : G E Ω, (∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1)) →
        A.valuation (σ t) ≤ A.valuation (c : Ω) := by
  intro E Ω _ _ _ _ _ K _ A c hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans E K }
  have hint : ∀ {y : Ω}, IsIntegral ℤ y → A.valuation y ≤ 1 := fun hy =>
    (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A hy)
  by_cases hcP : A.valuation (c : Ω) < 1
  swap
  · have h1 : 1 ≤ A.valuation (c : Ω) := not_lt.mp hcP
    refine ⟨1, K.one_mem, isIntegral_one, ?_, fun σ _ => ?_⟩
    · rw [sub_self, map_zero]; exact zero_le'
    · rw [map_one, map_one]; exact h1
  set f : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K) with hf
  have fint : ∀ r : 𝓞 K, IsIntegral ℤ (f r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (algebraMap K Ω).toIntAlgHom
  let Pg : (g : 𝓞 K →+* Ω) → (∀ r, IsIntegral ℤ (g r)) → Ideal (𝓞 K) := fun g hg =>
    (IsLocalRing.maximalIdeal A).comap (g.codRestrict A (fun r => mem_of_isIntegral_int A (hg r)))
  have memPg : ∀ g hg r, r ∈ Pg g hg ↔ A.valuation (g r) < 1 := fun g hg r => by
    simp only [Pg, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have primePg : ∀ g hg, (Pg g hg).IsPrime := fun g hg => Ideal.comap_isPrime _ _
  have key : ∀ (g : 𝓞 K →+* Ω) (hg : ∀ r, IsIntegral ℤ (g r)) (s u : 𝓞 K), s ∉ Pg g hg →
      s * u ∈ Ideal.span {(c : 𝓞 K)} → A.valuation (g u) ≤ A.valuation (c : Ω) := by
    intro g hg s u hs hsu
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hsu
    have hs1 : A.valuation (g s) = 1 :=
      le_antisymm (hint (hg s)) (not_lt.mp fun h => hs ((memPg g hg s).2 h))
    have := congrArg (fun y => A.valuation (g y)) hw
    simp only [map_mul, map_natCast, hs1, one_mul] at this
    rw [← this]
    exact mul_le_of_le_one_left' (hint (hg w))
  have hcP' : (c : 𝓞 K) ∈ Pg f fint := (memPg f fint _).2 (by rwa [map_natCast])
  have hPne : Pg f fint ≠ ⊥ := fun h => by
    have h' := hcP'
    rw [h, Ideal.mem_bot] at h'
    exact hc (by exact_mod_cast h')
  haveI hPmax : (Pg f fint).IsMaximal := Ideal.IsPrime.isMaximal (primePg f fint) hPne
  have hI : Ideal.span {(c : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hc
  classical
  obtain ⟨J, hPJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hI (Pg f fint)
  set a := Multiset.count (Pg f fint)
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(c : 𝓞 K)})) with ha
  have hJP : J ⊔ Pg f fint ^ a = ⊤ := Ideal.sup_pow_eq_top (by rwa [sup_comm])
  have h1mem : (1 : 𝓞 K) ∈ J ⊔ Pg f fint ^ a := by rw [hJP]; exact Submodule.mem_top
  obtain ⟨z, hz, y, hy, hzy⟩ := Submodule.mem_sup.1 h1mem
  obtain ⟨s, hsJ, hsP⟩ : ∃ s ∈ J, s ∉ Pg f fint := by
    by_contra hcon
    push_neg at hcon
    rw [sup_eq_left.2 hcon] at hPJ
    exact hPmax.ne_top hPJ
  have hz1 : z - 1 ∈ Pg f fint ^ a := by
    have e : z - 1 = -y := by rw [← hzy]; ring
    rw [e]; exact neg_mem hy
  refine ⟨f z, (algebraMap (𝓞 K) K z).2, fint z, ?_, ?_⟩
  · have := key f fint s (z - 1) hsP (by rw [hIJ, mul_comm s]; exact Ideal.mul_mem_mul hz1 hsJ)
    simpa only [map_sub, map_one] using this
  · rintro σ ⟨x, hxK, hxint, hx⟩
    set g : 𝓞 K →+* Ω := (σ : Ω →+* Ω).comp f with hg
    have gint : ∀ r, IsIntegral ℤ (g r) := fun r => (fint r).map (σ : Ω →+* Ω).toIntAlgHom
    have hxK' : IsIntegral ℤ (⟨x, hxK⟩ : K) :=
      (isIntegral_algHom_iff (algebraMap K Ω).toIntAlgHom (algebraMap K Ω).injective).1 hxint
    let r : 𝓞 K := ⟨⟨x, hxK⟩, hxK'⟩
    have hne : Pg g gint ≠ Pg f fint := by
      intro heq
      apply hx
      have h1 := memPg g gint r
      have h2 := memPg f fint r
      rw [heq] at h1
      exact h1.symm.trans h2
    obtain ⟨s', hs'P, hs'Q⟩ : ∃ s' ∈ Pg f fint ^ a, s' ∉ Pg g gint := by
      by_contra hcon
      push_neg at hcon
      haveI := primePg g gint
      have h1 : Pg f fint ≤ Pg g gint := Ideal.IsPrime.le_of_pow_le hcon
      exact hne (hPmax.eq_of_le (primePg g gint).ne_top h1).symm
    have := key g gint s' z hs'Q (by rw [hIJ]; exact Ideal.mul_mem_mul hs'P hz)
    exact this

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_algebraMap_sub_eq_sum_conjugates' : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by
  first | exact @GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates | exact GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates | (intros; apply GlobalTheory.exists_algebraMap_sub_eq_sum_conjugates <;> assumption)
end

section

open Polynomial

namespace GlobalTheory.FixedMemRange

theorem fixed_mem_range {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ} (hd : 0 < d)
    {w : AlgebraicClosure (ZMod g)} (hw : w ^ g ^ d = w) :
    ∃ k : GaloisField g d,
      ((IsAlgClosed.lift : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g)) : GaloisField g d → AlgebraicClosure (ZMod g)) k = w := by
  classical
  set ι : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g) := IsAlgClosed.lift with hι
  letI : Fintype (GaloisField g d) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField g d) = g ^ d := by rw [Fintype.card_eq_nat_card]; exact GaloisField.card g d hd.ne'
  have hq : 1 < g ^ d := Nat.one_lt_pow hd.ne' hg.out.one_lt
  set P : (AlgebraicClosure (ZMod g))[X] := X ^ (g ^ d) - X with hP
  have hP0 : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hPdeg : P.natDegree = g ^ d := Polynomial.natDegree_X_pow_sub_X hq
  have hsub : Finset.univ.image ι ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, mem_roots hP0]
    have hk : k ^ g ^ d = k := by
      rw [← hcard]; exact FiniteField.pow_card k
    simp [hP, IsRoot, sub_eq_zero, ← map_pow, hk]
  have hle : P.roots.toFinset.card ≤ (Finset.univ.image ι).card := by
    have hinj : Function.Injective ι := fun a b h => (RingHom.injective ι.toRingHom) h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard, ← hPdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hwm : w ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp [hP, IsRoot, sub_eq_zero, hw]
  rw [← heq] at hwm
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hwm
  exact ⟨k, hk⟩

theorem main : (let d1 : (g : ℕ) → ℕ → [Fact (Nat.Prime g)] → Type := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ GaloisField g d); let d2 : (g d : ℕ) → [inst : Fact (Nat.Prime g)] → d1 g d →ₐ[ZMod g] Formalism.CyclotomicNorms.Fbar g := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ IsAlgClosed.lift); ∀ {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ}, (0 : ℕ) < d → ∀ {w : Formalism.CyclotomicNorms.Fbar g}, w ^ g ^ d = w → ∃ (k : d1 g d), (d2 g d : d1 g d → Formalism.CyclotomicNorms.Fbar g) k = w) := by
  intro d1 d2 g hg d hd w hw
  exact fixed_mem_range hd hw

end GlobalTheory.FixedMemRange
end

section

namespace GlobalTheory.FixedFinsetInvariants

theorem exists_finset_fixed_mem_invariants {G LL V : Type} [Group G] [Field LL] [AddCommGroup V]
    [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ s : Finset G, ∀ v : V, (∀ g ∈ s, ρ g v = v) → v ∈ Formalism.WeaklyAdmissibleFiltrations.H0V ρ := by
  classical
  let F : Finset G → Submodule LL V := fun s => ⨅ g ∈ s, LinearMap.ker (ρ g - LinearMap.id)
  have hF : ∀ (s : Finset G) (v : V), v ∈ F s ↔ ∀ g ∈ s, ρ g v = v := by
    intro s v
    simp only [F, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule LL V)).has_min (Set.range F) ⟨F ∅, ∅, rfl⟩
  refine ⟨s, fun v hv => ?_⟩
  unfold Formalism.WeaklyAdmissibleFiltrations.H0V
  rw [Submodule.mem_iInf]
  intro g
  have hle : F (insert g s) ≤ F s := by
    intro w hw
    rw [hF] at hw ⊢
    exact fun h hh => hw h (Finset.mem_insert_of_mem hh)
  have heq : F (insert g s) = F s := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hv' : v ∈ F (insert g s) := heq ▸ (hF s v).2 hv
  have hg := (hF _ v).1 hv' g (Finset.mem_insert_self g s)
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact hg

end GlobalTheory.FixedFinsetInvariants
end

section

namespace GlobalTheory.NonzeroScalarLattice

theorem exists_ne_zero_smul_mem {G : Type} [Group G] {LL : Type} [Field LL] {O : Type}
    [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [IsDomain O] [IsFractionRing O LL]
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (w : V) :
    ∃ (b : O), b ≠ (0 : O) ∧ b • w ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T L := by
  have hw : w ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.T.smul_mem _ hax
    · rw [mul_smul]; exact L.T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap O LL q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • ((algebraMap O LL p / algebraMap O LL q) • x) = p • x := by
      rw [← algebraMap_smul LL q, smul_smul, mul_div_cancel₀ _ hq1, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.T.smul_mem _ hax

end GlobalTheory.NonzeroScalarLattice
end

section

namespace GlobalTheory.ZModDual

theorem card_quot_ker_le (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A] [Module (ZMod n) A]
    [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (A ⧸ LinearMap.ker b) ≤ Nat.card (B ⧸ LinearMap.ker b.flip) := by
  set K' := LinearMap.ker b.flip
  have : Finite (B ⧸ K') := Finite.of_surjective K'.mkQ K'.mkQ_surjective
  have : Finite (Module.Dual (ZMod n) B) :=
    Finite.of_injective (fun f : Module.Dual (ZMod n) B => (f : B → ZMod n)) DFunLike.coe_injective
  have hle : LinearMap.range b ≤ K'.dualAnnihilator := by
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hy) a
    simpa using this
  calc Nat.card (A ⧸ LinearMap.ker b) = Nat.card (LinearMap.range b) :=
        Nat.card_congr (LinearMap.quotKerEquivRange b).toEquiv
    _ ≤ Nat.card K'.dualAnnihilator :=
        Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ = Nat.card (Module.Dual (ZMod n) (B ⧸ K')) :=
        Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator K').toEquiv.symm
    _ = Nat.card (B ⧸ K') := card_dual_eq n (B ⧸ K')

theorem card_ker_mul_card_eq (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A]
    [Module (ZMod n) A] [Finite A] [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (LinearMap.ker b) * Nat.card B = Nat.card (LinearMap.ker b.flip) * Nat.card A := by
  have h1 := card_quot_ker_le n A B b
  have h2 := card_quot_ker_le n B A b.flip
  rw [LinearMap.flip_flip] at h2
  have heq : Nat.card (A ⧸ LinearMap.ker b) = Nat.card (B ⧸ LinearMap.ker b.flip) := le_antisymm h1 h2
  have eA := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b)
  have eB := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b.flip)
  rw [eA, eB, heq]
  ring

end GlobalTheory.ZModDual
end

section

open GlobalTheory.UnitLemma

theorem _root_.GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  first | exact @GlobalTheory.TorusInteg.torus_integral_iff | exact GlobalTheory.TorusInteg.torus_integral_iff | (intros; apply GlobalTheory.TorusInteg.torus_integral_iff <;> assumption)
end

section

open GlobalTheory.UnitLemma

theorem _root_.GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ t : T, ((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  first | exact @GlobalTheory.TorusKer.valsAt_torus_eq_one_iff | exact GlobalTheory.TorusKer.valsAt_torus_eq_one_iff | (intros; apply GlobalTheory.TorusKer.valsAt_torus_eq_one_iff <;> assumption)
end

section

open GlobalTheory.UnitLemma

theorem _root_.GlobalTheory.T.zValuationsAtIndices_torus_surjective : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype) := by
  first | exact @GlobalTheory.UnitLemma.valsAt_torus_surjective | exact GlobalTheory.UnitLemma.valsAt_torus_surjective | (intros; apply GlobalTheory.UnitLemma.valsAt_torus_surjective <;> assumption)
end
