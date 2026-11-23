module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle001
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.clSubUniv :
    ∀ (K : Type) [Field K] [NumberField K], clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  intro K _ _
  classical
  have key : ∀ I : Ideal (𝓞 K), ∀ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)),
      ClassGroup.mk0 ⟨I, hI⟩ ∈ clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro hI
      exact absurd hI (zero_notMem_nonZeroDivisors)
    | h₂ u hu =>
      intro hI
      have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
      subst hu'
      have : (⟨⊤, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = 1 := Subtype.ext Ideal.one_eq_top.symm
      rw [this, map_one]
      exact Subgroup.one_mem _
    | h₃ a p ha hp ih =>
      intro hI
      have ha' : a ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero ha
      have hp0 : p ≠ 0 := hp.ne_zero
      have hp' : p ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hp0
      have hsplit : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨p, hp'⟩ * ⟨a, ha'⟩ := rfl
      rw [hsplit, map_mul]
      refine Subgroup.mul_mem _ ?_ (ih ha')
      have hpr : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      let v : HeightOneSpectrum (𝓞 K) := ⟨p, hpr, hp0⟩
      have hv : primeCl v = ClassGroup.mk0 ⟨p, hp'⟩ := rfl
      rw [← hv]
      exact Subgroup.subset_closure ⟨v, Set.mem_univ _, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective x
  exact key I hI
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exp_tors (K : Type) [Field K] [NumberField K] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ a : K, IsOfFinOrder a → a ^ m = 1 := by
  refine ⟨Units.torsionOrder K, Units.torsionOrder_ne_zero K, fun a ha => ?_⟩
  obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  have hi : IsIntegral ℤ a := IsIntegral.of_pow hk (by rw [hak]; exact isIntegral_one)
  let x : 𝓞 K := ⟨a, hi⟩
  have hx : x ^ k = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hak
  let y : (𝓞 K)ˣ := Units.ofPowEqOne x k hx hk.ne'
  have hy : y ∈ Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Units.ext (by simpa [y] using hx)⟩)
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hy
  have h2 := congrArg (fun z : (𝓞 K)ˣ => algebraMap (𝓞 K) K z) hy
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h2
  exact h2

private theorem conj_root {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (g u : Ω ≃ₐ[F] Ω) (β : Ω)
    (hβ : IsOfFinOrder β) : g (u (g.symm β)) = u β := by
  have hp := IsPrimitiveRoot.orderOf β
  haveI : NeZero (orderOf β) := ⟨hβ.orderOf_pos.ne'⟩
  have key : ∀ s : Ω ≃ₐ[F] Ω, ∃ i : ℕ, β ^ i = s β := fun s => by
    obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one (ξ := s β) (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := key g.symm
  obtain ⟨j, hj⟩ := key u
  rw [← hi, map_pow, ← hj, ← pow_mul, mul_comm, pow_mul, hi, map_pow, g.apply_symm_apply]

private theorem exists_gen (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n] :
    ∃ (ξ : Ωˣ) (b : K), (ξ : Ω) ^ n = algebraMap K Ω b ∧
      ∀ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a → IsOfFinOrder β → ∃ j : ℤ, (ξ : Ω) ^ j = β := by
  obtain ⟨m, hm, hK⟩ := exp_tors K
  haveI : NeZero (n * m) := ⟨mul_ne_zero (NeZero.ne n) hm⟩
  let T : Subgroup Ωˣ := rootsOfUnity (n * m) Ω ⊓
    ((Units.map (algebraMap K Ω).toMonoidHom).range).comap (powMonoidHom n)
  haveI : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : T ≤ _))
  obtain ⟨⟨ξ, hξ⟩, hg⟩ := (isCyclic_subgroup_units T).exists_generator
  obtain ⟨b, hb⟩ := hξ.2
  refine ⟨ξ, b, ?_, fun β a h hβ => ?_⟩
  · have := congrArg Units.val hb
    simpa using this.symm
  · have h0 : β ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at h
      exact a.ne_zero ((map_eq_zero _).1 h.symm)
    have ha : IsOfFinOrder (a : K) := by
      have := hβ.pow (n := n)
      rw [h] at this
      obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 this
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, (algebraMap K Ω).injective (by rw [map_pow, hak, map_one])⟩
    have hT : Units.mk0 β h0 ∈ T := by
      refine ⟨(mem_rootsOfUnity _ _).2 (Units.ext ?_), a, Units.ext (by simpa using h.symm)⟩
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [pow_mul, h, ← map_pow, hK a ha, map_one]
    obtain ⟨j, hj⟩ := hg ⟨_, hT⟩
    refine ⟨j, ?_⟩
    have := congrArg (fun z : T => ((z : Ωˣ) : Ω)) hj
    simpa using this

private theorem exists_generator_kummer_cocycle {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (U : Subgroup (Ω ≃ₐ[F] Ω)) (n : ℕ) [NeZero n]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) (hU : ∀ u : U, u.1 ζ = ζ) (ξ : Ωˣ) (hξ : ∀ u : U, u.1 (ξ ^ n) = ξ ^ n) :
    ∃ u0 : U, ∀ u : U, ∃ k : ℤ, u.1 ξ / ξ = (u0.1 ξ / ξ) ^ k := by
  have h1 : ∀ u : U, (u.1 ξ / ξ) ^ n = 1 := fun u => by
    rw [div_pow, ← map_pow, hξ, div_self (pow_ne_zero _ ξ.ne_zero)]
  have h2 : ∀ u v : U, u.1 (v.1 ξ / ξ) = v.1 ξ / ξ := fun u v => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (h1 v)
    rw [← hi, map_pow, hU]
  have h3 : ∀ u : U, u.1 ξ ≠ 0 := fun u => (map_ne_zero _).2 ξ.ne_zero
  let f : U →* Ωˣ := MonoidHom.mk' (fun u => Units.mk0 (u.1 ξ / ξ) (div_ne_zero (h3 u) ξ.ne_zero)) fun u v => by
    apply Units.ext
    have := h2 u v
    rw [map_div₀, div_eq_iff (h3 u)] at this
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, this]
    ring
  have hle : f.range ≤ rootsOfUnity n Ω := by
    rintro _ ⟨u, rfl⟩
    exact (mem_rootsOfUnity _ _).2 (Units.ext (by simpa [f] using h1 u))
  haveI : Finite f.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨⟨_, u0, rfl⟩, hg⟩ := (isCyclic_subgroup_units f.range).exists_generator
  refine ⟨u0, fun u => ?_⟩
  obtain ⟨k, hk⟩ := hg ⟨f u, u, rfl⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun z : f.range => ((z : Ωˣ) : Ω)) hk
  simpa [f] using this.symm

theorem UpperTheory.V.Kum.reflRoot :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] (ψ : G F Ω →* (ZMod n)ˣ), U = galOf F K Ω → IsPrimitiveRoot ζ n →
    Nat.card {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} ≤ Nat.card (scalRep (ZMod n) ψ).invariants ∧
    Finite {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ ψ hU hζ
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hinj : ∀ x y : ZMod n, algebraMap K Ω ζ ^ x.val = algebraMap K Ω ζ ^ y.val → x = y := fun x y h =>
    ZMod.val_injective n (hζ'.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)
  obtain ⟨ξ, b, hb, hξ⟩ := exists_gen K Ω n
  obtain ⟨u0, hu0⟩ := exists_generator_kummer_cocycle (galOf F K Ω) n _ hζ' (fun u => u.2 ζ) ξ (fun u => by rw [hb]; exact u.2 b)
  have hinv : ∀ φ : galOf F K Ω → ZMod n, φ ∈ EqHom N (galOf F K Ω) (scalRep (ZMod n) ψ) → ∀ β : Ω,
      IsRad (algebraMap K Ω ζ) _ φ β → IsOfFinOrder β → φ u0 ∈ (scalRep (ZMod n) ψ).invariants := by
    intro φ hφ β hr hβ g
    let u' : galOf F K Ω := ⟨g * u0.1 * g⁻¹, (galOf_normal F K Ω).conj_mem _ u0.2 g⟩
    have h1 : φ u' = scalRep (ZMod n) ψ g (φ u0) :=
      (Submodule.mem_iInf _).1 hφ.2 g u0 u' fun x => by
        show g (u0.1 (g.symm (g x))) = g (u0.1 x)
        rw [g.symm_apply_apply]
    rw [← h1]
    apply hinj
    have h2 : u'.1 β = u0.1 β := conj_root g u0.1 β hβ
    rw [hr.2, hr.2] at h2
    exact mul_right_cancel₀ hr.1 h2
  have hval : ∀ (φ : galOf F K Ω → ZMod n) (j : ℤ), IsRad (algebraMap K Ω ζ) _ φ ((ξ : Ω) ^ j) →
      ∀ u, algebraMap K Ω ζ ^ (φ u).val = (u.1 ξ / ξ) ^ j := fun φ j hr u => by
    rw [div_zpow, ← map_zpow₀, hr.2, mul_div_cancel_right₀ _ hr.1]
  let e : {φ : galOf F K Ω → ZMod n // φ ∈ EqHom N _ (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) _ φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} →
      (scalRep (ZMod n) ψ).invariants := fun φ => ⟨φ.1 u0, by
    obtain ⟨h, β, a, hr, -, hβ⟩ := φ.2
    exact hinv _ h β hr hβ⟩
  have he : Function.Injective e := by
    rintro ⟨φ, hφ, β, a, hr, ha, hβ⟩ ⟨φ', hφ', β', a', hr', ha', hβ'⟩ h
    have h0 : φ u0 = φ' u0 := congrArg Subtype.val h
    obtain ⟨j, rfl⟩ := hξ β a ha hβ
    obtain ⟨j', rfl⟩ := hξ β' a' ha' hβ'
    refine Subtype.ext (funext fun u => hinj _ _ ?_)
    obtain ⟨k, hk⟩ := hu0 u
    show algebraMap K Ω ζ ^ (φ u).val = algebraMap K Ω ζ ^ (φ' u).val
    rw [hval φ j hr, hval φ' j' hr', hk, ← zpow_mul, ← zpow_mul, mul_comm k, mul_comm k, zpow_mul, zpow_mul,
      ← hval φ j hr, ← hval φ' j' hr', h0]
  exact ⟨Nat.card_le_card_of_injective e he, Finite.of_injective e he⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ram_one {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (L : IntermediateField K E) (h : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup) :
    (P.under (𝓞 L)).ramificationIdx (𝓞 K) = 1 := by
  have hb := v.ne_bot
  have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hb P
  have hqb : P.under (𝓞 L) ≠ ⊥ := Ideal.under_ne_bot _ hPb
  have : IsGaloisGroup L.fixingSubgroup L E :=
    .of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv L) fun _ _ ↦ rfl
  have : IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ L E
  have := v.isMaximal
  have : (P.under (𝓞 L)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqb
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have : Finite (𝓞 L ⧸ P.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L.fixingSubgroup) (P.under (𝓞 L)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[K] E)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P L.fixingSubgroup] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 L)) P
  have h4 : Nat.card (P.inertia L.fixingSubgroup) =
      Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := by
    rw [← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]
  rw [← h1, ← h2, h4] at h3
  have hpos : 0 < Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := Nat.card_pos
  rw [inf_eq_left.mpr h] at h3 hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)

private theorem dvd_of_ram {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (h : Q.ramificationIdx (𝓞 K) = 1) (n : ℕ) (b : L) (a : Kˣ) (hb : b ^ n = algebraMap K L a) :
    (n : ℤ) ∣ ordv v a := by
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have : w.asIdeal.LiesOver v.asIdeal := (inferInstance : Q.LiesOver v.asIdeal)
  have h1 := HeightOneSpectrum.valuation_liesOver L v w (a : K)
  rw [h, pow_one, ← hb, map_pow,
    ← HeightOneSpectrum.valuationOfNeZero_eq] at h1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, ← WithZero.coe_one, WithZero.coe_inj] at h1
    simp [ordv, h1]
  · have h0 : w.valuation L b ≠ 0 := fun e => by
      rw [e, zero_pow hn.ne'] at h1
      exact WithZero.coe_ne_zero h1
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hm, ← WithZero.coe_pow, WithZero.coe_inj] at h1
    rw [ordv, h1, toAdd_pow, dvd_neg, nsmul_eq_mul]
    exact dvd_mul_right _ _

private theorem dvd_fin {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal] (n : ℕ) (b : E) (a : Kˣ)
    (hb : b ^ n = algebraMap K E a) (h : ∀ τ ∈ P.inertia (E ≃ₐ[K] E), τ b = b) : (n : ℤ) ∣ ordv v a := by
  let L : IntermediateField K E := IntermediateField.fixedField (P.inertia (E ≃ₐ[K] E))
  have hle : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hbL : b ∈ L := (IntermediateField.mem_fixedField_iff _ _).2 h
  have : (P.under (𝓞 L)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  exact dvd_of_ram v (P.under (𝓞 L)) (ram_one v P L hle) n ⟨b, hbL⟩ a (Subtype.ext hb)

theorem UpperTheory.V.Kum.dvdOfIne :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (β : Ω) (a : Kˣ), IsPlaceOver A v → β ^ n = algebraMap K Ω a → (∀ g ∈ Ine (F := K) A, g β = β) → (n : ℤ) ∣ ordv v a := by
  intro K Ω _ _ _ _ _ n A v β a hA hβ hI
  have : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField
  have hβL : β ∈ L := FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  have : NumberField L := NumberField.of_module_finite K _
  have hv : (CompanionTheory.PlaceDict.cen A).under (𝓞 K) = v.asIdeal := Ideal.ext fun x => hA x
  have : Algebra.IsIntegral (𝓞 K) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have hm : (CompanionTheory.PlaceDict.cen A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap (𝓞 K) (𝓞 Ω))
      (algebraMap_isIntegral_iff.mpr this) _ (by
      have := v.isMaximal
      rwa [← hv] at this)
  let P : Ideal (𝓞 L) := (CompanionTheory.PlaceDict.cen A).under (𝓞 L)
  have : P.LiesOver v.asIdeal := ⟨by rw [← hv]; exact (Ideal.under_under _).symm⟩
  refine dvd_fin v P n ⟨β, hβL⟩ a (Subtype.ext hβ) fun τ hτ => ?_
  obtain ⟨φ, h1, h2⟩ := CompanionTheory.PlaceDict.lift L (CompanionTheory.PlaceDict.cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact hτ x
  obtain ⟨h3, h4⟩ := CompanionTheory.PlaceDict.of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  have h5 : φ ∈ Ine (F := K) A := ⟨h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩
  rw [← h1]
  exact Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ h5))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.unitMinus :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (a : Kˣ),
      a ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K →
      a * Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a ∈ powK (K := K) n →
      a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n ∧
        (Odd n → a ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n) := by
  intro K _ _ _ n a ha hc
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (a : K)
    (fun v => (ha v (Set.notMem_empty v)).le)
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((a⁻¹ : Kˣ) : K)
    (fun v => ((Subgroup.inv_mem _ ha) v (Set.notMem_empty v)).le)
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, hx, hy, map_one, Units.mul_inv]
  let u : (𝓞 K)ˣ := Units.mkOfMulEqOne x y hxy
  let f : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hu : f u = a := Units.ext hx
  have hcu : f (IsCMField.unitsComplexConj K u) = Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a := by
    rw [← hu]
    exact Units.ext rfl
  have hfin : IsOfFinOrder (u * (IsCMField.unitsComplexConj K u)⁻¹) :=
    (IsCMField.unitsMulComplexConjInv K u).2
  have htor : a * (Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a)⁻¹ ∈ CommGroup.torsion Kˣ := by
    have := f.isOfFinOrder hfin
    rw [map_mul, map_inv, hu, hcu] at this
    exact this
  have h2 : a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) n := by
    have e : a ^ 2 = (a * (Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a)⁻¹) *
        (a * Units.map (UpperTheory.V.cE (E := K)).toMonoidHom a) := by
      rw [mul_mul_mul_comm, inv_mul_cancel, mul_one, pow_two]
    rw [e]
    exact Subgroup.mul_mem_sup htor hc
  refine ⟨h2, ?_⟩
  rintro ⟨k, rfl⟩
  have hn : a ^ (2 * k + 1) ∈ CommGroup.torsion Kˣ ⊔ powK (K := K) (2 * k + 1) :=
    Subgroup.mem_sup_right ⟨a, rfl⟩
  rw [pow_succ, pow_mul] at hn
  exact (Subgroup.mul_mem_cancel_left _ (Subgroup.pow_mem _ h2 k)).1 hn
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

theorem UpperTheory.V.Kum.toGalDict :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω),
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A) ∧
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Ine (F := K) A ↔ u.1 ∈ Ine (F := F) A) ∧
    Continuous (toGal K hU) ∧ (galOf F K Ω ≤ U → IsHomeomorph (toGal K hU) ∧ IsOpen (U : Set (G F Ω))) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU
  obtain ⟨hE, hO, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A := by
    intro A u
    rw [mem_Dec, mem_Dec]
    have e : toGal K hU u • A = u.1 • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    rw [e]
  have hcomp : galEmb F K Ω ∘ toGal K hU = Subtype.val := funext fun u => AlgEquiv.ext fun x => rfl
  have hc : Continuous (toGal K hU) := by
    rw [hE.isInducing.continuous_iff, hcomp]
    exact continuous_subtype_val
  refine ⟨hD, fun A u => ?_, hc, fun h => ⟨?_, ?_⟩⟩
  · exact ⟨fun h => ⟨(hD A u).1 h.1, h.2⟩, fun h => ⟨(hD A u).2 h.1, h.2⟩⟩
  · rw [isHomeomorph_iff_exists_inverse]
    refine ⟨hc, fun σ => ⟨galEmb F K Ω σ, h (galEmb_mem F K Ω σ)⟩, fun u => Subtype.ext (AlgEquiv.ext fun x => rfl),
      fun σ => AlgEquiv.ext fun x => rfl, hE.continuous.subtype_mk _⟩
  · rw [le_antisymm hU h]
    exact hO
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (k : ℕ) (hk : k ≠ 0) :
    (Polynomial.X ^ k - 1 : Polynomial F).rootSet Ω = {b : Ω | ∃ m ∈ ({k} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
  have hp : (Polynomial.X ^ k - 1 : Polynomial F) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk) (1 : F)
  ext b
  rw [Polynomial.mem_rootSet_of_ne hp]
  simp [sub_eq_zero, hk]

private theorem apply_mem_fn_of_isLift (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (l n : ℕ) (τ : F ≃+* F)
    (σ : Ω ≃+* Ω) (h : IsLift τ σ) (x : Ω) (hx : x ∈ Fn F Ω l n) : σ x ∈ Fn F Ω l n := by
  have hx' : x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω) := hx
  show σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω)
  refine IntermediateField.adjoin_induction F
    (motive := fun x _ => σ x ∈ IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω))
    ?_ ?_ ?_ ?_ ?_ hx'
  · intro y hy
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet] at hy ⊢
    obtain ⟨hp, hy⟩ := hy
    refine ⟨hp, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at hy ⊢
    rw [← map_pow, ← map_one σ, ← map_sub, hy, map_zero]
  · intro c
    rw [h c]
    exact IntermediateField.algebraMap_mem _ _
  · intro y z _ _ hy hz
    rw [map_add (f := _)]
    exact add_mem hy hz
  · intro y _ hy
    rw [map_inv₀]
    exact inv_mem hy
  · intro y z _ _ hy hz
    rw [map_mul]
    exact mul_mem hy hz

theorem UpperTheory.V.Kum.fnCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) ∧ (∀ (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∃ τ' : Fn F Ω l n ≃+* Fn F Ω l n, IsLift τ' σ) ∧ (2 ≤ n → IsTotallyComplex (Fn F Ω l n)) := by
  intro F Ω _ _ _ _ _ l _ n
  have hl : l.Prime := Fact.out
  have hk : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ n) := ⟨hk⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hFn : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ m ∈ ({l ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
    show IntermediateField.adjoin F _ = _
    rw [rootSet_X_pow_sub_one_eq_setOf_exists_mem_singleton F Ω _ hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [hFn]
    refine IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot (S := {l ^ n}) (K := F) (L := Ω) ?_
    intro m hm _
    rw [Set.mem_singleton_iff] at hm
    subst hm
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  · intro τ σ h
    have hs : IsLift τ.symm σ.symm := by
      intro x
      apply σ.injective
      rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]
    refine ⟨{ toFun := fun x => ⟨σ x, apply_mem_fn_of_isLift F Ω l n τ σ h x.1 x.2⟩,
              invFun := fun x => ⟨σ.symm x, apply_mem_fn_of_isLift F Ω l n τ.symm σ.symm hs x.1 x.2⟩,
              left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1),
              right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1),
              map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1),
              map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }, ?_⟩
    intro x
    rfl
  · intro hn2
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hzmem : z ∈ Fn F Ω l n := by
      rw [hFn]
      exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, rfl, hk, hz.pow_eq_one⟩
    have hζ : IsPrimitiveRoot (⟨z, hzmem⟩ : Fn F Ω l n) (l ^ n) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Fn F Ω l n).val) hz Subtype.val_injective
    have hcyc := IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ℚ) hζ
    have h2 : 2 < l ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hl.pos hn2
    have htc := @IsCyclotomicExtension.Rat.isTotallyComplex (l ^ n) _
      (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) _ _ hcyc h2
    exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) (Fn F Ω l n)
end
