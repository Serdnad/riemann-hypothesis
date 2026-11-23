module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DirichletCharacter.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_eq_bot_of_orderOf {Q : Type} [CommGroup Q] [Finite Q] (χ : Q →* ℂˣ)
    (h : orderOf χ = Nat.card Q) : χ.ker = ⊥ := by
  have h1 : χ ^ χ.ker.index = 1 := by
    ext x
    have : x ^ χ.ker.index ∈ χ.ker := Subgroup.pow_index_mem _ _
    rw [MonoidHom.mem_ker, map_pow] at this
    simp [MonoidHom.pow_apply, this]
  have h2 : Nat.card Q ∣ χ.ker.index := h ▸ orderOf_dvd_of_pow_eq_one h1
  have h3 : χ.ker.index = Nat.card Q := Nat.dvd_antisymm (Subgroup.index_dvd_card _) h2
  have h4 := Subgroup.card_mul_index χ.ker
  rw [h3] at h4
  have h5 : Nat.card χ.ker = 1 := by
    have hp : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hp (by rw [h4, one_mul])
  exact Subgroup.card_eq_one.1 h5

open Classical in
private theorem totient_le_card_ker {Γ : Type} [CommGroup Γ] [Finite Γ] [Fintype (Γ →* ℂˣ)] (H : Subgroup Γ)
    (hH : IsCyclic (Γ ⧸ H)) :
    Nat.totient H.index ≤ (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card := by
  haveI : NeZero (Monoid.exponent (Γ ⧸ H)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Γ ⧸ H) ℂ
  haveI : Finite ((Γ ⧸ H) →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype ((Γ ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  haveI : IsCyclic ((Γ ⧸ H) →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  have hc : Fintype.card ((Γ ⧸ H) →* ℂˣ) = H.index := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]; rfl
  rw [← IsCyclic.card_orderOf_eq_totient (α := (Γ ⧸ H) →* ℂˣ) (d := H.index) (hc ▸ dvd_rfl)]
  refine Finset.card_le_card_of_injOn (fun χ => χ.comp (QuotientGroup.mk' H)) ?_ ?_
  · intro χ hχ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hχ ⊢
    have := ker_eq_bot_of_orderOf χ hχ
    rw [← MonoidHom.comap_ker, this, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · intro a _ b _ hab
    exact QuotientGroup.monoidHom_ext _ hab

theorem UpperTheory.V.HV.orbSum :
    ∀ (Γ : Type) [CommGroup Γ] [Finite Γ] (T : Finset (Subgroup Γ)), (∀ H ∈ T, IsCyclic (Γ ⧸ H)) → ∑ H ∈ T, Nat.totient H.index ≤ Nat.card Γ := by
  intro Γ _ _ T hT
  classical
  haveI : NeZero (Monoid.exponent Γ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Γ ℂ
  haveI : Finite (Γ →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype (Γ →* ℂˣ) := Fintype.ofFinite _
  calc ∑ H ∈ T, Nat.totient H.index
      ≤ ∑ H ∈ T, (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card :=
        Finset.sum_le_sum fun H hH => by convert totient_le_card_ker H (hT H hH)
    _ = (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker ∈ T).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ Fintype.card (Γ →* ℂˣ) := Finset.card_le_univ _
    _ = Nat.card Γ := by rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orb_gen {G O : Type} [CommGroup G] [Finite G] [CommRing O] [IsDomain O] (f : G →* Oˣ) :
    IsCyclic (G ⧸ f.ker) ∧ ∃ g : G, (∀ x, ∃ a : ℕ, f x = f g ^ a) ∧ f.ker.index = orderOf (f g) := by
  have hfin : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hc : IsCyclic f.range := isCyclic_subgroup_units f.range
  refine ⟨isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange f).symm
    (QuotientGroup.quotientKerEquivRange f).symm.surjective, ?_⟩
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := hc.exists_monoid_generator
  refine ⟨g, fun x => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hg ⟨f x, x, rfl⟩
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  · rw [Subgroup.index_ker, ← orderOf_eq_card_of_forall_mem_powers hg, ← Subgroup.orderOf_coe]

theorem UpperTheory.V.HV.orbFacts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.toUnitHom.ker.index = orderOf ψ ∧ IsCyclic ((ZMod N)ˣ ⧸ ψ.toUnitHom.ker) ∧
      (∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker ↔ ∃ j : ℕ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j) ∧
      {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker}.ncard = Nat.totient (orderOf ψ) := by
  intro O _ _ N _ ψ
  obtain ⟨hc, g, hg, hidx⟩ := orb_gen ψ.toUnitHom
  have hpow : ∀ (χ : DirichletCharacter O N) (k : ℕ) (x : (ZMod N)ˣ),
      (χ ^ k).toUnitHom x = χ.toUnitHom x ^ k := by
    intro χ k x
    ext
    simp [MulChar.pow_apply_coe]
  have hext : ∀ χ χ' : DirichletCharacter O N, (∀ x, χ.toUnitHom x = χ'.toUnitHom x) → χ = χ' := by
    intro χ χ' h
    ext x
    simpa using congrArg Units.val (h x)
  have hone : ∀ x, (1 : DirichletCharacter O N).toUnitHom x = 1 := by
    intro x
    ext
    simp
  have hord : orderOf ψ = orderOf (ψ.toUnitHom g) := by
    rw [orderOf_eq_orderOf_iff]
    intro k
    constructor
    · intro h
      rw [← hpow, h, hone]
    · intro h
      apply hext
      intro x
      obtain ⟨a, ha⟩ := hg x
      rw [hpow, hone, ha, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  have hpos : 0 < orderOf (ψ.toUnitHom g) :=
    (ψ.toUnitHom.isOfFinOrder (isOfFinOrder_of_finite g)).orderOf_pos
  have hfwd : ∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker →
      ∃ j < orderOf ψ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j := by
    intro ψ' h
    have hm : ∀ x, ψ'.toUnitHom x = 1 ↔ ψ.toUnitHom x = 1 := fun x => by
      rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, h]
    have ho : orderOf (ψ'.toUnitHom g) = orderOf (ψ.toUnitHom g) := by
      rw [orderOf_eq_orderOf_iff]
      intro k
      rw [← map_pow, ← map_pow, hm]
    have h1 := IsPrimitiveRoot.orderOf (ψ.toUnitHom g)
    have h2 := IsPrimitiveRoot.orderOf (ψ'.toUnitHom g)
    rw [ho] at h2
    haveI : NeZero (orderOf (ψ.toUnitHom g)) := ⟨hpos.ne'⟩
    obtain ⟨j, hj, hcop, hjj⟩ := (h1.isPrimitiveRoot_iff').1 h2
    refine ⟨j, hord ▸ hj, hord ▸ hcop, hext _ _ fun x => ?_⟩
    obtain ⟨a, ha⟩ := hg x
    have h3 : ψ.toUnitHom (x / g ^ a) = 1 := by rw [map_div, map_pow, ha, div_self']
    have h4 := (hm _).2 h3
    rw [map_div, map_pow, div_eq_one] at h4
    rw [hpow, h4, ha, ← hjj, ← pow_mul, ← pow_mul, mul_comm]
  have hbwd : ∀ j : ℕ, j.Coprime (orderOf ψ) → (ψ ^ j).toUnitHom.ker = ψ.toUnitHom.ker := by
    intro j hj
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hpow]
    constructor
    · intro h
      have h2 : ψ.toUnitHom x ^ orderOf ψ = 1 := by rw [← hpow, pow_orderOf_eq_one, hone]
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one h2)
      rw [hj.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    · intro h
      rw [h, one_pow]
  refine ⟨hidx.trans hord.symm, hc, fun ψ' => ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨j, -, hj⟩ := hfwd ψ' h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact hbwd j hj
  · have hset : {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker} =
        (fun j : ℕ => ψ ^ j) ''
          ((Finset.range (orderOf ψ)).filter (fun a => (orderOf ψ).Coprime a) : Finset ℕ) := by
      ext ψ'
      constructor
      · intro h
        obtain ⟨j, hj, hcop, rfl⟩ := hfwd ψ' h
        exact ⟨j, by simpa using ⟨hj, hcop.symm⟩, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
        exact hbwd j hj'.2.symm
    rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset, Nat.totient_eq_card_coprime]
    refine pow_injOn_Iio_orderOf.mono fun j hj => ?_
    have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
    exact hj'.1
end
