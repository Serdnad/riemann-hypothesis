module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle030
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle003
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle006
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open Pointwise

namespace GlobalTheory

theorem isFrob_restrictScalars_of_prime_absNorm :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z))
      (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal →
      (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w →
      ∀ σ : G Z Ω, IsFrob B (normV w) σ →
        Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧
          IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  intro F Ω _ _ _ _ _ Z _ w v hwv hp B hB σ hσ
  have hn : Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    have h1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
    rw [h1, pow_one] at h
    exact h
  refine ⟨hn, fun x => ?_, ?_, fun x hx => ?_⟩
  · have h := hB (algebraMap (𝓞 F) (𝓞 Z) x)
    rw [← Ideal.mem_of_liesOver w.asIdeal v.asIdeal x] at h
    exact h
  · have h : σ • B = B := hσ.1
    show (σ.restrictScalars F) • B = B
    ext x
    conv_rhs => rw [← h]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  · have e : normV v = normV w := by
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hn
    rw [e]
    exact hσ.2 x hx

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.ChebCross

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem autToPow_eq_iff {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (f : Ω ≃ₐ[F] Ω)
    (j : (ZMod m)ˣ) : hζ.autToPow F f = j ↔ f ζ = ζ ^ (j : ZMod m).val := by
  constructor
  · rintro rfl
    exact (hζ.autToPow_spec F f).symm
  · intro h
    rw [← hζ.autToPow_spec F f] at h
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h
    exact Units.ext (ZMod.val_injective m this)

theorem exists_fixing [CharZero Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (hirr : Irreducible (cyclotomic m L))
    (j : (ZMod m)ˣ) : ∃ u : Ω ≃ₐ[F] Ω, u ∈ L.fixingSubgroup ∧ hζ.autToPow F u = j := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero L := (algebraMap L Ω).charZero
  have hj : IsPrimitiveRoot (ζ ^ (j : ZMod m).val) m :=
    hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime j)
  have h1 : minpoly L (ζ ^ (j : ZMod m).val) = minpoly L ζ := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      ← hj.minpoly_eq_cyclotomic_of_irreducible hirr]
  obtain ⟨u, hu⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := L) Ω).1 h1
  refine ⟨u.restrictScalars F, ?_, ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact u.commutes ⟨x, hx⟩
  · rw [autToPow_eq_iff]
    exact hu

theorem irreducible_of_onto [CharZero Ω] (Z : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m)
    (h : ∀ j : (ZMod m)ˣ, ∃ u : Ω ≃ₐ[F] Ω, u ∈ Z.fixingSubgroup ∧ hζ.autToPow F u = j) :
    Irreducible (cyclotomic m Z) := by
  classical
  haveI : CharZero Z := (algebraMap Z Ω).charZero
  have hm : 0 < m := NeZero.pos m
  have h0 : aeval ζ (cyclotomic m Z) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm
  have hint : IsIntegral Z ζ := ⟨_, cyclotomic.monic m Z, h0⟩
  have hdvd := minpoly.dvd Z ζ h0
  have hsub : primitiveRoots m Ω ⊆ ((minpoly Z ζ).aroots Ω).toFinset := by
    intro μ hμ
    rw [mem_primitiveRoots hm] at hμ
    obtain ⟨i, hi, hic, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ
    obtain ⟨u, hu, hj⟩ := h (ZMod.unitOfCoprime i hic)
    rw [autToPow_eq_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi] at hj
    rw [Multiset.mem_toFinset, mem_aroots']
    refine ⟨((minpoly.monic hint).map (algebraMap Z Ω)).ne_zero, ?_⟩
    let v : Ω ≃ₐ[Z] Ω := Z.fixingSubgroupEquiv ⟨u, hu⟩
    have hv : v ζ = ζ ^ i := hj
    rw [← hv, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdeg : (cyclotomic m Z).natDegree ≤ (minpoly Z ζ).natDegree := by
    rw [natDegree_cyclotomic, ← hζ.card_primitiveRoots]
    refine (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ?_)
    refine (card_roots' _).trans ?_
    exact natDegree_map_le
  have := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m Z) hdvd hdeg
  rw [this]
  exact minpoly.irreducible hint

theorem exists_pow_eq_on (M : IntermediateField F Ω) [FiniteDimensional F M] [IsGalois F M]
    (h σ : Ω ≃ₐ[F] Ω)
    (hσ : σ ∈ (M ⊓ IntermediateField.fixedField (Subgroup.zpowers h)).fixingSubgroup) :
    ∃ k : ℕ, ∀ x ∈ M, σ x = (h ^ k) x := by
  let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M
  have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : M), ((ρ f x : M) : Ω) = f x := fun f x =>
    AlgEquiv.restrictNormal_commutes f M x
  have h1 : ρ σ ∈ Subgroup.zpowers (ρ h) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (ρ h)),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply Subtype.ext
    rw [hρ]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine hσ _ ⟨x.2, ?_⟩
    change (x : Ω) ∈ IntermediateField.fixedField (Subgroup.zpowers h)
    rw [IntermediateField.mem_fixedField_iff]
    rintro f ⟨n, rfl⟩
    have := hx (ρ (h ^ n)) ⟨n, by simp⟩
    rw [← hρ, this]
  rw [← mem_powers_iff_mem_zpowers] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, fun x hx => ?_⟩
  have := hρ σ ⟨x, hx⟩
  rw [← hk] at this
  simp only [← map_pow] at this
  rw [hρ] at this
  exact this.symm

theorem cross : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by
  intro F Ω _ _ _ _ _ L _ _ g m hm hdiv hirr
  haveI : Fact m.Prime := ⟨hm⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod m)ˣ)
  obtain ⟨u, hu, hu'⟩ := exists_fixing L hζ hirr (τ * (hζ.autToPow F g)⁻¹)
  set h := u * g with hh
  have hχ : hζ.autToPow F h = τ := by rw [hh, map_mul, hu']; simp
  haveI : IsCyclotomicExtension {m} F (IntermediateField.adjoin F {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IsCyclotomicExtension.finiteDimensional {m} F _
  haveI : IsGalois F (IntermediateField.adjoin F {ζ}) := IsCyclotomicExtension.isGalois {m} F _
  let M : IntermediateField F Ω := L ⊔ IntermediateField.adjoin F {ζ}
  haveI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _
  haveI : IsGalois F M := { }
  have hζM : ζ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.mem_adjoin_simple_self F ζ)
  refine ⟨M ⊓ IntermediateField.fixedField (Subgroup.zpowers h), τ, ?_, ?_, ?_⟩
  · exact Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : _ ≤ M)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  · refine irreducible_of_onto _ hζ fun j => ?_
    obtain ⟨n, rfl⟩ := hτ j
    refine ⟨h ^ n, ?_, by simp [hχ]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixedField_iff _ _).1 hx.2 _ ⟨n, rfl⟩
  · intro σ hσ hσζ
    obtain ⟨k, hk⟩ := exists_pow_eq_on M h σ hσ
    have h1 : hζ.autToPow F (h ^ k) = τ := by
      rw [autToPow_eq_iff, ← hk ζ hζM]
      exact hσζ ζ hζ.pow_eq_one
    rw [map_pow, hχ] at h1
    have hord : orderOf τ = m - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]
    have hmod : k ≡ 1 [MOD m - 1] := by
      rw [← hord, ← pow_eq_pow_iff_modEq, h1, pow_one]
    let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L
    have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : L), ((ρ f x : L) : Ω) = f x := fun f x =>
      AlgEquiv.restrictNormal_commutes f L x
    have h2 : ρ σ = ρ (h ^ k) := by
      ext x
      rw [hρ, hρ]
      exact hk _ ((le_sup_left : L ≤ M) x.2)
    have h3 : ρ h ^ k = ρ h := by
      conv_rhs => rw [← pow_one (ρ h)]
      rw [pow_eq_pow_iff_modEq]
      refine hmod.of_dvd (dvd_trans ?_ hdiv)
      rw [← IsGalois.card_aut_eq_finrank]
      exact orderOf_dvd_natCard _
    have h4 : ρ u = 1 := by
      rw [← IntermediateField.restrictNormalHom_ker] at hu
      exact hu
    rw [← IntermediateField.restrictNormalHom_ker]
    change ρ (σ * g⁻¹) = 1
    rw [map_mul, h2, map_pow, h3, hh, map_mul, h4, map_inv]
    simp

end GlobalTheory.ChebCross
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem exists_algebraMap_sub_eq_sum_conjugates : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by
  intro E Ω _ _ _ _ _ y
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Normal E Ω := IsAlgClosure.normal E Ω
  have hy : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set p := minpoly E y with hp
  set q := p.map (algebraMap E Ω) with hq
  have hirr : Irreducible p := minpoly.irreducible hy
  have hmon : p.Monic := minpoly.monic hy
  have hsep : q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E y : p.Separable)
  have hnd : q.roots.Nodup := nodup_roots hsep
  have hspl : q.Splits := IsAlgClosed.splits q
  have hsum : q.nextCoeff = -q.roots.sum := hspl.nextCoeff_eq_neg_sum_roots_of_monic (hmon.map _)
  have hq0 : q ≠ 0 := (hmon.map _).ne_zero
  have hyr : y ∈ q.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval E y
  refine ⟨-p.nextCoeff, q.roots.toFinset.erase y, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxy, hxr⟩ := Finset.mem_erase.mp hx
    refine ⟨hxy, ?_⟩
    have hax : aeval x p = 0 := by
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap] at hxr
      exact hxr
    have hmx : p = minpoly E x := minpoly.eq_of_irreducible_of_monic hirr hax hmon
    have horb : x ∈ MulAction.orbit (G E Ω) y :=
      (Normal.minpoly_eq_iff_mem_orbit (F := E) Ω).mp (by rw [← hmx])
    obtain ⟨σ, hσ⟩ := horb
    exact ⟨σ, hσ⟩
  · rw [Finset.sum_erase_eq_sub hyr, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd, Multiset.map_id', map_neg, ← nextCoeff_map_eq, ← hq, hsum, neg_neg]

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory.GLintLattice

variable {K : Type} [Field K] (A : ValuationSubring K) {r : ℕ}

theorem mem_span_basisFun_iff (y : Fin r → K) :
    y ∈ Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ ∀ i, y i ∈ A := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    refine ⟨fun i => ⟨y i, h i⟩, ?_⟩
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

theorem mulVec_maps_iff (M : Matrix (Fin r) (Fin r) K) :
    (∀ y : Fin r → K, (∀ i, y i ∈ A) → ∀ i, (M *ᵥ y) i ∈ A) ↔ ∀ i j, M i j ∈ A := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single_one] using this
  · intro h y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem (fun j _ => mul_mem (h i j) (hy j))

theorem mem_GLint_iff (x : GL (Fin r) K) :
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring ↔
      (∀ i j, (x : Matrix (Fin r) (Fin r) K) i j ∈ A) ∧
        (∀ i j, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ∈ A) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show ((u : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact (u : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
    · rw [← map_inv]
      show (((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact ((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map A.toSubring.subtype = (x : Matrix (Fin r) (Fin r) K) := by ext; rfl
    have hM' : M'.map A.toSubring.subtype = ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
      ext; rfl
    have inj : Function.Injective fun N : Matrix (Fin r) (Fin r) A.toSubring => N.map A.toSubring.subtype :=
      Matrix.map_injective Subtype.val_injective
    have e1 : M * M' = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.mul_inv)
    have e2 : M' * M = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.inv_mul)
    refine ⟨⟨M, M', e1, e2⟩, ?_⟩
    ext i j
    rfl

theorem stdLattice_map_eq_iff_mem_GLint : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ)
    (x : GL (Fin r) K),
    (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
        ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) =
      Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  intro K _ A r x
  have hf : ∀ z, ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) z =
      (x : Matrix (Fin r) (Fin r) K) *ᵥ z := fun z => rfl
  have inv_x : ∀ z : Fin r → K, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ
      ((x : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have x_inv : ∀ z : Fin r → K, (x : Matrix (Fin r) (Fin r) K) *ᵥ
      (((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_GLint_iff, ← mulVec_maps_iff, ← mulVec_maps_iff]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hm : (x : Matrix (Fin r) (Fin r) K) *ᵥ y ∈
          (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) :=
        ⟨y, (mem_span_basisFun_iff A y).2 hy, hf y⟩
      rw [h] at hm
      exact (mem_span_basisFun_iff A _).1 hm
    · have hm : y ∈ (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) := by
        rw [h]; exact (mem_span_basisFun_iff A y).2 hy
      obtain ⟨z, hz, hzy⟩ := hm
      rw [hf] at hzy
      rw [← hzy, inv_x]
      exact (mem_span_basisFun_iff A z).1 hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hf, mem_span_basisFun_iff]
      exact h1 z ((mem_span_basisFun_iff A z).1 hz)
    · intro y hy
      refine ⟨((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ y,
        (mem_span_basisFun_iff A _).2 (h2 y ((mem_span_basisFun_iff A y).1 hy)), ?_⟩
      rw [hf, x_inv]

end GlobalTheory.GLintLattice
end

section

open scoped BigOperators

namespace GlobalTheory

theorem card_subspaces_sup_eq_top :
    ∀ (k : Type) [Field k] [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k)),
      Module.finrank k R ≤ r →
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} =
        if Module.finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  intro k _ _ r t R hR
  convert AdaptedLocalData.card_sup_eq_top r t R hR

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.center_monoidAlgebra_le_span_centralIntegral : ∀ (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G), z ∈ Subalgebra.center R (MonoidAlgebra R G) → z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) '' {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) := by
  first | exact @GlobalTheory.GroupAlg.center_mem_span_classSums | exact GlobalTheory.GroupAlg.center_mem_span_classSums | (intros; apply GlobalTheory.GroupAlg.center_mem_span_classSums <;> assumption)
end

section

open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.rightInvariant_mul_eq_finprod_components : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ) (a : Γ → ℂ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ v g h, c v g = 1 → c v h = h → a (g * h) = a g * a h) → ∀ g, a g = ∏ᶠ v, a (c v g) := by
  first | exact @GlobalTheory.finprod_components_of_rightInvariant_mul | exact GlobalTheory.finprod_components_of_rightInvariant_mul | (intros; apply GlobalTheory.finprod_components_of_rightInvariant_mul <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  first | exact @GlobalTheory.OrbitCounting.counting_principle | exact GlobalTheory.OrbitCounting.counting_principle | (intros; apply GlobalTheory.OrbitCounting.counting_principle <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_equiv_finsupp_compl_prod_eq : ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  first | exact @GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | exact GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | (intros; apply GlobalTheory.finsupp_vanishing_on_equiv_compl_prod <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ) (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card → (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') → ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  first | exact @GlobalTheory.ph_a_basis | exact GlobalTheory.ph_a_basis | (intros; apply GlobalTheory.ph_a_basis <;> assumption)
end
