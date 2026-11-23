module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.WildAdditive

theorem not_isUnit_natCast (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Nontrivial O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : ¬ IsUnit (l : O) := by
  rintro ⟨u, hu⟩
  have htop : (⊤ : Submodule ℤ_[l] O) ≤ IsLocalRing.maximalIdeal ℤ_[l] • ⊤ := by
    intro x _
    have hx : x = (l : ℤ_[l]) • (((u⁻¹ : Oˣ) : O) * x) := by
      rw [Algebra.smul_def, map_natCast, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hx]
    have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span rfl
    exact Submodule.smul_mem_smul hl Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) ⊤
    (Module.finite_def.mp inferInstance) htop (IsLocalRing.maximalIdeal_le_jacobson _)
  exact top_ne_bot hbot

theorem exists_pow_nsmul_eq_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (x : KOG O 1) :
    ∃ n : ℕ, l ^ n • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) (y 0)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O

  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_natCast l O)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton] at hl

  obtain ⟨k, hk⟩ :=
    IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  obtain ⟨c, hc⟩ := hk.dvd.trans (pow_dvd_pow_of_dvd hl k)
  refine ⟨k, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  unfold stdG
  rw [LinearMap.mem_range]
  refine ⟨fun _ => c * a, ?_⟩
  funext j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  have hb' : algebraMap O (FractionRing O) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hlk : ((l ^ k : ℕ) : FractionRing O) =
      algebraMap O (FractionRing O) b * algebraMap O (FractionRing O) c := by
    rw [← map_mul, ← hc, map_pow, map_natCast, Nat.cast_pow]
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, Pi.smul_apply,
    nsmul_eq_mul, ← hab]
  rw [hlk, map_mul]
  field_simp

theorem eq_zero_of_wild (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (l : ℕ)
    (hl : l.Prime) (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (hA : IsPlaceOver A v)
    (M : Type) [AddCommGroup M] (f : G E Ω → M) (hf : IsLocallyConstant f)
    (I : Subgroup (G E Ω)) (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b)
    (hM : ∀ x : M, ∃ n : ℕ, l ^ n • x = 0) (σ : G E Ω) (hI : σ ∈ I)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : f σ = 0 := by
  classical
  have hI1 : (1 : G E Ω) ∈ I := I.one_mem
  have hf1 : f 1 = 0 := by
    have h := hadd 1 hI1 1 hI1
    rw [one_mul] at h
    simpa using h
  have hpow : ∀ n : ℕ, f (σ ^ n) = n • f σ := by
    intro n
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hadd _ (I.pow_mem hI n) _ hI, ih, succ_nsmul]
  have hU : f ⁻¹' {f 1} ∈ nhds (1 : G E Ω) := (hf.isOpen_fiber (f 1)).mem_nhds rfl
  obtain ⟨L, hLfin, hLsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hU
  have hUo : IsOpen (L.fixingSubgroup : Set (G E Ω)) := L.fixingSubgroup_isOpen
  have : Finite (G E Ω ⧸ L.fixingSubgroup) := L.fixingSubgroup.quotient_finite_of_isOpen hUo
  have : L.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hd : L.fixingSubgroup.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hσU : σ ^ L.fixingSubgroup.normalCore.index ∈ L.fixingSubgroup :=
    L.fixingSubgroup.normalCore_le (L.fixingSubgroup.normalCore.pow_index_mem σ)
  obtain ⟨a, d, hdl, hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd l hl.ne_one

  have hl1 : A.valuation (l : Ω) = 1 := by
    have h1 := (hA (l : 𝓞 E)).not.mpr hlv
    have h2 := A.valuation_le_one (l : A)
    simp only [map_natCast] at h1 h2
    exact le_antisymm h2 (not_lt.mp h1)
  have hk : ¬ A.valuation ((l ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hl1, one_pow]
    exact lt_irrefl _
  have hτ : ∀ y : Ω, y ≠ 0 → A.valuation ((σ ^ d) y / y - 1) < 1 :=
    GlobalTheory.WildInertiaChar.wild_pow A σ hσ d
  have hτU : σ ^ d ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ d) hτ (l ^ a) hk x
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσU
    rw [← pow_mul, mul_comm, ← hdec]
    exact hσU x hx
  have hd0 : d • f σ = 0 := by
    rw [← hpow d]
    have := hLsub hτU
    simpa [hf1] using this
  obtain ⟨n, hn⟩ := hM (f σ)
  have hcop : IsCoprime ((l ^ n : ℕ) : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hl).mpr hdl))
  obtain ⟨u, w, huw⟩ := hcop
  calc f σ = (1 : ℤ) • f σ := (one_zsmul _).symm
    _ = (u * ((l ^ n : ℕ) : ℤ) + w * (d : ℤ)) • f σ := by rw [huw]
    _ = u • ((l ^ n) • f σ) + w • (d • f σ) := by
        rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = 0 := by rw [hn, hd0, smul_zero, smul_zero, add_zero]

private theorem valuation_apply_eq_of_valuation_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  by_cases hy : y = 0
  · simp [hy]
  · have h1 : A.valuation (σ y / y) = 1 := by
      have := Valuation.map_one_add_of_lt A.valuation (hσ y hy)
      simpa using this
    rw [← div_mul_cancel₀ (σ y) hy, map_mul, h1, one_mul]

private theorem mem_ine_of_valuation_div_sub_one_lt_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  rw [mem_Ine]
  let : MulAction (G E Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
  refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← ValuationSubring.valuation_le_one_iff,
      ← ValuationSubring.valuation_le_one_iff]
    have key : A.valuation x = A.valuation (σ⁻¹ • x) := by
      have h := valuation_apply_eq_of_valuation_div_sub_one_lt A σ hσ (σ⁻¹ • x)
      rwa [← AlgEquiv.smul_def, smul_inv_smul] at h
    rw [key]
  · intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · have h3 : σ x - x = x * (σ x / x - 1) := by
        rw [mul_sub, mul_div_cancel₀ _ h0, mul_one]
      rw [h3, map_mul]
      calc _ ≤ 1 * A.valuation (σ x / x - 1) := by gcongr
        _ < 1 := by rw [one_mul]; exact hσ x h0

theorem main : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ f : GE D.nd → KOG (D.nd.O i) 1, IsLocallyConstant f → (∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f (a * b) = f a + f b) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), f σ = 0 := by
  intro D i v hv f hf hadd σ hσ
  exact eq_zero_of_wild D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.l i) (D.nd.lPrime i).out hv
    (D.nd.plOm.2 v) (KOG (D.nd.O i) 1) f hf (Ine (F := D.host.E) (D.nd.plOm.1 v)) hadd
    (exists_pow_nsmul_eq_zero (D.nd.l i) (D.nd.O i)) σ (mem_ine_of_valuation_div_sub_one_lt_one _ σ hσ) hσ

end GlobalTheory.WildAdditive
end

section

namespace GlobalTheory

open IsDiscreteValuationRing

theorem exists_toNat_addVal_algebraMap_eq_mul (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [Algebra O O'] [IsLocalHom (algebraMap O O')] (hinj : Function.Injective (algebraMap O O')) :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ x : O,
      (addVal O' (algebraMap O O' x)).toNat = e * (addVal O x).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : algebraMap O O' ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero (hinj (by simpa using h))
  have h1 : addVal O' (algebraMap O O' ϖ) ≠ ⊤ := by
    rwa [Ne, addVal_eq_top_iff]
  have h2 : addVal O' (algebraMap O O' ϖ) ≠ 0 := by
    rw [Ne, addVal_eq_zero_iff]
    intro h
    exact hϖ.not_isUnit (IsLocalHom.map_nonunit _ h)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 h1
  refine ⟨e, ?_, fun x => ?_⟩
  · rintro rfl
    exact h2 (by rw [← he]; rfl)
  · by_cases hx : x = 0
    · subst hx
      simp
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
      have hv : addVal O x = n := addVal_def x u hϖ n hu
      have hu0 : addVal O' (algebraMap O O' (u : O)) = 0 := by
        rw [addVal_eq_zero_iff]
        exact u.isUnit.map _
      have hv' : addVal O' (algebraMap O O' x) = ((e * n : ℕ) : ℕ∞) := by
        rw [hu, map_mul, map_pow, addVal_mul, addVal_pow, hu0, ← he, zero_add, nsmul_eq_mul]
        push_cast
        ring
      rw [hv, hv', ENat.toNat_natCast, ENat.toNat_natCast]

theorem nval_algebraMap_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (l : ℕ) (x : O), Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  intro O _ _ _ O' _ _ _ _ _ hinj l x
  obtain ⟨e, he, h⟩ := exists_toNat_addVal_algebraMap_eq_mul O O' hinj
  have hl : (l : O') = algebraMap O O' (l : O) := (map_natCast _ l).symm
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [hl, h, h]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

end GlobalTheory
end

section

namespace GlobalTheory

open Polynomial IsDiscreteValuationRing

theorem associated_primitiveRoot_sub_one_pow_totient_prime_pow {O : Type} [CommRing O] [IsDomain O]
    {l k : ℕ} (hl : l.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ (l ^ (k + 1))) :
    Associated ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) (l : O) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := O) (p := l) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  rw [← h1, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun μ hμ => ?_
  have hμ' : IsPrimitiveRoot μ (l ^ (k + 1)) :=
    (mem_primitiveRoots (pow_pos hl.pos _)).1 hμ
  obtain ⟨i, -, hi, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ'
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

theorem nval_primitiveRoot_prime_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  intro O _ _ _ l k hl hk hl0 hlu ζ hζ
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hass := associated_primitiveRoot_sub_one_pow_totient_prime_pow hl hζ
  have hφ : 0 < Nat.totient (l ^ (k + 1)) := Nat.totient_pos.2 (pow_pos hl.pos _)
  have hne : ζ - 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hφ.ne'] at hass
    exact hl0 ((associated_zero_iff_eq_zero _).1 hass.symm)
  refine ⟨hne, ?_⟩
  have hv : addVal O ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) = addVal O (l : O) :=
    (addVal_eq_iff_associated _ _).2 hass
  rw [addVal_pow] at hv
  have ht : addVal O (ζ - 1) ≠ ⊤ := fun h => hne (addVal_eq_top_iff.1 h)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 ht
  have hl1 : addVal O (l : O) ≠ 0 := fun h => hlu (addVal_eq_zero_iff.1 h)
  have hv' : addVal O (l : O) = ((Nat.totient (l ^ (k + 1)) * a : ℕ) : ℕ∞) := by
    rw [← hv, ← ha]; simp
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hl1
    rw [hv']; simp
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [hv', ← ha, ENat.toNat_coe, ENat.toNat_coe]
  have : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have : (Nat.totient (l ^ (k + 1)) : ℝ) ≠ 0 := by exact_mod_cast hφ.ne'
  push_cast
  field_simp

end GlobalTheory
end

section

namespace GlobalTheory

open Formalism.MainNotions.BlochKatoReduction Formalism.BasicNotions

theorem matAct_comp_linear {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (f : M →ₗ[R] N)
    (v : Fin n → M) : matAct (M := N) A (fun i => f (v i)) = fun i => f (matAct (M := M) A v i) := by
  funext i

  simp [matAct, map_sum, map_smul]

theorem matAct_self_apply {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) : matAct (M := R) A v = A.mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

private theorem matAct_fractionRing {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (v : Fin n → FractionRing O) :
    matAct (M := FractionRing O) A v = (A.map (algebraMap O (FractionRing O))).mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem matAct_fraction_bijective {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Function.Bijective (matAct (M := FractionRing O) A) := by
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = algebraMap O (FractionRing O) A.det := by
    rw [hB, RingHom.map_det]; rfl
  have hU : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det, hd, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr h
  have hf : ⇑(matAct (M := FractionRing O) A) = B.mulVec := funext (matAct_fractionRing A)
  rw [hf]
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hU, Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩

theorem nonempty_coker_equiv_ker_matAct {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Nonempty (((Fin n → O) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[O]
      LinearMap.ker (matAct (M := KmodO O) A)) := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let e : (Fin n → FractionRing O) ≃ₗ[O] (Fin n → FractionRing O) :=
    LinearEquiv.ofBijective (matAct (M := FractionRing O) A) (matAct_fraction_bijective A h)
  have he : ∀ x, e x = matAct (M := FractionRing O) A x := fun x => rfl
  have hAι : ∀ y, matAct (M := FractionRing O) A (ι y) = ι (A.mulVec y) := by
    intro y
    have key := matAct_comp_linear A (Algebra.linearMap O (FractionRing O)) y
    rw [matAct_self_apply] at key
    exact key
  have hAπ : ∀ x, matAct (M := KmodO O) A (π x) = π (matAct (M := FractionRing O) A x) :=
    fun x => matAct_comp_linear A (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ x
  have hπι : ∀ y, π (ι y) = 0 := by
    intro y
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y i, rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b hab
    funext i
    exact IsFractionRing.injective O (FractionRing O) (congrFun hab i)
  have hlift : ∀ x, π x = 0 → ∃ y, ι y = x := by
    intro x hx
    have hmem : ∀ i, ∃ a : O, algebraMap O (FractionRing O) a = x i := by
      intro i
      obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 (congrFun hx i)
      exact ⟨a, ha⟩
    choose y hy using hmem
    exact ⟨y, funext hy⟩
  let φ0 : (Fin n → O) →ₗ[O] (Fin n → KmodO O) := π ∘ₗ e.symm.toLinearMap ∘ₗ ι
  have hφ0 : ∀ y, φ0 y ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro y
    rw [LinearMap.mem_ker]
    show matAct (M := KmodO O) A (π (e.symm (ι y))) = 0
    rw [hAπ, ← he, e.apply_symm_apply, hπι]
  let φ := φ0.codRestrict _ hφ0
  have hφ : ∀ y, (φ y : Fin n → KmodO O) = π (e.symm (ι y)) := fun y => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    have hpre : ∀ i, ∃ k : FractionRing O, Submodule.Quotient.mk k = x i :=
      fun i => Submodule.Quotient.mk_surjective _ (x i)
    choose k hk using hpre
    have hπk : π k = x := funext hk
    obtain ⟨y, hy⟩ := hlift (matAct (M := FractionRing O) A k) (by
      rw [← hAπ, hπk]
      exact hx)
    refine ⟨y, Subtype.ext ?_⟩
    rw [hφ, hy, ← he, e.symm_apply_apply, hπk]
  have hkerφ : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      rw [hφ, Matrix.mulVecLin_apply, ← hAι, ← he, e.symm_apply_apply, hπι]
      rfl
    · intro hy
      have h0 : π (e.symm (ι y)) = 0 := by
        rw [← hφ, hy]
        rfl
      obtain ⟨z, hz⟩ := hlift _ h0
      refine ⟨z, hιinj ?_⟩
      rw [Matrix.mulVecLin_apply, ← hAι, hz, ← he, e.apply_symm_apply]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerφ).trans (φ.quotKerEquivOfSurjective hsurj)⟩

theorem length_ker_matAct_eq_top {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (h : A.det = 0) :
    Module.length O (LinearMap.ker (matAct (M := KmodO O) A)) = ⊤ := by
  classical
  by_contra hne
  have hfl := Module.length_ne_top_iff.mp hne
  have : IsNoetherian O (LinearMap.ker (matAct (M := KmodO O) A)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = 0 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨v, hv0, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hh
    exact hv0 (funext fun i => by
      by_contra hi
      exact hh ⟨i, hi⟩)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let g0 : FractionRing O →ₗ[O] (Fin n → KmodO O) :=
    π ∘ₗ LinearMap.pi (fun i => LinearMap.mulRight O (v i))
  have hg0 : ∀ t, g0 t = π (t • v) := fun t => rfl
  have hg0mem : ∀ t, g0 t ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro t
    rw [LinearMap.mem_ker, hg0]
    refine (matAct_comp_linear A
      (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (t • v)).trans ?_
    rw [matAct_fractionRing, ← hB, Matrix.mulVec_smul, hBv, smul_zero]
    funext i
    simp
  let g := g0.codRestrict _ hg0mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  have hle : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • LinearMap.range g := by
    rintro _ ⟨t, rfl⟩
    have ht : t = ϖ • (t / algebraMap O (FractionRing O) ϖ) := by
      rw [Algebra.smul_def]
      field_simp
    rw [ht, map_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) ⟨_, rfl⟩
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O)
    (LinearMap.range g) (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  set t := (algebraMap O (FractionRing O) ϖ * v i0)⁻¹ with ht
  have hgt : g t = 0 := by
    have hm : g t ∈ LinearMap.range g := ⟨t, rfl⟩
    rw [hbot] at hm
    exact (Submodule.mem_bot O).mp hm
  have hcomp : π (t • v) i0 = 0 := by
    rw [← hg0]
    exact congrFun (congrArg Subtype.val hgt) i0
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hcomp
  have ha' : algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) ϖ = 1 := by
    have h1 : algebraMap O (FractionRing O) a = t * v i0 := ha
    rw [h1, ht]
    field_simp
  rw [← map_mul, ← map_one (algebraMap O (FractionRing O))] at ha'
  have hmul : a * ϖ = 1 := IsFractionRing.injective O (FractionRing O) ha'
  have hunit : IsUnit ϖ := ⟨⟨ϖ, a, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩
  exact hϖ.not_isUnit hunit

theorem length_ker_matAct_kmod_eq_addVal_det :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : ℕ)
      (Φ : Matrix (Fin a) (Fin a) O),
      Module.length O (LinearMap.ker (Formalism.MainNotions.BlochKatoReduction.matAct (M := Formalism.BasicNotions.KmodO O) Φ)) =
        IsDiscreteValuationRing.addVal O Φ.det := by
  intro O _ _ _ a Φ
  by_cases h : Φ.det = 0
  · rw [length_ker_matAct_eq_top Φ h, h, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨e⟩ := nonempty_coker_equiv_ker_matAct Φ h
    rw [← e.length_eq]
    exact RelativeLengthSpanDet.length_coker Φ

end GlobalTheory
end
