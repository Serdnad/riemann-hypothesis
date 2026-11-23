module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem level_iff (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N]
    [hc : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ)] (H : Subgroup (ZMod N)ˣ) :
    HasLevel E N H ↔ ∃ j : E →ₐ[ℚ] CyclotomicField N ℚ, ∀ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      (∀ x : E, τ (j x) = j x) ↔ IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ ∈ H := by
  constructor
  · rintro ⟨j, ζ, hζ, h⟩
    exact ⟨j, fun τ => h τ _ (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one)⟩
  · rintro ⟨j, h⟩
    have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
    refine ⟨j, _, hζ, fun τ u hu => ?_⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one,
      (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.ext_iff] at hu
    rw [← hu]
    exact h τ

private theorem change (E F K : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field K] [NumberField K]
    (M N : ℕ) [NeZero M] [NeZero N] [IsCyclotomicExtension {M} ℚ F] [IsCyclotomicExtension {N} ℚ K]
    (h : M ∣ N) (H : Subgroup (ZMod M)ˣ) :
    (∃ j : E →ₐ[ℚ] F, ∀ τ : F ≃ₐ[ℚ] F,
      (∀ x : E, τ (j x) = j x) ↔ IsCyclotomicExtension.Rat.galEquivZMod M F τ ∈ H) ↔
    (∃ j : E →ₐ[ℚ] K, ∀ τ : K ≃ₐ[ℚ] K,
      (∀ x : E, τ (j x) = j x) ↔
        IsCyclotomicExtension.Rat.galEquivZMod N K τ ∈ H.comap (ZMod.unitsMap h)) := by
  haveI : IsGalois ℚ F := IsCyclotomicExtension.isGalois {M} ℚ F
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  obtain ⟨c, hc⟩ := id h
  have hη : IsPrimitiveRoot (IsCyclotomicExtension.zeta N ℚ K ^ c) M :=
    (IsCyclotomicExtension.zeta_spec N ℚ K).pow (NeZero.pos N) (hc.trans (mul_comm _ _))
  let i : F →ₐ[ℚ] K := ((IsCyclotomicExtension.zeta_spec M ℚ F).embeddingsEquivPrimitiveRoots K
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))).symm ⟨_, (mem_primitiveRoots (NeZero.pos M)).2 hη⟩
  letI : Algebra F K := i.toRingHom.toAlgebra
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois ℚ F K
  haveI : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have hinj := (algebraMap F K).injective
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨i.comp j, fun τ => ?_⟩
    rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h τ, ← hj]
    refine forall_congr' fun x => ?_
    rw [← hinj.eq_iff, AlgEquiv.restrictNormal_commutes]
    rfl
  · rintro ⟨j, hj⟩
    have hr : ∀ x : E, ∃ y : F, algebraMap F K y = j x := by
      intro x
      have : j x ∈ Set.range (algebraMap F K) := by
        rw [IsGalois.mem_range_algebraMap_iff_fixed]
        intro σ
        refine (hj (σ.restrictScalars ℚ)).2 ?_ x
        have h1 : (σ.restrictScalars ℚ).restrictNormal F = 1 := by
          ext y
          apply hinj
          rw [AlgEquiv.restrictNormal_commutes]
          exact σ.commutes y
        rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h, h1, map_one]
        exact H.one_mem
      exact this
    choose f hf using hr
    let j0 : E →+* F :=
      { toFun := f
        map_one' := hinj (by simp [hf])
        map_mul' := fun x y => hinj (by simp [hf])
        map_zero' := hinj (by simp [hf])
        map_add' := fun x y => hinj (by simp [hf]) }
    refine ⟨j0.toRatAlgHom, fun τ => ?_⟩
    have h2 := hj (τ.liftNormal K)
    rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h,
      AlgEquiv.restrict_liftNormal] at h2
    rw [← h2]
    refine forall_congr' fun x => ?_
    rw [← hf x, ← hinj.eq_iff, ← τ.liftNormal_commutes K]
    rfl

theorem UpperTheory.V.Chr.levChange :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N], (Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ H : Subgroup (ZMod N)ˣ, HasLevel E N H) ∧
          ∀ (M : ℕ) [NeZero M] (h : M ∣ N) (H : Subgroup (ZMod M)ˣ), HasLevel E M H ↔ HasLevel E N (H.comap (ZMod.unitsMap h)) := by
  intro E _ _ N _
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  constructor
  · rintro ⟨j⟩
    refine ⟨j.fieldRange.fixingSubgroup.map
      (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom, (level_iff E N _).2 ⟨j, fun τ => ?_⟩⟩
    refine Iff.trans ?_ (Subgroup.mem_map_iff_mem (f := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom)
      (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).injective).symm
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · rintro h _ ⟨x, rfl⟩
      exact h x
    · intro h x
      exact h _ ⟨x, rfl⟩
  · intro M _ h H
    haveI : IsCyclotomicExtension {M} ℚ (CyclotomicField M ℚ) := CyclotomicField.isCyclotomicExtension M ℚ
    rw [level_iff, level_iff]
    exact change E _ _ M N h H
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem exists_primitiveRoot_of_isAlgClosure' (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] : ∃ ζ : Ω, IsPrimitiveRoot ζ N := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω N

private theorem cls_apply_root_of_unity_eq_pow (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : ζ ^ N = 1) :
    σ ζ = ζ ^ ((cls k Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp [NeZero.ne N] at hζ
  have ht : Units.mk0 ζ h0 ∈ rootsOfUnity N Ω := by
    rw [mem_rootsOfUnity]
    ext
    simpa using hζ
  obtain ⟨ξ, hξ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
  have := modularCyclotomicCharacter.spec Ω hξ.card_rootsOfUnity
    (MulSemiringAction.toRingAut (G k Ω) Ω σ) ht
  exact this

private theorem cls_eq_of_forall_root_of_unity_apply_eq_pow (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (u : (ZMod N)ˣ)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ (u : ZMod N).val) : cls k Ω N σ = u := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
  ext1
  refine (modularCyclotomicCharacter.unique Ω hζ.card_rootsOfUnity
    (MulSemiringAction.toRingAut (G k Ω) Ω σ) (c := (u : ZMod N)) ?_).symm
  intro t ht
  rw [mem_rootsOfUnity] at ht
  have ht' : (t : Ω) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  exact h t ht'

private theorem root_of_unity_pow_natCast_zmod_val {Ω : Type} [Field Ω] (N : ℕ) [NeZero N] (ζ : Ω) (hζ : ζ ^ N = 1)
    (b : ℕ) : ζ ^ ((b : ZMod N)).val = ζ ^ b := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div b N, pow_add, pow_mul, hζ, one_pow, mul_one]

private theorem cls_eq_one_of_fixes_primitiveRoot (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ N)
    (hσ : σ ζ = ζ) : cls k Ω N σ = 1 := by
  apply cls_eq_of_forall_root_of_unity_apply_eq_pow
  intro ξ hξ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have h1 := root_of_unity_pow_natCast_zmod_val N _ hξ 1
  rw [Nat.cast_one, pow_one] at h1
  rw [map_pow, hσ, Units.val_one, h1]

theorem UpperTheory.V.Chr.clsFacts :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (N : ℕ) [NeZero N],
          IsOpen ((cls k Ω N).ker : Set (G k Ω)) ∧ (∀ (M : ℕ) [NeZero M] (h : M ∣ N), (ZMod.unitsMap h).comp (cls k Ω N) = cls k Ω M) ∧
          (∀ (σ : G k Ω) (u : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ (u : ZMod N).val) → cls k Ω N σ = u) ∧
          (∀ σ : G k Ω, IsConjOm σ.toRingEquiv → cls k Ω N σ = -1) ∧
          ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := k) A ≤ (cls k Ω N).ker := by
  intro k Ω _ _ _ _ _ N _
  refine ⟨?_, ?_, fun σ u h => cls_eq_of_forall_root_of_unity_apply_eq_pow k Ω N σ u h, ?_, ?_⟩
  · obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
    haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
    have hi : IsIntegral k ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    haveI : FiniteDimensional k (IntermediateField.adjoin k {ζ}) :=
      IntermediateField.adjoin.finiteDimensional hi
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin k {ζ}))
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact cls_eq_one_of_fixes_primitiveRoot k Ω N σ ζ hζ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ ζ
      (IntermediateField.mem_adjoin_simple_self k ζ))
  · intro M _ hMN
    ext1 σ
    symm
    apply cls_eq_of_forall_root_of_unity_apply_eq_pow
    intro ζ hζ
    rw [MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.cast_eq_val, root_of_unity_pow_natCast_zmod_val M ζ hζ]
    obtain ⟨d, hd⟩ := hMN
    exact cls_apply_root_of_unity_eq_pow k Ω N σ ζ (by rw [hd, pow_mul, hζ, one_pow])
  · intro σ hσ
    obtain ⟨j, hj⟩ := hσ
    apply cls_eq_of_forall_root_of_unity_apply_eq_pow
    intro ζ hζ
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have h0 : ζ ≠ 0 := by
      rintro rfl
      simp [NeZero.ne N] at hζ
    have hval : ((-1 : (ZMod N)ˣ) : ZMod N) = ((N - 1 : ℕ) : ZMod N) := by
      rw [Units.val_neg, Units.val_one, Nat.cast_sub hN1, ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [hval, root_of_unity_pow_natCast_zmod_val N ζ hζ, pow_sub₀ ζ h0 hN1, hζ, pow_one, one_mul]
    apply j.injective
    have hjζ := hj ζ
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv] at hjζ
    rw [hjζ, map_inv₀]
    have hz : (j ζ) ^ N = 1 := by rw [← map_pow, hζ, map_one]
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne N)
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  · intro A hA σ hσ
    rw [MonoidHom.mem_ker]
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
    apply cls_eq_one_of_fixes_primitiveRoot k Ω N σ ζ hζ
    have hin : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := hσ.2
    by_contra hne
    have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
    set ξ := σ ζ * ζ⁻¹ with hξdef
    have hξN : ξ ^ N = 1 := by
      rw [hξdef, mul_pow, inv_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul, inv_one]
    have hξ1 : ξ ≠ 1 := by
      intro h
      apply hne
      rw [hξdef, mul_inv_eq_one₀ h0] at h
      exact h
    have hv1 : ∀ x : Ω, x ^ N = 1 → A.valuation x = 1 := by
      intro x hx
      have hp : A.valuation x ^ N = 1 := by rw [← map_pow, hx, map_one]
      exact (pow_eq_one_iff.1 hp).resolve_right (NeZero.ne N)
    have hsum : ∑ i ∈ Finset.range N, ξ ^ i = 0 := by
      have hg := geom_sum_mul ξ N
      rw [hξN, sub_self] at hg
      exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hξ1)
    have hNeq : (N : Ω) = (1 - ξ) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j := by
      rw [Finset.mul_sum]
      simp_rw [mul_neg_geom_sum]
      rw [Finset.sum_sub_distrib, hsum]
      simp
    have hξA : ξ ∈ A := (A.valuation_le_one_iff ξ).1 (hv1 ξ hξN).le
    have hSA : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j) ∈ A :=
      sum_mem fun i _ => sum_mem fun j _ => pow_mem hξA j
    have hS : A.valuation (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j) ≤ 1 :=
      (A.valuation_le_one_iff _).2 hSA
    have hdiff : σ ζ - ζ = -(ζ * (1 - ξ)) := by
      rw [hξdef]
      field_simp
      ring
    have hlt : A.valuation (1 - ξ) < 1 := by
      have := hin ζ (hv1 ζ hζ.pow_eq_one).le
      rw [hdiff, Valuation.map_neg, map_mul, hv1 ζ hζ.pow_eq_one, one_mul] at this
      exact this
    apply hA
    rw [hNeq, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hS) hlt
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.levGal :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), HasLevel E N H → IsAbelianGalois ℚ E ∧ Module.finrank ℚ E = H.index ∧
          ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra E Ω], galOf ℚ E Ω = levH ℚ Ω H ∧ (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := by
  intro E _ _ N _ H hlev
  obtain ⟨j, ζ, hζ, hj⟩ := hlev
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfs : KStar.TotallyRealRoots.fieldSubgroup N (CyclotomicField N ℚ) j.fieldRange = H := by
    ext u
    unfold KStar.TotallyRealRoots.fieldSubgroup
    rw [Subgroup.mem_map_equiv]
    set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm u with hτdef
    have hu : IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ = u := by
      rw [hτdef]
      exact MulEquiv.apply_symm_apply _ u
    have hτ : τ ζ = ζ ^ (u : ZMod N).val := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, hu]
    rw [← hj τ u hτ, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x
      exact h (j x) ⟨x, rfl⟩
    · rintro h _ ⟨x, rfl⟩
      exact h x
  have hfr : Module.finrank ℚ j.fieldRange = Module.finrank ℚ E := by
    rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    rfl
  have hfin : Module.finrank ℚ E = H.index := by
    rw [← hfr, IntermediateField.finrank_eq_fixingSubgroup_index, ← hfs]
    unfold KStar.TotallyRealRoots.fieldSubgroup
    exact (Subgroup.index_map_of_bijective (MulEquiv.bijective _) _).symm
  refine ⟨IsAbelianGalois.of_algHom j, hfin, ?_⟩
  intro Ω _ _ _ _
  haveI : IsScalarTower ℚ E Ω := inferInstance
  haveI : IsAlgClosure E Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  have heq : galOf ℚ E Ω = levH ℚ Ω H := by
    ext σ
    rw [mem_galOf]
    unfold levH
    rw [Subgroup.mem_comap, ← hfs]
    exact LDataCardLeFinrank.classFix E Ω N (CyclotomicField N ℚ) j σ.toRingEquiv (cls ℚ Ω N σ)
      (fun z hz => cls_spec N σ z hz)
  obtain ⟨-, hopen, hidx⟩ := galEmbTop ℚ E Ω
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq, hidx, hfin]
  · rw [← heq]
    exact hopen
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.eigV :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)) [U.Normal],
          IsOpen (U : Set (G k Ω)) → U ≤ ψ.ker → ¬ l ∣ U.index → eigL l e U ψ = V l e ψ := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U _ hU hker hind
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l O
  have hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    have hk : (ψ⁻¹).ker = ψ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hk]
    exact Subgroup.isOpen_mono hker hU
  have hcont := (contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen
  unfold eigL V VS
  exact selEigBase O (G k Ω) (QO l O) _ (rho l e ψ) ψ (tw_apply l e ψ) hcont U ⊤ le_top
    (fun u hu => hker hu) (hU.preimage continuous_subtype_val)
    (by rw [Subgroup.relIndex_top_right]; exact hunit _ hind) _ (conjStable_shaFam k Ω l)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem fact_le_log {l e t : ℕ} (hl : l.Prime) (he : e ≠ 0) (het : e < t) :
    (e.factorization l : ℝ) * Real.log 2 ≤ Real.log t := by
  have h2 : 2 ^ e.factorization l ≤ e :=
    le_trans (Nat.pow_le_pow_left hl.two_le _) (Nat.ordProj_le l he)
  rw [← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h2.trans het.le

private theorem nu_sum (l N : ℕ) (hl : l.Prime) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t →
    ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ C * (t * Real.log t) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨((max (N.factorization l) (if l = 2 then 2 else 1) : ℕ) + 1 : ℝ) / Real.log 2,
    div_nonneg (by positivity) hlog2.le, ?_⟩
  intro t ht
  set M : ℕ := max (N.factorization l) (if l = 2 then 2 else 1) with hM
  have hlogt : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hterm : ∀ e ∈ Finset.Ico 1 t,
      (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ ((M : ℝ) + 1) / Real.log 2 * Real.log t := by
    intro e he
    rw [Finset.mem_Ico] at he
    have hv := fact_le_log hl (by omega) he.2
    have hnbN : LDataCardLeFinrank.nuBound l N e ≤ M + e.factorization l := by
      unfold LDataCardLeFinrank.nuBound
      rw [hM]
      split_ifs <;> first | exact le_refl _ | exact Nat.zero_le _
    have hnb : (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ (M : ℝ) + e.factorization l := by
      exact_mod_cast hnbN
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    calc (LDataCardLeFinrank.nuBound l N e : ℝ) * Real.log 2
        ≤ ((M : ℝ) + e.factorization l) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hnb hlog2.le
      _ = (M : ℝ) * Real.log 2 + (e.factorization l : ℝ) * Real.log 2 := by ring
      _ ≤ (M : ℝ) * Real.log t + Real.log t :=
          add_le_add (mul_le_mul_of_nonneg_left hlogt (by positivity)) hv
      _ = ((M : ℝ) + 1) * Real.log t := by ring
  have hC : 0 ≤ ((M : ℝ) + 1) / Real.log 2 * Real.log t :=
    mul_nonneg (div_nonneg (by positivity) hlog2.le) (hlog2.le.trans hlogt)
  calc ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ)
      ≤ ∑ e ∈ Finset.Ico 1 t, ((M : ℝ) + 1) / Real.log 2 * Real.log t := Finset.sum_le_sum hterm
    _ = ((t - 1 : ℕ) : ℝ) * (((M : ℝ) + 1) / Real.log 2 * Real.log t) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (t : ℝ) * (((M : ℝ) + 1) / Real.log 2 * Real.log t) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le t 1) hC
    _ = ((M : ℝ) + 1) / Real.log 2 * (t * Real.log t) := by ring

theorem UpperTheory.V.Chr.nuSum :
    (∀ l N : ℕ, l.Prime → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t → ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ C * (t * Real.log t)) ∧
          ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (f a : ℕ → ℕ∞) (b : ℕ → ℕ) (t : ℕ) (B B' : ℝ), (∀ e, 0 < e → e < t → a e ≠ ⊤ ∧ f e ≤ a e * eO l O + (b e : ℕ∞) * eO l O) →
            ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) ≤ B → ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) ≤ B' → SumLe l O f t (B + B') := by
  refine ⟨nu_sum, ?_⟩
  intro l _ O _ _ _ _ _ f a b t B B' h hB hB'
  obtain ⟨-, -, -, -, -, hne0, hle, -, -⟩ := dvrFacts l O
  have hfin : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hne0 (by rw [← hn]; rfl)
    exact_mod_cast this
  apply SumLe.mono l (g := fun e => a e * eO l O + (b e : ℕ∞) * eO l O)
  · refine ⟨fun e h0 ht => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (h e h0 ht).1
      show a e * eO l O + (b e : ℕ∞) * eO l O ≠ ⊤
      rw [← hm, ← hn]
      exact_mod_cast ENat.coe_ne_top (m * n + b e * n)
    · calc ∑ e ∈ Finset.Ico 1 t, nrm l O (a e * eO l O + (b e : ℕ∞) * eO l O)
          = ∑ e ∈ Finset.Ico 1 t, (((a e).toNat : ℝ) + (b e : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [Finset.mem_Ico] at he
            obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (h e (by omega) he.2).1
            unfold nrm
            rw [← hm, ← hn]
            rw [show (m : ℕ∞) * (n : ℕ∞) + ((b e : ℕ) : ℕ∞) * (n : ℕ∞) = ((m * n + b e * n : ℕ) : ℕ∞) by
              push_cast; rfl]
            rw [ENat.toNat_coe, ENat.toNat_coe, ENat.toNat_coe]
            push_cast
            field_simp
        _ = ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) + ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) :=
            Finset.sum_add_distrib
        _ ≤ B + B' := add_le_add hB hB'
  · intro e h0 ht
    exact (h e h0 ht).2
end
