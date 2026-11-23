module

public import GroundTheory.LocalFields.LocalAxiomDictionary
public import GroundTheory.LocalFields.MaximalUnramified
public import Mathlib.FieldTheory.Galois.Profinite
public import GroundTheory.LocalFields.Bundle007
public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.LocalFields.SeparableClosureValuation
public import GroundTheory.LocalFields.PadicLogSeries
public import Mathlib.Analysis.Complex.Circle
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import GroundTheory.LocalFields.LocalFourierHaar
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.PowerSeries.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Valuation

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def ordUnitsHom : Kˣ →* Multiplicative ℤ̂ where
  toFun x := Multiplicative.ofAdd ((ord (x : K) : ℤ) : ℤ̂)
  map_one' := by
    rw [Units.val_one, ord_one, Int.cast_zero, ofAdd_zero]
  map_mul' x y := by
    rw [Units.val_mul, ord_mul x.ne_zero y.ne_zero, Int.cast_add, ofAdd_add]

@[simp]
theorem toAdd_ordUnitsHom (x : Kˣ) :
    (ordUnitsHom K x).toAdd = ((ord (x : K) : ℤ) : ℤ̂) :=
  rfl


variable {K} in
theorem exists_ordUnitsHom_eq (n : ℤ) :
    ∃ x : Kˣ, ordUnitsHom K x = Multiplicative.ofAdd (n : ℤ̂) := by
  obtain ⟨x, hx, h⟩ := exists_ord_eq K n
  refine ⟨Units.mk0 x hx, Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_ordUnitsHom, Units.val_mk0, h, toAdd_ofAdd]

end Valuation

section Data

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def localValuation : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Multiplicative ℤ̂ :=
  (ordUnitsHom K).comp baseUnitsEquiv.toMonoidHom

theorem localValuation_apply (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    localValuation K Ω a = ordUnitsHom K (baseUnitsEquiv a) :=
  rfl

variable {K Ω}

theorem range_localValuation_comp_norm_of_eq (H : Subgroup (Ω ≃ₐ[K] Ω))
    [(H.subgroupOf ⊤).FiniteIndex] (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hL : L.fixingSubgroup = H) :
    ((localValuation K Ω).comp (norm Ωˣ ⊤ H)).range =
      (localValuation K Ω).range.map (powMonoidHom (inertiaDegree (unramifiedDegree K Ω) H)) := by
  subst hL
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have hsc : IsSepClosed Ω := IsSepClosure.sep_closed K
  rw [inertiaDegree_unramifiedDegree_fixingSubgroup]
  have key : ∀ u : Lˣ, ordUnitsHom K (normUnits K L u) =
      Multiplicative.ofAdd (((((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) : ℤ) * ord (u : L) : ℤ) : ℤ̂) := fun u => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ordUnitsHom, coe_normUnits, ord_norm, toAdd_ofAdd]
  ext z
  simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply, powMonoidHom_apply]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) (ord ((fixedModuleUnitsEquiv L a : Lˣ) : L))
    refine ⟨_, ⟨baseUnitsEquiv.symm x, rfl⟩, ?_⟩
    rw [localValuation_apply, localValuation_apply, MulEquiv.apply_symm_apply, hx,
      baseUnitsEquiv_norm, key]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨y, hy, hy'⟩ := exists_ord_eq L (ord ((baseUnitsEquiv b : Kˣ) : K))
    refine ⟨(fixedModuleUnitsEquiv L).symm (Units.mk0 y hy), ?_⟩
    rw [localValuation_apply, localValuation_apply, baseUnitsEquiv_norm, MulEquiv.apply_symm_apply,
      key, Units.val_mk0, hy']
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ordUnitsHom, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]

theorem intCast_mem_range_localValuation (n : ℤ) :
    Multiplicative.ofAdd (n : ℤ̂) ∈ (localValuation K Ω).range := by
  obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) n
  exact ⟨baseUnitsEquiv.symm x, by rw [localValuation_apply, MulEquiv.apply_symm_apply, hx]⟩

variable (K Ω)

noncomputable def localClassFieldData : ClassFieldData (Ω ≃ₐ[K] Ω) Ωˣ where
  deg := unramifiedDegree K Ω
  continuous_deg := unramifiedDegree_spec.1
  surjective_deg := unramifiedDegree_spec.2.1
  val := localValuation K Ω
  intCast_mem_range_val := intCast_mem_range_localValuation
  exists_eq_intCast_add_nsmul n _ a := by
    refine ⟨ord ((baseUnitsEquiv a : Kˣ) : K), 1, ?_⟩
    rw [map_one, toAdd_one, smul_zero, add_zero]
    rfl
  range_val_comp_norm U :=
    range_localValuation_comp_norm_of_eq (U : Subgroup (Ω ≃ₐ[K] Ω))
      (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
      (fixingSubgroup_fixedField_openSubgroup U)

@[simp]
theorem localClassFieldData_deg : (localClassFieldData K Ω).deg = unramifiedDegree K Ω :=
  rfl

@[simp]
theorem localClassFieldData_val : (localClassFieldData K Ω).val = localValuation K Ω :=
  rfl

end Data

section Axiom

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem natCard_tate_of_isCyclic (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) [(L'.subgroupOf K').Normal]
    [(L'.subgroupOf K').FiniteIndex] (E F : IntermediateField K Ω) [FiniteDimensional K E]
    [FiniteDimensional K F] (hEF : E ≤ F) (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
    (hcyc : IsCyclic (K' ⧸ L'.subgroupOf K')) :
    Nat.card (tateZero Ωˣ K' L') = L'.relIndex K' ∧ Nat.card (tateNegOne Ωˣ K' L') = 1 := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  have := normal_extendScalars K' L' hEF hK hL
  have := finiteDimensional_extendScalars hEF
  have : IsGalois E (IntermediateField.extendScalars hEF) :=
    isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  let T := galoisTateModel K' L' hEF hK hL
  have : IsCyclic (IntermediateField.extendScalars hEF ≃ₐ[E] IntermediateField.extendScalars hEF) :=
    isCyclic_of_surjective T.quotientEquiv.toMonoidHom T.quotientEquiv.surjective
  refine ⟨?_, ?_⟩
  · rw [T.natCard_tateZero, natCard_tateZero_units, T.relIndex_eq_natCard,
      IsGalois.card_aut_eq_finrank]
  · rw [T.natCard_tateNegOne, natCard_tateNegOne_units]


variable (K Ω) in
theorem classFieldAxiom_units : ClassFieldAxiom (Ω ≃ₐ[K] Ω) Ωˣ := by
  intro U V hVU _ hcyc
  exact natCard_tate_of_isCyclic (U : Subgroup (Ω ≃ₐ[K] Ω)) (V : Subgroup (Ω ≃ₐ[K] Ω))
    (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField_antitone hVU) (fixingSubgroup_fixedField_openSubgroup U)
    (fixingSubgroup_fixedField_openSubgroup V) hcyc

end Axiom

section Theory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def localClassFieldTheory : ClassFieldTheory (Ω ≃ₐ[K] Ω) Ωˣ where
  toClassFieldData := localClassFieldData K Ω
  isDiscreteModule := isDiscreteModule_units
  classFieldAxiom := classFieldAxiom_units K Ω

@[simp]
theorem localClassFieldTheory_deg : (localClassFieldTheory K Ω).deg = unramifiedDegree K Ω :=
  rfl

theorem localClassFieldTheory_val_apply (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    ((localClassFieldTheory K Ω).val a).toAdd = ((ord ((baseUnitsEquiv a : Kˣ) : K) : ℤ) : ℤ̂) :=
  rfl

end Theory

end GroundTheory.LocalField
end

section

noncomputable section

open IntermediateField Topology Filter

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.LocalField.Abstract

namespace FormalGroup

section UnramifiedTower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]


variable (K Ω) in
def unramifiedTowerRoot (k : ℕ) : Ω :=
  Classical.choose (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

theorem isPrimitiveRoot_unramifiedTowerRoot (k : ℕ) :
    IsPrimitiveRoot (unramifiedTowerRoot K Ω k) (Nat.card 𝓀[K] ^ (k + 1).factorial - 1) := by
  unfold unramifiedTowerRoot
  exact Classical.choose_spec (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))


variable (K Ω) in
def unramifiedTower (k : ℕ) : IntermediateField K Ω := K⟮unramifiedTowerRoot K Ω k⟯

theorem isUnramifiedSubextension_unramifiedTower (k : ℕ) :
    IsUnramifiedSubextension (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).1

theorem finrank_unramifiedTower (k : ℕ) :
    Module.finrank K (unramifiedTower K Ω k) = (k + 1).factorial :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).2

theorem le_unramifiedTower_of_isUnramifiedSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {k : ℕ} (hk : Module.finrank K E ≤ k + 1) :
    E ≤ unramifiedTower K Ω k := by
  have := hE.1
  exact hE.le_adjoin (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial Module.finrank_pos hk) (isPrimitiveRoot_unramifiedTowerRoot k)

theorem unramifiedTower_le_maximalUnramifiedExtension (k : ℕ) :
    unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_unramifiedTower k).le_maximalUnramifiedExtension

theorem exists_mem_unramifiedTower {x : Ω} (hx : x ∈ maximalUnramifiedExtension K Ω) :
    ∃ k, x ∈ unramifiedTower K Ω k := by
  obtain ⟨E, hE, hxE⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  exact ⟨Module.finrank K E, le_unramifiedTower_of_isUnramifiedSubextension hE (Nat.le_succ _) hxE⟩

instance (k : ℕ) : IsGalois K (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_unramifiedTower k).isGalois

end UnramifiedTower

section MaxUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}


variable [IsGalois K Ω]

end MaxUnramified

end FormalGroup

end GroundTheory.LocalField
end
end

section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Basis

theorem hasBasis_nhds_zero_valBall :
    (𝓝 (0 : K)).HasBasis (fun _ : ℤ => True) (fun n => (valBall (K := K) n : Set K)) := by
  have hballs := tendsto_zero_iff_valBall.mp (tendsto_id (x := 𝓝 (0 : K)))
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨n, _, hn⟩ => Filter.mem_of_superset (hballs n) hn⟩⟩
  by_contra h
  have h' : ∀ n : ℤ, ¬ (valBall (K := K) n : Set K) ⊆ t := fun n hn => h ⟨n, trivial, hn⟩
  have hex : ∀ k : ℕ, ∃ x : K, x ∈ valBall (K := K) k ∧ x ∉ t := fun k => by
    have := h' k
    rw [Set.not_subset] at this
    exact this
  choose x hx hxt using hex
  have hlim : Tendsto x atTop (𝓝 0) := by
    rw [tendsto_zero_iff_valBall]
    intro N
    filter_upwards [eventually_ge_atTop N.toNat] with k hk
    have hval : normalizedValuation K (x k) ≤ WithZero.exp (-(k : ℤ)) := hx k
    exact hval.trans (WithZero.exp_le_exp.mpr (by omega))
  obtain ⟨k, hk⟩ := (hlim.eventually ht).exists
  exact hxt k hk

end Basis

section Characters


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem eq_one_of_forall_norm_sub_one_lt (χ : AddChar K Circle) (H : AddSubgroup K)
    (h : ∀ x ∈ H, ‖(χ x : ℂ) - 1‖ < 1 / 2) {x : K} (hx : x ∈ H) : χ x = 1 := by
  have := GroundTheory.Global.eq_one_of_sq_mem (s := (fun y => (χ y : ℂ)) '' (H : Set K)) ?_ ?_
    ⟨x, hx, rfl⟩
  · exact Circle.coe_eq_one.mp this
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨y + y, H.add_mem hy hy, ?_⟩
    simp [AddChar.map_add_eq_mul, sq]
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy

theorem setOf_norm_sub_one_lt_mem_nhds :
    {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Circle) := by
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

variable (ψ : AddChar K Circle)

def IsTrivialOn (n : ℤ) : Prop := ∀ x ∈ valBall (K := K) n, ψ x = 1

variable {ψ} in
theorem IsTrivialOn.mono {m n : ℤ} (h : IsTrivialOn ψ m) (hmn : m ≤ n) : IsTrivialOn ψ n :=
  fun x hx => by
    have hval : normalizedValuation K x ≤ WithZero.exp (-n) := hx
    exact h x (hval.trans (WithZero.exp_le_exp.mpr (by omega)))

theorem exists_isTrivialOn (hψ : Continuous ψ) : ∃ n, IsTrivialOn ψ n := by
  have : ψ ⁻¹' {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : K) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact setOf_norm_sub_one_lt_mem_nhds
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp this
  exact ⟨n, fun x hx => eq_one_of_forall_norm_sub_one_lt ψ (valBall (K := K) n) (fun y hy => hn hy) hx⟩

theorem exists_le_of_isTrivialOn (hψ1 : ψ ≠ 1) : ∃ N, ∀ n, IsTrivialOn ψ n → N ≤ n := by
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hψ1 (DFunLike.ext _ _ fun a => (h a).trans (one_apply a).symm)
  refine ⟨ord x + 1, fun n hn => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hx (hn.mono (by omega : n ≤ ord x) x mem_valBall_ord)

def addCharConductor : ℤ := sInf {n : ℤ | IsTrivialOn ψ n}

variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

omit hψ in
theorem bddBelow_isTrivialOn : BddBelow {n : ℤ | IsTrivialOn ψ n} := by
  obtain ⟨N, hN⟩ := exists_le_of_isTrivialOn ψ hψ1
  exact ⟨N, fun m hm => hN m hm⟩

theorem isTrivialOn_addCharConductor : IsTrivialOn ψ (addCharConductor ψ) := by
  obtain ⟨n, hn⟩ := exists_isTrivialOn ψ hψ
  exact Int.csInf_mem ⟨n, hn⟩ (bddBelow_isTrivialOn hψ1)

theorem isTrivialOn_iff (n : ℤ) : IsTrivialOn ψ n ↔ addCharConductor ψ ≤ n :=
  ⟨fun h => csInf_le (bddBelow_isTrivialOn hψ1) h,
    fun h => (isTrivialOn_addCharConductor hψ hψ1).mono h⟩

omit hψ hψ1 in
theorem isTrivialOn_mulShift_iff {a : K} (ha : a ≠ 0) (n : ℤ) :
    IsTrivialOn (ψ.mulShift a) n ↔ IsTrivialOn ψ (n + ord a) := by
  constructor
  · intro h y hy
    have hy' : y ∈ a • (valBall (K := K) n : Set K) := by
      rw [smul_valBall ha]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    have := h x hx
    rwa [AddChar.mulShift_apply] at this
  · intro h x hx
    rw [AddChar.mulShift_apply]
    apply h
    have : a • x ∈ a • (valBall (K := K) n : Set K) := Set.smul_mem_smul_set hx
    rw [smul_valBall ha] at this
    exact this

theorem isTrivialOn_mulShift_iff_mem (a : K) (n : ℤ) :
    IsTrivialOn (ψ.mulShift a) n ↔ a ∈ valBall (K := K) (addCharConductor ψ - n) := by
  by_cases ha : a = 0
  · simp [ha, IsTrivialOn]
  rw [isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1, mem_valBall_iff_le_ord ha]
  omega

omit hψ1 in
theorem continuous_mulShift (a : K) : Continuous (ψ.mulShift a) := by
  have : (ψ.mulShift a : K → Circle) = fun x => ψ (a * x) := by
    ext x
    rw [AddChar.mulShift_apply]
  rw [this]
  exact hψ.comp (continuous_const_mul a)

omit hψ [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mulShift_ne_one {a : K} (ha : a ≠ 0) : ψ.mulShift a ≠ 1 :=
  AddChar.IsPrimitive.of_ne_one hψ1 ha


theorem addCharConductor_mulShift {a : K} (ha : a ≠ 0) :
    addCharConductor (ψ.mulShift a) = addCharConductor ψ - ord a := by
  have hc := continuous_mulShift hψ a
  have h1 := mulShift_ne_one hψ1 ha
  have key : ∀ n, addCharConductor (ψ.mulShift a) ≤ n ↔ addCharConductor ψ - ord a ≤ n := fun n => by
    rw [← isTrivialOn_iff hc h1, isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1]
    omega
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

end Characters

section Residue

end Residue

section Duality

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

end Duality

section SelfDual

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)


end SelfDual

end GroundTheory.LocalField
end
end
