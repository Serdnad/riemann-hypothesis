module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle001
public import GroundTheory.GlobalFields.SUnits
public import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Ramification
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
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

noncomputable def integerUnit {a : 𝓞 F} (ha : a ≠ 0) : Fˣ :=
  Units.mk0 (algebraMap (𝓞 F) F a) (by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    exact ha)

theorem coe_integerUnit {a : 𝓞 F} (ha : a ≠ 0) : (integerUnit ha : F) = algebraMap (𝓞 F) F a :=
  rfl

theorem integerUnit_mul {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0) :
    integerUnit hab = integerUnit ha * integerUnit hb :=
  Units.ext (by simp [coe_integerUnit])

theorem integerUnit_pow {a : 𝓞 F} (ha : a ≠ 0) (k : ℕ) (hak : a ^ k ≠ 0) :
    integerUnit hak = integerUnit ha ^ k :=
  Units.ext (by simp [coe_integerUnit])

theorem ordAt_pow (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (k : ℕ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  simp only [ordAt, map_pow, toAdd_pow, nsmul_eq_mul]
  ring

theorem ordAt_integerUnit_eq_of_associated {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associated a b) (w : HeightOneSpectrum (𝓞 F)) :
    ordAt w (integerUnit ha) = ordAt w (integerUnit hb) := by
  obtain ⟨u, rfl⟩ := h
  have hu : integerUnit hb = integerUnit ha * Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u :=
    Units.ext (by simp [coe_integerUnit])
  rw [hu, ordAt_mul]
  simp [ordAt, valuation_of_unit_eq]


open scoped Classical in
theorem ordAt_placeUnit (v w : HeightOneSpectrum (𝓞 F)) :
    ordAt w (GroundTheory.Global.SUnit.placeUnit v) = if w = v then (classNumber F : ℤ) else 0 := by
  rw [ordAt, GroundTheory.Global.SUnit.valuationOfNeZero_placeUnit]
  split_ifs <;> simp

theorem placeUnit_eq_integerUnit (v : HeightOneSpectrum (𝓞 F)) :
    GroundTheory.Global.SUnit.placeUnit v =
      integerUnit (GroundTheory.Global.SUnit.exists_pow_classNumber_eq_span v).choose_spec.1 :=
  Units.ext rfl

def primeNZD (v : HeightOneSpectrum (𝓞 F)) : (Ideal (𝓞 F))⁰ :=
  ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩


open scoped Classical in
theorem exists_ordAt_eq_of_mk0_eq {v p : HeightOneSpectrum (𝓞 F)}
    (h : ClassGroup.mk0 (primeNZD v) = ClassGroup.mk0 (primeNZD p)) :
    ∃ x : Fˣ, ∀ w, ordAt w x = (if w = v then 1 else 0) - (if w = p then 1 else 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  change Ideal.span {a} * v.asIdeal = Ideal.span {b} * p.asIdeal at hab
  set hF := classNumber F with hhF
  have hv := GroundTheory.Global.SUnit.exists_pow_classNumber_eq_span v
  have hp := GroundTheory.Global.SUnit.exists_pow_classNumber_eq_span p
  set πv := hv.choose
  set πp := hp.choose
  have hπv : πv ≠ 0 := hv.choose_spec.1
  have hπp : πp ≠ 0 := hp.choose_spec.1
  have hav : a ^ hF * πv ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) hπv
  have hbp : b ^ hF * πp ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) hπp
  have hspan : Ideal.span {a ^ hF * πv} = Ideal.span {b ^ hF * πp} := by
    have := congrArg (· ^ hF) hab
    simp only [mul_pow, Ideal.span_singleton_pow] at this
    rw [hv.choose_spec.2, hp.choose_spec.2, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton] at this
    exact this
  have hassoc := Ideal.span_singleton_eq_span_singleton.1 hspan
  refine ⟨integerUnit hb * (integerUnit ha)⁻¹, fun w => ?_⟩
  have key := ordAt_integerUnit_eq_of_associated hav hbp hassoc w
  rw [integerUnit_mul (pow_ne_zero _ ha) hπv hav, integerUnit_mul (pow_ne_zero _ hb) hπp hbp,
    integerUnit_pow ha hF (pow_ne_zero _ ha), integerUnit_pow hb hF (pow_ne_zero _ hb),
    ordAt_mul, ordAt_mul, ordAt_pow, ordAt_pow] at key
  have hv' : ordAt w (integerUnit hπv) = if w = v then (hF : ℤ) else 0 := by
    rw [← ordAt_placeUnit v w, placeUnit_eq_integerUnit]
  have hp' : ordAt w (integerUnit hπp) = if w = p then (hF : ℤ) else 0 := by
    rw [← ordAt_placeUnit p w, placeUnit_eq_integerUnit]
  rw [hv', hp'] at key
  have hh : (hF : ℤ) ≠ 0 := by exact_mod_cast classNumber_ne_zero F
  rw [ordAt_mul, ordAt_inv]
  apply mul_left_cancel₀ hh
  split_ifs at key ⊢ <;> linarith

variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem divS_placeUnit (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    divS S (Additive.ofMul (GroundTheory.Global.SUnit.placeUnit v.1)) =
      (classNumber F : ℤ) • Finsupp.single v 1 := by
  classical
  ext w
  rw [divS_apply, toMul_ofMul, ordAt_placeUnit, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : w = v
  · subst h
    simp
  · have h' : w.1 ≠ v.1 := fun e => h (Subtype.ext e)
    simp [h', Ne.symm h]

theorem classNumber_nsmul_sPic (c : sPic S) : classNumber F • c = 0 := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective (divS S).range c
  rw [← map_nsmul]
  refine (QuotientAddGroup.eq_zero_iff _).2 ?_
  induction D using Finsupp.induction_linear with
  | zero => rw [smul_zero]; exact zero_mem _
  | add f g hf hg => rw [smul_add]; exact add_mem hf hg
  | single v m =>
    refine ⟨m • Additive.ofMul (GroundTheory.Global.SUnit.placeUnit v.1), ?_⟩
    rw [map_zsmul, divS_placeUnit]
    ext w
    by_cases hw : v = w <;> simp [hw]
    ring


open scoped Classical in
noncomputable def sPicGen (c : ClassGroup (𝓞 F)) : sPic S :=
  if h : ∃ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, ClassGroup.mk0 (primeNZD v.1) = c then
    sPicMk S (Finsupp.single h.choose 1)
  else 0

theorem sPicMk_single_eq_sPicGen (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    sPicMk S (Finsupp.single v 1) = sPicGen S (ClassGroup.mk0 (primeNZD v.1)) := by
  classical
  have hex : ∃ u : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      ClassGroup.mk0 (primeNZD u.1) = ClassGroup.mk0 (primeNZD v.1) := ⟨v, rfl⟩
  rw [sPicGen, dite_eq_left hex]
  obtain ⟨x, hx⟩ := exists_ordAt_eq_of_mk0_eq hex.choose_spec.symm
  rw [← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).2 ⟨Additive.ofMul x, ?_⟩
  ext w
  rw [divS_apply, toMul_ofMul, hx, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have e1 : (w.1 = v.1) ↔ (v = w) := ⟨fun e => (Subtype.ext e).symm, fun e => by rw [e]⟩
  have e2 : (w.1 = hex.choose.1) ↔ (hex.choose = w) := ⟨fun e => (Subtype.ext e).symm, fun e => by rw [e]⟩
  simp only [e1, e2]

theorem closure_range_sPicGen : AddSubgroup.closure (Set.range (sPicGen S)) = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective (divS S).range c
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f g hf hg => rw [map_add (sPicMk S)]; exact add_mem hf hg
  | single v m =>
    rw [← Finsupp.smul_single_one, map_zsmul]
    refine AddSubgroup.zsmul_mem _ ?_ m
    change sPicMk S (Finsupp.single v 1) ∈ _
    rw [sPicMk_single_eq_sPicGen]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩

instance finite_sPic : Finite (sPic S) := by
  have : AddGroup.FG (sPic S) :=
    AddGroup.fg_iff.2 ⟨_, closure_range_sPicGen S, Set.finite_range _⟩
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun c => ?_
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨classNumber F, classNumber_pos F,
    classNumber_nsmul_sPic S c⟩

end GroundTheory.ProfCoh
end

section

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

open scoped Pointwise

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]


omit [NumberField F] in
theorem finiteDimensional_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M] :
    FiniteDimensional F E :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

theorem isUnramifiedIn_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M]
    (v : HeightOneSpectrum (𝓞 F)) (hM : Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  intro P hP hPv
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  have hu := ((isUnramifiedAt_tower_iff (F := F) (L := E) Q).1 (hM Q hQ this)).1
  have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
  subst e
  exact hu

theorem isUnramifiedIn_iff_inertia {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        ∀ σ ∈ Q.inertia Gal(M/F), ∀ x (hx : x ∈ E), σ ⟨x, h hx⟩ = ⟨x, h hx⟩ := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  constructor
  · intro hE Q hQ hQv σ hσ x hx
    have : (Q.under (𝓞 E)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact hQv.over⟩
    have hu := hE (Q.under (𝓞 E)) inferInstance this
    exact (isUnramifiedAt_under_iff_inertia Q).1 hu σ hσ ⟨x, hx⟩
  · intro hI P hP hPv
    obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hu := (isUnramifiedAt_under_iff_inertia (F := F) (E := E) Q).2
      (fun σ hσ y => hI Q hQ hQv σ hσ y.1 y.2)
    have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
    subst e
    exact hu


omit [NumberField F] in
theorem mem_map_fixedField_iff {M : IntermediateField F Ω} (H : Subgroup Gal(M/F)) (x : Ω) :
    x ∈ (IntermediateField.fixedField H).map M.val ↔ ∃ hx : x ∈ M, ∀ σ ∈ H, σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨⟨x, hx⟩, (IntermediateField.mem_fixedField_iff H _).2 hfix, rfl⟩

theorem isUnramifiedIn_iff_le_fixedField {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        E ≤ (IntermediateField.fixedField (Q.inertia Gal(M/F))).map M.val := by
  rw [isUnramifiedIn_iff_inertia h]
  refine forall_congr' fun Q => forall_congr' fun _ => forall_congr' fun _ => ?_
  constructor
  · intro hI x hx
    exact (mem_map_fixedField_iff _ x).2 ⟨h hx, fun σ hσ => hI σ hσ x hx⟩
  · intro hle σ hσ x hx
    obtain ⟨_, hfix⟩ := (mem_map_fixedField_iff _ x).1 (hle hx)
    exact hfix σ hσ

variable [IsGalois F Ω]

theorem isUnramifiedIn_sup {E₁ E₂ : IntermediateField F Ω} [FiniteDimensional F E₁]
    [FiniteDimensional F E₂] (v : HeightOneSpectrum (𝓞 F))
    (h₁ : Algebra.IsUnramifiedIn (𝓞 E₁) v.asIdeal) (h₂ : Algebra.IsUnramifiedIn (𝓞 E₂) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le (E₁ ⊔ E₂)
  rw [isUnramifiedIn_iff_le_fixedField hM]
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_left.trans hM)] at h₁
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_right.trans hM)] at h₂
  exact fun Q hQ hQv => sup_le (h₁ Q hQ hQv) (h₂ Q hQ hQv)

theorem IsUnramifiedOutside.sup {S : Set (HeightOneSpectrum (𝓞 F))} {E₁ E₂ : IntermediateField F Ω}
    [FiniteDimensional F E₁] [FiniteDimensional F E₂] (h₁ : IsUnramifiedOutside S E₁)
    (h₂ : IsUnramifiedOutside S E₂) : IsUnramifiedOutside S (E₁ ⊔ E₂) :=
  fun v hv => isUnramifiedIn_sup v (h₁ v hv) (h₂ v hv)

theorem isUnramifiedIn_bot (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(⊥ : IntermediateField F Ω)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le (⊥ : IntermediateField F Ω)
  rw [isUnramifiedIn_iff_inertia hM]
  intro Q _ _ σ _ x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes a

theorem isUnramifiedOutside_bot (S : Set (HeightOneSpectrum (𝓞 F))) :
    IsUnramifiedOutside S (⊥ : IntermediateField F Ω) :=
  fun v _ => isUnramifiedIn_bot v

theorem isUnramifiedIn_map {E : IntermediateField F Ω} [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) (hE : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) (τ : Gal(Ω/F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (τ : Ω →ₐ[F] Ω))) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le E
  set M' : IntermediateField F Ω := M.toIntermediateField with hM'
  set ρ : Gal(M'/F) := τ.restrictNormal M' with hρ
  have hρapp : ∀ y (hy : y ∈ M'), ((ρ ⟨y, hy⟩ : M') : Ω) = τ y := fun y hy =>
    AlgEquiv.restrictNormal_commutes τ M' ⟨y, hy⟩
  have hτM : E.map (τ : Ω →ₐ[F] Ω) ≤ M' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    have := (ρ ⟨y, hM hy⟩).2
    rwa [hρapp] at this
  rw [isUnramifiedIn_iff_inertia hM] at hE
  rw [isUnramifiedIn_iff_inertia hτM]
  intro Q hQ hQv σ hσ x hx
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  have hconj : ρ⁻¹ * σ * ρ ∈ (ρ⁻¹ • Q).inertia Gal(M'/F) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro z
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
      smul_sub, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    exact (AddSubgroup.mem_inertia.1 hσ) (ρ • z)
  have := NumberField.of_module_finite F M'
  have : IsGaloisGroup Gal(M'/F) (𝓞 F) (𝓞 M') := IsGaloisGroup.of_isFractionRing _ _ _ F M'
  have hfix := hE (ρ⁻¹ • Q) inferInstance inferInstance _ hconj y hy
  have hρy : ρ ⟨y, hM hy⟩ = ⟨(τ : Ω →ₐ[F] Ω) y, hτM hx⟩ := Subtype.ext (hρapp y (hM hy))
  rw [← hρy]
  calc σ (ρ ⟨y, hM hy⟩) = ρ ((ρ⁻¹ * σ * ρ) ⟨y, hM hy⟩) := by
        simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    _ = ρ ⟨y, hM hy⟩ := by rw [hfix]

theorem IsUnramifiedOutside.map {S : Set (HeightOneSpectrum (𝓞 F))} {E : IntermediateField F Ω}
    [FiniteDimensional F E] (hE : IsUnramifiedOutside S E) (τ : Gal(Ω/F)) :
    IsUnramifiedOutside S (E.map (τ : Ω →ₐ[F] Ω)) :=
  fun v hv => isUnramifiedIn_map v (hE v hv) τ

end GroundTheory.ProfCoh
end
