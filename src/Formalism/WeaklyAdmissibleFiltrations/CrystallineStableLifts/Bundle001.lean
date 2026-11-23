module

public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open LaurentPolynomial

def lpScaleF (c : ℚˣ) : Multiplicative ℤ →* LaurentPolynomial ℚ where
  toFun m := ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, zpow_add, Units.val_mul, T_add, smul_mul_smul_comm]

@[simp] lemma lpScaleF_apply (c : ℚˣ) (m : Multiplicative ℤ) :
    lpScaleF c m = ((c ^ m.toAdd : ℚˣ) : ℚ) • T m.toAdd := rfl

def lpScale (c : ℚˣ) : LaurentPolynomial ℚ →ₐ[ℚ] LaurentPolynomial ℚ :=
  AddMonoidAlgebra.lift ℚ (LaurentPolynomial ℚ) ℤ (lpScaleF c)

lemma lpScale_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScale c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]
  | C_mul_T n a =>
    have h1 : lpScale c (T n) = ((c ^ n : ℚˣ) : ℚ) • T n := by
      unfold lpScale T
      rw [AddMonoidAlgebra.lift_single, one_smul, lpScaleF_apply]
      rfl
    have h2 : (C a * T n : LaurentPolynomial ℚ) = a • T n := by
      rw [C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [h2, map_smul, h1, smul_smul, AddMonoidAlgebra.coeff_smul_apply,
      AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, smul_eq_mul]
    by_cases h : n = m
    · subst h
      simp only [if_true]
      ring
    · simp [h]

def lpScaleE (c : ℚˣ) : LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ :=
  AlgEquiv.ofAlgHom (lpScale c) (lpScale c⁻¹)
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [mul_inv_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])
    (AlgHom.ext fun f => LaurentPolynomial.ext fun m => by
      simp [lpScale_coeff, ← mul_assoc]
      rw [inv_mul_cancel₀ (zpow_ne_zero _ c.ne_zero), one_mul])

lemma lpScaleE_coeff (c : ℚˣ) (f : LaurentPolynomial ℚ) (m : ℤ) :
    (lpScaleE c f).coeff m = ((c ^ m : ℚˣ) : ℚ) * f.coeff m := by
  show (lpScale c f).coeff m = _
  rw [lpScale_coeff]

def lpScaleHom : ℚˣ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) where
  toFun := lpScaleE
  map_one' := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by simp [lpScaleE_coeff]
  map_mul' c d := AlgEquiv.ext fun f => LaurentPolynomial.ext fun m => by
    simp [lpScaleE_coeff, AlgEquiv.mul_apply, mul_zpow, mul_assoc]

def lpTwo : ℚˣ := Units.mk0 2 (by norm_num)

@[simp] lemma lpTwo_val : (lpTwo : ℚ) = 2 := rfl

@[simp] lemma lpTwo_zpow (m : ℤ) : ((lpTwo ^ m : ℚˣ) : ℚ) = (2 : ℚ) ^ m := by
  rw [Units.val_zpow_eq_zpow_val, lpTwo_val]

lemma lpTwo_fix (f : LaurentPolynomial ℚ) (h : lpScaleE lpTwo f = f) :
    algebraMap ℚ (LaurentPolynomial ℚ) (f.coeff 0) = f := by
  refine LaurentPolynomial.ext fun a => ?_
  rw [← C_eq_algebraMap, C_apply]
  by_cases ha : a = 0
  · rw [if_pos ha, ha]
  · rw [if_neg ha]
    have h' := congrArg (fun g : LaurentPolynomial ℚ => g.coeff a) h
    simp only [lpScaleE_coeff, lpTwo_zpow] at h'
    have h2 : (2 : ℚ) ^ a ≠ 1 := fun h1 => ha ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h1)
    have h3 : ((2 : ℚ) ^ a - 1) * f.coeff a = 0 := by rw [sub_mul, h', one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) h2
    · exact h4.symm

def lpFil (a : ℤ) : Submodule ℚ (LaurentPolynomial ℚ) where
  carrier := {f | ∀ m < a, f.coeff m = 0}
  add_mem' {x y} hx hy m hm := by simp [AddMonoidAlgebra.coeff_add, hx m hm, hy m hm]
  zero_mem' m _ := by simp
  smul_mem' c x hx m hm := by simp [hx m hm]

lemma lpFil_mul (a b : ℤ) (x y : LaurentPolynomial ℚ) (hx : x ∈ lpFil a) (hy : y ∈ lpFil b) :
    x * y ∈ lpFil (a + b) := by
  classical
  intro m hm
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  rw [if_neg]
  intro hij
  have hi' : ¬ i < a := fun h => (Finsupp.mem_support_iff.mp hi) (hx i h)
  have hj' : ¬ j < b := fun h => (Finsupp.mem_support_iff.mp hj) (hy j h)
  omega

theorem existsPeriodRingData_holds : ExPD := by
  let χ : Multiplicative ℤ →* ℚˣ := zpowersHom ℚˣ lpTwo
  let act : Multiplicative ℤ →* (LaurentPolynomial ℚ ≃ₐ[ℚ] LaurentPolynomial ℚ) := lpScaleHom.comp χ
  have hact : ∀ g (f : LaurentPolynomial ℚ) m, (act g f).coeff m = ((χ g ^ m : ℚˣ) : ℚ) * f.coeff m := by
    intro g f m
    exact lpScaleE_coeff (χ g) f m
  have hone : act (Multiplicative.ofAdd 1) = lpScaleE lpTwo := by
    show lpScaleE (χ (Multiplicative.ofAdd 1)) = lpScaleE lpTwo
    simp [χ]
  have hfix : ∀ f : LaurentPolynomial ℚ, (∀ g, act g f = f) → ∃ c : ℚ, algebraMap ℚ _ c = f := by
    intro f hf
    refine ⟨f.coeff 0, lpTwo_fix f ?_⟩
    have := hf (Multiplicative.ofAdd 1)
    rwa [hone] at this
  exact ⟨{
    p := 2
    hp := Nat.prime_two
    finK₀ := inferInstance
    finK := inferInstance
    σ := AlgHom.id ℚ ℚ
    σ_bij := ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
    actB := act
    invB := hfix
    φ := (lpScaleE lpTwo).toAlgHom
    φ_inj := (lpScaleE lpTwo).injective
    φ_K₀ := fun c => (lpScaleE lpTwo).toAlgHom.commutes c
    φ_comm := fun g b => LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (act g b)).coeff m = (act g (lpScaleE lpTwo b)).coeff m
      rw [lpScaleE_coeff, hact, hact, lpScaleE_coeff]
      ring
    actdR := act
    invdR := hfix
    ι := AlgHom.id ℚ _
    ι_inj := fun _ _ h => h
    ι_comm := fun _ _ => rfl
    Fil := lpFil
    Fil_anti := fun a f hf m hm => hf m (by omega)
    one_mem := fun m hm => by rw [← T_zero, T_apply, if_neg (by omega)]
    Fil_mul := lpFil_mul
    Fil_exh := fun x => by
      refine ⟨-(∑ i ∈ x.coeff.support, |i|), fun m hm => ?_⟩
      by_contra hne
      have hm' : m ∈ x.coeff.support := Finsupp.mem_support_iff.mpr hne
      have h1 := Finset.single_le_sum (f := fun i : ℤ => |i|) (fun i _ => abs_nonneg i) hm'
      have h2 := neg_abs_le m
      linarith
    Fil_sep := fun x hx => LaurentPolynomial.ext fun m => by
      rw [hx (m + 1) m (by omega)]
      rfl
    Fil_G := fun g a x hx m hm => by rw [hact, hx m hm, mul_zero]
    χ := χ
    t := T 1
    t_unit := isUnit_T 1
    t_act := fun g => LaurentPolynomial.ext fun m => by
      rw [hact, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul]
      by_cases h : (1 : ℤ) = m
      · subst h
        simp
      · simp [h]
    t_φ := LaurentPolynomial.ext fun m => by
      change (lpScaleE lpTwo (T 1)).coeff m = _
      rw [lpScaleE_coeff, AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, lpTwo_zpow]
      by_cases h : (1 : ℤ) = m
      · subst h
        norm_num
      · simp [h]
    mem_filtration_one := fun m hm => by rw [AlgHom.id_apply, T_apply, if_neg (by omega)]
    not_mem_filtration_two := fun h => by
      have h1 := h 1 (by norm_num)
      rw [AlgHom.id_apply, T_apply, if_pos rfl] at h1
      exact one_ne_zero h1
    fund := fun b hb _ => ⟨b.coeff 0, lpTwo_fix b hb⟩ }⟩

end Formalism.WeaklyAdmissibleFiltrations
end
end

section

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section TrivCrysProof

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

include PD in
private theorem trivCrys_nontrivial_B : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact zero_mem _

private def trivCrysIncl : K₀ →ₗ[Qp] B := (Algebra.linearMap K₀ B).restrictScalars Qp

private def trivCrysMap : LL ⊗[Qp] K₀ →ₗ[LL] LL ⊗[Qp] B :=
  AlgebraTensorModule.lTensor LL LL (trivCrysIncl (Qp := Qp) (K₀ := K₀) (B := B))

private theorem trivCrys_act_tmul (g : G) (l : LL) (b : B) :
    actVB PD (1 : Representation LL G LL) g (l ⊗ₜ[Qp] b) = l ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]

private theorem trivCrys_range_le (g : G) (y : LL ⊗[Qp] K₀) :
    actVB PD (1 : Representation LL G LL) g (trivCrysMap (LL := LL) (B := B) y) =
      trivCrysMap (LL := LL) (B := B) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [trivCrysMap, trivCrysIncl, AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, trivCrys_act_tmul]
    rw [AlgEquiv.commutes]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

variable [FiniteDimensional Qp LL]

private def trivCrysCoord (b : Basis (Fin (finrank Qp LL)) Qp LL) (i : Fin (finrank Qp LL)) :
    LL ⊗[Qp] B →ₗ[Qp] B :=
  (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B (b.coord i)

private theorem trivCrysCoord_tmul (b : Basis (Fin (finrank Qp LL)) Qp LL) (i) (l : LL) (c : B) :
    trivCrysCoord (B := B) b i (l ⊗ₜ[Qp] c) = b.coord i l • c := by
  simp [trivCrysCoord]

private theorem trivCrys_decomp (b : Basis (Fin (finrank Qp LL)) Qp LL) (x : LL ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] trivCrysCoord (B := B) b i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [trivCrysCoord_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Basis.coord_apply]
    rw [← TensorProduct.sum_tmul, Basis.sum_repr]
  | add y z hy hz =>
    conv_lhs => rw [hy, hz]
    rw [← Finset.sum_add_distrib]
    simp only [map_add (f := _), TensorProduct.tmul_add]

private theorem trivCrysCoord_act (b : Basis (Fin (finrank Qp LL)) Qp LL) (i) (g : G)
    (x : LL ⊗[Qp] B) :
    trivCrysCoord (B := B) b i (actVB PD (1 : Representation LL G LL) g x) =
      PD.actB g (trivCrysCoord (B := B) b i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    rw [trivCrys_act_tmul, trivCrysCoord_tmul, trivCrysCoord_tmul]
    exact (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem trivCrys_Dcris_eq :
    Dcris PD (1 : Representation LL G LL) = LinearMap.range (trivCrysMap (LL := LL) (K₀ := K₀) (B := B)) := by
  apply le_antisymm
  · intro x hx
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    let b := Module.finBasis Qp LL
    have hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = trivCrysCoord (B := B) b i x := by
      intro i
      apply PD.invB
      intro g
      rw [← trivCrysCoord_act PD b i g x, hx g]
    choose c hc using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] c i, ?_⟩

    rw [map_sum, trivCrys_decomp b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trivCrysMap, trivCrysIncl, AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, hc i]
  · rintro _ ⟨y, rfl⟩
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    exact fun g => trivCrys_range_le PD g y

include PD in
private theorem trivCrysMap_injective :
    Function.Injective (trivCrysMap (Qp := Qp) (LL := LL) (K₀ := K₀) (B := B)) := by
  haveI := trivCrys_nontrivial_B PD
  have hi : Function.Injective (trivCrysIncl (Qp := Qp) (K₀ := K₀) (B := B)) :=
    (algebraMap K₀ B).injective
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ hi
  exact h2

end TrivCrysProof

theorem trivialIsCrystalline_holds : TrivCrys := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _
  unfold IsCrys
  rw [trivCrys_Dcris_eq PD (LL := LL), LinearMap.finrank_range_of_inj (trivCrysMap_injective PD),
    Module.finrank_baseChange, Module.finrank_self, mul_one]

end Formalism.WeaklyAdmissibleFiltrations
end
end

section

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

theorem existsStableLattice_holds : ExLattice := by
  intro G _ LL _ O _ _ _ hinj
  have hli : LinearIndependent O (fun _ : Unit => (1 : LL)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    cases i
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def, mul_one] at hg
    exact (map_eq_zero_iff _ hinj).mp (by simpa using hg)
  refine ⟨⟨Submodule.span O (Set.range fun _ : Unit => (1 : LL)), ?_, ?_, ?_, ?_⟩⟩
  · intro g x hx
    simpa using hx
  · exact Submodule.fg_span (Set.finite_range _)
  · exact Module.Free.of_basis (Module.Basis.span hli)
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL) :=
      Submodule.subset_span ⟨(), rfl⟩
    have h2 := Submodule.smul_mem (Submodule.span LL (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL)) x
      (Submodule.subset_span h1)
    simpa using h2

end Formalism.WeaklyAdmissibleFiltrations
end
end

section

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section Top
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

end Top

section Stable
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem pc_actVB_mul (PD : PeriodData G Qp K₀ K B BdR) (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, map_mul, AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem pc_actVB_res (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, AlgebraTensorModule.map_tmul, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem pc_mem_Dpcris {x : V ⊗[Qp] B} :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ (h : G) x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, pc_actVB_res]

theorem pc_Dpcris_stable (g : G) {x : V ⊗[Qp] B} (hx : x ∈ PC.Dpcris ρ) :
    actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [pc_mem_Dpcris] at hx ⊢
  intro h
  have hmem : g⁻¹ * (h : G) * g ∈ PC.H := by
    have := PC.normal.conj_mem (h : G) h.2 g⁻¹
    rwa [inv_inv] at this
  have e : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
  rw [← pc_actVB_mul, e, pc_actVB_mul, hx ⟨_, hmem⟩]

end Stable

end Formalism.WeaklyAdmissibleFiltrations
end
end
