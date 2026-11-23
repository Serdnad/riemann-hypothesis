module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Support
public import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open scoped nonZeroDivisors

namespace GlobalTheory.DetClass

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def mat {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i)) (a : (i : ι) → I i) :
    Matrix ι ι R := fun j i => (φ (Pi.single i (a i)) j : R)

theorem det_mem {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a : (i : ι) → I i) : (mat φ a).det ∈ ∏ j, J j := by
  rw [Matrix.det_apply]
  refine Ideal.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  have h : ∏ i, (mat φ a) (σ i) i ∈ ∏ i, J (σ i) :=
    Ideal.prod_mem_prod fun i _ => (φ (Pi.single i (a i)) (σ i)).2
  rwa [Equiv.prod_comp σ J] at h

theorem det_swap {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (a b : (i : ι) → I i) :
    (∏ i, (b i : R)) * (mat φ a).det = (∏ i, (a i : R)) * (mat φ b).det := by
  have key : mat φ a * Matrix.diagonal (fun i => (b i : R))
      = mat φ b * Matrix.diagonal (fun i => (a i : R)) := by
    ext j i
    simp only [Matrix.mul_diagonal, mat]
    have h1 : (b i : R) • (Pi.single i (a i) : (k : ι) → I k)
        = (a i : R) • (Pi.single i (b i) : (k : ι) → I k) := by
      funext k
      by_cases hk : k = i
      · subst hk
        apply Subtype.ext
        simp [mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    have h2 := congrArg (fun x => ((φ x) j : R)) h1
    simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul] at h2
    rw [mul_comm, h2, mul_comm]
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h
  rw [mul_comm, h, mul_comm]

open Pointwise in
theorem span_mul_le {I J : ι → Ideal R} (φ : ((i : ι) → I i) →ₗ[R] ((i : ι) → J i))
    (b : (i : ι) → I i) :
    Ideal.span {(mat φ b).det} * ∏ i, I i ≤ Ideal.span {∏ i, (b i : R)} * ∏ j, J j := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  have hP : ∏ i, I i = Submodule.span R (∏ i, (I i : Set R)) := by
    rw [← Submodule.prod_span]
    simp only [Submodule.span_eq]
  rw [hP] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).mp hx
    have hs := det_swap φ (fun i => ⟨g i, hg (Finset.mem_univ i)⟩) b
    simp only at hs
    rw [mul_comm ((mat φ b).det), ← hs]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (det_mem φ _)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Ideal.add_mem _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ r hx

theorem mat_mul {I J : ι → Ideal R} (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩) * mat φ.toLinearMap (fun i => ⟨c, hI i⟩)
      = Matrix.diagonal fun _ => c * c := by
  ext j k
  simp only [Matrix.mul_apply, mat, Matrix.diagonal_apply, LinearEquiv.coe_coe]
  set v := φ (Pi.single k ⟨c, hI k⟩) with hv
  have hsw : ∀ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l)
      = c • (Pi.single i (v i) : (l : ι) → J l) := by
    intro i
    funext l
    by_cases hl : l = i
    · subst hl
      apply Subtype.ext
      simp [mul_comm]
    · simp [Pi.single_eq_of_ne hl]
  have hsum : ∑ i, (v i : R) • (Pi.single i ⟨c, hJ i⟩ : (l : ι) → J l) = c • v := by
    simp_rw [hsw, ← Finset.smul_sum, Finset.univ_sum_single]
  have h := congrArg (fun x => ((φ.symm x) j : R)) hsum

  simp only [map_sum, map_smul, hv, LinearEquiv.symm_apply_apply, Finset.sum_apply,
  Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] at h
  simp_rw [mul_comm _ ((v _ : J _) : R)]
  rw [h]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk]

theorem exists_span_mul_eq [IsDomain R] {I J : ι → Ideal R}
    (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hc0 : c ≠ 0) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    ∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} * ∏ i, I i = Ideal.span {y} * ∏ i, J i := by
  set d : R := ∏ _i : ι, c with hd
  have h1 := span_mul_le φ.toLinearMap (fun i => ⟨c, hI i⟩)
  have h2 := span_mul_le φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)
  simp only at h1 h2
  rw [← hd] at h1 h2
  set x := (mat φ.toLinearMap (fun i => ⟨c, hI i⟩)).det
  set y := (mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩)).det
  have hyx : y * x = d * d := by
    have h := congrArg Matrix.det (mat_mul φ c hI hJ)
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_mul_distrib] at h
    exact h
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => hc0
  have hdd : d * d ≠ 0 := mul_ne_zero hd0 hd0
  have hy0 : y ≠ 0 := fun h => hdd (by rw [← hyx, h, zero_mul])
  refine ⟨d * d, d * y, hdd, mul_ne_zero hd0 hy0, le_antisymm ?_ ?_⟩
  · rw [← hyx, ← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_comm (Ideal.span {d}), mul_assoc]
    exact Ideal.mul_mono_right h1
  · rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc,
      ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
    exact Ideal.mul_mono_right h2

end GlobalTheory.DetClass


open GlobalTheory.DetClass in
theorem GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv (R : Type) [CommRing R] [IsDedekindDomain R]
    (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰)
    (h : Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R)))) :
    ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  classical
  obtain ⟨φ⟩ := h
  have hne : ∀ K : (Ideal R)⁰, ∃ e : R, e ∈ (K : Ideal R) ∧ e ≠ 0 := fun K =>
    Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero K)
  choose e he he0 using hne
  set c : R := (∏ i, e (I i)) * ∏ i, e (J i) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
    (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
  have hI : ∀ i, c ∈ (I i : Ideal R) := fun i =>
    Ideal.mul_mem_right _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  have hJ : ∀ i, c ∈ (J i : Ideal R) := fun i =>
    Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_span_mul_eq φ c hc0 hI hJ
  rw [← map_prod, ← map_prod, ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa only [Submonoid.coe_finsetProd] using hxy
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PoincareDescent

theorem torsor_square {C : Type*} [Category C] [CartesianMonoidalCategory C] {A A' N : C} [GrpObj A] [GrpObj A']
    [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (h : IsPullback i (toUnit N) q η[A']) :
    IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q := by
  have hiq : i ≫ q = 1 := by
    rw [h.w]; rfl
  have hdiff : ∀ {W : C} (x y : W ⟶ A), x ≫ q = y ≫ q → (x⁻¹ * y) ≫ q = toUnit W ≫ η[A'] := by
    intro W x y e
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, inv_mul_cancel]; rfl
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift s.fst (h.lift (s.fst⁻¹ * s.snd) (toUnit _)
      (hdiff _ _ s.condition))) (fun s ↦ lift_fst _ _) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  · rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, h.lift_fst, mul_inv_cancel_left]
  · have e₁ : m ≫ fst A N = s.fst := h₁
    refine CartesianMonoidalCategory.hom_ext _ _ (by rw [e₁, lift_fst]) ?_
    rw [lift_snd]
    refine h.hom_ext ?_ (toUnit_unique _ _)
    rw [h.lift_fst, ← h₂, MonObj.comp_mul, e₁, Category.assoc, inv_mul_cancel_left]

end GlobalTheory.PoincareDescent
end

section

open CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.FlatFibreProduct

open TensorProduct

theorem injective_exact_of_isBaseChange {R R' M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [Module.Flat R R']
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module R M₁] [Module R M₂] [Module R M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R N₁] [Module R N₂] [Module R N₃]
    [Module R' N₁] [Module R' N₂] [Module R' N₃]
    [IsScalarTower R R' N₁] [IsScalarTower R R' N₂] [IsScalarTower R R' N₃]
    {ι₁ : M₁ →ₗ[R] N₁} {ι₂ : M₂ →ₗ[R] N₂} {ι₃ : M₃ →ₗ[R] N₃}
    (h₁ : IsBaseChange R' ι₁) (h₂ : IsBaseChange R' ι₂) (h₃ : IsBaseChange R' ι₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R'] N₂) (g' : N₂ →ₗ[R'] N₃)
    (hf : ∀ m, f' (ι₁ m) = ι₂ (f m)) (hg : ∀ m, g' (ι₂ m) = ι₃ (g m))
    (hinj : Function.Injective f) (hex : Function.Exact f g) :
    Function.Injective f' ∧ Function.Exact f' g' := by
  have k₁ : ∀ x, h₂.equiv (f.lTensor R' x) = f' (h₁.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hf]
    | add x y hx hy => simp_all
  have k₂ : ∀ x, h₃.equiv (g.lTensor R' x) = g' (h₂.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hg]
    | add x y hx hy => simp_all
  have inj := Module.Flat.lTensor_preserves_injective_linearMap (M := R') f hinj
  have ex := Module.Flat.lTensor_exact R' hex
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · apply h₁.equiv.symm.injective
    apply inj
    apply h₂.equiv.injective
    rw [k₁, k₁]
    simpa using hab
  · obtain ⟨x, rfl⟩ := h₂.equiv.surjective y
    rw [← k₂, LinearEquiv.map_eq_zero_iff, ex x]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨h₁.equiv z, (k₁ z).symm⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := h₁.equiv.surjective z
      refine ⟨w, h₂.equiv.injective ?_⟩
      rw [k₁, hz]

theorem exists_unique_of_flat_of_isPushout : ∀ {A B C D A' B' C' D' : CommRingCat.{0}} (fB : A ⟶ B) (fC : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D) (e : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C') (eD : D ⟶ D') (aB : A' ⟶ B') (aC : A' ⟶ C') (u' : B' ⟶ D') (v' : C' ⟶ D'), e.hom.Flat → IsPushout e fB aB eB → IsPushout e fC aC eC → IsPushout e (fB ≫ u) (aB ≫ u') eD → eB ≫ u' = u ≫ eD → eC ≫ v' = v ≫ eD → aB ≫ u' = aC ≫ v' → fB ≫ u = fC ≫ v → (∀ (b : B) (c : C), u.hom b = v.hom c → ∃! a : A, fB.hom a = b ∧ fC.hom a = c) → ∀ (b' : B') (c' : C'), u'.hom b' = v'.hom c' → ∃! a' : A', aB.hom a' = b' ∧ aC.hom a' = c' := by
  intro A B C D A' B' C' D' fB fC u v e eB eC eD aB aC u' v' hfl hB hC hD h1 h2 h3 h4 hfib
  letI : Algebra A A' := e.hom.toAlgebra
  letI : Algebra A B := fB.hom.toAlgebra
  letI : Algebra A C := fC.hom.toAlgebra
  letI : Algebra A D := (fB ≫ u).hom.toAlgebra
  letI : Algebra A' B' := aB.hom.toAlgebra
  letI : Algebra A' C' := aC.hom.toAlgebra
  letI : Algebra A' D' := (aB ≫ u').hom.toAlgebra
  letI : Algebra B B' := eB.hom.toAlgebra
  letI : Algebra C C' := eC.hom.toAlgebra
  letI : Algebra D D' := eD.hom.toAlgebra
  letI : Algebra A B' := (e ≫ aB).hom.toAlgebra
  letI : Algebra A C' := (e ≫ aC).hom.toAlgebra
  letI : Algebra A D' := (e ≫ aB ≫ u').hom.toAlgebra
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' D' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hB.w)
  haveI : IsScalarTower A C C' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hC.w)
  haveI : IsScalarTower A D D' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hD.w)
  haveI : Module.Flat A A' := hfl
  have PB : Algebra.IsPushout A A' B B' := CommRingCat.isPushout_iff_isPushout.mp hB
  have PC : Algebra.IsPushout A A' C C' := CommRingCat.isPushout_iff_isPushout.mp hC
  have PD : Algebra.IsPushout A A' D D' := CommRingCat.isPushout_iff_isPushout.mp hD
  have hb₁ : IsBaseChange A' (Algebra.linearMap A A') := IsBaseChange.linearMap A A'
  have hb₂ := IsBaseChange.prodMap _ _ PB.out PC.out
  have hb₃ := PD.out
  let uL : B →ₗ[A] D :=
    { toFun := u.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u.hom (fB.hom a * b) = (fB ≫ u).hom a * u.hom b
        rw [map_mul]; rfl }
  let vL : C →ₗ[A] D :=
    { toFun := v.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v.hom (fC.hom a * c) = (fB ≫ u).hom a * v.hom c
        rw [map_mul, h4]; rfl }
  let u'L : B' →ₗ[A'] D' :=
    { toFun := u'.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u'.hom (aB.hom a * b) = (aB ≫ u').hom a * u'.hom b
        rw [map_mul]; rfl }
  let v'L : C' →ₗ[A'] D' :=
    { toFun := v'.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v'.hom (aC.hom a * c) = (aB ≫ u').hom a * v'.hom c
        rw [map_mul, h3]; rfl }
  let f : A →ₗ[A] B × C := (Algebra.linearMap A B).prod (Algebra.linearMap A C)
  let g : B × C →ₗ[A] D := uL.coprod (-vL)
  let f' : A' →ₗ[A'] B' × C' := (Algebra.linearMap A' B').prod (Algebra.linearMap A' C')
  let g' : B' × C' →ₗ[A'] D' := u'L.coprod (-v'L)
  have hf : ∀ m, f' (Algebra.linearMap A A' m) =
      ((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) (f m) := by
    intro m
    refine Prod.ext ?_ ?_
    · exact congrArg (fun φ => φ.hom m) hB.w
    · exact congrArg (fun φ => φ.hom m) hC.w
  have hg : ∀ m, g' (((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) m) =
      (IsScalarTower.toAlgHom A D D').toLinearMap (g m) := by
    rintro ⟨b, c⟩
    change u'.hom (eB.hom b) + -v'.hom (eC.hom c) = eD.hom (u.hom b + -v.hom c)
    have e₁ : u'.hom (eB.hom b) = eD.hom (u.hom b) := congrArg (fun φ => φ.hom b) h1
    have e₂ : v'.hom (eC.hom c) = eD.hom (v.hom c) := congrArg (fun φ => φ.hom c) h2
    rw [map_add (f := _), map_neg, e₁, e₂]
  have hinj : Function.Injective f := by
    intro a₁ a₂ h
    have hb : fB.hom a₁ = fB.hom a₂ := congrArg Prod.fst h
    have hc : fC.hom a₁ = fC.hom a₂ := congrArg Prod.snd h
    obtain ⟨a, -, ha⟩ := hfib (fB.hom a₁) (fC.hom a₁)
      (by simpa using congrArg (fun φ => φ.hom a₁) h4)
    exact (ha a₁ ⟨rfl, rfl⟩).trans (ha a₂ ⟨hb.symm, hc.symm⟩).symm
  have hex : Function.Exact f g := by
    rintro ⟨b, c⟩
    change u.hom b + -v.hom c = 0 ↔ _
    rw [← sub_eq_add_neg, sub_eq_zero]
    constructor
    · intro h
      obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := hfib b c h
      exact ⟨a, Prod.ext ha₁ ha₂⟩
    · rintro ⟨a, ha⟩
      have hb : fB.hom a = b := congrArg Prod.fst ha
      have hc : fC.hom a = c := congrArg Prod.snd ha
      subst hb hc
      simpa using congrArg (fun φ => φ.hom a) h4
  obtain ⟨inj', ex'⟩ := injective_exact_of_isBaseChange hb₁ hb₂ hb₃ f g f' g' hf hg hinj hex
  intro b' c' h
  have h0 : g' (b', c') = 0 := by
    change u'.hom b' + -v'.hom c' = 0
    rw [h, add_neg_cancel]
  obtain ⟨a', ha'⟩ := (ex' (b', c')).1 h0
  refine ⟨a', ⟨congrArg Prod.fst ha', congrArg Prod.snd ha'⟩, fun y hy => inj' ?_⟩
  rw [ha']
  exact Prod.ext hy.1 hy.2

end GlobalTheory.FlatFibreProduct
end

section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.QuotientSupportBaseChange

theorem mem_support_baseChange {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : PrimeSpectrum A) :
    p ∈ Module.support A (A ⊗[R] M) ↔
      PrimeSpectrum.comap (algebraMap R A) p ∈ Module.support R M := by

  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let Kp := p.asIdeal.ResidueField
  let Kq := (PrimeSpectrum.comap (algebraMap R A) p).asIdeal.ResidueField
  have hq : (PrimeSpectrum.comap (algebraMap R A) p).asIdeal = p.asIdeal.comap (algebraMap R A) := rfl
  let _ : Algebra Kq Kp :=
    (Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) hq).toAlgebra
  have : IsScalarTower R Kq Kp := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R Kp r = Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal
      p.asIdeal (algebraMap R A) hq (algebraMap R Kq r)
    rw [Ideal.ResidueField.map_algebraMap]
    exact IsScalarTower.algebraMap_apply R A Kp r
  rw [(AlgebraTensorModule.cancelBaseChange R A Kp Kp M).nontrivial_congr,
    ← (AlgebraTensorModule.cancelBaseChange R Kq Kp Kp M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right Kq Kp

theorem nonempty_quotient_equiv {R A M N ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) (hf : IsBaseChange A f) (s : ι → M) :
    Nonempty ((A ⊗[R] (M ⧸ Submodule.span R (Set.range s))) ≃ₗ[A]
      N ⧸ Submodule.span A (Set.range fun i => f (s i))) := by

  let n := Submodule.span R (Set.range s)
  let e₀ := AlgebraTensorModule.tensorQuotientEquiv (R := R) A R A n
  have hmap : (LinearMap.range (AlgebraTensorModule.lTensor A A (n.subtype.restrictScalars R))).map
      (hf.equiv : A ⊗[R] M →ₗ[A] N) = Submodule.span A (Set.range fun i => f (s i)) := by
    change (n.baseChange A).map (hf.equiv : A ⊗[R] M →ₗ[A] N) = _
    rw [Submodule.baseChange_span, Submodule.map_span]
    congr 1
    ext x
    simp [IsBaseChange.equiv_tmul]
  exact ⟨e₀.trans (Submodule.Quotient.equiv _ _ hf.equiv hmap)⟩

theorem mem_support_quotient_iff (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R')
    (ga : S ⟶ S') (qa' : R' ⟶ S') (h : IsPushout qa ba ga qa') (hfin : qa.hom.Finite)
    {ι : Type} (s : ι → S) (p : PrimeSpectrum R') :
    ((letI := qa'.hom.toAlgebra; p ∈ Module.support R'
        (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R
        (S ⧸ Submodule.span R (Set.range s)))) := by
  let _ : Algebra R R' := ba.hom.toAlgebra
  let _ : Algebra R S := qa.hom.toAlgebra
  let _ : Algebra R' S' := qa'.hom.toAlgebra
  let _ : Algebra S S' := ga.hom.toAlgebra
  let _ : Algebra R S' := (qa ≫ ga).hom.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => by
    change (qa ≫ ga).hom r = qa'.hom (ba.hom r)
    rw [h.w]
    rfl
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hpo : Algebra.IsPushout R R' S S' := CommRingCat.isPushout_iff_isPushout.mp h.flip
  have : Module.Finite R S := hfin

  obtain ⟨e⟩ : Nonempty ((R' ⊗[R] (S ⧸ Submodule.span R (Set.range s))) ≃ₗ[R']
      S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) :=
    nonempty_quotient_equiv _ hpo.out s
  have key : p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) ↔
      PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)) := by
    rw [← e.support_eq]
    exact mem_support_baseChange p
  exact key

end GlobalTheory.QuotientSupportBaseChange
end

section

namespace GlobalTheory.NatCastStrictBound

theorem lt_natCast_of_add_one_lt_succ :
    ∀ {a : WithBot ℕ∞} {n : ℕ}, a + (1 : WithBot ℕ∞) < (↑(n + (1 : ℕ)) : WithBot ℕ∞) →
      a < (↑n : WithBot ℕ∞) := by
  intro a n h
  by_contra hc
  have hle : (↑n : WithBot ℕ∞) ≤ a := not_lt.mp hc
  have h2 : (↑n : WithBot ℕ∞) + 1 ≤ a + 1 := by gcongr
  rw [Nat.cast_add, Nat.cast_one] at h
  exact absurd h (not_lt.mpr h2)

end GlobalTheory.NatCastStrictBound
end
