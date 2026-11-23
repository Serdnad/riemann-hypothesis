module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle525
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem mOm_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] {α : A →+* B}
    (h : SemiHom (RingHom.id R) α) (e : ∀ a, α a = algebraMap A B a) (j : ℕ) (x : Om R A j) :
    h.mOm j x = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) x := by
  let L : Om R A j →ₗ[A] Om R B j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply, e]; exact algebraMap_smul B a _ }
  have hL : L = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti]
    apply Subtype.ext
    change h.mDR _ = _
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun i ↦ ?_)
    exact (h.mDR_ι (v i)).trans (congrArg _ (h.oneFormMap_eq_kaehlerDifferential_map e (v i)))
  exact LinearMap.congr_fun hL x

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExtJ

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

theorem surj_keyJ {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
    (y : TrivSqZeroExt (F.obj T') (Om R (F.obj T') j)) (a₀ : F.obj T) (η₀ : Om R (F.obj T) j)
    (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = pOm F j l η₀) :
    y * extMapJ F j l c ^ (k₁ + k₂ + 1) = extMapJ F j l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMapJ, fst_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMapJ, fst_extMapJ, snd_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      pOm_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_keyJ {T : C} (c x : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_omjExt (H : Desc.HasLoc F) : Desc.HasLoc (omjExt F j) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := FormExt.isLocalization_of_data F l c.fst h1 h2 h3
  haveI : Algebra.FormallyEtale (F.obj T) (F.obj T') :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c.fst)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R (F.obj T) (F.obj T')) j
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c.fst) (F.obj T') _).2 hb
  have hp : ∀ ω, pOm F j l ω =
      GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')) ω :=
    mOm_eq_exteriorPowerMapOver _ (fun _ ↦ rfl) j
  have hs : ∀ (a : F.obj T) (η : Om R (F.obj T') j), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omjExt_iff F j l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omjExt_iff F j u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T'))) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_keyJ F j l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : GlobalTheory.exteriorPowerMapOver (F.obj T') j
        (KaehlerDifferential.map R R (F.obj T) (F.obj T')) x.snd = 0 :=
      (hp _).symm.trans ((snd_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')))
      (x₁ := x.snd) (x₂ := 0) (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_keyJ F j c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExtJ
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh
open scoped TensorProduct

namespace GlobalTheory.Obs.TenExt

variable {R : Type} [CommRing R] (N : Type) [AddCommGroup N] [Module R N]

theorem rTensor_smul {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (f : B →ₐ[R] B')
    (a : B) (m : B ⊗[R] N) :
    LinearMap.rTensor N f.toLinearMap (a • m) = f a • LinearMap.rTensor N f.toLinearMap m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def tenMap {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N) →ₐ[R] TrivSqZeroExt (F.obj T') (F.obj T' ⊗[R] N) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (LinearMap.rTensor N (mp F φ).toLinearMap c.snd)
  map_one' := by ext <;> simp
  map_mul' c d := by
    ext
    · simp
    · simp [rTensor_smul]
  map_zero' := by ext <;> simp
  map_add' c d := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

@[simp] theorem fst_tenMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) :
    (tenMap N F φ c).fst = mp F φ c.fst := by simp [tenMap]

@[simp] theorem snd_tenMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) :
    (tenMap N F φ c).snd = LinearMap.rTensor N (mp F φ).toLinearMap c.snd := by simp [tenMap]

def tenExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N))
  map φ := CommAlgCat.ofHom (tenMap N F φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext ((fst_tenMap N F _ c).trans (mp_id F T _)) (by
    refine (snd_tenMap N F _ c).trans ?_
    rw [show (mp F (𝟙 T)).toLinearMap = LinearMap.id from LinearMap.ext fun x ↦ mp_id F T x]
    simp))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext (by
    change (tenMap N F (φ ≫ ψ) c).fst = (tenMap N F ψ (tenMap N F φ c)).fst
    simp only [fst_tenMap]; exact mp_comp F φ ψ _) (by
    change (tenMap N F (φ ≫ ψ) c).snd = (tenMap N F ψ (tenMap N F φ c)).snd
    simp only [snd_tenMap]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    congr 2
    exact LinearMap.ext fun x ↦ mp_comp F φ ψ x))

theorem isUnit_mp_tenExt_iff {T S : C} (u : T ⟶ S) (c : (tenExt N F).obj T) :
    IsUnit (mp (tenExt N F) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_tenMap N F u c)))

theorem span_inl_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (tenExt N F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (F.obj S ⊗[R] N))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.Obs.TenExt

namespace GlobalTheory.Obs.TenExt

variable {R : Type} [CommRing R] (N : Type) [AddCommGroup N] [Module R N]
variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N))
    (y : TrivSqZeroExt (F.obj T') (F.obj T' ⊗[R] N)) (a₀ : F.obj T)
    (η₀ : F.obj T ⊗[R] N) (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = LinearMap.rTensor N (mp F l).toLinearMap η₀) :
    y * tenMap N F l c ^ (k₁ + k₂ + 1) = tenMap N F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_tenMap, fst_tenMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_tenMap, fst_tenMap, snd_tenMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      rTensor_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_key {T : C} (c x : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_tenExt (H : Desc.HasLoc F) : Desc.HasLoc (tenExt N F) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := GlobalTheory.CechDR.FormExt.isLocalization_of_data F l c.fst h1 h2 h3
  have hp : ∀ m, LinearMap.rTensor N (mp F l).toLinearMap m =
      TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T')) m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hs : ∀ (a : F.obj T) (η : F.obj T' ⊗[R] N), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_tenExt_iff N F l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_tenExt_iff N F u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T'))) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    exact ⟨k₁ + k₂ + 1, _, surj_key N F l c y a₀ η₀ k₁ k₂ ha hη⟩
  · have e1 : mp F l x.fst = 0 :=
      (fst_tenMap N F l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T')) x.snd = 0 :=
      (hp _).symm.trans ((snd_tenMap N F l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T'))) (x₁ := x.snd) (x₂ := 0)
      (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_key N F c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.Obs.TenExt
end
end

section

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem mem_symCocycles_of_pullTwo_mulP {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) (h : pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1))) :
    c ∈ symCocycles R (G.A n) := by
  rw [mem_symCocycles] at h ⊢
  have h3 : Function.Injective
      (TensorProduct.map (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) (pullbackTwo (G.mulP n))) :=
    TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n)
      (G.pullbackTwo_mulP_injective n)
  refine ⟨h3 ?_, G.pullbackTwo_mulP_injective n ?_⟩
  · rw [← cobTwo_pullTwo, h.1, map_zero]
  · rw [← h.2]
    exact TensorProduct.map_comm _ _ c

end PDivGroup

end GlobalTheory
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]


variable (R A) in
def restrZeroLeft : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ (counit (R := R) (A := A)).rTensor A

theorem restrZeroLeft_tmul (a b : A) : restrZeroLeft R A (a ⊗ₜ b) = counit (R := R) a • b := by
  simp [restrZeroLeft]

theorem restrZeroLeft_comul (a : A) : restrZeroLeft R A (comul a) = a := by
  simp [restrZeroLeft, Coalgebra.rTensor_counit_comul]


variable (R A) in
def restrZeroZero : A ⊗[R] (A ⊗[R] A) →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ TensorProduct.map (counit (R := R) (A := A))
    (restrZeroLeft R A)

theorem restrZeroZero_tmul (a : A) (t : A ⊗[R] A) :
    restrZeroZero R A (a ⊗ₜ t) = counit (R := R) a • restrZeroLeft R A t := by
  simp [restrZeroZero]

theorem restrZeroZero_assoc (u : A ⊗[R] A) (b : A) :
    restrZeroZero R A (TensorProduct.assoc R A A A (u ⊗ₜ b)) =
      counit (R := R) (restrZeroLeft R A u) • b := by
  induction u with
  | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy, add_smul]
  | tmul x y =>
    rw [TensorProduct.assoc_tmul, restrZeroZero_tmul, restrZeroLeft_tmul, restrZeroLeft_tmul,
      map_smul, smul_eq_mul, mul_smul]

theorem restrZeroLeft_of_cobTwo_eq_zero {c : A ⊗[R] A} (hc : cobTwo R A c = 0) :
    restrZeroLeft R A c =
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) c)) := by
  have key : ∀ t : A ⊗[R] A, restrZeroZero R A (cobTwo R A t) = restrZeroLeft R A t -
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) t)) := fun t => by
    induction t with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
    | tmul a b =>
      rw [cobTwo_apply]
      simp only [map_sub, map_add (f := _), LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.flip_apply,
        TensorProduct.mk_apply, restrZeroZero_assoc, restrZeroZero_tmul, restrZeroLeft_comul,
        restrZeroLeft_tmul, Bialgebra.counit_one, one_smul, TensorProduct.map_tmul,
        TensorProduct.lid_tmul, smul_eq_mul, Algebra.algebraMap_eq_smul_one, mul_smul]
      abel
  have := key c
  rw [hc, map_zero] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

theorem dUnit_mul'_map (f g : A →ₐc[R] B) (t : A ⊗[R] A) :
    dUnit (R := R) (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) t)) =
      cotMap g (dUnit (R := R) (restrZeroLeft R A t)) +
        cotMap f (dUnit (R := R) (restrZeroLeft R A (TensorProduct.comm R A A t))) := by
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
  | tmul a b =>
    have e1 : dUnit (R := R) (counit (R := R) a • b) = counit (R := R) a • dUnit (R := R) b :=
      map_smul (AugCot.d _) _ _
    have e2 : dUnit (R := R) (counit (R := R) b • a) = counit (R := R) b • dUnit (R := R) a :=
      map_smul (AugCot.d _) _ _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.comm_tmul, restrZeroLeft_tmul,
      restrZeroLeft_tmul, e1, e2, map_smul, map_smul, cotMap_d, cotMap_d, dUnit, AugCot.d_mul]
    have c1 : counitAlgHom R B (f a) = counit (R := R) a := CoalgHomClass.counit_comp_apply f a
    have c2 : counitAlgHom R B (g b) = counit (R := R) b := CoalgHomClass.counit_comp_apply g b
    exact congrArg₂ (· + ·) (congrArg₂ (· • ·) c1 rfl) (congrArg₂ (· • ·) c2 rfl)

theorem dUnit_mul'_map_of_mem (f g : A →ₐc[R] B) {c : A ⊗[R] A} (hc : c ∈ symCocycles R A) :
    dUnit (R := R) (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) = 0 := by
  obtain ⟨h1, h2⟩ := mem_symCocycles.1 hc
  rw [dUnit_mul'_map, h2, restrZeroLeft_of_cobTwo_eq_zero h1, dUnit, AugCot.d_algebraMap,
    map_zero, map_zero, zero_add]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {G H : PDivGroup p R}

theorem rigExtMap_add (f g : G ⟶ H) : rigExtMap (f + g) = rigExtMap f + rigExtMap g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  let B : G.funs := ⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n)
      (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by
    dsimp only
    rw [← (c.2 n).2]
    generalize c.1 (n + 1) = t
    induction t with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x y => simp [res_app]⟩
  have hB : G.dFun B = 0 :=
    Subtype.ext (funext fun n => dUnit_mul'_map_of_mem (f.app n) (g.app n) (c.2 n).1)
  have hc : cocyclesMap (f + g) c = cocyclesMap f c + cocyclesMap g c + G.cob B :=
    Subtype.ext (funext fun n => T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1)
  change G.rigMk (cocyclesMap (f + g) c, omegaMap G H (f + g) w) =
    G.rigMk (cocyclesMap f c, omegaMap G H f w) + G.rigMk (cocyclesMap g c, omegaMap G H g w)
  rw [← map_add (f := _), Prod.mk_add_mk, map_add (omegaMap G H) f g, LinearMap.add_apply, hc]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · show G.cob B = _
    simp
  · show G.dFun B = _
    rw [hB]
    simp


variable (G) in
theorem rigExtMap_natCast_smul_id (hp : (p : R) = 0) : rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  let φ : (G ⟶ G) →+ (G.RigExt →ₗ[R] G.RigExt) :=
    AddMonoidHom.mk' (fun f => rigExtMap f) (fun f g => rigExtMap_add f g)
  have h : φ (p • 𝟙 G) = p • φ (𝟙 G) := map_nsmul φ p (𝟙 G)
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul] at h
  exact h

theorem rigExtMap_add_and_natCast_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G H : PDivGroup p R),
    (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧
      rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 :=
  fun _ _ _ _ h G _ => ⟨rigExtMap_add, G.rigExtMap_natCast_smul_id h⟩

end GlobalTheory.PDivGroup
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A) (z : A ⊗[O] A), cobOne O A b = a • z → ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}, ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | exact GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | (intros; apply GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul <;> assumption)
end
