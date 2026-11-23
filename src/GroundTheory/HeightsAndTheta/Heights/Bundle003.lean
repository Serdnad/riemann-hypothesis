module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
public import Mathlib.Basic.Complex.Basic
public import GroundTheory.HeightsAndTheta.Heights.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Defs
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

structure ProjScheme (A : Type u) [CommRing A] (N : ℕ) where

  X : Scheme.{u}

  ι : X ⟶ projectiveSpace A N

  isClosedImmersion : IsClosedImmersion ι

attribute [instance] ProjScheme.isClosedImmersion

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

variable (X : ProjScheme A N)

end ProjScheme

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

def Via {R : Type*} [CommRing R] (_φ : R →+* ℂ) : Type := ℂ

namespace Via

variable {R : Type*} [CommRing R] (φ : R →+* ℂ)

instance : Field (Via φ) := inferInstanceAs (Field ℂ)

instance : Algebra R (Via φ) := φ.toAlgebra

def ofComplex : ℂ ≃+* Via φ := RingEquiv.refl ℂ

end Via

variable {X : Scheme.{u}} (L : X.Modules)


variable (X) in
abbrev locRing (X : Scheme.{u}) (p : X) : CommRingCat.{u} :=
  TopCat.Presheaf.stalk (X := X.toTopCat) X.sheaf.obj p

abbrev modStalk (p : X) : Type u :=
  TopCat.Presheaf.stalk (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf p

def fibreAt (p : X) (φ : locRing X p →+* ℂ) : Type u :=
  TensorProduct (locRing X p) (Via φ) (modStalk L p)

variable {L}

def germM {U : X.Opens} {p : X} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) :
    modStalk L p :=
  TopCat.Presheaf.germ (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf U p hp s

def germR {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U) : locRing X p :=
  TopCat.Presheaf.germ (X := X.toTopCat) X.sheaf.obj U p hp r

lemma germM_smul {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (r • s) = germR hp r • germM hp s :=
  PresheafOfModules.germ_smul _ _ _ _ _ _

lemma germM_resM {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (resM _ hVU s) = germM (hVU hp) s :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf
    (homOfLE hVU) p hp s

lemma germR_resR {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V) (r : ringOn X U) :
    germR hp (resR hVU r) = germR (hVU hp) r :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) X.sheaf.obj (homOfLE hVU) p hp r

lemma germM_zero {U : X.Opens} {p : X} (hp : p ∈ U) :
    germM (L := L) hp (0 : ((preMod X).obj L).obj (op U)) = 0 :=
  map_zero _

theorem bijective_smul_germ {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) :
    Function.Bijective (fun r : locRing X p => r • germM hp e) := by
  have key : ∀ r : locRing X p, r • germM hp e = 0 → r = 0 := by
    intro r hr
    obtain ⟨V, hVU, hpV, r', rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat) X.sheaf.obj r hp
    change germR hpV r' • germM hp e = 0 at hr
    rw [← germM_resM hVU hpV, ← germM_smul] at hr
    obtain ⟨W, hpW, iV, iV', hW⟩ := TopCat.Presheaf.germ_eq (X := X.toTopCat) (C := Ab.{u})
      ((preMod X).obj L).presheaf p hpV hpV _ 0 (hr.trans (germM_zero hpV).symm)
    have h0 : resR iV.le r' • resM _ (iV.le.trans hVU) e = 0 := by
      rw [← resM_smul_res]
      exact hW.trans (map_zero _)
    have hz : resR iV.le r' = 0 :=
      (he W (iV.le.trans hVU)).1 (a₁ := resR iV.le r') (a₂ := 0) (by
        simp only [zero_smul]; exact h0)
    change germR hpV r' = 0
    rw [← germR_resR iV.le hpW, hz]
    exact map_zero _
  constructor
  · intro r₁ r₂ h
    have := key (r₁ - r₂) (by simp only at h; rw [sub_smul, h, sub_self])
    exact sub_eq_zero.mp this
  · intro m
    obtain ⟨V, hVU, hpV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat)
      (C := Ab.{u}) ((preMod X).obj L).presheaf m hp
    obtain ⟨r, hr⟩ := (he V hVU).2 t
    refine ⟨germR hpV r, ?_⟩
    change germR hpV r • germM hp e = germM hpV t
    rw [← hr, germM_smul, germM_resM]

def stalkEquiv {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : locRing X p ≃ₗ[locRing X p] modStalk L p :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (germM hp e)) (bijective_smul_germ hp he)

section Fibre

variable {p : X} {φ : locRing X p →+* ℂ}

instance : AddCommGroup (fibreAt L p φ) :=
  inferInstanceAs (AddCommGroup (TensorProduct (locRing X p) (Via φ) (modStalk L p)))

instance : Module (Via φ) (fibreAt L p φ) :=
  inferInstanceAs (Module (Via φ) (TensorProduct (locRing X p) (Via φ) (modStalk L p)))

instance : Module ℂ (fibreAt L p φ) :=
  Module.compHom (fibreAt L p φ) (Via.ofComplex φ).toRingHom

lemma complex_smul_def (c : ℂ) (s : fibreAt L p φ) : c • s = Via.ofComplex φ c • s := rfl


variable (L φ) in
def fibreMk (c : Via φ) (m : modStalk L p) : fibreAt L p φ :=
  (c ⊗ₜ[locRing X p] m : TensorProduct (locRing X p) (Via φ) (modStalk L p))


variable (φ) in
def value {U : X.Opens} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) : fibreAt L p φ :=
  fibreMk (L := L) (φ := φ) 1 (germM hp s)


variable (φ) in
def fibreEquiv {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreAt L p φ ≃ₗ[Via φ] Via φ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Via φ) (Via φ))
    (stalkEquiv hp he).symm).trans
      (TensorProduct.AlgebraTensorModule.rid (locRing X p) (Via φ) (Via φ))



end Fibre

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

universe u

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section DualCoord

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

variable {σ E}

theorem conjMap_surjective : Function.Surjective (conjMap σ E) := by
  intro v
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add v v' hv hv' =>
    obtain ⟨u, rfl⟩ := hv
    obtain ⟨u', rfl⟩ := hv'
    exact ⟨u + u', map_add _ _ _⟩
  | tmul w e =>
    refine ⟨ofComplex σ (starRingEnd ℂ ((ofComplex (conjugate σ)).symm w)) ⊗ₜ e, ?_⟩
    rw [conjMap_tmul, conj_ofComplex, Complex.conj_conj]
    rfl

end DualCoord

variable [NumberField K]

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]


omit [NumberField K] [Module.Projective (𝓞 K) E] in
theorem fibre_finite (σ : K →+* ℂ) : Module.Finite ℂ (Fibre σ E) := by
  have : Module.Finite ℂ (ComplexAt σ) := Module.Finite.equiv (ofComplex σ).toLinearEquiv
  exact Module.Finite.trans (ComplexAt σ) (Fibre σ E)

variable (h : HermitianMetric K E)

instance (σ : K →+* ℂ) : FiniteDimensional ℂ (FibreSpace h σ) := fibre_finite (E := E) σ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff Manifold
open Topology Set

noncomputable section

variable {N : ℕ}

namespace CP

def chartVec (i : Fin (N + 1)) (z : Fin N → ℂ) : Fin (N + 1) → ℂ := Fin.insertNth i 1 z

@[simp] lemma chartVec_self (i : Fin (N + 1)) (z : Fin N → ℂ) : chartVec i z i = 1 := by
  simp [chartVec]

@[simp] lemma chartVec_succAbove (i : Fin (N + 1)) (z : Fin N → ℂ) (j : Fin N) :
    chartVec i z (i.succAbove j) = z j := by
  simp [chartVec]

lemma chartVec_ne_zero (i : Fin (N + 1)) (z : Fin N → ℂ) : chartVec i z ≠ 0 := by
  intro h
  have := congr_fun h i
  simp at this

lemma contDiff_chartVec_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (i m : Fin (N + 1)) : ContDiff 𝕜 ∞ (fun z : Fin N → ℂ => chartVec i z m) := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp only [chartVec_self]; exact contDiff_const
  · simp only [chartVec_succAbove]
    exact (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin N => ℂ) k).contDiff

lemma continuous_chartVec (i : Fin (N + 1)) : Continuous (chartVec (N := N) i) :=
  continuous_pi fun m => (contDiff_chartVec_apply ℂ i m).continuous

def chartInv (i : Fin (N + 1)) (z : Fin N → ℂ) : CP N :=
  Projectivization.mk ℂ (chartVec i z) (chartVec_ne_zero i z)

lemma continuous_chartInv (i : Fin (N + 1)) : Continuous (chartInv (N := N) i) :=
  ProjTopology.continuous_mk'.comp
    ((continuous_chartVec i).subtype_mk fun z => chartVec_ne_zero i z)

def chartCoord (i : Fin (N + 1)) : CP N → (Fin N → ℂ) :=
  Projectivization.lift (fun v => fun j => v.1 (i.succAbove j) / v.1 i) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
    funext j
    have ht : t ≠ 0 := by rintro rfl; simp at ha
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hbi : b i = 0
    · simp [hbi]
    · field_simp)

@[simp] lemma chartCoord_mk (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    chartCoord i (Projectivization.mk ℂ v hv) = fun j => v (i.succAbove j) / v i := rfl

def chartDomain (i : Fin (N + 1)) : Set (CP N) :=
  {x | Projectivization.lift (fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => v.1 i ≠ 0) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at ha
    simp [ht]) x}

@[simp] lemma mk_mem_chartDomain (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ chartDomain i ↔ v i ≠ 0 := Iff.rfl

lemma chartInv_mem (i : Fin (N + 1)) (z : Fin N → ℂ) : chartInv i z ∈ chartDomain i := by
  simp [chartInv]

lemma chartCoord_chartInv (i : Fin (N + 1)) (z : Fin N → ℂ) : chartCoord i (chartInv i z) = z := by
  funext j; simp [chartInv]

lemma chartInv_chartCoord (i : Fin (N + 1)) {x : CP N} (hx : x ∈ chartDomain i) :
    chartInv i (chartCoord i x) = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [mk_mem_chartDomain] at hx
    simp only [chartInv, chartCoord_mk]
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (v i)⁻¹ (inv_ne_zero hx), ?_⟩
    funext m
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
    · simp [hx]
    · simp [div_eq_inv_mul]

lemma isQuotientMap_mk' : IsQuotientMap (Projectivization.mk' ℂ : {v : Fin (N + 1) → ℂ // v ≠ 0} → CP N) := by
  refine ⟨⟨rfl⟩, fun x => ?_⟩
  induction x using Projectivization.ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩

lemma isOpen_chartDomain (i : Fin (N + 1)) : IsOpen (chartDomain (N := N) i) := by
  rw [ProjTopology.isOpen_iff]
  have : (Projectivization.mk' ℂ) ⁻¹' (chartDomain (N := N) i) =
      {v : {v : Fin (N + 1) → ℂ // v ≠ 0} | v.1 i ≠ 0} := by
    ext ⟨v, hv⟩; exact Iff.rfl
  rw [this]
  exact isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const

lemma continuousOn_chartCoord (i : Fin (N + 1)) :
    ContinuousOn (chartCoord (N := N) i) (chartDomain i) := by
  rw [isQuotientMap_mk'.continuousOn_isOpen_iff (isOpen_chartDomain i)]
  refine continuousOn_pi.mpr fun j => ?_
  intro v hv
  have hvi : v.1 i ≠ 0 := hv
  have hc : ContinuousAt (fun w : {v : Fin (N + 1) → ℂ // v ≠ 0} => w.1 (i.succAbove j) / w.1 i) v :=
    (((continuous_apply _).comp continuous_subtype_val).continuousAt).div
      (((continuous_apply _).comp continuous_subtype_val).continuousAt) hvi
  exact hc.continuousWithinAt

def chart (i : Fin (N + 1)) : OpenPartialHomeomorph (CP N) (Fin N → ℂ) where
  toFun := chartCoord i
  invFun := chartInv i
  source := chartDomain i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := chartInv_mem i z
  left_inv' _ hx := chartInv_chartCoord i hx
  right_inv' z _ := chartCoord_chartInv i z
  open_source := isOpen_chartDomain i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_chartCoord i
  continuousOn_invFun := (continuous_chartInv i).continuousOn

lemma exists_mem_chartDomain (x : CP N) : ∃ i, x ∈ chartDomain i := by
  induction x using Projectivization.ind with
  | h v hv =>
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact ⟨i, hi⟩

def chartIndex (x : CP N) : Fin (N + 1) := (exists_mem_chartDomain x).choose

lemma mem_chartDomain_chartIndex (x : CP N) : x ∈ chartDomain (chartIndex x) :=
  (exists_mem_chartDomain x).choose_spec

end CP

end

end GroundTheory.Heights₂.Heights
end
