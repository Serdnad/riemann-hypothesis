module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Htat.HopfOrderFlatLocal

theorem flat_localized_of_flat_baseChange {R : Type} [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] (P : Ideal R) [P.IsMaximal] (R' : Type) [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [Module.Flat R R']
    (hP : (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P)
    [Module.Flat R' (R' ⊗[R] M)] : Module.Flat R (LocalizedModule P.primeCompl M) := by
  let Rp := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit (algebraMap R R' y) := by
    intro y
    by_contra h
    have h1 : (y : R) ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') :=
      (IsLocalRing.mem_maximalIdeal _).2 h
    exact y.2 (hP.le h1)
  let ψ : Rp →+* R' := IsLocalization.lift hu
  letI : Algebra Rp R' := ψ.toAlgebra
  have hψ : ∀ r : R, algebraMap Rp R' (algebraMap R Rp r) = algebraMap R R' r :=
    fun r => IsLocalization.lift_eq hu r
  haveI : IsScalarTower R Rp R' := .of_algebraMap_eq (fun r => (hψ r).symm)
  haveI : Module.Flat Rp R' := (Module.flat_iff_of_isLocalization Rp P.primeCompl R').2 inferInstance
  haveI : IsLocalHom (algebraMap Rp R') := ⟨fun x hx => by
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
    have e : algebraMap R R' r =
        algebraMap Rp R' (IsLocalization.mk' Rp r s) * algebraMap R R' s := by
      rw [← hψ s, ← map_mul, IsLocalization.mk'_spec, hψ]
    have hr : IsUnit (algebraMap R R' r) := by
      rw [e]; exact hx.mul (hu s)
    have hrP : r ∈ P.primeCompl := by
      intro hmem
      rw [← hP] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).1 hmem hr
    have h3 : IsUnit (algebraMap R Rp r) :=
      IsLocalization.map_units Rp (⟨r, hrP⟩ : P.primeCompl)
    rw [← IsLocalization.mk'_spec Rp r s] at h3
    exact isUnit_of_mul_isUnit_left h3⟩
  haveI : Module.FaithfullyFlat Rp R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Module.Flat R' (R' ⊗[Rp] (Rp ⊗[R] M)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange R Rp R' R' M)
  haveI : Module.Flat Rp (Rp ⊗[R] M) := Module.Flat.of_flat_tensorProduct Rp (Rp ⊗[R] M) R'
  haveI : Module.Flat R (Rp ⊗[R] M) :=
    (Module.flat_iff_of_isLocalization Rp P.primeCompl (Rp ⊗[R] M)).1 inferInstance
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M)
      (TensorProduct.mk R Rp M 1))

theorem flat_baseChange_of_flat_extOrder {R : Type} [CommRing R] {T : Type} [CommGroup T] [Finite T]
    (A : Subalgebra R (T → R)) (R' : Type) [CommRing R'] [Algebra R R'] [Module.Flat R R']
    [Module.Flat R' (extOrder (algebraMap R R') A)] : Module.Flat R' (R' ⊗[R] A) := by
  classical
  cases nonempty_fintype T
  let L : R' ⊗[R] A →ₗ[R'] (T → R') :=
    (TensorProduct.piScalarRight R R' R' T).toLinearMap ∘ₗ LinearMap.baseChange R' A.val.toLinearMap
  have hL : ∀ (r : R') (a : A), L (r ⊗ₜ a) = fun t => r * algebraMap R R' ((a : T → R) t) := by
    intro r a
    ext t
    simp [L, Algebra.smul_def, mul_comm]
  have hinj : Function.Injective L := by
    have h1 : Function.Injective (LinearMap.baseChange R' A.val.toLinearMap) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact (TensorProduct.piScalarRight R R' R' T).injective.comp h1
  have hrange : LinearMap.range L = Subalgebra.toSubmodule (extOrder (algebraMap R R') A) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.inductionOn with
      | tmul r a =>
        rw [hL]
        have : (fun t => algebraMap R R' ((a : T → R) t)) ∈ extOrder (algebraMap R R') A :=
          Algebra.subset_adjoin ⟨a, a.2, rfl⟩
        exact (extOrder (algebraMap R R') A).smul_mem this r
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro g hg
      have h := (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A g).1 hg
      refine Submodule.span_le.2 ?_ h
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨(1 : R') ⊗ₜ ⟨f, hf⟩, by rw [hL]; simp⟩
  haveI : Module.Flat R' (Subalgebra.toSubmodule (extOrder (algebraMap R R') A)) :=
    inferInstanceAs (Module.Flat R' (extOrder (algebraMap R R') A))
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective L hinj ≪≫ₗ LinearEquiv.ofEq _ _ hrange)

theorem mul_mem_span_prodSpan_of_mem_span {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type} [CommRing R']
    (φ : R →+* R') (A : Subalgebra R (T → R)) {a b : T → R'}
    (ha : a ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)})
    (hb : b ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)}) :
    (fun z : T × T => a z.1 * b z.2) ∈
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨a₀, ha₀, rfl⟩ := h
    induction hb using Submodule.span_induction with
    | mem b h =>
      obtain ⟨b₀, hb₀, rfl⟩ := h
      exact Submodule.subset_span ⟨fun z => a₀ z.1 * b₀ z.2,
        Submodule.subset_span ⟨a₀, ha₀, b₀, hb₀, rfl⟩, by ext z; simp⟩
    | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext z; simp [mul_add]
    | smul c x _ hx =>
      convert Submodule.smul_mem _ c hx using 1
      ext z; simp; ring
  | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext z; simp [add_mul]
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    ext z; simp; ring

theorem prodSpan_extOrder_le {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type}
    [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) :
    prodSpan (extOrder φ A) ≤
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_mem_span_prodSpan_of_mem_span φ A ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A a).1 ha) ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A b).1 hb)

theorem isHopfOrder_of_flat_local :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsNoetherianRing R]
      (A : Subalgebra R (T → R)), (∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) →
      (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R')
        (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧
        (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧
        IsHopfOrder (extOrder (algebraMap R R') A)) → IsHopfOrder A := by
  intro R _ _ T _ _ _ A hfull H
  haveI hfin : Module.Finite R A :=
    Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  haveI hflat : Module.Flat R A := Module.flat_of_localized_maximal A fun P hP => by
    obtain ⟨R', _, _, _, _, hf, hP', hH⟩ := H P hP
    haveI := hH.projective
    haveI : Module.Flat R' (R' ⊗[R] A) := flat_baseChange_of_flat_extOrder A R'
    exact flat_localized_of_flat_baseChange A P R' hP'
  refine ⟨hfin, Module.Flat.projective_of_finitePresentation, hfull, ?_, ?_⟩
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R (T × T) (prodSpan A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact prodSpan_extOrder_le _ A (hH.comul _ h1)
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R T (Subalgebra.toSubmodule A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A _).1 (hH.inv _ h1)

end PositivityTheory.HtPt.Htat.HopfOrderFlatLocal
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gamdel

theorem mem_mulLat_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup V) (v : V) : v ∈ mulLat w L ↔ w⁻¹ • v ∈ L := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.mulLat
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [← huv]
    simpa [inv_smul_smul₀ hw] using hu
  · intro h
    exact ⟨w⁻¹ • v, h, by simp [smul_inv_smul₀ hw]⟩

theorem smul_mem_stdLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (ι : Type) {a : Ω} (ha : a ∈ R) {v : ι → Ω} (hv : v ∈ stdLat R ι) : a • v ∈ stdLat R ι := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.stdLat at hv ⊢
  rw [AddSubgroup.mem_pi] at hv ⊢
  intro j hj
  have hvj : v j ∈ R := by simpa using hv j hj
  simpa [smul_eq_mul] using R.mul_mem ha hvj

def graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') :
    AddSubgroup (V × V') where
  carrier := {p | w • p.1 ∈ A ∧ p.2 - f p.1 ∈ B}
  zero_mem' := by
    refine ⟨by simp, by simp⟩
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · have := A.add_mem h1 h3
      simpa [smul_add] using this
    · have := B.add_mem h2 h4
      convert this using 1
      simp only [Prod.snd_add, Prod.fst_add, map_add (f := _)]
      abel
  neg_mem' := by
    rintro p ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := A.neg_mem h1
      simpa [smul_neg] using this
    · have := B.neg_mem h2
      convert this using 1
      simp only [Prod.snd_neg, Prod.fst_neg, map_neg]
      abel

theorem mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') (a : V)
    (b : V') : (a, b) ∈ graphLat w A B f ↔ w • a ∈ A ∧ b - f a ∈ B := Iff.rfl

theorem smul_mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V')
    (f : V →ₗ[Ω] V') (a : Ω) (hA : ∀ v ∈ A, a • v ∈ A) (hB : ∀ v ∈ B, a • v ∈ B)
    (v : V × V') (hv : v ∈ graphLat w A B f) : a • v ∈ graphLat w A B f := by
  have hv' := (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f v.1 v.2).1 hv
  refine (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f (a • v).1 (a • v).2).2 ⟨?_, ?_⟩
  · rw [Prod.smul_fst, smul_smul, mul_comm, ← smul_smul]
    exact hA _ hv'.1
  · rw [Prod.smul_snd, Prod.smul_fst, map_smul, ← smul_sub]
    exact hB _ hv'.2

theorem glue_gamdel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) := by
  intro o Ω _ _ _ R w hwR hw r s n W om hW hom i q hiW hqS hexW hexS hsurj
  have hS : ∀ a ∈ R, ∀ v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n),
      a • v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) :=
    fun a ha v hv => PositivityTheory.HtPt.Gamdel.smul_mem_stdLat R (Fin n) ha hv
  have hmem := fun {V : Type} [AddCommGroup V] [Module Ω V] (L : AddSubgroup V) (x : V) =>
    PositivityTheory.HtPt.Gamdel.mem_mulLat_iff hw L x
  refine ⟨PositivityTheory.HtPt.Gamdel.graphLat w W (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) i,
    PositivityTheory.HtPt.Gamdel.graphLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) om q,
    fun a b => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _, fun b c => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _,
    fun a ha => ⟨PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hW a ha) (hS a ha),
      PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hS a ha) (hom a ha)⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hb).1
    · intro ha
      refine ⟨i a, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨ha, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨W.zero_mem, h⟩⟩
  · intro a
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      have h4 := hexW _ h1 h3
      rwa [hmem, inv_smul_smul₀ hw] at h4
    · intro ha
      exact ⟨hW w hwR a ha, hiW a ha⟩
  · intro b
    constructor
    · rintro ⟨c, hc⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hc).1
    · intro hb
      refine ⟨q b, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨hb, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro c
    constructor
    · rintro ⟨b, hb⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at hb
      have h1 := hom w hwR _ hb.2
      have h2 := hqS _ hb.1
      have hc : w • c = w • (c - q b) + q (w • b) := by
        rw [map_smul, smul_sub, sub_add_cancel]
      rw [hc]
      exact om.add_mem h1 h2
    · intro hc
      obtain ⟨b0, hb0, h⟩ := hsurj _ hc
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h
      refine ⟨w⁻¹ • b0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
  · intro c
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨AddSubgroup.zero_mem _, h⟩⟩
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : q (w • b) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w om := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      obtain ⟨a0, ha0, h4⟩ := (hexS _ h1).1 h3
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h4
      refine ⟨w⁻¹ • a0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
    · rintro ⟨a, ha⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at ha
      obtain ⟨h1, h2⟩ := ha
      have hwb : w • b ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) := by
        have e : w • b = w • (b - i a) + i (w • a) := by
          rw [map_smul, smul_sub, sub_add_cancel]
        rw [e]
        exact AddSubgroup.add_mem _ (hS w hwR _ h2) (hiW _ h1)
      refine ⟨hwb, ?_⟩
      have h3 : w • b - i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, ← smul_sub, inv_smul_smul₀ hw]
        exact h2
      have h4 := (hexS _ hwb).2 ⟨w • a, h1, h3⟩
      rwa [hmem, map_smul, inv_smul_smul₀ hw] at h4

end PositivityTheory.HtPt.Gamdel
end

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {Y Z : Scheme.{0}}

theorem valAt_comp (y : Spec (CommRingCat.of B) ⟶ Y) (φ : Y ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ W) (f : Γ(Z, W)) :
    valAt (y ≫ φ) W h f = valAt y (φ ⁻¹ᵁ W) h ((φ.app W).hom f) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_spec (φ : B →+* B') (y : Spec (CommRingCat.of B) ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ y) ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ y) W h' f = φ (valAt y W h f) := by
  have e : (Spec.map (CommRingCat.ofHom φ) ≫ y).appLE W ⊤ h' =
      y.appLE W ⊤ h ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    have := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) y W ⊤ ⊤ h le_top
    rw [← this]
    simp [Scheme.Hom.appLE]
    rfl
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  simp only [valAt, e]
  exact congrArg (fun z => z.hom ((y.appLE W ⊤ h).hom f)) n

theorem valAt_congr {B : Type} [CommRing B] {Y : Scheme.{0}} {y y' : Spec (CommRingCat.of B) ⟶ Y} (e : y = y') (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y' ⁻¹ᵁ W) (f : Γ(Y, W)) : valAt y W h f = valAt y' W h' f := by
  subst e; rfl

end Pull

theorem reg_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  have h1 : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := e ▸ h1
  have h3 : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun z _ => by
    have hz : z = Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact h2 (by trivial)
  refine (Pull.valAt_comp _ F U h1 s).symm.trans ((Pull.valAt_congr e U h1 h2 s).trans ?_)
  rw [Pull.valAt_spec κ _ U h3, hs t h3]

end PositivityTheory.HtPt.Htat
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ci.Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
  [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem one (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩

theorem mul {a b : Ω} {r s : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  obtain ⟨_, v, rfl, rfl⟩ := hb
  exact ⟨h, u * v, map_mul _ _ _, map_mul _ _ _⟩

theorem pow {a : Ω} {r : R} (ha : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  exact ⟨h, u ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem prod (h : genPt ξ ⤳ centre z) {ι : Type} (T : Finset ι) {a : ι → Ω} {r : ι → R}
    (ha : ∀ k, ValAt ξ z (a k) (r k)) : ValAt ξ z (∏ k ∈ T, a k) (∏ k ∈ T, r k) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact one h
  | insert k T hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]; exact mul (ha k) ih

theorem mem {a : Ω} {r : R} (ha : ValAt ξ z a r) (h : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, u, rfl, -⟩ := ha
  exact ⟨u, rfl⟩

theorem of_mem {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨_, h, u, rfl, rfl⟩

theorem zpow {K : Type} [Field K] {z : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (ha : ValAt ξ z a r)
    (ha' : ValAt ξ z a⁻¹ r⁻¹) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using pow ha n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow ha' (n + 1)

end PositivityTheory.HtPt.Ci.Val
end
end
