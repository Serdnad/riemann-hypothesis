module

public import GroundTheory.AutomorphicForms.Bundle004
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import GroundTheory.AutomorphicForms.StableConjCyclic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Type*} [CommRing A] [CommRing B]


omit [DecidableEq ι] in
theorem map_unitaryExpr (φ : A →+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, φ (sA x) = sB (φ x)) (H M : Matrix ι ι A) :
    ((M.map sA)ᵀ * H * M).map φ = ((M.map φ).map sB)ᵀ * H.map φ * M.map φ := by
  have hc : (φ : A → B) ∘ sA = sB ∘ φ := funext hs
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map, hc]

theorem map_mem_unitaryGroupMatrix (φ : A →+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, φ (sA x) = sB (φ x)) {HA : Matrix ι ι A} {HB : Matrix ι ι B}
    (hH : HA.map φ = HB) {g : GL ι A} (hg : g ∈ unitaryGroupMatrix sA HA) :
    Matrix.GeneralLinearGroup.map φ g ∈ unitaryGroupMatrix sB HB := by
  rw [mem_unitaryGroupMatrix] at *
  have := congrArg (fun M => M.map φ) hg
  rw [map_unitaryExpr φ hs, hH] at this
  exact this

noncomputable def unitaryGroupMatrixCongr (e : A ≃+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, e (sA x) = sB (e x)) {HA : Matrix ι ι A} {HB : Matrix ι ι B}
    (hH : HA.map e = HB) : unitaryGroupMatrix sA HA ≃* unitaryGroupMatrix sB HB where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (e : A →+* B) g,
    map_mem_unitaryGroupMatrix (e : A →+* B) hs hH g.2⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.map (e.symm : B →+* A) g,
    map_mem_unitaryGroupMatrix (e.symm : B →+* A)
      (fun x => by
        apply e.injective
        simp only [RingHom.coe_coe, RingEquiv.apply_symm_apply]
        rw [hs, RingEquiv.apply_symm_apply])
      (by rw [← hH, Matrix.map_map]; ext i j; simp) g.2⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  right_inv g := by
    apply Subtype.ext; apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  map_mul' a b := by
    apply Subtype.ext
    simp

end Transport

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

section BaseChange

variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]

noncomputable def conjBase : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id R R) (conj F E).toAlgHom).toRingHom

variable {F E R S T}

@[simp]
theorem conjBase_tmul (r : R) (e : E) : conjBase F E R (r ⊗ₜ e) = r ⊗ₜ conj F E e := rfl


variable (E) in
noncomputable def tensorMap (f : R →ₐ[F] S) : R ⊗[F] E →ₐ[F] S ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)

omit [Algebra.IsQuadraticExtension F E] in
@[simp]
theorem tensorMap_tmul (f : R →ₐ[F] S) (r : R) (e : E) :
    tensorMap E f (r ⊗ₜ e) = f r ⊗ₜ e := rfl

theorem tensorMap_conjBase (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    tensorMap E f (conjBase F E R z) = conjBase F E S (tensorMap E f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r e => rw [conjBase_tmul, tensorMap_tmul, tensorMap_tmul, conjBase_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [Algebra.IsQuadraticExtension F E] in
theorem tensorMap_includeRight (f : R →ₐ[F] S) (e : E) :
    tensorMap E f (Algebra.TensorProduct.includeRight e) =
      (Algebra.TensorProduct.includeRight e : S ⊗[F] E) := by
  simp [Algebra.TensorProduct.includeRight_apply]



end BaseChange

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Points

variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]

noncomputable def unitaryPoints : Subgroup (GL ι (R ⊗[F] E)) :=
  unitaryGroupMatrix (conjBase F E R)
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E))

variable {F E H R S T}

omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem map_includeRight_tensorMap (f : R →ₐ[F] S) :
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)).map
      ((tensorMap E f : R ⊗[F] E →ₐ[F] S ⊗[F] E) : R ⊗[F] E →+* S ⊗[F] E) =
      H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] S ⊗[F] E) := by
  rw [Matrix.map_map]
  congr 1
  funext e
  exact tensorMap_includeRight f e


variable (F E H) in
noncomputable def unitaryMap (f : R →ₐ[F] S) : unitaryPoints F E H R →* unitaryPoints F E H S :=
  ((Matrix.GeneralLinearGroup.map
      ((tensorMap E f : R ⊗[F] E →ₐ[F] S ⊗[F] E) : R ⊗[F] E →+* S ⊗[F] E)).comp
    (unitaryPoints F E H R).subtype).codRestrict _ fun g =>
    map_mem_unitaryGroupMatrix _ (tensorMap_conjBase f) (map_includeRight_tensorMap f) g.2

end Points

section Functor

open CategoryTheory

universe u

variable (F E : Type u) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  {ι : Type u} [Fintype ι] [DecidableEq ι]

end Functor

section Rational

variable {F E H}

theorem lid_conjBase (z : F ⊗[F] E) :
    Algebra.TensorProduct.lid F E (conjBase F E F z) = conj F E (Algebra.TensorProduct.lid F E z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r e =>
    simp only [conjBase_tmul, Algebra.TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem map_includeRight_lid :
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] F ⊗[F] E)).map
      ((Algebra.TensorProduct.lid F E : F ⊗[F] E ≃ₐ[F] E) : F ⊗[F] E ≃+* E) = H := by
  rw [Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id H]
  congr 1
  funext e
  simp [Algebra.TensorProduct.includeRight_apply]


variable (F E H) in
noncomputable def unitaryPointsRationalEquiv :
    unitaryPoints F E H F ≃* unitaryGroupMatrix (conjHom F E) H :=
  unitaryGroupMatrixCongr ((Algebra.TensorProduct.lid F E).toRingEquiv)
    (fun z => lid_conjBase z) map_includeRight_lid

variable {V : Type*} [AddCommGroup V] [Module E V]


variable (F E) in
noncomputable def unitaryPointsRationalEquivHermitian (h : HermitianForm F E V)
    (v : Basis ι E V) : unitaryPoints F E (gram h.toSesq v) F ≃* h.unitaryGroup :=
  (unitaryPointsRationalEquiv F E (gram h.toSesq v)).trans (unitaryGroupEquivMatrix h v).symm

end Rational

end GroundTheory.Automorphic
end

section

noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global NumberField.InfinitePlace.Completion

def Rep {F : Type*} [Field F] (d : F) {n : ℕ} (a : Fin n → F) (c : F) : Prop :=
  ∃ s : Fin n → F, (∀ i, SqNorm d (s i)) ∧ ∑ i, a i * s i = c

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]

end Local

section Real

variable {K : Type*} [Field K] {w : InfinitePlace K}

end Real

section Global

universe u

variable {K : Type u} [Field K] [NumberField K]

end Global

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

open Module

section Conj

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

instance finiteDimensional_of_isQuadraticExtension : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)

theorem conjHom_apply (x : E) : conjHom F E x = conj F E x :=
  rfl

theorem exists_not_mem_range : ∃ ζ : E, ζ ∉ Set.range (algebraMap F E) := by
  by_contra H
  push Not at H
  have hbij : Function.Bijective (Algebra.linearMap F E) :=
    ⟨(algebraMap F E).injective, fun y => H y⟩
  have h1 := (LinearEquiv.ofBijective _ hbij).finrank_eq
  rw [Module.finrank_self, Algebra.IsQuadraticExtension.finrank_eq_two] at h1
  exact absurd h1 (by norm_num)

theorem conj_eq_self_iff [Algebra.IsSeparable F E] {x : E} :
    conj F E x = x ↔ x ∈ Set.range (algebraMap F E) := by
  refine ⟨fun hx => ?_, fun ⟨c, hc⟩ => hc ▸ conj_algebraMap c⟩
  by_contra hne
  rw [conj_apply] at hx
  have h2 : algebraMap F E (Algebra.trace F E x) = 2 * x := by linear_combination hx
  by_cases h2E : (2 : E) = 0
  · have htx : Algebra.trace F E x = 0 := by
      apply (algebraMap F E).injective
      rw [h2, h2E, zero_mul, map_zero]
    have ht1 : Algebra.trace F E 1 = 0 := by
      have := trace_algebraMap_quadratic (F := F) (E := E) 1
      rw [map_one, mul_one] at this
      rw [this]
      apply (algebraMap F E).injective
      rw [map_ofNat, h2E, map_zero]
    apply Algebra.trace_ne_zero F E
    refine (basisOneOf hne).ext fun i => ?_
    fin_cases i
    · simp [basisOneOf_zero, ht1]
    · simp [basisOneOf_one, htx]
  · apply hne
    refine ⟨2⁻¹ * Algebra.trace F E x, ?_⟩
    rw [map_mul, h2, map_inv₀, map_ofNat, ← mul_assoc, inv_mul_cancel₀ h2E, one_mul]

end Conj

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']

namespace HermitianForm

def Isometric (h : HermitianForm F E V) (h' : HermitianForm F E V') : Prop :=
  ∃ e : V ≃ₗ[E] V', ∀ x y, h'.toSesq (e x) (e y) = h.toSesq x y

theorem conj_toSesq (h : HermitianForm F E V) (x y : V) :
    conj F E (h.toSesq x y) = h.toSesq y x :=
  h.isSymm.eq x y

namespace Isometric

end Isometric

section Separable

variable [Algebra.IsSeparable F E]

end Separable

end HermitianForm

end GroundTheory.Automorphic

end
end

section

namespace GroundTheory.Automorphic

open Module

section CommuteField

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem commute_of_commute_of_separable_charpoly {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  let K := AlgebraicClosure E
  let φ : E →+* K := algebraMap E K
  let Φ : Module.End E V →+* Matrix (Fin n) (Fin n) K :=
    φ.mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom
  let Ψ : Matrix (Fin n) (Fin n) K →+* Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv.toRingHom
  have hsep : (Ψ (Φ f)).charpoly.Separable := by
    change (Matrix.toLin' ((LinearMap.toMatrix b b f).map φ)).charpoly.Separable
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    exact hf.map
  have hc := commute_of_commute_of_separable hsep ((hg.map Φ).map Ψ) ((hg'.map Φ).map Ψ)
  have hinj : Function.Injective (Ψ.comp Φ) := by
    intro x y hxy
    have h1 : Φ x = Φ y := (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective hxy
    have h2 : LinearMap.toMatrixAlgEquiv b x = LinearMap.toMatrixAlgEquiv b y := by
      ext i j
      exact φ.injective (congrFun (congrFun h1 i) j)
    exact (LinearMap.toMatrixAlgEquiv b).injective h2
  change g * g' = g' * g
  apply hinj
  rw [map_mul, map_mul]
  exact hc.eq

end CommuteField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]

namespace HermitianForm

variable (h : HermitianForm F E V)

noncomputable def adjoint (A : Module.End E V) : Module.End E V where
  toFun y := (Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)
  map_add' x y := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, map_add (f := _), LinearMap.add_comp]
  map_smul' c x := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, LinearMap.map_smulₛₗ, LinearMap.smul_comp,
      RingHom.id_apply]

theorem toSesq_adjoint_left (A : Module.End E V) (y x : V) :
    h.toSesq (h.adjoint A y) x = h.toSesq y (A x) := by
  change h.toSesq ((Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)) x = _
  rw [Equiv.ofBijective_apply_symm_apply (⇑h.toSesq) h.nonsingular]
  rfl

theorem eq_adjoint_iff (A B : Module.End E V) :
    B = h.adjoint A ↔ ∀ y x, h.toSesq (B y) x = h.toSesq y (A x) := by
  refine ⟨fun hB y x => hB ▸ h.toSesq_adjoint_left A y x, fun hB => LinearMap.ext fun y => ?_⟩
  apply h.nonsingular.1
  ext x
  rw [hB, toSesq_adjoint_left]

theorem adjoint_mul (A B : Module.End E V) : h.adjoint (A * B) = h.adjoint B * h.adjoint A := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rw [Module.End.mul_apply, toSesq_adjoint_left, toSesq_adjoint_left, Module.End.mul_apply]

theorem adjoint_one : h.adjoint 1 = 1 := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rfl

noncomputable def adjointEquiv (g : V ≃ₗ[E] V) : V ≃ₗ[E] V where
  toLinearMap := h.adjoint g.toLinearMap
  invFun := h.adjoint g.symm.toLinearMap
  left_inv x := by
    change (h.adjoint g.symm.toLinearMap * h.adjoint g.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.toLinearMap * g.symm.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl
  right_inv x := by
    change (h.adjoint g.toLinearMap * h.adjoint g.symm.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.symm.toLinearMap * g.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl

end HermitianForm

section Stable

variable [FiniteDimensional E V]

def IsRegularSemisimple (γ : V ≃ₗ[E] V) : Prop :=
  (γ.toLinearMap).charpoly.Separable

def torusE (γ : V ≃ₗ[E] V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.centralizer {γ}



def TorusE (γ : V ≃ₗ[E] V) : Type _ := torusE γ

namespace TorusE

variable {γ : V ≃ₗ[E] V}




variable [Fact (IsRegularSemisimple γ)]

end TorusE

end Stable

end GroundTheory.Automorphic
end
