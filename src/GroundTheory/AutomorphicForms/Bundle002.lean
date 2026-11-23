module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
public import Lean.Elab.MutualDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Topology.Algebra.Group.ContinuousInv

@[expose] public section

section

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace SchurOrthogonality

open MeasureTheory Topology Set Function ComplexConjugate Module

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

theorem span_orbit_eq_top [π.IsIrreducible] {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (range fun g => π g v) = ⊤ := by
  set S := Submodule.span ℂ (range fun g => π g v)
  have hS : ∀ g, ∀ ⦃x⦄, x ∈ S → π g x ∈ S := by
    intro g x hx
    have : S ≤ S.comap (π g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [Module.End.mul_apply]⟩)
    exact this hx
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation π) with h | h
  · exfalso
    apply hv
    have : v ∈ (⟨S, hS⟩ : Subrepresentation π).toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exact congrArg Subrepresentation.toSubmodule h

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {Z : Subgroup G} [Z.Normal]

variable [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)] {ν : Measure (G ⧸ Z)}

section Characters

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Characters

section Orthogonality

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  {Z : Subgroup G} [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompactSpace (G ⧸ Z)]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}


end Orthogonality

end SchurOrthogonality

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open AddMonoidAlgebra

variable {n : ℕ}


variable (n) in
abbrev LaurentRing (n : ℕ) : Type := AddMonoidAlgebra ℂ (Fin n → ℤ)

abbrev monomial (l : Fin n → ℤ) : LaurentRing n := single l 1

def monomialChar (l : Fin n → ℤ) : (Fin n → ℂˣ) →* ℂ where
  toFun w := ∏ i, ((w i ^ l i : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' w w' := by
    simp only [Pi.mul_apply, mul_zpow, Units.val_mul, Finset.prod_mul_distrib]

theorem monomialChar_apply (l : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar l w = ∏ i, ((w i ^ l i : ℂˣ) : ℂ) := rfl

@[simp]
theorem monomialChar_zero (w : Fin n → ℂˣ) : monomialChar 0 w = 1 := by
  simp [monomialChar_apply]

theorem monomialChar_add (l l' : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar (l + l') w = monomialChar l w * monomialChar l' w := by
  simp only [monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def pointHom (w : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun l := monomialChar (Multiplicative.toAdd l) w
  map_one' := by simp [monomialChar_apply]
  map_mul' l l' := by
    simp only [toAdd_mul, monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul,
      Finset.prod_mul_distrib]

def evalAt (w : Fin n → ℂˣ) : LaurentRing n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (pointHom w)

theorem evalAt_single (w : Fin n → ℂˣ) (l : Fin n → ℤ) (c : ℂ) :
    evalAt w (single l c) = c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_single, smul_eq_mul]
  rfl

theorem evalAt_apply (w : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt w p = p.coeff.sum fun l c => c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_apply]
  rfl

theorem monomialChar_injective : Function.Injective (monomialChar : (Fin n → ℤ) → _) := by
  intro l l' h
  funext i
  have h2 := DFunLike.congr_fun h (Pi.mulSingle i (Units.mk0 (2 : ℂ) two_ne_zero))
  simp only [monomialChar_apply] at h2
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp)] at h2
  simp only [Pi.mulSingle_eq_same, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h2
  have hn : ‖(2 : ℂ) ^ l i‖ = ‖(2 : ℂ) ^ l' i‖ := by rw [h2]
  rw [norm_zpow, norm_zpow, Complex.norm_two] at hn
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) hn

theorem eq_zero_of_forall_evalAt {p : LaurentRing n} (h : ∀ w, evalAt w p = 0) : p = 0 := by
  have hli : LinearIndependent ℂ (fun l : Fin n → ℤ => ((monomialChar l : (Fin n → ℂˣ) →* ℂ) :
      (Fin n → ℂˣ) → ℂ)) :=
    (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp _ monomialChar_injective
  have hz : Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) p.coeff =
      Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) 0 := by
    rw [map_zero]
    funext w
    rw [Finsupp.linearCombination_apply, Pi.zero_apply, ← h w, evalAt_apply, Finsupp.sum,
      Finsupp.sum, Finset.sum_apply]
    rfl
  exact AddMonoidAlgebra.coeff_eq_zero.1 (hli hz)

theorem eq_of_forall_evalAt {p q : LaurentRing n} (h : ∀ w, evalAt w p = evalAt w q) : p = q :=
  sub_eq_zero.1 (eq_zero_of_forall_evalAt fun w => by rw [map_sub, h, sub_self])

theorem exists_eq_evalAt (ψ : LaurentRing n →ₐ[ℂ] ℂ) : ∃ w : Fin n → ℂˣ, ψ = evalAt w := by
  set M : Multiplicative (Fin n → ℤ) →* ℂ := (AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ)).symm ψ
  let U : Multiplicative (Fin n → ℤ) →* ℂˣ := M.toHomUnits
  set w : Fin n → ℂˣ := fun i => U (Multiplicative.ofAdd (Pi.single i 1))
  refine ⟨w, ?_⟩
  have hl : ∀ l : Multiplicative (Fin n → ℤ),
      l = ∏ i, (Multiplicative.ofAdd (Pi.single i 1 : Fin n → ℤ)) ^ (Multiplicative.toAdd l i) := by
    intro l
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hM : M = pointHom w := by
    refine MonoidHom.ext fun l => ?_
    have h1 : M l = (U l : ℂ) := rfl
    rw [h1]
    conv_lhs => rw [hl l]
    rw [map_prod, Units.coe_prod]
    simp only [map_zpow]
    rfl
  rw [evalAt, ← hM, Equiv.apply_symm_apply]

instance : Algebra.FiniteType ℂ (LaurentRing n) := by
  infer_instance

theorem exists_ker_evalAt_comp_eq {A : Type*} [CommRing A] [Algebra ℂ A]
    (Φ : A →ₐ[ℂ] LaurentRing n) (hΦ : Function.Injective Φ)
    [hint : Algebra.IsIntegral Φ.range (LaurentRing n)] (I : Ideal A) [hI : I.IsMaximal] :
    ∃ w : Fin n → ℂˣ, RingHom.ker ((evalAt w).comp Φ) = I := by
  let e : A ≃ₐ[ℂ] Φ.range := AlgEquiv.ofInjective Φ hΦ
  let P : Ideal Φ.range := I.comap (e.symm : Φ.range →+* A)
  haveI : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hP : RingHom.ker (algebraMap Φ.range (LaurentRing n)) ≤ P := by
    intro x hx
    have : x = 0 := Subtype.ext hx
    rw [this]
    exact P.zero_mem
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hP
  letI := Ideal.Quotient.field Q
  haveI : Algebra.FiniteType ℂ (LaurentRing n ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q)
      (Ideal.Quotient.mkₐ_surjective ℂ Q)
  haveI := finite_of_finite_type_of_isJacobsonRing ℂ (LaurentRing n ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := LaurentRing n ⧸ Q)
  let e' : ℂ ≃ₐ[ℂ] LaurentRing n ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) hbij
  let ψ : LaurentRing n →ₐ[ℂ] ℂ := e'.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q)
  have hker : ∀ p, ψ p = 0 ↔ p ∈ Q := by
    intro p
    simp only [ψ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [AlgEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨w, hw⟩ := exists_eq_evalAt ψ
  refine ⟨w, Ideal.ext fun a => ?_⟩
  rw [RingHom.mem_ker, AlgHom.comp_apply, ← hw, hker]
  have h1 : Φ a = algebraMap Φ.range (LaurentRing n) (e a) := rfl
  rw [h1, ← Ideal.mem_under, hQP]
  change e.symm (e a) ∈ I ↔ a ∈ I
  rw [AlgEquiv.symm_apply_apply]

theorem isIntegral_of_forall (A : Subalgebra ℂ (LaurentRing n))
    (h₁ : ∀ i, IsIntegral A (monomial (Pi.single i 1 : Fin n → ℤ)))
    (h₂ : ∀ i, IsIntegral A (monomial (Pi.single i (-1) : Fin n → ℤ))) :
    Algebra.IsIntegral A (LaurentRing n) := by
  let S : Subalgebra ℂ (LaurentRing n) := (integralClosure A (LaurentRing n)).restrictScalars ℂ
  have hmono : ∀ l : Fin n → ℤ, monomial l ∈ S := by
    intro l
    have hl : monomial l = ∏ i, monomial (Pi.single i (l i) : Fin n → ℤ) := by
      rw [AddMonoidAlgebra.prod_single]
      simp only [Finset.prod_const_one]
      congr 1
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hl]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    rcases le_or_gt 0 (l i) with h | h
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i 1) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, hk, ← Pi.single_smul]
        simp
      rw [this]
      exact Subalgebra.pow_mem _ (h₁ i) k
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h.le)
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i (-1)) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, ← Pi.single_smul]
        congr 2
        simp only [nsmul_eq_mul, mul_neg, mul_one]
        omega
      rw [this]
      exact Subalgebra.pow_mem _ (h₂ i) k
  refine ⟨fun p => ?_⟩
  have : p ∈ S := by
    rw [← AddMonoidAlgebra.sum_coeff_single p]
    refine Subalgebra.sum_mem _ fun l _ => ?_
    have : (single l (p.coeff l) : LaurentRing n) = p.coeff l • monomial l := by
      rw [AddMonoidAlgebra.smul_single', mul_one]
    rw [this]
    exact Subalgebra.smul_mem _ (hmono l) _
  exact this

end Spherical

end GroundTheory.Automorphic
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Topology Set DoubleCoset

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]

section Action

variable (P Q : Subgroup G) (x : G)

@[instance_reducible]
def doubleCosetAction : MulAction (P × Q) (doubleCoset x (P : Set G) Q) where
  smul pq g := ⟨(pq.1 : G) * g * (pq.2 : G)⁻¹, by
    obtain ⟨p, hp, q, hq, h⟩ := mem_doubleCoset.1 g.2
    refine mem_doubleCoset.2 ⟨pq.1 * p, P.mul_mem pq.1.2 hp, q * (pq.2 : G)⁻¹,
      Q.mul_mem hq (Q.inv_mem pq.2.2), ?_⟩
    rw [h]
    group⟩
  one_smul g := Subtype.ext (by
    show ((1 : P × Q).1 : G) * g * ((1 : P × Q).2 : G)⁻¹ = g
    simp)
  mul_smul a b g := Subtype.ext (by
    show ((a * b).1 : G) * g * ((a * b).2 : G)⁻¹ =
      (a.1 : G) * ((b.1 : G) * g * (b.2 : G)⁻¹) * (a.2 : G)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group)

end Action

variable {P Q : Subgroup G}

theorem isOpenMap_doubleCoset (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G)) (x : G)
    (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q)) :
    IsOpenMap (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) := by
  let := doubleCosetAction P Q x
  have : SigmaCompactSpace P := hP.sigmaCompactSpace
  have : SigmaCompactSpace Q := hQ.sigmaCompactSpace
  have : LocallyCompactSpace (doubleCoset x (P : Set G) Q) := hC.locallyCompactSpace
  have : ContinuousSMul (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨Continuous.subtype_mk ?_ _⟩
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv)
  have : MulAction.IsPretransitive (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := mem_doubleCoset.1 a.2
    obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := mem_doubleCoset.1 b.2
    refine ⟨(⟨p₂ * p₁⁻¹, P.mul_mem hp₂ (P.inv_mem hp₁)⟩, ⟨q₂⁻¹ * q₁, Q.mul_mem (Q.inv_mem hq₂) hq₁⟩), ?_⟩
    apply Subtype.ext
    show (p₂ * p₁⁻¹) * (a : G) * (q₂⁻¹ * q₁)⁻¹ = b
    rw [h₁, h₂]
    group
  have hopen := isOpenMap_smul_of_sigmaCompact (G := P × Q) (X := doubleCoset x (P : Set G) Q)
    ⟨x, mem_doubleCoset_self P Q x⟩
  let e : (P × Q) ≃ₜ (P × Q) := (Homeomorph.refl P).prodCongr (Homeomorph.inv Q)
  have : (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) =
      (fun γ : P × Q => γ • (⟨x, mem_doubleCoset_self P Q x⟩ : doubleCoset x (P : Set G) Q)) ∘ e := by
    funext pq
    apply Subtype.ext
    show (pq.1 : G) * x * pq.2 = (pq.1 : G) * x * ((pq.2⁻¹ : Q) : G)⁻¹
    simp
  rw [this]
  exact hopen.comp e.isOpenMap

theorem exists_nhds_inter_doubleCoset_subset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {y : G} (hy : y ∈ doubleCoset x (P : Set G) Q) {UP UQ : Set G} (hUP : UP ∈ 𝓝 (1 : G))
    (hUQ : UQ ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ UP ∧ ∃ q ∈ Q, q ∈ UQ ∧ z = p * y * q := by
  have hCy : doubleCoset y (P : Set G) Q = doubleCoset x (P : Set G) Q := doubleCoset_eq_of_mem hy
  rw [← hCy] at hC ⊢
  have hopen := isOpenMap_doubleCoset hP hQ y hC
  set W : Set (P × Q) := {pq | (pq.1 : G) ∈ interior UP ∧ (pq.2 : G) ∈ interior UQ}
  have hW : IsOpen W :=
    (isOpen_interior.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isOpen_interior.preimage (continuous_subtype_val.comp continuous_snd))
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (hopen W hW)
  have h1 : (1 : P × Q) ∈ W := ⟨mem_interior_iff_mem_nhds.2 hUP, mem_interior_iff_mem_nhds.2 hUQ⟩
  have hyV : y ∈ V := by
    have : (⟨y, mem_doubleCoset_self P Q y⟩ : doubleCoset y (P : Set G) Q) ∈
        Subtype.val ⁻¹' V := by
      rw [hV]
      exact ⟨1, h1, Subtype.ext (by simp)⟩
    exact this
  refine ⟨V, hVo.mem_nhds hyV, fun z hz hzC => ?_⟩
  have : (⟨z, hzC⟩ : doubleCoset y (P : Set G) Q) ∈ Subtype.val ⁻¹' V := hz
  rw [hV] at this
  obtain ⟨pq, hpq, hpqz⟩ := this
  refine ⟨pq.1, pq.1.2, interior_subset hpq.1, pq.2, pq.2.2, interior_subset hpq.2, ?_⟩
  exact (congrArg Subtype.val hpqz).symm

theorem exists_isCompact_subset_doubleCoset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {Kc : Set G} (hK : IsCompact Kc) (hKC : Kc ⊆ doubleCoset x (P : Set G) Q) :
    ∃ L : Set G, IsCompact L ∧ L ⊆ Q ∧ ∀ z ∈ Kc, ∃ p ∈ P, ∃ l ∈ L, z = p * x * l := by
  obtain ⟨K₁, hK₁c, hK₁⟩ := exists_compact_mem_nhds (1 : G)
  have hloc : ∀ c ∈ Kc, ∃ V ∈ 𝓝 c, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ (univ : Set G) ∧ ∃ q ∈ Q, q ∈ K₁ ∧ z = p * c * q :=
    fun c hc => exists_nhds_inter_doubleCoset_subset hP hQ hC (hKC hc) Filter.univ_mem hK₁
  choose V hV hVsub using hloc
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' V hV
  have hq : ∀ c : Kc, ∃ p ∈ P, ∃ q ∈ Q, (c : G) = p * x * q := fun c => mem_doubleCoset.1 (hKC c.2)
  choose pc hpc qc hqc hcq using hq
  refine ⟨⋃ c ∈ t, (fun z => qc c * z) '' ((Q : Set G) ∩ K₁), ?_, ?_, ?_⟩
  · exact t.isCompact_biUnion fun c _ =>
      (hK₁c.inter_left hQ).image (continuous_const.mul continuous_id)
  · intro l hl
    simp only [Set.mem_iUnion, Set.mem_image] at hl
    obtain ⟨c, _, z, hz, rfl⟩ := hl
    exact Q.mul_mem (hqc c) hz.1
  · intro z hz
    have hz' := ht hz
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨c, hct, hzc⟩ := hz'
    obtain ⟨p, hp, -, q, hq, hqK, rfl⟩ := hVsub c c.2 z hzc (hKC hz)
    refine ⟨p * pc c, P.mul_mem hp (hpc c), qc c * q, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨c, hct, q, ⟨hq, hqK⟩, rfl⟩
    · rw [hcq c]
      group

end Parabolic

end GroundTheory.Automorphic
end
end
