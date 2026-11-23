module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

variable (R : Type) [CommRing R] (ι : Type) (m : ℕ)

def orig : Ideal (MvPolynomial ι R) := Ideal.span (Set.range X)

abbrev Jet : Type := MvPolynomial ι R ⧸ orig R ι ^ (m + 1)

variable {R ι m}

theorem map_orig_pow {B : Type} [CommRing B] (f : MvPolynomial ι R →+* B) (k : ℕ) :
    Ideal.map f (orig R ι ^ k) = Ideal.span (Set.range fun i => f (X i)) ^ k := by
  rw [orig, Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
  rfl

def liftJet {B : Type} [CommRing B] [Algebra R B] (f : MvPolynomial ι R →ₐ[R] B)
    (h : Ideal.span (Set.range fun i => f (X i)) ^ (m + 1) = ⊥) : Jet R ι m →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ f fun a ha => by
    have : f a ∈ Ideal.map (f : MvPolynomial ι R →+* B) (orig R ι ^ (m + 1)) :=
      Ideal.mem_map_of_mem _ ha
    have h' : Ideal.span (Set.range fun i => (f : MvPolynomial ι R →+* B) (X i)) ^ (m + 1) = ⊥ := h
    rw [map_orig_pow, h'] at this
    exact (Submodule.mem_bot _).1 this

def jetMap {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') :
    Jet R ι m →ₐ[R] Jet R ι' m :=
  liftJet ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (X i)) =
        Ideal.map (Ideal.Quotient.mk (orig R ι' ^ (m + 1))) (Ideal.span (Set.range φ)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      congr 1
      ext x
      simp
    rw [h1, ← Ideal.map_pow]
    have h2 : Ideal.span (Set.range φ) ^ (m + 1) ≤ orig R ι' ^ (m + 1) :=
      Ideal.pow_right_mono (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hφ i)) _
    refine (Ideal.map_mono h2).trans ?_
    rw [Ideal.map_quotient_self])

theorem X_mem_orig {ι' : Type} (i : ι') : (X i : MvPolynomial ι' R) ∈ orig R ι' :=
  Ideal.subset_span ⟨i, rfl⟩

def jetIn {K : Type} (k : K) : Jet R ι m →ₐ[R] Jet R (K × ι) m :=
  jetMap (fun i => X (k, i)) fun i => X_mem_orig (k, i)

def jetScale (c : ι → R) : Jet R ι m →ₐ[R] Jet R ι m :=
  jetMap (fun i => C (c i) * X i) fun i => Ideal.mul_mem_left _ _ (X_mem_orig i)

def jetAug : Jet R ι m →ₐ[R] R :=
  liftJet (aeval fun _ => (0 : R)) (by
    have : Ideal.span (Set.range fun i => (aeval fun _ => (0 : R)) (X i : MvPolynomial ι R)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      simp
    rw [this, Ideal.bot_pow (Nat.succ_ne_zero m)])

def jetTan [DecidableEq ι] (ℓ : ι) : Jet R ι (m + 1) →ₐ[R] DualNumber R :=
  liftJet (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (X i : MvPolynomial ι R))
        ≤ Ideal.span {(DualNumber.eps : DualNumber R)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i = ℓ
      · simp [h]
      · simp [h]
    refine (Ideal.pow_right_mono h1 _).trans ?_
    refine (Ideal.pow_le_pow_right (show 2 ≤ m + 1 + 1 by omega)).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

theorem sub_const_mem_orig (P : MvPolynomial ι R) :
    P - C (MvPolynomial.constantCoeff P) ∈ orig R ι := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp
  next p q hp hq =>
    have h : p + q - C (MvPolynomial.constantCoeff (p + q)) =
        (p - C (MvPolynomial.constantCoeff p)) + (q - C (MvPolynomial.constantCoeff q)) := by
      simp only [map_add (f := _)]
      ring
    rw [h]
    exact Ideal.add_mem _ hp hq
  next p n _ =>
    simp only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (X_mem_orig n)

def degLE [Fintype ι] [DecidableEq ι] (m : ℕ) : Finset (ι →₀ ℕ) :=
  ((Finset.univ : Finset (ι → Fin (m + 1))).image fun v =>
    Finsupp.equivFunOnFinite.symm fun i => (v i : ℕ)).filter fun e => (e.sum fun _ k => k) ≤ m

def psTrunc [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : MvPolynomial ι R :=
  ∑ e ∈ degLE m, monomial e (MvPowerSeries.coeff e f)

def psJet [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : Jet R ι m :=
  Ideal.Quotient.mk _ (psTrunc m f)

def jetSubstPS {ι' : Type} [Fintype ι'] [DecidableEq ι'] (φ : ι → MvPowerSeries ι' R) : Jet R ι m →ₐ[R] Jet R ι' m :=
  jetMap (fun i => psTrunc m (φ i) - C (MvPolynomial.constantCoeff (psTrunc m (φ i))))
    fun i => sub_const_mem_orig _

def jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

end Formalism.L2.Pj
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

namespace HeckeJ

open scoped TensorProduct

section Gen

variable {L : Type*} [Field L] (σ₀ : L →+* ℂ) {WL : Type*} [AddCommGroup WL] [Module L WL]
  {H F : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup F] [Module ℂ F]
  (j : WL →ₛₗ[σ₀] H) (em : H →ₗ[ℂ] F) (TF : F →ₗ[ℂ] F) (c : ℂ)

def IsHkJ (T : WL →ₗ[L] WL) : Prop := ∀ x, em (j (T x)) = c • TF (em (j x))


variable {σ₀ j em TF c}

variable (σ₀ j em TF c)

variable {σ₀ j em TF c}

end Gen

section Inj

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

end Inj

end HeckeJ

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj.LocFrM

open TensorProduct

variable {O : Type*} [CommRing O] [IsLocalRing O] {V : Type*} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]

theorem range_projective (e : Module.End O V) (he : IsIdempotentElem e) :
    Module.Projective O (LinearMap.range e) := by
  refine Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict ?_
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  show e (e y) = e y
  exact LinearMap.congr_fun he y

theorem range_free (e : Module.End O V) (he : IsIdempotentElem e) : Module.Free O (LinearMap.range e) := by
  haveI := range_projective e he
  haveI : Module.FinitePresentation O (LinearMap.range e) := Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

section Split

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

end Formalism.L2.Pj.LocFrM
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

abbrev Letter (T : Type) (r : T → ℕ) (n : ℕ) : Type := Σ σ : T, Fin (r σ) × Fin n

variable {T : Type} (r : T → ℕ) (n : ℕ)

variable (k : Type) [Field k]

def lap (hinv : Matrix (Fin n) (Fin n) k) (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) :
    MvPolynomial (Letter T r n) k →ₗ[k] MvPolynomial (Letter T r n) k :=
  ∑ b, ∑ b', hinv b b' •
    ((pderiv (⟨τ, a, b⟩ : Letter T r n)).toLinearMap ∘ₗ
      (pderiv (⟨τ', a', b'⟩ : Letter T r n)).toLinearMap)

def harmK (cc : T → T) (isX : T → Prop) (hinv : T → Matrix (Fin n) (Fin n) k) :
    Submodule k (MvPolynomial (Letter T r n) k) :=
  ⨅ (τ : T) (_ : isX τ) (a : Fin (r τ)) (a' : Fin (r (cc τ))),
    LinearMap.ker (lap r n k (hinv τ) τ (cc τ) a a')

def rowShift (σ : T) (i i' : Fin (r σ)) (t : k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => open Classical in
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X ℓ + C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ

def RowInv (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ (σ : T) (i i' : Fin (r σ)), i' < i → ∀ t : k, rowShift r n k σ i i' t P = P

def RowDeg (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ m ∈ P.support, ∀ (σ : T) (i : Fin (r σ)), ∑ b : Fin n, m ⟨σ, i, b⟩ = a σ i

def HHa (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) : Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ harmK r n k cc isX (fun _ => 1) ∧ RowInv r n k P ∧ RowDeg r n k a P}

def HaO (O : Subring k) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ HHa r n k cc isX a ∧ ∀ m, P.coeff m ∈ O}

end Formalism.L2.Pj
end
end

section

set_option autoImplicit false

noncomputable section

open Polynomial IsLocalRing

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem mem_adjoin_mod (α : B) (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X])
    (hβ : Irreducible (aeval α f)) :
    ∀ (n : ℕ) (b : B), ∃ s ∈ Algebra.adjoin A {α}, ∃ c : B, b = s + aeval α f ^ n * c := by
  have hra : ∀ G : A[X], residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
    intro G
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1
    all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)
  intro n
  induction n with
  | zero => intro b; exact ⟨0, Subalgebra.zero_mem _, b, by simp⟩
  | succ n ih =>
    intro b
    obtain ⟨s, hs, c, rfl⟩ := ih b
    have hc : residue B c ∈ Algebra.adjoin (ResidueField A) {residue B α} := by
      rw [hres]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨p, hp⟩ := hc
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective p
    have hm : c - aeval α P ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hra]
      rw [← hp]
      exact sub_self _
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hβ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c', hc'⟩ := hm
    have hα : aeval α f ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ f
    have hP : aeval α P ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ P
    refine ⟨s + aeval α f ^ n * aeval α P, ?_, c', ?_⟩
    · exact Subalgebra.add_mem _ hs (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hα n) hP)
    · have e : c = aeval α P + c' * aeval α f := by rw [hc']; ring
      rw [e]
      ring

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem adjoin_eq_top_of_gen [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (α : B)
    (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X]) (hβ : Irreducible (aeval α f)) :
    Algebra.adjoin A {α} = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact hϖ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hβ
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have key : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule (Algebra.adjoin A {α}) ⊔ (maximalIdeal A) • ⊤ := by
    intro b _
    obtain ⟨s, hs, c, hc⟩ := mem_adjoin_mod α hres f hβ e b
    have e1 : b = s + ϖ • ((↑u⁻¹ : B) * c) := by
      rw [hc, Algebra.smul_def, hu]
      congr 1
      rw [mul_comm (↑u : B), mul_assoc, ← mul_assoc (↑u : B), Units.mul_inv, one_mul]
    rw [e1]
    exact Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).mpr hs)
      (Submodule.smul_mem_smul hϖm Submodule.mem_top)
  have hfg : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  rw [eq_top_iff]
  intro x _
  exact (Subalgebra.mem_toSubmodule _).mp (hle Submodule.mem_top)

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem residue_aeval (α : B) (G : A[X]) :
    residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)

theorem adjoin_residue_gen [Finite (ResidueField B)] :
    ∃ γ : ResidueField B, Algebra.adjoin (ResidueField A) {γ} = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ResidueField B)ˣ)
  refine ⟨(g : ResidueField B), ?_⟩
  rw [eq_top_iff]
  intro x _
  by_cases hx : x = 0
  · rw [hx]; exact Subalgebra.zero_mem _
  · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
    have e : x = (g : ResidueField B) ^ n := by
      rw [← Units.val_pow_eq_pow_val, show g ^ n = Units.mk0 x hx from hn, Units.val_mk0]
    rw [e]
    exact Subalgebra.pow_mem (Algebra.adjoin (ResidueField A) {(g : ResidueField B)})
      (Algebra.subset_adjoin (Set.mem_singleton _)) n

theorem exists_adjoin_eq_top [Module.Finite A B] [Finite (ResidueField A)]
    (hinj : Function.Injective (algebraMap A B)) : ∃ α : B, Algebra.adjoin A {α} = ⊤ := by
  haveI : Finite (ResidueField B) := IsLocalRing.ResidueField.finite_of_finite (R := A) ‹_›
  obtain ⟨γ, hγ⟩ := adjoin_residue_gen (A := A) (B := B)
  obtain ⟨α0, rfl⟩ := IsLocalRing.residue_surjective γ
  have hint : IsIntegral (ResidueField A) (residue B α0) := IsIntegral.of_finite _ _
  have hsep : (minpoly (ResidueField A) (residue B α0)).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  have hq0 : aeval (residue B α0) (minpoly (ResidueField A) (residue B α0)) = 0 := minpoly.aeval _ _
  have hq' : aeval (residue B α0) (derivative (minpoly (ResidueField A) (residue B α0))) ≠ 0 :=
    hsep.aeval_derivative_ne_zero hq0
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective
    (minpoly (ResidueField A) (residue B α0))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hm : aeval α0 P ∈ maximalIdeal B := by
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, hP, hq0]
  have hd : IsUnit (aeval α0 (derivative P)) := by
    by_contra hnu
    have h3 : aeval α0 (derivative P) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, ← Polynomial.derivative_map, hP] at h3
    exact hq' h3
  by_cases h2 : aeval α0 P ∈ Ideal.span {π ^ 2}
  · refine ⟨α0 + π, adjoin_eq_top_of_gen hinj (α0 + π) ?_ P ?_⟩
    · have hr : residue B π = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr (hmax ▸ Ideal.mem_span_singleton_self π)
      rw [map_add (f := _), hr, add_zero]; exact hγ
    · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h2
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.map (algebraMap A B)) α0 π
      have e : aeval (α0 + π) P = π * (aeval α0 (derivative P) + π * (t + k)) := by
        simp only [Polynomial.aeval_def, ← Polynomial.eval_map] at ht ⊢
        rw [← Polynomial.derivative_map, hk, ← ht]
        ring
      have hv : IsUnit (aeval α0 (derivative P) + π * (t + k)) := by
        by_contra hnu
        have h1 : aeval α0 (derivative P) + π * (t + k) ∈ maximalIdeal B :=
          (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have h3 : π * (t + k) ∈ maximalIdeal B := by
          rw [hmax]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
        have h4 : aeval α0 (derivative P) ∈ maximalIdeal B := by
          simpa using Ideal.sub_mem _ h1 h3
        exact (IsLocalRing.mem_maximalIdeal _).mp h4 hd
      rw [e]
      exact (irreducible_mul_isUnit hv).mpr hπ
  · refine ⟨α0, adjoin_eq_top_of_gen hinj α0 hγ P ?_⟩
    rw [hmax] at hm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hm
    have hwu : IsUnit w := by
      by_contra hnu
      apply h2
      have h5 : w ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hmax, Ideal.mem_span_singleton'] at h5
      obtain ⟨v, hv⟩ := h5
      rw [Ideal.mem_span_singleton']
      exact ⟨v, by rw [← hw, ← hv]; ring⟩
    rw [← hw, mul_comm]
    exact (irreducible_mul_isUnit hwu).mpr hπ

end Formalism.L2.Pj.AvAlg
end
end
