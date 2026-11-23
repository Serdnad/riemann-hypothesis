module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle108
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle022
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRed

theorem bc_val {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (g : GL (Fin n) A) :
    (Formalism.UG.bc f g : GL (Fin n) B).val = f.mapMatrix g.val := rfl

theorem eq_one_of_reduction_eq_one {E R k : Type} [Field E] [CommRing R] [CommRing k]
    [Nontrivial k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) {n m : ℕ} (hm : IsUnit (m : k))
    (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ^ m = 1)
    (hxy : Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x) (hy : Formalism.UG.bc φ y = 1) : u = 1 := by
  have hU : u.val ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have h1 : (u.val - 1) * ∑ j ∈ Finset.range m, u.val ^ j = 0 := by
    rw [mul_geom_sum, hU, sub_self]
  have hj : ∀ j : ℕ, S.subtype.mapMatrix (y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (u.val ^ j) * x.val := by
    intro j
    have h : Formalism.UG.bc S.subtype (y ^ j) = x⁻¹ * Formalism.UG.bc ι (u ^ j) * x := by
      rw [map_pow, map_pow, hxy]
      simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := j)
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, bc_val, bc_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val] at h'
    exact h'
  have hsum : S.subtype.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j)
      = (x⁻¹).val * ι.mapMatrix (∑ j ∈ Finset.range m, u.val ^ j) * x.val := by

    rw [map_sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hj j
  have hY : φ.mapMatrix y.val = 1 := by
    rw [← bc_val, hy, Units.val_one]
  have hk : φ.mapMatrix (∑ j ∈ Finset.range m, y.val ^ j) = (m : k) • 1 := by

    rw [map_sum]
    simp only [map_pow, hY, one_pow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have hd : (∑ j ∈ Finset.range m, u.val ^ j).det ≠ 0 := by
    intro h0
    have h2 : S.subtype (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := by
      rw [RingHom.map_det, hsum, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, h0, map_zero,
        mul_zero, zero_mul]
    have h3 : (∑ j ∈ Finset.range m, y.val ^ j).det = 0 := Subtype.ext h2
    have h4 := RingHom.map_det φ (∑ j ∈ Finset.range m, y.val ^ j)
    rw [h3, map_zero, hk, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    exact (hm.pow _).ne_zero h4.symm
  have hunit : IsUnit (∑ j ∈ Finset.range m, u.val ^ j) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hd)
  have h5 : u.val - 1 = 0 := (hunit.mul_left_eq_zero).1 h1
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h5)

theorem eq_one_of_unipotent_reduction :
    ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  intro E R k _ _ _ _ S ι φ p n hp hchar hlt u x y hu hxy hnil
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Units.ext (Subsingleton.elim _ _)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one (R := k) hp.ne_one
  obtain ⟨a, ha⟩ := hnil
  have hpa : (Formalism.UG.bc φ y) ^ (p ^ a) = 1 := by
    apply Units.ext
    have h1 : ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) ^ (p ^ a) = 0 :=
      pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le ha
    rw [sub_pow_char_pow_of_commute p a (Commute.one_right _), one_pow, sub_eq_zero] at h1
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.orderOf_pos.ne' p hp.ne_one
  apply GlobalTheory.BadShare.gl_eq_one_of_pow_prime_pow E n p hp hlt u (a + b)
  refine eq_one_of_reduction_eq_one S ι φ (m := m) ((CharP.isUnit_natCast_iff hp).2 hm)
    _ x (y ^ p ^ (a + b)) ?_ ?_ ?_
  · rw [← pow_mul, pow_add, mul_assoc, ← hbm, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, map_pow, hxy]
    simpa using conj_pow (a := x⁻¹) (b := Formalism.UG.bc ι u) (i := p ^ (a + b))
  · rw [map_pow, pow_add, pow_mul, hpa, one_pow]

end GlobalTheory.UnipRed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FreeOfCharacter

noncomputable def freeRep (P : Type) [Group P] (N : ℕ) :
    Representation ℂ P (Fin N → MonoidAlgebra ℂ P) where
  toFun g :=
    { toFun := fun x => (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [← MonoidAlgebra.one_def]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [smul_smul, MonoidAlgebra.single_mul_single]

theorem freeRep_apply {P : Type} [Group P] {N : ℕ} (g : P) (x : Fin N → MonoidAlgebra ℂ P) :
    freeRep P N g x = (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x := rfl

theorem trace_freeRep {P : Type} [Group P] [Finite P] (N : ℕ) {g : P} (hg : g ≠ 1) :
    LinearMap.trace ℂ _ (freeRep P N g) = 0 := by
  classical
  haveI := Fintype.ofFinite P
  let b := Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ
  have hb : ∀ (j : Fin N) (q : P), b ⟨j, q⟩ = Pi.single j (MonoidAlgebra.single q 1) := by
    intro j q
    simp [b, Pi.basis_apply]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨j, p⟩ := i
  have hmove : freeRep P N g (b ⟨j, p⟩) = b ⟨j, g * p⟩ := by
    rw [hb, hb, freeRep_apply]
    funext k
    by_cases hk : k = j
    · subst hk
      simp [MonoidAlgebra.single_mul_single]
    · simp [hk]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hmove, b.repr_self, Finsupp.single_apply, if_neg]
  intro h
  rw [Sigma.mk.inj_iff, heq_iff_eq] at h
  exact hg (mul_right_cancel (h.2.trans (one_mul p).symm))

theorem finrank_free (P : Type) [Group P] [Finite P] (N : ℕ) :
    Module.finrank ℂ (Fin N → MonoidAlgebra ℂ P) = Nat.card P * N := by
  haveI := Fintype.ofFinite P
  rw [Module.finrank_eq_card_basis (Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ),
    Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

theorem free_of_trace_eq_zero : ∀ (P M : Type) [Group P] [Finite P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ P M), (∀ g : P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M ∧ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ P] (Fin N → MonoidAlgebra ℂ P)) := by
  intro P M _ _ _ _ _ ρ hρ
  classical
  haveI := Fintype.ofFinite P
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  haveI : Invertible (Nat.card P : ℂ) := invertibleOfNonzero hcard

  have hz : ∀ g : P, g ≠ 1 → ρ.character g = 0 := hρ
  have havg := Representation.card_inv_mul_sum_char_eq_finrank ρ
  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => hz g hg) (by simp),
    Representation.char_one] at havg
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M := by
    refine ⟨Module.finrank ℂ (Representation.invariants ρ), ?_⟩
    have hc : ((Nat.card P * Module.finrank ℂ (Representation.invariants ρ) : ℕ) : ℂ) =
        (Module.finrank ℂ M : ℂ) := by
      push_cast
      rw [← havg, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    exact_mod_cast hc
  refine ⟨N, hN, ?_⟩
  haveI : FiniteDimensional ℂ (MonoidAlgebra ℂ P) :=
    Module.Finite.of_basis (MonoidAlgebra.basis P ℂ)

  have hχ : ρ.character = (freeRep P N).character := by
    funext g
    by_cases hg : g = 1
    · subst hg
      rw [Representation.char_one, Representation.char_one, finrank_free, hN]
    · exact (hz g hg).trans (trace_freeRep N hg).symm
  obtain ⟨e⟩ := GlobalTheory.CharacterDetermines.nonempty_equiv_of_character_eq P M
    (Fin N → MonoidAlgebra ℂ P) ρ (freeRep P N) hχ

  have hlin : ∀ (r : MonoidAlgebra ℂ P) (x : M),
      e.toLinearEquiv (ρ.asAlgebraHom r x) = (freeRep P N).asAlgebraHom r (e.toLinearEquiv x) := by
    intro r x
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      simp only [Representation.asAlgebraHom_of]
      exact e.toIntertwiningMap.isIntertwining _ _ g x
    | add f f' hf hf' => simp only [map_add (f := _), LinearMap.add_apply, hf, hf']
    | smul c f hf => simp only [map_smul, LinearMap.smul_apply, hf]

  have hact : ∀ (r : MonoidAlgebra ℂ P) (y : Fin N → MonoidAlgebra ℂ P),
      (freeRep P N).asAlgebraHom r y = r • y := by
    intro r y
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [Representation.asAlgebraHom_of, freeRep_apply, MonoidAlgebra.of_apply]
    | add f f' hf hf' => rw [map_add (f := _), LinearMap.add_apply, hf, hf', add_smul]
    | smul c f hf => rw [map_smul, LinearMap.smul_apply, hf, smul_assoc]
  exact ⟨{ (ρ.asModuleEquiv.trans e.toLinearEquiv).toAddEquiv with
    map_smul' := fun r x => by
      change e.toLinearEquiv (ρ.asModuleEquiv (r • x)) = r • e.toLinearEquiv (ρ.asModuleEquiv x)
      rw [Representation.asModuleEquiv_map_smul, hlin, hact] }⟩

end GlobalTheory.FreeOfCharacter
end
