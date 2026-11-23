module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.DualLattices.FormalChartAtZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.ResField

variable {C : Type} [Field C] (V : VF C)

theorem nonneg (x : V.RR) : 0 ≤ V.v (x : C) := by
  have h : ((0 : ℝ) : WithTop ℝ) ≤ V.v (x : C) := x.2
  simpa using h

def mm : Ideal V.RR where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {x y} hx hy => V.v.map_lt_add hx hy
  zero_mem' := by simp [VF.MM]
  smul_mem' := fun c x hx => by
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left (nonneg V c))

theorem mm_isMaximal : (mm V).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x _ hx hxJ => ?_⟩
  · have h1 : 0 < V.v ((1 : V.RR) : C) := h
    simp at h1
  · have hx' : ¬ 0 < V.v (x : C) := hx
    have hx0 : V.v (x : C) = 0 := le_antisymm (not_lt.mp hx') (nonneg V x)
    have hne : (x : C) ≠ 0 := by
      intro h
      rw [h, AddValuation.map_zero] at hx0
      exact WithTop.top_ne_zero hx0
    have hinv : ((0 : ℝ) : WithTop ℝ) ≤ V.v ((x : C)⁻¹) := by
      rw [AddValuation.map_inv, hx0]
      simp
    let y : V.RR := ⟨(x : C)⁻¹, hinv⟩
    have hyx : y * x = 1 := Subtype.ext (by simp [y, hne])
    rw [← hyx]
    exact J.mul_mem_left y hxJ

theorem integers : (AddValuation.toValuation V.v).Integers V.RR :=
  Valuation.integer.integers (AddValuation.toValuation V.v)

theorem isAlgClosed_of_surjective [IsAlgClosed C] {Ω : Type} [Field Ω] (ρ : V.RR →+* Ω)
    (hρ : Function.Surjective ρ) : IsAlgClosed Ω := by
  refine IsAlgClosed.of_exists_root Ω fun p hp hirr => ?_
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective ρ hρ p)) hp
  have hdeg : (q.map (algebraMap V.RR C)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (integers V).hom_inj, hqdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral V.RR z := ⟨q, hqmon, hz⟩
  obtain ⟨y, rfl⟩ := (integers V).exists_of_le_one ((integers V).mem_of_integral hint)
  rw [Polynomial.eval₂_at_apply] at hz
  have hy : q.eval y = 0 := (integers V).hom_inj (by rw [hz, map_zero])
  refine ⟨ρ y, ?_⟩
  rw [← hqmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

theorem exists_residueField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  intro C _ V _
  have := mm_isMaximal V
  let _ : Field (V.RR ⧸ mm V) := Ideal.Quotient.field (mm V)
  have hl : ((V.l : ℕ) : V.RR ⧸ mm V) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (mm V)), Ideal.Quotient.eq_zero_iff_mem]
    show 0 < V.v (((V.l : ℕ) : V.RR) : C)
    have hc : (((V.l : ℕ) : V.RR) : C) = ((V.l : ℕ) : C) := by simp
    rw [hc, V.v_l]
    exact zero_lt_one
  have : CharP (V.RR ⧸ mm V) V.l := (CharP.charP_iff_prime_eq_zero V.l_prime).2 hl
  exact ⟨V.RR ⧸ mm V, inferInstance, isAlgClosed_of_surjective V _ Ideal.Quotient.mk_surjective,
    inferInstance, Ideal.Quotient.mk (mm V), fun x => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.AlphaPair.ResField
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem embOK_exists_ringHom :
    ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  intro T C _ _ V ι' h
  have hnn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
    intro a
    unfold vV
    by_cases ha : valV T.V (algebraMap T.V T.Fr a) = 0
    · simp [ha]
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have := (WithZero.log_le_log ha one_ne_zero).2 h1
    simp at this
    omega
  have hl0 : vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by
    intro h0
    have hl : ((V.l : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 V.l_prime.ne_zero
    have := h _ hl
    rw [map_natCast, V.v_l, h0] at this
    simp at this
  have hl : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have h0 := hnn (V.l : T.V)
    rw [map_natCast] at h0
    exact_mod_cast lt_of_le_of_ne h0 hl0.symm
  have hR : ∀ x : T.V, (ι'.comp (algebraMap T.V T.Fr)) x ∈ V.RR := by
    intro x
    show V.Ge 0 (ι' (algebraMap T.V T.Fr x))
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero]; exact VF.Ge.zero 0
    unfold VF.Ge
    rw [h _ h0]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast hnn x) hl.le)
  refine ⟨(ι'.comp (algebraMap T.V T.Fr)).codRestrict V.RR hR, fun x => rfl, fun x hx => ?_⟩
  have key : ((0 : ℝ) : WithTop ℝ) < V.v (ι' (algebraMap T.V T.Fr x)) := by
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero, V.v.map_zero]; exact WithTop.coe_lt_top _
    rw [h _ h0]
    have h2 : valV T.V (algebraMap T.V T.Fr x) < 1 := by
      unfold valV
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hx
    have h3 := (WithZero.log_lt_log (valV_ne_zero h0) one_ne_zero).2 h2
    have h4 : 0 < vV T.V (algebraMap T.V T.Fr x) := by
      simp at h3
      unfold vV
      omega
    exact WithTop.coe_lt_coe.2 (div_pos (by exact_mod_cast h4) hl)
  exact key

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaChar
open Polynomial

theorem poly_eq_one {Ω : Type} [Field Ω] (p : ℕ) [CharP Ω p] (w : Polynomial Ω) (c : Ω)
    (hd : w.degree < p) (h0 : w.coeff 0 = 1) (h : derivative w = C c * w) : w = 1 := by
  have hw : w ≠ 0 := by rintro rfl; simp at h0
  have hc : c = 0 := by
    by_contra hc
    have h1 := degree_derivative_lt hw
    rw [h, degree_C_mul hc] at h1
    exact lt_irrefl _ h1
  rw [hc, C_0, zero_mul] at h
  ext n
  rcases n with _ | n
  · simpa using h0
  · simp only [coeff_one, Nat.succ_ne_zero, ite_false]
    by_cases hn : n + 1 < p
    · have h2 := congrArg (fun q : Polynomial Ω => q.coeff n) h
      simp only [coeff_derivative, coeff_zero] at h2
      have h3 : ((n : Ω) + 1) ≠ 0 := by
        intro h3
        have : ((n + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h3
        rw [CharP.cast_eq_zero_iff Ω p] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      exact (mul_eq_zero.1 h2).resolve_right h3
    · apply coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hd (by exact_mod_cast (not_lt.1 hn))

theorem char_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (u : ∀ (A : Type) [CommRing A] [Algebra Ω A], A → Aˣ), (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 → u B (f a) = Units.map (f : A →* B) (u A a)) → (∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → u A (a + a') = u A a * u A a') → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → u A a = 1 := by
  intro Ω _ p hp _ u hnat hadd
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp0 : p ≠ 0 := by omega
  have hm : (X ^ p : Polynomial Ω).Monic := monic_X_pow p
  let R := AdjoinRoot (X ^ p : Polynomial Ω)
  let t : R := AdjoinRoot.root (X ^ p : Polynomial Ω)
  have ht : t ^ p = 0 := by
    have := AdjoinRoot.mk_self (f := (X ^ p : Polynomial Ω))
    rwa [map_pow, AdjoinRoot.mk_X] at this
  obtain ⟨w0, hw0⟩ := AdjoinRoot.mk_surjective (g := (X ^ p : Polynomial Ω)) (u R t : R)
  let w : Polynomial Ω := w0 %ₘ (X ^ p)
  have hwd : w.degree < p := by
    have := degree_modByMonic_lt w0 hm
    rwa [degree_X_pow] at this
  have hw : aeval t w = (u R t : R) := by
    rw [← hw0, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_mk]
    have := modByMonic_add_div w0 (X ^ p)
    exact ⟨-(w0 /ₘ X ^ p), by simp only [w]; linear_combination this⟩
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 →
      (u A a : A) = aeval a w := by
    intro A _ _ a ha
    let f : R →ₐ[Ω] A := Ideal.Quotient.liftₐ (Ideal.span {(X ^ p : Polynomial Ω)}) (aeval a) (by
      intro q hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hq
      simp [ha])
    have hf : f t = a := by
      change aeval a (X : Polynomial Ω) = a
      simp
    have h1 := hnat R A f t ht
    rw [hf] at h1
    rw [h1, ← hf, aeval_algHom_apply, hw]
    rfl
  have h0 : w.coeff 0 = 1 := by
    have h1 := hadd Ω 0 0 (zero_pow hp0) (zero_pow hp0)
    rw [add_zero, left_eq_mul] at h1
    have h2 := key Ω 0 (zero_pow hp0)
    rw [h1] at h2
    rw [coeff_zero_eq_aeval_zero, ← h2]; rfl
  have hder : derivative w = C ((derivative w).coeff 0) * w := by
    let D := DualNumber R
    let e : D := DualNumber.eps
    let j : R →ₐ[Ω] D := TrivSqZeroExt.inlAlgHom Ω R R
    have he : e ^ 2 = 0 := by rw [pow_two]; exact DualNumber.eps_mul_eps
    have hep : e ^ p = 0 := pow_eq_zero_of_le hp2 he
    have hs : (j t) ^ p = 0 := by rw [← map_pow, ht, map_zero]
    have hpD : (p : D) = 0 := by
      rw [← map_natCast (algebraMap Ω D), CharP.cast_eq_zero, map_zero]
    have hse : (j t + e) ^ p = 0 := by
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (j t) e
      rw [hr, hs, hep, hpD]; simp
    have h1 := congrArg Units.val (hadd D (j t) e hs hep)
    rw [Units.val_mul, key D _ hse, key D _ hs, key D _ hep,
      aeval_add_of_sq_eq_zero _ _ _ he] at h1
    have h2 : aeval e w = 1 + algebraMap Ω D ((derivative w).coeff 0) * e := by
      have := aeval_add_of_sq_eq_zero w 0 e he
      rw [zero_add] at this
      rw [this, ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero', h0, map_one]
    rw [h2, aeval_algHom_apply, aeval_algHom_apply, ← j.commutes, mul_add, _root_.mul_one,
      add_right_inj, ← _root_.mul_assoc, ← map_mul] at h1
    have hsnd : ∀ x : R, TrivSqZeroExt.snd (j x * e) = x := by
      intro x
      change TrivSqZeroExt.snd ((TrivSqZeroExt.inl x : DualNumber R) * DualNumber.eps) = x
      rw [DualNumber.snd_mul]; simp
    have h3 := congrArg TrivSqZeroExt.snd h1
    rw [hsnd, hsnd] at h3
    have h4 : aeval t (derivative w - C ((derivative w).coeff 0) * w) = 0 := by
      rw [map_sub, map_mul, aeval_C, h3]; ring
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h4
    have h5 := eq_zero_of_dvd_of_degree_lt h4 (by
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_derivative_le hwd
      · rw [← smul_eq_C_mul]; exact lt_of_le_of_lt (degree_smul_le _ _) hwd)
    exact sub_eq_zero.1 h5
  have hone := poly_eq_one p w _ hwd h0 hder
  intro A _ _ a ha
  ext
  rw [key A a ha, hone]; simp

end GlobalTheory.AlphaChar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_pth_root_torus_point_nilpotent_augmented_ext : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ χ : Multiplicative X →* Aˣ, (∀ x, π (χ x).val = 1) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω) (χ' : Multiplicative X →* A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧ (∀ x, π' (χ' x).val = 1) ∧ χ' ^ p = (Units.map (f : A →* A')).comp χ := by
  first | exact @GlobalTheory.TorusRoot.exists_root_character | exact GlobalTheory.TorusRoot.exists_root_character | (intros; apply GlobalTheory.TorusRoot.exists_root_character <;> assumption)
end
