module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (aff y 0) = aff (Units.map (f : R →* S) y) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mem {R : Type} [CommRing R] (y : Rˣ) : aff y 0 ∈ mirab R := by
  change Matrix.vecMul _ _ = _
  ext i
  fin_cases i <;> simp [aff, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

open UpperTheory.V.Af.GlobalFixedVectors Matrix in
theorem UpperTheory.V.Sd.Hm.fixunit :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (φ : TR.Sm F 2), IsOpen {k | TR.finRep F 2 k φ = φ} →
        ∀ c : Pl F → ℕ, (∀ w, φ ∈ Hi.fixd (locSm F w) (K1 w (c w))) → ∀ u : (Af F)ˣ, (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) →
        ∀ g, φ.1 (g * finGL F 2 (aff u 0)) = φ.1 g := by
  classical
  intro F _ _ _ φ hop c hc u hu g
  have key : ∀ S : Finset (Pl F),
      (∀ k ∈ KAway 2 1 S, (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) → TR.finRep F 2 k φ = φ) →
      (∀ k ∈ KAway 2 1 ∅, (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) → TR.finRep F 2 k φ = φ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      intro h
      refine ih fun k hk hl => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : TR.finRep F 2 (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) φ = φ := hc w _ (hl w)
      have h4 := h _ h2 fun v => by
        by_cases hv : v = w
        · subst hv; simp [pLoc_locGL]
        · simpa [pLoc_locGL_of_ne hv] using hl v
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (hop.mem_nhds (by simp))
  have hi : ∀ w, Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) = 1 := fun w => by
    have : Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) * Valued.v (pLoc F w (u : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rwa [hu, mul_one] at this
  have m1 : ∀ w, pLoc F w (u : Af F) ∈ w.adicCompletionIntegers F := fun w => (hu w).le
  have m2 : ∀ w, pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F) ∈ w.adicCompletionIntegers F := fun w => (hi w).le
  let u0 : (Ohat F)ˣ := ⟨⟨u, mem_Ohat.2 m1⟩, ⟨((u⁻¹ : (Af F)ˣ) : Af F), mem_Ohat.2 m2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  have e := key S (fun k hk _ => hS hk) (aff u 0) (mem_KAway.2 ⟨⟨aff u0 0, ?_, ?_⟩, by simp⟩) fun w => ?_
  · exact congrFun (congrArg Subtype.val e) g
  · haveI : Subsingleton (Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · rw [map_aff]; rfl
  · let u1 : (w.adicCompletionIntegers F)ˣ := ⟨⟨_, m1 w⟩, ⟨_, m2 w⟩,
      Subtype.ext (by change pLoc F w _ * pLoc F w _ = 1; rw [← map_mul, Units.mul_inv, map_one]),
      Subtype.ext (by change pLoc F w _ * pLoc F w _ = 1; rw [← map_mul, Units.inv_mul, map_one])⟩
    refine ⟨aff u1 0, ?_, ?_⟩
    · change GeneralLinearGroup.map _ (aff u1 0) ∈ mirab _
      rw [map_aff]
      exact aff_mem _
    · rw [map_aff, map_aff]
      congr 1
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

private theorem fin_supp' (y : (Af F)ˣ) : Function.HasFiniteMulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖ := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

private theorem abs_reAt [IsTotallyReal F] (v : InfinitePlace F) (x : F) : |reAt v x| = v x ^ v.mult := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  have hm : v.mult = 1 := by simp [InfinitePlace.mult, hv]
  rw [hm, pow_one, reAt, ← InfinitePlace.norm_embedding_eq, ← InfinitePlace.embedding_of_isReal_apply hv,
    Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]

private theorem absF_rat (x : Fˣ) :
    absF (Units.map (algebraMap F (Af F)).toMonoidHom x) = ∏ᶠ w : FinitePlace F, w (x : F) := by
  unfold absF
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
  refine finprod_congr fun w => ?_
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Sd.Hm.absf :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
        (∀ y : (Af F)ˣ, 0 < absF y) ∧ (∀ y z : (Af F)ˣ, absF (y * z) = absF y * absF z) ∧
        (∀ u : (Af F)ˣ, (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → absF u = 1) ∧
        ∀ x : Fˣ, (∏ v, |reAt v (x : F)|) * absF (Units.map (algebraMap F (Af F)).toMonoidHom x) = 1 := by
  intro F _ _ _
  refine ⟨fun y => ?_, fun y z => ?_, fun u hu => ?_, fun x => ?_⟩
  · exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w =>
      norm_pos_iff.2 (y.isUnit.map (pLoc F w)).ne_zero
  · unfold absF
    rw [← finprod_mul_distrib (fin_supp' y) (fin_supp' z)]
    simp
  · exact finprod_eq_one_of_forall_eq_one fun w => nrm_unit (hu w)
  · rw [absF_rat]
    simp only [abs_reAt]
    exact NumberField.prod_abs_eq_one x.ne_zero
end
