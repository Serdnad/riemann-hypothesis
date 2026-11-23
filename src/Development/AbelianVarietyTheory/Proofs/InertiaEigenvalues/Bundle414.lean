module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle402
public import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.Polynomial.Roots
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.aeval_eq_zero_low_coeff_three_nilpotents : ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ) (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 → (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) → (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) → MvPolynomial.aeval ξ F = 0 := by
  first | exact @GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | exact GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | (intros; apply GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory

theorem localSubalgebra_eval_sub_mem_maximalIdeal {X O : Type} [CommRing O] [IsLocalRing O]
    (T : Subalgebra O (X → O)) [IsLocalRing T] {f : X → O} (hf : f ∈ T) (x y : X) :
    f x - f y ∈ IsLocalRing.maximalIdeal O := by
  classical
  haveI : (IsLocalRing.maximalIdeal O).IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  let ψ : X → (T →+* O ⧸ IsLocalRing.maximalIdeal O) := fun z =>
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp
      ((Pi.evalRingHom (fun _ : X => O) z).comp (T.val : T →+* (X → O)))
  have hψ : ∀ z (g : T), ψ z g = Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) ((g : X → O) z) :=
    fun _ _ => rfl
  have hsurj : ∀ z, Function.Surjective (ψ z) := by
    intro z q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨algebraMap O T a, by rw [hψ]; rfl⟩
  have hker : ∀ z, RingHom.ker (ψ z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hg : (⟨f, hf⟩ - algebraMap O T (f y) : T) ∈ RingHom.ker (ψ y) := by
    rw [RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem]
    simp
  rw [hker y, ← hker x, RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem] at hg
  simpa using hg

theorem hensel_roots_of_local_family : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] {t : ℕ} (T : Subalgebra O (X → O)), IsLocalRing T → ∀ (P : X → Polynomial O), (∀ j, (fun x => (P x).coeff j) ∈ T) → (∀ x, (P x).Monic ∧ (P x).natDegree = t) → ∀ (π : X) (d : Fin t → O), (∀ a b, a ≠ b → IsUnit (d a - d b)) → P π = ∏ c, (Polynomial.X - Polynomial.C (d c)) → ∀ x, ∃ β : Fin t → O, Function.Injective β ∧ P x = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  intro X O _ _ _ _ t T hT P hcoeff hdeg π d hd hπ x
  have hmap : (P x).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) =
      (P π).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) := by
    ext j
    simp only [Polynomial.coeff_map]
    rw [Ideal.Quotient.eq]
    exact localSubalgebra_eval_sub_mem_maximalIdeal T (hcoeff j) x π
  have hroot : ∀ c, ∃ b, (P x).IsRoot b ∧ b - d c ∈ IsLocalRing.maximalIdeal O := by
    intro c
    apply HenselianRing.is_henselian (P x) (hdeg x).1 (d c)
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
        hmap, hπ, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ c) (by simp), map_zero]
    · rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map, hmap,
        Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      apply IsUnit.map
      rw [hπ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero,
        Polynomial.eval_prod]
      have : ∀ a ∈ Finset.univ.erase c, IsUnit (d c - d a) := fun a ha =>
        hd c a (Finset.ne_of_mem_erase ha).symm
      exact IsUnit.prod_iff.2 this
  choose β hβ hβm using hroot
  have hinj : Function.Injective β := by
    intro a b hab
    by_contra hne
    have hmem : d b - d a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ (hβm a) (hβm b)
      rw [hab] at this
      convert this using 1; ring
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (hd b a (Ne.symm hne))
  refine ⟨β, hinj, ?_⟩
  have hx0 : P x ≠ 0 := (hdeg x).1.ne_zero
  have hle : (Finset.univ.val.map β) ≤ (P x).roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro r hr
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hr
    exact (Polynomial.mem_roots hx0).mpr (hβ c)
  have hcard : (P x).roots.card ≤ (Finset.univ.val.map β).card := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, ← (hdeg x).2]
    exact Polynomial.card_roots' _
  have heq : Finset.univ.val.map β = (P x).roots := Multiset.eq_of_le_of_card_le hle hcard
  have hrc : (P x).roots.card = (P x).natDegree := by
    rw [← heq, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, (hdeg x).2]
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hdeg x).1 hrc, ← heq,
    Multiset.map_map]
  rfl

end GlobalTheory
end
