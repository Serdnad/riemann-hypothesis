module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Mathlib.FieldTheory.Perfect

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def intO : Submodule O LL := LinearMap.range (Algebra.linearMap O LL)

def Xq (lam : O) (a : ℕ) : Submodule O (LL ⧸ intO (O := O) LL) :=
  LinearMap.ker (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] (LL ⧸ intO (O := O) LL)))

variable {LL}
variable {V V' : Type} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module LL V'] [Module O V']
  [IsScalarTower O LL V']

def scalQ (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') (t : ↥T) :
    (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  (intO (O := O) LL).liftQ (T'.mkQ ∘ₗ (LinearMap.id : LL →ₗ[O] LL).smulRight (j t)) (by
    rintro _ ⟨c, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Algebra.linearMap_apply, algebraMap_smul]
    exact T'.smul_mem c (hj t t.2))

def scalB (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T →ₗ[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' where
  toFun := scalQ T T' j hj
  map_add' t u := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_add]
  map_smul' c t := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_comm s c]

def iotaG (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T ⊗[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  TensorProduct.lift (scalB T T' j hj)

theorem iotaG_tmul (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T')
    (t : ↥T) (s : LL) :
    iotaG T T' j hj (t ⊗ₜ Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • j t) := rfl

end Gen

section Conc

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def iotaW (lam : O) (a k : ℕ) :
    ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ stdG O LL k :=
  iotaG (stdG O LL k) (stdG O LL k) LinearMap.id (fun _ h => h) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

def constOne : LL →ₗ[O] (Fin 1 → LL) := LinearMap.pi fun _ => LinearMap.id

theorem constOne_mem : ∀ v ∈ intO (O := O) LL, constOne (O := O) LL v ∈ stdG O LL 1 := by
  rintro _ ⟨c, rfl⟩
  simp only [constOne, stdG]
  refine ⟨fun _ => c, ?_⟩
  ext i
  simp

def iotaC (lam : O) (a : ℕ) :
    ↥(intO (O := O) LL) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin 1 → LL) ⧸ stdG O LL 1 :=
  iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

variable {LL}

def latOne (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) :
    Lattice (O := O) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ)) where
  T := intO LL
  stable g x hx := by
    obtain ⟨c, rfl⟩ := hx
    refine ⟨((ψ g : Oˣ) : O) * c, ?_⟩
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.linearMap_apply, Algebra.smul_def]
  fg := by
    rw [intO, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL ((intO (O := O) LL : Set LL)) :=
      Submodule.subset_span ⟨1, map_one (algebraMap O LL)⟩
    simpa using Submodule.smul_mem _ x h1

end Conc

end GlobalTheory.UseLoc.Cases

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory

theorem jTil_shift_block : ∀ (l n t : ℕ) (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n t h w η typ U → ∀ (a : ZMod n) (S : Set ℚ), (∀ b : ℤ, ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ S) ∧ (U a).count (b + w a) ≤ 1) → ∀ b : ℤ, (if ((b : ℚ) ∈ S ∨ ∃ c : ℕ, c < t ∧ (b : ℚ) = c) then (1 : ℤ) else 0) = tableLineDegreeTwo.jTil U w t a (b + w a) := by
  intro l n t h w η typ U hS a S hU b
  have hsg : 0 ≤ tableLineDegreeTwo.sg n l h a := by
    unfold tableLineDegreeTwo.sg Formalism.WachCohomologyFacts.V2.sgN
    exact Int.floor_nonneg.mpr (tsum_nonneg fun j => by positivity)
  obtain ⟨_, _, _, hG, hB, _, hT2, _⟩ := hS a
  have hblk : (∃ c : ℕ, c < t ∧ (b : ℚ) = c) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor
    · rintro ⟨c, hc, hbc⟩
      have : b = (c : ℤ) := by exact_mod_cast hbc
      omega
    · rintro ⟨h0, h1⟩
      refine ⟨b.toNat, by omega, ?_⟩
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hwin : ((w a : ℤ) ≤ b + w a ∧ b + w a ≤ (w a : ℤ) + t - 1) ↔ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> omega
  have hc1 := (hU b).2
  have hcS : (b : ℚ) ∈ S → (U a).count (b + w a) = 1 := (hU b).1.2
  have hcN : (b : ℚ) ∉ S → (U a).count (b + w a) = 0 := fun hn => by
    have := mt (hU b).1.1 hn
    omega
  have hboth : (b : ℚ) ∈ S → ¬ (0 ≤ b ∧ b ≤ (t : ℤ) - 1) := by
    rintro hbS ⟨h0, h1⟩
    have hmem : b + (w a : ℤ) ∈ U a := Multiset.count_pos.mp (by rw [hcS hbS]; omega)
    have hlow : b + (w a : ℤ) ∈ tableLineDegreeTwo.lows (typ a) (h a) (η a) (U a) := by
      unfold tableLineDegreeTwo.lows
      rw [Multiset.mem_filter]
      refine ⟨hmem, ?_⟩
      unfold Formalism.WachCohomologyFacts.V2.InWinN
      cases hty : typ a
      · have := hB hty
        simp only [Bool.false_eq_true, if_false]
        constructor <;> omega
      · have := hG hty
        simp only [if_true]
        constructor <;> omega
    have hy : b + (w a : ℤ) ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (w a) t := by
      unfold Formalism.WachCohomologyFacts.Top.GlobalTheory
      rw [Finset.mem_Icc]
      constructor <;> omega
    have := hT2 _ hlow _ hy
    rw [sub_self, abs_zero] at this
    linarith
  unfold tableLineDegreeTwo.jTil
  by_cases hbS : (b : ℚ) ∈ S
  · have hn := hboth hbS
    rw [if_pos (Or.inl hbS), if_neg (by rwa [hwin]), hcS hbS]
    simp
  · rw [hcN hbS]
    by_cases hbl : 0 ≤ b ∧ b ≤ (t : ℤ) - 1
    · rw [if_pos (Or.inr (hblk.2 hbl)), if_pos (hwin.2 hbl)]
      simp
    · rw [if_neg (by rintro (h1 | h1); exact hbS h1; exact hbl (hblk.1 h1)), if_neg (by rwa [hwin])]
      simp

end GlobalTheory
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

theorem exists_diagonal_ringHom_of_letterwise_reductions :
    ∀ (I E F R : Type) [Fintype I] [CommRing E] [CommRing F] [CommRing R] (e : I → E), (∀ i, e i * e i = e i) → (∀ i j, i ≠ j → e i * e j = 0) → ∑ i, e i = 1 → ∀ (p : I → (E →+* F)) (r : E →+* R), (∀ i, Function.Surjective (p i)) → (∀ i x, p i x = 0 → r (e i) * r x = 0) → ∃ κ : F →+* R, ∀ i x, r (e i) * κ (p i x) = r (e i) * r x := by
  intro I E F R _ _ _ _ e hid hort hsum p r hsurj hker
  classical
  choose s hs using hsurj
  have key : ∀ i x y, p i x = p i y → r (e i) * r x = r (e i) * r y := by
    intro i x y h
    have := hker i (x - y) (by rw [map_sub, h, sub_self])
    rw [map_sub, mul_sub] at this
    exact sub_eq_zero.mp this
  have hext : ∀ a b : R, (∀ i, r (e i) * a = r (e i) * b) → a = b := by
    intro a b h
    have h1 : ∑ i, r (e i) = 1 := by rw [← map_sum, hsum, map_one]
    calc a = (∑ i, r (e i)) * a := by rw [h1, one_mul]
      _ = (∑ i, r (e i)) * b := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => h i
      _ = b := by rw [h1, one_mul]
  have hidR : ∀ i, r (e i) * r (e i) = r (e i) := fun i => by rw [← map_mul, hid]
  let k : F → R := fun c => ∑ i, r (e i) * r (s i c)
  have hk0 : ∀ i c, r (e i) * k c = r (e i) * r (s i c) := by
    intro i c
    show r (e i) * ∑ j, r (e j) * r (s j c) = _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [← mul_assoc, hidR]
    · intro j _ hj
      rw [← mul_assoc, ← map_mul, hort i j (Ne.symm hj), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : ∀ i x, r (e i) * k (p i x) = r (e i) * r x := by
    intro i x
    rw [hk0]
    exact key i _ _ (hs i _)
  refine ⟨{ toFun := k, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hk⟩
  · apply hext
    intro i
    have := hk i 1
    rwa [map_one, map_one] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a * s i b)
    rw [map_mul, hs, hs, map_mul] at h
    have ha := hk0 i a
    have hb := hk0 i b
    have hi := hidR i
    rw [h]
    linear_combination (-(k b)) * ha - (r (s i a)) * hb
  · apply hext
    intro i
    have := hk i 0
    rwa [map_zero, map_zero] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a + s i b)
    rw [map_add (f := _), hs, hs, map_add (f := _)] at h
    rw [h, mul_add, mul_add, hk0, hk0]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.NormalSeparable

section SlopeTestRemainingChoices
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem aeval_mem (U : Submodule ℂ H) (S : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, Polynomial.aeval S q u ∈ U := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simpa [Module.algebraMap_end_apply] using U.smul_mem a hu
  · intro p r hp hr u hu
    simpa using U.add_mem (hp u hu) (hr u hu)
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS u hu)

theorem aeval_adj (U : Submodule ℂ H) (S S' : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (S u) v = inner ℂ u (S' v)) (hS' : ∀ u ∈ U, S' u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (Polynomial.aeval S q u) v
      = inner ℂ u (Polynomial.aeval S' (q.map (starRingEnd ℂ)) v) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu v hv
    simp [Module.algebraMap_end_apply, inner_smul_left, inner_smul_right, mul_comm]
  · intro p r hp hr u hu v hv
    simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, inner_add_left, inner_add_right,
      hp u hu v hv, hr u hu v hv]
  · intro n a ih u hu v hv
    have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial ℂ)
        = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
    rw [e]
    generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
    have e2 : (p * Polynomial.X).map (starRingEnd ℂ) = Polynomial.X * p.map (starRingEnd ℂ) := by
      rw [Polynomial.map_mul, Polynomial.map_X, mul_comm]
    rw [e2, map_mul, Polynomial.aeval_X, Module.End.mul_apply, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, ih _ (hS u hu) v hv]
    exact hadj u hu _ (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _ v hv)

theorem aeval_comm (U : Submodule ℂ H) (S B : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hc : ∀ u ∈ U, S (B u) = B (S u)) (q : Polynomial ℂ) :
    ∀ u ∈ U, Polynomial.aeval S q (B u) = B (Polynomial.aeval S q u) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simp [Module.algebraMap_end_apply]
  · intro p r hp hr u hu
    simp only [map_add (f := _), LinearMap.add_apply, hp u hu, hr u hu]
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    simp only [Module.End.mul_apply]
    rw [hc u hu, ih _ (hS u hu)]

theorem normal_sq_zero (U : Submodule ℂ H) (A A' : Module.End ℂ H) (hA : ∀ u ∈ U, A u ∈ U)
    (hA' : ∀ u ∈ U, A' u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (A u) v = inner ℂ u (A' v))
    (hc : ∀ u ∈ U, A (A' u) = A' (A u)) (u : H) (hu : u ∈ U) (h : A (A u) = 0) : A u = 0 := by
  have hw : A u ∈ U := hA u hu
  have h1 : A' (A u) = 0 := by
    have h2 : inner ℂ (A' (A u)) (A' (A u)) = 0 := by
      rw [← hadj _ (hA' _ hw) _ hw, hc _ hw, h, map_zero, inner_zero_left]
    exact inner_self_eq_zero.mp h2
  have h3 : inner ℂ (A u) (A u) = 0 := by
    rw [hadj _ hu _ hw, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h3

end SlopeTestRemainingChoices

theorem minpoly_separable_of_normal : ∀ (K V H : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ : K →+* ℂ) (j : V →ₛₗ[φ] H) (T : Module.End K V) (S S' : Module.End ℂ H), (∀ (n : ℕ) (x : Fin n → V), LinearIndependent K x → LinearIndependent ℂ (fun a => j (x a))) → (∀ x, j (T x) = S (j x)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S' u ∈ Submodule.span ℂ (Set.range j)) → (∀ u ∈ Submodule.span ℂ (Set.range j), ∀ v ∈ Submodule.span ℂ (Set.range j), inner ℂ (S u) v = inner ℂ u (S' v)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S (S' u) = S' (S u)) → (minpoly K T).Separable := by
  intro K V H _ _ _ _ _ _ φ j T S S' hlin hT hS' hadj hc
  haveI : CharZero K := φ.charZero
  set U : Submodule ℂ H := Submodule.span ℂ (Set.range j) with hU
  have hjU : ∀ x, j x ∈ U := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hSU : ∀ u ∈ U, S u ∈ U := by
    have hle : U ≤ U.comap S := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ← hT x]
      exact Submodule.subset_span ⟨T x, rfl⟩
    intro u hu
    exact hle hu
  have hinj : ∀ v : V, j v = 0 → v = 0 := by
    intro v hv
    by_contra hne
    have hli : LinearIndependent K (fun _ : Fin 1 => v) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp only [Fin.sum_univ_one] at hg
      exact (smul_eq_zero.mp hg).resolve_right hne
    have h1 := hlin 1 (fun _ => v) hli
    exact h1.ne_zero 0 (by simpa using hv)
  have htr : ∀ (p : Polynomial K) (x : V),
      j (Polynomial.aeval T p x) = Polynomial.aeval S (p.map φ) (j x) := by
    intro p
    refine Polynomial.induction_on p ?_ ?_ ?_
    · intro a x
      simp [Module.algebraMap_end_apply]
    · intro p r hp hr x
      simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, hp, hr]
    · intro n a ih x
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
      rw [e]
      generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
      rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply, ih, Polynomial.map_mul,
        Polynomial.map_X, map_mul, Polynomial.aeval_X, Module.End.mul_apply, hT]
  have hsq : Squarefree (minpoly K T) := by
    intro q hq
    obtain ⟨r, hr⟩ := hq
    have hp0 : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    have hann : Polynomial.aeval T (q * r) = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.zero_apply]
      apply hinj
      have e1 : Polynomial.aeval T (q * r) x = Polynomial.aeval T q (Polynomial.aeval T r x) := by
        rw [map_mul, Module.End.mul_apply]
      rw [e1, htr]
      have h0 : Polynomial.aeval T q (Polynomial.aeval T q (Polynomial.aeval T r x)) = 0 := by
        have h4 : Polynomial.aeval T (q * q * r) x = 0 := by
          rw [← hr, minpoly.aeval, LinearMap.zero_apply]
        simpa only [map_mul, Module.End.mul_apply] using h4
      have h0' : Polynomial.aeval S (q.map φ)
          (Polynomial.aeval S (q.map φ) (j (Polynomial.aeval T r x))) = 0 := by
        rw [← htr, ← htr, h0, map_zero]
      have hcomm1 : ∀ u ∈ U, Polynomial.aeval S (q.map φ) (S' u)
          = S' (Polynomial.aeval S (q.map φ) u) :=
        GlobalTheory.NormalSeparable.aeval_comm U S S' hSU hc (q.map φ)
      have hcomm2 := GlobalTheory.NormalSeparable.aeval_comm U S' (Polynomial.aeval S (q.map φ)) hS'
        (fun u hu => (hcomm1 u hu).symm) ((q.map φ).map (starRingEnd ℂ))
      exact GlobalTheory.NormalSeparable.normal_sq_zero U (Polynomial.aeval S (q.map φ))
        (Polynomial.aeval S' ((q.map φ).map (starRingEnd ℂ)))
        (GlobalTheory.NormalSeparable.aeval_mem U S hSU _) (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _)
        (GlobalTheory.NormalSeparable.aeval_adj U S S' hSU hadj hS' _) (fun u hu => (hcomm2 u hu).symm)
        (j (Polynomial.aeval T r x)) (hjU _) h0'
    have hdvd : minpoly K T ∣ q * r := minpoly.dvd K T hann
    rw [hr] at hdvd
    have hqr : q * r ≠ 0 := by
      intro h
      apply hp0
      rw [hr, mul_assoc, h, mul_zero]
    have h5 : q * (q * r) ∣ 1 * (q * r) := by rwa [one_mul, ← mul_assoc]
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hqr).mp h5)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory.NormalSeparable
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory

theorem charpoly_split_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  intro O V B _ _ _ _ _ _ _ _ _ _ _ e t T he hs
  refine ⟨(LinearMap.charpoly t).map (algebraMap O (FractionRing O)), ?_, hs, ?_⟩
  · exact ((LinearMap.charpoly_monic t).map _).ne_zero
  · have hpow : ∀ (n : ℕ) (b : B), (T ^ n) (e b) = e ((t ^ n) b) := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih => intro b; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← he, ih]
    have key : ∀ (q : O[X]) (b : B), Polynomial.aeval T (q.map (algebraMap O (FractionRing O))) (e b) = e (Polynomial.aeval t q b) := by
      intro q b
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq]
      | monomial n a =>
          simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, LinearMap.map_smul_of_tower]
          rw [algebraMap_smul]
    have hle : Submodule.span (FractionRing O) (Set.range e) ≤ LinearMap.ker (Polynomial.aeval T ((LinearMap.charpoly t).map (algebraMap O (FractionRing O)))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, key, LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero]
    intro x hx
    exact hle hx

end GlobalTheory
end
