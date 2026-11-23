module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Order.WithBotTop
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem finite_monomials_of_multidegree (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  apply (Finsupp.finite_of_degree_eq (∑ k, m k)).subset
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd ⊢
  rw [← hd, Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Finset.sum_fn, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockWeight, Pi.single_apply]

theorem finiteDimensional_multiHomogForms (F : Type*) [Field F] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_monomials_of_multidegree (ι := ι) m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})

end

theorem GradedFinite.proof : GradedFinite.Statement := by
  intro F _ K _ _ ι _ I m
  have hfin := finiteDimensional_multiHomogForms (ι := ι) F m
  have hP : FiniteDimensional F (gradedPiece I m) := by
    unfold gradedPiece
    exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfin).map (Ideal.Quotient.mkₐ F I).toLinearMap)
  refine ⟨hP, ?_⟩
  unfold hilbFn
  rw [if_pos fun k => Int.natCast_nonneg (m k)]
  simp only [Int.toNat_natCast]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ContractRelDimLe.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → relDim (contractPrime j P') ≤ relDim P'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivCycleMinimal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), P.IsPrime →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ a : MRing ι F, a ∉ P →
    ∀ (W : Ideal (MRing ι F)) (hW : W.IsPrime), relDim W = (n : ℕ) → P ⊔ Ideal.span {a} ≤ W →
      haveI := hW
      W ∈ (P ⊔ Ideal.span {a}).minimalPrimes ∧ multAt (P ⊔ Ideal.span {a}) W ≠ ⊤

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivPushForwardLocal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : MRing (fun k => ι' (j k)) F), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    ∀ M : Ideal (MRing ι' F) → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      cycEval M (divCycle P' (rename (blockIncl j ι') a)) =
        relDeg j P' * divCycle (contractPrime j P') a W

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FunctionFieldFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
      haveI := hP'.isPrime
      relDeg j P' ≠ 0

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {F : Type*} [Field F] {K : Type*} {ι : K → Type*}

theorem relDim_eq_iff_hasRelDim [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) :
    relDim I = (n : WithBot (WithTop ℤ)) ↔ IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim I n := by
  unfold relDim IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x
  have e1 : ((n : ℕ) : WithBot (WithTop ℤ)) = some (some (n : ℤ)) := rfl
  have e2 : ((n + Fintype.card K : ℕ) : WithBot ℕ∞) = some (some (n + Fintype.card K)) := rfl
  rw [e1, e2]
  rcases x with _ | _ | e
  · simp [WithBot.map]
  · simp only [WithBot.map, WithTop.map, Option.map]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · simp only [WithBot.map, WithTop.map, Option.map]
    constructor
    · intro h
      have h1 : (e : ℤ) - Fintype.card K = n := Option.some.inj (Option.some.inj h)
      have h2 : e = n + Fintype.card K := by omega
      rw [h2]
      exact rfl
    · intro h
      have h1 : e = n + Fintype.card K := Option.some.inj (Option.some.inj h)
      subst h1
      congr 2
      push_cast
      ring

variable [DecidableEq K]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem relDim_bot {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] :
    relDim (⊥ : Ideal (MRing ι F)) =
      (((Fintype.card (Σ k, ι k) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := by
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card]
  rfl

abbrev ProjIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

theorem relDim_projectiveSpace {F : Type*} [Field F] (N : ℕ) :
    relDim (⊥ : Ideal (MRing (ProjIdx N) F)) = (N : WithBot (WithTop ℤ)) := by
  rw [relDim_bot]
  simp [Fintype.card_sigma]
  rfl

def binomFn (N : ℕ) (t : ℤ) : ℤ := if 0 ≤ t then ((t.toNat + N).choose N : ℤ) else 0

theorem binomFn_sub (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by
  unfold binomFn
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · simp
  · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨(t - 1).toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : ((u : ℤ) + 1).toNat = u + 1 := by omega
    have h2 : ((u : ℤ) + 1 - 1).toNat = u := by omega
    have h3 := Nat.choose_succ_succ (u + N + 1) N
    rw [h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3,
      show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]
    push_cast
    ring

theorem weight_projIdx (N : ℕ) (d : (Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :
    Finsupp.weight (blockWeight (ProjIdx N)) d () = ∑ x, d x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  simp [blockWeight]

theorem finrank_gradedPiece_projectiveSpace (F : Type*) [Field F] (N a : ℕ) :
    Module.finrank F (gradedPiece (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ => a)) =
      (a + N).choose N := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ F (⊥ : Ideal (MRing (ProjIdx N) F))).toLinearMap := by
    intro x y h
    simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, sub_eq_zero] using h
  unfold gradedPiece
  rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  let s : Set ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :=
    {d | Finsupp.weight (blockWeight (ProjIdx N)) d = fun _ => a}
  let e : s ≃ (Finset.univ.finsuppAntidiag a : Finset ((Σ _ : Unit, ProjIdx N ()) →₀ ℕ)) :=
    Equiv.subtypeEquivRight fun d => by
      rw [Finset.mem_finsuppAntidiag]
      simp only [s, Set.mem_ofPred_eq, Finset.subset_univ, and_true]
      constructor
      · intro h
        rw [← weight_projIdx]
        exact congrFun h ()
      · intro h
        funext u
        rw [weight_projIdx]
        exact h
  have : Fintype s := Fintype.ofEquiv _ e.symm
  rw [LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s), Module.finrank_finsupp_self,
    Fintype.card_congr e, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Fintype.card_sigma]
  rw [add_comm, Nat.choose_symm_add]

theorem hilbFn_projectiveSpace (F : Type*) [Field F] (N : ℕ) (m : Unit → ℤ) :
    hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) m = binomFn N (m ()) := by
  unfold hilbFn binomFn
  by_cases hm : 0 ≤ m ()
  · rw [if_pos (fun k => hm), if_pos hm]
    have : (fun k => (m k).toNat) = fun _ : Unit => (m ()).toNat := rfl
    rw [this, finrank_gradedPiece_projectiveSpace]
  · rw [if_neg (fun h => hm (h ())), if_neg hm]

theorem foldr_diffStep_binomFn (j N : ℕ) :
    (List.replicate j (1 : Unit → ℤ)).foldr diffStep (fun m => binomFn (N + j) (m ())) =
      fun m => binomFn N (m ()) := by
  induction j generalizing N with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, show N + (j + 1) = (N + 1) + j by omega, ih]
    funext m
    simp only [diffStep, Pi.sub_apply, Pi.one_apply]
    exact binomFn_sub N (m ())

theorem intNum_projectiveSpace (F : Type*) [Field F] (N : ℕ) :
    intNum F (⊥ : Ideal (MRing (ProjIdx N) F)) (fun _ : Fin N => (1 : Unit → ℤ)) = 1 := by
  have hh : hilbFn (⊥ : Ideal (MRing (ProjIdx N) F)) = fun m => binomFn (0 + N) (m ()) := by
    funext m
    rw [zero_add, hilbFn_projectiveSpace]
  unfold intNum mixedDiff
  rw [List.ofFn_const, hh, foldr_diffStep_binomFn]
  have hev : ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = 1 :=
    (Filter.eventually_ge_atTop 0).mono fun m hm => by
      have : (0 : ℤ) ≤ m () := hm ()
      simp [binomFn, this]
  have hex : ∃ c, ∀ᶠ m : Unit → ℤ in Filter.atTop, binomFn 0 (m ()) = c := ⟨1, hev⟩
  unfold eventualValue
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hev).exists
  exact h1.symm.trans h2

theorem blockIncl_injective {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  cases j.injective h1
  rw [eq_of_heq h2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem relDim_of_ringKrullDim_eq (I : Ideal (MRing ι F)) (d : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = (d : WithBot ℕ∞)) :
    relDim I = (((d : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  rfl


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem relDim_map_injective :
    Function.Injective (WithBot.map (fun d : ℕ∞ =>
      WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)) :=
  WithBot.map_injective (WithTop.map_injective fun a b h => by
    have h' : (a : ℤ) - Fintype.card K = (b : ℤ) - Fintype.card K := h
    omega)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
