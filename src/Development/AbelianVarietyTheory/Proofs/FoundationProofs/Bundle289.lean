module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle098
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching.AddColumn

theorem weight_mapDomain (r n : ℕ) (u : Fin r × Fin n →₀ ℕ) :
    (∀ i : Fin n, Finsupp.weight (colW r (n + 1))
        (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) i.castSucc = Finsupp.weight (colW r n) u i) ∧
      Finsupp.weight (colW r (n + 1)) (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) (Fin.last n) = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, ha.1, hb.1]
    · rw [Finsupp.mapDomain_add, map_add (f := _), Pi.add_apply, ha.2, hb.2]
  | single v k =>
    refine ⟨fun i => ?_, ?_⟩
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply]
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply,
        (Fin.castSucc_lt_last v.2).ne']

theorem colAddGen_rename_castSucc (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l.castSucc j.castSucc
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename (Option.map (Prod.map id Fin.castSucc)) (colAddGen R l j f) := by
  have e : (colAddGen R (r := r) l.castSucc j.castSucc).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename (Option.map (Prod.map id Fin.castSucc))).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hv : s = j
    · simp [colAddGen, hv]
    · simp [colAddGen, hv]
  exact DFunLike.congr_fun e f

theorem colAddGen_rename_last (R : Type*) [CommRing R] {r n : ℕ} (l : Fin (n + 1))
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l (Fin.last n)
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename some (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) := by
  have e : (colAddGen R (r := r) l (Fin.last n)).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename some).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [colAddGen, (Fin.castSucc_lt_last s).ne]
  exact DFunLike.congr_fun e f

theorem add_column : ∀ (r n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → (∀ f ∈ dualWeyl ℂ r n (fun i => ν i.castSucc), rename (Prod.map id Fin.castSucc) f ∈ dualWeyl ℂ r (n + 1) ν) ∧ ∀ (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ), rowAct ℂ g (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) = rename (Prod.map id Fin.castSucc) (rowAct ℂ g f) := by
  intro r n ν hν
  refine ⟨fun f hf => ?_, fun g f => ?_⟩
  · simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
    refine ⟨fun d hd => ?_, fun l j hlj => ?_⟩
    · obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
      have h := hf.1 hu
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [(weight_mapDomain r n u).2, hν]
      · rw [(weight_mapDomain r n u).1, h]
    · induction j using Fin.lastCases with
      | last => exact colAddGen_rename_last ℂ l f
      | cast j =>
        induction l using Fin.lastCases with
        | last => exact absurd hlj (not_lt.2 (Fin.le_last _))
        | cast l =>
          rw [colAddGen_rename_castSucc, hf.2 l j (Fin.castSucc_lt_castSucc_iff.1 hlj), rename_rename,
            rename_rename]
          rfl
  · have e : (rowAct ℂ g).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
        (rename (Prod.map id Fin.castSucc)).comp (rowAct ℂ g) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, s⟩
      simp [rowAct]
    exact DFunLike.congr_fun e f

end GlobalTheory.Branching.AddColumn
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem exists_poly_rowAct_coef (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P := by
  induction f using MvPolynomial.induction_on generalizing l with
  | C a => exact ⟨C (l (C a)), fun g => by simp [rowAct]⟩
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp l
    obtain ⟨Q, hQ⟩ := hq l
    exact ⟨P + Q, fun g => by simp only [map_add (f := _), hP, hQ]⟩
  | mul_X p v hp =>
    choose P hP using fun b : Fin n => hp (l ∘ₗ LinearMap.mulRight ℂ (X (b, v.2)))
    refine ⟨∑ b, X (v.1, b) * P b, fun g => ?_⟩
    have e : rowAct ℂ g (X v) = ∑ b, g v.1 b • X (b, v.2) := by
      simp [rowAct, smul_eq_C_mul]

    rw [map_mul, e, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
    rfl

theorem eq_zero_of_vanish_unitaryGroup (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) : P = 0 := by
  have hinj : Function.Injective (fun x : Fin n × Fin n => ((), x) : Fin n × Fin n → Unit × Fin n × Fin n) :=
    fun x y e => congrArg Prod.snd e
  apply rename_injective _ hinj
  rw [map_zero]
  refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := Unit) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
  rw [eval_rename]
  have := h (u ()) (Matrix.mem_unitaryGroup_iff'.2 (hu ()))
  simpa [Function.comp_def] using this

theorem rowAct_coef_poly_and_unitary_dense :
    (∀ (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ) (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)),
      ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
        l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P) ∧
    ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
      (∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) → P = 0 :=
  ⟨exists_poly_rowAct_coef, eq_zero_of_vanish_unitaryGroup⟩

end GlobalTheory.Branching
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_genericDet (R : Type) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (lpMinor R n le_rfl le_rfl) = C g.det * lpMinor R n le_rfl le_rfl := by
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 p q
  simp [rowAct, Matrix.mul_apply]

theorem genericDet_pow_mem (R : Type) [CommRing R] (n c : ℕ) :
    lpMinor R n le_rfl le_rfl ^ c ∈ dualWeyl R n n (fun _ => c) := by
  have h := bidetMem R n n c (fun _ => n) (fun _ => le_rfl) (fun _ => Fin.castLE le_rfl)
  have e : shapeDeg (n := n) (fun _ : Fin c => n) = fun _ => c := by
    funext t
    simp [shapeDeg]
  rw [e] at h
  simpa [bideterminant, initMinor, lpMinor] using h

theorem genericDet_pow_mul_hw (R : Type) [CommRing R] (n c : ℕ) (ν : Fin n → ℕ) :
    lpMinor R n le_rfl le_rfl ^ c * hw R le_rfl ν = hw R (le_refl n) (fun i => ν i + c) := by
  cases n with
  | zero => simp [hw, lpMinor]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_left_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      have hs : (Fin.castSucc s).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_pos hs]
      omega
    · have hs : ¬ (Fin.last m).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_neg hs, Nat.sub_zero]
      rw [pow_add, mul_comm]
      rfl

theorem genericDet_pow_mul :
    ∀ (n c : ℕ) (ν : Fin n → ℕ), (∀ f ∈ dualWeyl ℂ n n ν, lpMinor ℂ n le_rfl le_rfl ^ c * f ∈ dualWeyl ℂ n n (fun i => ν i + c)) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ), rowAct ℂ g (lpMinor ℂ n le_rfl le_rfl ^ c * f) = g.det ^ c • (lpMinor ℂ n le_rfl le_rfl ^ c * rowAct ℂ g f)) ∧ (Antitone ν → lpMinor ℂ n le_rfl le_rfl ^ c * hw ℂ le_rfl ν = hw ℂ (le_refl n) (fun i => ν i + c)) := by
  intro n c ν
  refine ⟨fun f hf => ?_, fun g f => ?_, fun _ => genericDet_pow_mul_hw ℂ n c ν⟩
  · rw [mul_comm]
    exact (dualWeylMul ℂ n n ν (fun _ => c) f _).1 hf (genericDet_pow_mem ℂ n c)
  · rw [map_mul, map_pow, rowAct_genericDet, mul_pow, smul_eq_C_mul, map_pow, mul_assoc]

end GlobalTheory.Branching
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockIrr

theorem act_diag_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} (h : v ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  have h1 := (Submodule.mem_iInf _).1 h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  exact sub_eq_zero.1 h1

theorem irreducible_of_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  intro p q M H _ _ E hE hadj S hS μ v U hv hU hline N hNU hN
  by_cases hvN : v ∈ N
  · exact Or.inr (le_antisymm hNU (hU N hvN hN))
  left
  have horth : ∀ x ∈ N, inner ℂ (E x) (E v) = 0 := by
    intro x hx
    have hx' := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => hN a a (hS.refl a)) x hx (M.wts x)
    clear hx
    induction hx' using Submodule.iSup_induction' with
    | mem ν y hy =>
      obtain ⟨hyN, hyν⟩ := hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, hc⟩ := hline y (hNU hyN) hyν
        by_cases hc0 : c = 0
        · simp [hc, hc0]
        · exfalso
          apply hvN
          have : v = c⁻¹ • y := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [this]
          exact N.smul_mem _ hyN
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h1 := hadj (Eab a a) y v
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_diag_of_mem_wtSub hyν, act_diag_of_mem_wtSub hv, map_smul, map_smul,
          inner_smul_left, inner_smul_right, map_ratCast] at h1
        have hne : ((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha
        have h2 : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) * inner ℂ (E y) (E v) = 0 := by
          rw [sub_mul, h1, sub_self]
        exact (mul_eq_zero.1 h2).resolve_left hne
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _), inner_add_left, hy, hz, add_zero]
  let U' : Submodule ℂ M.V :=
    { carrier := {y | ∀ x ∈ N, inner ℂ (E x) (E y) = 0}
      add_mem' := fun {y z} hy hz x hx => by
        rw [map_add (f := _), inner_add_right, hy x hx, hz x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c y hy x hx => by
        rw [map_smul, inner_smul_right, hy x hx, mul_zero] }
  have hUU' : U ≤ U' := by
    refine hU U' horth ?_
    intro a b hab y hy x hx
    have h1 := hadj (adjZ (Eab a b)) x y
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at h1
    rw [← h1]
    apply hy
    rw [GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (hN b a (hS.symm hab) x hx)
  rw [eq_bot_iff]
  intro x hx
  have h0 : inner ℂ (E x) (E x) = 0 := hUU' (hNU hx) x hx
  rw [inner_self_eq_zero] at h0
  exact (Submodule.mem_bot ℂ).2 (hE (by rw [h0, map_zero]))

end GlobalTheory.FockIrr
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AnalyticClosure
open GlobalTheory.FockTensor

variable {p q : ℕ} {T : GrpData p q}

def restrictRep (πU : URep T) (K : Submodule ℂ πU.H) (hK : IsClosed (K : Set πU.H))
    (hinv : ∀ g, ∀ x ∈ K, πU.π g x ∈ K) : URep T :=
  haveI : CompleteSpace K := hK.completeSpace_coe
  { H := K
    π :=
      { toFun := fun g => ((πU.π g).comp K.subtypeL).codRestrict K (fun x => hinv g x x.2)
        map_one' := by ext x; simp
        map_mul' := fun a b => by ext x; simp; rfl }
    isom := fun g x => πU.isom g x
    cont := fun x => (πU.cont x).subtype_mk _ }

theorem inner_orbit_eq_zero (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (y : V) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (w : πU.H) (hw : ∀ v, inner ℂ w (E v) = 0) (t : ℝ) :
    inner ℂ w (πU.π (T.expt (t • Y)) (E y)) = 0 := by
  have key := GlobalTheory.FactorialJet.eq_zero_of_factorial_bound ℂ
    (fun k t => inner ℂ w (πU.π (T.expt (t • Y)) (E ((A ^ k) y)))) (‖w‖ * C) ρ
    (mul_nonneg (norm_nonneg _) hC) hρ ?_ ?_ ?_ 0 t
  · simpa using key
  · intro k s
    have h1 := hasDerivAt_orbit πU hY (hd ((A ^ k) y)) s
    have h2 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    rw [pow_succ', Module.End.mul_apply]
    exact h2
  · intro k s
    refine (norm_inner_le_norm _ _).trans ?_
    rw [πU.isom, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← mul_assoc]
    exact hb k
  · intro k
    simp [T.expt_zero, hw]

theorem orbit_mem_closure (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (hb : ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (t : ℝ) (x : πU.H) (hx : x ∈ (LinearMap.range E).topologicalClosure) :
    πU.π (T.expt (t • Y)) x ∈ (LinearMap.range E).topologicalClosure := by
  have h0 : ∀ y, πU.π (T.expt (t • Y)) (E y) ∈ (LinearMap.range E).topologicalClosure := by
    intro y
    obtain ⟨C, ρ, hC, hρ, h⟩ := hb y
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    refine inner_orbit_eq_zero πU A E hY hd y hC hρ h w (fun v => ?_) t
    exact (Submodule.mem_orthogonal' _ _).1 hw _ (LinearMap.mem_range_self _ v)
  have hcl : IsClosed ((πU.π (T.expt (t • Y))) ⁻¹'
      ((LinearMap.range E).topologicalClosure : Set πU.H)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
  have hsub : ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) ⊆
      (πU.π (T.expt (t • Y))) ⁻¹' ((LinearMap.range E).topologicalClosure : Set πU.H) := by
    rintro _ ⟨y, rfl⟩
    exact h0 y
  exact closure_minimal hsub hcl hx

theorem exists_subrep_closure : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  intro p q T hgen πU V _ _ act E hd hb
  have hinv : ∀ g : T.G, ∀ x ∈ (LinearMap.range E).topologicalClosure,
      πU.π g x ∈ (LinearMap.range E).topologicalClosure := by
    intro g
    have hg : g ∈ Subgroup.closure (T.expt '' upq p q) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      simpa using orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) 1 x hx
    | inv_mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      have he : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
        have := T.expt_add Y hY 1 (-1)
        rw [add_neg_cancel, zero_smul, one_smul, T.expt_zero] at this
        exact inv_eq_of_mul_eq_one_right this.symm
      rw [he]
      exact orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) (-1) x hx
    | one => intro x hx; simpa using hx
    | mul a b _ _ ha hb' =>
      intro x hx
      rw [map_mul, ContinuousLinearMap.mul_apply]
      exact ha _ (hb' x hx)
  set K := (LinearMap.range E).topologicalClosure with hKdef
  have hK : IsClosed (K : Set πU.H) := Submodule.isClosed_topologicalClosure _
  have hmem : ∀ x, E x ∈ K := fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
  refine ⟨restrictRep πU K hK hinv, E.codRestrict K hmem, K.subtypeₗᵢ, ?_, fun x => rfl,
    fun g y => rfl, ?_⟩
  · show Dense (Set.range (E.codRestrict K hmem : V → K))
    rw [Subtype.dense_iff]
    intro x hx
    have : (Subtype.val '' Set.range (E.codRestrict K hmem : V → K)) =
        ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) := by
      rw [← Set.range_comp, LinearMap.coe_range]; rfl
    exact this ▸ (hx : x ∈ closure ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H))
  · intro Y hY x
    have h := hd Y hY x
    rw [hasDerivAt_iff_isLittleO_nhds_zero, ← Asymptotics.isLittleO_norm_left] at h ⊢
    exact h

end GlobalTheory.AnalyticClosure
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.imaginary_quadratic_field_structure : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  first | exact @GlobalTheory.QuadSubfield.quadratic_subfield | exact GlobalTheory.QuadSubfield.quadratic_subfield | (intros; apply GlobalTheory.QuadSubfield.quadratic_subfield <;> assumption)
end
