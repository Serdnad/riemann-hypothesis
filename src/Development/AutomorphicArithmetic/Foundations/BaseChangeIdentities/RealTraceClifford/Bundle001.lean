module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle234
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def chi {n : ℕ} (x : Wt n) : Multiplicative (Wt n) →* ℂ where
  toFun θ := Complex.exp (Complex.I * ∑ a, ((Multiplicative.toAdd θ a : ℝ) : ℂ) * (x a : ℂ))
  map_one' := by simp
  map_mul' s t := by
    simp [← Complex.exp_add, add_mul, mul_add, Finset.sum_add_distrib]

private theorem chi_inj {n : ℕ} : Function.Injective (chi (n := n)) := by
  intro x y hxy
  funext a
  by_contra hne
  have hd' : x a - y a ≠ 0 := sub_ne_zero.2 hne
  have e := congrArg (fun φ : Multiplicative (Wt n) →* ℂ =>
    φ (Multiplicative.ofAdd (Pi.single a (Real.pi / (x a - y a))))) hxy
  simp [chi, Pi.single_apply] at e
  rw [Complex.exp_eq_exp_iff_exists_int] at e
  obtain ⟨m, hm⟩ := e
  have hi := congrArg Complex.im hm
  simp at hi
  have hp : Real.pi / (x a - y a) * (x a - y a) = Real.pi := div_mul_cancel₀ _ hd'
  have h2 : Real.pi * 1 = Real.pi * (2 * m) := by linear_combination hi - hp
  have h3 := mul_left_cancel₀ Real.pi_ne_zero h2
  have h4 : (1 : ℤ) = 2 * m := by exact_mod_cast h3
  omega

private theorem evT_eq_sum_coeff_chi {n : ℕ} (θ : Wt n) (f : FR n) :
    evT θ f = ∑ x ∈ f.coeff.support, f.coeff x * chi x (Multiplicative.ofAdd θ) := by
  simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum, chi]

private theorem ev_zero {n : ℕ} (f : FR n) (h : ∀ θ : Wt n, evT θ f = 0) : f = 0 := by
  have hli : LinearIndependent ℂ (fun x : Wt n => ((chi x : Multiplicative (Wt n) → ℂ))) :=
    (linearIndependent_monoidHom (Multiplicative (Wt n)) ℂ).comp chi chi_inj
  apply AddMonoidAlgebra.ext
  apply linearIndependent_iff.1 hli
  ext θ
  have hθ := h (Multiplicative.toAdd θ)
  rw [evT_eq_sum_coeff_chi] at hθ
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simpa [Finset.sum_apply] using hθ

theorem UpperTheory.RealTr.evInj :
    ∀ (n : ℕ) (f : FR n), (∀ θ : Wt n, (Function.Injective fun a => Complex.exp (Complex.I * θ a) ^ 2) → evT θ f = 0) → f = 0 := by
  intro n f hf
  apply ev_zero f
  intro θ0
  let v : Wt n := fun a => ((a : ℕ) : ℝ)
  obtain ⟨bad, hbad, hmem⟩ : ∃ S : Set ℝ, S.Countable ∧ ∀ t : ℝ, t ∉ S →
      Function.Injective fun a => Complex.exp (Complex.I * (((θ0 + t • v) a : ℝ) : ℂ)) ^ 2 := by
    refine ⟨⋃ p : Fin n × Fin n, ⋃ m : ℤ,
      {((m : ℝ) * Real.pi - (θ0 p.1 - θ0 p.2)) / (v p.1 - v p.2)}, ?_, ?_⟩
    · exact Set.countable_iUnion fun p => Set.countable_iUnion fun m => Set.countable_singleton _
    · intro t ht a b hab
      by_contra hne
      apply ht
      simp only at hab
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at hab
      obtain ⟨m, hm⟩ := hab
      have hi := congrArg Complex.im hm
      simp [Pi.add_apply, Pi.smul_apply] at hi
      have hv : v a - v b ≠ 0 := sub_ne_zero.2 (fun e => hne (Fin.ext (by simpa [v] using e)))
      refine Set.mem_iUnion.2 ⟨(a, b), Set.mem_iUnion.2 ⟨m, Set.mem_singleton_iff.2 ?_⟩⟩
      rw [eq_div_iff hv]
      linarith
  have hφ : (fun t : ℝ => evT (θ0 + t • v) f) = fun t => ∑ x ∈ f.coeff.support,
      f.coeff x * Complex.exp (Complex.I * ∑ a, (((θ0 a + t * v a : ℝ)) : ℂ) * (x a : ℂ)) := by
    funext t
    simp [evT, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  have hcont : Continuous fun t : ℝ => evT (θ0 + t • v) f := by
    rw [hφ]
    fun_prop
  have hzero := Continuous.ext_on (hbad.dense_compl ℝ) hcont continuous_const
    (fun t ht => hf (θ0 + t • v) (hmem t ht))
  simpa using congrFun hzero 0
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem UpperTheory.RealTr.casPK {n : ℕ} {A : Type} [Ring A] (E1 E2 : Fin n → Fin n → A) :
    Cas (fun a b => E1 a b - E2 a b) + Cas (fun a b => E1 a b + E2 a b) = 2 * (Cas E1 + Cas E2) := by
  simp only [Cas, two_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  noncomm_ring

private theorem UpperTheory.RealTr.casAdd {n : ℕ} {A : Type} [Ring A] (K s : Fin n → Fin n → A)
    (h : ∀ a b d e, K a b * s d e = s d e * K a b) :
    Cas (fun a b => K a b + s a b) = Cas K + Cas s + 2 * ∑ a, ∑ b, K a b * s b a := by
  have h1 : ∑ a, ∑ b, s a b * K b a = ∑ a, ∑ b, K a b * s b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (h a b b a).symm
  have h2 : Cas (fun a b => K a b + s a b) =
      Cas K + Cas s + (∑ a, ∑ b, K a b * s b a + ∑ a, ∑ b, s a b * K b a) := by
    simp only [Cas, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    noncomm_ring
  rw [h2, h1, two_mul]

private theorem UpperTheory.RealTr.dd1 {n : ℕ} {A : Type} [Ring A] (u : Fin n → Fin n → A) :
    (∑ a, ∑ b, u a b) * (∑ a, ∑ b, u a b) = ∑ a, ∑ b, ∑ d, ∑ e, u a b * u d e := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]

private theorem UpperTheory.RealTr.dd2 {n : ℕ} {A : Type} [Ring A] (u : Fin n → Fin n → A) :
    (∑ a, ∑ b, u a b) * (∑ a, ∑ b, u a b) = ∑ a, ∑ b, ∑ d, ∑ e, u d e * u a b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]

private theorem UpperTheory.RealTr.sum3 {n : ℕ} {A : Type} [AddCommMonoid A] (g : Fin n → Fin n → Fin n → A) :
    ∑ a, ∑ b, ∑ d, g a b d = ∑ d, ∑ b, ∑ a, g a b d := by
  calc ∑ a, ∑ b, ∑ d, g a b d = ∑ a, ∑ d, ∑ b, g a b d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, g a b d := Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, g a b d := Finset.sum_congr rfl fun d _ => Finset.sum_comm

private theorem UpperTheory.RealTr.sumSpn {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (x y : Fin n) :
    ∑ z, c x z * c z y = spn c x y + if x = y then algebraMap ℂ A ((n : ℂ) / 2) else 0 := by
  simp only [spn, sub_add_cancel]

private theorem UpperTheory.RealTr.sumSwap {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (x y : Fin n) :
    ∑ z, c z x * c y z = (if x = y then (n : A) else 0) -
      (spn c y x + if y = x then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
  rw [← UpperTheory.RealTr.sumSpn, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  have h : ∀ z, c z x * c y z + c y z * c z x = if x = y then 1 else 0 := by
    intro z
    rw [hc z x y z]
    simp
  simp only [h]
  by_cases hxy : x = y <;> simp [hxy]

private theorem UpperTheory.RealTr.dCore {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]
    (P K c : Fin n → Fin n → A)
    (hPP : ∀ a b d e, P a b * P d e - P d e * P a b =
      (if b = d then K a e else 0) - (if e = a then K d b else 0))
    (hPc : ∀ a b d e, P a b * c d e = c d e * P a b)
    (hc : Clif c) :
    2 * ((∑ a, ∑ b, P a b * c b a) * ∑ a, ∑ b, P a b * c b a) =
      Cas P - 2 * ∑ a, ∑ b, K a b * spn c b a := by
  have hmul : ∀ a b d e, (P a b * c b a) * (P d e * c e d) = P a b * P d e * (c b a * c e d) := by
    intro a b d e
    calc P a b * c b a * (P d e * c e d) = P a b * (c b a * P d e) * c e d := by
          simp only [mul_assoc]
      _ = P a b * (P d e * c b a) * c e d := by rw [hPc d e b a]
      _ = _ := by simp only [mul_assoc]
  have hpt : ∀ a b d e, (P a b * c b a) * (P d e * c e d) + (P d e * c e d) * (P a b * c b a) =
      (if a = e then (if b = d then P a b * P d e else 0) else 0)
      - (if b = d then K a e * (c e d * c b a) else 0)
      + (if e = a then K d b * (c e d * c b a) else 0) := by
    intro a b d e
    have h1 := hc b a e d
    have h3 : P d e * P a b = P a b * P d e -
        ((if b = d then K a e else 0) - (if e = a then K d b else 0)) := by
      rw [← hPP a b d e]; abel
    have h4 : P a b * P d e * (c b a * c e d) + P d e * P a b * (c e d * c b a) =
        P a b * P d e * (c b a * c e d + c e d * c b a) -
          ((if b = d then K a e else 0) - (if e = a then K d b else 0)) * (c e d * c b a) := by
      rw [h3, sub_mul, mul_add]; abel
    rw [hmul, hmul, h4, h1]
    by_cases hae : a = e <;> by_cases hbd : b = d <;> simp [hae, hbd, sub_mul, eq_comm] <;> abel
  have hS1 : ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0) = Cas P := by
    simp [Cas, Finset.sum_ite_eq]
  have hS2 : ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0) =
      ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0)
        = ∑ b, ∑ e, K a e * (c e b * c b a) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          simp
      _ = ∑ e, ∑ b, K a e * (c e b * c b a) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.mul_sum, UpperTheory.RealTr.sumSpn]
  have hS3 : ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) =
      ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) -
        (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)) := by
    calc ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0)
        = ∑ a, ∑ b, ∑ d, K d b * (c a d * c b a) := by simp
      _ = ∑ d, ∑ b, ∑ a, K d b * (c a d * c b a) := UpperTheory.RealTr.sum3 _
      _ = _ := by
          refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.mul_sum, UpperTheory.RealTr.sumSwap c hc]
  have hhalf : algebraMap ℂ A ((n : ℂ) / 2) + algebraMap ℂ A ((n : ℂ) / 2) = (n : A) := by
    rw [← map_add (f := _), add_halves, map_natCast]
  have hfin : ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) -
      ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) -
        (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)) =
      2 * ∑ a, ∑ b, K a b * spn c b a := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hi : (if a = b then (n : A) else 0) =
        (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) +
          (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
      by_cases hab : a = b
      · simp [hab, hhalf]
      · simp [hab, Ne.symm hab]
    rw [hi]
    noncomm_ring
  calc 2 * ((∑ a, ∑ b, P a b * c b a) * ∑ a, ∑ b, P a b * c b a)
      = (∑ a, ∑ b, P a b * c b a) * (∑ a, ∑ b, P a b * c b a) +
        (∑ a, ∑ b, P a b * c b a) * (∑ a, ∑ b, P a b * c b a) := two_mul _
    _ = ∑ a, ∑ b, ∑ d, ∑ e, ((P a b * c b a) * (P d e * c e d) + (P d e * c e d) * (P a b * c b a)) := by
        nth_rewrite 1 [UpperTheory.RealTr.dd1 (fun a b => P a b * c b a)]
        rw [UpperTheory.RealTr.dd2 (fun a b => P a b * c b a)]
        simp only [Finset.sum_add_distrib]
    _ = ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0)
        - ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0)
        + ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) := by
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
        rw [hS1, hS2, hS3, ← hfin]; abel

private theorem UpperTheory.RealTr.commSpn {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (x : A) (h : ∀ d e, x * c d e = c d e * x) (a b : Fin n) : x * spn c a b = spn c a b * x := by
  have h' : Commute x (spn c a b) := by
    unfold spn
    refine Commute.sub_right (Commute.sum_right _ _ _ fun d _ => Commute.mul_right (h _ _) (h _ _)) ?_
    split_ifs
    · exact Algebra.commutes _ _ |>.symm
    · exact Commute.zero_right _
  exact h'

theorem UpperTheory.RealTr.diracAlg :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (E1 E2 c : Fin n → Fin n → A), GlRel E1 → GlRel E2 → (∀ a b d e, E1 a b * E2 d e = E2 d e * E1 a b) →
      Clif c → (∀ a b d e, E1 a b * c d e = c d e * E1 a b ∧ E2 a b * c d e = c d e * E2 a b) →
      2 * ((∑ a, ∑ b, (E1 a b - E2 a b) * c b a) * ∑ a, ∑ b, (E1 a b - E2 a b) * c b a) =
        2 * (Cas E1 + Cas E2) + Cas (spn c) - Cas fun a b => E1 a b + E2 a b + spn c a b := by
  intro n A _ _ E1 E2 c h1 h2 h12 hc hEc
  have hPP : ∀ a b d e, (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) =
      (if b = d then E1 a e + E2 a e else 0) - (if e = a then E1 d b + E2 d b else 0) := by
    intro a b d e
    have h : (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) =
        (E1 a b * E1 d e - E1 d e * E1 a b) + (E2 a b * E2 d e - E2 d e * E2 a b) := by
      simp only [sub_mul, mul_sub, h12 a b d e, h12 d e a b]
      abel
    rw [h, h1 a b d e, h2 a b d e]
    split_ifs <;> abel
  have hPc : ∀ a b d e, (E1 a b - E2 a b) * c d e = c d e * (E1 a b - E2 a b) := by
    intro a b d e
    rw [sub_mul, mul_sub, (hEc a b d e).1, (hEc a b d e).2]
  have hK : ∀ a b d e, (E1 a b + E2 a b) * spn c d e = spn c d e * (E1 a b + E2 a b) := by
    intro a b d e
    refine UpperTheory.RealTr.commSpn c _ (fun d e => ?_) d e
    rw [add_mul, mul_add, (hEc a b d e).1, (hEc a b d e).2]
  have e1 : Cas (fun a b => E1 a b + E2 a b + spn c a b) =
      Cas (fun a b => E1 a b + E2 a b) + Cas (spn c) +
        2 * ∑ a, ∑ b, (E1 a b + E2 a b) * spn c b a :=
    UpperTheory.RealTr.casAdd (fun a b => E1 a b + E2 a b) (spn c) hK
  rw [UpperTheory.RealTr.dCore (fun a b => E1 a b - E2 a b) (fun a b => E1 a b + E2 a b) c hPP hPc hc, e1,
    ← UpperTheory.RealTr.casPK E1 E2]
  abel
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem tri {A : Type} [Ring A] (x y z p q : A) (h1 : y * z + z * y = p)
    (h2 : x * z + z * x = q) : x * y * z - z * (x * y) = x * p - q * y := by
  rw [← h1, ← h2]
  noncomm_ring

private theorem leib {A : Type} [Ring A] (X u v : A) :
    X * (u * v) - u * v * X = (X * u - u * X) * v + u * (X * v - v * X) := by
  noncomm_ring

private theorem spn_comm {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (a b d e : Fin n) :
    spn c a b * c d e - c d e * spn c a b =
      (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have hsum : spn c a b * c d e - c d e * spn c a b =
      ∑ f, (c a f * c f b * c d e - c d e * (c a f * c f b)) := by
    unfold spn
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [hsum]
  have hterm : ∀ f, c a f * c f b * c d e - c d e * (c a f * c f b) =
      c a f * (if b = d ∧ f = e then 1 else 0) - (if f = d ∧ a = e then 1 else 0) * c f b := by
    intro f
    exact tri _ _ _ _ _ (hc f b d e) (hc a f d e)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases hbd : b = d
    · simp [hbd]
    · simp [hbd]
  · by_cases hea : e = a
    · subst hea
      simp
    · have : ∀ f : Fin n, ¬ (f = d ∧ a = e) := fun f h => hea h.2.symm
      simp [this, hea]

theorem UpperTheory.RealTr.spnRel :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A), Clif c → GlRel (spn c) ∧
      ∀ a b d e, spn c a b * c d e - c d e * spn c a b = (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  intro n A _ _ c hc
  refine ⟨?_, fun a b d e => spn_comm c hc a b d e⟩
  intro a b g h
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have expand : ∀ X : A, X * spn c g h - spn c g h * X =
      ∑ f, (X * (c g f * c f h) - c g f * c f h * X) := by
    intro X
    unfold spn
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [expand]
  simp_rw [leib, spn_comm c hc]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  unfold spn
  by_cases hbg : b = g <;> by_cases hha : h = a
  · subst hbg
    subst hha
    simp
  · simp [hbg, hha, Ne.symm hha]
  · simp [hbg, hha, Ne.symm hbg]
    abel
  · simp [hbg, hha, Ne.symm hbg, Ne.symm hha]
end
end

section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.rdcalc :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V],
      (∀ f f' : Mat n → V, Set.EqOn f f' (GLs n) → ∀ X, Set.EqOn (Rd X f) (Rd X f') (GLs n)) ∧
      ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) → (∀ X, ContDiffOn ℝ ∞ (Rd X f) (GLs n)) ∧
        (∀ X Y, ∀ g ∈ GLs n, Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g) ∧
        ∀ h ∈ GLs n, ∀ X, ∀ g ∈ GLs n, Rd X (fun y => f (h * y)) g = Rd X f (h * g) ∧
          Rd X (fun y => f (y * h)) g = Rd (h⁻¹ * X * h) f (g * h) := by
  intro n V _ _
  refine ⟨fun f f' e X => GlobalTheory.CompanionTheory.RCalc.Rd_congr X e, fun f hf =>
    ⟨fun X => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf, fun X Y g hg => GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y hf hg,
      fun h hh X g hg => ?_⟩⟩
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have hhg : h * g ∈ GLs n := by
    show (h * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hh hg
  have hgh : g * h ∈ GLs n := by
    show (g * h).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  constructor
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hhg
    have hc : HasFDerivAt (fun y : Mat n => f (h * y))
        ((fderiv ℝ f (h * g)).comp (GlobalTheory.CompanionTheory.RCalc.mulL h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => h * y) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulL h).hasFDerivAt
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulL_apply, mul_assoc]
  · have hd := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hf hgh
    have hc : HasFDerivAt (fun y : Mat n => f (y * h))
        ((fderiv ℝ f (g * h)).comp (GlobalTheory.CompanionTheory.RCalc.mulR h)) g :=
      HasFDerivAt.comp (g := f) (f := fun y : Mat n => y * h) g hd.hasFDerivAt
        (GlobalTheory.CompanionTheory.RCalc.mulR h).hasFDerivAt
    have e : g * h * (h⁻¹ * X * h) = g * X * h := by
      rw [Matrix.mul_assoc g h, ← Matrix.mul_assoc h, ← Matrix.mul_assoc h, Matrix.mul_nonsing_inv h hdet,
        Matrix.one_mul, Matrix.mul_assoc]
    simp only [Rd, hc.fderiv, ContinuousLinearMap.comp_apply, GlobalTheory.CompanionTheory.RCalc.mulR_apply, e]
end
end

section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.lgCpt :
    ∀ (n : ℕ) (R : ℝ), IsCompact {y : G n | lg y.val ≤ R} := by
  intro n R
  obtain ⟨-, -, -, -, hc, -⟩ := GlobalTheory.T.length_function_facts_hold n
  exact hc R
end
end
