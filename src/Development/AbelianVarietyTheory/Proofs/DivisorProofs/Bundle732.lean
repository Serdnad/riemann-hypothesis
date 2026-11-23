module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeThetaKernelPoissonSummation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle694
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.SzSum

section

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_zero (r : ℝ) : Sz l lam r 0 := by
  refine ⟨zero_mem _, ?_⟩
  have : (⟨0, zero_mem _⟩ : algebraicClosure ℚ ℂ) = 0 := rfl
  rw [this, map_zero, norm_zero]
  positivity

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_sub {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x - y) := by
  rw [sub_eq_add_neg]
  exact sz_add hx (sz_neg hy)

theorem sz_mul {r s : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam s y) : Sz l lam (r + s) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r s : ℝ} {x : ℂ} (h : r ≤ s) (hx : Sz l lam r x) : Sz l lam s x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_int (n : ℤ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨intCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), intCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := Subtype.ext (by simp)
  rw [this, map_intCast, Real.rpow_zero]
  exact IsUltrametricDist.norm_intCast_le_one _ n

theorem sz_sum {κ : Type*} (t : Finset κ) {r : ℝ} {x : κ → ℂ} (h : ∀ k ∈ t, Sz l lam r (x k)) :
    Sz l lam r (∑ k ∈ t, x k) :=
  Finset.sum_induction x (Sz l lam r) (fun _ _ => sz_add) (sz_zero r) h

end

theorem sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ r : ℝ, Sz l lam r 0) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y) ∧ Sz l lam r (x - y)) ∧ (∀ (r s : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam s y → Sz l lam (r + s) (x * y)) ∧ (∀ (r s : ℝ) (x : ℂ), r ≤ s → Sz l lam r x → Sz l lam s x) ∧ (∀ n : ℤ, Sz l lam 0 (n : ℂ)) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (x : κ → ℂ), (∀ k ∈ t, Sz l lam r (x k)) → Sz l lam r (∑ k ∈ t, x k)) :=
  fun _ _ _ => ⟨sz_zero, fun _ _ _ hx hy => ⟨sz_add hx hy, sz_sub hx hy⟩, fun _ _ _ _ hx hy => sz_mul hx hy,
    fun _ _ _ h hx => sz_mono h hx, sz_int, fun _ t _ _ h => sz_sum t h⟩

end GlobalTheory.QFam.SzSum
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_of_forall_rat_gt : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    ∀ (r : ℝ) (x : ℂ), (∀ q : ℚ, r < q → Sz l lam q x) → Sz l lam r x := by
  intro l hl lam r x h
  obtain ⟨q₀, hq₀⟩ := exists_rat_gt r
  obtain ⟨hx, -⟩ := h q₀ hq₀
  refine ⟨hx, ?_⟩
  by_contra hc
  rw [not_le] at hc
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := lt_trans one_pos hl1
  have ht : 0 < ‖lam ⟨x, hx⟩‖ := lt_trans (Real.rpow_pos_of_pos hl0 r) hc
  have h1 : r < Real.logb l ‖lam ⟨x, hx⟩‖ := (Real.lt_logb_iff_rpow_lt hl1 ht).2 hc
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  obtain ⟨_, hle⟩ := h q hq1
  exact absurd ((Real.lt_logb_iff_rpow_lt hl1 ht).1 hq2) (not_lt.2 hle)

end GlobalTheory.QFam
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (le_min ih (le_of_eq (AddValuation.map_one v).symm)).trans (AddValuation.map_add v _ _)

theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast]
    exact val_natCast_nonneg v m
  · rw [Int.cast_neg, AddValuation.map_neg, Int.cast_natCast]
    exact val_natCast_nonneg v m

theorem val_natCast_eq_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (n : ℕ) (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 := val_natCast_nonneg v n
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hn).gcd_eq_one, Nat.cast_one] at hb
  have key : (1 : C) = (p : C) * (Nat.gcdA p n : C) + (n : C) * (Nat.gcdB p n : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    push_cast at this
    exact this
  have one_pos' : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  have h1 : 0 < v ((p : C) * (Nat.gcdA p n : C)) := by
    rw [AddValuation.map_mul, hv]
    exact add_pos_of_pos_of_nonneg one_pos' (val_intCast_nonneg v _)
  have h2 : 0 < v ((n : C) * (Nat.gcdB p n : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (val_intCast_nonneg v _)
  have hsum := AddValuation.map_add v ((p : C) * (Nat.gcdA p n : C)) ((n : C) * (Nat.gcdB p n : C))
  rw [← key, AddValuation.map_one] at hsum
  exact absurd hsum (not_le.2 (lt_min h1 h2))

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem detDepth_eq_zero_of_lt : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  intro C _ _ v p hp hv i d c G u hu hc
  obtain ⟨hlo, hcont, -⟩ := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds C v p hp hv i d c G u hu
  obtain ⟨-, -, hone, hrow⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  set α₀ : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα₀
  have hmem : α₀ ∈ (detPow C i c).support := by
    rw [MvPolynomial.mem_support_iff, hone]
    exact one_ne_zero
  have hfact : v (mfact α₀ : C) = 0 := by
    have hcast : (mfact α₀ : C) = ((α₀.prod fun _ n => n.factorial : ℕ) : C) := by
      unfold mfact
      rw [Nat.cast_finsuppProd]
    rw [hcast]
    apply val_natCast_eq_zero v p hp hv
    intro hdvd
    rw [Finsupp.prod] at hdvd
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    rw [hp.dvd_factorial] at hx
    obtain ⟨b, a⟩ := x
    have hle : α₀ ⟨b, a⟩ ≤ c := by
      rw [← (hrow α₀ hmem).1 a]
      exact Finset.single_le_sum (f := fun b' => α₀ ⟨b', a⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    omega
  have hle : content v (detPow C i c) ≤ 0 := by
    unfold content
    refine (iInf₂_le α₀ hmem).trans (le_of_eq ?_)
    rw [hone, one_mul, hfact]
    rfl
  exact le_antisymm (hcont.trans hle) hlo

end GlobalTheory.FGDepth
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FlowLemma

open MvPolynomial in
private lemma shiftNu_add_right {p q : ℕ} (c : ℚ) (f g : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (a : _root_.Formalism.BasicNotions.TH.Ix p q) :
    _root_.Formalism.BasicNotions.TH.shiftNu c (fun x => f x + g x) a = _root_.Formalism.BasicNotions.TH.shiftNu c f a + g a := by
  cases a <;> simp only [_root_.Formalism.BasicNotions.TH.shiftNu] <;> ring

open MvPolynomial in
private lemma degW_blattner_le_of_sign_lemma {p q : ℕ} (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c : ℚ) (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam) (s : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (hs : ∀ a, s a = 1 ∨ s a = -1)
    (hsν : ∀ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a = |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|)
    (hmono : ∀ a b, lam b < lam a → s b ≤ s a)
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  obtain ⟨m, hm, rfl⟩ := hC μ v hv
  set Δ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ := fun x =>
    ∑ a, ∑ b, (m a b : ℚ) * ((if x = a then 1 else 0) - if x = b then 1 else 0) with hΔ
  have key : ∑ x, s x * Δ x = ∑ a, ∑ b, (m a b : ℚ) * (s a - s b) := by
    simp only [hΔ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hnn : 0 ≤ ∑ x, s x * Δ x := by
    rw [key]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : m a b = 0
    · simp [h0]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hmono a b (hm a b h0)))
  have habs : ∀ x y : ℚ, ∀ a, s a * (x + y) ≤ |x + y| := by
    intro x y a
    rcases hs a with h | h <;> rw [h]
    · simpa using le_abs_self (x + y)
    · simpa using neg_le_abs (x + y)
  unfold _root_.Formalism.BasicNotions.TH.degW
  calc ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|
      = ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a := by simp [hsν]
    _ ≤ ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + ∑ x, s x * Δ x := le_add_of_nonneg_right hnn
    _ = ∑ a, s a * (_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a) := by
        rw [← Finset.sum_add_distrib]; simp [mul_add]
    _ ≤ ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a| :=
        Finset.sum_le_sum fun a _ => habs _ _ a
    _ = ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (fun x => _root_.Formalism.BasicNotions.TH.blattner lam x + Δ x) a| := by
        simp [shiftNu_add_right]


open MvPolynomial in
theorem _root_.GlobalTheory.FlowLemma.degW_blattner_le (p q : ℕ) (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c θ : ℚ)
    (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam)
    (hs : ∀ a, (θ < lam a → 0 ≤ _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a) ∧
      (lam a ≤ θ → _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a ≤ 0))
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  refine degW_blattner_le_of_sign_lemma M lam c hC (fun a => if θ < lam a then 1 else -1)
    (fun a => ?_) (fun a => ?_) (fun a b hab => ?_) μ v hv
  · split_ifs <;> simp
  · split_ifs with h
    · simp [abs_of_nonneg ((hs a).1 h)]
    · simp [abs_of_nonpos ((hs a).2 (not_lt.1 h))]
  · beta_reduce
    split_ifs with h1 h2 h2 <;> first | exact absurd (h1.trans hab) h2 | norm_num

end GlobalTheory.FlowLemma
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockNormBound

theorem norm_sum_sq_of_orth {κ H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Finset κ) (v : κ → H) (h : ∀ a b, a ≠ b → inner ℂ (v a) (v b) = 0) :
    ‖∑ a ∈ s, v a‖ ^ 2 = ∑ a ∈ s, ‖v a‖ ^ 2 := by

  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [inner_sum, Finset.sum_eq_single a, inner_self_eq_norm_sq]
  · intro b _ hb; exact h a b (Ne.symm hb)
  · intro h'; exact absurd ha h'

def mfact {σ : Type} (α : σ →₀ ℕ) : ℝ := α.prod (fun _ k => (k.factorial : ℝ))

theorem mfact_nonneg {σ : Type} (α : σ →₀ ℕ) : 0 ≤ mfact α :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem mfact_add {σ : Type} [DecidableEq σ] (α : σ →₀ ℕ) (i : σ) :
    mfact (α + Finsupp.single i 1) = ((α i : ℝ) + 1) * mfact α := by
  unfold mfact
  rw [← Finsupp.mul_prod_erase' (α + Finsupp.single i 1) i _ (by simp),
    ← Finsupp.mul_prod_erase' α i _ (by simp)]
  have : Finsupp.erase i (α + Finsupp.single i 1) = Finsupp.erase i α := by
    ext j; by_cases hj : j = i
    · simp [hj]
    · simp [Finsupp.erase_ne hj, Finsupp.single_eq_of_ne hj]
  rw [this]
  simp [Nat.factorial_succ]
  ring

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem norm_mono (h : IsFockIP ι) (α : σ →₀ ℕ) : ‖ι (monomial α 1)‖ ^ 2 = mfact α := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h α α, if_pos rfl]
  have : α.prod (fun _ k => (k.factorial : ℂ)) = ((mfact α : ℝ) : ℂ) := by
    simp [mfact, Finsupp.prod]
  rw [this]; simp

theorem norm_comb (h : IsFockIP ι) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℂ)
    (g : (σ →₀ ℕ) → (σ →₀ ℕ)) (hg : ∀ a b, a ≠ b → c a ≠ 0 → c b ≠ 0 → g a ≠ g b) :
    ‖ι (∑ a ∈ s, monomial (g a) (c a))‖ ^ 2 = ∑ a ∈ s, ‖c a‖ ^ 2 * mfact (g a) := by
  have e : ∀ a, ι (monomial (g a) (c a)) = c a • ι (monomial (g a) 1) := by
    intro a; rw [← map_smul, smul_monomial]; simp

  rw [map_sum, norm_sum_sq_of_orth]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [e, norm_smul, mul_pow, norm_mono h]
  · intro a b hab
    rw [e, e]
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    rw [inner_smul_left, inner_smul_right, h, if_neg (hg a b hab ha hb)]; simp

theorem fock_norm_bounds (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (h : IsFockIP ι) (i : σ) (d : ℕ)
    (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧
      ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  have hd : ∀ a ∈ P.support, (a i : ℝ) ≤ d := by
    intro a ha
    have h1 : a i ≤ P.degreeOf i := monomial_le_degreeOf i ha
    exact_mod_cast h1.trans ((degreeOf_le_totalDegree P i).trans hP)
  have h0 : ‖ι P‖ ^ 2 = ∑ a ∈ P.support, ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := by
    conv_lhs => rw [P.as_sum]
    exact norm_comb h _ _ id (fun a b hab _ _ => hab)
  have h1 : X i * P = ∑ a ∈ P.support, monomial (a + Finsupp.single i 1) (AddMonoidAlgebra.coeff P a) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [X, monomial_mul, add_comm, one_mul]
  have h2 : pderiv i P = ∑ a ∈ P.support, monomial (a - Finsupp.single i 1) (AddMonoidAlgebra.coeff P a * a i) := by
    conv_lhs => rw [P.as_sum]

    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pderiv_monomial]
  have hsub : ∀ a : σ →₀ ℕ, a i ≠ 0 → a - Finsupp.single i 1 + Finsupp.single i 1 = a := by
    intro a ha
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha))
  constructor
  · rw [h1, norm_comb h _ _ _ (fun a b hab _ _ hh => hab (add_right_cancel hh)), h0,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [mfact_add]
    have := hd a ha
    have h3 : 0 ≤ ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
    nlinarith
  · rw [h2, norm_comb h, h0, Finset.mul_sum]
    · refine Finset.sum_le_sum fun a ha => ?_
      have h3 : 0 ≤ ‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
      by_cases hz : a i = 0
      · simp only [hz, Nat.cast_zero, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (by positivity) h3
      have h4 := mfact_add (a - Finsupp.single i 1) i
      rw [hsub a hz] at h4
      have h5 : (((a - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℝ) + 1 = a i := by
        have := congrArg (fun f : σ →₀ ℕ => f i) (hsub a hz)
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        exact_mod_cast this
      rw [h5] at h4
      rw [norm_mul, Complex.norm_natCast]
      calc (‖AddMonoidAlgebra.coeff P a‖ * a i) ^ 2 * mfact (a - Finsupp.single i 1)
          = a i * (‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a) := by rw [h4]; ring
        _ ≤ d * (‖AddMonoidAlgebra.coeff P a‖ ^ 2 * mfact a) := mul_le_mul_of_nonneg_right (hd a ha) h3
    · intro a b hab ha hb hh
      have ha' : a i ≠ 0 := fun z => ha (by simp [z])
      have hb' : b i ≠ 0 := fun z => hb (by simp [z])
      apply hab
      rw [← hsub a ha', hh, hsub b hb']

end GlobalTheory.FockNormBound
end
end

section

open IsLocalRing GlobalTheory.UT

namespace GlobalTheory.Poinc

theorem sumI_maximalIdeal_unique :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (Ix : Type) (x : Ix → R) (s s' : R),
      SumI (maximalIdeal R) x s → SumI (maximalIdeal R) x s' → s = s' := by
  classical
  intro R _ _ _ Ix x s s' ⟨N, _, _, _, h⟩ ⟨N', _, _, _, h'⟩
  have key : ∀ n : ℕ, s - s' ∈ maximalIdeal R ^ n := by
    intro n
    obtain ⟨S, hS⟩ := h n
    obtain ⟨S', hS'⟩ := h' n
    have le : ∀ M : Submodule R R, maximalIdeal R ^ n • M ≤ maximalIdeal R ^ n := fun M =>
      Submodule.smul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
    have h1 := le _ (hS (S ∪ S') Finset.subset_union_left)
    have h2 := le _ (hS' (S ∪ S') Finset.subset_union_right)
    have h3 := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_right] at h3
  have hb : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have : s - s' ∈ ⨅ n : ℕ, maximalIdeal R ^ n := Ideal.mem_iInf.2 key
  rw [hb, Ideal.mem_bot] at this
  exact sub_eq_zero.1 this

end GlobalTheory.Poinc
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.heckeThetaKernel_poisson_summation : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → ∃ (a : (I → ℂ) → ℂ) (κ : ℂ), (∀ ε : ℝ, 0 < ε → Summable (fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))) ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ v, a v ≠ 0 → v ≠ 0 → δ ≤ ‖v‖) ∧ ∀ y : I → ℝ, GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y = κ * (Real.exp (-∑ i, y i) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n (-y) := by
  first | exact @GlobalTheory.HeckePoisson.theta_poisson | exact GlobalTheory.HeckePoisson.theta_poisson | (intros; apply GlobalTheory.HeckePoisson.theta_poisson <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  first | exact @GlobalTheory.SecGlue.exists_lift_of_chart_lifts | exact GlobalTheory.SecGlue.exists_lift_of_chart_lifts | (intros; apply GlobalTheory.SecGlue.exists_lift_of_chart_lifts <;> assumption)
end
