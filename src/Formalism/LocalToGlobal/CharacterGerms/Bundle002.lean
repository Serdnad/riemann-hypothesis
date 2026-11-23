module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle001
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Lemmata.MiscLemmasH.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Formalism.IncomingBounds.Bundle001

@[expose] public section

section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

section Eig

variable {C : Type} [Field C] [CharZero C] {n : ℕ}

theorem sq_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (u : Fin n → C)
    (h2 : Matrix.mulVec t (Matrix.mulVec t u - μ • u) = μ • (Matrix.mulVec t u - μ • u)) :
    Matrix.mulVec t u = μ • u := by
  set x := Matrix.mulVec t u - μ • u with hxdef
  have htu : Matrix.mulVec t u = μ • u + x := by rw [hxdef]; abel
  have hx : ∀ k : ℕ, Matrix.mulVec (t ^ k) x = μ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' t k, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h2, smul_smul, ← pow_succ]
  have hu : ∀ k : ℕ, Matrix.mulVec (t ^ (k + 1)) u = μ ^ (k + 1) • u + (((k : C) + 1) * μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp [htu]
    | succ k ih =>
      rw [pow_succ' t (k + 1), ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, htu, h2]
      push_cast
      module
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hA := hu (r + 1)
  rw [show r + 1 + 1 = r + 2 from rfl, ht, htu] at hA
  have hB := hx (r + 2)
  rw [ht, h2] at hB
  suffices hx0 : x = 0 by rw [htu, hx0, add_zero]
  by_cases hμ : μ = 0
  · subst hμ
    simp at hA
    exact hA
  · have hB' : (μ ^ (r + 2) - μ) • x = 0 := by rw [sub_smul, ← hB, sub_self]
    rcases smul_eq_zero.mp hB' with h | h
    · have h1 : μ ^ (r + 1) = 1 := by
        have e1 : μ ^ (r + 1) * μ = 1 * μ := by
          rw [← pow_succ, one_mul]
          exact sub_eq_zero.mp h
        exact mul_right_cancel₀ hμ e1
      rw [sub_eq_zero.mp h, h1, mul_one] at hA
      have hA2 := add_left_cancel hA
      have e : (((r + 1 : ℕ) : C) + 1) • x = ((r : C) + 1) • x + x := by
        push_cast
        rw [add_smul, one_smul]
      rw [e] at hA2
      have h3 : ((r : C) + 1) • x = 0 := add_eq_right.mp hA2.symm
      exact (smul_eq_zero.mp h3).resolve_left (Nat.cast_add_one_ne_zero r)
    · exact h

theorem gen_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (w : Fin n → C)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLin' t : Module.End C (Fin n → C)) μ) : Matrix.mulVec t w = μ • w := by
  rw [Module.End.mem_maxGenEigenspace] at hw
  obtain ⟨k, hk⟩ := hw
  induction k generalizing w with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hk
    subst hk
    simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hk
    have hy := ih _ hk
    have e : (Matrix.toLin' t - μ • (1 : Module.End C (Fin n → C))) w = Matrix.mulVec t w - μ • w := by
      simp [Matrix.toLin'_apply]
    rw [e] at hy
    exact sq_to_eig hq t ht μ w hy

end Eig

theorem jointEig_holds : JointEigSt := by
  intro C _ _ hC n q hq T hT hcomm v
  let f : T → Module.End C (Fin n → C) := fun t => Matrix.toLin' t.1
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun i j _ => by
      show (Matrix.toLin' i.1).comp (Matrix.toLin' j.1) = (Matrix.toLin' j.1).comp (Matrix.toLin' i.1)
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm i.1 i.2 j.1 j.2])
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hv : v ∈ ⨆ χ : T → C, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun v => ∃ (m : ℕ) (w : Fin m → Fin n → C),
    v = ∑ j, w j ∧ ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j) hv ?_ ?_ ?_
  · intro χ x hx
    refine ⟨1, fun _ => x, by simp, fun _ t ht => ⟨χ ⟨t, ht⟩, gen_to_eig hq t (hT t ht) _ x ?_⟩⟩
    exact (Submodule.mem_iInf _).mp hx ⟨t, ht⟩
  · exact ⟨0, Fin.elim0, by simp, fun j => Fin.elim0 j⟩
  · rintro x y ⟨m₁, w₁, rfl, h₁⟩ ⟨m₂, w₂, rfl, h₂⟩
    refine ⟨m₁ + m₂, Fin.append w₁ w₂, by rw [Fin.sum_univ_add]; simp, fun j => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using h₁ j
    · simpa using h₂ j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section T

variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]

theorem tauX_tmul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) (z : ℤ_[l]) (x : OE) :
    tauX τ (z ⊗ₜ x) = algebraMap ℤ_[l] R z * τ x := by
  simp [tauX]

theorem natCast_eq_tmul (k : ℕ) : ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) = (k : ℤ_[l]) ⊗ₜ (1 : OE) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, ih, Nat.cast_succ, TensorProduct.add_tmul, Algebra.TensorProduct.one_def]

theorem natCast_tmul (k : ℕ) (y : OE) : (k : ℤ_[l]) ⊗ₜ[ℤ] y = (1 : ℤ_[l]) ⊗ₜ[ℤ] ((k : OE) * y) := by
  have h1 : (k : ℤ_[l]) = (k : ℤ) • (1 : ℤ_[l]) := by simp
  have h2 : ((k : OE) * y) = (k : ℤ) • y := by simp
  rw [h1, h2, TensorProduct.smul_tmul]

theorem natCast_mul_tmul (k : ℕ) (z : ℤ_[l]) (y : OE) :
    ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (z ⊗ₜ y) = ((k : ℤ_[l]) * z) ⊗ₜ y := by
  rw [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem decomp (s : ℤ_[l] ⊗[ℤ] OE) :
    ∃ (x : OE) (s' : ℤ_[l] ⊗[ℤ] OE), s = 1 ⊗ₜ x + ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * s' := by
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z y =>
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hn
    obtain ⟨z', hz'⟩ := hn
    refine ⟨(n : OE) * y, z' ⊗ₜ y, ?_⟩
    rw [natCast_mul_tmul, ← natCast_tmul, ← TensorProduct.add_tmul, mul_comm (l : ℤ_[l]) z', hz']
    congr 1
    ring
  | add a b ha hb =>
    obtain ⟨x, s', hs⟩ := ha
    obtain ⟨x', t', ht⟩ := hb
    refine ⟨x + x', s' + t', ?_⟩
    rw [hs, ht, TensorProduct.tmul_add]
    ring

theorem completeA [Module.Free ℤ OE] [Module.Finite ℤ OE] :
    IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := by
  classical
  have key : ∀ (A : Type) [CommRing A] (a x : A) (n : ℕ),
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule A A) ↔ ∃ s, x = a ^ n * s := by
    intro A _ a x n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, -, hs⟩
      exact ⟨s, by rw [← hs, smul_eq_mul]⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, Submodule.mem_top, by rw [hs, smul_eq_mul]⟩
  let bR := Algebra.TensorProduct.basis ℤ_[l] (Module.Free.chooseBasis ℤ OE)
  have hl : ∀ (n : ℕ) (s : ℤ_[l] ⊗[ℤ] OE),
      ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) ^ n * s = ((l : ℤ_[l]) ^ n) • s := by
    intro n s
    rw [Algebra.smul_def, map_pow, map_natCast]
  have hcoord : ∀ (n : ℕ) (x : ℤ_[l] ⊗[ℤ] OE),
      (∃ s, x = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) ^ n * s) ↔ ∀ i, ∃ c, bR.repr x i = (l : ℤ_[l]) ^ n * c := by
    intro n x
    constructor
    · rintro ⟨s, rfl⟩ i
      refine ⟨bR.repr s i, ?_⟩
      rw [hl, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro h
      choose c hc using h
      refine ⟨∑ i, c i • bR i, ?_⟩
      rw [hl]
      apply bR.repr.injective
      ext i
      rw [hc i, LinearEquiv.map_smul, Finsupp.smul_apply, bR.repr_sum_self, smul_eq_mul]
  have hZ : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have haus : ∀ x : ℤ_[l] ⊗[ℤ] OE, (∀ n : ℕ, x ≡ 0 [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ n • ⊤ :
      Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))]) → x = 0 := by
    intro x hx
    apply bR.repr.injective
    apply Finsupp.ext
    intro i
    rw [map_zero, Finsupp.zero_apply]
    apply hZ.toIsHausdorff.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, key]
    have h := hx n
    rw [SModEq.sub_mem, sub_zero, key, hcoord] at h
    exact h i
  have prec : ∀ f : ℕ → ℤ_[l] ⊗[ℤ] OE, (∀ {m n : ℕ}, m ≤ n → f m ≡ f n
      [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ m • ⊤ : Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))]) →
      ∃ L, ∀ n, f n ≡ L [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ n • ⊤ :
        Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))] := by
    intro f hf
    have hci : ∀ i, ∃ Li : ℤ_[l], ∀ n, bR.repr (f n) i ≡ Li
        [SMOD (Ideal.span {((l : ℕ) : ℤ_[l])} ^ n • ⊤ : Submodule ℤ_[l] ℤ_[l])] := by
      intro i
      apply hZ.toIsPrecomplete.prec
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem, key, hcoord] at h
      rw [SModEq.sub_mem, key]
      obtain ⟨c, hc⟩ := h i
      exact ⟨c, by rw [← hc, map_sub, Finsupp.sub_apply]⟩
    choose L hL using hci
    refine ⟨∑ i, L i • bR i, fun n => ?_⟩
    rw [SModEq.sub_mem, key, hcoord]
    intro i
    have h := hL i n
    rw [SModEq.sub_mem, key] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [map_sub, Finsupp.sub_apply, bR.repr_sum_self, hc]⟩
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := ⟨haus⟩
  haveI : IsPrecomplete (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := ⟨fun f hf => prec f hf⟩
  exact IsAdicComplete.mk

variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]

def chi (τ : OE →+* R) : (ℤ_[l] ⊗[ℤ] OE) →+* ResidueField R := (residue R).comp (tauX τ).toRingHom

theorem chi_apply (τ : OE →+* R) (s : ℤ_[l] ⊗[ℤ] OE) : chi τ s = residue R (tauX τ s) := rfl

theorem chi_one_tmul (τ : OE →+* R) (x : OE) : chi τ ((1 : ℤ_[l]) ⊗ₜ[ℤ] x) = residue R (τ x) := by
  rw [chi_apply, tauX_tmul, map_one, one_mul]

theorem chi_l (hl : ((l : ℕ) : R) ∈ maximalIdeal R) (τ : OE →+* R) (s : ℤ_[l] ⊗[ℤ] OE) :
    chi τ (((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * s) = 0 := by
  have hl0 : ((l : ℕ) : ResidueField R) = 0 := by
    rw [← map_natCast (residue R), residue_eq_zero_iff]
    exact hl
  rw [map_mul, map_natCast, hl0, zero_mul]

theorem chi_alg (τ : OE →+* R) (r : ℤ_[l]) :
    chi τ (algebraMap ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) r) = ((residue R).comp (algebraMap ℤ_[l] R)) r := by
  rw [chi_apply, AlgHom.commutes]
  rfl

variable {d : ℕ} [NeZero d] (em : ZMod d → OE →+* R)

theorem res_frob (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (a : ZMod d) (x : OE) :
    residue R (em (a + 1) x) = residue R (em a x) ^ l := by
  have h := (residue_eq_zero_iff _).mpr (hfrob a x)
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact h

theorem res_frob_pow (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (a : ZMod d) (x : OE) :
    ∀ k : ℕ, residue R (em (a + (k : ZMod d)) x) = residue R (em a x) ^ (l ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, res_frob em hfrob, ih, ← pow_mul, Nat.pow_succ l k]

theorem mem_all (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {x : OE}
    (h : em 0 x ∈ maximalIdeal R) (a : ZMod d) : em a x ∈ maximalIdeal R := by
  have hk := res_frob_pow em hfrob 0 x a.val
  rw [zero_add, ZMod.natCast_zmod_val] at hk
  rw [← residue_eq_zero_iff, hk, (residue_eq_zero_iff _).mpr h,
    zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]

theorem key (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {s : ℤ_[l] ⊗[ℤ] OE}
    (hs : e * s = s) (h0 : chi (em 0) s = 0) : ∃ w, s = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * w := by
  obtain ⟨x, s', hs'⟩ := decomp s
  have hx0 : em 0 x ∈ maximalIdeal R := by
    rw [hs', map_add (f := _), chi_one_tmul, chi_l hl, add_zero, residue_eq_zero_iff] at h0
    exact h0
  obtain ⟨y, hy⟩ := hε x (mem_all em hfrob hx0)
  have hkey : (1 : ℤ_[l]) ⊗ₜ[ℤ] ε * (1 ⊗ₜ x) = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (1 ⊗ₜ y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hy, natCast_mul_tmul, mul_one, natCast_tmul]
  refine ⟨1 ⊗ₜ y + z * (1 ⊗ₜ x) + e * s', ?_⟩
  linear_combination (-1 : ℤ_[l] ⊗[ℤ] OE) * hs + e * hs' + (1 ⊗ₜ x) * he + hkey

end T

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

def VLim (V : VF C) {N : Type} (m : ℕ → ℕ → N → C) (m' : ℕ → N → C) : Prop :=
  ∀ (K : ℝ) (s : ℕ) (n : N), ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (m' s n - m k s n)

theorem VLim.mul_right {V : VF C} {N : Type} {m : ℕ → ℕ → N → C} {m' : ℕ → N → C} (h : VLim V m m')
    (y : ℕ → N → C) : VLim V (fun k => m k * y) (m' * y) := by
  intro K s n
  by_cases hy : y s n = 0
  · exact ⟨0, fun k _ => by simp [hy, VF.Ge.zero]⟩
  · have hne : V.v (y s n) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]; exact hy
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    obtain ⟨k0, hk0⟩ := h (K - r) s n
    refine ⟨k0, fun k hk => ?_⟩
    have e : (m' * y) s n - (m k * y) s n = (m' s n - m k s n) * y s n := by
      simp only [Pi.mul_apply]; ring
    rw [e]
    have hyr : V.Ge r (y s n) := by unfold VF.Ge; rw [← hr]
    have := (hk0 k hk).mul hyr
    simpa using this

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

variable {C : Type} [Field C]

def IntS (V : VF C) {σ : Type} (F : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, V.Ge 0 (MvPowerSeries.coeff μ F)

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing Polynomial

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Complete

variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)


end Complete

section Lift

variable {A : Type} [CommRing A] (I : Ideal A)

theorem lift_idem [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  first | exact Bl.SecondBlockLemmaI.goal1 .. | (apply Bl.SecondBlockLemmaI.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaI.goal1 <;> assumption)

theorem idem_zero [IsHausdorff I A] {f : A} (h : f * f = f) (hf : f ∈ I) : f = 0 := by
  refine IsHausdorff.haus (I := I) ‹_› f fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  rcases n with _ | n
  · simp
  · have he : IsIdempotentElem f := h
    rw [← he.pow_succ_eq n]
    exact Ideal.pow_mem_pow hf _

end Lift

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

section

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

def LinN {C : Type} [CommRing C] {dd : ℕ} (f : Pt C 1 dd) : Prop :=
  ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (f i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)

section Gen

variable {C : Type} [CommRing C] {dd : ℕ}

theorem linN_const {f : Pt C 1 dd} (hf : LinN f) (i : Fin dd) : constantCoeff (f i) = 0 := by
  have h := hf i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h, MvPowerSeries.coeff_zero_X]

end Gen

end LogEx

end Formalism.L2.FormalSeriesBounds
end
end
