module

public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_dvdPow {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hx : ∀ k, DvdPow ϖ (k + 1) x) : x = 0 := by
  by_contra h0
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have key : ∀ N : ℕ, Valued.v x ≤ WithZero.exp (-(N : ℤ)) := by
    intro N
    obtain ⟨b, hb, hxb⟩ := hx N
    rw [hxb, map_mul, map_pow, hϖ]
    calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
          mul_le_mul' le_rfl hb
      _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
          rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
      _ ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by push_cast; omega)
  obtain ⟨m, hm⟩ : ∃ m, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have h1 := key ((-m).toNat + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  have := Int.self_le_toNat (-m)
  push_cast at h1
  omega

end GlobalTheory.Hk3.IntWittBase

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_map {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {m : ℕ} {a : L}
    (h : DvdPow ϖ m a) : DvdPow ϖ m (σ a) := by
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨σ b, ?_, by rw [map_mul, map_pow, hσϖ]⟩
  show Valued.v (σ b) ≤ 1
  rw [hσv]; exact hb

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_apply (σ : L →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ A i j = σ (A j i) := rfl

theorem int_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L) (hB : ∀ i j, B i j ∈ intL L) :
    ∀ i j, (A * B) i j ∈ intL L := by
  intro i j; rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => mul_mem (hA i l) (hB l j)

theorem int_cT {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ intL L) : ∀ i j, cT σ A i j ∈ intL L := by
  intro i j; rw [cT_apply]; show Valued.v (σ _) ≤ 1; rw [hσv]; exact hA j i

theorem mc_mul_left {ϖ : L} {n m : ℕ} {A D : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L)
    (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m ((A * D) i j) := by
  intro i j; rw [Matrix.mul_apply]; exact dvdPow_sum _ _ fun l _ => dvdPow_mul_int (hD l j) (hA i l)

theorem mc_mul_right {ϖ : L} {n m : ℕ} {D B : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j))
    (hB : ∀ i j, B i j ∈ intL L) : ∀ i j, DvdPow ϖ m ((D * B) i j) := by
  intro i j; rw [Matrix.mul_apply]
  exact dvdPow_sum _ _ fun l _ => by rw [mul_comm]; exact dvdPow_mul_int (hD i l) (hB l j)

theorem mc_cT {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {n m : ℕ}
    {D : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m (cT σ D i j) := by
  intro i j; rw [cT_apply]; exact dvdPow_map hσv hσϖ (hD j i)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_sub (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) : cT σ (A - B) = cT σ A - cT σ B := by
  ext i j; simp [cT_apply]

end GlobalTheory.Hk3.IntWittBase
end

section

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_mem_intVec_of_int {a b : ℕ} {M : Matrix (Fin a) (Fin b) L}
    (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) {v : Fin b → L} (hv : v ∈ intVec L b) :
    M.mulVec v ∈ intVec L a := by
  rw [mem_intVec] at hv ⊢
  intro i
  change (∑ j, M i j * v j) ∈ Formalism.UG.intL L
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

theorem entry_mem_of_mem_GLint {n : ℕ} {g : GL (Fin n) L} (hg : g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨g0, rfl⟩ := hg
  exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2

theorem latIdx_add_int {a b : ℕ} (x u : Matrix (Fin a) (Fin b) L) (hu : u ∈ intMat L a b) :
    latIdx (x + u) = latIdx x := by
  have hf : (fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec (x + u) (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)) =
      fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    funext v
    rw [Matrix.add_mulVec, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff _).2 (mulVec_mem_intVec_of_int ((mem_intMat u).1 hu) v.2), add_zero]
  unfold latIdx
  rw [hf]

def quotMul {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) :
    (Fin a → L) ⧸ intVec L a →+ (Fin a → L) ⧸ intVec L a :=
  QuotientAddGroup.map (intVec L a) (intVec L a) (Matrix.mulVecLin M).toAddMonoidHom
    fun _ hv => mulVec_mem_intVec_of_int hM hv

theorem quotMul_mk {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) (v : Fin a → L) :
    quotMul M hM (QuotientAddGroup.mk v) = QuotientAddGroup.mk (M.mulVec v) := rfl

theorem latIdx_GLint_mul {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) (h : GL (Fin a) L)
    (hh : h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = latIdx x := by
  have h1 := entry_mem_of_mem_GLint hh
  have h2 := entry_mem_of_mem_GLint (inv_mem hh)
  have hinj : Function.Injective (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
    have hl : Function.LeftInverse (quotMul ((h⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) h2)
        (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H v =>
        rw [quotMul_mk, quotMul_mk, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
    exact hl.injective
  have hr : (Set.range fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec ((h : Matrix (Fin a) (Fin a) L) * x) (v : Fin b → L)) :
        (Fin a → L) ⧸ intVec L a)) =
      quotMul (h : Matrix (Fin a) (Fin a) L) h1 '' Set.range fun v : intVec L b =>
        (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    rw [← Set.range_comp]
    congr 1
    funext v
    exact congrArg QuotientAddGroup.mk (Matrix.mulVec_mulVec _ _ _).symm
  unfold latIdx
  rw [hr, Nat.card_image_of_injective hinj]

theorem latIdx_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x :=
  fun _ _ _ _ _ x => ⟨fun u hu => latIdx_add_int x u hu, fun h hh => latIdx_GLint_mul x h hh⟩

end GlobalTheory.Hk3.HoweDuality

end
end

section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_pow_mul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (z : L) :
    ∃ n : ℕ, Valued.v (ϖ ^ n * z) ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m := ⟨_, (WithZero.exp_log hv).symm⟩
  refine ⟨m.toNat, ?_⟩
  rw [map_mul, map_pow, hϖ, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul]
  have := Int.self_le_toNat m
  omega

theorem pow_mul_int_mono {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) {z : L} {n m : ℕ} (hnm : n ≤ m)
    (h : Valued.v (ϖ ^ n * z) ≤ 1) : Valued.v (ϖ ^ m * z) ≤ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm (ϖ ^ n), mul_assoc, map_mul, map_pow]
  exact mul_le_one' (pow_le_one' hϖ k) h

theorem exists_pow_smul_int {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) : ∃ K : ℕ, ∀ i j, Valued.v (ϖ ^ K * x i j) ≤ 1 := by
  choose n hn using fun p : Fin a × Fin b => exists_pow_mul_int hϖ (x p.1 p.2)
  have hϖ1 : Valued.v ϖ ≤ 1 := by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  refine ⟨∑ p, n p, fun i j => pow_mul_int_mono hϖ1 ?_ (hn (i, j))⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))

theorem finite_range_latIdx {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) L) :
    (Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a)).Finite := by
  obtain ⟨-, -, -, hϖ, -, h2q, hc⟩ := hU
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hV
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ1 : V ϖ ≤ 1 := by rw [hV, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hc' : Nat.card (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) = q ^ 2 := hc
  haveI : Finite (V.valuationSubring ⧸ IsLocalRing.maximalIdeal V.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ (by omega))
  let ϖO : V.valuationSubring := ⟨ϖ, hϖ1⟩
  have hmax : IsLocalRing.maximalIdeal V.valuationSubring ≤ Ideal.span {ϖO} := by
    intro z hz
    rw [Valuation.mem_maximalIdeal_iff] at hz
    rw [Ideal.mem_span_singleton']
    by_cases hz0 : (z : L) = 0
    · exact ⟨0, by ext; simp [hz0]⟩
    have hϖ0 : ϖ ≠ 0 := by
      intro e; rw [e, map_zero] at hϖ'; exact WithZero.zero_ne_coe hϖ'
    have hz' : Valued.v (z : L) < 1 := hz
    have hle : Valued.v (z : L) ≤ Valued.v ϖ := by
      have hv : Valued.v (z : L) ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
      rw [hϖ', ← WithZero.exp_log hv, WithZero.exp_le_exp]
      rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz'
      omega
    have hq1 : Valued.v ((z : L) / ϖ) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (by rw [hϖ']; exact WithZero.exp_pos)]
      exact hle
    refine ⟨⟨(z : L) / ϖ, hq1⟩, ?_⟩
    ext
    simp [ϖO, div_mul_cancel₀ _ hϖ0]
  haveI : Finite (V.valuationSubring ⧸ Ideal.span {ϖO}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hmax)
  obtain ⟨K, hK⟩ := exists_pow_smul_int hϖ' x
  haveI hfinK : Finite (V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) :=
    Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) K
  let g : (Fin b → V.valuationSubring ⧸ Ideal.span {ϖO} ^ K) → (Fin a → L) ⧸ intVec L a :=
    fun c => QuotientAddGroup.mk (Matrix.mulVec x fun j => (((c j).out : V.valuationSubring) : L))
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨u, rfl⟩
  have hu : ∀ j, Valued.v ((u : Fin b → L) j) ≤ 1 := (mem_intVec _).1 u.2
  refine ⟨fun j => Ideal.Quotient.mk _ ⟨(u : Fin b → L) j, hu j⟩, ?_⟩
  have hd : ∀ j, ∃ t : V.valuationSubring,
      (((Ideal.Quotient.mk (Ideal.span {ϖO} ^ K) ⟨(u : Fin b → L) j, hu j⟩).out : V.valuationSubring) : L) =
        (u : Fin b → L) j + ϖ ^ K * t := by
    intro j
    have hm := Ideal.Quotient.mk_out (I := Ideal.span {ϖO} ^ K)
      (⟨(u : Fin b → L) j, hu j⟩ : V.valuationSubring)
    have hm' := Ideal.Quotient.eq.1 hm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((Ideal.span_singleton_pow ϖO K).le hm')
    refine ⟨t, ?_⟩
    have := congrArg (fun w : V.valuationSubring => (w : L)) ht
    push_cast at this
    simp only [ϖO] at this
    linear_combination -this
  choose t ht using hd
  refine (QuotientAddGroup.eq.2 ?_).symm
  intro i
  simp only [Pi.add_apply, Pi.neg_apply, Matrix.mulVec, dotProduct, ht, mul_add, Finset.sum_add_distrib,
    neg_add_cancel_left]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [show x i j * (ϖ ^ K * (t j : L)) = (ϖ ^ K * x i j) * (t j : L) by ring]
  exact Subring.mul_mem _ (hK i j) (t j).2

theorem latIdx_le_of_ker : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) →
      ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  intro L _ _ ϖ σ q a b x y hU hN
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSx
  set Sy := Set.range fun u : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec y (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) with hSy
  let h : (Fin a → L) ⧸ intVec L a → (Fin a → L) ⧸ intVec L a := fun c =>
    if hc : ∃ u : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a) = c
    then QuotientAddGroup.mk (Matrix.mulVec y (hc.choose : Fin b → L)) else 0
  have hsub : Sy ⊆ h '' Sx := by
    rintro _ ⟨u, rfl⟩
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    have hc : ∃ u' : intVec L b, (QuotientAddGroup.mk (Matrix.mulVec x (u' : Fin b → L)) : (Fin a → L) ⧸ intVec L a) =
        QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) := ⟨u, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he ⊢
    have hd := hN ((u : Fin b → L) - (u' : Fin b → L)) (fun i => Subring.sub_mem _ (u.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  unfold latIdx
  rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard hsub (hfin.image h)).trans (Set.ncard_image_le hfin)

end GlobalTheory.Hk3.HoweDuality

end
end

section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt.ElemDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_int {m k : ℕ} {A : Matrix (Fin m) (Fin k) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    {c : Fin k → L} (hc : ∀ j, c j ∈ Formalism.UG.intL L) : ∀ i, (A *ᵥ c) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hc j)

theorem diag_mulVec_of_lt {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (j : Fin n) (hj : (j : ℕ) < n') :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) ⟨j, hj⟩ =
      (if 0 < a ⟨j, hj⟩ then ϖ⁻¹ ^ a ⟨j, hj⟩ else 0) * c j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : ¬ ((j : ℕ) = (b : ℕ)) := fun h => hb (Fin.ext h.symm)
    simp [this]
  · simp

theorem diag_mulVec_of_ge {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (i : Fin n') (hi : ¬ (i : ℕ) < n) :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) i = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro b _
  have : ¬ ((i : ℕ) = (b : ℕ)) := fun h => hi (h ▸ b.isLt)
  simp [this]

end GlobalTheory.Hk3.IntWitt.ElemDiv

end


open GlobalTheory.Hk3.IntWitt.ElemDiv in
theorem GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ V : GL (Fin n) L, V ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧ ∃ a : Fin n → ℕ,
      ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
        ((∀ i, (x *ᵥ ((V : Matrix (Fin n) (Fin n) L) *ᵥ c)) i ∈ Formalism.UG.intL L) ↔
          ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
  intro L _ _ ϖ hϖ n n' x
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := GlobalTheory.Hk3.smith_int_approx L ϖ hϖ n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  set O := Formalism.UG.intL L with hOdef
  let QO : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q i j, hQ i j⟩
  let QO' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q' i j, hQ' i j⟩
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) L) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hm1 : O.subtype.mapMatrix QO = Q := by ext i j; rfl
  have hm2 : O.subtype.mapMatrix QO' = Q' := by ext i j; rfl
  have e1 : QO * QO' = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQQ'])
  have e2 : QO' * QO = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQ'Q])
  let U : GL (Fin n) O := ⟨QO, QO', e1, e2⟩
  let V : GL (Fin n) L := ⟨Q, Q', hQQ', hQ'Q⟩
  refine ⟨V, ⟨U, Units.ext hm1⟩, fun j => if h : (j : ℕ) < n' then a ⟨j, h⟩ else 0, ?_⟩
  intro c hc
  set Dm : Matrix (Fin n') (Fin n) L :=
    Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDm
  have hPw : P *ᵥ (x *ᵥ (Q *ᵥ c)) = Dm *ᵥ c + (P * x * Q - Dm) *ᵥ c := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hEc : ∀ i, ((P * x * Q - Dm) *ᵥ c) i ∈ O := mulVec_int hE hc
  show (∀ i, (x *ᵥ (Q *ᵥ c)) i ∈ O) ↔ _
  constructor
  · intro hw j
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      have h1 := mulVec_int hP hw i
      rw [hPw, Pi.add_apply] at h1
      have := Subring.sub_mem _ h1 (hEc i)
      rwa [add_sub_cancel_right] at this
    by_cases hj : (j : ℕ) < n'
    · simp only [dif_pos hj]
      have h2 := hDc ⟨j, hj⟩
      rw [hDm, diag_mulVec_of_lt ϖ a c j hj] at h2
      split_ifs at h2 with ha
      · refine ⟨ϖ⁻¹ ^ a ⟨j, hj⟩ * c j, h2, ?_⟩
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow, one_mul]
      · have : a ⟨j, hj⟩ = 0 := by omega
        rw [this]; exact dvdPow_zero_iff.mpr (hc j)
    · simp only [dif_neg hj]; exact dvdPow_zero_iff.mpr (hc j)
  · intro hd
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      by_cases hi : (i : ℕ) < n
      · have hij : i = ⟨((⟨i, hi⟩ : Fin n) : ℕ), i.isLt⟩ := Fin.ext rfl
        rw [hij, hDm, diag_mulVec_of_lt ϖ a c ⟨i, hi⟩ i.isLt]
        split_ifs with ha
        · have h3 := hd ⟨i, hi⟩
          simp only [dif_pos i.isLt] at h3
          obtain ⟨b, hb, hcb⟩ := h3
          rw [hcb, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, one_mul]; exact hb
        · rw [zero_mul]; exact Subring.zero_mem _
      · rw [hDm, diag_mulVec_of_ge ϖ a c i hi]; exact Subring.zero_mem _
    have hPwi : ∀ i, (P *ᵥ (x *ᵥ (Q *ᵥ c))) i ∈ O := by
      intro i; rw [hPw, Pi.add_apply]; exact Subring.add_mem _ (hDc i) (hEc i)
    intro i
    have key : ∀ w : Fin n' → L, w = P' *ᵥ (P *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
    rw [key (x *ᵥ (Q *ᵥ c))]; exact mulVec_int hP' hPwi i
end

section


theorem _root_.GlobalTheory.T.phaseCondition_integral_basisChange : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ)
    (P : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) →
    (∀ i j, P i j ∈ Formalism.UG.intL L) → (∀ i j, Q' i j ∈ Formalism.UG.intL L) → Q * Q' = 1 →
    ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (P * x * Q)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))) + σ (δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))))) / 2) = 1) := by
  first | exact @GlobalTheory.phaseCondition_basisChange | exact GlobalTheory.phaseCondition_basisChange | (intros; apply GlobalTheory.phaseCondition_basisChange <;> assumption)
end

section


theorem _root_.GlobalTheory.T.smith_normal_form_integral_matrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ (P P' : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L) (a : Fin n' → ℕ),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ Q * Q' = 1 ∧
      ∀ i j, (P * x * Q - Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.smith_int_approx | exact GlobalTheory.Hk3.smith_int_approx | (intros; apply GlobalTheory.Hk3.smith_int_approx <;> assumption)
end
