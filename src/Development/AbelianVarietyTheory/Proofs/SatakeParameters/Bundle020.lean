module

public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle012
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
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
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_span_fin_of_fg {L : Type} [Field L] (O : ValuationSubring L) (n : ℕ) (N : Submodule O (Fin n → L))
    (hN : N.FG) : ∃ c : Fin n → Fin n → L, N = Submodule.span O (Set.range c) := by
  classical
  have : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  have : Module.Flat O N :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let k := Module.finrank O N
  let B : Module.Basis (Fin k) O N := Module.finBasis O N
  have hli : LinearIndependent O (fun i => (B i : Fin n → L)) :=
    B.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hliL : LinearIndependent L (fun i => (B i : Fin n → L)) :=
    (LinearIndependent.iff_fractionRing O L).1 hli
  have hk : k ≤ n := by simpa using hliL.fintype_card_le_finrank
  refine ⟨fun j => if h : (j : ℕ) < k then (B ⟨j, h⟩ : Fin n → L) else 0, le_antisymm ?_ ?_⟩
  · have hsp : N = Submodule.span O (Set.range fun i => (B i : Fin n → L)) := by
      have h1 := congrArg (Submodule.map N.subtype) B.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
      exact h1.symm
    refine hsp.le.trans (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by simp⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : (j : ℕ) < k
    · simp [h]
    · simp [h]

theorem mem_span_cols_iff {L : Type} [Field L] (O : ValuationSubring L) {n : ℕ} {ι : Type} [Fintype ι]
    (M : Matrix (Fin n) ι L) (v : Fin n → L) :
    v ∈ Submodule.span O (Set.range fun j i => M i j) ↔ ∃ u : ι → L, (∀ i, u i ∈ O) ∧ v = M *ᵥ u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => c j, fun j => (c j).2, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun j => ⟨u j, hu j⟩, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_square_span_cols : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) ι L), ∃ b : Matrix (Fin n) (Fin n) L, ∀ v : Fin n → L,
      (∃ u : ι → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = M *ᵥ u) ↔ ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
  intro L _ _ n ι _ _ M
  let O : ValuationSubring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  obtain ⟨c, hc⟩ := exists_span_fin_of_fg O n (Submodule.span O (Set.range fun j i => M i j))
    (Submodule.fg_span (Set.finite_range _))
  refine ⟨Matrix.of fun i j => c j i, fun v => ?_⟩
  have h1 := mem_span_cols_iff O M v
  have h2 := mem_span_cols_iff O (Matrix.of fun i j => c j i) v
  rw [hc] at h1
  exact h1.symm.trans h2

end GlobalTheory.Hk3.HoweG
end

section

open Matrix

namespace GlobalTheory.Hk3

theorem one_add_maximal_inv_int (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (n : ℕ) (X : Matrix (Fin n) (Fin n) L) (hX : ∀ i j, Valued.v (X i j) < 1) :
    ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧
      ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  classical
  let v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v
  let O := v.valuationSubring
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, (hX i j).le⟩
  have hY : ∀ i j, IsLocalRing.residue O (Y i j) = 0 := fun i j => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L v).2 (hX i j)
  have h1 : (IsLocalRing.residue O).mapMatrix (1 + Y) = 1 := by
    rw [map_add (f := _), map_one]
    have : (IsLocalRing.residue O).mapMatrix Y = 0 := by
      ext i j; exact hY i j
    rw [this, add_zero]
  have hd : IsUnit (1 + Y).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1, det_one]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨Units.map (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _).toMonoidHom u, ?_, ?_⟩
  · show O.subtype.mapMatrix (u : Matrix (Fin n) (Fin n) O) = _
    rw [hu, map_add (f := _), map_one]
    rfl
  · intro i j
    rw [← map_inv]
    exact ((u⁻¹ : (Matrix (Fin n) (Fin n) O)ˣ).1 i j).2

end GlobalTheory.Hk3
end

section

namespace GlobalTheory.MatrixEntryBound

theorem entry_bound {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L}
    (hϖ : (Valued.v : L → WithZero (Multiplicative ℤ)) ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ ^ m * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by simp [hx]⟩
  · have hv : (Valued.v : L → WithZero (Multiplicative ℤ)) x ≠ 0 := by
      simpa using hx
    refine ⟨(WithZero.log (Valued.v x)).toNat, fun m hm => ?_⟩
    rw [map_mul, map_pow, hϖ, ← WithZero.exp_log hv, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    have : WithZero.log (Valued.v x) ≤ (m : ℤ) := by
      have := Int.self_le_toNat (WithZero.log (Valued.v x)); omega
    simp; omega

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}, (Valued.v : L → WithZero (Multiplicative ℤ)) ϖ = WithZero.exp (-1 : ℤ) → ∀ (M : Matrix (Fin n) (Fin n) L), ∃ (N : ℕ), ∀ (i j : Fin n), ϖ ^ N * M i j ∈ Formalism.UG.intL L := by
  intro L _ _ n ϖ hϖ M
  choose f hf using fun p : Fin n × Fin n => entry_bound hϖ (M p.1 p.2)
  refine ⟨Finset.univ.sup f, fun i j => ?_⟩
  unfold Formalism.UG.intL
  exact hf (i, j) _ (Finset.le_sup (f := f) (Finset.mem_univ (i, j)))

end GlobalTheory.MatrixEntryBound
end

section

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def DvdPow (ϖ : L) (k : ℕ) (a : L) : Prop := ∃ b ∈ Formalism.UG.intL L, a = ϖ ^ k * b

def IndepMod (ϖ : L) {ι : Type} [Fintype ι] {m : ℕ} (z : ι → Fin m → L) : Prop :=
  ∀ d : ι → L, (∀ i, d i ∈ Formalism.UG.intL L) → (∀ r, DvdPow ϖ 1 (∑ i, d i * z i r)) → ∀ i, DvdPow ϖ 1 (d i)

theorem dvdPow_zero_iff {ϖ a : L} : DvdPow ϖ 0 a ↔ a ∈ Formalism.UG.intL L := by
  constructor
  · rintro ⟨b, hb, rfl⟩; simpa using hb
  · intro h; exact ⟨a, h, by simp⟩

theorem dvdPow_add {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a + b) := by
  obtain ⟨c, hc, rfl⟩ := ha; obtain ⟨d, hd, rfl⟩ := hb
  exact ⟨c + d, (Formalism.UG.intL L).add_mem hc hd, by ring⟩

theorem dvdPow_neg {ϖ a : L} {k : ℕ} (ha : DvdPow ϖ k a) : DvdPow ϖ k (-a) := by
  obtain ⟨c, hc, rfl⟩ := ha
  exact ⟨-c, (Formalism.UG.intL L).neg_mem hc, by ring⟩

theorem dvdPow_sub {ϖ a b : L} {k : ℕ} (ha : DvdPow ϖ k a) (hb : DvdPow ϖ k b) : DvdPow ϖ k (a - b) := by
  rw [sub_eq_add_neg]; exact dvdPow_add ha (dvdPow_neg hb)

theorem dvdPow_zero (ϖ : L) (k : ℕ) : DvdPow ϖ k 0 := ⟨0, (Formalism.UG.intL L).zero_mem, by simp⟩

theorem dvdPow_mul_int {ϖ a c : L} {k : ℕ} (ha : DvdPow ϖ k a) (hc : c ∈ Formalism.UG.intL L) : DvdPow ϖ k (c * a) := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨c * b, (Formalism.UG.intL L).mul_mem hc hb, by ring⟩

theorem dvdPow_sum {ϖ : L} {k : ℕ} {ι : Type} (s : Finset ι) (f : ι → L) (h : ∀ i ∈ s, DvdPow ϖ k (f i)) :
    DvdPow ϖ k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dvdPow_zero ϖ k
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact dvdPow_add (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem dvdPow_mono {ϖ a : L} {k l : ℕ} (hϖ : ϖ ∈ Formalism.UG.intL L) (hlk : l ≤ k) (ha : DvdPow ϖ k a) : DvdPow ϖ l a := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨ϖ ^ (k - l) * b, (Formalism.UG.intL L).mul_mem ((Formalism.UG.intL L).pow_mem hϖ _) hb, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlk]

end GlobalTheory.Hk3.IntWitt

end
end

section

namespace GlobalTheory


open Matrix in
theorem phaseCondition_basisChange : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L)
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
  intro L _ _ σ δ n n' A ψ P Q Q' hσσ hσv hP hQ' hQQ' x hx C' hskew hv hint
  have hmap1 : (1 : Matrix (Fin n) (Fin n) L).map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  have hyQ' : (P * x * Q) * Q' = P * x := by rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
  have e1 : ∀ Z : Matrix (Fin n) (Fin n') L, Q * (Q' * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hQQ', Matrix.one_mul]
  have e2 : ∀ Z : Matrix (Fin n) (Fin n') L, (Q'.map σ)ᵀ * ((Q.map σ)ᵀ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', hmap1, Matrix.transpose_one,
      Matrix.one_mul]
  have intMul : ∀ {a b c : ℕ} (M : Matrix (Fin a) (Fin b) L) (N : Matrix (Fin b) (Fin c) L),
      (∀ i j, M i j ∈ Formalism.UG.intL L) → (∀ i j, N i j ∈ Formalism.UG.intL L) → ∀ i j, (M * N) i j ∈ Formalism.UG.intL L := by
    intro a b c M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)
  have hPσ : ∀ i j, (P.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
    intro i j
    show Valued.v (σ (P j i)) ≤ 1
    rw [hσv]; exact hP j i
  have htr : Matrix.trace ((P.map σ)ᵀ * C' * P * (x * A * (x.map σ)ᵀ)) =
      Matrix.trace (C' * ((P * x * Q) * (Q' * A * (Q'.map σ)ᵀ) * ((P * x * Q).map σ)ᵀ)) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc, e1, e2]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hCx : (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * C' * P * x := by
    calc (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * (C' * ((P * x * Q) * Q')) := by
          simp only [Matrix.mul_assoc]
      _ = (P.map σ)ᵀ * (C' * (P * x)) := by rw [hyQ']
      _ = _ := by simp only [Matrix.mul_assoc]
  have := hx ((P.map σ)ᵀ * C' * P) ?_ ?_ ?_
  · rw [htr] at this; exact this
  · intro i j

    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσσ, hskew,
    Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · intro i j
    have hlt : ∀ (a b : L), Valued.v a ≤ 1 → Valued.v b < 1 → Valued.v (a * b) < 1 := by
      intro a b ha hb
      rw [map_mul]
      calc Valued.v a * Valued.v b ≤ 1 * Valued.v b := mul_le_mul' ha le_rfl
        _ = Valued.v b := one_mul _
        _ < 1 := hb
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [mul_comm]
    refine hlt _ _ (hP k j) ?_
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    exact hlt _ _ (hPσ i l) (hv l k)
  · intro i j
    rw [← hCx]
    exact intMul _ _ (intMul _ _ hPσ hint) hQ' i j

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i j => (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (Formalism.UG.intL L).neg_mem (ha i j)

def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : ℕ) : AddSubgroup (Fin a → L) where
  carrier := {u | ∀ i, u i ∈ Formalism.UG.intL L}
  zero_mem' := fun _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i => (Formalism.UG.intL L).add_mem (ha i) (hb i)
  neg_mem' := fun ha i => (Formalism.UG.intL L).neg_mem (ha i)

theorem mem_intMat {a b : ℕ} (u : Matrix (Fin a) (Fin b) L) : u ∈ intMat L a b ↔ ∀ i j, u i j ∈ Formalism.UG.intL L := Iff.rfl

theorem mem_intVec {a : ℕ} (u : Fin a → L) : u ∈ intVec L a ↔ ∀ i, u i ∈ Formalism.UG.intL L := Iff.rfl

def latIdx {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) : ℕ :=
  Nat.card (Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a))

end GlobalTheory.Hk3.HoweDuality

end
end

section

noncomputable section

namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x : Matrix (Fin n') (Fin n) L) :
    Matrix (Fin n) (Fin n') L :=
  ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L)

def HomA (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) ∧
    ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ (adj σ JS JT x *ᵥ w)) i ∈ Formalism.UG.intL L

def GramEq (σ : L →+* L) {n n' : ℕ} (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  ∀ m m' : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → (∀ i, m' i ∈ Formalism.UG.intL L) → ∀ c ∈ Formalism.UG.intL L,
    (∀ i, (x *ᵥ (c • m)) i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • m')) i ∈ Formalism.UG.intL L) →
      c * (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ m) (y *ᵥ m') -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ m) (x *ᵥ m')) ∈ Formalism.UG.intL L

def SelfDual (σ : L →+* L) {n : ℕ} (JS : GL (Fin n) L) (a : GL (Fin n) L) : Prop :=
  (∀ i j, (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) i j ∈
      Formalism.UG.intL L) ∧
    ∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L

end GlobalTheory.Hk3.HoweG

end
end

section

open Matrix

theorem _root_.GlobalTheory.T.gram_hermitian_skewTrace_sigmaFixed : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, σ (σ x) = x) → σ δ = -δ →
  ∀ (n' r : ℕ) (JT : GL (Fin n') L) (z : Matrix (Fin n') (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ k j, σ (Γ k j) = - Γ j k) →
  (∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) = (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j) ∧
  σ (δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z))) =
    δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z)) := by
  first | exact @GlobalTheory.gram_hermitian_and_trace_fixed | exact GlobalTheory.gram_hermitian_and_trace_fixed | (intros; apply GlobalTheory.gram_hermitian_and_trace_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeDoubleCoset_adicCompletion_inv_mul_integral : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F) (k : ℕ), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (a a' b b' g g' : GL (Fin n) (v.adicCompletion F)), (∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) → (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  first | exact @GlobalTheory.hecke_loc_inv_mul_int | exact GlobalTheory.hecke_loc_inv_mul_int | (intros; apply GlobalTheory.hecke_loc_inv_mul_int <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.skewConjGram_sigmaConjTranspose_trace_identity : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  first | exact @GlobalTheory.skewConj_cT_mul_and_trace | exact GlobalTheory.skewConj_cT_mul_and_trace | (intros; apply GlobalTheory.skewConj_cT_mul_and_trace <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory

namespace GlobalTheory

theorem hermitianForm_norm_sq_le_re_mul_re :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  intro V _ _ Bf hsymm hpos v w
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf y x
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (Bf x y) = Bf y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (Bf x x)
        by_cases hx : x = 0
        · subst hx; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show Bf z (x + y) = Bf z x + Bf z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show Bf y (r • x) = starRingEnd ℂ r * Bf y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c v w
  change ‖Bf w v‖ * ‖Bf v w‖ ≤ RCLike.re (Bf v v) * RCLike.re (Bf w w) at h
  rw [hsymm v w, RCLike.norm_conj] at h
  rw [sq]
  exact h

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)), ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  first | exact @GlobalTheory.exists_embedding_padicAlgCl_place | exact GlobalTheory.exists_embedding_padicAlgCl_place | (intros; apply GlobalTheory.exists_embedding_padicAlgCl_place <;> assumption)
end
