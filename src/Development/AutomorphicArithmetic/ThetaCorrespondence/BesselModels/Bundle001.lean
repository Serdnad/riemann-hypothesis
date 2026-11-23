module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Formalism.PeriodIntegrals.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselRadical

theorem mem_unipRad_of_mem_Nset {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hu : u ∈ Formalism.QuantumDeterminants.Nset k r) : u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  obtain ⟨hU, hcol, hmid⟩ := hu
  have hspan : ∀ y : Fin (2 * r + k + 1) → ℂ, (∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) →
      y = colE k r *ᵥ fun b => y (PI.UpqRep.eI k r b) := by
    intro y hy
    funext i
    simp only [Matrix.mulVec, dotProduct, colE, ite_mul, one_mul, zero_mul]
    by_cases hi : (i : ℕ) < r
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have h : i = PI.UpqRep.eI k r ⟨i, hi⟩ := Fin.ext rfl
        rw [if_pos h, ← h]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (congrArg Fin.val h).symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hy i (not_lt.mp hi)]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro h
      apply hi
      rw [h]
      exact b.isLt
  have key : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) (j : Fin (2 * r + k + 1)), (b : ℕ) + j = 2 * r + k →
      (((colE k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) *ᵥ x) b = x j := by
    intro x b j hbj
    rw [← Matrix.mulVec_mulVec]
    have hc : ∀ w : Fin (2 * r + k + 1) → ℂ, ((colE k r)ᴴ *ᵥ w) b = w (PI.UpqRep.eI k r b) := by
      intro w
      simp [Matrix.mulVec, dotProduct, colE, Matrix.conjTranspose_apply]
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    have hb := b.isLt
    rw [Finset.sum_eq_single j]
    · have h1 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) j = 1 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hbj, hb]
      rw [h1, one_mul]
    · intro m _ hm
      have hne : (b : ℕ) + m ≠ 2 * r + k := fun h => hm (Fin.ext (by omega))
      have h0 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) m = 0 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hne, not_le.mpr hb]
      rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨hU, ?_, ?_⟩
  · intro i
    have hy : ∀ m, ((u - 1) *ᵥ fun m => colE k r m i) m
        = u m (PI.UpqRep.eI k r i) - if m = PI.UpqRep.eI k r i then 1 else 0 := by
      intro m
      simp [Matrix.mulVec, dotProduct, colE, Matrix.sub_apply, Matrix.one_apply, sub_mul]
    refine ⟨fun b => ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r b), ?_, hspan _ ?_⟩
    · intro j hij
      show ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r j) = 0
      rw [hy]
      exact sub_eq_zero.mpr (hcol i _ hij)
    · intro m hm
      rw [hy]
      exact sub_eq_zero.mpr (hcol i m (le_trans (Nat.le_of_lt i.isLt) hm))
  · intro x hx
    have hxz : ∀ j : Fin (2 * r + k + 1), r + k < (j : ℕ) → x j = 0 := by
      intro j hj
      have hjN := j.isLt
      have hb : 2 * r + k - (j : ℕ) < r := by omega
      have h := key x ⟨2 * r + k - j, hb⟩ j (by show 2 * r + k - (j : ℕ) + j = 2 * r + k; omega)
      rw [← h, hx]
      rfl
    refine ⟨fun b => ((u - 1) *ᵥ x) (PI.UpqRep.eI k r b), hspan _ ?_⟩
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : (j : ℕ) ≤ r + k
    · have h0 : (u - 1) i j = 0 := by
        rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
        by_cases hjr : (j : ℕ) < r
        · exact hcol ⟨j, hjr⟩ i (by show (j : ℕ) ≤ i; omega)
        · exact hmid i j (not_lt.mp hjr) hj hi
      rw [h0, zero_mul]
    · rw [hxz j (not_le.mp hj), mul_zero]

end UpperTheory.Lit.Bur.BesselRadical

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup : ∀ {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.Nset k r), u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  first | exact @UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | exact UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | (intros; apply UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset <;> assumption)
end

section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.BlockEmb

open PI.UpqRep PI.HwUniqW

theorem blockW_mul_colW {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) :
    PI.UpqRep.blockW m r s * colW m r = colW m r * s := by
  ext i a
  have h1 : (PI.UpqRep.blockW m r s * colW m r) i a = PI.UpqRep.blockW m r s i (bl m r a) := by
    simp [Matrix.mul_apply, colW]
  rw [h1]
  by_cases hi : InB m r i
  · have hp : i.val - r < m := by unfold InB at hi; omega
    have hb := block_mk hi hp
    rw [← hb, blockW_bl, Matrix.mul_apply]
    simp [colW, blockIndex_injective.eq_iff]
  · rw [blockW_out s hi, if_neg (ne_of_inB (inB_bl a) hi).symm, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    simp [colW, (ne_of_inB (inB_bl b) hi).symm]

theorem blockW_mulVec_of_vanish {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) {y : Fin (2 * r + m + 1) → ℂ}
    (hy : ∀ a, y (bl m r a) = 0) : PI.UpqRep.blockW m r s *ᵥ y = y := by
  have hz : ∀ j, InB m r j → y j = 0 := fun j hj => by
    have hp : j.val - r < m := by unfold InB at hj; omega
    rw [← block_mk hj hp]; exact hy _
  funext i
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : InB m r i
  · rw [hz i hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : InB m r j
    · rw [hz j hj, mul_zero]
    · rw [blockW_in_out s hi hj, zero_mul]
  · simp [blockW_out s hi]

theorem isEmb_conj_blockW {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ}
    {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r)
    (hF : Q * colW m r = F * A) (hA : A * Ai = 1) :
    IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  have hFe : F = Q * colW m r * Ai := by rw [hF, Matrix.mul_assoc, hA, Matrix.mul_one]
  refine ⟨?_, fun x hx => ?_⟩
  · calc Q * PI.UpqRep.blockW m r s * Qi * F
        = Q * PI.UpqRep.blockW m r s * (Qi * Q) * colW m r * Ai := by
          rw [hFe]; simp only [Matrix.mul_assoc]
      _ = Q * (PI.UpqRep.blockW m r s * colW m r) * Ai := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Q * colW m r) * s * Ai := by
          rw [blockW_mul_colW]; simp only [Matrix.mul_assoc]
      _ = F * (A * s * Ai) := by
          rw [hF]; simp only [Matrix.mul_assoc]
  · have hy : ∀ a, (Qi *ᵥ x) (bl m r a) = 0 := fun a => by
      have e : (colW m r)ᴴ * PI.UpqRep.Hpk m r * Qi = Aᴴ * (Fᴴ * J) := by
        have hH : PI.UpqRep.Hpk m r = Qᴴ * J * Q := hg.symm
        rw [hH]
        calc (colW m r)ᴴ * (Qᴴ * J * Q) * Qi = (Q * colW m r)ᴴ * J * (Q * Qi) := by
              rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
          _ = Aᴴ * (Fᴴ * J) := by
              rw [h1, hF, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      rw [← colW_mulVec (Qi *ᵥ x) a, mulVec_mulVec, e, ← mulVec_mulVec, hx, mulVec_zero]; rfl
    rw [← mulVec_mulVec, ← mulVec_mulVec, blockW_mulVec_of_vanish s hy, mulVec_mulVec, h1, one_mulVec]

end UpperTheory.Lit.Bur.BlockEmb

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.blockEmbed_conj_isUnitaryEmbedding : ∀ {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r) (hF : Q * colW m r = F * A) (hA : A * Ai = 1), IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  first | exact @UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | exact UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | (intros; apply UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW <;> assumption)
end
end

section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.CWCombo

theorem isCWCont_of_sobCont {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v)
    {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp)
    (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp}
    (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  classical
  have hnn : ∀ (L : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))) (v : H),
      0 ≤ (L.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := fun L v =>
    List.sum_nonneg (by
      intro x hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _)
  have key : ∀ s : Finset ι, ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, ∀ X ∈ w, PI.UpqRep.InLieHpk k r X) ∧
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ‖∑ i ∈ s, l i v • b i‖ ≤
        C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, [], by simp, by simp⟩
    | insert i s hi ih =>
      obtain ⟨C, Ws, hW, hb⟩ := ih
      obtain ⟨S, D, hS, hD⟩ := hl i
      refine ⟨|D| * ‖b i‖ + |C|, S ++ Ws, ?_, ?_⟩
      · intro w hw X hX
        rcases List.mem_append.1 hw with h | h
        · exact hS w h X hX
        · exact hW w h X hX
      · intro v hv
        have e : ‖l i v‖ ≤ D * (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum := by
          have := hD v (hs v hv)
          simpa only [dsigW_eq] using this
        have h1 := hnn S v
        have h2 := hnn Ws v
        have h3 := hb v hv
        rw [Finset.sum_insert hi, List.map_append, List.sum_append]
        set P := (S.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        set Q := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v‖).sum
        have hbn : 0 ≤ ‖b i‖ := norm_nonneg _
        have e1 : ‖l i v • b i‖ ≤ |D| * ‖b i‖ * P := by
          rw [norm_smul]
          calc ‖l i v‖ * ‖b i‖ ≤ (|D| * P) * ‖b i‖ :=
                mul_le_mul_of_nonneg_right (e.trans (mul_le_mul_of_nonneg_right (le_abs_self D) h1)) hbn
            _ = |D| * ‖b i‖ * P := by ring
        have e2 : ‖∑ j ∈ s, l j v • b j‖ ≤ |C| * Q :=
          h3.trans (mul_le_mul_of_nonneg_right (le_abs_self C) h2)
        have a1 : 0 ≤ |D| * ‖b i‖ * Q := mul_nonneg (mul_nonneg (abs_nonneg _) hbn) h2
        have a2 : 0 ≤ |C| * P := mul_nonneg (abs_nonneg _) h1
        calc ‖l i v • b i + ∑ j ∈ s, l j v • b j‖ ≤ ‖l i v • b i‖ + ‖∑ j ∈ s, l j v • b j‖ := norm_add_le _ _
          _ ≤ |D| * ‖b i‖ * P + |C| * Q := add_le_add e1 e2
          _ ≤ (|D| * ‖b i‖ + |C|) * (P + Q) := by nlinarith
  obtain ⟨C, Ws, hW, hb⟩ := key Finset.univ
  exact ⟨C, Ws, hW, fun v hv => by rw [hB v hv]; exact hb v hv⟩

end UpperTheory.Lit.Bur.CWCombo

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.casselmanWallachCont_finite_sum_sobolev_forms : ∀ {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hs : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → SmoothVec (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ v) {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {ι : Type} [Fintype ι] (l : ι → H →ₗ[ℂ] ℂ) (b : ι → Wp) (hl : ∀ i, Sobolev₂ (lieG (Formalism.QuantumDeterminants.Hpk k r)) σ (l i)) {B : H → Wp} (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = ∑ i, l i v • b i), PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  first | exact @UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | exact UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont | (intros; apply UpperTheory.Lit.Bur.CWCombo.isCWCont_of_sobCont <;> assumption)
end

section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselContra

theorem isContIrred_contra_conj : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  intro m W _ _ _ J₀ A Ai h1 h2 hA π₀ hπ
  have hJ : Aiᴴ * Ai = J₀ := by
    calc Aiᴴ * Ai = Aiᴴ * (Aᴴ * J₀ * A) * Ai := by rw [hA, Matrix.mul_one]
      _ = (A * Ai)ᴴ * J₀ * (A * Ai) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by simp [h1]
  have hmem : ∀ h, h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) →
      A * hᴴ * Ai ∈ Formalism.QuantumDeterminants.UH J₀ := by
    intro h hh
    have hh' : h * hᴴ = 1 := mul_eq_one_comm.1 (mem_UH_one.1 hh)
    show (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = J₀
    calc (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = Aiᴴ * h * (Aᴴ * J₀ * A) * hᴴ * Ai := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Aiᴴ * (h * hᴴ) * Ai := by
          rw [hA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = J₀ := by rw [hh', Matrix.mul_one, hJ]
  have hadj : ∀ g, g ∈ Formalism.QuantumDeterminants.UH J₀ →
      (Ai * g * A)ᴴ ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro g hg
    have hg' : gᴴ * J₀ * g = J₀ := hg
    refine mem_UH_one.2 (mul_eq_one_comm.1 ?_)
    rw [conjTranspose_conjTranspose]
    calc (Ai * g * A)ᴴ * (Ai * g * A) = Aᴴ * (gᴴ * (Aiᴴ * Ai) * g) * A := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hg', hA]
  have hback : ∀ g : Matrix (Fin m) (Fin m) ℂ, A * ((Ai * g * A)ᴴ)ᴴ * Ai = g := by
    intro g
    rw [conjTranspose_conjTranspose]
    calc A * (Ai * g * A) * Ai = (A * Ai) * g * (A * Ai) := by
          simp only [Matrix.mul_assoc]
      _ = g := by simp [h1]
  obtain ⟨⟨hone, hmul⟩, hc, hi⟩ := hπ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun w l => ?_, fun U hU => ?_⟩
  · have : A * (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * Ai = 1 := by simp [h1]
    beta_reduce
    rw [this, hone]
    ext l x
    simp
  · have e : A * (a * b)ᴴ * Ai = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by
      calc A * (a * b)ᴴ * Ai = A * bᴴ * (Ai * A) * aᴴ * Ai := by
            rw [h2, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by simp only [Matrix.mul_assoc]
    beta_reduce
    rw [e, hmul _ (hmem b hb) _ (hmem a ha)]
    ext l x
    simp
  · obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective l
    have hφ : Continuous fun h : Matrix (Fin m) (Fin m) ℂ => A * hᴴ * Ai :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    exact (hc x w).comp hφ.continuousOn hmem
  · have hs : ∀ g ∈ Formalism.QuantumDeterminants.UH J₀, ∀ v ∈ U.dualCoannihilator,
        π₀ g v ∈ U.dualCoannihilator := fun g hg v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro l hl
      have := hv _ (hU _ (hadj g hg) l hl)
      beta_reduce at this
      rw [hback] at this
      simpa using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)]
    rcases hi _ hs with h | h
    · rw [h]; exact Or.inr Submodule.dualAnnihilator_bot
    · rw [h]; exact Or.inl Submodule.dualAnnihilator_top

end UpperTheory.Lit.Bur.BesselContra

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  first | exact @UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | exact UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | (intros; apply UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj <;> assumption)
end
