module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Mathlib.RingTheory.PowerSeries.Log
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
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
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.MapNMul

theorem cc_subst {R : Type} [CommRing R] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (k : ℕ) :
    nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem cc_nmul {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) : ∀ (k : ℕ) (i : Fin d), constantCoeff (nmul μ k i) = 0 := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    simp only [op, at2]
    rw [cc_subst (fun s => by cases s <;> simp [ih]), hμ]

theorem map_nmul (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    ∀ (k : ℕ) (i : Fin d), map φ (nmul μ k i) = nmul (fun j => map φ (μ j)) k i := by
  intro k
  induction k with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ, nmul_succ]
    simp only [op, at2]
    have hs : HasSubst (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [cc_nmul μ hμ]
    rw [map_subst hs]
    congr 1
    funext s
    cases s <;> simp [ih]

end GlobalTheory.MapNMul
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobStep

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_comp (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = ((substAlgHom (R := Q) (S := Q) (HasSubst.X_pow (σ := σ) (S := Q) hp)).toRingHom.comp
      (MvPowerSeries.map s)) f := by
  simp [frob]

theorem frob_smul (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) (b : B) (f : MvPowerSeries σ Q) :
    frob p s (algebraMap B Q b • f) = algebraMap B Q (τ b) • frob p s f := by
  unfold frob
  rw [smul_eq_C_mul, map_mul, map_C, hs, ← smul_eq_C_mul,
    subst_smul (HasSubst.X_pow (σ := σ) (S := Q) hp)]

theorem frob_comb (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) {ι : Type} [Fintype ι]
    (w : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb w e) = ∑ i, algebraMap B Q (τ (w i)) • frob p s (e i) := by

  rw [comb, frob_eq_comp p hp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← frob_eq_comp p hp, frob_smul p hp τ s hs]

theorem in_top_sum_smul {σ : Type} {ι : Type} [Fintype ι] (c : ι → B)
    (g : ι → MvPowerSeries σ Q) (h : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  intro α
  choose b _ hb using fun i => h i α
  refine ⟨∑ i, c i * b i, Submodule.mem_top, ?_⟩

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, hb, map_mul]

theorem comb_mulVec {σ : Type} {ι : Type} [Fintype ι] (M : Matrix ι ι B) (v : ι → B)
    (e : ι → MvPowerSeries σ Q) :
    comb (M.mulVec v) e = ∑ i, algebraMap B Q (v i) • comb (fun l => M l i) e := by

  simp only [comb, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul, Finset.smul_sum, smul_smul,
  ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem frob_comb_step : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q]
    (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) →
    ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B),
    (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) →
    ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  intro p hp B Q _ _ _ σ s hs d ι _ e M hM w
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have key : frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e =
      ∑ i, algebraMap B Q (σ (w i)) • (frob p s (e i) - comb (fun l => M l i) e) := by
    rw [frob_comb p hp0 σ s hs, comb_mulVec]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [key]
  exact in_top_sum_smul _ _ hM

end GlobalTheory.FrobStep
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.BasisTrans

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_add {g h : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) (hh : In (⊤ : Ideal B) h) :
    In (⊤ : Ideal B) (g + h) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  obtain ⟨b, -, hb⟩ := hh α
  exact ⟨a + b, trivial, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩

theorem in_smul (c : B) {g : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) :
    In (⊤ : Ideal B) (algebraMap B Q c • g) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  exact ⟨c * a, trivial, by rw [coeff_smul, ha, map_mul]⟩

theorem in_sum {κ : Type} (s : Finset κ) (g : κ → MvPowerSeries σ Q)
    (hg : ∀ j ∈ s, In (⊤ : Ideal B) (g j)) : In (⊤ : Ideal B) (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hg a (Finset.mem_insert_self _ _)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem comb_one {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvPowerSeries σ Q) (i : ι) :
    comb ((1 : Matrix ι ι B) i) e = e i := by
  simp [comb, Matrix.one_apply]

theorem comb_mul {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι → MvPowerSeries σ Q)
    (f : κ → MvPowerSeries σ Q) (P : ι → κ → B) (P' : κ → ι → B) (i : ι) :
    e i - comb ((Matrix.of P * Matrix.of P') i) e =
      (e i - comb (P i) f) + ∑ j, algebraMap B Q (P i j) • (f j - comb (P' j) e) := by

  simp only [comb, Matrix.mul_apply, Matrix.of_apply, smul_sub, Finset.sum_sub_distrib,
  Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun j k => algebraMap B Q (P i j * P' j k) • e k)]
  abel

theorem mul_eq_one {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q)
    (he : IsBasis μ e) (P : ι → κ → B) (P' : κ → ι → B)
    (h1 : ∀ i, In (⊤ : Ideal B) (e i - comb (P i) f))
    (h2 : ∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) :
    Matrix.of P * Matrix.of P' = 1 := by
  funext i
  obtain ⟨b, -, hb⟩ := he.2 (e i) (he.1 i)
  have hA : In (⊤ : Ideal B) (e i - comb ((Matrix.of P * Matrix.of P') i) e) := by
    rw [comb_mul e f P P' i]
    exact in_add (h1 i) (in_sum _ _ fun j _ => in_smul _ (h2 j))
  have hB : In (⊤ : Ideal B) (e i - comb ((1 : Matrix ι ι B) i) e) := by
    rw [comb_one, sub_self]; exact in_zero
  exact (hb _ hA).trans (hb _ hB).symm

theorem trans_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  intro B Q _ _ _ d μ ι κ _ _ _ _ e f he hf P P' h1 h2
  exact ⟨mul_eq_one μ e f he P P' h1 h2, mul_eq_one μ f e hf P' P h2 h1⟩

end GlobalTheory.BasisTrans
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CobSwap

theorem hasSubst_swapVars {R : Type} [CommRing R] {d : ℕ} :
    HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
  hasSubst_of_constantCoeff_zero fun j => by cases j <;> simp

theorem swap_map {B Q : Type} [CommRing B] [CommRing Q] (h : B →+* Q) {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) B) : swap (map h c) = map h (swap c) := by
  unfold swap at2
  rw [map_subst hasSubst_swapVars]
  congr 1
  funext j
  cases j <;> simp

theorem swap_subst {R : Type} [CommRing R] {d : ℕ} (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hν : ∀ i, constantCoeff (ν i) = 0) (f : MvPowerSeries (Fin d) R) :
    swap (subst ν f) = subst (fun i => swap (ν i)) f := by
  unfold swap at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hν) hasSubst_swapVars]

theorem swap_inL {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inL f) = inR f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inR f) = inL f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_sub {R : Type} [CommRing R] {d : ℕ} (a b : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap (a - b) = swap a - swap b := by
  unfold swap at2
  exact subst_sub hasSubst_swapVars a b

theorem swap_cob1_eq_of_swap_eq : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) →
    (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q,
    swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  intro B Q _ _ _ d μ h0 hs g
  have h0' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, h0 i]
  have hs' : ∀ i, swap (up Q μ i) = up Q μ i := fun i => by
    simp only [up]; rw [swap_map, hs i]
  unfold cob1
  rw [swap_sub, swap_sub, swap_subst _ h0', swap_inL, swap_inR]
  simp only [hs']
  abel

end GlobalTheory.CobSwap
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.QLog.Chart.exists_dual_lift_lin : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  intro p O _ G d c m hp
  obtain ⟨n, hn⟩ := c.ker 1 2
  refine ⟨n, fun u => ?_⟩
  let L : MvPowerSeries (Fin d) O →ₗ[O] O := ∑ i, u i • coeff (Finsupp.single i 1)
  have hL : ∀ F, L F = ∑ i, u i * lin F i := fun F => by simp [L, LinearMap.sum_apply, lin]
  let f : MvPowerSeries (Fin d) O →ₗ[O] O ⧸ m := m.mkQ ∘ₗ L
  have hk : LinearMap.ker (c.ev n).toLinearMap ≤ LinearMap.ker f := by
    intro F hF
    have h := hn F hF
    change Ideal.Quotient.mk m (L F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hL]
    refine Submodule.sum_mem _ fun i _ => m.mul_mem_left _ ?_
    obtain ⟨a, ha⟩ := h (Finsupp.single i 1) (by simp)
    have : lin F i = p ^ 1 * a := ha
    rw [this, pow_one]
    exact m.mul_mem_right _ hp
  let g : G.A n →ₗ[O] O ⧸ m := (LinearMap.ker (c.ev n).toLinearMap).liftQ f hk ∘ₗ
    ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm.toLinearMap
  have hg : ∀ F, g (c.ev n F) = f F := fun F => by
    have : ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm (c.ev n F) =
        Submodule.Quotient.mk F := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property m.mkQ g m.mkQ_surjective
  refine ⟨WithConv.toConv φ, fun F => ?_⟩
  rw [← hL, ← Submodule.Quotient.eq]
  exact (LinearMap.congr_fun hφ (c.ev n F)).trans (hg F)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.DualFrobNilMat

theorem mulVec_transpose_inv_blk_apply {B : Type} [CommRing B] (σ : B →+* B) (p : ℕ) {d k : ℕ}
    (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (w : Fin d ⊕ Fin k → B) (r : Fin d ⊕ Fin k) :
    ((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r =
      (∑ j : Fin d, U⁻¹ (Sum.inl j) r * σ (w (Sum.inl j))) +
      (p : B) * ∑ j : Fin k, U⁻¹ (Sum.inr j) r * σ (w (Sum.inr j)) := by
  have hU : ∀ r s, U.transpose⁻¹ r s = U⁻¹ s r := fun r s => by
    rw [← Matrix.transpose_nonsing_inv]; rfl
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.mul_diagonal, hU, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_one, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem isNil_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  intro B O _ _ θ σ p m hp hm hσ d k U c hc hS
  obtain ⟨N, hN⟩ := hS
  set ρ : B →+* O ⧸ m := (Ideal.Quotient.mk m).comp θ with hρ
  have hρp : ρ (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hp
  have hρσ : ∀ b, ρ (σ b) = ρ b ^ p := by
    intro b
    obtain ⟨e, he⟩ := hσ b
    have h := congrArg ρ he
    rw [map_sub, map_mul, map_pow, hρp, zero_mul, sub_eq_zero] at h
    exact h
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply hm
    obtain ⟨e, he⟩ := hσ 0
    simp only [map_zero, pow_zero, zero_sub, Nat.cast_zero, zero_mul, neg_eq_zero] at he
    have h1 : (1 : O) = 0 := by rw [← map_one θ, he, map_zero]
    rw [Ideal.eq_top_iff_one, h1]
    exact m.zero_mem
  have hT : ∀ (w : Fin d ⊕ Fin k → B) r,
      ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r) =
        ∑ j, ρ (U⁻¹ (Sum.inl j) r) * ρ (w (Sum.inl j)) ^ p := by
    intro w r

    rw [mulVec_transpose_inv_blk_apply, map_add (f := _), map_mul, hρp, zero_mul, add_zero, map_sum]
    simp only [map_mul, hρσ]
  have hinl : ∀ a j, ρ (U⁻¹ (Sum.inl j) (Sum.inl a)) = ρ (c a j) := by
    intro a j
    obtain ⟨e, he⟩ := hc a j
    have h := congrArg ρ he
    rw [map_sub, map_mul, hρp, zero_mul, sub_eq_zero] at h
    exact h.symm
  have hiter : ∀ (t : ℕ) (v : Fin d ⊕ Fin k → B),
      (fun a => ρ (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[t] v) (Sum.inl a))) =
      (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[t]
        (fun a => ρ (v (Sum.inl a))) := by
    intro t
    induction t with
    | zero => intro v; rfl
    | succ t ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      funext a
      rw [hT]
      exact Finset.sum_congr rfl fun j _ => by rw [hinl]; rfl
  refine ⟨N + 1, fun v r hu => hm ?_⟩
  rw [Function.iterate_succ_apply'] at hu
  have h0 : ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ
      (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[N] v) j)) r) = 0 := by
    rw [hT]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h := congrFun (hiter N v) j
    rw [hN] at h
    simp only [Pi.zero_apply] at h
    rw [h, zero_pow hp0, mul_zero]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h0) hu

end GlobalTheory.DualFrobNilMat
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.InvSolve

theorem in_iff_mem {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) :
    In N f ↔ ∀ α, coeff α f ∈ N.toAddSubmonoid.map (algebraMap B Q).toAddMonoidHom := by
  simp only [In, AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  constructor
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩

theorem in_mul_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) (h : MvPowerSeries σ B) (hf : In N f) :
    In N (f * map (algebraMap B Q) h) := by
  classical
  rw [in_iff_mem] at hf ⊢
  intro α
  rw [coeff_mul]
  refine AddSubmonoid.sum_mem _ fun x _ => ?_
  obtain ⟨b, hb, e⟩ := AddSubmonoid.mem_map.1 (hf x.1)
  refine AddSubmonoid.mem_map.2 ⟨b * coeff x.2 h, N.mul_mem_right _ hb, ?_⟩
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at e ⊢
  rw [map_mul, e, coeff_map]

theorem in_sum {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (s : Finset ι) (f : ι → MvPowerSeries σ Q) (hf : ∀ i ∈ s, In N (f i)) :
    In N (∑ i ∈ s, f i) := by
  rw [in_iff_mem] at *
  intro α

  rw [map_sum]
  exact AddSubmonoid.sum_mem _ fun i hi => (in_iff_mem N (f i)).1 (hf i hi) α

theorem solve : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (N : Ideal B) (M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B)), (∀ i j, constantCoeff (M i j) = if i = j then 1 else 0) → ∀ (v g : Fin d → MvPowerSeries (Fin d) Q), (∀ i, ∑ j, v j * map (algebraMap B Q) (M j i) = g i) → (∀ i, In N (g i)) → ∀ j, In N (v j) := by
  intro B Q _ _ _ d N M hM v g hv hg j
  classical
  have hc : (constantCoeff : MvPowerSeries (Fin d) B →+* B).mapMatrix M = 1 := by
    ext i k; simp [hM, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hc, Matrix.det_one]
    exact isUnit_one
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  let φ : MvPowerSeries (Fin d) B →+* MvPowerSeries (Fin d) Q := map (algebraMap B Q)
  have h2 : φ.mapMatrix M * φ.mapMatrix M⁻¹ = 1 := by rw [← map_mul, h1, map_one]
  have hvg : Matrix.vecMul v (φ.mapMatrix M) = g := funext fun i => by
    simpa [Matrix.vecMul, dotProduct, φ] using hv i
  have hv' : v = Matrix.vecMul g (φ.mapMatrix M⁻¹) := by
    rw [← hvg, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
  rw [hv']
  simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, φ]
  exact in_sum N _ _ fun i _ => in_mul_map N _ _ (hg i)

end GlobalTheory.InvSolve
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_powerSeries_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q], DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  first | exact @GlobalTheory.QLog.LogDiff.dIn_log | exact GlobalTheory.QLog.LogDiff.dIn_log | (intros; apply GlobalTheory.QLog.LogDiff.dIn_log <;> assumption)
end
