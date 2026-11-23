module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectComp

variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ}

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_zero (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) :
    _root_.GlobalTheory.QLog.nmul μ 0 = fun _ => 0 := rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_succ_eq_op_X (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (k : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (k + 1) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ k) (fun i => X i) := by
  rw [_root_.GlobalTheory.QLog.nmul, _root_.GlobalTheory.QLog.nmul, Function.iterate_succ_apply']

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma hasSubst_sumElim_of_constantCoeff_eq_zero {τ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) :
    HasSubst (Sum.elim v w) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hv, hw]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_katz_op_eq_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.op μ v w i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw)
    (fun s => by cases s <;> simp [hv, hw]) (hμ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_nmul_eq_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul_zero]
  | succ k ih =>
    rw [nmul_succ_eq_op_X]
    exact constantCoeff_katz_op_eq_zero μ hμ ih (fun j => constantCoeff_X j) i

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma mvPowerSeries_map_injective {σ A B : Type} [CommRing A] [CommRing B] {h : A →+* B}
    (hh : Function.Injective h) : Function.Injective (map (σ := σ) h) := fun p q hpq => by
  ext n
  apply hh
  simpa using congrArg (coeff n) hpq

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_zero_divisor {σ τ : Type} {c : σ → MvPowerSeries τ S} (hc : HasSubst c) :
    subst c (0 : MvPowerSeries σ S) = 0 := by
  rw [← coe_substAlgHom hc, map_zero]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_subst_sumElim_eq_subst_sumElim_subst {τ υ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (g : MvPowerSeries (Fin d ⊕ Fin d) S) :
    subst c (subst (Sum.elim v w) g) =
      subst (Sum.elim (fun j => subst c (v j)) (fun j => subst c (w j))) g := by
  rw [subst_comp_subst_apply (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw) hc]
  congr 1
  funext s
  cases s <;> rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_katz_op_eq_op_subst {τ υ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (i : Fin d) :
    subst c (_root_.GlobalTheory.Katz.op μ v w i) =
      _root_.GlobalTheory.Katz.op μ (fun j => subst c (v j)) (fun j => subst c (w j)) i :=
  subst_subst_sumElim_eq_subst_sumElim_subst hv hw hc (μ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_add_eq_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (a b : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (a + b) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ a) (_root_.GlobalTheory.QLog.nmul μ b) := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have ha : HasSubst (_root_.GlobalTheory.QLog.nmul μ a) := hasSubst_of_constantCoeff_zero (hN a)
  induction b with
  | zero =>
    funext i
    have h := congrArg (subst (_root_.GlobalTheory.QLog.nmul μ a))
      (congrFun hG.unit i)
    rw [subst_katz_op_eq_op_subst μ (fun j => constantCoeff_X j) (fun _ => by simp) ha] at h
    simp only [subst_X ha, subst_zero_divisor ha] at h
    rw [Nat.add_zero, nmul_zero]
    exact h.symm
  | succ b ih =>
    rw [← Nat.add_assoc, nmul_succ_eq_op_X, ih, nmul_succ_eq_op_X]
    funext i
    have hc : HasSubst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with s | s | s <;> simp [hN]
    have h := congrArg (subst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))))
      (congrFun hG.assoc i)
    have h1 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x1]
    have h2 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x2]
    have h3 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x3]
    rw [subst_katz_op_eq_op_subst μ (constantCoeff_katz_op_eq_zero μ hμ h1 h2) h3 hc,
      subst_katz_op_eq_op_subst μ h1 (constantCoeff_katz_op_eq_zero μ hμ h2 h3) hc] at h
    simp_rw [subst_katz_op_eq_op_subst μ h1 h2 hc, subst_katz_op_eq_op_subst μ h2 h3 hc] at h
    simp only [_root_.GlobalTheory.Katz.x1, _root_.GlobalTheory.Katz.x2, _root_.GlobalTheory.Katz.x3,
      subst_X hc, Sum.elim_inl, Sum.elim_inr] at h
    exact h

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_nmul_nmul_eq_nmul_mul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (k m : ℕ) (i : Fin d) :
    subst (_root_.GlobalTheory.QLog.nmul μ m) (_root_.GlobalTheory.QLog.nmul μ k i) =
      _root_.GlobalTheory.QLog.nmul μ (k * m) i := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) := hasSubst_of_constantCoeff_zero (hN m)
  induction k generalizing i with
  | zero =>
    simp only [Nat.zero_mul, nmul_zero]
    exact subst_zero_divisor hm
  | succ k ih =>
    rw [nmul_succ_eq_op_X, subst_katz_op_eq_op_subst μ (hN k) (fun j => constantCoeff_X j) hm]
    simp_rw [ih, subst_X hm]
    rw [Nat.succ_mul, nmul_add_eq_op hG]


set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
theorem _root_.GlobalTheory.DefectComp.main : ∀ (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), _root_.GlobalTheory.Katz.IsLaw μ → Function.Injective (algebraMap R Q) → ∀ (f : MvPowerSeries (Fin d) Q), constantCoeff f = 0 → ∀ (k m : ℕ) (s t u : MvPowerSeries (Fin d) R), map (algebraMap R Q) s = _root_.GlobalTheory.QLog.defect μ k f → map (algebraMap R Q) t = _root_.GlobalTheory.QLog.defect μ m f → map (algebraMap R Q) u = _root_.GlobalTheory.QLog.defect μ (k * m) f → u = subst (_root_.GlobalTheory.QLog.nmul μ m) s + (k : R) • t := by
  intro R Q _ _ _ d μ hG hinj f _ k m s t u hs ht hu
  have hμ := hG.const
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_nmul_eq_zero' μ hμ m)
  have hmQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ m
  have hkQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ k
  apply mvPowerSeries_map_injective hinj
  rw [map_add (f := _), map_subst hm, hs, hu, Nat.cast_smul_eq_nsmul, map_nsmul, ht]
  change _ = subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
    (_root_.GlobalTheory.QLog.defect μ k f) + _
  simp only [_root_.GlobalTheory.QLog.defect]
  rw [subst_sub hmQ, subst_smul hmQ, subst_comp_subst_apply hkQ hmQ]
  have hcomp : (fun i => subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
      (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k) i)) =
      _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ (k * m)) := by
    funext i
    change subst (fun j => map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ m j))
      (map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ k i)) =
        map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ (k * m) i)
    rw [← map_subst hm, subst_nmul_nmul_eq_nmul_mul hG]
  rw [hcomp, ← Nat.cast_smul_eq_nsmul Q, Nat.cast_mul, mul_smul, smul_sub]
  abel

end GlobalTheory.DefectComp
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Limits

theorem smod_pow_iff {R : Type} [CommRing R] (a x y : R) (m : ℕ) :
    x ≡ y [SMOD (Ideal.span {a} ^ m • ⊤ : Submodule R R)] ↔ a ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eval_eq_of_le {O σ : Type} [CommRing O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hr : ∀ n f, r n (E (n + 1) f) = E n f) {n k : ℕ} (hnk : n ≤ k) (x y : MvPowerSeries σ O)
    (h : E k x = E k y) : E n x = E n y := by
  induction k, hnk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact ih (by rw [← hr k x, ← hr k y, h])

theorem exists_unique_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] [Fintype σ] (A : ℕ → Type) [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)] [∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (y : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n), (∀ n, IsEval p (y n) (E n)) → (∀ n f, r n (E (n + 1) f) = E n f) → (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, (∀ n, E n f = 0) → f = 0) ∧ ((∀ n, Function.Surjective (E n)) → ∀ a : ∀ n, A n, (∀ n, r n (a (n + 1)) = a n) → ∃ f, ∀ n, E n f = a n) := by
  intro p O σ _ _ _ A _ _ _ r y E hev hr hker
  have hausO : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
  have precO : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
  have hle : ∀ {n k : ℕ}, n ≤ k → ∀ x y, E k x = E k y → E n x = E n y :=
    fun hnk => eval_eq_of_le A r E hr hnk
  refine ⟨fun f hf => ?_, fun hsurj a ha => ?_⟩
  · ext α
    refine hausO.haus _ fun m => (smod_pow_iff _ _ _ _).2 ?_
    obtain ⟨n, hn⟩ := hker m (α.degree + 1)
    simpa using hn f (hf n) α (Nat.lt_succ_self _)
  · choose nk hnk using fun m => hker m m
    choose g hg using fun n => hsurj n (a n)
    set ν : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nk j with hν
    have hνmono : Monotone ν := fun m m' hmm' => by
      simp only [hν]
      exact Nat.add_le_add hmm' (Finset.sum_le_sum_of_subset
        (Finset.range_mono (Nat.succ_le_succ hmm')))
    have hνk : ∀ m, nk m ≤ ν m := fun m => by
      simp only [hν]
      exact le_add_left (Finset.single_le_sum (f := nk) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_self m)))
    have hνm : ∀ m, m ≤ ν m := fun m => by simp only [hν]; exact Nat.le_add_right _ _

    have hga : ∀ n k, n ≤ k → E n (g k) = a n := by
      intro n k hnk
      induction k, hnk using Nat.le_induction with
      | base => exact hg n
      | succ k hk ih =>
        rw [← ih]
        refine hle hk _ _ ?_
        rw [← hr k, hg (k + 1), ha k, hg k]

    have hKν : ∀ m k, ν m ≤ k → ∀ x, E k x = 0 → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α x := by
      intro m k hk x hx α hα
      refine hnk m x ?_ α hα
      have := hle ((hνk m).trans hk) x 0 (by rw [hx, map_zero])
      rwa [map_zero] at this
    set h : ℕ → MvPowerSeries σ O := fun m => g (ν m) with hh
    have hD : ∀ m m', m ≤ m' → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α (h m') - coeff α (h m) := by
      intro m m' hmm' α hα
      rw [← map_sub]
      refine hKν m (ν m) le_rfl _ ?_ α hα
      rw [map_sub, hh, hga _ _ (hνmono hmm'), hga _ _ le_rfl, sub_self]
    have hL : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ j, (p : O) ^ j ∣ coeff α (h (j + (α.degree + 1))) - L := by
      intro α
      obtain ⟨L, hL⟩ := precO.prec (f := fun j => coeff α (h (j + (α.degree + 1)))) (by
        intro j j' hjj'
        rw [smod_pow_iff]
        have := hD (j + (α.degree + 1)) (j' + (α.degree + 1)) (by omega) α (by omega)
        rw [← neg_sub, dvd_neg]
        exact (pow_dvd_pow _ (by omega)).trans this)
      exact ⟨L, fun j => (smod_pow_iff _ _ _ _).1 (hL j)⟩
    choose L hLs using hL
    let f : MvPowerSeries σ O := fun α => L α
    have hf : ∀ m M (α : σ →₀ ℕ), m ≤ M → α.degree < M →
        (p : O) ^ m ∣ coeff α f - coeff α (h M) := by
      intro m M α hmM hα
      have h1 := hLs α M
      have h2 := hD M (M + (α.degree + 1)) (by omega) α hα
      have : coeff α f - coeff α (h M) =
          (coeff α (h (M + (α.degree + 1))) - coeff α (h M)) -
            (coeff α (h (M + (α.degree + 1))) - L α) := by
        show L α - _ = _; ring
      rw [this]
      exact (pow_dvd_pow _ hmM).trans (dvd_sub h2 h1)
    refine ⟨f, fun n => ?_⟩
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(p : A n)}) inferInstance _ fun m => ?_
    rw [smod_pow_iff, sub_zero]
    obtain ⟨N₀, hN₀⟩ := (hev n).2 m
    set M := max (max m N₀) n with hM
    have hEM : E n (h M) = a n := hga _ _ ((le_max_right _ _).trans (hνm M))
    have hdiv : ∀ α : σ →₀ ℕ, α.degree < N₀ → (p : O) ^ m ∣ coeff α (f - h M) := by
      intro α hα
      rw [map_sub]
      exact hf m M α (by omega) (by omega)
    let Q : MvPowerSeries σ O := fun α =>
      if hα : α.degree < N₀ then Classical.choose (hdiv α hα) else 0
    have hR : ∀ α : σ →₀ ℕ, α.degree < N₀ →
        coeff α (f - h M - (p : O) ^ m • Q) = 0 := by
      intro α hα
      rw [map_sub, coeff_smul]
      show coeff α (f - h M) - (p : O) ^ m * (if hα : α.degree < N₀ then _ else 0) = 0
      rw [dite_eq_left hα, ← Classical.choose_spec (hdiv α hα), sub_self]
    have hsplit : E n f - a n = (p : A n) ^ m * E n Q + E n (f - h M - (p : O) ^ m • Q) := by
      rw [map_sub, map_sub, map_smul, hEM, Algebra.smul_def, map_pow, map_natCast]
      ring
    rw [hsplit]
    exact dvd_add (dvd_mul_right _ _) (hN₀ _ hR)

end GlobalTheory.Limits
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.AugNil

theorem aeval_mem_span {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {d : ℕ}
    (x : Fin d → A) (P : MvPolynomial (Fin d) R) (h0 : MvPolynomial.constantCoeff P = 0) :
    MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) (by rwa [MvPolynomial.constantCoeff_eq] at h0)
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (Finsupp.ext h)
  refine Ideal.mul_mem_left _ _ ?_
  have hdvd : x i ∣ ∏ j ∈ m.support, x j ^ m j :=
    (dvd_pow_self (x i) hi).trans (Finset.dvd_prod_of_mem _ (Finsupp.mem_support_iff.2 hi))
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem dvd_pow_of_mem_span {A : Type} [CommRing A] {d : ℕ} (x : Fin d → A) (p : A) (N₀ : ℕ)
    (hx : ∀ i, p ∣ x i ^ N₀) (a : A) (ha : a ∈ Ideal.span (Set.range x)) :
    p ∣ a ^ (d * N₀ + 1) := by
  obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  have h := Ideal.sum_pow_mem_span_pow Finset.univ (fun i => r i • x i) N₀
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← Ideal.mem_span_singleton]
  refine Ideal.span_le.2 ?_ h
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton]
  simp only [smul_eq_mul, mul_pow]
  exact Dvd.dvd.mul_left ((hx i).trans (pow_dvd_pow _ (Nat.le_succ _))) _

theorem aug_nil : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 →
      (p : G.A 1) ∣ c.ev 1 f ^ N := by
  intro p O _ G d c
  classical
  choose Ni hNi using c.nil 1
  let N₀ := Finset.univ.sup Ni
  have hx : ∀ i, (p : G.A 1) ∣ c.x 1 i ^ N₀ := fun i =>
    (hNi i).trans (pow_dvd_pow _ (Finset.le_sup (Finset.mem_univ i)))
  obtain ⟨N₁, hN₁⟩ := (c.isEval 1).2 1
  refine ⟨d * N₀ + 1, fun f hf => ?_⟩
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N₁) f with hPdef
  have hR : (p : G.A 1) ∣ c.ev 1 (f - (P : MvPowerSeries (Fin d) O)) := by
    have h := hN₁ (f - P) (fun α hα => ?_)
    · simpa using h
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro i
    have : α i ≤ α.degree := by
      rw [Finsupp.degree]
      by_cases hi : α i = 0
      · rw [hi]; exact Nat.zero_le _
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hi)
    simpa using this.trans hα.le
  have hP : c.ev 1 (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x 1) P := by
    have : (c.ev 1).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (c.x 1) :=
      MvPolynomial.algHom_ext fun i => by simp [(c.isEval 1).1 i]
    exact congrArg (fun φ => φ P) this
  have hP0 : MvPolynomial.constantCoeff P = 0 := by
    rw [MvPolynomial.constantCoeff_eq, hPdef, coeff_trunc', if_pos (zero_le')]
    simpa using hf
  have ha := dvd_pow_of_mem_span (c.x 1) (p : G.A 1) N₀ hx _ (aeval_mem_span (c.x 1) P hP0)
  rw [← hP] at ha
  have hsub := sub_dvd_pow_sub_pow (c.ev 1 f) (c.ev 1 P) (d * N₀ + 1)
  rw [← map_sub] at hsub
  simpa using dvd_add (hR.trans hsub) ha

end GlobalTheory.AugNil
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem ql_comb_top : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  intro B O Q _ _ _ _ θ d μ hμ ι _ e he w
  have hc : ∀ i, constantCoeff (up Q μ i) = 0 := by
    intro i
    simp [up, hμ.const i]
  have hzero : QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
    refine ⟨by simp, fun i => ⟨0, Submodule.mem_top, by simp [lin]⟩, fun α => ⟨0, Submodule.mem_top, ?_⟩⟩
    have := formalCoboundary_smul hc (0 : Q) 0
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have hadd : ∀ f g : MvPowerSeries (Fin d) Q, QL μ ⊤ f → QL μ ⊤ g → QL μ ⊤ (f + g) := by
    rintro f g ⟨hf0, hf1, hf2⟩ ⟨hg0, hg1, hg2⟩
    refine ⟨by simp [hf0, hg0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      obtain ⟨b, -, hb⟩ := hg1 i
      exact ⟨a + b, Submodule.mem_top, by simp only [lin, map_add (f := _)] at ha hb ⊢; rw [ha, hb]⟩
    · obtain ⟨a, -, ha⟩ := hf2 α
      obtain ⟨b, -, hb⟩ := hg2 α
      exact ⟨a + b, Submodule.mem_top, by rw [formalCoboundary_add hc, map_add (f := _), ha, hb, map_add (f := _)]⟩
  have hsmul : ∀ (c : B) (f : MvPowerSeries (Fin d) Q), QL μ ⊤ f → QL μ ⊤ (algebraMap B Q c • f) := by
    rintro c f ⟨hf0, hf1, hf2⟩
    refine ⟨by simp [hf0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      simp only [lin, map_smul, smul_eq_mul] at ha ⊢
      rw [ha, map_mul]
    · obtain ⟨a, -, ha⟩ := hf2 α
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      rw [formalCoboundary_smul hc, map_smul, smul_eq_mul, ha, map_mul]
  unfold comb
  exact Finset.sum_induction _ (QL μ ⊤) hadd hzero fun i _ => hsmul (w i) (e i) (he i)

end GlobalTheory.QLog
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

theorem _root_.GlobalTheory.T.mvPowerSeries_subst_coeff_sub_mem_ideal : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ] (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) → (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) → ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := by
  first | exact @GlobalTheory.SubstMod.subst_coeff_sub_mem | exact GlobalTheory.SubstMod.subst_coeff_sub_mem | (intros; apply GlobalTheory.SubstMod.subst_coeff_sub_mem <;> assumption)
end
