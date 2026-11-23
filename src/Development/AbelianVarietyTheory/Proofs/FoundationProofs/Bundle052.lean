module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
public import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FamOfLevel

theorem redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) : redGL N (γ * δ) = redGL N γ * redGL N δ := by
  simp [redGL]

theorem redGL_eq_one_iff (N : ℕ) (γ : SL(2, ℤ)) : redGL N γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem', redGL]
  constructor
  · intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa using h
  · intro h
    rw [h]; simp

theorem slash_eq_of_redGL_eq (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) {γ δ : SL(2, ℤ)}
    (h : redGL N γ = redGL N δ) : f ∣[k] γ = f ∣[k] δ := by
  have hη : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma N := by
    rw [← redGL_eq_one_iff, redGL_mul, h, ← redGL_mul, mul_inv_cancel]
    simp [redGL]
  have : γ = (γ * δ⁻¹) * δ := by group
  rw [this, SlashAction.slash_mul, hf _ hη]

theorem exists_family (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) :
    ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧
      (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧
      ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  classical
  let F : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α =>
    if h : ∃ γ : SL(2, ℤ), α = redGL N γ then f ∣[k] h.choose else 0
  have hF : ∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ := by
    intro γ
    have h : ∃ δ : SL(2, ℤ), redGL N γ = redGL N δ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact slash_eq_of_redGL_eq N k f hf h.choose_spec.symm
  refine ⟨F, ?_, hF, ?_⟩
  · intro α γ
    rw [gact_one]
    by_cases h : ∃ δ : SL(2, ℤ), α = redGL N δ
    · obtain ⟨δ, rfl⟩ := h
      rw [hF, ← redGL_mul, hF, SlashAction.slash_mul]
    · have h' : ¬ ∃ δ : SL(2, ℤ), α * redGL N γ = redGL N δ := by
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ * γ⁻¹, ?_⟩
        rw [redGL_mul, ← hδ, mul_assoc, ← redGL_mul, mul_inv_cancel]
        simp [redGL]
      simp only [F, dif_neg h, dif_neg h']
      exact SlashAction.zero_slash _ _
  · intro α
    by_cases h : ∃ γ : SL(2, ℤ), α = redGL N γ
    · exact Or.inl h
    · right; simp only [F, dif_neg h]

end GlobalTheory.FamOfLevel
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_redGL_eq {N : ℕ} (g : GL (Fin 2) (ZMod N))
    (hg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1) : ∃ γ : SL(2, ℤ), redGL N γ = g := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) N ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod N)), hg⟩
  refine ⟨γ, Units.ext ?_⟩
  show ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = g
  rw [hγ]; rfl

theorem dg_conj_lift : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), (∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u) ∧ ∀ γ' : SL(2, ℤ), ∃ γ : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u := by
  intro N _ u
  have hdet : ∀ γ : SL(2, ℤ), Matrix.det ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro γ
    exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).2
  have hconj : ∀ (a g : GL (Fin 2) (ZMod N)), Matrix.det ((g : Matrix (Fin 2) (Fin 2) (ZMod N))) = 1 →
      Matrix.det (((a⁻¹ * g * a : GL (Fin 2) (ZMod N))) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro a g hg
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hg, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine ⟨fun γ => ?_, fun γ' => ?_⟩
  · obtain ⟨γ', h⟩ := exists_redGL_eq _ (hconj (dg u) (redGL N γ) (hdet γ))
    refine ⟨γ', ?_⟩
    rw [h]; group
  · obtain ⟨γ, h⟩ := exists_redGL_eq _ (hconj (dg u)⁻¹ (redGL N γ') (hdet γ'))
    refine ⟨γ, ?_⟩
    rw [h]; group

end GlobalTheory.FN
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Per

def qp (q u : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * u)

theorem multipliable_qp {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun m : ℕ => 1 - q ^ (m + 1) * u := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * u)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem qp_shift {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : qp q u = (1 - q * u) * qp q (q * u) := by
  have e : (fun m : ℕ => 1 - q ^ (m + 1 + 1) * u) = fun m : ℕ => 1 - q ^ (m + 1) * (q * u) := by
    funext m; ring
  have h : Multipliable fun m : ℕ => (fun m : ℕ => 1 - q ^ (m + 1) * u) (m + 1) := by
    show Multipliable fun m : ℕ => 1 - q ^ (m + 1 + 1) * u
    rw [e]; exact multipliable_qp hq _
  have := tprod_eq_zero_mul' (f := fun m : ℕ => 1 - q ^ (m + 1) * u) h
  simp only [e, zero_add, pow_one] at this
  exact this

def tp (q u : ℂ) : ℂ := (1 - u) * qp q u * qp q u⁻¹

theorem tp_shift {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) : tp q (q * u) = -u⁻¹ * tp q u := by
  have e : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  unfold tp
  rw [← qp_shift hq u, qp_shift hq (q * u)⁻¹, e]
  have : 1 - u⁻¹ = -u⁻¹ * (1 - u) := by field_simp; ring
  rw [this]; ring

theorem tp_shift_pow {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) (k : ℕ) :
    tp q (q ^ k * u) = (-u⁻¹) ^ k * (q ^ (k.choose 2))⁻¹ * tp q u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : q ^ (k + 1) * u = q * (q ^ k * u) := by ring
    have e2 : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [e, tp_shift hq hq0 (mul_ne_zero (pow_ne_zero _ hq0) hu), ih, e2, pow_add q, pow_succ (-u⁻¹)]
    generalize (-u⁻¹) ^ k = A
    field_simp

theorem cth_eq {q t : ℂ} (hq : ‖q‖ < 1) (c : ℕ) (h1 : ∀ m : ℕ, 1 - q ^ (m + 1) * t ^ c ≠ 0)
    (h2 : ∀ m : ℕ, 1 - q ^ (m + 1) * (t ^ c)⁻¹ ≠ 0) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have pA := (multipliable_qp hq t).hasProd
  have pB := (multipliable_qp hq t⁻¹).hasProd
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ h1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ h2
  have hP : HasProd (fun m : ℕ => cthFac c q t (m + 1)) (qp q t ^ (c ^ 2) * qp q t⁻¹ ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, div_eq_mul_inv, qp] using this
  have eC : qp q (t ^ c) = C := pC.tprod_eq
  have eD : qp q (t ^ c)⁻¹ = D := pD.tprod_eq
  unfold cth tp
  rw [hP.tprod_eq, eC, eD]
  simp only [div_eq_mul_inv, mul_inv, mul_pow]
  ring

theorem expo (c : ℕ) : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c.choose 2 : ℕ) : ℤ) := by
  have h : (c : ℤ) - (c : ℤ) ^ 2 = 2 * -((c.choose 2 : ℕ) : ℤ) := by
    induction c with
    | zero => simp
    | succ k ih =>
      have e2 : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
      rw [e2]; push_cast; linarith
  rw [h]; exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem mono_shift {q t : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ht : t ≠ 0) (c : ℕ) :
    (-(q * t)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q (q * t) ^ (c ^ 2) / tp q ((q * t) ^ c)) =
      (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have hs : (-t⁻¹) ^ (c ^ 2) = (-(t ^ c)⁻¹) ^ c := by
    have hpar : (-1 : ℂ) ^ (c ^ 2) = (-1) ^ c := by
      rcases Nat.even_or_odd c with h | h
      · rw [h.neg_one_pow, (h.pow_of_ne_zero two_ne_zero).neg_one_pow]
      · rw [h.neg_one_pow, h.pow.neg_one_pow]
    rw [neg_pow, neg_pow (t ^ c)⁻¹, hpar, ← inv_pow, ← pow_mul, sq]
  have hn : (-(t ^ c)⁻¹) ^ c ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  have hqk : q ^ (c.choose 2) ≠ 0 := pow_ne_zero _ hq0
  have e : -(q * t) = q * -t := by ring
  rw [tp_shift hq hq0 ht, mul_pow q t c, tp_shift_pow hq hq0 (pow_ne_zero c ht), mul_pow, hs, e, mul_zpow, expo,
    zpow_neg q, zpow_natCast]
  generalize (-(t ^ c)⁻¹) ^ c = A at hn
  generalize q ^ (c.choose 2) = B at hqk
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

theorem sg_eq {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    sg c x τ = ee τ ^ ((c ^ 2 - 1) / 12) * ((-ee (pt x τ)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (tp (ee τ) (ee (pt x τ)) ^ (c ^ 2) / tp (ee τ) (ee (pt x τ) ^ c))) := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  unfold sg
  rw [cth_eq (norm_ee_lt_one τ) c (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).1)
    (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).2), mul_assoc]

theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (n : Fin 2 → ℤ) : admitted c fun i => x i + n i := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact h.2.2 ⟨⟨a - c * n 0, by push_cast; rw [ha]; ring⟩, ⟨b - c * n 1, by push_cast; rw [hb]; ring⟩⟩

theorem sg_step {c : ℕ} {x y : Fin 2 → ℚ} (hx : admitted c x) (hy : admitted c y) (τ : ℍ) (h0 : y 0 = x 0 + 1) (h1 : y 1 = x 1) :
    sg c y τ = sg c x τ := by
  have e : ee (pt y τ) = ee τ * ee (pt x τ) := by
    rw [← ee_add]; congr 1; simp only [pt, h0, h1]; push_cast; ring
  rw [sg_eq hx, sg_eq hy, e, mono_shift (norm_ee_lt_one τ) (ee_ne_zero _) (ee_ne_zero _)]

theorem sg_fst {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (τ : ℍ) (k : ℤ) :
    sg c (fun i => x i + (![k, 0] : Fin 2 → ℤ) i) τ = sg c x τ := by
  induction k using Int.induction_on with
  | zero =>
    congr 1; funext i; fin_cases i <;> simp
  | succ k ih =>
    rw [← ih]
    exact sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)
  | pred k ih =>
    rw [← ih]
    exact (sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)).symm

theorem sg_add_int : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x →
    sg c (fun i => x i + n i) τ = sg c x τ := by
  intro c x n τ hx
  rw [← sg_fst hx τ (n 0)]
  have e1 : ee (n 1 : ℂ) = 1 := by
    unfold ee
    rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
  unfold sg
  congr 1
  rw [← mul_one (ee (pt (fun i => x i + (![n 0, 0] : Fin 2 → ℤ) i) τ)), ← e1, ← ee_add]
  congr 1
  simp [pt]; ring

end GlobalTheory.Sieg.Per
end
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_ne_zero : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x τ ≠ 0 :=
  fun _ _ τ h => (GlobalTheory.Sieg.Model.multipliable_and_sg_ne_zero h τ).2.2

end GlobalTheory.Sieg
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.QConst

open Filter Topology

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private theorem natDegree_lt_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p.natDegree < w + 1 := by
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem norm_eval_le_sum_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (x : ℂ) : ‖p.eval x‖ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j‖ * ‖x‖ ^ j := by
  rw [eval_eq_sum_range' (natDegree_lt_of_mem_degreeLT hp)]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_mul, norm_pow]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem eq_C_of_eval_add_natCast_eq {Q : ℂ[X]} {n : ℕ} (hn : 0 < n)
    (hQ : ∀ x : ℂ, Q.eval (x + n) = Q.eval x) : Q = C (Q.coeff 0) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : ∀ k : ℕ, IsRoot (Q - C (Q.eval 0)) ((k : ℂ) * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℂ) * n = (k : ℂ) * n + n := by push_cast; ring
      simp only [IsRoot.def, eval_sub, eval_C] at ih ⊢
      rw [hk, hQ]
      exact ih
  have hinf : Set.Infinite {x | IsRoot (Q - C (Q.eval 0)) x} :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * n)
      (fun a b hab => by exact_mod_cast mul_right_cancel₀ hn' hab) hroot
  rw [coeff_zero_eq_eval_zero]
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem tendsto_exp_neg_mul_mul_add_pow_zero {c : ℝ} (hc : 0 < c) (b : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => Real.exp (-c * y) * (b + y) ^ m) atTop (𝓝 0) := by
  have h1 := ((isLittleO_pow_exp_pos_mul_atTop m hc).comp_tendsto
    (tendsto_atTop_add_const_left atTop b tendsto_id)).tendsto_div_nhds_zero
  have h2 := h1.const_mul (Real.exp (c * b))
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id]
  rw [mul_add, Real.exp_add, neg_mul, Real.exp_neg]
  field_simp


open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
theorem _root_.GlobalTheory.HeckeFamilyMatrices.QConst.qconst : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    Q = C (Q.coeff 0) := by
  intro w n V Q C' c hn hc hQ hV hper h
  have hT : _root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := by
    unfold _root_.GlobalTheory.HeckeFamilyMatrices.mat
    exact ModularGroup.coe_T_zpow _
  have htrans : ∀ (τ : ℍ) (x : ℂ),
      (V τ).eval x = (V (ModularGroup.T ^ (n : ℤ) • τ)).eval (x + n) := by
    intro τ x
    rw [← hper τ, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ x (hV _) (by rw [hT]; simp), hT]
    simp
  have hbound : ∀ τ : ℍ, 1 ≤ τ.im → ∀ b : ℝ, 1 + ‖(τ : ℂ)‖ ≤ b → ∀ x : ℂ,
      ‖(V τ - Q).eval x‖ ≤ C' * Real.exp (-c * τ.im) * b ^ w *
        ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j := by
    intro τ hτ b hb x
    have hC' : 0 ≤ C' := by
      have h0 := h τ hτ 0 (Nat.zero_le _)
      have : 0 < Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by positivity
      nlinarith [norm_nonneg ((V τ - Q).coeff 0)]
    rw [Finset.mul_sum]
    refine (norm_eval_le_sum_of_mem_degreeLT (Submodule.sub_mem _ (hV τ) hQ) x).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hj' : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact mul_le_mul_of_nonneg_right ((h τ hτ j hj').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb w)
        (mul_nonneg hC' (Real.exp_pos _).le))) (by positivity)
  refine eq_C_of_eval_add_natCast_eq hn fun x => ?_
  set M : ℝ := ∑ j ∈ Finset.range (w + 1), ‖x + n‖ ^ j + ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j
  have hest : ∀ y : ℝ, 1 ≤ y → ‖Q.eval (x + n) - Q.eval x‖ ≤
      C' * M * (Real.exp (-c * y) * ((1 + n) + y) ^ w) := by
    intro y hy
    let τ : ℍ := ⟨(y : ℂ) * Complex.I, by simp; linarith⟩
    have hτim : τ.im = y := by simp [τ, UpperHalfPlane.im]
    have hτn : ‖(τ : ℂ)‖ = y := by
      simp [τ, abs_of_pos (show (0 : ℝ) < y by linarith)]
    have hτ'c : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = τ + n := by
      rw [ModularGroup.coe_T_zpow_smul_eq]
      simp
    have hτ'im : (ModularGroup.T ^ (n : ℤ) • τ).im = y := by
      rw [← hτim, ← UpperHalfPlane.coe_im, hτ'c, ← UpperHalfPlane.coe_im]
      simp
    have hτ'n : 1 + ‖((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ)‖ ≤ (1 + n) + y := by
      rw [hτ'c]
      have := norm_add_le (τ : ℂ) (n : ℂ)
      rw [hτn, Complex.norm_natCast] at this
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 := hbound τ (by rw [hτim]; exact hy) ((1 + n) + y) (by rw [hτn]; linarith) x
    have e2 := hbound _ (by rw [hτ'im]; exact hy) ((1 + n) + y) hτ'n (x + n)
    rw [hτim] at e1
    rw [hτ'im] at e2
    have hsplit : Q.eval (x + n) - Q.eval x =
        (V τ - Q).eval x - (V (ModularGroup.T ^ (n : ℤ) • τ) - Q).eval (x + n) := by
      simp only [eval_sub, htrans τ x]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    simp only [M]
    ring
  have hlim := (tendsto_exp_neg_mul_mul_add_pow_zero hc (1 + n) w).const_mul (C' * M)
  rw [mul_zero] at hlim
  have hle : ‖Q.eval (x + n) - Q.eval x‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hest⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

end GlobalTheory.HeckeFamilyMatrices.QConst
end
