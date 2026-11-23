module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesRightMulPermutesCosets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistribution
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem norm_eval_smul_mul_im_rpow : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  intro w σ P τ hP
  have hden : denom σ τ = ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hj : ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have hc : ((σ • τ : ℍ) : ℂ) = (((mat σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 0 1 : ℤ) : ℂ)) /
      (((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ)) := by
    rw [specialLinearGroup_apply]
    simp
  have him := ModularGroup.im_smul_eq_div_normSq σ τ
  rw [hden] at him
  rw [eval_polySlash w (mat σ) P τ hP hj, ← hc, him]
  set j := ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) with hjdef
  have hn : 0 < ‖j‖ := norm_pos_iff.2 hj
  have hτ : 0 < τ.im := τ.im_pos
  rw [Complex.normSq_eq_norm_sq, Real.div_rpow hτ.le (by positivity), norm_mul, norm_pow]
  have h2 : (‖j‖ ^ 2) ^ (-(w : ℝ) / 2) = (‖j‖ ^ w)⁻¹ := by
    rw [← Real.rpow_natCast ‖j‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_natCast ‖j‖ w,
      ← Real.rpow_neg hn.le]
    congr 1
    push_cast
    ring
  rw [h2, div_inv_eq_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem evalDiag_T_step (w n : ℕ) (V : ℍ → ℂ[X]) (hV : ∀ τ, V τ ∈ degreeLT ℂ (w + 1))
    (hT : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ)
    (τ : ℍ) :
    (V (ModularGroup.T ^ (n : ℤ) • τ)).eval ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  have hm : mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := ModularGroup.coe_T_zpow _
  have hc : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = (τ : ℂ) + n := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast; ring
  rw [← hT τ, eval_polySlash w _ _ _ (hV _), hm, hc]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    simp
  · rw [hm]
    simp

theorem evalDiag_T_invariant : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  intro w n V hV hT m
  have step := evalDiag_T_step w n V hV hT
  simp only [zpow_mul]
  induction m using Int.induction_on with
  | zero => intro τ; simp
  | succ k ih =>
    intro τ
    rw [zpow_add_one, mul_smul, ih, step]
  | pred k ih =>
    intro τ
    have e : (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ) - 1) • τ =
        (ModularGroup.T ^ (n : ℤ)) ^ (-(k : ℤ)) • ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ) := by
      rw [zpow_sub_one, mul_smul]
    rw [e, ih, ← step ((ModularGroup.T ^ (n : ℤ))⁻¹ • τ), smul_inv_smul]

end GlobalTheory.HeckeFamilyMatrices
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.finrank_b1_eq_of_gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 0 < M → 1 ≤ w → CongruenceSubgroup.Gamma M ≤ Γ → Module.finrank ℂ (B1 Γ w) = w + 1 := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le | exact GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ → IsDCReps (Lev N l) (dg 1 q) (tqFam q σ)) ∧ IsDCReps (Lev N l) (dg 1 l) (ulFam l) ∧ ∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ → IsDCReps (Lev N l) (mat σ) (fun _ : Unit => mat σ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level | exact GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level | (intros; apply GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (ι : Type) [Fintype ι] (α : Matrix (Fin 2) (Fin 2) ℤ) (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < α.det → IsDCReps Γ α δ → (∀ z ∈ Z1 Γ w, hk Γ w δ z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, hk Γ w δ z ∈ B1 Γ w) ∧ ∀ z, cj (hk Γ w δ z) = hk Γ w δ (cj z) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj | exact GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj | (intros; apply GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SlashAction

theorem polySlash_matrix_mul : ∀ (w : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) →
    slP w (A * B) p = slP w B (slP w A p) :=
  fun w A B p hp => (GlobalTheory.HeckeFamilyMatrices.HkC.polySlash_comp w A B p (GlobalTheory.HeckeFamilyMatrices.HkC.mem_degLT_iff.1 hp)).symm

end GlobalTheory.HeckeFamilyMatrices.SlashAction
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeTqRepresentatives_right_mul_permutes_cosets : ∀ (N l q : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → q.Prime → ¬ q ∣ N * l → ∀ σ : SL(2, ℤ), IsDiam N l (q : ZMod N) σ → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' : Lev N l, tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  first | exact @GlobalTheory.TqPerm.tqFam_perm | exact GlobalTheory.TqPerm.tqFam_perm | (intros; apply GlobalTheory.TqPerm.tqFam_perm <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.prod_smoothedThetaQProduct_distribution : ∀ (c m : ℕ) (Q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖Q‖ < 1 → Q ≠ 0 → t ≠ 0 → (∀ n : ℤ, Q ^ n * t ^ c ≠ 1) → ∏ j ∈ Finset.range m, cth c (Q ^ m) (t * Q ^ j) = cth c Q t := by
  first | exact @GlobalTheory.Sieg.prod_cth_mul_pow | exact GlobalTheory.Sieg.prod_cth_mul_pow | (intros; apply GlobalTheory.Sieg.prod_cth_mul_pow <;> assumption)
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Hol

theorem differentiable_ee : Differentiable ℂ ee := by
  unfold ee
  exact (differentiable_id.const_mul _).cexp

theorem differentiableOn_geomProd {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    DifferentiableOn ℂ (fun z => ∏' m : ℕ, (1 - ee z ^ (m + 1) * g z)) {z : ℂ | 0 < z.im} := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hec : Continuous ee := differentiable_ee.continuous
  have hgc : Continuous g := hg.continuous
  have hloc : HasProdLocallyUniformlyOn (fun (m : ℕ) (z : ℂ) => 1 + -(ee z ^ (m + 1) * g z))
      (fun z => ∏' m : ℕ, (1 + -(ee z ^ (m + 1) * g z))) {z : ℂ | 0 < z.im} := by
    refine hasProdLocallyUniformlyOn_of_forall_compact hU fun K hK hKc => ?_
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · subst hK0
      exact Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun _ => (0 : ℝ)) summable_zero
        (.of_forall fun n z hz => absurd hz (Set.notMem_empty z))
        (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne (continuous_norm.comp hec).continuousOn
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hgc.continuousOn
    set r := ‖ee z₀‖ with hr_def
    have hr1 : r < 1 := norm_ee_lt_one ⟨z₀, hK hz₀⟩
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr : ∀ z ∈ K, ‖ee z‖ ≤ r := fun z hz => hmax hz
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)
    refine Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun n => C * r * r ^ n)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (C * r)) (.of_forall fun n z hz => ?_)
      (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    rw [norm_neg, norm_mul, norm_pow]
    calc ‖ee z‖ ^ (n + 1) * ‖g z‖ ≤ r ^ (n + 1) * C :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hr z hz) _) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 _)
      _ = C * r * r ^ n := by ring
  have hd := hloc.differentiableOn (.of_forall fun n => by
    simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
      ((differentiable_const (1 : ℂ)).add ((differentiable_ee.pow (i + 1)).mul hg).neg).differentiableOn)) hU
  refine hd.congr fun z _ => ?_
  simp only [sub_eq_add_neg]

def geomProd (q a : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * a)

theorem tprod_cthFac {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ ≠ 0 ∧
    ∏' m : ℕ, cthFac c (ee τ) (ee (pt x τ)) (m + 1) =
      geomProd (ee τ) (ee (pt x τ)) ^ (c ^ 2) * geomProd (ee τ) (ee (pt x τ))⁻¹ ^ (c ^ 2) /
        (geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹) := by
  obtain ⟨hc1, hc6, hnot⟩ := h
  have hq : ‖ee τ‖ < 1 := norm_ee_lt_one τ
  have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact hnot ⟨⟨(c : ℤ) * a, by push_cast; rw [ha]⟩, ⟨(c : ℤ) * b, by push_cast; rw [hb]⟩⟩
  have hcx : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa [nsmul_eq_mul] using hnot
  have htc : ee (pt x τ) ^ c = ee (pt (c • x) τ) := ee_pt_pow c x τ
  have n1 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).1
  have n2 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ))⁻¹ ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).2
  have n3 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ^ c ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).1
  have n4 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ) ^ c)⁻¹ ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).2
  obtain ⟨P1, -, h1⟩ := hasProd_geom hq _ n1
  obtain ⟨P2, -, h2⟩ := hasProd_geom hq _ n2
  obtain ⟨P3, hP3, h3⟩ := hasProd_geom hq _ n3
  obtain ⟨P4, hP4, h4⟩ := hasProd_geom hq _ n4
  have e1 : geomProd (ee τ) (ee (pt x τ)) = P1 := h1.tprod_eq
  have e2 : geomProd (ee τ) (ee (pt x τ))⁻¹ = P2 := h2.tprod_eq
  have e3 : geomProd (ee τ) (ee (pt x τ) ^ c) = P3 := h3.tprod_eq
  have e4 : geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ = P4 := h4.tprod_eq
  rw [e1, e2, e3, e4]
  refine ⟨mul_ne_zero hP3 hP4, ?_⟩
  have hall := ((hasProd_pow h1 (c ^ 2)).mul (hasProd_pow h2 (c ^ 2))).mul
    (hasProd_inv (h3.mul h4) (mul_ne_zero hP3 hP4))
  rw [div_eq_mul_inv, ← hall.tprod_eq]
  refine tprod_congr fun m => ?_
  unfold cthFac
  rw [div_eq_mul_inv]

end GlobalTheory.Sieg.Hol

namespace GlobalTheory.Sieg

open Hol

theorem mdifferentiable_sg :
    ∀ (c : ℕ) (x : Fin 2 → ℚ), admitted c x → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sg c x) := by
  intro c x h
  rw [UpperHalfPlane.mdifferentiable_iff]
  set T : ℂ → ℂ := fun z => ee ((x 0 : ℂ) * z + (x 1 : ℂ)) with hT
  have hTd : Differentiable ℂ T := differentiable_ee.comp ((differentiable_id.const_mul _).add_const _)
  have hT0 : ∀ z, T z ≠ 0 := fun z => ee_ne_zero _
  have hG1 := differentiableOn_geomProd hTd
  have hG2 := differentiableOn_geomProd (hTd.inv hT0)
  have hG3 := differentiableOn_geomProd (hTd.pow c)
  have hG4 := differentiableOn_geomProd ((hTd.pow c).inv fun z => pow_ne_zero _ (hT0 z))
  have hnd : ∀ z ∈ {z : ℂ | 0 < z.im}, 1 - T z ^ c ≠ 0 := fun z hz =>
    (multipliable_and_sg_ne_zero h ⟨z, hz⟩).2.1
  have hnG : ∀ z ∈ {z : ℂ | 0 < z.im}, geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹ ≠ 0 :=
    fun z hz => (tprod_cthFac h ⟨z, hz⟩).1
  have hH : DifferentiableOn ℂ (fun z => ee z ^ ((c ^ 2 - 1) / 12) * (-T z) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (1 - T z) ^ (c ^ 2) / (1 - T z ^ c) *
      (geomProd (ee z) (T z) ^ (c ^ 2) * geomProd (ee z) (T z)⁻¹ ^ (c ^ 2) /
        (geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹))) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.mul (DifferentiableOn.div (DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_) ?_ hnd)
      (DifferentiableOn.div (DifferentiableOn.mul (hG1.pow _) (hG2.pow _)) (hG3.mul hG4) hnG)
    · exact (differentiable_ee.pow _).differentiableOn
    · exact hTd.neg.differentiableOn.zpow (Or.inl fun z _ => neg_ne_zero.mpr (hT0 z))
    · exact (((differentiable_const _).sub hTd).pow _).differentiableOn
    · exact ((differentiable_const _).sub (hTd.pow c)).differentiableOn
  refine hH.congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  unfold sg cth
  rw [(tprod_cthFac h ⟨z, hz'⟩).2]
  rfl

end GlobalTheory.Sieg
end
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (x y : ℂ) : ∏ j ∈ Finset.range m, (x - ζ ^ j * y) = x ^ m - y ^ m := by
  have hinj : Set.InjOn (fun j : ℕ => ζ ^ j) (Finset.range m) := fun i hi j hj h =>
    hζ.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  have himage :
      (Finset.range m).image (fun j : ℕ => ζ ^ j) = Polynomial.nthRootsFinset m (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      rw [Polynomial.mem_nthRootsFinset hm, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [hζ.pow_sub_pow_eq_prod_sub_mul x y hm, ← himage, Finset.prod_image hinj]

open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.ee_nat_div_eq_pow (m j : ℕ) :
    _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m) = Complex.exp (2 * Real.pi * Complex.I / m) ^ j := by
  rw [_root_.GlobalTheory.Sieg.ee, ← Complex.exp_nat_mul]
  congr 1
  ring

open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow {c m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hm : 0 < m) (hc : Nat.Coprime c m) (q t : ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) n =
      _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) n := by
  have key : ∀ {ξ : ℂ}, IsPrimitiveRoot ξ m → ∀ (u : ℂ) (g : ℕ → ℂ), (∀ j, g j = ξ ^ j * u) →
      ∏ j ∈ Finset.range m, (1 - q ^ n * g j) = 1 - (q ^ m) ^ n * u ^ m := by
    intro ξ hξ u g hg
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hξ hm 1 (q ^ n * u)
    rw [one_pow] at h
    calc ∏ j ∈ Finset.range m, (1 - q ^ n * g j)
          = ∏ j ∈ Finset.range m, (1 - ξ ^ j * (q ^ n * u)) :=
          Finset.prod_congr rfl fun j _ => by rw [hg]; ring
      _ = _ := by rw [h]; ring
  unfold _root_.GlobalTheory.Sieg.cthFac
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow,
    Finset.prod_pow, key hζ t _ (fun j => by ring),
    key hζ.inv t⁻¹ _ (fun j => by rw [mul_inv, inv_pow]; ring),
    key (hζ.pow_of_coprime c hc) (t ^ c) _
      (fun j => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring),
    key (hζ.pow_of_coprime c hc).inv (t ^ c)⁻¹ _
      (fun j => by rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm c j, mul_inv]; ring)]
  ring


open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.prod_cth_mul_ee : ∀ (c m : ℕ) (q t : ℂ), 1 < c →
    Nat.Coprime c 6 → 0 < m → Nat.Coprime c m →
    ‖q‖ < 1 → q ≠ 0 → t ≠ 0 → (∀ n : ℤ, q ^ n * t ^ (c * m) ≠ 1) →
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cth c q (t * _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m)) =
      _root_.GlobalTheory.Sieg.cth c (q ^ m) (t ^ m) := by
  intro c m q t _ _ hm hc hq _ ht _
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  simp only [_root_.GlobalTheory.Sieg.ee_nat_div_eq_pow]
  rw [← hζdef]
  have hA : ∏ j ∈ Finset.range m, (-(t * ζ ^ j)) = -t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 0 t
    simp only [zero_pow hm.ne', zero_sub] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hB : ∏ j ∈ Finset.range m, (1 - t * ζ ^ j) = 1 - t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 1 t
    rw [one_pow] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hC : ∏ j ∈ Finset.range m, (1 - (t * ζ ^ j) ^ c) = 1 - (t ^ m) ^ c := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot (hζ.pow_of_coprime c hc) hm 1 (t ^ c)
    rw [one_pow, ← pow_mul, mul_comm c m, pow_mul] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring
  have hD : ∏ j ∈ Finset.range m, ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) (n + 1) =
      ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) (n + 1) := by
    rw [← Multipliable.tprod_finsetProd fun j _ =>
      _root_.GlobalTheory.Sieg.cthFac_multipliable c q _ hq (mul_ne_zero ht (pow_ne_zero _ hζ0))]
    exact tprod_congr fun n => _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow hζ hm hc q t (n + 1)
  unfold _root_.GlobalTheory.Sieg.cth
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_zpow,
    Finset.prod_const, Finset.card_range, hB, hC, hD]
  rw [hA]

end GlobalTheory.Sieg
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.cosetRepresentativeTrace_fixed_properties : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  first | exact @GlobalTheory.AlmostEt.cosetTrace_fixed_props | exact GlobalTheory.AlmostEt.cosetTrace_fixed_props | (intros; apply GlobalTheory.AlmostEt.cosetTrace_fixed_props <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∃ N : Subgroup G, N.Normal ∧ (∀ σ : G, σ ∈ N ↔ ¬ Moves v ⊤ σ) ∧ ∃ i : ℝ≥0, i < 1 ∧ ∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | exact GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | (intros; apply GlobalTheory.AlmostEt.exists_normal_not_moves_uniform <;> assumption)
end
