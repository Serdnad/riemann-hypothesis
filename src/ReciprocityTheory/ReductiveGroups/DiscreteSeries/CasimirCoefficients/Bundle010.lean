module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhiA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle003

@[expose] public section

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace CapPhi

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

lemma capelliC_negT {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] (E : Fin n → Fin n → 𝒰) (x : ℂ) :
    capelliC (fun a b => -E b a) x = (-1) ^ n * rminor E id id ((n : ℂ) - 1 - x) := by
  unfold capelliC cminor rminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← (Int.cast_commute _ _).eq, mul_assoc]
  congr 1
  have hf : (fun j : Fin n => capEntry (fun a b => -E b a) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) =
      Neg.neg ∘ fun j : Fin n => capEntry E ((n : ℂ) - 1 - x - ((n : ℕ) : ℂ) + 1 + ((j : ℕ) : ℂ)) (id j)
        (id (σ j)) := by
    funext j
    simp only [capEntry, id, Function.comp]
    by_cases h : σ j = j
    · simp only [h, if_true]
      rw [neg_add, ← map_neg]
      congr 2
      ring
    · have h' : ¬ j = σ j := fun e => h e.symm
      simp only [if_neg h, if_neg h', add_zero]
  rw [hf, ← List.map_ofFn, List.prod_map_neg, List.length_ofFn]

def negE : Fin n → Fin n → Module.End ℂ (smoothS n) := fun a b => eOp (-(Matrix.single a b (1 : ℂ)))

lemma single_mul_single' (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs <;> simp_all

lemma isGlRep_negE : IsGlRep (negE (n := n)) := by
  apply isGlRep_eOp
  intro a b c d
  simp only [neg_mul_neg, single_mul_single']
  split_ifs <;> abel

lemma negE_apply (a b : Fin n) (G : smoothS n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    ((negE a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z = -Lhol (Matrix.single a b 1) G z := by
  show ltOp (-(Matrix.single a b (1 : ℂ))) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z = _
  rw [ltOp_of_mem _ hz]
  show fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z (-(Matrix.single a b (1 : ℂ)) * z) =
    -fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z (Matrix.single a b 1 * z)
  rw [Matrix.neg_mul, map_neg]

lemma negE_apply_out (a b : Fin n) (G : smoothS n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) :
    ((negE a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z = 0 := by
  exact ltOp_of_not_mem _ hz

def phiS (μ : Fin n → ℤ) : smoothS n :=
  ⟨(OmegaSet n).indicator (PhiM μ),
    (show ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) from fun _ hz => (contDiffAt_phiM μ hz).contDiffWithinAt).congr
      fun _ hz => Set.indicator_of_mem hz _⟩

lemma phiS_eqOn (μ : Fin n → ℤ) : Set.EqOn (PhiM μ) ((phiS μ : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (OmegaSet n) :=
  fun _ hz => (Set.indicator_of_mem hz (PhiM μ)).symm

lemma phiS_up (μ : Fin n → ℤ) (a b : Fin n) (hab : a < b) : (-negE b a) (phiS μ) = 0 := by
  apply Subtype.ext
  funext z
  show -((negE b a (phiS μ) : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z = 0
  by_cases hz : z ∈ OmegaSet n
  · rw [negE_apply _ _ _ hz, ← lhol_congr (phiS_eqOn μ) hz, lhol_phiM_lower μ hab hz, neg_zero, neg_zero]
  · rw [negE_apply_out _ _ _ hz, neg_zero]

lemma phiS_diag (μ : Fin n → ℤ) (a : Fin n) : (-negE a a) (phiS μ) = (-(μ a : ℂ)) • phiS μ := by
  apply Subtype.ext
  funext z
  show -((negE a a (phiS μ) : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z =
    (-(μ a : ℂ)) • ((phiS μ : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z
  by_cases hz : z ∈ OmegaSet n
  · rw [negE_apply _ _ _ hz, ← lhol_congr (phiS_eqOn μ) hz, lhol_phiM_diag μ a hz, ← phiS_eqOn μ hz,
      smul_eq_mul]
    ring
  · rw [negE_apply_out _ _ _ hz]
    show -(0 : ℂ) = (-(μ a : ℂ)) • (OmegaSet n).indicator (PhiM μ) z
    rw [Set.indicator_of_notMem hz, smul_zero, neg_zero]

lemma capelliC_phiS (μ : Fin n → ℤ) (u : ℂ) :
    capelliC (negE (n := n)) u (phiS μ) =
      ((-1) ^ n * ∏ a : Fin n, ((n : ℂ) - 1 - u + -(μ a : ℂ) - ((a : ℕ) : ℂ))) • phiS μ := by
  have hw := capelliC_hw (fun a b => -negE (n := n) b a) (fun a => -(μ a : ℂ)) (phiS μ)
    ((n : ℂ) - 1 - u) (phiS_up μ) (phiS_diag μ)
  rw [capelliC_negT, sub_sub_cancel] at hw
  have hR : capelliC (negE (n := n)) u = rminor (negE (n := n)) id id u :=
    cminor_eq_rminor (negE (n := n)) isGlRep_negE id id u
  have hm : ∀ (A : Module.End ℂ (smoothS n)) (v : smoothS n), ((-1) ^ n * A) v = ((-1 : ℂ) ^ n) • A v := by
    intro A v
    rw [show ((-1 : Module.End ℂ (smoothS n))) ^ n = algebraMap ℂ _ ((-1 : ℂ) ^ n) by simp,
      Module.End.mul_apply, Module.algebraMap_end_apply]
  rw [hm] at hw
  rw [hR, mul_smul, ← hw, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

lemma top_eqOn (x : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (h : Set.EqOn F G (OmegaSet n)) :
    Set.EqOn (Formalism.QuantumDeterminants.Top negL x a b F) ((capEntry negE x a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (OmegaSet n) := by
  intro z hz
  have hF : F z = (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z := h hz
  have hL : Lhol (Matrix.single a b 1) F z = Lhol (Matrix.single a b 1) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
    show fderiv ℂ F z _ = fderiv ℂ (G : Matrix (Fin n) (Fin n) ℂ → ℂ) z _
    rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (isOpen_omega.mem_nhds hz) h)]
  have hN := negE_apply a b G hz
  simp only [Formalism.QuantumDeterminants.Top, negL, capEntry, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  split_ifs with hab
  · simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hN, hF, hL, smul_eq_mul]
    ring
  · simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply, hN, hL, zero_add, add_zero]

lemma fold_eqOn : ∀ (p : ℕ) (T : Fin p → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (A : Fin p → Module.End ℂ (smoothS n)),
    (∀ i (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (T i F) ((A i G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)) →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn ((List.ofFn T).foldr (fun t h => t h) F)
        ((((List.ofFn A).prod) G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)
  | 0, T, A, _, F, G, h => by simpa using h
  | p + 1, T, A, hTA, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact hTA 0 _ _ (fold_eqOn p (fun i => T i.succ) (fun i => A i.succ) (fun i => hTA i.succ) F G h)

lemma qdet_eq (u : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n) (h : Set.EqOn F G (OmegaSet n))
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp negL u F z = ((capelliC (negE (n := n)) u G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp capelliC cminor
  simp only [Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := fold_eqOn n (fun k : Fin n => Formalism.QuantumDeterminants.Top negL (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k))
    (fun j : Fin n => capEntry (negE (n := n)) (u - ((j : ℕ) : ℂ)) (id (σ j)) (id j))
    (fun i F' G' h' => top_eqOn _ _ _ F' G' h') F G h hz
  rw [Pi.smul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, Int.cast_smul_eq_zsmul]
  exact congrArg _ key

end CapPhi

open CapPhi in
theorem cap_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) (Y : ℂ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp negL (Y + ((n : ℂ) - 1) / 2) (PhiM μ) z =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y * PhiM μ z := by
  rw [qdet_eq (Y + ((n : ℂ) - 1) / 2) (PhiM μ) (phiS μ) (phiS_eqOn μ) hz, capelliC_phiS,
    Submodule.coe_smul, Pi.smul_apply, ← phiS_eqOn μ hz, smul_eq_mul]
  congr 1
  have hfac : ∀ a : Fin n, ((n : ℂ) - 1 - (Y + ((n : ℂ) - 1) / 2) + -(μ a : ℂ) - ((a : ℕ) : ℂ)) =
      (-1) * (Y + (lam a : ℂ)) := by
    intro a
    have h1 : (μ a : ℝ) = lam a + (((n : ℝ) - 1) / 2 - (a : ℕ)) := hμ a
    have h2 : (μ a : ℂ) = (lam a : ℂ) + (((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) := by
      have h3 := congrArg (fun x : ℝ => (x : ℂ)) h1
      push_cast at h3
      linear_combination h3
    rw [h2]
    ring
  unfold Formalism.QuantumDeterminants.capP
  simp only [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_assoc, ← mul_pow]
  norm_num

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem single_mul_single_one (i j k l : Fin n) :
    Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem lhol_neg (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol (-X) F z = -Lhol X F z := by
  simp [Lhol, Matrix.neg_mul]

theorem phiM_contDiffOn (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) :=
  fun _ hz => (contDiffAt_phiM μ hz).contDiffWithinAt

def phiT (μ : Fin n → ℤ) : smoothS n :=
  ⟨(OmegaSet n).indicator (PhiM μ), (phiM_contDiffOn μ).congr fun _ hz => Set.indicator_of_mem hz _⟩

theorem phiT_eqOn (μ : Fin n → ℤ) :
    Set.EqOn (PhiM μ) ((phiT μ : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n) :=
  fun _ hz => (Set.indicator_of_mem hz _).symm

theorem eOp_phiT (μ : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (h : ∀ z ∈ OmegaSet n, Lhol X (PhiM μ) z = c * PhiM μ z) : eOp X (phiT μ) = c • phiT μ := by
  apply Subtype.ext
  funext z
  rw [eOp_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, lhol_congr (phiT_eqOn μ).symm hz, h z hz, ← phiT_eqOn μ hz]
  · rw [ltOp_of_not_mem _ hz]
    simp [phiT, Set.indicator_apply, hz]

def xRev (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => -Matrix.single (Fin.rev a) (Fin.rev b) 1

def xTr (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => Matrix.single b a 1

theorem xRev_rel (a b c d : Fin n) : xRev n c d * xRev n a b - xRev n a b * xRev n c d =
    (if b = c then xRev n a d else 0) - (if d = a then xRev n c b else 0) := by
  unfold xRev
  rw [neg_mul_neg, neg_mul_neg, single_mul_single_one, single_mul_single_one]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = a
    · subst h2
      simp <;> abel
    · simp [h2, Ne.symm h2]
  · by_cases h2 : d = a
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem xTr_rel (a b c d : Fin n) : xTr n c d * xTr n a b - xTr n a b * xTr n c d =
    (if b = c then xTr n a d else 0) - (if d = a then xTr n c b else 0) := by
  unfold xTr
  rw [single_mul_single_one, single_mul_single_one]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = a
    · subst h2
      simp <;> abel
    · simp [h2, Ne.symm h2]
  · by_cases h2 : d = a
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem hw_rev (μ : Fin n → ℤ) :
    IsHWVec (fun a b => eOp (xRev n a b)) (fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xRev
    rw [lhol_neg, lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xRev n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xRev
      rw [lhol_neg, lhol_phiM_lower μ (Fin.rev_lt_rev.2 hab) hz]
      simp
    rw [h0, zero_smul]

theorem hw_tr (μ : Fin n → ℤ) :
    IsHWVec (fun a b => eOp (xTr n a b)) (fun a => -((μ a : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xTr
    rw [lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xTr n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xTr
      rw [lhol_phiM_lower μ hab hz]
      simp
    rw [h0, zero_smul]

theorem rho_rev_add (a : Fin n) : rho n (Fin.rev a) + rho n a = 0 := by
  have ha := a.isLt
  unfold rho
  rw [Fin.val_rev, Nat.cast_sub (by omega : a.val + 1 ≤ n)]
  push_cast
  ring

private theorem gval_comp_perm (l : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    gval (fun r => l (σ r)) k = gval l k := by
  have h : (∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l (σ r)) * PowerSeries.X)⁻¹)) =
      ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹) :=
    Equiv.prod_comp σ (fun r => 1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)
  unfold gval gelfandSeries
  beta_reduce
  rw [h]

theorem gelfand_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (PhiM μ) z =
        ((-1 : ℂ) ^ k * gval (icShift lam) k) * PhiM μ z ∧
      opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (PhiM μ) z =
        gval (icShift (-lam)) k * PhiM μ z := by
  constructor
  · have hY : ∀ a b, Matrix.single a b (1 : ℂ) = (-1 : ℂ) • xRev n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xRev]
    have hν : ((fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) + rho n) = fun a => lam (Fin.revPerm a) := by
      funext a
      simp only [Pi.add_apply, Fin.revPerm_apply, hμ (Fin.rev a)]
      have := rho_rev_add (n := n) a
      linarith
    refine (opGelfand_eq (xRev n) _ Fin.revPerm (-1) hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xRev n) xRev_rel) (hw_rev μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz]
    rw [show icShift (fun a => lam (Fin.revPerm a)) = fun a => icShift lam (Fin.revPerm a) from rfl,
      gval_comp_perm]
    ring
  · have hY : ∀ a b, Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ) =
        (1 : ℂ) • xTr n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xTr]
    have hν : ((fun a => -((μ a : ℤ) : ℝ)) + rho n) = -lam := by
      funext a
      simp only [Pi.add_apply, Pi.neg_apply, hμ a]
      ring
    refine (opGelfand_eq (xTr n) _ Fin.revPerm 1 hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xTr n) xTr_rel) (hw_tr μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz, one_pow, one_mul]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
