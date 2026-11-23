module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle189
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GelfRec

open Polynomial Matrix

noncomputable def entrySum {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ[X]) (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) : ℂ[X] :=
  ∑ a, ∑ b, (E * (A ^ k).map C) a b

theorem natDegree_adjugate_le (m : ℕ) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (a b : Fin (m + 1)) :
    (adjugate ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C) a b).natDegree
      ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have hs : ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C).submatrix
        b.succAbove a.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove).map C
        + (B.submatrix b.succAbove a.succAbove).map C := by
    rfl
  rw [hs]
  have h1 := natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove)
    (B.submatrix b.succAbove a.succAbove)
  rw [Fintype.card_fin] at h1
  refine natDegree_mul_le.trans ?_
  have h2 : ((-1 : ℂ[X]) ^ ((b : ℕ) + (a : ℕ))).natDegree = 0 := by
    rcases neg_one_pow_eq_or ℂ[X] ((b : ℕ) + (a : ℕ)) with h | h <;> simp [h]
  omega

theorem entrySum_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (k : ℕ) :
    x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A k
        + entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A (k + 1)
      = det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C) * C (∑ a, ∑ b, (A ^ k) a b) := by
  set M := x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C with hM
  set E := adjugate M with hEdef
  have hE : E * M = M.det • (1 : Matrix (Fin n) (Fin n) ℂ[X]) := adjugate_mul M
  have hp : (A ^ (k + 1)).map C = A.map C * (A ^ k).map C := by
    rw [pow_succ']
    exact Matrix.map_mul
  have key : x • (E * (A ^ k).map C) + E * (A ^ (k + 1)).map C = M.det • (A ^ k).map C := by
    have h3 : (E * M) * (A ^ k).map C = M.det • (A ^ k).map C := by
      rw [hE, Matrix.smul_mul, Matrix.one_mul]
    rw [← h3, hp, hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_assoc]
  have h4 := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ[X] => ∑ a, ∑ b, B a b) key
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Matrix.map_apply] at h4

  simp only [entrySum, map_sum]
  exact h4

theorem newton_closed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (N : ℕ) :
    x ^ (N + 1) * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A 0
        - det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)
          * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
      = (-1) ^ N * x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : ∑ k ∈ Finset.range (N + 1), C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
        = x * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
          + C ((-1 : ℂ) ^ N * ∑ a, ∑ b, (A ^ N) a b) * x := by
      have h1 : ∀ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
          = x * (C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)) := by
        intro k hk
        have hk' : k ≤ N := (Finset.mem_range.1 hk).le
        rw [Nat.succ_sub hk', pow_succ]
        ring
      rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.mul_sum]
      simp
    have hstep := entrySum_step A x N
    rw [hs]
    simp only [map_mul, map_pow, map_neg, map_one] at ih hstep ⊢
    linear_combination x * ih + (-1) ^ N * x * hstep

theorem shift_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (X - C c : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C
      = (X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ).map C + (A - c • (1 : Matrix (Fin n) (Fin n) ℂ)).map C := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [Matrix.one_apply_ne h]

theorem natDegree_entrySum_le (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ) (k : ℕ) :
    (entrySum (adjugate ((X - C c : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + A.map C))
      A k).natDegree ≤ m := by
  rw [shift_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  rw [Matrix.mul_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
  exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_le m _ a d)

theorem entrySum_zero {n : ℕ} (l : Fin n → ℂ) (x : ℂ[X]) :
    entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C))
        (Formalism.REAL.Amat l) 0
      = ∏ s, (x + C (l s) + 1) - ∏ s, (x + C (l s)) := by
  have hM : x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C
      = (compRingHom x).mapMatrix
        ((X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C) := by
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have h0 := congrArg (compRingHom x) (GlobalTheory.CompanionTheory.AdjSum.adj_sum n l)

  simp only [map_sum, map_sub, map_prod, map_add (f := _), map_one, coe_compRingHom_apply, X_comp, C_comp] at h0
  rw [← h0, hM, ← RingHom.map_adjugate]
  simp [entrySum]

theorem det_shift (m : ℕ) (χ : Fin (m + 1) → ℂ) :
    det ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
        + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C)
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [det_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.map_apply,
      Formalism.REAL.Amat, Matrix.of_apply, if_true, smul_eq_mul, mul_one]
    rw [hc]
    ring
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := ne_of_gt hij'
    simp [Formalism.REAL.Amat, Matrix.one_apply_ne hne, hne, not_lt.2 hij'.le]

theorem prod_monic (m : ℕ) (c : Fin (m + 1) → ℂ) :
    (∏ s, (X + C (c s))).coeff (m + 1) = 1 := by
  have hm : (∏ s, (X + C (c s))).Monic := monic_prod_of_monic _ _ fun s _ => monic_X_add_C _
  have hd : (∏ s, (X + C (c s))).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
    simp
  have h1 := hm.coeff_natDegree
  rwa [hd] at h1

theorem gelfVal_newton : ∀ (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ), ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).comp (Polynomial.X + 1) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2)))) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) = GlobalTheory.Dec.gelfVal χ N := by
  intro m χ N
  have hdet := det_shift m χ
  have hz := entrySum_zero (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) (X - C (m : ℂ))
  have hc := newton_closed (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hs := entrySum_step (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hdeg := natDegree_entrySum_le m (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (m : ℂ) (N + 1)
  have hterm : ∀ s : Fin (m + 1), (X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2)
      = X + C (χ s - (m : ℂ) / 2) := by
    intro s
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    rw [hc]
    ring
  have hQ : (∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1)
      = ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) + 1) := by
    rw [prod_comp]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hterm s]
    simp
    ring
  have hP : ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2))
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := Finset.prod_congr rfl fun s _ => hterm s
  rw [hP, ← hQ] at hz
  rw [hz, hdet] at hc
  rw [hdet] at hs
  have hsq : (-1 : ℂ[X]) ^ N * (-1) ^ N = 1 := by
    rw [← mul_pow]
    simp
  change _ = ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b
  have hgoal : (-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * ((∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1) - (∏ s, (X + C (χ s - (m : ℂ) / 2)))) - (∏ s, (X + C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (X - C (m : ℂ)) ^ (N - k))
      = C (∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b) * (∏ s, (X + C (χ s - (m : ℂ) / 2)))
        - entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (N + 1) := by
    have hc' := hc
    simp only [GlobalTheory.Dec.gelfVal] at *
    linear_combination (-1 : ℂ[X]) ^ N * hc' + hs + (X - C (m : ℂ)) * entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) N * hsq
  rw [hgoal, coeff_sub, coeff_C_mul, prod_monic m (fun s => χ s - (m : ℂ) / 2),
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hdeg)]
  simp

end GlobalTheory.CompanionTheory.GelfRec
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq.Dep

open GlobalTheory.AbLaw (rs_rs rs_self)

variable {Y : Scheme.{0}}

theorem existsUnique_glue {I : Type} (O : I → Y.Opens) {W : Y.Opens} (hO : ∀ a, O a ≤ W)
    (hc : W ≤ ⨆ a, O a) (s : ∀ a, Γ(Y, O a))
    (h : ∀ a b, rs Y (inf_le_left : O a ⊓ O b ≤ O a) (s a) = rs Y inf_le_right (s b)) :
    ∃! t : Γ(Y, W), ∀ a, rs Y (hO a) t = s a :=
  Y.sheaf.existsUnique_gluing' O W (fun a => homOfLE (hO a)) hc s h

theorem exists_split {U : Y.Opens} (hU : IsAffineOpen U) {I : Type} (O : I → Y.Opens)
    (hO : ∀ a, O a ≤ U) (hc : U ≤ ⨆ a, O a) (φ : ∀ a b, Γ(Y, O a ⊓ O b))
    (hφ : ∀ a b d (W : Y.Opens) (ha : W ≤ O a) (hb : W ≤ O b) (hd : W ≤ O d),
      rs Y (le_inf ha hb) (φ a b) + rs Y (le_inf hb hd) (φ b d) = rs Y (le_inf ha hd) (φ a d)) :
    ∃ ψ : ∀ a, Γ(Y, O a), ∀ a b,
      φ a b = rs Y inf_le_left (ψ a) - rs Y inf_le_right (ψ b) := by
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB Y
  let ch : ∀ W : Y.Opens, GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W ≃ₗ[Γ(Y, W)] Γ(Y, W) :=
    fun W => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top
  have hr : ∀ {W W' : Y.Opens} (h : W' ≤ W) (s : GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W),
      ch W' (GlobalTheory.AbLaw.SecOn.restrict _ h s) = rs Y h (ch W s) := fun {W W'} h s =>
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top h s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU I O hO hc
    (fun a b => (ch _).symm (φ a b)) (by
      intro a b d W ha hb hd
      apply (ch W).injective
      rw [map_add (f := _), hr, hr, hr]
      simpa only [LinearEquiv.apply_symm_apply] using hφ a b d W ha hb hd)
  refine ⟨fun a => ch _ (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, hr, hr]

section Pot

variable {A : Type} (V : A → Y.Opens)

theorem cocycle_on {α : ∀ a b, Γ(Y, V a ⊓ V b)}
    (hα : ∀ a b d, rs Y (le₁₂ V a b d) (α a b) + rs Y (le₂₃ V a b d) (α b d) =
      rs Y (le₁₃ V a b d) (α a d))
    (a b d : A) (W : Y.Opens) (ha : W ≤ V a) (hb : W ≤ V b) (hd : W ≤ V d) :
    rs Y (le_inf ha hb) (α a b) + rs Y (le_inf hb hd) (α b d) = rs Y (le_inf ha hd) (α a d) := by
  have h := congrArg (rs Y (le_inf (le_inf ha hb) hd)) (hα a b d)
  simpa only [map_add (f := _), rs_rs] using h

def IsPot (α : ∀ a b, Γ(Y, V a ⊓ V b)) (U : Y.Opens) (p : ∀ a, Γ(Y, U ⊓ V a)) : Prop :=
  ∀ a b (W : Y.Opens) (h : W ≤ U) (ha : W ≤ V a) (hb : W ≤ V b),
    rs Y (le_inf h ha) (p a) - rs Y (le_inf h hb) (p b) = rs Y (le_inf ha hb) (α a b)

theorem exists_isPot (hV : ⨆ a, V a = ⊤) {α : ∀ a b, Γ(Y, V a ⊓ V b)}
    (hα : ∀ a b d, rs Y (le₁₂ V a b d) (α a b) + rs Y (le₂₃ V a b d) (α b d) =
      rs Y (le₁₃ V a b d) (α a d))
    {U : Y.Opens} (hU : IsAffineOpen U) : ∃ p, IsPot V α U p := by
  obtain ⟨ψ, hψ⟩ := exists_split hU (fun a => U ⊓ V a) (fun _ => inf_le_left)
    (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top))
    (fun a b => rs Y (inf_le_inf inf_le_right inf_le_right) (α a b)) (by
      intro a b d W ha hb hd
      simp only [rs_rs]
      exact cocycle_on V hα a b d W (ha.trans inf_le_right) (hb.trans inf_le_right)
        (hd.trans inf_le_right))
  refine ⟨ψ, fun a b W h ha hb => ?_⟩
  have e := congrArg (rs Y (le_inf (le_inf h ha) (le_inf h hb))) (hψ a b)
  simp only [map_sub, rs_rs] at e
  exact e.symm

variable {V}

theorem existsUnique_diff (hV : ⨆ a, V a = ⊤) {α : ∀ a b, Γ(Y, V a ⊓ V b)} {U W : Y.Opens}
    (h : W ≤ U) {p : ∀ a, Γ(Y, U ⊓ V a)} {q : ∀ a, Γ(Y, W ⊓ V a)} (hp : IsPot V α U p)
    (hq : IsPot V α W q) :
    ∃! f : Γ(Y, W), ∀ a, rs Y (inf_le_left : W ⊓ V a ≤ W) f =
      rs Y (inf_le_inf_right _ h) (p a) - q a := by
  refine existsUnique_glue (fun a => W ⊓ V a) (fun _ => inf_le_left)
    (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top)) _ fun a b => ?_
  have hW : W ⊓ V a ⊓ (W ⊓ V b) ≤ W := inf_le_left.trans inf_le_left
  have ha : W ⊓ V a ⊓ (W ⊓ V b) ≤ V a := inf_le_left.trans inf_le_right
  have hb : W ⊓ V a ⊓ (W ⊓ V b) ≤ V b := inf_le_right.trans inf_le_right
  have e1 := hp a b _ (hW.trans h) ha hb
  have e2 := hq a b _ hW ha hb
  simp only [map_sub, rs_rs]
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact e1.trans e2.symm

end Pot

section Coh

variable {k : Type} [Field k] (s : Y ⟶ Sp k) {A : Type} {V : A → Y.Opens}

theorem rs_cst {U W : Y.Opens} (h : W ≤ U) (c : k) :
    rs Y h (GlobalTheory.SmallExtLift.cst s U c) = GlobalTheory.SmallExtLift.cst s W c :=
  (Sec.res s h).commutes c

theorem smul_eq {U : Y.Opens} (c : k) (x : Γ(Y, U)) :
    @HSMul.hSMul k (Sec s U) (Sec s U) _ c x = GlobalTheory.SmallExtLift.cst s U c * x :=
  Algebra.smul_def (A := Sec s U) c x

variable {α : ∀ a b, Γ(Y, V a ⊓ V b)} (hV : ⨆ a, V a = ⊤)
  {P : ∀ T : Y.affineOpens, ∀ a, Γ(Y, T.1 ⊓ V a)} (hP : ∀ T, IsPot V α T.1 (P T))

def diffF (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) : Γ(Y, T'.1) :=
  (existsUnique_diff hV h (hP T) (hP T')).choose

theorem diffF_spec (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) (a : A) :
    rs Y (inf_le_left : T'.1 ⊓ V a ≤ T'.1) (diffF hV hP T T' h) =
      rs Y (inf_le_inf_right _ h) (P T a) - P T' a :=
  (existsUnique_diff hV h (hP T) (hP T')).choose_spec.1 a

theorem diffF_comp (T T' T'' : Y.affineOpens) (h : T'.1 ≤ T.1) (h' : T''.1 ≤ T'.1) :
    diffF hV hP T T'' (h'.trans h) = rs Y h' (diffF hV hP T T' h) + diffF hV hP T' T'' h' := by
  refine (existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).unique
    (existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).choose_spec.1 fun a => ?_
  have e1 := congrArg (rs Y (inf_le_inf_right (V a) h')) (diffF_spec hV hP T T' h a)
  have e2 := diffF_spec hV hP T' T'' h' a
  simp only [map_sub, rs_rs] at e1
  rw [map_add (f := _), rs_rs, e2]
  rw [show rs Y _ (diffF hV hP T T' h) = _ from e1]
  abel

def diffZ : CatCoh.Z1 (OAff s) :=
  ⟨fun T T' φ => diffF hV hP T.unop T'.unop (leOfHom φ.unop), fun _ _ _ φ ψ =>
    diffF_comp hV hP _ _ _ (leOfHom φ.unop) (leOfHom ψ.unop)⟩

end Coh

end GlobalTheory.CompanionTheory.FewEq.Dep

namespace GlobalTheory.CompanionTheory.FewEq

open Dep
open GlobalTheory.AbLaw (rs_rs rs_self)

theorem depSt : DepSt := by
  intro k _ Y s₀ hsep n r hfin hle hnr A V hV hVa α hα
  have hex := fun (i : Fin r) (T : Y.affineOpens) => exists_isPot V hV (hα i) T.2
  choose p hp using hex
  let f : Fin r → CatCoh.Z1 (OAff s₀) := fun i => diffZ s₀ hV (hp i)
  have hnot : ¬ LinearIndependent k (fun i => CatCoh.H1.mk (OAff s₀) (f i)) := fun hli => by
    have : r ≤ Module.finrank k (HO1 s₀) :=
      (Fintype.card_fin r).symm.le.trans hli.fintype_card_le_finrank
    omega
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnot
  have h0 : CatCoh.H1.mk (OAff s₀) (∑ i, c i • f i) = 0 := by

    rw [map_sum]
    simpa only [map_smul] using hc
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h0
  obtain ⟨G, hG⟩ : ∃ G : ∀ T : Y.affineOpens, Γ(Y, T.1), ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1),
      G T' - rs Y h (G T) = ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * diffF hV (hp i) T T' h := by
    refine ⟨fun T => g (Opposite.op T), fun T T' h => ?_⟩
    have e := congrFun (congrFun (congrFun hg (Opposite.op T)) (Opposite.op T'))
      (homOfLE (show T' ≤ T from h)).op
    let ev : CatCoh.Z1 (OAff s₀) →+ Γ(Y, T'.1) :=
      { toFun := fun z => z.1 (Opposite.op T) (Opposite.op T') (homOfLE (show T' ≤ T from h)).op
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact e.trans ((map_sum ev (fun i => c i • f i) Finset.univ).trans
      (Finset.sum_congr rfl fun i _ => smul_eq s₀ (c i) _))
  let P : ∀ T : Y.affineOpens, ∀ a, Γ(Y, T.1 ⊓ V a) := fun T a =>
    ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * p i T a + rs Y inf_le_left (G T)
  have hPot : ∀ (T : Y.affineOpens) (a b : A) (W : Y.Opens) (h : W ≤ T.1) (ha : W ≤ V a)
      (hb : W ≤ V b), rs Y (le_inf h ha) (P T a) - rs Y (le_inf h hb) (P T b) =
        rs Y (le_inf ha hb) (∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b) := by
    intro T a b W h ha hb

    simp only [P, map_add (f := _), map_sum, map_mul, rs_rs, rs_cst]
    simp only [← hp _ T a b W h ha hb, mul_sub, Finset.sum_sub_distrib]
    ring
  have hPres : ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) (a : A),
      rs Y (inf_le_inf_right _ h) (P T a) = P T' a := by
    intro T T' h a
    have e := congrArg (rs Y (inf_le_left : T'.1 ⊓ V a ≤ T'.1)) (hG T T' h)

    simp only [map_sub, map_sum, map_mul, rs_rs, rs_cst, diffF_spec, mul_sub,
    Finset.sum_sub_distrib] at e

    simp only [P, map_add (f := _), map_sum, map_mul, rs_rs, rs_cst]
    linear_combination -e
  refine ⟨c, fun a => rs Y (le_inf le_rfl le_rfl) (P ⟨V a, hVa a⟩ a),
    fun h => hi₀ (by rw [h]; rfl), fun a b => ?_⟩
  let T' : Y.affineOpens := ⟨V a ⊓ V b, IsAffineOpen.inf (hVa a) (hVa b)⟩
  have e := hPot T' a b T'.1 le_rfl inf_le_left inf_le_right
  rw [← hPres ⟨V a, hVa a⟩ T' inf_le_left a, ← hPres ⟨V b, hVa b⟩ T' inf_le_right b] at e
  simp only [rs_rs] at e ⊢
  rw [rs_self] at e
  exact e.symm

end GlobalTheory.CompanionTheory.FewEq
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_lead_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    Function.Surjective (leadE K j a (n := a + j)) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | exact GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_surjective <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_lead_zero_of_class_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | exact GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_class_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | exact GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | (intros; apply GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic <;> assumption)
end
