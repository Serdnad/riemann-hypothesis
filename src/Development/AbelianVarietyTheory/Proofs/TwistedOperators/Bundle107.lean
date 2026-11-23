module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Mathlib.MeasureTheory.Function.L2Space
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle099
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle061
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply

@[expose] public section

section


theorem _root_.GlobalTheory.T.regularSemisimple_unitaryGroup_concrete : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple := by
  first | exact @GlobalTheory.RegSSObj.regularSemisimple | exact GlobalTheory.RegSSObj.regularSemisimple | (intros; apply GlobalTheory.RegSSObj.regularSemisimple <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isHilbertSchmidt_of_ae_pointwise_bounded_Lp_two : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  first | exact @GlobalTheory.isHilbertSchmidt_of_ae_bounded | exact GlobalTheory.isHilbertSchmidt_of_ae_bounded | (intros; apply GlobalTheory.isHilbertSchmidt_of_ae_bounded <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.absDetOnStableSubspace_conjTranspose : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)), (∀ y ∈ V, g *ᵥ y ∈ V) → (∀ y ∈ V, gᴴ *ᵥ y ∈ V) → GlobalTheory.FlagMeas.detOn gᴴ V = GlobalTheory.FlagMeas.detOn g V := by
  first | exact @GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose | exact GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose | (intros; apply GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.absDetOnStableSubspace_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)), (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ, GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  first | exact @GlobalTheory.FlagMeas.detOn_exp_smul | exact GlobalTheory.FlagMeas.detOn_exp_smul | (intros; apply GlobalTheory.FlagMeas.detOn_exp_smul <;> assumption)
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.PhiUpperDeriv

theorem differentiableAt_prod {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset ι)
    {f : ι → E → ℂ} {z : E} (h : ∀ i, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ s, f i y) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem differentiableAt_leadMinor {n : ℕ} (l : ℕ) (hl : l ≤ n) (z : Matrix (Fin n) (Fin n) ℂ) :
    DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) z := by
  have hent : ∀ a b : Fin n, DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => y a b) z := by
    intro a b
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun y => y a b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiableAt
  have hexp : (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) = fun y =>
      ∑ σ : Equiv.Perm (Fin l), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i) := by
    funext y
    simp only [leadMinor, Matrix.det_apply', Matrix.submatrix_apply]
  rw [hexp]
  have key : ∀ σ : Equiv.Perm (Fin l), DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i)) z :=
    fun σ => (differentiableAt_prod Finset.univ fun i => hent _ _).const_mul _
  have hsum := DifferentiableAt.sum (u := Finset.univ) fun σ _ => key σ
  rw [Finset.sum_fn] at hsum
  exact hsum

theorem differentiableAt_Phi {n : ℕ} (lam : Fin n → ℝ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n) :
    DifferentiableAt ℂ (Phi lam) y := by
  have hPhi : Phi lam = fun z => ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i)) :=
    funext fun _ => rfl
  rw [hPhi]
  refine differentiableAt_prod Finset.univ fun i => ?_
  exact (differentiableAt_leadMinor (i.val + 1) i.isLt y).zpow (Or.inl (hy i))

theorem Phi_mul_unipotent {n : ℕ} (lam : Fin n → ℝ) {y N : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n)
    (hN : ∀ i i' : Fin n, i' ≤ i → N i i' = 0) (t : ℂ) : Phi lam (y + t • (y * N)) = Phi lam y := by
  have hline : y + t • (y * N) = 1 * y * (1 + t • N) := by
    rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hlo : IsLo (1 : Matrix (Fin n) (Fin n) ℂ) := fun i j hij =>
    Matrix.one_apply_ne (ne_of_lt hij)
  have hup : IsUp (1 + t • N) := fun i j hji => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN i j hji.le, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  have hdiag : ∀ l, (1 : Matrix (Fin n) (Fin n) ℂ) l l ≠ 0 ∧ (1 + t • N) l l ≠ 0 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  obtain ⟨-, hval⟩ := GlobalTheory.PhiTriangular.phiTri n lam 1 y (1 + t • N) hlo hup hdiag hy
  rw [hline, hval]
  have hone : ∀ l, ((1 : Matrix (Fin n) (Fin n) ℂ) l l * (1 + t • N) l l) = 1 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  simp only [hone, _root_.one_zpow, Finset.prod_const_one, one_mul]

theorem fderiv_Phi_upper : ∀ (n : ℕ) (lam : Fin n → ℝ) (y N : Matrix (Fin n) (Fin n) ℂ), y ∈ Omega n →
    (∀ i i' : Fin n, i' ≤ i → N i i' = 0) → fderiv ℂ (Phi lam) y (y * N) = 0 := by
  intro n lam y N hy hN
  have hD : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) y) y := (differentiableAt_Phi lam hy).hasFDerivAt
  have hL : HasDerivAt (fun t : ℂ => y + t • (y * N)) (y * N) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℂ)).smul_const (y * N)).const_add y
    simpa only [one_smul, id] using h1
  have hcomp : HasDerivAt (fun t : ℂ => Phi lam (y + t • (y * N))) (fderiv ℂ (Phi lam) y (y * N)) 0 :=
    hD.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hconst : (fun t : ℂ => Phi lam (y + t • (y * N))) = fun _ => Phi lam y :=
    funext fun t => Phi_mul_unipotent lam hy hN t
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 (Phi lam y))

end GlobalTheory.PhiUpperDeriv
end

section

open Formalism.REAL Finset Polynomial

open GlobalTheory.Dec (gelfVal)

namespace GlobalTheory.CapelliNewton

theorem gelfVal_zero (m : ℕ) (χ : Fin (m+1) → ℂ) : gelfVal χ 0 = (m:ℂ) + 1 := by
  simp [gelfVal, Matrix.one_apply]

theorem etr_apply_all {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (k : ℕ) (w : V) :
    etr E k w = gelfVal χ k • w := by
  cases k with
  | zero => rw [gelfVal_zero]; simp [etr, epow, add_smul]; rw [Nat.cast_smul_eq_nsmul]
  | succ k => exact hetr k w

noncomputable def polyOf {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : ℂ[X] :=
  ∑ i ∈ range (d + 1), C (φ (c i v)) * X ^ i

theorem polyOf_eval {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) (u : ℂ) :
    (polyOf d c φ v).eval u = φ ((∑ i ∈ range (d + 1), u ^ i • c i) v) := by
  unfold polyOf

  rw [eval_finsetSum, LinearMap.sum_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm]

theorem polyOf_natDegree {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).natDegree ≤ d := by
  unfold polyOf
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp (mem_range.mp hi)

theorem polyOf_coeff {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (c : ℕ → Module.End ℂ V)
    (φ : Module.Dual ℂ V) (v : V) : (polyOf d c φ v).coeff d = φ (c d v) := by
  unfold polyOf
  rw [finsetSum_coeff, sum_eq_single d]
  · simp
  · intro b _ hb; simp [coeff_C_mul_X_pow, hb.symm]
  · intro h; exact absurd (self_mem_range_succ d) h

noncomputable def capQ (m : ℕ) (χ : Fin (m+1) → ℂ) : ℂ[X] := ∏ s, (X + C (χ s - (m : ℂ) / 2))

theorem capQ_eval (m : ℕ) (χ : Fin (m+1) → ℂ) (u : ℂ) :
    (capQ m χ).eval u = ∏ s, (u - (m : ℂ) / 2 + χ s) := by
  simp [capQ, eval_prod]; refine prod_congr rfl fun s _ => by ring

theorem capQ_monic (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_add_C _

theorem capQ_natDegree (m : ℕ) (χ : Fin (m+1) → ℂ) : (capQ m χ).natDegree = m + 1 := by
  unfold capQ
  rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem main_succ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ)
    (E : Fin (m+1) → Fin (m+1) → Module.End ℂ V) (χ : Fin (m+1) → ℂ) (hE : GlRel E)
    (hetr : ∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) (u : ℂ) (v : V) :
    qdet E u v = (∏ s, (u - (m : ℂ) / 2 + χ s)) • v := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) E
  set P := polyOf (m + 1) c φ v with hPdef
  have hP : ∀ w : ℂ, φ (qdet E w v) = P.eval w := fun w => by rw [polyOf_eval, hc]

  have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → Module.End ℂ V, ∀ w : ℂ,
      qminor E (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
    intro i j
    obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap (Module.End ℂ V) (m + 1) m E (Fin.succAbove j) (Fin.succAbove i) 0
    exact ⟨c', fun w => by simpa using hc' w⟩
  choose cm hcm using hmin
  let N := m + 1
  let Rc : ℕ → Module.End ℂ V := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * cm i j d * epow E (N + 1) j i
  have hR : ∀ w : ℂ, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V) * qminor E (Fin.succAbove j) (Fin.succAbove i) w * epow E (N + 1) j i
      = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
    intro w
    simp only [Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
    conv_lhs => enter [2, x]; rw [sum_comm]
    rw [sum_comm]
  set Rp := polyOf m Rc φ v
  have hrec : ∀ w : ℂ, (w - m) ^ (N + 1) * (P.eval (w + 1) - P.eval w) - P.eval w * ∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k = (C (-(-1) ^ N) * Rp).eval w := by
    intro w
    have h1 := congrArg (fun T : Module.End ℂ V => φ (T v)) (GlobalTheory.T.traced_qminor_comatrix_truncated_inverse (Module.End ℂ V) m E hE w N)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', hR] at h1
    have h2 : (qdet E w * ∑ k ∈ range (N + 1), algebraMap ℂ (Module.End ℂ V) ((-1) ^ k * (w - m) ^ (N - k)) * etr E k) v
        = (∑ k ∈ range (N + 1), (-1) ^ k * (w - m) ^ (N - k) * gelfVal χ k) • qdet E w v := by
      rw [Module.End.mul_apply, LinearMap.sum_apply]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, etr_apply_all m E χ hetr, smul_smul]
      rw [← sum_smul, map_smul]
    rw [h2] at h1
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_add (f := _), map_smul, LinearMap.sub_apply, map_sub, smul_eq_mul] at h1
    rw [← polyOf_eval] at h1
    simp only [hP] at h1
    simp only [eval_mul, eval_neg, eval_pow, eval_C]
    linear_combination h1
  obtain ⟨rs, hrs, hrsE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m N χ
  have hf := GlobalTheory.T.poly_eq_zero_of_newton_recursion m N (gelfVal χ) (P - C (φ v) * capQ m χ) (C (-(-1) ^ N) * Rp - C (φ v) * rs)
    (Nat.lt_succ_self m) (gelfVal_zero m χ) ?_ ?_ ?_
  · have := congrArg (eval u) hf
    simp only [eval_sub, eval_mul, eval_C, eval_zero, capQ_eval] at this
    rw [map_sub, map_smul, hP, smul_eq_mul]; linear_combination this
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_sub, coeff_C_mul]
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · rw [coeff_eq_zero_of_natDegree_lt ((polyOf_natDegree _ _ _ _).trans_lt h),
        coeff_eq_zero_of_natDegree_lt (by rw [capQ_natDegree]; exact h)]; simp
    · have hk' : k = m + 1 := le_antisymm h hk
      subst hk'
      have := (capQ_monic m χ).coeff_natDegree
      rw [capQ_natDegree] at this
      rw [this, polyOf_coeff, hc1]; simp
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_le _ _ |>.trans (polyOf_natDegree _ _ _ _)
    · exact natDegree_C_mul_le _ _ |>.trans hrs
  · intro w
    have h1 := hrec w
    have h2 := hrsE w
    rw [← capQ_eval m χ (w + 1), ← capQ_eval m χ w] at h2
    simp only [eval_sub, eval_mul, eval_C] at h1 h2 ⊢
    linear_combination h1 - φ v * h2

end GlobalTheory.CapelliNewton

namespace GlobalTheory.CapelliNewton

theorem capelli_of_gelfand : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (k : ℕ) (v : V), etr E (k + 1) v = gelfVal χ (k + 1) • v) → ∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v := by
  intro V _ _ n E χ hE hetr Y v
  cases n with
  | zero => simp [qdet, qminor]
  | succ m =>
    rw [main_succ V m E χ hE hetr]
    congr 1
    refine prod_congr rfl fun s _ => ?_
    push_cast; ring

end GlobalTheory.CapelliNewton
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.powerIntegrability

theorem one_le_hsn {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (g : UJ ε) : 1 ≤ hsn (umat g) := by
  set a : Fin m := ⟨0, hm⟩
  have h : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h2 := congrFun (congrFun h a) a
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at h2
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h2
  have hn : (1 : ℝ) ≤ ∑ l, ‖umat g l a‖ ^ 2 := by
    have e1 : ‖((if ε a = true then 1 else -1 : ℂ))‖ = 1 := by split_ifs <;> simp
    rw [← e1, ← h2]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp [sq]
  have hc : ∑ l, ‖umat g l a‖ ^ 2 ≤ ∑ l, ∑ b, ‖umat g l b‖ ^ 2 :=
    Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun b => ‖umat g l b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)
  unfold hsn
  exact Real.one_le_sqrt.mpr (hn.trans hc)

theorem continuous_hsn_umat {m : ℕ} (ε : Fin m → Bool) : Continuous fun g : UJ ε => hsn (umat g) := by
  unfold hsn
  have hu : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
  refine Real.continuous_sqrt.comp ?_
  fun_prop

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal.powerIntegrability

theorem const_le (m : ℕ) (hm : 1 ≤ m) : 2 * (33 : ℝ) ^ (2 * m ^ 2) ≤ Real.exp (10 * (m : ℝ) ^ 2) := by
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have e1 : Real.exp (10 * (m : ℝ) ^ 2) = Real.exp 10 ^ (m ^ 2) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e10 : (2178 : ℝ) ≤ Real.exp 10 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (2178 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1.le 10
  have e2 : (33 : ℝ) ^ (2 * m ^ 2) = 1089 ^ (m ^ 2) := by rw [pow_mul]; norm_num
  rw [e1, e2]
  calc 2 * (1089 : ℝ) ^ (m ^ 2) ≤ 2 ^ (m ^ 2) * 1089 ^ (m ^ 2) := by
        gcongr; exact le_self_pow₀ (by norm_num) (by omega)
    _ = 2178 ^ (m ^ 2) := by rw [← mul_pow]; norm_num
    _ ≤ Real.exp 10 ^ (m ^ 2) := pow_le_pow_left₀ (by norm_num) e10 _

theorem term_le (m : ℕ) (A : ℝ) (hA : 4 * (m : ℝ) ^ 2 + 1 ≤ A) (j : ℕ) :
    ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2) ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have hb : 1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4) ≤ 33 * 4 ^ j := by
    have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
      rw [← pow_mul, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]; ring
    rw [this]; linarith
  have hr0 : 0 ≤ (2 : ℝ) ^ (-A) := by positivity
  have hq : (2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2) ≤ 1 / 2 := by
    have e : (4 : ℝ) ^ (2 * m ^ 2) = (2 : ℝ) ^ ((4 * m ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [e, ← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (-A + ((4 * m ^ 2 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  calc ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)
      ≤ ((2 : ℝ) ^ (-A)) ^ j * (33 * 4 ^ j) ^ (2 * m ^ 2) := by
        gcongr
    _ = 33 ^ (2 * m ^ 2) * ((2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2)) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j]; ring
    _ ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
        gcongr

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal


open GlobalTheory.SepReal.powerIntegrability in
theorem powInt_of_volBall : VolBall → PowInt := by
  intro hV m ε A hm hA
  obtain ⟨-, hfin, -⟩ := hV m ε (1 / 4) 1 (by norm_num) one_pos
  set μN := muG ε (nbh ε (1 / 4)) with hμN
  set r : ℝ := (2 : ℝ) ^ (-A) with hr
  have hcont := continuous_hsn_umat ε
  have hpos : ∀ g : UJ ε, 0 < hsn (umat g) := fun g => lt_of_lt_of_le one_pos (one_le_hsn hm g)
  have hf_cont : Continuous fun g : UJ ε => hsn (umat g) ^ (-A) :=
    hcont.rpow_const fun g => Or.inl (hpos g).ne'
  have hf_nn : ∀ g : UJ ε, 0 ≤ hsn (umat g) ^ (-A) := fun g => (Real.rpow_pos_of_pos (hpos g) _).le
  let S : ℕ → Set (UJ ε) := fun j => {g | hsn (umat g) ≤ (2 : ℝ) ^ (j + 1)}
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hcont.measurable measurable_const
  have hpt : ∀ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g := by
    intro g
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (one_le_hsn hm g) (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show g ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    have key : r ^ j = ((2 : ℝ) ^ j) ^ (-A) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [key]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith [sq_nonneg (m : ℝ)])
  have hL : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε ≤ ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
    calc ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε
        ≤ ∫⁻ g, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε := lintegral_mono hpt
      _ = ∑' j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε :=
          lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable
      _ = ∑' j, ENNReal.ofReal (r ^ j) * muG ε (S j) := by
          congr 1; funext j; exact lintegral_indicator_const (hS j) _
      _ ≤ ∑' j, ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have hb := (hV m ε (1 / 4) ((2 : ℝ) ^ (j + 1)) (by norm_num) (by positivity)).2.2
          calc ENNReal.ofReal (r ^ j) * muG ε (S j)
              ≤ ENNReal.ofReal (r ^ j) * (ENNReal.ofReal ((1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN) :=
                by gcongr
            _ = ENNReal.ofReal (r ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal (33 ^ (2 * m ^ 2) * (1 / 2) ^ j) * μN := by
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (term_le m A hA j)) (zero_le')
            _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
                have h2 : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) = 2⁻¹ ^ j := by
                  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
                rw [ENNReal.ofReal_mul (by positivity), h2]
      _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * (∑' j : ℕ, (2⁻¹ : ENNReal) ^ j) * μN := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_comm (2 : ENNReal)]
  have hLfin : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε < ⊤ :=
    lt_of_le_of_lt hL (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hnn : 0 ≤ᵐ[muG ε] fun g => hsn (umat g) ^ (-A) := Filter.Eventually.of_forall hf_nn
  refine ⟨⟨hf_cont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hLfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf_cont.aestronglyMeasurable]
  calc (∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε).toReal
      ≤ (ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hL
    _ = 2 * 33 ^ (2 * m ^ 2) * μN.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ Real.exp (10 * (m : ℝ) ^ 2) * μN.toReal :=
        mul_le_mul_of_nonneg_right (const_le m hm) ENNReal.toReal_nonneg

end GlobalTheory.SepReal

end
end

section


theorem _root_.GlobalTheory.T.isInterlaced_sub_single_of_spread : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}, GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) → (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  first | exact @GlobalTheory.SepReal.interlaced_sub_single | exact GlobalTheory.SepReal.interlaced_sub_single | (intros; apply GlobalTheory.SepReal.interlaced_sub_single <;> assumption)
end
