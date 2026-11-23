module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle060
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m] [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) → (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 → Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  first | exact @GlobalTheory.PMonE.normal_of_inv_mul | exact GlobalTheory.PMonE.normal_of_inv_mul | (intros; apply GlobalTheory.PMonE.normal_of_inv_mul <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (r : ℕ), IsTest (unitG r F) := by
  first | exact @GlobalTheory.JR.UnitTest.unitG_isTest | exact GlobalTheory.JR.UnitTest.unitG_isTest | (intros; apply GlobalTheory.JR.UnitTest.unitG_isTest <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (H₀ : Matrix (Fin r) (Fin r) F), H₀.IsSymm → H₀.det ≠ 0 → ∃ (Ω : Set (Matrix (Fin r) (Fin r) F)) (k : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F), IsOpen Ω ∧ H₀ ∈ Ω ∧ ContinuousOn k Ω ∧ k H₀ = 1 ∧ ∀ H ∈ Ω, H.IsSymm → (k H)ᵀ * H₀ * k H = H := by
  first | exact @GlobalTheory.symm_congr_local_continuous | exact GlobalTheory.symm_congr_local_continuous | (intros; apply GlobalTheory.symm_congr_local_continuous <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.integralGLSet_isOpen_and_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  first | exact @GlobalTheory.JR.GLift.glO_isOpen_isCompact | exact GlobalTheory.JR.GLift.glO_isOpen_isCompact | (intros; apply GlobalTheory.JR.GLift.glO_isOpen_isCompact <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isTest_unitIndicatorHermitianBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ), (∀ y : E, ‖star y‖ = ‖y‖) → IsTest (unitU r F E) := by
  first | exact @GlobalTheory.JR.isTest_unitU | exact GlobalTheory.JR.isTest_unitU | (intros; apply GlobalTheory.JR.isTest_unitU <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  first | exact @GlobalTheory.JR.transfer_factor_lemma | exact GlobalTheory.JR.transfer_factor_lemma | (intros; apply GlobalTheory.JR.transfer_factor_lemma <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OmegaInv

theorem norm_det_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _)

theorem eta_congr {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have hiff : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  unfold eta
  split_ifs <;> tauto

theorem omega_act (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ)
    (k : GL (Fin n) F) (hk : k ∈ glO n F) (Y : Gl n F) : omega (act k Y) = omega Y := by
  unfold omega
  apply eta_congr
  have h1 := (GlobalTheory.JR.transfer_factor_lemma F n).1
  have h2 := (GlobalTheory.JR.transfer_factor_lemma F n).2
  have hl : lastDet (act k Y) = lastDet Y * ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
    rw [h1, h1, h2, Matrix.det_mul, mul_assoc]
  have ha := norm_det_le_one _ (fun i j => (hk i j).1)
  have hb := norm_det_le_one _ (fun i j => (hk i j).2)
  have hprod : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  have hkinv : ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    apply le_antisymm hb
    by_contra hlt
    push_neg at hlt
    have : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt
    linarith
  rw [hl, norm_mul, hkinv, mul_one]

end GlobalTheory.JR.OmegaInv

theorem GlobalTheory.JR.omega_act_glO : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y :=
  fun F _ _ n k hk Y => GlobalTheory.JR.OmegaInv.omega_act F n k hk Y
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem norm_mulVec_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (i : Fin n) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  rw [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)

theorem norm_vecMul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (v : Fin n → F) (A : Matrix (Fin n) (Fin n) F) (hv : ∀ i, ‖v i‖ ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (j : Fin n) : ‖(v ᵥ* A) j‖ ≤ 1 := by
  rw [Matrix.vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hv k) (norm_nonneg _) (hA k j)

def IsIntegral {F : Type} [NormedField F] {n : ℕ} (Y : Gl n F) : Prop :=
  (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1

theorem isIntegral_act {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ glO n F) {Y : Gl n F} (hY : IsIntegral Y) : IsIntegral (act k Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hY
  refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, h4⟩
  · exact norm_mul_apply_le_one _ _
      (fun i j => norm_mul_apply_le_one _ _ (fun i j => (hk i j).1) h1 i j) (fun i j => (hk i j).2) i j
  · exact norm_mulVec_apply_le_one _ _ (fun i j => (hk i j).1) h2 i
  · exact norm_vecMul_apply_le_one _ _ h3 (fun i j => (hk i j).2) i

theorem act_inv_act {F : Type} [Field F] {n : ℕ} (k : GL (Fin n) F) (Y : Gl n F) :
    act k⁻¹ (act k Y) = Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, inv_inv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((k : Matrix (Fin n) (Fin n) F) * A *
        ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (k : Matrix (Fin n) (Fin n) F) = A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  · show (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) *ᵥ b = b
    rw [Units.inv_mul, Matrix.one_mulVec]
  · show c ᵥ* (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) = c
    rw [Units.inv_mul, Matrix.vecMul_one]

theorem unitG_act : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F),
    k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  intro F _ _ n k hk Y
  have hk' : k⁻¹ ∈ glO n F := (glOSub n F).inv_mem hk
  have key : IsIntegral (act k Y) ↔ IsIntegral Y :=
    ⟨fun h => act_inv_act k Y ▸ isIntegral_act hk' h, isIntegral_act hk⟩
  have e : ∀ Z : Gl n F, unitG n F Z = Set.indicator {Z | IsIntegral Z} 1 Z := fun _ => rfl
  rw [e, e]
  by_cases h : IsIntegral Y
  · rw [Set.indicator_of_mem (show act k Y ∈ {Z | IsIntegral Z} from key.2 h),
      Set.indicator_of_mem (show Y ∈ {Z | IsIntegral Z} from h)]
    rfl
  · rw [Set.indicator_of_notMem (show act k Y ∉ {Z | IsIntegral Z} from fun h' => h (key.1 h')),
      Set.indicator_of_notMem (show Y ∉ {Z | IsIntegral Z} from h)]

end GlobalTheory.JR.GLift
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by
  first | exact @GlobalTheory.TraceUnit.exists_trace_unit | exact GlobalTheory.TraceUnit.exists_trace_unit | (intros; apply GlobalTheory.TraceUnit.exists_trace_unit <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) ∧ Continuous (fun Y : Gl r F => inv Y) ∧ Continuous (fun a : Inv r F => Delta a) ∧ ∀ (C : Set (Gl r F)) (Ω : Set (Inv r F)), IsCompact C → IsCompact Ω → (∀ a ∈ Ω, Delta a ≠ 0) → IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  first | exact @GlobalTheory.JR.OrbitProper.main | exact GlobalTheory.JR.OrbitProper.main | (intros; apply GlobalTheory.JR.OrbitProper.main <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b → ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  first | exact @GlobalTheory.PMonE.LangOnto.lang_onto | exact GlobalTheory.PMonE.LangOnto.lang_onto | (intros; apply GlobalTheory.PMonE.LangOnto.lang_onto <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.lang_count_frobenius_eq_mulVec_solutions : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 → (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧ Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  first | exact @GlobalTheory.PMonE.langCount | exact GlobalTheory.PMonE.langCount | (intros; apply GlobalTheory.PMonE.langCount <;> assumption)
end
