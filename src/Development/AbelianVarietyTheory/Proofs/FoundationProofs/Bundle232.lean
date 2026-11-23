module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle214
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle702
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle084
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle217
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (c : ℂ) (n : ℕ), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, (fun h => GlobalTheory.Hk.heckeT k q σ h - c • h)^[n] ⇑f = 0 → GlobalTheory.Hk.heckeT k q σ ⇑f = c • ⇑f := by
  first | exact @GlobalTheory.Hk.Semisimple.heckeT_semisimple | exact GlobalTheory.Hk.Semisimple.heckeT_semisimple | (intros; apply GlobalTheory.Hk.Semisimple.heckeT_semisimple <;> assumption)
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelMem


open Polynomial in
theorem mem_range_of_isIntegral {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {α : ℂ}
    (hα : IsIntegral ℚ α) : α ∈ Set.range ε := by
  have h0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hα
  have e : ((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
  have hb : α ∈ (((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε).roots := by
    rw [e, Polynomial.mem_roots (Polynomial.map_ne_zero h0), Polynomial.IsRoot,
      ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ α
  rw [Polynomial.Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

theorem isIntegral_ee {M : ℕ} (hM : 0 < M) : IsIntegral ℚ (ee (1 / (M : ℂ))) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h : ee (1 / (M : ℂ)) ^ M = 1 := by
    rw [ee, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact IsIntegral.of_pow hM (by rw [h]; exact isIntegral_one)

theorem isIntegral_of_mem_adjoin {M : ℕ} (hM : 0 < M) {z : ℂ}
    (hz : z ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) : IsIntegral ℚ z := by
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_ee hM)
  have h := Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))})
  exact IntermediateField.isIntegral_iff.1 h

theorem act_zero (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 0 = x 0 * (γ 0 0 : ℚ) + x 1 * (γ 1 0 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem act_one' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 1 = x 0 * (γ 0 1 : ℚ) + x 1 * (γ 1 1 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) : GlobalTheory.Sieg.admitted c (act x γ) := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hx.2.2 ⟨⟨m0 * γ 1 1 - m1 * γ 1 0, ?_⟩, ⟨m1 * γ 0 0 - m0 * γ 0 1, ?_⟩⟩⟩
  all_goals
    have hdet : ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at this
      exact_mod_cast this
    rw [act_zero] at hm0
    rw [act_one'] at hm1
    push_cast
  · linear_combination (γ 1 1 : ℚ) * hm0 - (γ 1 0 : ℚ) * hm1 + ((c : ℚ) * x 0) * hdet
  · linear_combination (γ 0 0 : ℚ) * hm1 - (γ 0 1 : ℚ) * hm0 + ((c : ℚ) * x 1) * hdet

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem exp_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {c M : ℕ} (hM : 0 < M)
    {y : Fin 2 → ℚ} (P : Fin 2 → ℤ) (hP : ∀ i, (M : ℚ) * y i = P i) (hy : GlobalTheory.Sieg.admitted c y) :
    ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c y τ) := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : ∀ i, ((P i % (M : ℤ)).toNat : ℚ) = ((P i % (M : ℤ) : ℤ) : ℚ) := fun i => by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)]
  have hlt : (P 0 % (M : ℤ)).toNat < M := by
    have := Int.emod_lt_of_pos (P 0) (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  set a0 : ℕ := (P 0 % (M : ℤ)).toNat with ha0
  set a1 : ℕ := (P 1 % (M : ℤ)).toNat with ha1
  set x' : Fin 2 → ℚ := ![(a0 : ℚ) / M, (a1 : ℚ) / M] with hx'
  have hx'i : ∀ i, x' i = ((P i % (M : ℤ) : ℤ) : ℚ) / M := fun i => by
    fin_cases i
    · simp [x', ha0, hr]
    · simp [x', ha1, hr]
  set n : Fin 2 → ℤ := fun i => P i / (M : ℤ) with hn
  have hyx : y = fun i => x' i + n i := by
    funext i
    have h1 : y i = (P i : ℚ) / M := by rw [← hP i]; field_simp
    have h2 : (P i : ℚ) = (M : ℚ) * ((P i / (M : ℤ) : ℤ) : ℚ) + ((P i % (M : ℤ) : ℤ) : ℚ) := by
      have h3 : P i = (M : ℤ) * (P i / (M : ℤ)) + P i % (M : ℤ) := by rw [Int.emod_def]; ring
      exact_mod_cast h3
    rw [h1, hx'i, h2]
    simp only [n]
    field_simp
    ring
  have hadm : GlobalTheory.Sieg.admitted c x' := by
    refine ⟨hy.1, hy.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hy.2.2 ⟨⟨m0 + c * n 0, ?_⟩, ⟨m1 + c * n 1, ?_⟩⟩⟩
    · rw [hyx]; push_cast; rw [hm0]; ring
    · rw [hyx]; push_cast; rw [hm1]; ring
  have hper : ∀ τ : ℍ, sg c y τ = sg c x' τ := fun τ => by
    rw [hyx]; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x' n τ hadm
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A, hQ, -, hA, -, -⟩ := hk a1 hadm
  have hε : ∀ j, ε (Function.invFun ε (A j)) = A j := fun j =>
    Function.invFun_eq (mem_range_of_isIntegral ε (isIntegral_of_mem_adjoin hM (hA j)))
  classical
  refine ⟨fun m => if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0, k,
    fun m hm => by simp [not_le.2 hm], fun τ => ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + k) := fun i j h => by simpa using h
  rw [← Function.Injective.hasSum_iff hinj (fun m hm => by
    have : ¬ k ≤ m := fun h => hm ⟨(m - k).toNat, by simp; omega⟩
    simp [this])]
  have h1 := (hQ τ).mul_left (ee ((k : ℂ) / M * (τ : ℂ)))
  have key : ee ((k : ℂ) / M * (τ : ℂ)) * (sg c x' τ * ee (-((k : ℂ) / M) * (τ : ℂ))) = sg c y τ := by
    rw [hper, mul_left_comm, ee, ee, ← Complex.exp_add]
    have : 2 * ↑Real.pi * Complex.I * ((k : ℂ) / ↑M * ↑τ) + 2 * ↑Real.pi * Complex.I * (-((k : ℂ) / ↑M) * ↑τ) = 0 := by
      ring
    rw [this, Complex.exp_zero, mul_one]
  rw [key] at h1
  have e : (fun m : ℤ => ε (if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / M)) ∘ (fun j : ℕ => (j : ℤ) + k) =
      fun j : ℕ => ee ((k : ℂ) / M * (τ : ℂ)) * (A j * Complex.exp (2 * Real.pi * Complex.I * j * τ / M)) := by
    funext j
    simp only [Function.comp_apply, le_add_iff_nonneg_left, Nat.cast_nonneg, if_true, add_sub_cancel_right,
      Int.toNat_natCast, hε]
    rw [mul_left_comm, ee, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact e ▸ h1

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem an_siegel_eq : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  intro Ω _ _ _ ε T c x hx
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set M : ℕ := (x 0).den * (x 1).den with hMdef
  have hM : 0 < M := Nat.mul_pos (x 0).den_pos (x 1).den_pos
  set Px : Fin 2 → ℤ := ![(x 0).num * (x 1).den, (x 1).num * (x 0).den] with hPx
  have hMx : ∀ i, (M : ℚ) * x i = Px i := fun i => by
    fin_cases i
    · simp only [hMdef, hPx, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 0)]; ring
    · simp only [hMdef, hPx, Matrix.cons_val_one, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 1)]; ring
  have hd : DifferentiableOn ℂ (sgC c x) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)
  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ := by
    intro γ hγ τ
    haveI : NeZero M := ⟨hM.ne'⟩
    obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have d00 : (M : ℤ) ∣ γ 0 0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g00, sub_self])
    have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g01
    have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g10
    have d11 : (M : ℤ) ∣ γ 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g11, sub_self])
    obtain ⟨t00, h00⟩ := d00
    obtain ⟨t01, h01⟩ := d01
    obtain ⟨t10, h10⟩ := d10
    obtain ⟨t11, h11⟩ := d11
    have e : act x γ = fun i => x i + (![Px 0 * t00 + Px 1 * t10, Px 0 * t01 + Px 1 * t11] : Fin 2 → ℤ) i := by
      have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * t00 := by
        have : γ 0 0 = 1 + M * t00 := by rw [← h00]; ring
        rw [this]; push_cast; ring
      have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * t11 := by
        have : γ 1 1 = 1 + M * t11 := by rw [← h11]; ring
        rw [this]; push_cast; ring
      have q01 : ((γ 0 1 : ℤ) : ℚ) = M * t01 := by rw [h01]; push_cast; ring
      have q10 : ((γ 1 0 : ℤ) : ℚ) = M * t10 := by rw [h10]; push_cast; ring
      have r0 : act x γ 0 = x 0 + ((Px 0 * t00 + Px 1 * t10 : ℤ) : ℚ) := by
        rw [act_zero, q00, q10]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      have r1 : act x γ 1 = x 1 + ((Px 0 * t01 + Px 1 * t11 : ℤ) : ℚ) := by
        rw [act_one', q01, q11]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      funext i
      fin_cases i
      · simpa using r0
      · simpa using r1
    rw [e]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ τ hx
  refine SiegelModel.an_siegel T M hM hd (fun γ τ => GlobalTheory.T.siegel_function_transformation c x γ τ hx) hlev (fun γ => ?_)
  refine exp_int ε hM (fun i => Px 0 * γ 0 i + Px 1 * γ 1 i) (fun i => ?_) (admissible_act_SL2 hx γ)
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [← hMx 0, ← hMx 1]
  ring

end GlobalTheory.KZ.SiegelMem
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType.ClearBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_congr (χ : kˣ →* ℂˣ) {x y : k} (h : valuation k x = valuation k y) : Triv χ x ↔ Triv χ y := by
  unfold Triv; rw [h]

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h) zero_le'
  rw [Valuation.zero_iff, sub_eq_zero] at h0
  have : u = 1 := Units.ext h0
  simp [this]

theorem res_zero_iff (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem val_det_eq_one {n r : ℕ} {M M' : Matrix (Fin n) (Fin n) k}
    (hM : ∀ i j, valuation k (M i j) ≤ 1) (hM' : ∀ i j, valuation k (M' i j) ≤ 1)
    (hsame : ∀ i j : Fin n, ((i : ℕ) < r ↔ (j : ℕ) < r) → M i j = M' i j)
    (hur : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (M i j) < 1)
    (hur' : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (M' i j) < 1)
    (hd : valuation k M.det = 1) : valuation k M'.det = 1 := by
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨M i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  let A' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨M' i j, (Valuation.mem_integer_iff _ _).2 (hM' i j)⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = M := rfl
  have hA' : (algebraMap 𝒪[k] k).mapMatrix A' = M' := rfl
  have hI := Valuation.integer.integers (valuation k)
  have key : ∀ B : Matrix (Fin n) (Fin n) 𝒪[k], (∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → valuation k (B i j : k) < 1) →
      ((IsLocalRing.residue 𝒪[k]).mapMatrix B).det =
        (toSquareBlockProp ((IsLocalRing.residue 𝒪[k]).mapMatrix B) (fun i => r ≤ (i : ℕ))).det *
        (toSquareBlockProp ((IsLocalRing.residue 𝒪[k]).mapMatrix B) (fun i => ¬ r ≤ (i : ℕ))).det := by
    intro B hB
    refine twoBlockTriangular_det _ _ fun i hi j hj => ?_
    exact (res_zero_iff _).2 (hB i j (by omega) hj)
  have e1 : ((IsLocalRing.residue 𝒪[k]).mapMatrix A).det = ((IsLocalRing.residue 𝒪[k]).mapMatrix A').det := by
    rw [key A hur, key A' hur']
    congr 2
    · ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toSquareBlockProp_def, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      congr 1; exact Subtype.ext (hsame i j (by omega))
    · ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [toSquareBlockProp_def, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      congr 1; exact Subtype.ext (hsame i j (by omega))
  have u1 : IsUnit A.det := hI.isUnit_iff_valuation_eq_one.2 (by rw [RingHom.map_det, hA, hd])
  have u2 : IsUnit A'.det := by
    by_contra hc
    have h0 : IsLocalRing.residue 𝒪[k] A'.det = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hc
    rw [RingHom.map_det, ← e1, ← RingHom.map_det, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 u1
  have := hI.isUnit_iff_valuation_eq_one.1 u2
  rwa [RingHom.map_det, hA'] at this

end GlobalTheory.PsType.ClearBlock

namespace GlobalTheory.PsType


open ClearBlock in
theorem clear_upper_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), Ordered ψ → Cut ψ r → ∀ j ∈ grp ψ, ∃ y ∈ strip ψ r ϖ 0,
      ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → (y⁻¹ * j).val a b = 0 := by
  intro k _ _ _ _ n ψ r ϖ hord hcut g hg
  have hint : ∀ a b, valuation k (g.val a b) ≤ 1 := GlobalTheory.BlockType.val_le_one_of_mem_KO hg.1
  have hur : ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → valuation k (g.val a b) < 1 := by
    intro a b ha hb
    refine lt_of_le_of_ne (hint a b) fun h1 => hcut a b ha hb ?_
    exact (triv_congr _ (h1.trans (map_one _).symm)).1 (hg.2 a b (Fin.lt_iff_val_lt_val.2 (by omega)))
  have hdet : valuation k g.val.det = 1 := (GlobalTheory.LocStd.mem_KO_iff_det.1 hg.1).2
  obtain ⟨Dm, hDm⟩ : ∃ Dm : Matrix (Fin n) (Fin n) k, ∀ a b, Dm a b = if ((a : ℕ) < r ↔ (b : ℕ) < r) then g.val a b else 0 :=
    ⟨fun a b => _, fun _ _ => rfl⟩
  obtain ⟨Um, hUm⟩ : ∃ Um : Matrix (Fin n) (Fin n) k, ∀ a b, Um a b = if r ≤ (a : ℕ) ∧ (b : ℕ) < r then 0 else g.val a b :=
    ⟨fun a b => _, fun _ _ => rfl⟩
  have hDint : ∀ a b, valuation k (Dm a b) ≤ 1 := fun a b => by
    rw [hDm]; split_ifs
    · exact hint a b
    · simp
  have hUint : ∀ a b, valuation k (Um a b) ≤ 1 := fun a b => by
    rw [hUm]; split_ifs
    · simp
    · exact hint a b
  have hDdet : valuation k Dm.det = 1 :=
    val_det_eq_one hint hDint (fun a b h => by rw [hDm, if_pos h]) hur
      (fun a b ha hb => by rw [hDm, if_neg (by omega)]; simp) hdet
  have hUdet : valuation k Um.det = 1 :=
    val_det_eq_one hint hUint (fun a b h => by rw [hUm, if_neg (by omega)]) hur
      (fun a b ha hb => by rw [hUm, if_neg (by omega)]; exact hur a b ha hb) hdet
  obtain ⟨Dg, hDK, hDv⟩ := GlobalTheory.LocStd.mem_image_KO.2
    ⟨fun a b => (Valuation.mem_integer_iff _ _).2 (hDint a b), hDdet⟩
  obtain ⟨Ug, hUK, hUv⟩ := GlobalTheory.LocStd.mem_image_KO.2
    ⟨fun a b => (Valuation.mem_integer_iff _ _).2 (hUint a b), hUdet⟩
  have hD : Dg ∈ grp ψ := ⟨hDK, fun a b hab => by
    rw [hDv, hDm]; split_ifs
    · exact hg.2 a b hab
    · exact triv_zero _⟩
  have hU : Ug ∈ grp ψ := ⟨hUK, fun a b hab => by
    rw [hUv, hUm]; split_ifs
    · exact triv_zero _
    · exact hg.2 a b hab⟩
  have hy : Ug * Dg⁻¹ ∈ grp ψ := GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ hord Ug hU _ (GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ hord Dg hD)
  set Di : Matrix (Fin n) (Fin n) k := ((Dg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hDi
  have hDi1 : Dm * Di = 1 := by rw [← hDv]; exact Dg.mul_inv
  have hDi2 : Di * Dm = 1 := by rw [← hDv]; exact Dg.inv_mul
  let Q : Matrix (Fin n) (Fin n) k := diagonal fun a => if (a : ℕ) < r then (0 : k) else 1
  have hDQ : Dm * Q = Q * Dm := by
    ext a b
    simp only [Q, mul_diagonal, diagonal_mul, hDm]
    by_cases ha : (a : ℕ) < r <;> by_cases hb : (b : ℕ) < r <;> simp [ha, hb]
  have hQDi : Di * Q = Q * Di := calc
    Di * Q = Di * Q * (Dm * Di) := by rw [hDi1, Matrix.mul_one]
    _ = Di * (Dm * Q) * Di := by rw [hDQ]; simp only [Matrix.mul_assoc]
    _ = (Di * Dm) * Q * Di := by simp only [Matrix.mul_assoc]
    _ = Q * Di := by rw [hDi2, Matrix.one_mul]
  have hDioff : ∀ l b : Fin n, r ≤ (l : ℕ) → (b : ℕ) < r → Di l b = 0 := by
    intro l b hl hb
    have := congrFun (congrFun hQDi l) b
    simp only [Q, mul_diagonal, diagonal_mul, if_pos hb, if_neg (Nat.not_lt.2 hl)] at this
    simpa using this.symm
  refine ⟨Ug * Dg⁻¹, ?_, ?_⟩
  · have hyv : (Ug * Dg⁻¹).val = (Um - Dm) * Di + 1 := by
      rw [Units.val_mul, hUv, Matrix.sub_mul, hDi1, sub_add_cancel]
    intro a b
    split_ifs with hab
    · rw [pow_zero, one_mul]
      exact ⟨GlobalTheory.BlockType.val_le_one_of_mem_KO hy.1 a b,
        hy.2 a b (Fin.lt_iff_val_lt_val.2 (by omega))⟩
    · rw [hyv, Matrix.add_apply, Matrix.mul_apply]
      rw [Finset.sum_eq_zero, zero_add]
      intro l _
      rw [Matrix.sub_apply]
      by_cases ha : (a : ℕ) < r
      · have hb : (b : ℕ) < r := by omega
        by_cases hl : (l : ℕ) < r
        · simp [hUm, hDm, ha, hl, Nat.not_le.2 ha]
        · rw [hDioff l b (by omega) hb, mul_zero]
      · by_cases hl : (l : ℕ) < r <;> simp [hUm, hDm, ha, hl]
  · intro a b ha hb
    set Ui : Matrix (Fin n) (Fin n) k := ((Ug⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hUi
    have hUi1 : Ui * Um = 1 := by rw [← hUv]; exact Ug.inv_mul
    have e : ((Ug * Dg⁻¹)⁻¹ * g).val = Dm + Dm * Ui * (g.val - Um) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, hDv, Matrix.mul_sub, Matrix.mul_assoc Dm Ui Um, hUi1,
        Matrix.mul_one, add_sub_cancel]
    rw [e, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero]
    · rw [hDm, if_neg (by omega), zero_add]
    · intro l _
      rw [Matrix.sub_apply, hUm, if_neg (by omega), sub_self, mul_zero]

end GlobalTheory.PsType
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem theta_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  intro k _ _ _ _ n ψ hψ a ha b hb
  have P := GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k
  obtain ⟨-, -, -, -, -, -, hevmul, hevcong, hevtriv⟩ := P
  unfold theta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  by_cases ht : Triv (ψ m / nxt ψ m) 1
  · rw [hevtriv _ _ ht, hevtriv _ _ ht, hevtriv _ _ ht, one_mul]
  · obtain ⟨hv, hc⟩ := GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k n ψ hψ m ht
    have hab := GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ hψ a ha b hb
    have va := hv a ha
    have vb := hv b hb
    have vab := hv (a * b) hab
    have vprod : valuation k (minor a m * minor b m) = 1 := by rw [map_mul, va, vb, one_mul]
    rw [hevcong _ _ _ vab vprod (hc a ha b hb), hevmul _ _ _ va vb]

end GlobalTheory.PsType
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (F : Finset (integralClosure (O0 p) Ω)), ∃ (C : Subalgebra (O0 p) (integralClosure (O0 p) Ω)) (tr : (integralClosure (O0 p) Ω) → (integralClosure (O0 p) Ω)) (n : ℕ) (a b : Fin n → (integralClosure (O0 p) Ω)), (↑F : Set (integralClosure (O0 p) Ω)) ⊆ C ∧ IsTrData (towerAlg T) C tr a b (p : (integralClosure (O0 p) Ω)) := by
  first | exact @GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg | exact GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg | (intros; apply GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (γ : SL(2, ℤ)), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) a → ∃ C δ : ℝ, 0 < δ ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im → ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C * Real.exp (-δ * τ.im) := by
  first | exact @GlobalTheory.EisM.cusp_decay | exact GlobalTheory.EisM.cusp_decay | (intros; apply GlobalTheory.EisM.cusp_decay <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L → MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  first | exact @GlobalTheory.EisM.To_MF | exact GlobalTheory.EisM.To_MF | (intros; apply GlobalTheory.EisM.To_MF <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.cuspForm_lseries_extends_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  first | exact @GlobalTheory.EisM.lseries_cusp_entire | exact GlobalTheory.EisM.lseries_cusp_entire | (intros; apply GlobalTheory.EisM.lseries_cusp_entire <;> assumption)
end
