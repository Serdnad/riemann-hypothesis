module

import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGrowthOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothing

@[expose] public section

open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspStabFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zfin_of_comm (T : Module.End ℂ (Sm E a)) (hT : ∀ z ∈ Zalg E a, z * T = T * z) {φ : Sm E a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (T φ)) '' Zalg E a)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
    Zalg E a)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, (LinearMap.congr_fun (hT z hz) φ).symm⟩

theorem zalg_comm_fin (k : GL (Fin a) (Af E)) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    z * finRep E a k = finRep E a k * z := by
  let S := Subalgebra.centralizer ℂ ({finRep E a k} : Set (Module.End ℂ (Sm E a)))
  have hL : ∀ X, lie E a X ∈ S := fun X T hT => by
    rw [Set.mem_singleton_iff.1 hT]; exact (lie_rt_fin X k).symm
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have hS : Zalg E a ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hS hz (finRep E a k) rfl).symm

theorem level_of_le {φ ψ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ})
    (hle : ∀ k, finRep E a k φ = φ → finRep E a k ψ = ψ) : IsOpen {k | finRep E a k ψ = ψ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.mem_nhds (by simp)) fun k hk => hle k hk)

theorem height_mul_le_const (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  apply _root_.GlobalTheory.AutGrowth.SmoothFinite.height_mul_le <;> assumption

theorem growth_mul_const {f : GL (Fin a) (Cinf E) → ℂ} (c : GL (Fin a) (Cinf E))
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (y * c)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  obtain ⟨B, hB, hB'⟩ := _root_.GlobalTheory.AutGrowth.SmoothFinite.height_mul_le c
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => (hC _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * c)]) (hB' y) N) C0

theorem isCuspForm_act' (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E a) (φ : Sm E a) (h : IsCuspForm φ) : IsCuspForm (act o φ) := by
  apply _root_.UpperTheory.V.Cm.isCuspForm_act <;> assumption

end GlobalTheory.CuspStabFin

theorem GlobalTheory.CuspStabFin.isCuspForm_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (o : GlobalTheory.CuspRep.Op E a) (φ : GlobalTheory.CuspRep.Sm E a),
    GlobalTheory.CuspRep.IsCuspForm φ → GlobalTheory.CuspRep.IsCuspForm (GlobalTheory.CuspRep.act o φ) :=
  fun hP _ _ _ _ _ o φ h => GlobalTheory.CuspStabFin.isCuspForm_act' hP o φ h
