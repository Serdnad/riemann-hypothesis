module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

noncomputable section

namespace GlobalTheory.HCF.FormsSub

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isAutForm_zero : IsAutForm (0 : Sm E a) := by
  constructor
  · intro γ g
    rfl
  · have : {k | finRep E a k (0 : Sm E a) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
    rw [this]; exact isOpen_univ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp
  · intro g
    exact ⟨0, 0, fun y => by simp⟩

theorem isAutForm_add {φ ψ : Sm E a} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) : IsAutForm (φ + ψ) := by
  apply _root_.GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add <;> assumption

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (hφ : IsAutForm φ) : IsAutForm (c • φ) := by
  apply _root_.GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul <;> assumption

theorem foldr_lin (χ : Module.End ℂ (Sm E a) → ℂ) (c : ℂ) (φ ψ : Sm E a) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (c • φ + ψ) =
      c • zs.foldr (fun z f => z f - χ z • f) φ + zs.foldr (fun z f => z f - χ z • f) ψ := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.foldr_cons]
    rw [ih, map_add (f := _), map_smul]
    module

theorem foldr_zero (χ : Module.End ℂ (Sm E a) → ℂ) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (0 : Sm E a) = 0 := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [List.foldr_cons, ih, map_zero, smul_zero, sub_zero]

end GlobalTheory.HCF.FormsSub


open GlobalTheory.HCF.FormsSub in
theorem GlobalTheory.HCF.formsGL_single_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ),
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W {χ} N), φ ∈ formsGL E a L W {χ} N := by
  intro E _ _ _ a L W χ N
  let S : Submodule ℂ (Sm E a) :=
    { carrier := formsGL E a L W {χ} N
      zero_mem' := by
        refine ⟨isAutForm_zero, fun k _ => map_zero _, fun g => ?_, χ, rfl, fun zs _ _ => foldr_zero χ zs⟩
        have : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
          funext k; simp
        rw [this]; exact W.zero_mem
      add_mem' := by
        rintro φ ψ ⟨a1, b1, c1, χ1, e1, d1⟩ ⟨a2, b2, c2, χ2, e2, d2⟩
        rw [Set.mem_singleton_iff] at e1 e2
        rw [e1] at d1
        rw [e2] at d2
        refine ⟨isAutForm_add a1 a2, fun k hk => by rw [map_add (f := _), b1 k hk, b2 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
              (fun k : Kinf E a => (cptRep E a k φ).1 g) + (fun k : Kinf E a => (cptRep E a k ψ).1 g) := by
            funext k; simp
          rw [this]; exact W.add_mem (c1 g) (c2 g)
        · have := foldr_lin χ 1 φ ψ zs
          rw [one_smul, one_smul] at this
          rw [this, d1 zs hl hz, d2 zs hl hz, add_zero]
      smul_mem' := by
        rintro c φ ⟨a1, b1, c1, χ1, e1, d1⟩
        rw [Set.mem_singleton_iff] at e1
        rw [e1] at d1
        refine ⟨isAutForm_smul c a1, fun k hk => by rw [map_smul, b1 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) = c • (fun k : Kinf E a => (cptRep E a k φ).1 g) := by
            funext k; simp
          rw [this]; exact W.smul_mem c (c1 g)
        · have := foldr_lin χ c φ 0 zs
          rw [add_zero, foldr_zero, add_zero] at this
          rw [this, d1 zs hl hz, smul_zero] }
  intro φ hφ
  exact (Submodule.span_le (p := S)).2 le_rfl hφ
