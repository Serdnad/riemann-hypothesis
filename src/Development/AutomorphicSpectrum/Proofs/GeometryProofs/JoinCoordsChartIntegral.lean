module

import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCentreChartStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem mem_of_isIntegral_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {v : Ω} (hv : IsIntegral R v)
    (hv0 : v ≠ 0) (hu : v⁻¹ ∈ R) : v ∈ R := by
  apply _root_.PositivityTheory.HtPt.Mb.LNormChart.ChNorm.mem_of_isIntegral_of_inv_mem <;> assumption

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem chRing_join_iff {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    {d n : ℕ} (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔
      a ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
  apply _root_.PositivityTheory.HtPt.Mb.LNormChart.ChNorm.chRing_join_iff <;> assumption

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem joinCo_div {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) {d n : ℕ} (z : κ ⊕ Fin n → Ω)
    (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (q : κ × (κ ⊕ Fin n)) :
    joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d) := by
  simp only [joinCo, RingHom.id_apply, hz c]
  exact mul_div_mul_comm _ _ _ _

theorem join_chart_normalisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' := by
  intro o _ Ω _ _ κ _ x d n z M' hz hspan c hc
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d) := fun k =>
    (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hxS : ∀ j, x j / x c ∈ chRing o x c := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨fun a => ?_, fun p' hp' => ?_⟩
  · rw [chRing_join_iff x z hz c hc a]
    constructor
    · intro ha
      have hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤
          (integralClosure (chRing o x c) Ω).restrictScalars o := by
        apply Algebra.adjoin_le
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2
            (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))
      exact (mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))
    · intro ha
      have hSle : chRing o x c ≤
          Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) :=
        Algebra.adjoin_mono Set.subset_union_left
      refine Submodule.span_induction
        (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)))
        ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)
      · rintro _ ⟨k, rfl⟩
        exact Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro s b _ hb
        rw [Subalgebra.smul_def]
        exact mul_mem (hSle s.2) hb
  · obtain ⟨hctr, l, hl⟩ :=
      GlobalTheory.T.join_coords_centre_chart o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'
    obtain ⟨c', -, hc'⟩ := hctr
    have ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p' := fun r =>
      hc' _ (Subalgebra.algebraMap_mem _ r)
    have hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p' := by
      intro a ha
      have h1 : a ∈ (chRing o x c).toSubring := ha
      rw [chRing, Algebra.adjoin_eq_ring_closure] at h1
      exact (Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r)
        (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1
    let φ : chRing o x c →+* regAt M'.ξ p' :=
      { toFun := fun s => ⟨s, hSle s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)
    obtain ⟨hzl, hzr⟩ := hl
    have hv : z l / x c ^ d ∈ regAt M'.ξ p' :=
      mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)
    have hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p' := fun k => by
      have e : z k / x c ^ d = z k / z l * (z l / x c ^ d) := by field_simp
      rw [e]
      exact mul_mem (hzr k) hv
    refine ⟨?_, fun q => ?_⟩
    · simp only [joinCo, RingHom.id_apply, hz c]
      exact mul_ne_zero hc hd
    · rw [joinCo_div x z hz c q]
      exact mul_mem (hp' q.1) (hy q.2)

end GlobalTheory.CompanionTheory.Ar.ChNorm
