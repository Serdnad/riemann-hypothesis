module

public import Formalism.MahlerMeasure.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.ObjSeg
public import Formalism.SharpRestriction.GrowthBounds.FlipOneThree
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction
import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Dim

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem xi_span (ι : ℚ_[p] →+* KK O) {N r t b : ℕ} (g : MvPolynomial (BVar N r t) (KK O))
    (hg : g ∈ XiPolZ O N r t b) :
    g ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.XiPolZ p N r t b : Set (MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]))) := by
  classical
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hsupp := ((mem_restrictSupport_iff _).1 hg.1) (Finset.mem_coe.2 hμ)
  have h1 : monomial μ (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r t b := by
    refine ⟨?_, ⟨monomial μ 1, by simp⟩⟩
    show monomial μ (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] _
    rw [mem_restrictSupport_iff]
    intro m hm
    have : m = μ := by
      have := support_monomial_subset hm
      simpa using this
    rw [this]
    exact hsupp
  have h2 : monomial μ (g.coeff μ) = g.coeff μ • map ι (monomial μ (1 : ℚ_[p])) := by
    rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1, rfl⟩)

theorem finrank_span_image_le (ι : ℚ_[p] →+* KK O) {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℚ_[p] V₁]
    [AddCommGroup V₂] [Module (KK O) V₂] (f : V₁ → V₂) (hadd : ∀ u v, f (u + v) = f u + f v)
    (hsm : ∀ (c : ℚ_[p]) u, f (c • u) = ι c • f u) (W : Submodule ℚ_[p] V₁) [FiniteDimensional ℚ_[p] W] :
    Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁))) ≤ Module.finrank ℚ_[p] W := by
  classical
  set bW := Module.finBasis ℚ_[p] W
  have h0 : f 0 = 0 := by
    have := hsm 0 0
    rwa [zero_smul, map_zero, zero_smul] at this
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℚ_[p] W))) (c : Fin (Module.finrank ℚ_[p] W) → ℚ_[p]),
      f (∑ i ∈ s, c i • (bW i : V₁)) = ∑ i ∈ s, ι (c i) • f (bW i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]
  have hle : Submodule.span (KK O) (f '' (W : Set V₁)) ≤
      Submodule.span (KK O) (Set.range fun i => f (bW i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (⟨w, hw⟩ : W) = ∑ i, (bW.repr ⟨w, hw⟩ i) • bW i := (bW.sum_repr _).symm
    have hw'' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V₁) := by
      have h3 := congrArg (Submodule.subtype W) hw'

      rw [map_sum] at h3
      simpa only [Submodule.subtype_apply, map_smul] using h3
    rw [hw'', hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  calc Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁)))
      ≤ Module.finrank (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank ℚ_[p] W)) := finrank_range_le_card _
    _ = Module.finrank ℚ_[p] W := Fintype.card_fin _

theorem finrank_biSup_le {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (U : ι → Submodule K V)
    (s : Finset ι) (hU : ∀ i ∈ s, FiniteDimensional K (U i)) :
    FiniteDimensional K (⨆ i ∈ s, U i : Submodule K V) ∧
      Module.finrank K (⨆ i ∈ s, U i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), U i) = (⊥ : Submodule K V) by simp]
    exact ⟨inferInstance, by simp⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have ha' := hU a (Finset.mem_insert_self a s)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left h2 _)

end Dim

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

private theorem sort_get_lt_of_lt (s : Finset ℕ) (l u : Fin (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).length)
    (h : l < u) : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l < (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
  have hp := Finset.pairwise_sort s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hn := Finset.sort_nodup s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hle : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≤ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u :=
    hp.rel_get_of_lt h
  have hne : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≠ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
    intro he
    have := (List.nodup_iff_injective_get.mp hn) he
    exact absurd this (ne_of_lt h)
  omega

theorem segDists_lt {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (l u : Fin (segS TT j)) (h : l < u) :
    (segDists TT j).get l < (segDists TT j).get u := sort_get_lt_of_lt _ l u h

theorem segDists_lt_G {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (u : Fin (segS TT j)) :
    (segDists TT j).get u < segG TT j := by
  have hm : (segDists TT j).get u ∈ segDists TT j := List.get_mem _ _
  unfold segDists at hm
  rw [Finset.mem_sort, Finset.mem_image] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  rw [Finset.mem_filter] at hx
  have e : (segDists TT j).get u = cdist (segStart TT j) x := hxe.symm
  rw [e]
  exact hx.2.2.2

theorem P_step (l u : Fin X.s) (h : l < u) :
    X.p * (X.S C0 CE1 CE2).P X.p u ≤ (X.S C0 CE1 CE2).P X.p l := by
  have h1 := segDists_lt X.L.TT X.j l u h
  have h2 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p * X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u) ≤
    X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get l)
  rw [← pow_succ']
  exact Nat.pow_le_pow_right hp (by omega)

theorem p_le_P (u : Fin X.s) : X.p ≤ (X.S C0 CE1 CE2).P X.p u := by
  have h1 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p ≤ X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u)
  calc X.p = X.p ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right hp (by omega)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

end Formalism.MainNotions.G.SymmetricFormBlocks

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem winA_sum (X : flipOneThree.Inst) (f : ℕ → ℝ) :
    ∑ aPlus ∈ X.winA, f aPlus = ∑ j ∈ Finset.range X.winA.card, f (X.L.a + j) := by
  unfold flipOneThree.Inst.winA
  rw [Nat.card_Icc, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
