module

public import GroundTheory.AutomorphicForms.SphericalMinuscule
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.AutomorphicForms.GLnLocal
public import GroundTheory.AutomorphicForms.MacdonaldHecke
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_perm_mem_iff {N : ℕ} {A B : Finset (Fin N)} (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin N), ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  have e1 : {x // x ∈ A} ≃ {x // x ∈ B} := Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // x ∉ A} ≃ {x // x ∉ B} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨(Equiv.sumCompl (· ∈ A)).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ B))),
    fun x => ?_⟩
  by_cases hx : x ∈ A
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ⟨fun _ => hx, fun _ => (e1 ⟨x, hx⟩).2⟩
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hx, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ⟨fun h' => absurd h' (e2 ⟨x, hx⟩).2, fun h' => absurd h' hx⟩

theorem lamS_comp_of_mem_iff {N : ℕ} {A B : Finset (Fin N)} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ x, σ x ∈ B ↔ x ∈ A) : lamS B ∘ σ = lamS A := by
  funext x
  simp only [Function.comp_apply, lamS, hσ]

section Values

variable {n : ℕ} {ω : GL (Fin n) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F n, ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F n, ω (k * g) = ω g)
include hR hL

end Values

section ValuesCons

variable {N : ℕ} {ω : GL (Fin (N + 1)) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (k * g) = ω g)
include hR hL

end ValuesCons

variable {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]


end SatakeBound

end GroundTheory.BlockD
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open IsDedekindDomain NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa
  Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizer_eq :
    Valued.v (uniformizer (w.adicCompletion K) : w.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  have hS : (Valuation.integer (ValuativeRel.valuation (w.adicCompletion K))) =
      (w.adicCompletionIntegers K).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff w x
  let e := RingEquiv.subringCongr hS
  have hirr : Irreducible (e (uniformizer (w.adicCompletion K))) :=
    (MulEquiv.irreducible_iff e).2 (irreducible_uniformizer _)
  have := GroundTheory.Global.valued_of_irreducible (v := w) (K := K)
    (ϖ := ⟨(e (uniformizer (w.adicCompletion K)) : w.adicCompletion K), (e _).2⟩) (by exact hirr)
  simpa [e] using this

theorem valued_le_one_of_mem {x : w.adicCompletion K} (hx : x ∈ 𝒪[w.adicCompletion K]) :
    Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K w).1
    ((GroundTheory.Global.mem_valuationInteger_iff w x).1 hx)

variable {w}

end SatakeBound

end GroundTheory.BlockD
end
end
